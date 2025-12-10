//! This crate provides functionality for checking the determinacy of circuits.
//! It has support for different backends including `cvc5` and `z3`.
//!
//! # Features
//!
//! - **cvc5**: Enables cvc5 backend.
//! - **z3**: Enables z3 backend.
//!
//! Note: Both features `cvc5` and `z3` cannot be enabled at the same time.
//!
//! # Usage
//!
//! To use the crate, make sure to provide the appropriate feature flag
//! depending on the backend you want to use.
#![warn(
    missing_docs,
    unreachable_pub,
    non_ascii_idents,
    unreachable_pub,
    unused_crate_dependencies,
    unused_qualifications,
    nonstandard_style,
    rustdoc::all
)]
#![deny(rust_2018_idioms, unsafe_code)]

#[cfg(feature = "cvc5")]
/// This module contains the cvc5 backend for the circomference binary
pub mod cvc5_lib;

#[cfg(feature = "z3")]
/// This module contains the z3 backend for the circomference binary
pub mod z3_lib;

use clap::Parser;
use memory_stats::{memory_stats, MemoryStats};
use r1cs_file::R1csFile;

use regex::Regex;
use smtlib::{Logic, SatResult};
use std::{
    fs::File,
    io::{Read, Write},
    path::Path,
};

#[cfg(feature = "cvc5")]
use crate::cvc5_lib::smt_check_determinacy;
#[cfg(feature = "cvc5")]
use crate::cvc5_lib::{r1cs_to_circuit, Circuit};

#[cfg(feature = "z3")]
use crate::z3_lib::smt_check_determinacy_z3;
#[cfg(feature = "z3")]
use crate::z3_lib::{r1cs_to_circuit_z3, CircuitZ3};

/// This struct holds the arguments provided to your program via the command
/// line.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
pub struct Args {
    /// Name of the R1CS file
    #[arg(short, long)]
    pub r1cs_file: String,

    /// Check for weak determinacy or strong determinacy
    #[arg(short, long, default_value_t = false)]
    pub weak_det: bool,

    /// Profile memory usage
    #[arg(short, long, default_value_t = false)]
    pub mem_prof: bool,

    /// Input for verbosity, default is false.
    #[arg(short, long, default_value_t = false)]
    pub verbose: bool,

    /// Optional input for dumping witness assignments to a file
    #[arg(short, long)]
    pub assgn_dump_path: Option<String>,

    /// Optional input for symfile path for prettier variable names on dump
    #[arg(short, long)]
    pub sym_path: Option<String>,

    /// Optional input for timeout in milliseconds
    #[arg(short, long)]
    pub timeout: Option<u64>,

    /// Optional input for trusted function path
    #[arg(short, long)]
    pub det_func_path: Option<Vec<String>>,

    /// Optional input for specifying a cvc5 binary path instead of default
    #[arg(short, long)]
    pub cvc5_path: Option<String>,
}

/// Entry point for the circomference binary.
///
/// This function first checks that the "cvc5" and "z3" features are not both
/// enabled. If they are, it will panic as these two features are mutually
/// exclusive.
///
/// Depending on the enabled feature, it will then parse the arguments passed to
/// the program and call either `execute` (if "cvc5" feature is enabled) or
/// `execute_z3` (if "z3" feature is enabled). Both functions return a
/// `SatResult`.
///
/// Finally, it will match on the `SatResult` to print a corresponding message
/// to the console:
///
/// - `SatResult::Sat` indicates the circuit is not deterministic and two
///   distinct witnesses exist that satisfy the constraints.
/// - `SatResult::Unsat` indicates the system is deterministic.
/// - `SatResult::Unknown` indicates the result is unknown.
///
/// # Panics
/// Panics if both "cvc5" and "z3" features are enabled at the same time.
///
/// # Features
/// - "cvc5": Enables the cvc5 backend.
/// - "z3": Enables the z3 backend.
fn main() {
    if cfg!(feature = "cvc5") && cfg!(feature = "z3") {
        panic!("feature \"cvc5\" and feature \"z3\" cannot be enabled at the same time");
    }

    #[cfg(feature = "cvc5")]
    let sat_result = execute(Args::parse());
    #[cfg(feature = "z3")]
    let sat_result = execute_z3(Args::parse());

    match sat_result {
        SatResult::Sat => {
            println!("The circuit is not deterministic! Two distinct witnesses exist that satisfy the constraints.");
        }
        SatResult::Unsat => println!("The system is deterministic!"),
        SatResult::Unknown => println!("The result is unknown!"),
    }
}

/// Executes the deterministic check for a circuit using the CVC5 solver.
///
/// This function is available when the "cvc5" feature is enabled. It processes
/// a given R1CS file, sets up the CVC5 backend, and creates a solver with the
/// CVC5 backend. It then sets up the logic for the solver to `QF_FF` and sets
/// the field order.
///
/// It checks the determinacy of the circuit using the `smt_check_determinacy`
/// function. If memory profiling is enabled, it also profiles the memory.
///
/// # Parameters
///
/// - `args`: The arguments passed from the command line. Contains the R1CS
///   file, information on whether to perform a weak deterministic check,
///   assignment dump path, symbolic path, and path to the CVC5 binary, among
///   other arguments.
///
/// # Returns
///
/// A `SatResult` which is the result of the `smt_check_determinacy` call. It
/// contains the result of the satisfiability check: `Sat`, `Unsat`, or
/// `Unknown`.
///
/// # Panics
///
/// This function will panic if the path to the CVC5 binary does not exist.
///
/// # Features
///
/// This function is available when the "cvc5" feature is enabled.
///
/// # Example
///
/// ```no_run
/// # use craterustc::Args;
/// let args = Args::new(); // add your own arguments
/// let result = execute(args);
/// println!("{:?}", result);
/// ```
#[cfg(feature = "cvc5")]
fn execute(args: Args) -> SatResult {
    println!("Checking R1CS file: {}", args.r1cs_file);

    let r1cs_description = process_r1cs(&args.r1cs_file);
    let det_func_paths = args.det_func_path.unwrap_or_default();
    let mut det_func_r1cs: Vec<R1csFile<32>> = vec![];

    if det_func_paths.len() > 0 {
        println!("Using trusted functions: {:?}", det_func_paths);
        for det_func in det_func_paths {
            det_func_r1cs.push(process_r1cs(&det_func));
        }
    }

    // Set up the backend
    // Assert first that the cvc5 binary is an existing path
    let cvc5_binary_path = Path::new("src/cvc5");
    assert!(
        cvc5_binary_path.exists(),
        "CVC5 binary does not exist in circomference/src!"
    );

    let backend_cvc5 = smtlib::backend::Cvc5Binary::new(cvc5_binary_path).unwrap();

    let mut det_func_circuits: Vec<Circuit> = vec![];
    let circuit: Circuit = r1cs_to_circuit(&r1cs_description);
    for det_func_file in det_func_r1cs {
        det_func_circuits.push(r1cs_to_circuit(&det_func_file));
    }

    // Set up the solver
    let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, args.verbose).unwrap();
    println!("Using CVC5 backend");
    cvc5_solver.set_logic(Logic::QF_FF).unwrap();
    cvc5_solver.set_field_order(&circuit.prime).unwrap();

    let sat_result = smt_check_determinacy(
        &circuit,
        &args.weak_det,
        &args.assgn_dump_path,
        &args.sym_path,
        &mut cvc5_solver,
        &args.cvc5_path,
        &Some(det_func_circuits),
    )
    .unwrap();
    if args.mem_prof {
        let _ = profile_memory();
    }

    if args.assgn_dump_path.is_some() {
        let _ = clean_output(&args.assgn_dump_path.unwrap());
    }

    sat_result
}

/// Executes the deterministic check for a circuit using the statically linked
/// Z3 solver.
///
/// This function is available when the "z3" feature is enabled. It processes
/// the given R1CS file, sets up the Z3 backend, and creates a solver with the
/// Z3 backend.
///
/// Similarly to the above, it checks the determinacy of the circuit using the
/// `smt_check_determinacy_z3` function.
///
/// # Parameters
///
/// - `args`: Command-line arguments, including the R1CS file, whether to
///   perform a weak deterministic check, assignment dump path, symbolic path,
///   and others.
///
/// # Returns
///
/// A `SatResult` which contains the result of the satisfiability check: `Sat`,
/// `Unsat`, or `Unknown`.
///
/// # Features
///
/// This function is available when the "z3" feature is enabled.
///
/// # Example
///
/// ```no_run
/// # use craterustc::Args;
/// let args = Args::new(); // add your own arguments
/// let result = execute_z3(args);
/// println!("{:?}", result);
/// ```
#[cfg(feature = "z3")]
fn execute_z3(args: Args) -> SatResult {
    println!("Checking R1CS file: {}", args.r1cs_file);

    let r1cs_description = process_r1cs(&args.r1cs_file);

    // 1. Set up the backend
    let backend_z3 = smtlib::backend::Z3Static::new(&args.timeout).unwrap();
    let mut z3_solver = smtlib::Solver::new(backend_z3, false).unwrap();

    let circuit: CircuitZ3 = r1cs_to_circuit_z3(&r1cs_description);

    let sat_result = smt_check_determinacy_z3(
        &circuit,
        &args.weak_det,
        &args.assgn_dump_path,
        &args.sym_path,
        &mut z3_solver,
    )
    .unwrap();

    if args.mem_prof {
        let _ = profile_memory();
    }

    match sat_result {
        SatResult::Sat => {
            println!("The circuit is not deterministic! Two distinct witnesses exist that satisfy the constraints.");
        }
        SatResult::Unsat => println!("The system is deterministic!"),
        SatResult::Unknown => println!("The result is unknown!"),
    }

    sat_result
}

/// Processes a given R1CS file and returns an R1CS object.
///
/// This function reads data from a file specified by `r1cs_file`, then creates
/// and returns an `R1csFile` object.
///
/// # Parameters
///
/// - `r1cs_file`: A string slice that holds the path to the R1CS file.
///
/// # Returns
///
/// An `R1csFile<32>` object read from the file.
///
/// # Panics
///
/// This function will panic if it cannot read the file or parse the file
/// contents into an `R1csFile<32>` (e.g. if file doesn't exist).
///
/// # Example
///
/// ```no_run
/// # use crate::process_r1cs;
/// let r1cs_file = "path/to/your/file.r1cs";
/// let r1cs = process_r1cs(r1cs_file);
/// println!("{:?}", r1cs);
/// ```
pub fn process_r1cs(r1cs_file: &str) -> R1csFile<32> {
    // Move this out into a separate function
    let data = std::fs::read(r1cs_file).unwrap();
    let file = R1csFile::<32>::read(data.as_slice()).unwrap();

    file
}

/// Profiles the current memory usage of the application.
///
/// This function gathers and prints the current physical and virtual memory
/// usage statistics of the running process. If it fails to retrieve these
/// statistics, it will print an error message.
///
/// # Returns
///
/// An `Option<MemoryStats>` object. If the memory stats are successfully
/// retrieved, it will return `Some(MemoryStats)`, where `MemoryStats` contains
/// the current physical and virtual memory usage statistics. If it fails, it
/// will return `None`.
///
/// # Example
///
/// ```no_run
/// # use crate::profile_memory;
/// let memory_stats = profile_memory();
/// match memory_stats {
///     Some(stats) => println!("Physical memory: {}, Virtual memory: {}", stats.physical_mem, stats.virtual_mem),
///     None => println!("Couldn't retrieve memory statistics."),
/// }
/// ```
fn profile_memory() -> Option<MemoryStats> {
    // Memory profiling
    if let Some(usage) = memory_stats() {
        println!("Current physical memory usage: {}", usage.physical_mem);
        println!("Current virtual memory usage: {}", usage.virtual_mem);
    } else {
        println!("Couldn't get the current memory usage :(");
    }

    memory_stats()
}

fn clean_output(file_path: &str) -> std::io::Result<()> {
    let mut file = File::open(file_path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;

    // Add any additional substrings you want to remove in this vector
    let to_remove = vec![
        "SpecConstant(Fieldelement(Fieldelement(",
        "[WitnessVariable {",
        "WitnessAST { w: ",
        "WitnessVariable { value: ",
        "FieldElement(Identifier(Sorted(Simple(Symbol(",
        "Sort(Simple(Symbol(\"F\")))))), ",
        "), ",
        "))",
        " }",
        "{",
        ")}",
        "\"#f",
        "m21888242871839275222246405745257275088548364400416034343698204186575808495617\"",
        "value: ",
        "WitnessAST { w: ",
    ];

    let mut cleaned = contents.clone();
    for removal in to_remove {
        cleaned = cleaned.replace(removal, "");
    }

    // Remove each number following the witness name
    let re = Regex::new(r"\)\d").unwrap();
    cleaned = re.replace_all(&cleaned, ")").to_string();

    // Add newlines between witness assignments
    cleaned = cleaned.replace("Witness Assignments:", "\nWitness Assignments:");
    cleaned = cleaned.replace("\"witness", "\n\"witness");

    // Add newlines between witness names and their determinism status
    cleaned = cleaned.replace(":  (", ":\n(");
    cleaned = cleaned.replace(", (", ",\n(");
    cleaned = cleaned.replace(")d", ")\nd");
    // Cleans up deterministic status display
    cleaned = cleaned.replace("e]", "e");

    let mut file = File::create(file_path)?; // re-open the file for writing
    file.write_all(cleaned.as_bytes())?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{
        path::Path,
        process::{Command, Stdio},
    };
    use tempfile::NamedTempFile;

    /// The function is expected to process the `.r1cs` file correctly and
    /// retrieve its description. The test asserts that the processed
    /// description has some expected properties (number of wires, number of
    /// public outputs, and number of public inputs).
    #[test]
    fn test_process_r1cs() {
        let r1cs_file = "tests/TriviallyDeterministic.r1cs";
        let r1cs_description = process_r1cs(r1cs_file);

        assert_eq!(r1cs_description.header.n_wires, 3);
        assert_eq!(r1cs_description.header.n_pub_out, 1);
        assert_eq!(r1cs_description.header.n_pub_in, 1);
    }

    #[test]
    fn test_clean_output() {
        // Create a temporary file.
        let mut tmpfile: NamedTempFile = NamedTempFile::new().unwrap();

        // Write test data to the temporary file.
        writeln!(
            tmpfile,
            "SpecConstant(Fieldelement(Fieldelement( hello [WitnessVariable {{ world"
        )
        .unwrap();

        // Get the file path.
        let file_path = tmpfile.path().to_str().unwrap().to_string();

        // Clean the file.
        clean_output(&file_path).unwrap();

        // Read the cleaned data back from the file.
        let mut file = std::fs::File::open(file_path).unwrap();
        let mut contents = String::new();
        file.read_to_string(&mut contents).unwrap();

        // Assert that the cleaned data is as expected.
        assert_eq!(contents, " hello  world\n");
    }

    /// The function is expected to execute the binary with the default
    /// arguments and print the expected output. The test asserts that the
    /// output is as expected
    #[test]
    fn test_input_args() {
        let executable_path = "./target/debug/circomference";
        assert!(
            Path::new(executable_path).exists(),
            "Executable does not exist, try building first"
        );
        let mut cmd_defaults = Command::new(executable_path);
        let test_file_path = "tests/TriviallyDeterministic.r1cs";
        let output = cmd_defaults
            .arg("--r1cs-file")
            .arg(test_file_path)
            .stdout(Stdio::piped())
            .output()
            .expect("Failed to execute command");
        assert_eq!(
            String::from_utf8_lossy(&output.stdout),
            "Checking R1CS file: tests/TriviallyDeterministic.r1cs\nUsing CVC5 backend\nSetting logic to QF_FF\nThe system is deterministic!\n"
        );

        // Test with long flags
        let mut cmd = Command::new("./target/debug/circomference");
        let output_2 = cmd
            .arg("--r1cs-file")
            .arg(test_file_path)
            .arg("--weak-det")
            .arg("--assgn-dump-path")
            .arg("test/dump.txt") // Shouldn't dump if deterministic
            .arg("--timeout")
            .arg("1000")
            .stdout(Stdio::piped())
            .output()
            .expect("Failed to execute command");
        assert_eq!(
            String::from_utf8_lossy(&output_2.stdout),
            "Checking R1CS file: tests/TriviallyDeterministic.r1cs\nUsing CVC5 backend\nSetting logic to QF_FF\nThe system is deterministic!\n"
        );

        let mut cmd_check_nondet = Command::new("./target/debug/circomference");
        let test_file_path_nondet = "tests/sqrt.r1cs";
        let dump_path_nondet = "tests/dump.txt";

        // Shortcuts should also work
        let output_3 = cmd_check_nondet
            .arg("-r")
            .arg(test_file_path_nondet)
            .arg("-w")
            .arg("-a")
            .arg(dump_path_nondet)
            .arg("-t")
            .arg("1000")
            .stdout(Stdio::piped())
            .output()
            .expect("Failed to execute command");
        assert_eq!(
            String::from_utf8_lossy(&output_3.stdout),
            "Checking R1CS file: tests/sqrt.r1cs\nUsing CVC5 backend\nSetting logic to QF_FF\nDumping witness assignments to \"tests/dump.txt\"\nSetting logic to QF_FF\nThe circuit is not deterministic! Two distinct witnesses exist that satisfy the constraints.\n"
        );
        assert!(
            Path::new(executable_path).exists(),
            "Executable does not exist, try building first"
        );
        // Here, assert that test dumppath exists
        assert!(Path::new(dump_path_nondet).exists());
    }

    #[test]
    fn test_mem_prof() {
        let mem_profile = profile_memory().expect("Unable to profile memory usage");
        assert!(mem_profile.physical_mem > 0);
        assert!(mem_profile.virtual_mem > 0);
    }
}
