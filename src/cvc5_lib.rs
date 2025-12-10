use num_bigint::BigUint;
use smtlib::Backend;
use smtlib_lowlevel::backend::Cvc5Binary;

use smtlib::{theories::fieldelements::FieldElement, Bool, Logic, Model, Solver, Sort};

use std::{
    collections::{HashMap, HashSet},
    fs::{File, OpenOptions},
    io::{self, BufRead, Write},
    ops::{Add, BitAnd, Mul, Not, Range},
    path::Path,
    string::String,
};

use std::thread;

use r1cs_file::R1csFile;
use smtlib::{Error, SatResult};

/// `ConstraintAST` represents a Rank-1 Constraint System (R1CS)[https://docs.circom.io/background/background/#rank-1-constraint-system]
///
/// R1CS is a way of expressing a computation as a system of polynomial
/// equations, where each equation is of the form `(c0 . w) * (c1 . w) - (c2 .
/// w) = 0 (mod p)`.
///
/// Each of these constraints is expressed as a vector of (FieldElement, u32)
/// pairs, where the FieldElement represents a field element, and u32 is the
/// position of the coefficient in the polynomial equation.
///
/// # Fields
/// * `c0`: The first constraint vector. Represents the vector of coefficients
///   for the first part of the equation.
/// * `c1`: The second constraint vector. Represents the vector of coefficients
///   for the second part of the equation.
/// * `c2`: The third constraint vector. Represents the vector of coefficients
///   for the third part of the equation.
/// * `trusted`: A boolean that denotes whether the constraint is a part of a trusted function.
#[derive(Debug, Clone)]
pub struct ConstraintAST {
    /// The first constraint vector
    pub c0: Vec<(FieldElement, u32)>,
    /// The second constraint vector
    pub c1: Vec<(FieldElement, u32)>,
    /// The third constraint vector
    pub c2: Vec<(FieldElement, u32)>,
    /// Is this constraint a part of a trusted function?
    pub trusted: bool,
}

impl PartialEq for ConstraintAST {
    /// Checks whether or not the input constraint (acquired from user specifying a trusted r1cs)
    /// matches the corresponding constraint given a certain offset in the original r1cs.
    fn eq(&self, other: &Self) -> bool {
        let c0_match = self.c0.iter().zip(&other.c0).all(|((fe1, i1), (fe2, i2))| fe1 == fe2 && i1 == i2);
        let c1_match = self.c1.iter().zip(&other.c1).all(|((fe1, i1), (fe2, i2))| fe1 == fe2 && i1 == i2);
        let c2_match = self.c2.iter().zip(&other.c2).all(|((fe1, i1), (fe2, i2))| fe1 == fe2 && i1 == i2);

        c0_match && c1_match && c2_match
    }
}

/// The `Constraints` struct represents the complete set of Rank-1 Constraint
/// System (R1CS) constraints present in a given circuit. These constraints are
/// expressed in Abstract Syntax Tree (AST) form as a `ConstraintAST` for use by
/// the solvers.
///
/// There is a function `constraints_to_ast` that converts the constraints from
/// the parsed R1CS file to AST form.
///
/// # Fields
///
/// * `constraints`: A vector of `ConstraintAST` objects, each object represents
///   a unique R1CS constraint in the circuit.
///
/// # Example
///
/// ```rust
/// let constraints = constraints_to_ast(&file_deterministic.constraints);
/// ```
///
/// # See Also
///
/// * [ConstraintAST]: Structure representing a single R1CS constraint in AST
///   form.
#[derive(Debug, PartialEq, Clone)]
pub struct Constraints {
    /// The vector of constraints
    pub constraints: Vec<ConstraintAST>,
}

/// The `WitnessVariable` struct represents a variable in a witness for a Rank-1
/// Constraint System (R1CS). A witness is a specific assignment of values to
/// the variables that satisfy the R1CS constraints.
///
/// Each `WitnessVariable` consists of a `value`, which is a tuple containing a
/// field element and a position, and a `deterministic` flag that indicates
/// whether the variable is deterministic or not (used in determinacy
/// propagation, see propagate_determinacy)
///
/// # Fields
///
/// * `value`: A tuple consisting of a `FieldElement` and a `u32` which
///   represents the value and position of the variable in the witness
///   respectively.
/// * `deterministic`: A boolean that denotes whether the variable is
///   deterministic.
///
/// # Example
///
/// ```rust
/// let field_element = FieldElement::from(1);
/// let variable = WitnessVariable {
///     value: (field_element, 1),
///     deterministic: true,
/// };
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct WitnessVariable {
    /// The value of the variable
    pub value: (FieldElement, u32),
    /// Whether the variable is deterministic or not
    pub deterministic: bool,
}


/// The `WitnessAST` struct represents a witness for a Rank-1 Constraint System
/// (R1CS) in the Abstract Syntax Tree (AST) form. A witness is a specific
/// assignment of values to the variables that satisfies the R1CS constraints.
///
/// A constraint of the form (c0 . w) * (c1 . w) - (c2 . w) = 0 (mod p)
/// is satisfied by the witness, where `c*` are the corresponding
/// constraint vectors, and `w` is the witness vector.
///
/// The `WitnessAST` struct stores a vector of `WitnessVariable` structs, where
/// each `WitnessVariable` represents a variable in the witness, along with
/// information about whether it is deterministic (used in determinacy
/// propagation).
///
/// # Fields
///
/// * `w`: A `Vec<WitnessVariable>` that stores the variables of the witness.
///   Each `WitnessVariable` represents a variable in the witness along with
///   information about whether it is deterministic.
///
/// # Example
///
/// ```rust
/// let field_element = FieldElement::from(1); // this will depend on your specific `FieldElement` implementation
/// let variable = WitnessVariable {
///     value: (field_element, 1),
///     deterministic: true,
/// };
/// let witness = WitnessAST {
///     w: vec![variable],
/// };
/// ```
#[derive(Debug, PartialEq, Clone)]
pub struct WitnessAST {
    /// The vector of witness variables
    pub w: Vec<WitnessVariable>,
}

/// The `Circuit` struct represents an R1CS circuit. It contains information
/// about the circuit's outputs, fixed inputs, private inputs, constraints,
/// prime field, and the number of wires.
///
/// r1cs_to_circuit converts the parsed R1CS file to a `Circuit` struct.
///
/// # Fields
///
/// - `outputs`: A range representing the outputs in the circuit.
///
/// - `fixed_inputs`: A range representing the fixed (public) inputs in the
///   circuit.
///
/// - `private_inputs`: A range representing the private inputs in the circuit.
///
/// - `constraints`: An instance of `Constraints`, containing all the R1CS
///   constraints in the circuit.
///
/// - `prime`: The prime number that defines the finite field for the circuit.
///
/// - `n_wires`: The total number of wires in the circuit.
///
/// # Example
///
/// ```rust
/// use crate::r1cs::Constraints;
/// use num_bigint::BigUint;
/// use std::ops::Range;
///
/// let circuit = r1cs_to_circuit(&r1cs_file);
/// ```
#[derive(Clone)]
pub struct Circuit {
    /// The range of outputs in the circuit
    pub outputs: Range<u32>,
    /// The range of fixed inputs in the circuit
    pub fixed_inputs: Range<u32>,
    /// The range of private inputs in the circuit
    pub private_inputs: Range<u32>,
    /// The constraints in the circuit
    pub constraints: Constraints,
    /// The prime number that defines the finite field for the circuit
    pub prime: BigUint,
    /// The total number of wires in the circuit
    pub n_wires: u32,
}

/// `SatOutput` is a structure that holds the results of a satisfiability check
/// for a R1CS circuit.
///
/// If a circuit is not deterministic, there should be two different witnesses
/// that satisfy the same set of constraints. `witness_1` and `witness_2`
/// represent these two witnesses. The `model` field stores the model generated
/// by the solver which proves the non-determinism.
///
/// # Fields
///
/// - `witness_1`: The first witness that satisfies the constraints of the R1CS
///   circuit.
/// - `witness_2`: The second witness that satisfies the constraints of the R1CS
///   circuit.
/// - `model`: The model that was generated by the solver to prove
///   non-determinism.
pub struct SatOutput {
    /// The first witness that satisfies the constraints of the R1CS circuit
    pub witness_1: WitnessAST,
    /// The second witness that satisfies the constraints of the R1CS circuit
    pub witness_2: WitnessAST,
    /// The model that was generated by the solver to prove non-determinism
    pub model: Model,
}

/// Checks whether a given circuit is deterministic.
///
/// A circuit is deterministic if and only if it has exactly one solution (or
/// witness). If there are no non-fixed variables then there is exactly one
/// assignment and thus it is trivially deterministic. It's possible for the
/// circuit to be deterministic even with no constraints - e.g. if it only has
/// fixed inputs. It's also possible for the circuit to be nondeterministic with
/// no constraints - e.g. if there are any non-fixed inputs.
///
/// This function uses an SMT solver to perform the check. It first determines
/// the set of variables that could be nondeterministic and then uses the solver
/// to look for a second solution. If a second solution is found, the circuit is
/// non-deterministic.
///
/// The function also supports weak determinacy check where only the output
/// wires of the circuit are considered fixed.
///
/// # Parameters
/// - `circuit`: The circuit to check for determinacy.
/// - `witness_det`: A flag indicating whether to perform a weak deterministic
///   check.
/// - `assgn_dump`: An optional path to dump the assignment if the circuit is
///   not deterministic.
/// - `sym_file`: An optional path to the symbolic representation of the
///   circuit.
/// - `solver`: A mutable reference to the SMT solver.
/// - `cvc5_path`: An optional path to the CVC5 binary.
/// - `det_funcs`: Trusted functions that are deterministic.
///
/// # Returns
/// A `Result` which is `Ok` if the function executed successfully, and `Err`
/// otherwise. The `Ok` variant contains a `SatResult` which indicates the
/// result of the satisfiability check: `Sat`, `Unsat`, or `Unknown`.
/// ```
pub fn smt_check_determinacy<B: Backend>(
    circuit: &Circuit,
    witness_det: &bool,
    assgn_dump: &Option<String>,
    sym_file: &Option<String>,
    solver: &mut Solver<B>,
    cvc5_path: &Option<String>,
    det_funcs: &Option<Vec<Circuit>>,
) -> Result<SatResult, Error> {
    let num_vars = circuit.n_wires;
    let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

    let fixed_inputs = if *witness_det {
        circuit.outputs.end..circuit.private_inputs.end
    } else {
        circuit.outputs.end..circuit.fixed_inputs.end
    };

    // Remove the fixed wires (the first wire is always 1 and fixed)
    let _ = variable_witness_indices.remove(&0);
    for i in fixed_inputs.clone() {
        let _ = variable_witness_indices.remove(&(i as usize));
    }

    let (mut witness1, mut witness2) = check_unique_satisfying_witnesses(
        solver,
        &fixed_inputs,
        &variable_witness_indices,
        num_vars,
        sym_file,
    );

    // Propagate determinacy in trusted functions
    propagate_trusted_functions(&mut circuit.clone(), det_funcs);

    // Continue propagation of determinacy until no progress is made
    let mut iterative_propagation_unknowns: Vec<u32>;
    let mut unknown_vars = check_unknown_vars(circuit, solver, &mut witness1, &mut witness2);
    if unknown_vars.len() > 0 {
        println!("Unknown variables: {:?}, retrying", unknown_vars);
        iterative_propagation_unknowns = check_unknown_vars(circuit, solver, &mut witness1, &mut witness2);
        while unknown_vars != iterative_propagation_unknowns {
            unknown_vars = iterative_propagation_unknowns;
            iterative_propagation_unknowns = check_unknown_vars(circuit, solver, &mut witness1, &mut witness2);
        }
    }

    // Create subcircuits from the main circuit, then for each subcircuit,
    // parallelize solving for determinacy. This allows us to run multiple
    // satsolvers at the same time to speed up proving nondeterminacy
    check_determinacy_and_dump(
        assgn_dump,
        &mut witness1,
        &mut witness2,
        &unknown_vars,
        circuit,
        sym_file,
        witness_det,
        cvc5_path,
    )
}

/// Checks the variables of a circuit that are indeterminate when checked with
/// two different witnesses.
///
/// For each constraint, perform determinacy propagation for the variables (see
/// propagate_determinacy). If there exists non-deterministic variables by
/// determinacy propagation, the function attempts to use the sat solver to
/// determine whether the constraint is satisfied by the two witnesses.
///
/// # Parameters
///
/// - `circuit`: A reference to the circuit whose variables are being checked.
/// - `solver`: A mutable reference to the solver being used to check
///   satisfiability.
/// - `witness1`: A mutable reference to the first witness configuration.
/// - `witness2`: A mutable reference to the second witness configuration.
///
/// # Returns
///
/// A vector of variable indices that are unknown, i.e., cannot be classified as
/// either deterministic or non-deterministic.
///
/// # Panics
///
/// This function will panic if there is an error in processing satisfiability
/// in either of the witnesses.
fn check_unknown_vars<B: Backend>(
    circuit: &Circuit,
    solver: &mut Solver<B>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
) -> Vec<u32> {
    let mut unknown_vars = vec![];

    // This loop should continue as long as there's progress being made
    loop {
        let mut progress_made = false;

        let old_witness_1 = witness1.clone();
        let old_witness_2 = witness2.clone();

        for constraint in circuit.constraints.constraints.iter() {
            if constraint.trusted {
                // Check if any input variables in c0, c1 are deterministic
                let deterministic = constraint.c0.iter().any(|(_, i)| witness1.w[*i as usize].deterministic)
                    || constraint.c1.iter().any(|(_, i)| witness1.w[*i as usize].deterministic);
            
                // If any input variables are deterministic, set the outputs in c2 as deterministic.
                // Otherwise, do nothing.
                if deterministic {
                    constraint.c2.iter().for_each(|(_, i)| {
                        witness1.w[*i as usize].deterministic = true;
                        witness2.w[*i as usize].deterministic = true;
                    });
                }
                continue;
            }
            let non_deterministic_vars_witness1 = propagate_determinacy(constraint, witness1);
            let non_deterministic_vars_witness2 = propagate_determinacy(constraint, witness2);

            if !non_deterministic_vars_witness1.is_empty()
                && !non_deterministic_vars_witness2.is_empty()
            {
                match (
                    assert_satisfies(solver, constraint, witness1)
                        .expect("Error occurred while processing witness1"),
                    assert_satisfies(solver, constraint, witness2)
                        .expect("Error occurred while processing witness2"),
                ) {
                    (SatResult::Sat, SatResult::Sat) => mark_vars_as_non_deterministic(
                        &non_deterministic_vars_witness1,
                        witness1,
                        witness2,
                    ),
                    (SatResult::Unknown, SatResult::Unknown) => {
                        unknown_vars.extend(non_deterministic_vars_witness1);
                        unknown_vars.extend(non_deterministic_vars_witness2);
                    }
                    _ => {
                        mark_vars_as_deterministic(&non_deterministic_vars_witness1, witness1, witness2)
                    }
                };
            }

            // Check if old witnesses are different than new witnesses
            if old_witness_1 != *witness1 || old_witness_2 != *witness2 {
                progress_made = true;
            }
        }

        if !progress_made {
            break;
        }
    }

    unknown_vars
}

/// Marks the specified variables as deterministic in the given witnesses.
///
/// # Arguments
///
/// * `vars` - A set of variables to mark as deterministic.
/// * `witness1` - The first witness to modify.
/// * `witness2` - The second witness to modify.
///
/// # Example
/// ```rust
/// let mut witness1 = create_mock_witness();
/// let mut witness2 = create_mock_witness();
///
/// let mut vars = HashSet::new();
/// vars.insert(0);
/// vars.insert(1);
///
/// mark_vars_as_deterministic(&vars, &mut witness1, &mut witness2);
/// ```
fn mark_vars_as_deterministic(
    vars: &HashSet<u32>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
) {
    for var in vars {
        witness1.w[*var as usize].deterministic = true;
        witness2.w[*var as usize].deterministic = true;
    }
}

/// Marks the specified variables as nondeterministic in the given witnesses.
///
/// # Arguments
///
/// * `vars` - A set of variables to mark as nondeterministic.
/// * `witness1` - The first witness to modify.
/// * `witness2` - The second witness to modify.
///
/// # Example
/// ```rust
/// let mut witness1 = create_mock_witness();
/// let mut witness2 = create_mock_witness();
///
/// let mut vars = HashSet::new();
/// vars.insert(0);
/// vars.insert(1);
///
/// mark_vars_as_non_deterministic(&vars, &mut witness1, &mut witness2);
/// ```
fn mark_vars_as_non_deterministic(
    vars: &HashSet<u32>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
) {
    for var in vars {
        witness1.w[*var as usize].deterministic = false;
        witness2.w[*var as usize].deterministic = false;
    }
}

/// This function generates witness assignments for a given circuit. These
/// assignments are solutions for the circuit's constraints that are then
/// checked for satisfaction. If a solution is found that satisfies all
/// constraints, it's added to a `SatOutput` structure. Each `SatOutput`
/// structure consists of two witnesses and a model. A thread is spawned for
/// each constraint and each thread independently seeks to find satisfying
/// solutions. All `SatOutput` are then written to a file.
///
/// # Arguments
///
/// * `circuit: &Circuit` - A reference to the circuit. This circuit is a
///   structure which contains the constraints which need to be satisfied, along
///   with other metadata.
///
/// * `assgn_dump: &mut File` - A mutable reference to the file where results
///   should be written to.
///
/// * `sym_file: &Option<String>` - An optional string representing the symbolic
///   file. If a value is provided, the symbolic file can be used in constraint
///   satisfaction.
///
/// * `witness_det: &bool` - A boolean that determines the range of fixed
///   inputs. If set to `true`, the range is from the end of the circuit outputs
///   to the end of the private inputs. Otherwise, the range is from the end of
///   the circuit outputs to the end of the fixed inputs.
///
/// * `cvc5_path: &Option<String>` - An optional string representing the path to
///   the `cvc5` backend. `cvc5` is a popular solver for SMT problems, and can
///   be used here to check constraint satisfaction.
///
/// # Notes
///
/// The function works by creating a range of fixed inputs and then spawning a
/// thread for each constraint in the circuit. Each thread creates its own
/// solver instance, finds unique satisfying witnesses, asserts satisfaction of
/// the constraint for each witness, checks if the constraint is satisfiable,
/// and finally returns a `SatOutput` structure containing the witnesses and the
/// model. All threads are then joined and the results are written to the file
/// referenced by `assgn_dump`.
///
/// # Panics
///
/// The function might panic if the `cvc5` backend cannot be initialized, or if
/// the solver cannot satisfy the constraint, or if the file operations fail.
fn generate_witness_for_circuit(
    circuit: &Circuit,
    assgn_dump: &mut File,
    sym_file: &Option<String>,
    witness_det: &bool,
    cvc5_path: &Option<String>,
) {
    let num_vars = circuit.n_wires;

    let mut handles = vec![];

    let fixed_inputs = if *witness_det {
        circuit.outputs.end..circuit.private_inputs.end
    } else {
        circuit.outputs.end..circuit.fixed_inputs.end
    };

    for constraint in circuit.constraints.constraints.iter() {
        let prime_clone = circuit.prime.clone();
        let sym_file = sym_file.clone();
        let cvc5_path_clone = cvc5_path.clone();
        let constraint_clone = constraint.clone();

        let handle = thread::spawn(move || {
            // Redo all witness constraints (neq, satisfies constraints, etc.)
            // Solve for each constraint with each solver in parallel
            let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

            let par_fixed_inputs = fixed_inputs.start..fixed_inputs.end;

            for i in par_fixed_inputs {
                let _ = variable_witness_indices.remove(&(i as usize));
            }
            let _ = variable_witness_indices.remove(&0);

            let par_fixed_inputs = fixed_inputs.start..fixed_inputs.end;

            // Convert the (u32, u32) pairs back to (Int, u32) pairs
            let par_constraint = constraint_clone;

            let model: Model;
            // Create a new solver for each thread
            let mut cvc5_binary_path = Path::new("src/cvc5");
            if cvc5_path_clone.is_some() {
                cvc5_binary_path = Path::new(cvc5_path_clone.as_ref().unwrap());
            }
            let par_backend_cvc5 = Cvc5Binary::new(cvc5_binary_path).unwrap();
            // No need for verbose parallel solving (unless in debug)
            let mut par_solver_cvc5 = Solver::new(par_backend_cvc5, false).unwrap();
            par_solver_cvc5.set_logic(Logic::QF_FF).unwrap();
            par_solver_cvc5.set_field_order(&prime_clone).unwrap();
            let (par_witness1, par_witness2) = check_unique_satisfying_witnesses(
                &mut par_solver_cvc5,
                &par_fixed_inputs,
                &variable_witness_indices,
                num_vars,
                &sym_file,
            );
            let _ = assert_satisfies(&mut par_solver_cvc5, &par_constraint, &par_witness1);
            let _ = assert_satisfies(&mut par_solver_cvc5, &par_constraint, &par_witness2);

            let _ = par_solver_cvc5.check_sat().unwrap();
            model = par_solver_cvc5.get_model().unwrap();
            SatOutput {
                witness_1: par_witness1,
                witness_2: par_witness2,
                model,
            }
        });
        handles.push(handle);
    }

    let results: Vec<SatOutput> = handles
        .into_iter()
        .map(|handle| handle.join().unwrap())
        .collect();

    for result in results {
        write_results_to_file(assgn_dump, result);
    }
}

/// Writes the results of constraint satisfaction to a specified file.
///
/// # Arguments
///
/// * `dump_file: &mut File` - A mutable reference to the file where the results
///   should be written.
///
/// * `result: SatOutput` - The `SatOutput` structure that contains two
///   witnesses and a model resulting from the constraint satisfaction process.
///
/// # Behavior
///
/// The function writes the `SatOutput` data in the format: "Witness 1:
/// _witness1_\nWitness 2: _witness2_\nWitness Assignments:\n_model_\n". If the
/// write operation fails for any reason, the function will panic with the
/// message "Unable to write to file".
///
/// # Panics
///
/// The function will panic if it's unable to write to the `dump_file`.
fn write_results_to_file(dump_file: &mut File, result: SatOutput) {
    write!(
        dump_file,
        "Witness 1: {:?}\nWitness 2: {:?}\nWitness Assignments:\n{:?}\n",
        result.witness_1, result.witness_2, result.model,
    )
    .expect("Unable to write to file");
}

/// Checks determinacy of the witness, optionally dumps the witness assignments
/// to a file, and returns the satisfiability result of a circuit.
///
/// # Arguments
///
/// * `assgn_dump: &Option<String>` - An optional reference to a String
///   containing the path to the file where witness assignments should be
///   dumped, if the witnesses are non-deterministic.
///
/// * `witness1: &mut WitnessAST` - A mutable reference to the first witness to
///   be checked for determinacy.
///
/// * `witness2: &mut WitnessAST` - A mutable reference to the second witness to
///   be checked for determinacy.
///
/// * `unknown_vars: &[u32]` - A reference to a slice of unknown variables in
///   the circuit.
///
/// * `circuit: &Circuit` - A reference to the circuit for which the determinacy
///   is being checked.
///
/// * `sym_file: &Option<String>` - An optional reference to a String containing
///   the symbolic file's path.
///
/// * `witness_det: &bool` - A boolean flag indicating if weak determinacy is
///   being checked.
///
/// * `cvc5_path: &Option<String>` - An optional reference to a String
///   containing the path to the CVC5 solver.
///
/// # Returns
///
/// Returns a `Result` holding `SatResult`, which could be one of `Unsat`,
/// `Unknown`, or `Sat`. Returns `Error` if any error occurs.
///
/// # Behavior
///
/// If both witnesses are deterministic and a path for dumping is provided, the
/// function dumps the witness assignments to the specified file. It then checks
/// if the witnesses are deterministic. If they are, the function returns
/// `SatResult::Unsat`. If they are not, and there are no unknown variables in
/// the circuit, the function returns `SatResult::Sat`. Otherwise, it returns
/// `SatResult::Unknown`.
///
/// # Panics
///
/// This function will panic if it's unable to create the file specified by
/// `assgn_dump`. The reason for failure could include insufficient permissions,
/// lack of disk space, or other I/O-related errors.
#[allow(clippy::too_many_arguments)]
fn check_determinacy_and_dump(
    assgn_dump: &Option<String>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
    unknown_vars: &[u32],
    circuit: &Circuit,
    sym_file: &Option<String>,
    witness_det: &bool,
    cvc5_path: &Option<String>,
) -> Result<SatResult, Error> {
    let is_deterministic =
        witness1.w.iter().all(|w| w.deterministic) && witness2.w.iter().all(|w| w.deterministic);
    if assgn_dump.is_some() && !is_deterministic {
        let dump_path = Path::new(assgn_dump.as_ref().unwrap());
        println!("Dumping witness assignments to {:?}", dump_path);
        let mut dump_file = OpenOptions::new()
            .write(true)
            .create(true)
            .append(true)
            .open(dump_path)
            .expect("Unable to create file");
        generate_witness_for_circuit(circuit, &mut dump_file, sym_file, witness_det, cvc5_path);
    }
    if is_deterministic {
        Ok(SatResult::Unsat)
    } else if !unknown_vars.is_empty() {
        Ok(SatResult::Unknown)
    } else {
        Ok(SatResult::Sat)
    }
}

/// Checks determinacy of the witness, optionally dumps the witness assignments
/// to a file, and returns the satisfiability result of a circuit.
///
/// # Arguments
///
/// * `assgn_dump: &Option<String>` - An optional reference to a String
///   containing the path to the file where witness assignments should be
///   dumped, if the witnesses are non-deterministic.
///
/// * `witness1: &mut WitnessAST` - A mutable reference to the first witness to
///   be checked for determinacy.
///
/// * `witness2: &mut WitnessAST` - A mutable reference to the second witness to
///   be checked for determinacy.
///
/// * `unknown_vars: &[u32]` - A reference to a slice of unknown variables in
///   the circuit.
///
/// * `circuit: &Circuit` - A reference to the circuit for which the determinacy
///   is being checked.
///
/// * `sym_file: &Option<String>` - An optional reference to a String containing
///   the symbolic file's path.
///
/// * `witness_det: &bool` - A boolean flag indicating if weak determinacy is
///   being checked.
///
/// * `cvc5_path: &Option<String>` - An optional reference to a String
///   containing the path to the CVC5 solver.
///
/// # Returns
///
/// Returns a `Result` holding `SatResult`, which could be one of `Unsat`,
/// `Unknown`, or `Sat`. Returns `Error` if any error occurs.
///
/// # Behavior
///
/// If both witnesses are deterministic and a path for dumping is provided, the
/// function dumps the witness assignments to the specified file. It then checks
/// if the witnesses are deterministic. If they are, the function returns
/// `SatResult::Unsat`. If they are not, and there are no unknown variables in
/// the circuit, the function returns `SatResult::Sat`. Otherwise, it returns
/// `SatResult::Unknown`.
///
/// # Panics
///
/// This function will panic if it's unable to create the file specified by
/// `assgn_dump`. The reason for failure could include insufficient permissions,
/// lack of disk space, or other I/O-related errors.
fn check_unique_satisfying_witnesses<B: Backend>(
    solver: &mut Solver<B>,
    fixed_inputs: &Range<u32>,
    witness_indices: &HashSet<usize>,
    num_vars: u32,
    sym_file: &Option<String>,
) -> (WitnessAST, WitnessAST) {
    // Create the witness using the solver such that
    // 1. Each witness is unique
    // 2. The witnesses both satisfy the constraints
    // Assert also that each member of the witness is between 0 and the prime int
    let mut witness_1 = WitnessAST {
        w: Vec::with_capacity(num_vars as usize),
    };
    let mut witness_2 = WitnessAST {
        w: Vec::with_capacity(num_vars as usize),
    };

    let mut variable_names: Vec<String> = if let Some(file) = sym_file.as_ref() {
        match get_variable_names(Path::new(file)) {
            Ok(names) => names,
            Err(e) => {
                eprintln!("Failed to get variable names: {}", e);
                vec![]
            }
        }
    } else {
        vec![]
    };
    // The first variable be the fixed wire
    variable_names.insert(0, "fixed_1_wire".to_string());

    for i in 0..num_vars {
        let default_name_1 = format!("wire_{}", i);
        let name_1 = variable_names
            .get(i as usize)
            .map(|name| name.as_str())
            .unwrap_or(&default_name_1);

        let mut witness_var_1 = WitnessVariable {
            value: (*FieldElement::from_name(format!("witness_1_{}", name_1)), i),
            deterministic: false,
        };

        let default_name_2 = format!("wire_{}", i);
        let name_2 = variable_names
            .get(i as usize)
            .map(|name| name.as_str())
            .unwrap_or(&default_name_2);

        let mut witness_var_2: WitnessVariable;
        if witness_indices.contains(&(i as usize)) {
            witness_var_2 = WitnessVariable {
                value: (*FieldElement::from_name(format!("witness_2_{}", name_2)), i),
                deterministic: false,
            };
        } else {
            // Make the other assignments same for both witnesses
            witness_var_1.deterministic = true;
            witness_var_2 = witness_var_1.clone();
        };

        if fixed_inputs.contains(&i) || i == 0 {
            witness_var_1.deterministic = true;
            witness_var_2.deterministic = true;
        }
        witness_1.w.push(witness_var_1);
        witness_2.w.push(witness_var_2);
    }

    // Assert that first wire is 1; this fixed wire is deterministic
    let _ = solver.assert(witness_1.w[0].value.0._eq(FieldElement::from(1)));
    let _ = solver.assert(witness_2.w[0].value.0._eq(FieldElement::from(1)));

    // Assert that wires outside of fixed assignments are different
    assert_witnesses_neq(&witness_1.w, &witness_2.w, witness_indices, solver);

    (witness_1, witness_2)
}

/// Checks that the witness components of `witness_1` and `witness_2` are not
/// equal.
///
/// # Arguments
///
/// * `witness_1: &[WitnessVariable]` - A slice containing the
///   `WitnessVariable`s for the first witness.
///
/// * `witness_2: &[WitnessVariable]` - A slice containing the
///   `WitnessVariable`s for the second witness.
///
/// * `witness_indices: &HashSet<usize>` - A reference to a HashSet containing
///   indices of the witnesses.
///
/// * `solver: &mut Solver<B>` - A mutable reference to the solver object that
///   is used to assert the constraints.
///
/// # Behavior
///
/// This function asserts the inequality of non-fixed components of two
/// witnesses using the provided solver. First, it finds the non-fixed
/// components of the witnesses and collects them into vectors.
/// Next, it converts these vectors into HashMaps for efficient lookup, with
/// keys being positions of variables and values being the actual variables.
/// Then, it forms the union of all the positions in both the witnesses.
/// Finally, it asserts the inequality of the components at each of these
/// positions and passes this assertion to the solver.
///
/// Note: The function uses a sparse representation for the vector's values,
/// thus, if a position doesn't have a value, it defaults to 0.
///
/// If a variable is missing for a non-zero constraint index, the function will
/// panic with an error message.
fn assert_witnesses_neq<B: Backend>(
    witness_1: &[WitnessVariable],
    witness_2: &[WitnessVariable],
    witness_indices: &HashSet<usize>,
    solver: &mut Solver<B>,
) {
    let assertion = Bool::from(true); // Default: True, i.e. witnesses are unique.

    let mut variable_wires_1: Vec<(FieldElement, u32)> = vec![];
    let mut variable_wires_2: Vec<(FieldElement, u32)> = vec![];

    for (coefficient_1, coefficient_2) in witness_1.iter().zip(witness_2) {
        if witness_indices.contains(&(coefficient_1.value.1 as usize)) {
            variable_wires_1.push(coefficient_1.value);
        }
        if witness_indices.contains(&(coefficient_2.value.1 as usize)) {
            variable_wires_2.push(coefficient_2.value);
        }
    }

    // Convert tuples to HashMaps for efficient lookup
    let map_witness_1: HashMap<u32, FieldElement> = variable_wires_1
        .iter()
        .map(|(val, pos)| (*pos, *val))
        .collect();
    let map_witness_2: HashMap<u32, FieldElement> = variable_wires_2
        .iter()
        .map(|(val, pos)| (*pos, *val))
        .collect();

    // get union of positions
    let all_positions: HashSet<u32> = map_witness_1
        .keys()
        .chain(map_witness_2.keys())
        .cloned()
        .collect();

    // due to the sparse representation of the vectors' values, values default to 0
    // if it doesn't have a u32 position value.
    let witnesses_identical = all_positions.iter().fold(assertion, |acc, pos| {
        let witness_1_value = map_witness_1
            .get(pos)
            .expect("Witness variable is missing for a nonzero constraint index");
        let witness_2_value = map_witness_2
            .get(pos)
            .expect("Witness variable is missing for a nonzero constraint index");
        acc.bitand(witness_1_value._eq(*witness_2_value))
    });

    let _ = solver.assert(witnesses_identical.not());
}

/// Asserts that a witness satisfies a given constraint.
///
/// # Arguments
///
/// * `solver: &mut Solver<B>` - A mutable reference to the solver object that
///   is used to assert the constraints.
///
/// * `constraint: &ConstraintAST` - A reference to the constraint that the
///   witness is supposed to satisfy.
///
/// * `witness: &WitnessAST` - A reference to the witness that is supposed to
///   satisfy the constraint.
///
/// # Behavior
///
/// This function calculates the dot product of the vectors formed by the
/// constraint coefficients and the witness. Then, it asserts that the dot
/// product of the first and second vectors plus the third equals zero (mod p).
///
/// After asserting the above constraint, the function checks whether the solver
/// can find a solution that satisfies the asserted constraints. A system is
/// non-deterministic if and only if there are two distinct assignments to the
/// non-fixed variables that satisfy the constraints.
///
/// # Returns
///
/// Returns a `SatResult` which indicates whether a satisfying solution was
/// found (Sat), wasn't found (Unsat), or it's unknown whether a satisfying
/// solution exists (Unknown).
///
/// # Errors
///
/// Returns an `Error` if there is a problem asserting the constraint or
/// checking the satisfiability.
fn assert_satisfies<B: Backend>(
    solver: &mut Solver<B>,
    constraint: &ConstraintAST,
    witness: &WitnessAST,
) -> Result<SatResult, Error> {
    let dot_c0_w = dot_product(&constraint.c0, &witness.w);
    let dot_c1_w = dot_product(&constraint.c1, &witness.w);
    let dot_c2_w = dot_product(&constraint.c2, &witness.w);

    solver.assert(
        dot_c0_w
            .mul(dot_c1_w)
            .add(dot_c2_w)
            ._eq(FieldElement::from(0)),
    )?;

    solver.check_sat()
}

/// Converts a vector of field elements parsed from an R1CS file to a vector of
/// CVC5 AST nodes.
///
/// # Arguments
///
/// * `elements: &[(r1cs_file::FieldElement<32>, u32)]` - A reference to a
///   vector of tuples, where each tuple contains a field element (parsed from
///   an R1CS file) and a corresponding index.
///
/// # Behavior
///
/// This function iterates over each tuple in the input vector, converts the
/// field element into a BigUint, then converts the BigUint to an SMT field
/// element. The index of the element is kept as it is. A new vector of tuples
/// is returned where each tuple contains an SMT field element and a
/// corresponding index.
///
/// # Returns
///
/// Returns a `Vec<(FieldElement, u32)>` which is a vector of tuples, where each
/// tuple contains a field element represented as an SMT node and a
/// corresponding index.
///
/// # Notes
///
/// This function assumes that the `r1cs_file::FieldElement` can be converted
/// into a `BigUint` using the `from_bytes_le` function, and that the `BigUint`
/// can be converted into a SMT field element using the
/// `biguint_to_smt_field_element` function.
fn field_element_to_ast(
    elements: &[(r1cs_file::FieldElement<32>, u32)],
) -> Vec<(FieldElement, u32)> {
    elements
        .iter()
        .map(|(field_element, u)| {
            let int_field_element = BigUint::from_bytes_le(field_element.as_slice());
            let field_element = biguint_to_smt_field_element(int_field_element);
            (field_element, *u)
        })
        .collect()
}

/// Labels trusted witness variables as deterministic.
///
/// Suppose we know that a function f(x) = y is deterministic.
/// If we see the same constraints somewhere else, we can mark deterministic
/// input variables deterministic instead of individually evaluating constraints
fn propagate_trusted_functions(original_circuit: &mut Circuit, det_funcs: &Option<Vec<Circuit>>) {
    let original_constraints = &mut original_circuit.constraints.constraints;
    if det_funcs.is_none() {
        return;
    }
    let det_funcs = det_funcs.as_ref().unwrap();
    for det_func in det_funcs {
        // First, check whether or not a constraint is a subset of the original constraints
        // If it is, mark the constraint as trusted and continue
        let input_constraints = &det_func.constraints.constraints;
        let _ = check_corresponding_constraints(original_constraints, input_constraints);
    }
}

/// Checks whether or not the input constraint (acquired from user specifying a trusted r1cs)
/// occurs in the original set of constraints.
/// The input constraints will have the same constraint values, but with different indices.
/// The indices will be offset by the length of the original constraints.
fn check_corresponding_constraints(original_constraints: &mut Vec<ConstraintAST>, input_constraints: &Vec<ConstraintAST>) -> bool {
    // TODO: Incorporate more test examples to ensure that offset for the input constraints is consistent
    let offset = input_constraints.len() as u32;
    // Exclude the 0 wire when shifting
    let shifted_constraints: Vec<ConstraintAST> = input_constraints.into_iter().map(|input_constraint| {
        ConstraintAST {
            c0: input_constraint.c0.clone().into_iter().map(|(field_element, index)| (field_element, if index > 1 { index + offset } else { index })).collect(),
            c1: input_constraint.c1.clone().into_iter().map(|(field_element, index)| (field_element, if index > 1 { index + offset } else { index })).collect(),
            c2: input_constraint.c2.clone().into_iter().map(|(field_element, index)| (field_element, if index > 1 { index + offset } else { index })).collect(),
            trusted: true,
        }
    }).collect();

    for shifted_constraint in &shifted_constraints {
        if !original_constraints.contains(&shifted_constraint) {
            return false;
        }
    }

    // If the constraints are all contained in the original constraints, then the function is trusted
    // Mark the matching constraint in the original function as trusted
    for shifted_constraint in &shifted_constraints {
        let index = original_constraints.iter().position(|original_constraint| original_constraint == shifted_constraint).unwrap();
        original_constraints[index].trusted = true;
    }

    true
}

/// Converts the constraint descriptions parsed from an R1CS file to CVC5 AST
/// nodes.
///
/// # Arguments
///
/// * `constraints: &r1cs_file::Constraints<32>` - A reference to the
///   constraints parsed from an R1CS file.
///
/// # Behavior
///
/// This function iterates over each constraint in the input constraints,
/// converting each one to an `ConstraintAST`. This is done by calling the
/// `field_element_to_ast` function on each part of the constraint (c0, c1, c2).
/// These new AST constraints are then added to a `Constraints` object.
///
/// # Returns
///
/// Returns a `Constraints` object which contains a vector of constraints
/// represented as `ConstraintAST` objects.
///
/// # Notes
///
/// This function assumes that the `r1cs_file::Constraints` object can be
/// iterated over, and that each constraint can be converted into a
/// `ConstraintAST` object by calling the `field_element_to_ast` function on
/// each part of the constraint.
fn constraints_to_ast(constraints: &r1cs_file::Constraints<32>) -> Constraints {
    let mut ast_constraints = Constraints {
        constraints: vec![],
    };
    for constraint in &constraints.0 {
        let ast_constraint = ConstraintAST {
            c0: field_element_to_ast(&constraint.0),
            c1: field_element_to_ast(&constraint.1),
            c2: field_element_to_ast(&constraint.2),
            // Constraints should never be trusted by default
            trusted: false,
        };
        ast_constraints.constraints.push(ast_constraint);
    }
    ast_constraints
}

/// This function returns all variables that co-occur with a specified variable
/// within the same constraint of a system.
///
/// Co-occurrence is defined as appearing within the same component (`c0`, `c1`,
/// or `c2`) of a given constraint.
///
/// # Arguments
///
/// * `constraint` - A reference to a `ConstraintAST` object representing the
///   constraint to be checked.
/// * `var_index` - A reference to a `u32` indicating the index of the variable
///   of interest.
///
/// # Returns
///
/// Returns a `Vec<(FieldElement, u32)>` that includes all variables that
/// co-occur with the specified variable in the given constraint. Each tuple
/// contains a `FieldElement` and a `u32` index.
///
/// # Examples
///
/// ```rust
/// let co_occurring_variables = return_coocurring_variables_in_constraint_system(&constraint, &var_index);
/// ```
///
/// Note: This function operates on individual constraints, not on a complete
/// system of constraints. To find all the co-occurring variables for a specific
/// variable across an entire system, you may need to iterate over all
/// constraints in the system.
fn return_coocurring_variables_in_constraint_system(
    constraint: &ConstraintAST,
    var_index: &u32,
) -> Vec<(FieldElement, u32)> {
    let mut variables = vec![];
    if constraint.c0.iter().any(|(_, index)| index == var_index) {
        variables.extend(constraint.c0.clone());
    }
    if constraint.c1.iter().any(|(_, index)| index == var_index) {
        variables.extend(constraint.c1.clone());
    }
    if constraint.c2.iter().any(|(_, index)| index == var_index) {
        variables.extend(constraint.c2.clone());
    }
    variables
}

/// Converts a BigUint number to a SMT field element.
///
/// # Arguments
///
/// * `x` - The `BigUint` to be converted into a `FieldElement`.
///
/// # Returns
///
/// Returns a `FieldElement` representing the `BigUint` number in the SMT field.
///
/// # Examples
///
/// ```rust
/// let smt_field_element = biguint_to_smt_field_element(big_uint_number);
/// ```
///
/// Note: This function is required for converting numbers obtained from R1CS
/// file parsing or other sources into FieldElements that can be used in the SMT
/// solver.

fn biguint_to_smt_field_element(x: BigUint) -> FieldElement {
    FieldElement::from(x)
}

/// Propagates determinacy of variables across a given constraint system and
/// witness.
///
/// The function evaluates the deterministic nature of variables in the `c2`
/// vector of the constraint. It iterates over the `c2` vector, and for each
/// variable, it calls the helper function
/// `return_coocurring_variables_in_constraint_system` to determine if the
/// variable co-occurs with other variables in the constraint system.
///
/// If a variable in `c2` does not co-occur with others and is not present in
/// `c0` or `c1` vectors, it's considered deterministic and added to the
/// deterministic variables set. Otherwise, it's added to the non-deterministic
/// variables set.
///
/// After all variables in `c2` have been evaluated, the function updates the
/// witness with the determinacy information and returns the set of
/// non-deterministic variables.
///
/// # Arguments
///
/// * `constraint: &ConstraintAST` - A reference to a ConstraintAST object,
///   representing a constraint system.
/// * `witness: &mut WitnessAST` - A mutable reference to a WitnessAST object,
///   containing the assignment of variables.
///
/// # Returns
///
/// * `HashSet<u32>` - This function returns a `HashSet<u32>` that contains the
///   indexes of the non-deterministic variables in the constraint system.
fn propagate_determinacy(constraint: &ConstraintAST, witness: &mut WitnessAST) -> HashSet<u32> {
    let mut deterministic_variables = HashSet::new();
    let mut non_deterministic_variables = HashSet::new();

    for (_, var_index) in &constraint.c2 {
        classify_variables(constraint, var_index, &mut deterministic_variables, &mut non_deterministic_variables);
    }
    for witness_variable in &mut witness.w {
        if deterministic_variables.contains(&witness_variable.value.1) {
            witness_variable.deterministic = true;
        }
    }

    non_deterministic_variables
}

fn classify_variables(
    constraint: &ConstraintAST, 
    var_index: &u32,
    deterministic_variables: &mut HashSet<u32>,
    non_deterministic_variables: &mut HashSet<u32>
) {
    let coocurring_variables =
        return_coocurring_variables_in_constraint_system(constraint, var_index);
    if coocurring_variables.len() == 1
        && !constraint
            .c0
            .iter()
            .any(|(_, var_index_c0)| var_index_c0 == var_index)
        && !constraint
            .c1
            .iter()
            .any(|(_, var_index_c1)| var_index_c1 == var_index)
    {
        let _ = deterministic_variables.insert(*var_index);
    } else {
        let _ = non_deterministic_variables.insert(*var_index);
    }
}

/// The `r1cs_to_circuit` function takes a description of a R1CS file and
/// converts it into a `Circuit` object.
///
/// According to the R1CS file specification, the wires are organized in a
/// contiguous manner. The first wire is a fixed wire, followed by public outputs, then public inputs, and finally private inputs. Find more information [here](https://github.com/iden3/r1csfile/blob/master/doc/r1cs_bin_format.md)
///
/// It converts each constraint in the R1CS file (given by three linear
/// combinations) into `ConstraintAST` instances, which are then used to build
/// the `Circuit`.
///
/// # Parameters
///
/// - `r1cs_description`: A reference to a `R1csFile` instance, which contains
///   the description of the R1CS file.
///
/// # Returns
///
/// A `Circuit` object representing the R1CS circuit described by the input R1CS
/// file.
///
/// # Example
///
/// ```rust
/// let r1cs_description = process_r1cs("path_to_r1cs_file");
/// let circuit = r1cs_to_circuit(&r1cs_description);
/// ```
///
/// # Panics
///
/// This function will panic if there's an error in processing the R1CS file.
pub fn r1cs_to_circuit(r1cs_description: &R1csFile<32>) -> Circuit {
    let prime = BigUint::from_bytes_le(r1cs_description.header.prime.as_slice());

    let outputs_end_index = r1cs_description.header.n_pub_out + 1;
    let fixed_inputs_end_index =
        r1cs_description.header.n_pub_in + r1cs_description.header.n_pub_out + 1;

    Circuit {
        outputs: 1..outputs_end_index,
        fixed_inputs: outputs_end_index..fixed_inputs_end_index,
        private_inputs: fixed_inputs_end_index..r1cs_description.header.n_wires,
        // Using the z3 solver, we construct equations of the form (c0 . w) * (c1 . w) - (c2 . w) =
        // 0 (mod p) By turning each constraint (given by three linear combinations) into
        // AST::Int() nodes.
        constraints: constraints_to_ast(&r1cs_description.constraints),
        prime,
        n_wires: r1cs_description.header.n_wires,
    }
}

/// Fetches variable names from a `.sym` file to facilitate pretty variable
/// naming when dumping satisfying witness assignments.
///
/// This function reads the file line by line, each line is then split by comma
/// `,` character, if the split line contains at least 4 parts, the fourth part
/// which is presumed to be the variable name is pushed into a vector of
/// variable names.
///
/// # Arguments
///
/// * `path: &Path` - A reference to a Path object, representing the path to the
///   `.sym` file.
///
/// # Returns
///
/// * This function returns a `Vec<String>` of variable names when the operation
///   is successful.
/// It returns an `Err` variant of `io::Result` if there's an issue opening or
/// reading from the file.
///
/// # Errors
///
/// This function will return an error if the `.sym` file cannot be opened or
/// read.
fn get_variable_names(path: &Path) -> io::Result<Vec<String>> {
    let file = File::open(path)?;
    let reader = io::BufReader::new(file);

    let mut variable_names = Vec::new();

    for line in reader.lines() {
        let line = line?;
        let parts: Vec<&str> = line.split(',').collect();
        if parts.len() >= 4 {
            variable_names.push(parts[3].to_string());
        }
    }

    Ok(variable_names)
}

/// Computes the dot product of two vectors of tuples, where each tuple
/// represents a value and its position.
///
/// This function takes two vectors of tuples as arguments: `constraint` and
/// `witness`. The `constraint` vector contains tuples of type `(FieldElement,
/// u32)`, where `FieldElement` is the value at the position represented by
/// `u32`. The `witness` vector contains `WitnessVariable` objects.
///
/// The dot product is computed by iterating over unique keys (positions) from
/// both vectors and accumulating the product of corresponding values (field
/// elements) from each vector.
///
/// # Arguments
///
/// * `constraint: &[(FieldElement, u32)]` - A reference to a vector of tuples
///   `(FieldElement, u32)`,
/// representing the constraint.
/// * `witness: &[WitnessVariable]` - A reference to a slice of
///   `WitnessVariable` objects, representing the witness.
///
/// # Returns
///
/// * `FieldElement` - The result of the dot product operation.
///
/// # Panic
///
/// This function may panic if a witness variable is missing for a nonzero
/// constraint index.
fn dot_product(constraint: &[(FieldElement, u32)], witness: &[WitnessVariable]) -> FieldElement {
    let dot_product = FieldElement::from(0);

    // Create an array of witness values from the witness variables
    let witness_values: Vec<(FieldElement, u32)> = witness.iter().map(|w| w.value).collect();

    let map_constraint: HashMap<u32, FieldElement> =
        constraint.iter().map(|(val, pos)| (*pos, *val)).collect();
    let map_witness: HashMap<u32, FieldElement> = witness_values
        .iter()
        .map(|(val, pos)| (*pos, *val))
        .collect();

    let zero = FieldElement::from(0);
    let dot_product = map_constraint
        .keys()
        .chain(map_witness.keys())
        .collect::<HashSet<_>>() // this ensures that the positions are unique to avoid keys getting processed twice when
        // chaining
        .iter() // next, we can use the iterator directly
        .fold(dot_product, |acc, pos| {
            let constraint_value = map_constraint.get(pos).unwrap_or(&zero);
            let witness_value = map_witness
                .get(pos)
                .expect("Witness variable is missing for a nonzero constraint index");
            acc.add(constraint_value.mul(*witness_value))
        });

    dot_product
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests whether or not we can find a result for a trivially non-deterministic
    // R1CS file (i.e. one that has multiple satisfying assignments)
    // Has no constraints, so should be satisfiable
    fn create_mock_witness() -> WitnessAST {
        WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 3),
                    deterministic: false,
                },
            ],
        }
    }

    #[test]
    fn test_trivially_nondeterministic() {
        let data_nondeterministic = std::fs::read("tests/multiplier_insecure.r1cs").unwrap();
        let file_nondeterministic = R1csFile::<32>::read(data_nondeterministic.as_slice()).unwrap();
        println!("Header: {:?}", file_nondeterministic.header);
        println!("Constraints: {:?}", file_nondeterministic.constraints);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = false;
        let assgn_dump_path = None;
        let sym_file = None;
        let det_funcs = None;

        let sat_result_cvc5 = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check_cvc5 = format!("{:?}", sat_result_cvc5);
        println!("Debug sat result {}", debug_sat_check_cvc5);

        let expected_sat_cvc_5 = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check_cvc5, expected_sat_cvc_5);
    }

    // Tests whether or not we can find a result for a non-deterministic R1CS file
    // (i.e. a constrained circuit that has multiple satisfying assignments due to
    // there only being 1 logic gate)
    #[test]
    fn test_nondeterministic() {
        // Multiplexer test case
        let data_nondeterministic = std::fs::read("tests/Decoder@multiplexer.r1cs").unwrap();
        let file_nondeterministic = R1csFile::<32>::read(data_nondeterministic.as_slice()).unwrap();
        println!("Header: {:?}", file_nondeterministic.header);
        println!("Constraints: {:?}", file_nondeterministic.constraints);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();
        let circuit = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = false;
        let assgn_dump_path = None;
        let sym_file = None;
        let det_funcs = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);

        // Sqrt test case
        let data_nondeterministic_sqrt = std::fs::read("tests/sqrt.r1cs").unwrap();
        let file_nondeterministic_sqrt =
            R1csFile::<32>::read(data_nondeterministic_sqrt.as_slice()).unwrap();
        println!("Header: {:?}", file_nondeterministic_sqrt.header);
        println!("Constraints: {:?}", file_nondeterministic.constraints);

        let backend_sqrt = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver_sqrt = smtlib::Solver::new(backend_sqrt, true).unwrap();
        solver_sqrt.set_logic(Logic::QF_FF).unwrap();
        solver_sqrt.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit_sqrt = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());
        let det_funcs = None;

        let sat_result_sqrt = smt_check_determinacy(
            &circuit_sqrt,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver_sqrt,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result_sqrt);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    // A demonstration of how circomference can help find bugs in real time
    // This test case demonstrates that removing constriant gates from the IsZero
    // circuit (from circomlib) produces a non-deterministic circuit.
    // A public input `out` only returns 1 if the input `in` is 0.
    // `out` is initialized to a constraint (-`in` * 1 / `in` + 1), and constrained
    // to `in * out === 0` deterministically. Therefore, if we remove the
    // initializing constraint gate, there will be multiple, unintended solutions to
    // the circuit. This means that there are multiple witness assignments such
    // that
    #[test]
    fn test_nondeterministic_is_zero_circuit() {
        let data_nondeterministic = std::fs::read("tests/is_zero_insecure.r1cs").unwrap();
        let file_nondeterministic = R1csFile::<32>::read(data_nondeterministic.as_slice()).unwrap();
        println!("Header: {:?}", file_nondeterministic.header);
        println!("Constraints: {:?}", file_nondeterministic.constraints);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = true;
        let assgn_dump_path = Some("tests/dump.txt".to_string());
        let sym_file = Some("circomference/tests/is_zero_insecure.sym".to_string());
        let det_funcs = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_not_deterministic_under_only_witness_determinacy_check() {
        let data_nondeterministic = std::fs::read("tests/IsZero@comparators.r1cs").unwrap();
        let file_nondeterministic = R1csFile::<32>::read(data_nondeterministic.as_slice()).unwrap();
        println!("Header: {:?}", file_nondeterministic.header);
        println!("Constraints: {:?}", file_nondeterministic.constraints);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = false;
        let assgn_dump_path = None;
        let sym_file = None;
        let det_funcs = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_nondet_with_symfile_and_dump_path() {
        let data_nondeterministic = std::fs::read("tests/monty.r1cs").unwrap();
        let file_nondeterministic = R1csFile::<32>::read(data_nondeterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_nondeterministic.header);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_nondeterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = false;
        let assgn_dump_path = Some("tests/dump.txt".to_string());
        let sym_file = Some("circomference/tests/monty.sym".to_string());
        let det_funcs = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Tests whether or not we can find a result for a deterministic R1CS file
    // (i.e. one that has only one satisfying assignment)
    // Trivially deterministic: has all fixed variables, no non-fixed
    #[test]
    fn test_trivially_deterministic() {
        let data_deterministic = std::fs::read("tests/TriviallyDeterministic.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug File: {:?}", file_deterministic);
        // println!("Debug Header: {:?}", file_deterministic.header);
        // println!("Debug Wiremap: {:?}", file_deterministic.map);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_deterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = true;
        let assgn_dump_path = None;
        let sym_file = None;
        let det_funcs = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Unsat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_deterministic_under_output_determinacy_check() {
        let data_deterministic = std::fs::read("tests/IsZero@comparators.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_deterministic.header);
        println!(
            "Debug File Constraints: {:?}",
            file_deterministic.constraints
        );

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_deterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = true;
        let assgn_dump_path = None;
        let det_funcs = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Unsat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_deterministic_with_trusted_function() {
        let data_deterministic = std::fs::read("tests/BigIsZero.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_deterministic.header);
        println!(
            "Debug File Constraints: {:?}",
            file_deterministic.constraints
        );

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let circuit = r1cs_to_circuit(&file_deterministic);
        let cvc5_path = Some("src/cvc5".to_string());

        let witness_det = true;
        let assgn_dump_path = None;
        let sym_file = None;

        let trusted_data_deterministic = std::fs::read("tests/IsZero@comparators.r1cs").unwrap();
        let trusted_file_deterministic = R1csFile::<32>::read(trusted_data_deterministic.as_slice()).unwrap();
        let trusted_circuit = r1cs_to_circuit(&trusted_file_deterministic);
        let det_funcs = Some(vec![trusted_circuit]);

        let sat_result = smt_check_determinacy(
            &circuit,
            &witness_det,
            &assgn_dump_path,
            &sym_file,
            &mut cvc5_solver,
            &cvc5_path,
            &det_funcs,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Unsat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied
    // The dot product with the witness and constraint here would be
    // (3 * 1) * (3 * 2) + 3 * 8 = 0 mod 7
    #[test]
    fn test_assert_constraint_satisfied() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(8), 6)],
            trusted: false,
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let witness_sat = assert_satisfies(&mut solver, &constraint, &witness);
        println!("Debug witness_sat: {:?}", witness_sat.unwrap());
        println!("Debug witness: {:?}", witness);
        println!("Debug witness var: {:?}", witness.w[0].value.0);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied mod 7
    // (1 * 1) * (7 * 2) - 7 * 1 = 7 = 42 = 0 mod 7
    #[test]
    fn test_assert_constraint_sat_by_mod() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(7), 4)],
            c2: vec![(FieldElement::from(7), 6)],
            trusted: false,
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // (1 * 2) * (3 * 3) + (3 * 6 + 2 * 3) = 42 = 0 mod 7
    #[test]
    fn test_assert_constraint_sat_multi_item_vec_input() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(6), 6), (FieldElement::from(3), 2)],
            trusted: false,
        };
        println!("Debug constraint: {:?}", constraint);

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_assert_sat_by_empty_constraint() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![],
            c1: vec![],
            c2: vec![],
            trusted: false,
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is not satisfied
    // (1 * 1) * (3 * 1) - 6 * 1 = -3 != 0 mod 7
    #[test]
    fn test_assert_constraint_not_satisfied() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(6), 6)],
            trusted: false,
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied by two unique witnesses
    // The dot product with the witnesses and constraint here would be
    // witness1 : (3 * 1) * (3 * 2) + 4 * 6 = 42 = 0 mod 7
    // witness2 : (4 * 1) * (1 * 3) + 5 * 6 = 42 = 0 mod 7
    #[test]
    fn test_constraint_satisfied_by_two_unique_witnesses() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(6), 6)],
            trusted: false,
        };

        let witness1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(4), 6),
                    deterministic: false,
                },
            ],
        };

        let witness2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(5), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(4), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(4), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 6),
                    deterministic: false,
                },
            ],
        };

        let witness_indices: HashSet<usize> = [1, 3, 5].iter().cloned().collect();

        assert_witnesses_neq(&witness1.w, &witness2.w, &witness_indices, &mut solver);
        let _ = assert_satisfies(&mut solver, &constraint, &witness1);
        let _ = assert_satisfies(&mut solver, &constraint, &witness2);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is not satisfied by two identical witnesses
    // Using witness1 twice in the check should return Unsat
    #[test]
    fn test_constraint_not_satisfied_by_two_identical_witnesses() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(6), 6)],
            trusted: false,
        };

        let witness1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let witness_indices: HashSet<usize> = [1, 3, 5].iter().cloned().collect();

        assert_witnesses_neq(&witness1.w, &witness1.w, &witness_indices, &mut solver);
        let _ = assert_satisfies(&mut solver, &constraint, &witness1);

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Tests whether or not the correct dot product will yield Sat
    // (1 * 4) + (2 * 5) + (3 * 6) = 32
    #[test]
    fn test_dot_product_sat() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(FieldElement, u32)> = vec![
            (FieldElement::from(1), 1),
            (FieldElement::from(2), 2),
            (FieldElement::from(3), 3),
        ];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (FieldElement::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(FieldElement::from(32)));

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_dot_product_sat_empty_array() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(FieldElement, u32)> = vec![];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (FieldElement::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(FieldElement::from(0)));

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_dot_product_unsat_diff_length() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&bn_254_field_modulus).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(FieldElement, u32)> =
            vec![(FieldElement::from(1), 1), (FieldElement::from(2), 2)];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (FieldElement::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(FieldElement::from(0)));

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // The incorrect dot product will yield Unsat
    // (1 * 4) + (2 * 5) + (3 * 6) != 0
    #[test]
    fn test_dot_product_unsat() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(FieldElement, u32)> = vec![
            (FieldElement::from(1), 1),
            (FieldElement::from(2), 2),
            (FieldElement::from(3), 3),
        ];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (FieldElement::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (FieldElement::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(FieldElement::from(0)));

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    // Tests whether or not witnesses are differentiated correctly.
    // The system is only satisfiable when all witness variables differ
    fn test_assert_witnesses_neq_distinct() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let witness_1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 3),
                    deterministic: false,
                },
            ],
        };
        let witness_2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(4), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(6), 3),
                    deterministic: false,
                },
            ],
        };

        let witness_indices: HashSet<usize> = [1, 2, 3].iter().cloned().collect();

        assert_witnesses_neq(&witness_1.w, &witness_2.w, &witness_indices, &mut solver);
        // Check if the assertion is true. This should succeed because the witnesses are
        // unique.
        let debug_expected = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());
        assert_eq!(debug_sat_check, debug_expected);
    }

    #[test]
    fn test_assert_witnesses_neq_identical() {
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();
        let witness_1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 3),
                    deterministic: false,
                },
            ],
        };
        let witness_2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(3), 3),
                    deterministic: false,
                },
            ],
        };
        println!("Debug witness 1.0: {:?}", witness_1.w[0]);
        println!("Debug witness 1.1: {:?}", witness_1.w[1]);
        println!("Debug witness 1.2: {:?}", witness_1.w[2]);
        println!("Debug witness 2.0: {:?}", witness_2.w[0]);
        println!("Debug witness 2.1: {:?}", witness_2.w[1]);
        println!("Debug witness 2.2: {:?}", witness_2.w[2]);
        let witness_indices: HashSet<usize> = [1, 2, 3].iter().cloned().collect();

        assert_witnesses_neq(&witness_1.w, &witness_2.w, &witness_indices, &mut solver);
        // Check if the assertion is false. This should succeed because the witnesses
        // are identical.
        let debug_expected = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());
        assert_eq!(debug_sat_check, debug_expected);
    }

    #[test]
    fn test_assert_witnesses_neq_empty_arrays() {
        // 1. Set up the backend (in this case z3)
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let witness_1 = WitnessAST { w: vec![] };
        let witness_2 = WitnessAST { w: vec![] };
        let witness_indices: HashSet<usize> = HashSet::new();
        assert_witnesses_neq(&witness_1.w, &witness_2.w, &witness_indices, &mut solver);
        // Check if the assertion is false. This should succeed because the witnesses
        // are identical.
        let debug_sat = format!("{:?}", solver.check_sat().unwrap());
        let debug_expected = format!("{:?}", SatResult::Unsat);
        assert_eq!(debug_sat, debug_expected);
    }

    #[test]
    fn test_variables_that_cooccur_get_returned() {
        let data_deterministic = std::fs::read("tests/TriviallyDeterministic.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_nondeterministic.header);

        let circuit = r1cs_to_circuit(&file_deterministic);
        println!(
            "Debug circuit constraint system: {:?}",
            circuit.constraints.constraints
        );
        // Test to see if co-ocurring variables for the output are returned correctly
        let cooccurring_vars = return_coocurring_variables_in_constraint_system(
            &circuit.constraints.constraints[0],
            &1,
        );
        let debug_cocurring_vars = format!("{:?}", cooccurring_vars);
        println!("Cooccurring vars: {}", debug_cocurring_vars);
        // In this case, there's only one constraint that contains cocurring variables
        // for the public output
        assert!(circuit.constraints.constraints.len() == 1);

        let debug_expected = format!("{:?}", circuit.constraints.constraints[0].c2);
        assert_eq!(debug_cocurring_vars, debug_expected);
    }

    #[test]
    fn test_assert_fixed_inputs_are_deterministic() {
        // Assert that fixed inputs in a circuit get marked as deterministic
        let data_deterministic = std::fs::read("tests/sqrt.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        println!("Debug Header: {:?}", file_deterministic.header);

        // 1. Set up the backend (in this case z3)
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let circuit = r1cs_to_circuit(&file_deterministic);
        let num_vars = circuit.n_wires;

        let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

        // Output determinacy check: if we check for weak determinacy, we fix all inputs
        // to check to see if we get the same output Else, we just check for the
        // normal determinacy condition: whether or not there are two distinct
        // assignments to the non-fixed variables that satisfy the constraints.
        let witness_det = false;
        let sym_file = None;
        let fixed_inputs: Range<u32> = if witness_det {
            circuit.outputs.end..circuit.private_inputs.end
        } else {
            circuit.outputs.end..circuit.fixed_inputs.end
        };

        for i in fixed_inputs.clone() {
            let _ = variable_witness_indices.remove(&(i as usize));
        }

        // Witness determinacy check
        let (witness1, witness2) = check_unique_satisfying_witnesses(
            &mut solver,
            &fixed_inputs,
            &variable_witness_indices,
            num_vars,
            &sym_file,
        );

        assert!(!witness1.w[1].deterministic);
        assert!(witness1.w[2].deterministic);
        assert!(!witness2.w[1].deterministic);
        assert!(witness2.w[2].deterministic);
    }

    #[test]
    fn test_assert_variables_nondeterministic_do_not_get_determinacy_propagated() {
        // Assert that fixed inputs in a circuit get marked as deterministic
        // Here, we use the sqrt circuit because sqrt is a special case with out * out
        // == in
        let data_deterministic = std::fs::read("tests/sqrt.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();

        // 1. Set up the backend (in this case z3)
        let backend = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend, true).unwrap();
        let prime = BigUint::from(7u32);

        solver.set_logic(Logic::QF_FF).unwrap();
        solver.set_field_order(&prime).unwrap();

        let circuit = r1cs_to_circuit(&file_deterministic);
        let num_vars = circuit.n_wires;

        let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

        // Output determinacy check: if we check for weak determinacy, we fix all inputs
        // to check to see if we get the same output Else, we just check for the
        // normal determinacy condition: whether or not there are two distinct
        // assignments to the non-fixed variables that satisfy the constraints.
        let witness_det = false;
        let sym_file = None;
        let fixed_inputs: Range<u32> = if witness_det {
            circuit.outputs.end..circuit.private_inputs.end
        } else {
            circuit.outputs.end..circuit.fixed_inputs.end
        };

        for i in fixed_inputs.clone() {
            let _ = variable_witness_indices.remove(&(i as usize));
        }

        let (mut witness1, mut witness2) = check_unique_satisfying_witnesses(
            &mut solver,
            &fixed_inputs,
            &variable_witness_indices,
            num_vars,
            &sym_file,
        );

        for constraint in circuit.constraints.constraints.iter() {
            let _ = propagate_determinacy(constraint, &mut witness1);
            let _ = propagate_determinacy(constraint, &mut witness2);
        }

        assert!(!witness1.w[1].deterministic);
        assert!(witness1.w[2].deterministic);
        assert!(!witness2.w[1].deterministic);
        assert!(witness2.w[2].deterministic);

        // assert!(solver.check_sat().unwrap() == SatResult::Sat);
        let debug_sat = format!("{:?}", solver.check_sat().unwrap());
        println!("Debug sat: {}", debug_sat);
    }

    #[test]
    fn test_constraint_to_ast_conversion() {
        let data_deterministic = std::fs::read("tests/sqrt.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        println!("Debug Header: {:?}", file_deterministic.header);
        println!("Debug Constraints: {:?}", file_deterministic.constraints);

        let constraints = constraints_to_ast(&file_deterministic.constraints);
        println!("Debug Z3constraints: {:?}", constraints);
        println!(
            "Debug individual constraint: {:?}",
            constraints.constraints[0]
        );
        assert!(constraints.constraints.len() == 1);
    }

    #[test]
    fn test_mark_vars_as_deterministic() {
        let mut witness1 = create_mock_witness();
        let mut witness2 = create_mock_witness();

        let mut vars = HashSet::new();
        let _ = vars.insert(0);
        let _ = vars.insert(1);

        mark_vars_as_deterministic(&vars, &mut witness1, &mut witness2);

        assert!(witness1.w[0].deterministic);
        assert!(witness1.w[1].deterministic);
        assert!(witness2.w[0].deterministic);
        assert!(witness2.w[1].deterministic);
    }

    #[test]
    fn test_mark_vars_as_non_deterministic() {
        let mut witness1 = create_mock_witness();
        let mut witness2 = create_mock_witness();

        let mut vars = HashSet::new();
        let _ = vars.insert(0);
        let _ = vars.insert(1);

        mark_vars_as_non_deterministic(&vars, &mut witness1, &mut witness2);

        assert!(!witness1.w[0].deterministic);
        assert!(!witness1.w[1].deterministic);
        assert!(!witness2.w[0].deterministic);
        assert!(!witness2.w[1].deterministic);
    }

    #[test]
    fn test_return_coocurring_variables_in_constraint_system_c0() {
        // Create an instance of ConstraintAST where the c0 array has a matching
        // var_index
        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2), (FieldElement::from(2), 3)],
            c1: vec![(FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(4), 5)],
            trusted: false,
        };

        // This should return c0 since var_index is found in c0
        let result = return_coocurring_variables_in_constraint_system(&constraint, &2);
        let debug_result = format!("{:?}", result);
        println!("Debug result: {}", debug_result);
        let debug_c0 = format!("{:?}", constraint.c0);
        assert_eq!(debug_result, debug_c0);
    }

    #[test]
    fn test_return_coocurring_variables_in_constraint_system_c1() {
        // Create an instance of ConstraintAST where the c1 array has a matching
        // var_index
        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3), (FieldElement::from(3), 4)],
            c2: vec![(FieldElement::from(4), 5)],
            trusted: false,
        };

        // This should return c1 since var_index is found in c1
        let result = return_coocurring_variables_in_constraint_system(&constraint, &3);
        let debug_result = format!("{:?}", result);
        println!("Debug result: {}", debug_result);
        let debug_c1 = format!("{:?}", constraint.c1);
        assert_eq!(debug_result, debug_c1);
    }

    #[test]
    fn test_return_coocurring_variables_in_constraint_system_c2() {
        // Create an instance of ConstraintAST where the c2 array has a matching
        // var_index
        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3)],
            c2: vec![(FieldElement::from(3), 4), (FieldElement::from(4), 5)],
            trusted: false,
        };

        // This should return c2 since var_index is found in c2
        let result = return_coocurring_variables_in_constraint_system(&constraint, &5);
        let debug_result = format!("{:?}", result);
        println!("Debug result: {}", debug_result);
        let debug_c2 = format!("{:?}", constraint.c2);
        assert_eq!(debug_result, debug_c2);
    }

    #[test]
    fn test_return_coocurring_variables_in_constraint_system_no_match() {
        // Create an instance of ConstraintAST where no array has a matching var_index
        let constraint = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3)],
            c2: vec![(FieldElement::from(3), 4)],
            trusted: false,
        };

        // This should return an empty Vec since var_index is not found in any array
        let result = return_coocurring_variables_in_constraint_system(&constraint, &5);
        let empty: Vec<(FieldElement, u32)> = vec![];
        let debug_result = format!("{:?}", result);
        println!("Debug result: {}", debug_result);
        let debug_empty = format!("{:?}", empty);
        assert_eq!(debug_result, debug_empty);
    }

    #[test]
    fn test_get_variable_names() {
        // The path to your test .sym file
        let test_file_path = Path::new("tests/monty.sym");

        // Call get_variable_names with the path of the .sym file
        let variable_names =
            get_variable_names(test_file_path).expect("Failed to get variable names");

        println!("Debug variable names: {:?}", variable_names);

        // Check that the returned variable names match the known data
        assert_eq!(
            variable_names,
            vec![
                "main.out[0]",
                "main.out[1]",
                "main.in1[0]",
                "main.in1[1]",
                "main.in2[0]",
                "main.in2[1]",
                "main.lamda"
            ]
        );
    }

    #[test]
    fn test_constraint_and_witness_equality() {
        // The path to your test .sym file
        let witness_1 = create_mock_witness();
        let witness_2 = create_mock_witness();
        let witness_3 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (FieldElement::from(4), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(5), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (FieldElement::from(6), 3),
                    deterministic: false,
                },
            ],
        };
        assert!(witness_1 == witness_2);
        assert!(witness_2 != witness_3);

        let constraint_1 = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3)],
            c2: vec![(FieldElement::from(3), 4)],
            trusted: false,
        };

        let constraint_2 = ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3)],
            c2: vec![(FieldElement::from(3), 4)],
            trusted: false,
        };

        let constraint_3 = ConstraintAST {
            c0: vec![(FieldElement::from(3), 2)],
            c1: vec![(FieldElement::from(4), 3)],
            c2: vec![(FieldElement::from(5), 4)],
            trusted: false,
        };

        assert!(constraint_1 == constraint_2);
        assert!(constraint_2 != constraint_3);
    }

    #[test]
    fn test_contains_matching_constraints_basic() {
        // Create an instance of ConstraintAST where no array has a matching var_index
        let mut constraints_1 = vec![ConstraintAST {
            c0: vec![(FieldElement::from(1), 4)],
            c1: vec![(FieldElement::from(2), 5)],
            c2: vec![(FieldElement::from(3), 0)],
            trusted: false,
        }, ConstraintAST {
            c0: vec![(FieldElement::from(4), 1)],
            c1: vec![(FieldElement::from(5), 4)],
            c2: vec![(FieldElement::from(6), 1)],
            trusted: false,
        },
        // Also insert a filler constraint to test matching
        ConstraintAST {
            c0: vec![(FieldElement::from(1), 1)],
            c1: vec![(FieldElement::from(2), 4)],
            c2: vec![(FieldElement::from(3), 1)],
            trusted: false,
        }];
        let constraints_2 = vec![ConstraintAST {
            c0: vec![(FieldElement::from(1), 2)],
            c1: vec![(FieldElement::from(2), 3)],
            c2: vec![(FieldElement::from(3), 0)],
            trusted: false,
        }, ConstraintAST {
            c0: vec![(FieldElement::from(4), 1)],
            c1: vec![(FieldElement::from(5), 2)],
            c2: vec![(FieldElement::from(6), 1)],
            trusted: false,
        }];

        let mut constraints_3 = vec![ConstraintAST {
            c0: vec![(FieldElement::from(1), 1)],
            c1: vec![(FieldElement::from(2), 4)],
            c2: vec![(FieldElement::from(3), 1)],
            trusted: false,
        }];
        let constraints_4 = vec![ConstraintAST {
            c0: vec![(FieldElement::from(4), 1)],
            c1: vec![(FieldElement::from(5), 2)],
            c2: vec![(FieldElement::from(6), 1)],
            trusted: false,
        }];

        // Should return true for matching constraints
        assert!(check_corresponding_constraints(&mut constraints_1, &constraints_2));
        assert!(!check_corresponding_constraints(&mut constraints_3, &constraints_4));
    }

    #[test]
    fn test_can_propagate_trusted_function() {
        let data_deterministic = std::fs::read("tests/BigIsZero.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_deterministic.header);

        let backend_cvc5 = smtlib::backend::Cvc5Binary::new("src/cvc5").unwrap();
        // 2. Set up the solver
        let mut cvc5_solver = smtlib::Solver::new(backend_cvc5, false).unwrap();
        let bn_254_field_modulus = BigUint::parse_bytes(
            b"21888242871839275222246405745257275088548364400416034343698204186575808495617",
            10,
        )
        .unwrap();

        cvc5_solver.set_logic(Logic::QF_FF).unwrap();
        cvc5_solver.set_field_order(&bn_254_field_modulus).unwrap();

        let mut circuit = r1cs_to_circuit(&file_deterministic);

        let det_func_path = std::fs::read("tests/IsZero@comparators.r1cs").unwrap();
        let det_func_r1cs = R1csFile::<32>::read(det_func_path.as_slice()).unwrap();
        let det_func_circuit = r1cs_to_circuit(&det_func_r1cs);
        let det_funcs = Some(vec![det_func_circuit]);

        propagate_trusted_functions(&mut circuit, &det_funcs);

        println!("Debug circuit: {:?}", circuit.constraints.constraints);

        // Assert that the trusted function is propagated
        // i.e. there are trusted constraints within the main circuit
        assert!(circuit.constraints.constraints[0].trusted);
        assert!(circuit.constraints.constraints[1].trusted);
    }
}
