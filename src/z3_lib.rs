use num_bigint::BigUint;
use smtlib::Backend;
use smtlib_lowlevel::{
    ast::{SpecConstant, Term},
    lexicon::Numeral,
};

use smtlib::{backend::Z3Static, Bool, Int, Model, Solver, Sort};

use std::{
    collections::{HashMap, HashSet},
    fs::{File, OpenOptions},
    io::{self, BufRead, Write},
    ops::{Add, BitAnd, Mul, Not, Range, Rem, Sub},
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
/// Each of these constraints is expressed as a vector of (Int, u32)
/// pairs, where the Int represents a field element, and u32 is the
/// position of the coefficient in the polynomial equation.
///
/// # Fields
/// * `c0`: The first constraint vector. Represents the vector of coefficients
///   for the first part of the equation.
/// * `c1`: The second constraint vector. Represents the vector of coefficients
///   for the second part of the equation.
/// * `c2`: The third constraint vector. Represents the vector of coefficients
///   for the third part of the equation.
#[derive(Debug, Clone)]
pub struct ConstraintAST {
    /// The first constraint vector
    pub c0: Vec<(Int, u32)>,
    /// The second constraint vector
    pub c1: Vec<(Int, u32)>,
    /// The third constraint vector
    pub c2: Vec<(Int, u32)>,
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
#[derive(Debug)]
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
/// * `value`: A tuple consisting of a `Int` and a `u32` which represents the
///   value and position of the variable in the witness respectively.
/// * `deterministic`: A boolean that denotes whether the variable is
///   deterministic.
///
/// # Example
///
/// ```rust
/// let int = Int::from(1);
/// let variable = WitnessVariable {
///     value: (int, 1),
///     deterministic: true,
/// };
/// ```
#[derive(Debug, Clone)]
pub struct WitnessVariable {
    /// The value of the variable
    pub value: (Int, u32),
    /// Whether the variable is deterministic or not
    pub deterministic: bool,
}

/// The `WitnessAST` struct represents a witness for a Rank-1 Constraint System
/// (R1CS) in the Abstract Syntax Tree (AST) form. A witness is a specific
/// assignment of values to the variables that satisfies the R1CS constraints.
///
/// A constraint of the form (c0 . w) * (c1 . w) - (c2 .
/// w) = 0 (mod p) is satisfied by the witness, where `c*` are the corresponding
/// constraint vectors, and `w` is the witness vector.
///
/// The `WitnessAST` struct stores a vector of `WitnessVariable` structs, where
/// each `WitnessVariable` represents a variable in the witness, along with
/// information about whether it is deterministic (used in determinacy
/// propagation).
#[derive(Debug)]
pub struct WitnessAST {
    /// The vector of witness variables
    pub w: Vec<WitnessVariable>,
}

/// The `Circuit` struct represents an R1CS circuit. It contains information
/// about the circuit's outputs, fixed inputs, private inputs, constraints,
/// prime field, and the number of wires.
///
/// r1cs_to_circuit converts the parsed R1CS file to a `Circuit` struct.
pub struct CircuitZ3 {
    /// The range of outputs in the circuit
    outputs: Range<u32>,
    /// The range of fixed inputs in the circuit
    fixed_inputs: Range<u32>,
    /// The range of private inputs in the circuit
    private_inputs: Range<u32>,
    /// The constraints in the circuit
    constraints: Constraints,
    /// The prime number that defines the finite field for the circuit
    prime: Int,
    /// The total number of wires in the circuit
    n_wires: u32,
}

/// `SatOutput` is a structure that holds the results of a satisfiability check
/// for a R1CS circuit.
///
/// If a circuit is not deterministic, there should be two different witnesses
/// that satisfy the same set of constraints. `witness_1` and `witness_2`
/// represent these two witnesses. The `model` field stores the model generated
/// by the solver which proves the non-determinism.
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
pub fn smt_check_determinacy_z3<B: Backend>(
    circuit: &CircuitZ3,
    weak_det: &bool,
    assgn_dump: &Option<String>,
    sym_file: &Option<String>,
    solver: &mut Solver<B>,
) -> Result<SatResult, Error> {
    let num_vars = circuit.n_wires;
    let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

    let fixed_inputs = if *weak_det {
        circuit.outputs.end..circuit.private_inputs.end
    } else {
        circuit.outputs.end..circuit.fixed_inputs.end
    };

    for i in fixed_inputs.clone() {
        let _ = variable_witness_indices.remove(&(i as usize));
    }
    let _ = variable_witness_indices.remove(&0); // Remove the fixed wire 0

    let (mut witness1, mut witness2) = check_unique_satisfying_witnesses(
        solver,
        &circuit.prime,
        &fixed_inputs,
        &variable_witness_indices,
        num_vars,
        sym_file,
    );

    // Create subcircuits from the main circuit, then for each subcircuit,
    // parallelize solving for determinacy This allows us to run multiple
    // satsolvers at the same time to speed up proving nondeterminacy
    let unknown_vars = check_unknown_vars(circuit, solver, &mut witness1, &mut witness2);

    check_determinacy_and_dump(
        assgn_dump,
        &mut witness1,
        &mut witness2,
        &unknown_vars,
        circuit,
        sym_file,
        weak_det,
    )
}

/// Checks the variables of a circuit that are indeterminate when checked with
/// two different witnesses.
///
/// For each constraint, perform determinacy propagation for the variables (see
/// propagate_determinacy). If there exists non-deterministic variables by
/// determinacy propagation, the function attempts to use the sat solver to
/// determine whether the constraint is satisfied by the two witnesses.
fn check_unknown_vars<B: Backend>(
    circuit: &CircuitZ3,
    solver: &mut Solver<B>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
) -> Vec<u32> {
    let mut unknown_vars = vec![];

    for constraint in circuit.constraints.constraints.iter() {
        let non_deterministic_vars_witness1 = propagate_determinacy(constraint, witness1);
        let non_deterministic_vars_witness2 = propagate_determinacy(constraint, witness2);

        if !non_deterministic_vars_witness1.is_empty()
            && !non_deterministic_vars_witness2.is_empty()
        {
            match (
                assert_satisfies(solver, &circuit.prime, constraint, witness1)
                    .expect("Error occurred while processing witness1"),
                assert_satisfies(solver, &circuit.prime, constraint, witness2)
                    .expect("Error occurred while processing witness1"),
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
fn generate_witness_for_circuit(
    circuit: &CircuitZ3,
    assgn_dump: &mut File,
    sym_file: &Option<String>,
    weak_det: &bool,
) {
    let num_vars = circuit.n_wires;

    let mut handles = vec![];

    let fixed_inputs = if *weak_det {
        circuit.outputs.end..circuit.private_inputs.end
    } else {
        circuit.outputs.end..circuit.fixed_inputs.end
    };

    for constraint in circuit.constraints.constraints.iter() {
        let prime = circuit.prime;
        let sym_file = sym_file.clone();
        let c0 = constraint.c0.clone();
        let c1 = constraint.c1.clone();
        let c2 = constraint.c2.clone();

        let handle = thread::spawn(move || {
            let par_backend = Z3Static::new(&None).unwrap();
            // ToDo: pass timeout information here
            let mut par_solver = Solver::new(par_backend, false).unwrap();
            // Redo all witness constraints (neq, satisfies constraints, etc.)
            // Solve for each solver in parallel
            let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

            let par_fixed_inputs = fixed_inputs.start..fixed_inputs.end;

            for i in par_fixed_inputs {
                variable_witness_indices.remove(&(i as usize));
            }
            variable_witness_indices.remove(&0); // Remove the fixed wire 0

            let par_fixed_inputs = fixed_inputs.start..fixed_inputs.end;
            let (par_witness1, par_witness2) = check_unique_satisfying_witnesses(
                &mut par_solver,
                &prime,
                &par_fixed_inputs,
                &variable_witness_indices,
                num_vars,
                &sym_file,
            );

            // Convert the (u32, u32) pairs back to (Int, u32) pairs
            let par_constraint = ConstraintAST { c0, c1, c2 };

            let _ = assert_satisfies(&mut par_solver, &prime, &par_constraint, &par_witness1);
            let _ = assert_satisfies(&mut par_solver, &prime, &par_constraint, &par_witness2);

            par_solver.check_sat().unwrap();
            let model: Model = par_solver.get_model().unwrap();

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

    // Write results at the end to a file (Todo: refactor this into its own
    // function)
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
fn check_determinacy_and_dump(
    assgn_dump: &Option<String>,
    witness1: &mut WitnessAST,
    witness2: &mut WitnessAST,
    unknown_vars: &[u32],
    circuit: &CircuitZ3,
    sym_file: &Option<String>,
    weak_det: &bool,
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
        generate_witness_for_circuit(circuit, &mut dump_file, sym_file, weak_det);
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
fn check_unique_satisfying_witnesses<B: Backend>(
    solver: &mut Solver<B>,
    prime_int: &Int,
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
            value: (*Int::from_name(format!("witness_1_{}", name_1)), i),
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
                value: (*Int::from_name(format!("witness_2_{}", name_2)), i),
                deterministic: false,
            };
        } else {
            // Make the other assignments same for both witnesses
            witness_var_1.deterministic = true;
            witness_var_2 = witness_var_1.clone();
        };
        let _ = solver.assert(Int::ge(witness_var_1.value.0, Int::from(0)));
        let _ = solver.assert(Int::ge(witness_var_2.value.0, Int::from(0)));
        let _ = solver.assert(Int::lt(witness_var_1.value.0, *prime_int));
        let _ = solver.assert(Int::lt(witness_var_2.value.0, *prime_int));
        if fixed_inputs.contains(&i) || i == 0 {
            witness_var_1.deterministic = true;
            witness_var_2.deterministic = true;
        }
        witness_1.w.push(witness_var_1);
        witness_2.w.push(witness_var_2);
    }

    // Assert that first wire is 1; this fixed wire is deterministic
    let _ = solver.assert(witness_1.w[0].value.0._eq(Int::from(1)));
    let _ = solver.assert(witness_2.w[0].value.0._eq(Int::from(1)));

    // Assert that wires outside of fixed assignments are different
    assert_witnesses_neq(&witness_1.w, &witness_2.w, witness_indices, solver);

    (witness_1, witness_2)
}

/// Checks !((a_1 == b_1) /\ (a_2 == b_2) /\ ... /\ (a_n == b_n)) for each of
/// the individual witness components. (i.e. the witness components of
/// `witness_1` and `witness_2` are not equal).
fn assert_witnesses_neq<B: Backend>(
    witness_1: &[WitnessVariable],
    witness_2: &[WitnessVariable],
    witness_indices: &HashSet<usize>,
    solver: &mut Solver<B>,
) {
    let assertion = Bool::from(true); // Default: True, i.e. witnesses are unique.

    let mut variable_wires_1: Vec<(Int, u32)> = vec![];
    let mut variable_wires_2: Vec<(Int, u32)> = vec![];

    for (coefficient_1, coefficient_2) in witness_1.iter().zip(witness_2) {
        if witness_indices.contains(&(coefficient_1.value.1 as usize)) {
            variable_wires_1.push(coefficient_1.value);
        }
        if witness_indices.contains(&(coefficient_2.value.1 as usize)) {
            variable_wires_2.push(coefficient_2.value);
        }
    }

    // Convert tuples to HashMaps for efficient lookup
    let map_witness_1: HashMap<u32, Int> = variable_wires_1
        .iter()
        .map(|(val, pos)| (*pos, *val))
        .collect();
    let map_witness_2: HashMap<u32, Int> = variable_wires_2
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
fn assert_satisfies<B: Backend>(
    solver: &mut Solver<B>,
    prime_int: &Int,
    constraint: &ConstraintAST,
    witness: &WitnessAST,
) -> Result<SatResult, Error> {
    let dot_c0_w = dot_product(&constraint.c0, &witness.w);
    let dot_c1_w = dot_product(&constraint.c1, &witness.w);
    let dot_c2_w = dot_product(&constraint.c2, &witness.w);

    solver.assert(
        Int::sub(Int::mul(dot_c0_w, dot_c1_w), dot_c2_w)
            .rem(*prime_int)
            ._eq(Int::from(0)),
    )?;

    // Check if the constraints are satisfiable: that there are two unique witnesses
    // that satisfy the constraints In the end, we want a positive result; a
    // system is non-deterministic if and only if there are two distinct assignments
    // to the non-fixed variables that satisfy the constraints.

    solver.check_sat()
}

/// Converts a vector of field elements parsed from an R1CS file to a vector of
/// z3 AST nodes.
fn field_element_to_z3_int(elements: &[(r1cs_file::FieldElement<32>, u32)]) -> Vec<(Int, u32)> {
    elements
        .iter()
        .map(|(field_element, u)| {
            let int_field_element = BigUint::from_bytes_le(field_element.as_slice());
            let field_element = string_to_smt_int(int_field_element.to_string());
            (field_element, *u)
        })
        .collect()
}

// Convert the constraints descriptions given by the R1CS file parser to z3 AST
// nodes
fn constraints_to_ast(constraints: &r1cs_file::Constraints<32>) -> Constraints {
    let mut ast_constraints = Constraints {
        constraints: vec![],
    };
    for constraint in &constraints.0 {
        let ast_constraint = ConstraintAST {
            c0: field_element_to_z3_int(&constraint.0),
            c1: field_element_to_z3_int(&constraint.1),
            c2: field_element_to_z3_int(&constraint.2),
        };
        ast_constraints.constraints.push(ast_constraint);
    }
    ast_constraints
}

/// Converts the constraint descriptions parsed from an R1CS file to z3 AST
/// nodes.
fn string_to_smt_int(x: String) -> Int {
    Term::SpecConstant(SpecConstant::Numeral(Numeral(x))).into()
}

/// This function returns all variables that co-occur with a specified variable
/// within the same constraint of a system.
fn return_coocurring_variables_in_constraint_system(
    constraint: &ConstraintAST,
    var_index: &u32,
) -> Vec<(Int, u32)> {
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

/// Propagates determinacy of variables across a given constraint system and
/// witness.
fn propagate_determinacy(constraint: &ConstraintAST, witness: &mut WitnessAST) -> HashSet<u32> {
    let mut deterministic_variables = HashSet::new();
    let mut non_deterministic_variables = HashSet::new();
    for (_, var_index) in &constraint.c2 {
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
            deterministic_variables.insert(var_index);
        } else {
            non_deterministic_variables.insert(*var_index);
        }
    }
    for witness_variable in &mut witness.w {
        if deterministic_variables.contains(&witness_variable.value.1) {
            witness_variable.deterministic = true;
        }
    }

    non_deterministic_variables
}

/// The `r1cs_to_circuit` function takes a description of a R1CS file and
/// converts it into a `Circuit` object.
/// Wires are contiguous and are organized as follows, according to the r1cs
/// file specification 0..1: fixed wire 1
/// 1..=n_pub_out: public outputs
/// public_outputs.end..=n_pub_in: public inputs
/// public_inputs.end..=n_prv_in: private inputs
pub fn r1cs_to_circuit_z3(r1cs_description: &R1csFile<32>) -> CircuitZ3 {
    let prime = BigUint::from_bytes_le(r1cs_description.header.prime.as_slice());
    let prime_int = string_to_smt_int(prime.to_string());

    let outputs_end_index = r1cs_description.header.n_pub_out + 1;
    let fixed_inputs_end_index =
        r1cs_description.header.n_pub_in + r1cs_description.header.n_pub_out + 1;

    CircuitZ3 {
        outputs: 1..outputs_end_index,
        fixed_inputs: outputs_end_index..fixed_inputs_end_index,
        private_inputs: fixed_inputs_end_index..r1cs_description.header.n_wires,
        // Using the z3 solver, we construct equations of the form (c0 . w) * (c1 . w) - (c2 . w) =
        // 0 (mod p) By turning each constraint (given by three linear combinations) into
        // AST::Int() nodes.
        constraints: constraints_to_ast(&r1cs_description.constraints),
        prime: prime_int,
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
/// `witness`. The `constraint` vector contains tuples of type `(Int,
/// u32)`, where `Int` is the value at the position represented by
/// `u32`. The `witness` vector contains `WitnessVariable` objects.
///
/// The dot product is computed by iterating over unique keys (positions) from
/// both vectors and accumulating the product of corresponding values (field
/// elements) from each vector.
fn dot_product(constraint: &[(Int, u32)], witness: &[WitnessVariable]) -> Int {
    let dot_product = Int::from(0);

    // Create an array of witness values from the witness variables
    let witness_values: Vec<(Int, u32)> = witness.iter().map(|w| w.value).collect();

    let map_constraint: HashMap<u32, Int> =
        constraint.iter().map(|(val, pos)| (*pos, *val)).collect();
    let map_witness: HashMap<u32, Int> = witness_values
        .iter()
        .map(|(val, pos)| (*pos, *val))
        .collect();

    let zero = Int::from(0);
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
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 3),
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

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_nondeterministic);

        let weak_det = false;
        let assgn_dump_path = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Sat);

        assert_eq!(debug_sat_check, expected_sat);
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

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_nondeterministic);

        let weak_det = false;
        let assgn_dump_path = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
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

        let backend_sqrt = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver_sqrt = smtlib::Solver::new(backend_sqrt, false).unwrap();
        let circuit_sqrt = r1cs_to_circuit_z3(&file_nondeterministic);

        let sat_result_sqrt = smt_check_determinacy_z3(
            &circuit_sqrt,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver_sqrt,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result_sqrt);
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

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_nondeterministic);

        let weak_det = false;
        let assgn_dump_path = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
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

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_nondeterministic);

        let weak_det = false;
        let assgn_dump_path = Some("tests/dump.txt".to_string());
        let sym_file = Some("tests/monty.sym".to_string());

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
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

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_deterministic);

        let weak_det = true;
        let assgn_dump_path = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Unsat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_deterministic_under_output_check() {
        let data_deterministic = std::fs::read("tests/IsZero@comparators.r1cs").unwrap();
        let file_deterministic = R1csFile::<32>::read(data_deterministic.as_slice()).unwrap();
        // println!("Debug Header: {:?}", file_deterministic.header);
        println!(
            "Debug File Constraints: {:?}",
            file_deterministic.constraints
        );

        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_deterministic);

        let weak_det = true;
        let assgn_dump_path = None;
        let sym_file = None;

        let sat_result = smt_check_determinacy_z3(
            &circuit,
            &weak_det,
            &assgn_dump_path,
            &sym_file,
            &mut solver,
        )
        .unwrap();

        let debug_sat_check = format!("{:?}", sat_result);
        println!("Debug sat result {}", debug_sat_check);

        let expected_sat = format!("{:?}", SatResult::Unsat);

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied
    // The dot product with the witness and constraint here would be
    // (3 * 1) * (3 * 2) - 3 * 6 = 0 mod 7
    #[test]
    fn test_assert_constraint_satisfied() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(6), 6)],
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness);
        println!("Debug witness: {:?}", witness);
        println!("Debug witness var: {:?}", witness.w[0].value.0);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied mod 7
    // (1 * 1) * (7 * 2) - 7 * 1 = 7 == 0 mod 7
    #[test]
    fn test_assert_constraint_sat_by_mod() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(7), 4)],
            c2: vec![(Int::from(7), 6)],
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // (1 * 2) * (3 * 3) - (2 * 6 + 6) = 0
    #[test]
    fn test_assert_constraint_sat_multi_item_vec_input() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(6), 6), (Int::from(3), 2)],
        };
        println!("Debug constraint: {:?}", constraint);

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_assert_sat_by_empty_constraint() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![],
            c1: vec![],
            c2: vec![],
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is not satisfied
    // (1 * 1) * (3 * 1) - 6 * 1 = -3 != 0 mod 7
    #[test]
    fn test_assert_constraint_not_satisfied() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(6), 6)],
        };

        let witness = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 6),
                    deterministic: false,
                },
            ],
        };

        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness);

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is satisfied by two unique witnesses
    // The dot product with the witnesses and constraint here would be
    // witness1 : (3 * 1) * (3 * 2) - 3 * 6 = 0 mod 7
    // witness2 : (4 * 1) * (1 * 3) - 2 * 6 = 0 mod 7
    #[test]
    fn test_constraint_satisfied_by_two_unique_witnesses() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(6), 6)],
        };

        let witness1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let witness2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(5), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(4), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(4), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(1), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 6),
                    deterministic: false,
                },
            ],
        };

        let witness_indices: HashSet<usize> = [1, 3, 5].iter().cloned().collect();

        assert_witnesses_neq(&witness1.w, &witness2.w, &witness_indices, &mut solver);
        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness1);
        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness2);

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Asserts that a constraint is not satisfied by two identical witnesses
    // Using witness1 twice in the check should return Unsat
    #[test]
    fn test_constraint_not_satisfied_by_two_identical_witnesses() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        let prime_int = Int::from(7);

        let constraint = ConstraintAST {
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(6), 6)],
        };

        let witness1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(5), 3),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 4),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(9), 5),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 6),
                    deterministic: false,
                },
            ],
        };

        let witness_indices: HashSet<usize> = [1, 3, 5].iter().cloned().collect();

        assert_witnesses_neq(&witness1.w, &witness1.w, &witness_indices, &mut solver);
        let _ = assert_satisfies(&mut solver, &prime_int, &constraint, &witness1);

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // Tests whether or not the correct dot product will yield Sat
    // (1 * 4) + (2 * 5) + (3 * 6) = 32
    #[test]
    fn test_dot_product_sat() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(Int, u32)> =
            vec![(Int::from(1), 1), (Int::from(2), 2), (Int::from(3), 3)];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (Int::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(Int::from(32)));

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_dot_product_sat_empty_array() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(Int, u32)> = vec![];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (Int::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(Int::from(0)));

        let expected_sat = format!("{:?}", SatResult::Sat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    fn test_dot_product_unsat_diff_length() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(Int, u32)> = vec![(Int::from(1), 1), (Int::from(2), 2)];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (Int::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(Int::from(0)));

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    // The incorrect dot product will yield Unsat
    // (1 * 4) + (2 * 5) + (3 * 6) != 0
    #[test]
    fn test_dot_product_unsat() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();

        // Define a constraint and witness for testing
        let constraint: Vec<(Int, u32)> =
            vec![(Int::from(1), 1), (Int::from(2), 2), (Int::from(3), 3)];

        let witness: Vec<WitnessVariable> = vec![
            WitnessVariable {
                value: (Int::from(4), 1),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(5), 2),
                deterministic: false,
            },
            WitnessVariable {
                value: (Int::from(6), 3),
                deterministic: false,
            },
        ];

        let result = dot_product(&constraint, &witness);

        let _test_constraint = solver.assert(result._eq(Int::from(0)));

        let expected_sat = format!("{:?}", SatResult::Unsat);
        let debug_sat_check = format!("{:?}", solver.check_sat().unwrap());

        assert_eq!(debug_sat_check, expected_sat);
    }

    #[test]
    // Tests whether or not witnesses are differentiated correctly.
    // The system is only satisfiable when all witness variables differ
    fn test_assert_witnesses_neq_distinct() {
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let witness_1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 3),
                    deterministic: false,
                },
            ],
        };
        let witness_2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(4), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(5), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(6), 3),
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
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let witness_1 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 3),
                    deterministic: false,
                },
            ],
        };
        let witness_2 = WitnessAST {
            w: vec![
                WitnessVariable {
                    value: (Int::from(1), 1),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(2), 2),
                    deterministic: false,
                },
                WitnessVariable {
                    value: (Int::from(3), 3),
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
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
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

        let circuit = r1cs_to_circuit_z3(&file_deterministic);
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
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_deterministic);
        let num_vars = circuit.n_wires;

        let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

        // Output determinacy check: if we check for weak determinacy, we fix all inputs
        // to check to see if we get the same output Else, we just check for the
        // normal determinacy condition: whether or not there are two distinct
        // assignments to the non-fixed variables that satisfy the constraints.
        let weak_det = false;
        let sym_file = None;
        let fixed_inputs: Range<u32> = if weak_det {
            circuit.outputs.end..circuit.private_inputs.end
        } else {
            circuit.outputs.end..circuit.fixed_inputs.end
        };

        for i in fixed_inputs.clone() {
            variable_witness_indices.remove(&(i as usize));
        }

        // Witness determinacy check
        let (witness1, witness2) = check_unique_satisfying_witnesses(
            &mut solver,
            &circuit.prime,
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
        let backend_z3 = smtlib::backend::Z3Static::new(&None).unwrap();
        // 2. Set up the solver
        let mut solver = smtlib::Solver::new(backend_z3, false).unwrap();
        let circuit = r1cs_to_circuit_z3(&file_deterministic);
        let num_vars = circuit.n_wires;

        let mut variable_witness_indices: HashSet<usize> = (0..num_vars as usize).collect();

        // Output determinacy check: if we check for weak determinacy, we fix all inputs
        // to check to see if we get the same output Else, we just check for the
        // normal determinacy condition: whether or not there are two distinct
        // assignments to the non-fixed variables that satisfy the constraints.
        let weak_det = false;
        let sym_file = None;
        let fixed_inputs: Range<u32> = if weak_det {
            circuit.outputs.end..circuit.private_inputs.end
        } else {
            circuit.outputs.end..circuit.fixed_inputs.end
        };

        for i in fixed_inputs.clone() {
            variable_witness_indices.remove(&(i as usize));
        }

        let (mut witness1, mut witness2) = check_unique_satisfying_witnesses(
            &mut solver,
            &circuit.prime,
            &fixed_inputs,
            &variable_witness_indices,
            num_vars,
            &sym_file,
        );

        for constraint in circuit.constraints.constraints.iter() {
            propagate_determinacy(constraint, &mut witness1);
            propagate_determinacy(constraint, &mut witness2);
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
        vars.insert(0);
        vars.insert(1);

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
        vars.insert(0);
        vars.insert(1);

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
            c0: vec![(Int::from(1), 2), (Int::from(2), 3)],
            c1: vec![(Int::from(3), 4)],
            c2: vec![(Int::from(4), 5)],
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
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(2), 3), (Int::from(3), 4)],
            c2: vec![(Int::from(4), 5)],
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
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(2), 3)],
            c2: vec![(Int::from(3), 4), (Int::from(4), 5)],
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
            c0: vec![(Int::from(1), 2)],
            c1: vec![(Int::from(2), 3)],
            c2: vec![(Int::from(3), 4)],
        };

        // This should return an empty Vec since var_index is not found in any array
        let result = return_coocurring_variables_in_constraint_system(&constraint, &5);
        let empty: Vec<(Int, u32)> = vec![];
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
}
