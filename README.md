# Circomference - Automated R1CS Circuit Verification

Circomference is a tool for performing automatic verification on the determinacy of Rank 1 Constraint Systems (R1CS) circuits. The tool uses a SMTLIB2-compliant SATSolver to potentially find two, unique satisfying assignments to the circuit's constraints. If two such assignments are found, the circuit is considered to be non-deterministic. Otherwise, the circuit is considered to be deterministic. Circomference also supports a set of determinacy propagation rules to help prove determinacy of a circuit.

Circomference is extensible through multiple components:
  - **Backends**: Circomference supports multiple SMTLIB2-compliant SAT solver backends. Currently, Circomference supports [CVC5 and Z3](https://github.com/trail-of-forks/smtlib-rs). The solver can be specified through the command line. Advancements in solver technology would likely be needed to improve Circomference's ability to reason about non-linear equations over finite fields. Therefore, Circomference is designed to be easily extensible to support new solvers.
  - **Determinacy Propagation**: Circomference supports a set of [determinacy propagation rules](https://0xparc.org/blog/ecne). These rules are used to propagate determinacy information through the circuit. The rules are also designed to be easily extensible to support new rules.

[![Crates.io](https://img.shields.io/crates/v/circomference.svg)](https://crates.io/crates/circomference)
[![Docs.rs](https://docs.rs/circomference/badge.svg)](https://docs.rs/circomference)
[![CI](https://github.com/trailofbits/circomference/workflows/CI/badge.svg)](https://github.com/trailofbits/circomference/actions)

## Using Circomference

## Installation
```bash
cargo build
cargo test
# For a list of commands, try:
./target/debug/circomference --help
```

```bash
# Run the following if you would like to rebuild the cvc5 solver.
cargo run cvc5-builder
```

### Cargo

* Install the rust toolchain in order to have cargo installed by following
  [this](https://www.rust-lang.org/tools/install) guide.
* run `cargo install circomference`

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.

See [CONTRIBUTING.md](CONTRIBUTING.md).
