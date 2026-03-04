# RefinedRust verification framework


![RefinedRust logo](refinedrust-logo.svg "RefinedRust logo"){width=200}

This repository contains the RefinedRust development version.

[Wiki and Documentation](https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/wikis/home)

## Structure
The Rocq implementation of RefinedRust can be found in the `theories` subfolder.
The frontend implementation can be found in the `rr_frontend` subfolder.
Case studies and tests can be found in the `case_studies` subfolder.
Stdlib interfaces (without proofs) can be found in the `stdlib` subfolder.

### For the `theories` subfolder:
* the `caesium` subfolder contains the Radium operational semantics, an adaptation of RefinedC's Caesium semantics.
* the `lithium` subfolder contains RefinedC's Lithium separation logic automation engine with very lightweight modifications.
* the `rust_typing` subfolder contains the implementation of the RefinedRust type system and proof automation.

## Setup
To use this project, you will need to install some specific dependencies.

There are two maintained ways to do this, using `nix` or (`opam` and `rustup`).

If you are using `nix`, you do not need to have a copy of this repository.

### Setup using `nix` flakes
We assume that you have `nix` installed on your system. Setup instructions can be found here: https://nixos.org/download

You can use `nix shell` to enter an interactive subshell containing the project:
```bash
nix shell "gitlab:lgaeher/refinedrust-dev?host=gitlab.mpi-sws.org"
```

The project lives in this subshell and will disappear as soon as you leave the subshell.

If you do not have flakes enabled, you may get this error:
```
error: experimental Nix feature 'nix-command' is disabled; use ''–extra-experimental-features nix-command' to override
```

All you have to do is activate flakes temporarily by using `--extra-experimental-features 'nix-command flakes'`:
```bash
nix --extra-experimental-features 'nix-command flakes' shell "gitlab:lgaeher/refinedrust-dev?host=gitlab.mpi-sws.org"
```

If you also need a specific toolchain to build RefinedRust against, you can append `.#target.<toolchain>`, as follows:
```bash
nix shell "gitlab:lgaeher/refinedrust-dev?host=gitlab.mpi-sws.org".#target.riscv64gc-unknown-none-elf
```


### Setup using `opam` and `rustup`
We assume that you have `opam` installed on your system. Setup instructions can be found here: https://opam.ocaml.org/doc/Install.html
Make sure that you have a working `rustup`/Rust install. Instructions for setting up Rust can be found on https://rustup.rs/.

You can either setup the necessary dependencies for working on the RefinedRust code and its case studies itself, within a checkout of the RefinedRust repository, or install it on your system to verify Rust code elsewhere.
Note that, if you choose the latter option, you will potentially run into issues when trying to use the same opam switch to modify the contents of the RefinedRust repository.

#### Setup instructions for working on RefinedRust or on its case studies:
0. `cd` into the directory containing this README.
1. Create a new opam switch for RefinedRust:
```
opam switch create refinedrust --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda
opam switch link refinedrust .
opam switch refinedrust
opam repo add rocq-released https://rocq-prover.org/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```
2. Install the necessary dependencies:
```
opam pin add rocq-prover 9.1.0
make builddep
```
3. Build the Rocq implementation of the type system:
```
make setup-dune
make typesystem
```
4. Run `./refinedrust build` in `rr_frontend` to build the frontend.
5. Run `./refinedrust install` in `rr_frontend` to install the frontend into your Rust path.
6. Optionally: compile the standard library with `make stdlib.proof`

##### Upgrading RefinedRust
Run the following steps again:
- Run `make builddep`
- Run `./refinedrust install` in `rr_frontend`
- Optional: run `make clean_stdlib && make stdlib.proof` to upgrade the standard library

You will also need to run `cargo clean && cargo refinedrust` in your project to re-generate the Rocq translation.

#### Setup instructions for installing RefinedRust on your system
We provide scripts to install RefinedRust.

0. `cd` into the directory containing this README.
1. First, set up a new opam switch.
```
opam switch create refinedrust --packages=ocaml-variants.4.14.2+options,ocaml-option-flambda
opam switch link refinedrust .
opam switch refinedrust
```

2. Run the following commands:
```
REFINEDRUST_ROOT=. ./scripts/setup-rust.sh
REFINEDRUST_ROOT=. ./scripts/install-frontend.sh
REFINEDRUST_ROOT=. ./scripts/setup-coq.sh
REFINEDRUST_ROOT=. ./scripts/install-typesystem.sh
REFINEDRUST_ROOT=. ./scripts/install-stdlib.sh
```

This will install the RefinedRust frontend, as well as the Rocq type system and the specifications and proofs for the Rust standard library components that RefinedRust comes with.

##### Upgrading RefinedRust
Run the following steps again:
```
REFINEDRUST_ROOT=. ./scripts/install-frontend.sh
REFINEDRUST_ROOT=. ./scripts/install-typesystem.sh
REFINEDRUST_ROOT=. ./scripts/install-stdlib.sh
```

You will also need to run `cargo clean && cargo refinedrust` in your project to re-generate the Rocq translation.

## Frontend usage
After installing RefinedRust, it can be invoked through `cargo`, Rust's build system and package manager, by running `cargo refinedrust`.

For example, you can build the examples from the paper (located in `case_studies/paper-examples`) by running:
```
cd case_studies/paper-examples
cargo refinedrust
dune build
```

The invocation of `cargo refinedrust` will generate a folder `output/paper_examples` with two subdirectories: `generated` and `proofs`.
The `generated` subdirectory contains auto-generated code that may be overwritten by RefinedRust at any time during subsequent invocations.
The `proofs` subdirectory contains proofs which may be edited manually (see the section [Proof Editing](#proof-editing) below) and are not overwritten by RefinedRust.

More specifically, the `generated` directory will contain:
* `generated_code_crate.v` contains the definition of the code translated to the Radium semantics, including layout specifications for the used structs and enums.
* `generated_specs_crate.v` contains the definition of the annotated specifications for functions and data structures in terms of RefinedRust's type system.
* for each function `fun` with annotated specifications: a file `generated_template_fun.v` containing the lemma statement that has to be proven to show the specification, as well as auto-generated parts of the proof that may change when implementation details of `fun` are changed.

The `proofs` subdirectory contains for each function `fun` a proof that invokes the components defined in the `generated_template_fun.v` file.

In addition, RefinedRust generates an `interface.rrlib` file containing the ADTs and functions which are publicly exported and specified.
Verification of other crates can import these specifications.
The `lib_load_paths` config option influences where the verifier searches for these interface files.
The crate-level `rr::include` directive can be used to import these proof files (see the description in `SPEC_FORMAT.md`).

## Proof editing
You can interactively look at the generated Rocq code using a Rocq plugin like Rocqtail, VSRocq, Proof General, or RocqIDE for the editor of your choice.
To do so, your editor needs to know about the Rocq project structure.
As RefinedRust uses the `dune` build system to compile the Rocq files, if your editor/plugin supports `dune`, it will automatically find the dependencies.
Otherwise, run `dune build` in the folder containing the file you want to edit once. `dune` will create a `_RocqProject` file that all Rocq frontends should understand.

Changes to the `proof_*.v` files in the generated `proofs` folder are persistent and files are not changed once RefinedRust has generated them once.
This enables to write semi-automatic proofs.
`proof_*.v` files are intended to be checked into `git`, as they are stable.

On changes to implementations or specifications, only the files located in `generated` are modified.
The default automatic proofs in `proof_*.v` files are stable under any changes to a function.
Of course, once you change proofs manually, changing an implementation or specification may require changes to your manually-written code.

## License
We currently re-use code from the following projects:
- rustc: https://github.com/rust-lang/rust (under the MIT license)
- miri: https://github.com/rust-lang/miri (under the MIT license)
- RefinedC: https://gitlab.mpi-sws.org/iris/refinedc (under the BSD 3-clause license)
- Iris: https://gitlab.mpi-sws.org/iris/iris (under the BSD 3-clause license)
- lambda-rust: https://gitlab.mpi-sws.org/iris/lambda-rust (under the BSD 3-clause license)
- Prusti: https://github.com/viperproject/prusti-dev (under the MPL 2.0 license)
- Rocq ident-to-string: https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Macros/ident_to_string.v (under the MIT license)

We provide the RefinedRust code under the BSD 3-clause license.
