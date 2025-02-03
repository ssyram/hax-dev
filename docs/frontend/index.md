# Frontend

The frontend of hax is the part of the toolchain that takes care of extracting and exporting given [Rust crates](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html) to abstract syntax trees (AST).

## A Brief Tour of The Rust Compiler

The Rust compiler transforms raw source code from the user into various representations, all the way to machine code when that's what the user requests.

The Rust compiler has several intermediate representations (IR), exposing various views on Rust programs, each suited for different jobs: parsing, typing, borrow checking, etc. As illustrated below by the diagram, the following main IR are:

  - **Parse AST**: an untyped abstract syntax tree (AST) just after parsing;
  - **HIR**: Higher-level Intermediate Representation, an AST close to Rust surface language after name resolution and macro expansion;
  - **THIR**: Typed Higher-level Intermediate Representation, a fully typed version of HIR;
  - **MIR**: Mid-level Intermediate Representation, a simplified Rust AST, in which borrow checking takes place;
  - **LLVM**: interfaces with LLVM.

![](./rustc-diagram.excalidraw.png){: .center style="width:min(100%, 500px)"}

## Querying The Rust Compiler is Hard

The Rust compiler has mechanisms enabling one to hook at the various parse, HIR, THIR, etc. stages. From here, it is possible to interactively ask Rust about the types, traits, names, etc. of a certain Rust construct inside a snippet of code.

Rust is optmizied for performance, and its query system is a complex beast. Finding your way to the information you are looking for is not simple and requires a certain familiarity with the compiler.

From this observation, we decided to split hax in two: a first part that interacts with rustc, and a second that transform Rust ASTs to our various backends.

The goal of the frontend is to take care of all the boring and complex job of interacting with rustc.
The frontend takes Rust code and extracts complete ASTs, designed for easy consumption for other tools.

The ASTs we define are mirrored version of rustc's THIR and MIR, enriched with a lot of extra pieces of data.

## Workflow of the JSON extraction

The frontend defines a binary `cargo-hax`, providing a [custom command](https://doc.rust-lang.org/book/ch14-05-extending-cargo.html) `hax` to `cargo` that allows you to get a JSON-encoded AST for a given Rust program.

Running `cargo hax json` invokes hax' frontend and queries for JSON.

The motivation behind hax' frontend is that interacting with the Rust compiler (rustc) can be difficult. Rustc works with its internal optimized representations and with a system of interactive queries.

![](./workflow-diagram.excalidraw.png)

The hax frontend. Its [rustdoc](https://doc.rust-lang.org/rustdoc/what-is-rustdoc.html) documentation can be found [here](./docs/hax_frontend_exporter/index.html).
