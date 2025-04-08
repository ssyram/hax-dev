This crate contains the [rust files](https://github.com/rust-lang/rust/tree/master/tests/coverage) from rustc [coverage tests](https://rustc-dev-guide.rust-lang.org/tests/compiletest.html#coverage-tests). 

The following test target are available:
- `json` to test AST extraction as json using hax frontend
- `fstar` to test that extraction to F* succeeds
- `coq` to test that extraction to coq succeeds

## Running

A script is available to run the tests using `./rustc-coverage-tests <target>` where `<target>` is either one of the targets or `all`.

## Modifying

### Updating sources

To sync the test suite with the latest version from rustc, the rust files from the rust repo need to be copied to this directory in replacement of the outdated copies. The `lib.rs` and `mod.rs` files shouldn't be removed.

### Adding a new test target

To add a new test target:
- Add a corresponding feature to the `Cargo.toml`
- Activate the wanted tests for this feature by enabling them under the feature (using the `cfg` attributes in the `lib.rs`/`mod.rs` files)
- Modify the script to add the new target
