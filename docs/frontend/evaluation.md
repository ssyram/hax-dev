# Evaluation of the hax frontend

(intro)
We evaluate the hax frontend with first quantitative metrics, and then a qualitative study.

## Quantitative evaluation

### What are we testing in the toolchain?

The hax toolchain [is architectured](./evaluation.md#high-level-arch) as several pieces: first, the frontend hooks into the Rust compiler and exports rich abstract syntax trees (ASTs) for given crates. Then, there are the engine and the backend, consuming those ASTs to produce code. On the side, there is the hax library and the models of existing Rust libraries.

This quantitative evaluation is about what we call the frontend: the process of producing JSON-encoded ASTs out of Rust code.

Our goal is to *measure* how well the frontend performs.
 - **Successful extraction:** what is the success rate of producing ASTs?
 - **Performance:** we use hax for verifying real-world crates; we should make sure its performance is not prohibitive.

### How are we testing the hax frontend?

For a given selection of Rust crate, our protocol is as follows.
 1. Clone the source code of the crate.
 2. Run `cargo fetch` to download the required dependencies for the crate.
 3. Run `cargo hax json` (with the appropriate flags), and record errors and time.
 4. Clean Cargo's cache with `cargo clean`.
 5. Run `cargo check`, record errors and time. `cargo hax json` being a `cargo check` with extra work, this measure serves as reference.

This protocol is implemented as a tool we develop at Cryspen: `hax-test-crates`.
This tool does extra work and tests some other parts of the hax toolchain.

### What crate are we testing?

To get a representative corpus of crate, we first include the 5k most downlaoded
crates on crates.io.

Then, we also include the top 2k crates in the cryptography category of
crates.io. hax is about verifying critical software, and cryptography certainly
matters in this area.

> TODO: pin a the precise list of crate

> TODO: actually run the tool on all those crate, currently it's less than that

### How many crates do we extract successfully?

As presented in the chart below, each crate may fall into one of four
categoires: (1) hax extracted an AST successfully (2) hax timed-out (3) hax
failed or (4) both `cargo check` and `cargo hax` failed.

> TODO: pie chart with those 4 cats.
> TODO: look into timeouts
> TODO: look into failures

**Failures.** On XX crates, hax failed on NN crates, for the following reasons:
 - (todo) rustc overflow
 - (todo) bug issue #XX

**Timeouts.** Also, YY crates timeout.

All the other crates were successfully extracted. For those, we focus on performance and time.

### How performant is the frontend?

To compare the numbers and make sense of them, we had to do some normalization.
Indeed, recorded times vary significantly based on the size and complexity of
the crate. A "big" crate naturally takes longer to build than a "small" crate,
making direct comparisons misleading. We therefore normalized our measurements
to allow a fair evaluation of both `cargo check` and `cargo hax` across all
crates in our data set.

> TODO: add plot for correlation between size and `cargo hax` times.


We break down the results into two main categories: **crypto crates** and **general crates**.

#### Crypto Crates

| Statistic       | Cargo Check | Cargo Hax |
|-----------------|------------:|----------:|
| **Median**      |       0.148 |     0.796 |
| **Mean**        |       0.199 |     0.777 |
| **10th Decile** |       0.411 |     0.948 |

Observations:

- For *median* and *mean* values, `cargo hax` is between 4 and 5.3 times slower than a regular `cargo check`.
- In contrast, at the **10th decile**, `cargo hax` is only about 2 times slower than `cargo check`, which seems to indiquate that it perform better in bigger settings.

#### General Crates

| Statistic       | Cargo Check | Cargo Hax |
|-----------------|------------:|----------:|
| **Median**      |       0.147 |     0.780 |
| **Mean**        |       0.215 |     0.771 |
| **10th Decile** |       0.425 |     0.953 |

Overall, it seems that the general crates are a little friendlier to hax, only by a little offset. 

## Conclusion

The hax frontend is capable of extracting successfuly a great portion of Rust crates out there.

However, there are edge cases that triggers prohibitive performance issue or plain failures.

Also, this quantitative evaluation have its limits:
 - only the frontend is evaluated, we need to evaluate the various parts of the engine and backends
 - the contents and well-formedness of the JSON produced is out of scope of this evaluation, whence the need for a quantitative evaluation as well. 
