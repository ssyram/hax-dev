# Benchmarks for the hax frontend

This section is brief report summarizing our benchmarking results for the hax's frontend.
The goal was to compare `cargo check` with `cargo hax` on a large set of Rust crates, with a particular focus on cryptography-related crates.
The values presented here are normalized to enable fair comparisons across crates of vastly different sizes and complexity.

We have been developing a tool to benchmark the *hax* toolchain by running it on a diverse collection of Rust crates: `hax-test-crates`.
Since cryptography is important to Cryspen and in general in verfied software, we included a substantial subset of crypto-related crates among the 1000 crates of interest.
The remainder of the crates encompasses a variety of general-purpose crates—covering everything from small utilities to bigger crates.

Raw compilation times vary significantly based on the size and complexity of the crate.
A "big" crate naturally takes longer to build than a "small" crate, making direct comparisons misleading.
We therefore normalized our measurements to allow a fair evaluation of both `cargo check` and `cargo hax` across all crates in our data set.

We use the median, mean, and 10th decile to summarize the data.

## Results

We break down the results into two main categories: **crypto crates** and **general crates**.

### Crypto Crates

| Statistic       | Cargo Check | Cargo Hax |
|-----------------|------------:|----------:|
| **Median**      |       0.148 |     0.796 |
| **Mean**        |       0.199 |     0.777 |
| **10th Decile** |       0.411 |     0.948 |

Observations:

- For *median* and *mean* values, `cargo hax` is between 4 and 5.3 times slower than a regular `cargo check`.
- In contrast, at the **10th decile**, `cargo hax` is only about 2 times slower than `cargo check`, which seems to indiquate that it perform better in bigger settings.

### General Crates

| Statistic       | Cargo Check | Cargo Hax |
|-----------------|------------:|----------:|
| **Median**      |       0.147 |     0.780 |
| **Mean**        |       0.215 |     0.771 |
| **10th Decile** |       0.425 |     0.953 |

Overall, it seems that the general crates are a little friendlier to hax, only by a little offset. 
