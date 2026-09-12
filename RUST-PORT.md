# Rust counterexample search

The current counterexample search is implemented in Rust. It generates the same
1,257 starts as the Python reference, traces them with arbitrary-precision
integers, writes the same result fields, and generates independent Lean
certificates. The three older generalized-family Python analysis scripts remain
historical tools; this port covers the new original-conjecture search.

## Measured performance

Five timed runs after one discarded warmup, on this ARM64 Mac with CPython
3.14.7 and Rust 1.98.1 in release mode:

| Implementation | Median search time | Observed range | Speed relative to Python |
|---|---:|---:|---:|
| Python reference | 2.8363 s | 2.8286–2.8387 s | 1× |
| Rust, 1 worker | 0.1613 s | 0.1603–0.1642 s | **17.58×** |
| Rust, 8 workers | 0.0657 s | 0.0654–0.0669 s | **43.15×** |

The single-worker comparison supports using Rust for this workload. These are
measurements of the implementations, including allocation and peak-tracking
improvements, rather than a universal language speed ratio. Python's big-integer
operations already execute in native code; Rust removes interpreter overhead and
allows the search to update integers in place. The parallel result includes an
additional 2.45× improvement over single-worker Rust.

Timers include trajectory search and row collection on the same ordered inputs.
They exclude seed generation, export, process startup, compilation, and Lean.
The runs were sequential; there were no concurrent builds or verification jobs,
but no CPU affinity or thermal controls were applied. Raw samples, environment,
source/binary hashes, and verification details are in
[`results/rust_benchmark.json`](results/rust_benchmark.json).

**The full certified workflow has a smaller speedup.** In the verification run,
Rust search took about 0.16 s, seed generation about 0.004 s, export about 0.010 s,
and Lean replay about **38 s**. That Lean figure is one observed verification run,
not a repeated benchmark. Porting the search does not speed up Lean's independent
replay of the same trajectories. Wall-clock measurements are empirical and are
not claimed to be certified by Lean.

## Run

```sh
cargo build --release --locked
target/release/collatz-search --verify-lean

# Optional parallel search; preserves the original input/output order.
target/release/collatz-search --threads 8 --verify-lean

# Search timing only; leaves result artifacts untouched.
target/release/collatz-search --bench 5

# Reproduce the Python/Rust comparison (one warmup, five retained samples).
python3 bench/compare.py --repeats 5 --threads 8
```

Use a release build for speed. The default outputs, under the project directory,
are `CollatzSearchCertsRust.lean`, `results/counterexample_search_rust.json`, and,
when verification runs, `results/counterexample_search_rust.log`. Override the
paths with `--certificate FILE` and `--output-dir DIR`; relative paths are
resolved from the invocation directory. `--fuel N` sets the ordinary-step limit
per start, with 300,000 as the default. An exhausted limit remains unresolved.

The executable does not invoke Python. The Python baseline is retained for
independent comparisons and for the benchmark driver. A Rust search can run
without Lean installed; `--verify-lean` requires the pinned Lean 4.31.0 toolchain.

## Correctness and proof checks

- Every generated input, result field, row ordering, and family summary matches
  the Python baseline. All 1,257 starts reach 1, with identical first-descent,
  first-arrival, and peak-bit metrics.
- Generated Lean certificate bodies match the Python version, apart from the
  provenance and output filename. Lean accepted all Rust-generated trajectories.
- The universal checker-soundness theorem has no axioms. Finite replay uses
  `native_decide`, which trusts Lean's compiler and native runtime.
- All 14 Rust tests pass; `cargo fmt --check` and Clippy with warnings denied pass.
  Tests cover large integers, known trajectories, fuel boundaries, complete seed
  parity, certificate filtering, and empty successful datasets.
- A parallel zero-fuel run yields 1,257 unresolved cases and an empty successful
  certificate. It does not silently report convergence. Relative certificate
  paths, invalid options, and output-path collision rejection were also checked.

```sh
cargo test --locked
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
python3 bench/compare.py --check-only
```

The source is organized into [`src/search.rs`](src/search.rs) for exact arithmetic,
[`src/seeds.rs`](src/seeds.rs) for deterministic starts,
[`src/certificates.rs`](src/certificates.rs) for certificate generation, and
[`src/main.rs`](src/main.rs) for execution, parallel workers, artifacts, and Lean
invocation. Dependencies are pinned in `Cargo.lock`.

The mathematical objective remains unresolved. Faster search excludes more
specific candidates; it does not prove convergence of every positive integer.
See [ATTEMPT.md](ATTEMPT.md) for the proof attempts and remaining gap.
