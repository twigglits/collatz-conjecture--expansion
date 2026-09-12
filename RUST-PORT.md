# Rust search and verification tools

The current counterexample search is implemented in Rust. It generates the same
1,257 starts as the Python reference, traces them with arbitrary-precision
integers, writes the same result fields, and generates independent Lean
certificates. Rust replacements also cover the three generalized-family Python
analysis scripts. Python sources remain independent references and benchmark
inputs; the Rust executables do not invoke Python.

| Python reference | Rust executable | Purpose |
|---|---|---|
| `search_counterexample.py` | `collatz-search` | Structured arbitrary-precision counterexample search and Lean replay |
| `analyze.py` | `analyze` | CUDA sample rechecks, cycle identities, inventory tables, and Lean generation |
| `verify_universal.py` | `verify-universal` | Universal-family catalog, divisor-law census, and large-integer identities |
| `verify_frontier.py` | `verify-frontier` | Orbit formulas, cycle equations, congruence restrictions, and residue counts |
| — | `residue-sieve` | Adaptive exact affine descent over whole residue classes |

CUDA sweep engines and Lean proofs remain in their native languages. Rewriting
the Python layer does not accelerate those separate computations.

## Measured performance

Five timed runs after one discarded warmup, on this ARM64 Mac with CPython
3.14.7 and Rust 1.98.1 in release mode:

| Implementation | Median search time | Observed range | Speed relative to Python |
|---|---:|---:|---:|
| Python reference | 2.8950 s | 2.8831–2.9217 s | 1× |
| Rust, 1 worker | 0.1609 s | 0.1603–0.1618 s | **17.99×** |
| Rust, 8 workers | 0.0668 s | 0.0652–0.0699 s | **43.34×** |

The single-worker comparison supports using Rust for this workload. These are
measurements of the implementations, including allocation and peak-tracking
improvements, rather than a universal language speed ratio. Python's big-integer
operations already execute in native code; Rust removes interpreter overhead and
allows the search to update integers in place. The parallel result includes an
additional 2.41× improvement over single-worker Rust.

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

Use a release build for speed. The default search outputs, under the project directory,
are `CollatzSearchCertsRust.lean`, `results/counterexample_search_rust.json`, and,
when verification runs, `results/counterexample_search_rust.log`. Override the
paths with `--certificate FILE` and `--output-dir DIR`; relative paths are
resolved from the invocation directory. `--fuel N` sets the ordinary-step limit
per start, with 300,000 as the default. An exhausted limit remains unresolved.

The Python baseline is retained for independent comparisons and for the benchmark
driver. A Rust search can run without Lean installed; `--verify-lean` requires
the pinned Lean 4.31.0 toolchain.

## Local worker scaling

The local hardware reports an Apple M5 with 10 physical/logical CPU cores:
four fast cores named `Super` by `sysctl`, six `Efficiency` cores, and 24 GiB RAM.
Eight workers is not a program limit. The CLI caps actual workers at the number
of inputs and currently assigns contiguous chunks of approximately equal input
count, although trajectories require very different amounts of work.

Eight timed repetitions per configuration after a discarded warmup, on the
same 1,257-input search:

| Requested workers | Actual workers | Median search time |
|---:|---:|---:|
| 8 | 8 | 0.0696 s |
| 10 | 10 | 0.0701 s |
| 16 | 16 | 0.0496 s |
| 32 | 32 | 0.0396 s |
| 64 | 63 | 0.0433 s |
| 128 | 126 | 0.0453 s |
| 256 | 252 | 0.0314 s |
| 512 | 419 | **0.0279 s** |
| 1,257 | 1,257 | 0.0315 s |

The 512 setting was fastest among those tested, about 2.5 times faster than
eight in this comparison. It does not mean 419 cores are available: splitting
the uneven workload into smaller chunks improves load balance, while additional
thread creation eventually costs more. A queue shared by a smaller fixed worker
pool is a candidate for improving this tradeoff; it has not been implemented or
benchmarked. These measurements apply to this batch and exclude Lean.

Raw samples, a confirmation run at 32 workers, hardware fields, correctness
comparisons, and source hashes are in
[`results/rust_worker_scaling.json`](results/rust_worker_scaling.json).

```sh
target/release/collatz-search --threads 512 --bench 5
```

## Other Rust executables

```sh
cargo build --release --locked --bins
target/release/analyze --verify-lean
target/release/verify-universal
target/release/verify-frontier
target/release/residue-sieve --depth 26 --verify-lean
```

Each executable supports `--help`. The historical analysis uses
`results/raw.jsonl`; universal verification uses `results/universal.jsonl`.
Generated Rust outputs use separate names or directories so the original Python
artifacts remain available for comparison. The verifier fuzz tests use a
reproducible SHAKE256 stream rather than Python's Mersenne Twister, so their
random samples differ; the committed CUDA data and deterministic counts agree.

The verified historical analysis is saved in `results/analyze-rust/`, including
89 cycle certificates and 38 range certificates. The universal report is
`results/universal_summary_rust.md`; frontier outputs are
`results/frontier_summary_rust.md` and `results/frontier_verification_rust.json`.

The residue sieve stores exact affine maps with checked `u128` arithmetic,
supports depth at most 63, and defaults to a five-million-node work budget.
Overflow or budget exhaustion returns an error without exporting a partial count.
It closes a class only after accounting for the additive term and all positive
exceptions greater than 1. `--verify-lean` independently recomputes the count;
open classes remain unresolved. This establishes descent for the accepted
classes, not the full Collatz conjecture.

The saved depth-26 run certifies 66,071,490 accepted classes out of 67,108,864;
1,037,374 remain unresolved. Rust traversal took about 0.022 s and Lean replay
about 46 s in that run. These are separate, single-run timings and are not part
of the repeated search benchmark above.

## Correctness and proof checks

- Every generated input, result field, row ordering, and family summary matches
  the Python baseline. All 1,257 starts reach 1, with identical first-descent,
  first-arrival, and peak-bit metrics.
- Generated Lean certificate bodies match the Python version, apart from the
  provenance and output filename. Lean accepted all Rust-generated trajectories.
- The trajectory checker's soundness theorem has no axioms. Finite replay uses
  `native_decide`, which trusts Lean's compiler and native runtime.
- Rust tests cover large integers, known trajectories, fuel boundaries, complete seed
  parity, certificate filtering, and empty successful datasets.
- A parallel zero-fuel run yields 1,257 unresolved cases and an empty successful
  certificate. It does not silently report convergence. Relative certificate
  paths, invalid options, and output-path collision rejection were also checked.
- The complete suite passes 38 tests. The separate Lean integration test also
  passes at depths 0, 1, and 8; it is opt-in because it requires Lean.
  Formatting and Clippy with warnings denied pass. The analysis parity test
  requires Python; the production executables do not.

```sh
cargo test --locked
cargo test --locked --test residue_cli -- --ignored
cargo fmt --all -- --check
cargo clippy --locked --all-targets -- -D warnings
python3 bench/compare.py --check-only
```

The source is organized into [`src/search.rs`](src/search.rs) for exact arithmetic,
[`src/seeds.rs`](src/seeds.rs) for deterministic starts,
[`src/certificates.rs`](src/certificates.rs) for certificate generation, and
[`src/main.rs`](src/main.rs) for execution, parallel workers, artifacts, and Lean
invocation. Dependencies are pinned in `Cargo.lock`.

The additional command-line tools live in [`src/bin/`](src/bin/), with shared
positive-integer arithmetic and deterministic verifier sampling in
[`src/verify_helpers.rs`](src/verify_helpers.rs). Signed cycle equations in
`analyze` use `BigInt`; positive large-integer searches and verifiers use `BigUint`.

The mathematical objective remains unresolved. Faster search excludes more
specific candidates; it does not prove convergence of every positive integer.
See [ATTEMPT.md](ATTEMPT.md) for the proof attempts and remaining gap.
