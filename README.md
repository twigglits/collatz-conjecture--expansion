# collatz-conjecture--expansion

An attempt to disprove or prove the positive-integer Collatz conjecture using exact searches and formally checked arguments. No counterexample or complete proof has been found.

**Read [ATTEMPT.md](ATTEMPT.md) for the current (3,1) attempt and its exact remaining gap.**
The earlier generalized-family study is in [REPORT.md](REPORT.md). The historical
[working paper](COLLATZ-EXPANSION.md) has scope errata; its July [PDF](COLLATZ-EXPANSION.pdf)
has not been updated and should not be used for the corrected claims.

The current search is written in **Rust**, with exact big integers and independent
Lean certificates. It measured **17.99× faster than Python with one worker** on
the identical 1,257-input workload. See [RUST-PORT.md](RUST-PORT.md) for benchmark
scope and reproduction; Lean verification remains a separate cost.

```sh
cargo run --release --locked -- --verify-lean
# Historical Python analysis now has Rust replacements:
cargo run --release --locked --bin analyze -- --verify-lean
cargo run --release --locked --bin verify-universal
cargo run --release --locked --bin verify-frontier
# Adaptive descent certificates for whole residue classes:
cargo run --release --locked --bin residue-sieve -- --depth 26 --verify-lean
```

Mathematical computational claims are backed by CUDA records or Lean proofs.
Performance timings are explicitly identified as empirical measurements.

| File | Role |
|---|---|
| `CollatzContradiction.lean` | Kernel-checked equivalence of universal descent and convergence, least-counterexample restrictions modulo 48, and ordinary/shortcut correspondence |
| `CollatzGrowth.lean` | Kernel-checked arbitrarily long initial growth and obstruction to a uniform finite descent horizon |
| `CollatzPeriodic.lean` | Kernel-checked integrality obstruction: an endlessly repeated halving block forces a cycle |
| `CollatzPacking.lean` / `APERIODIC-ATTEMPT.md` | Checked finite packing lemmas and written summability restrictions on divergent orbits |
| `CollatzRepetition.lean` / `STURMIAN-ATTEMPT.md` | Checked finite parity-collision criterion and written exclusions of mechanical and substitution-generated itineraries |
| `CollatzComplexity.lean` / `COMPLEXITY-GROWTH.md` | Checked growth bound using cumulative odd counts, finite descent-or-repeat criteria, and written density/complexity restrictions |
| `ORBIT-ESCAPE.md` / `CollatzEscapeBounds.lean` | Written inverse-power summability and running-maximum bounds; kernel-checked integer comparisons for a rational exponent |
| `CYCLE-ATTEMPT.md` | Written cycle-minimum bounds independent of period, with the remaining ordered-divisibility gap |
| `CollatzCycleBlocks.lean` / `CYCLE-WORDS.md` | Checked repeated-block divisibility obstruction and written exclusions of ordered cycle-word families |
| `src/` / `CollatzSearchCertsRust.lean` | Rust structured large-integer search, parallel workers, and independent Lean replay |
| `search_counterexample.py` / `CollatzSearchCerts.lean` | Python reference implementation and baseline certificates retained for independent comparison |
| `bench/compare.py` | Reproducible output comparison and Python/Rust timing, with raw results in `results/rust_benchmark.json` |
| `COLLATZ-EXPANSION.md` / `.pdf` | Working paper (typeset via pandoc → pdflatex): machine-verified structure of f(x)=ax+c — theorems, certificates, drift law, cycle-equation mechanism |
| `collatz.cu` | CUDA sweep engine: cycle inventory (Brent) + mass orbit classification for `f(x)=ax+c` variants |
| `universal.cu` | CUDA verifier for the sharpened universal-cycle laws: rigidity grid (2.7e11 pairs), fixed-point census vs. the divisor law, universal-family catalog (all odd a < 2^24), scaling-identity fuzz |
| `CollatzTheory.lean` | General theorems, kernel-only proofs (parity reduction, scaling conjugacy, gcd absorption, universal cycle for a = 2^k−1 **and its converse**: master formula F(c) = odd(a+1)·c, one-step cycle law, orbit transport) |
| `CollatzCerts.lean` | Generated certificates: 89 cycle proofs (`decide`) + 38 range-classification proofs (`native_decide`) |
| `CollatzFrontier.lean` | Frontier theorems, kernel-only: Böhm–Sontacchi cycle equation proved for **all** parameters (was: verified on 89 instances) + the forced drift bound 2^H > a^k for every cycle; repulsion (dual of absorption); coset confinement of orbits in c·⟨2⟩ mod a; finite Terras descent with certified good-residue densities (86.84% of classes mod 2^20) |
| `src/bin/analyze.rs` / `analyze.py` | Rust GPU-output analysis and retained Python reference; exact signed cycle equations and Lean certificate generation |
| `src/bin/verify-universal.rs` / `verify_universal.py` | Rust universal-family verifier and Python reference: catalog re-iteration, law set-equality, 350-digit stress instances |
| `src/bin/verify-frontier.rs` / `verify_frontier.py` | Rust frontier verifier and Python reference: formula fuzz, cycle equations, and direct good-residue counts |
| `src/residue.rs` / `src/bin/residue-sieve.rs` | Adaptive whole-class descent search with checked arithmetic, work limits, and independent Lean count verification |
| `results/` | Raw sweep JSON, summary tables, logs |

The local `lean-toolchain` pins Lean 4.31.0. For current reproduction commands,
see [ATTEMPT.md](ATTEMPT.md); historical CUDA commands are in §7 of [REPORT.md](REPORT.md).
