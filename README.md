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
| `docs/ORBIT-PACKING-BOOTSTRAP.md` / `lean/PackingExponent.lean` | Written recursive interval bound with exponent H₂(log₃2), stronger universal escape restrictions, and checked exact supporting inequalities |
| `docs/ORBIT-PACKING-LOG.md` | Written uniform square-root-logarithm refinement and exclusion of the endpoint cumulative growth bound |
| `docs/NO-DESCENT-BALLOT.md` | Written sharper interval count and critical-power summability for starts that never descend, using a published ballot theorem |
| `docs/FOLDED-CYCLES.md` / `lean/FoldedCycleBounds.lean` | Written coprime-count restriction for integer cycles of odd spread below eight; kernel-checked finite order and rotation lemmas |
| `CollatzRepetition.lean` / `STURMIAN-ATTEMPT.md` | Checked finite parity-collision criterion and written exclusions of mechanical and substitution-generated itineraries |
| `lean/PrefixRepetition.lean` / `docs/PREFIX-REPETITION.md` | Kernel-checked growth and repeated-prefix return criterion; written exclusion of unbounded prefix squares in nonrepeating trajectories |
| `CollatzComplexity.lean` / `COMPLEXITY-GROWTH.md` | Checked growth bound using cumulative odd counts, finite descent-or-repeat criteria, and written density/complexity restrictions |
| `ORBIT-ESCAPE.md` / `CollatzEscapeBounds.lean` | Written inverse-power summability and running-maximum bounds; kernel-checked integer comparisons for a rational exponent |
| `CYCLE-ATTEMPT.md` | Written cycle-minimum bounds independent of period, with the remaining ordered-divisibility gap |
| `CollatzCycleBlocks.lean` / `CYCLE-WORDS.md` | Checked repeated-block divisibility obstruction and written exclusions of ordered cycle-word families |
| `CollatzCycleCriterion.lean` | Kernel-checked necessary and sufficient ordered cycle test for every nonempty positive halving word |
| `CollatzCycleBudget.lean` / `GENERAL-CYCLE-DEFECTS.md` | Checked joint budget for arbitrary halving exponents; written period, exponent, and height bounds |
| `CollatzCycleExtrema.lean` / `CYCLE-EXTREMA.md` | Checked prefix-rotation lemma and written sharp cycle-minimum extrema with explicit rational candidates |
| `docs/MECHANICAL-SWAP-EXCLUSION.md` / `lean/MechanicalDefectFinite.lean` / `lean/MechanicalLogBracket.lean` | Written exclusion of every single adjacent swap of a mechanical cycle word, supported by checked finite word and rational arithmetic; necessary distance bounds for arbitrary primitive cycles |
| `docs/MECHANICAL-DISTANCE-EXCLUSION.md` / `lean/MechanicalDistanceFinite.lean` | Written exclusion through half-Hamming distance 31 from every same-count cyclic mechanical word of slope p/N, supported by exact count-pair certificates |
| `docs/MECHANICAL-MASKS.md` / `lean/MechanicalMaskWitness.lean` | Written rational families showing limits of bounded discrepancy; checked distance-35 witness with 289 length-32 factors and failed integer divisibility |
| `docs/MASK-CYCLE-OBSTRUCTIONS.md` / `lean/MechanicalMaskArithmetic.lean` / `lean/MaskCatalogBounds.lean` | Kernel-checked mask divisibility normal form; written eventual exclusions for two families with independently chosen edits, with an unresolved finite cutoff |
| `lean/MaskSubsetDecoder.lean` / `lean/MaskSubsetFinite.lean` | Kernel-checked complete subset decoder; native finite certificates exclude all \(2^{80}\) and \(2^{1231}\) masks at two specified count pairs |
| `docs/MASK-TRANSITIONS.md` / `lean/MaskTransitionBounds.lean` | Written lower bound on adjacent halving-1 occurrences in surviving long masks; kernel-checked local repairs and supporting arithmetic |
| `docs/MASK-DENSITY.md` / `lean/MaskDensityBounds.lean` | Written empirical-entropy bound and positive densities of both good and bad blocks in surviving masks; checked finite distributions and power comparisons |
| `lean/BoundedStandardCycle.lean` | Direct convergence certificate through one million, kernel checker soundness, and triviality of any cycle with a checked small state |
| `CollatzCycleSeparation.lean` | Kernel-checked local replacement cancellation, numerator injectivity, and repeated-block edit exclusions |
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

The local `lean-toolchain` pins Lean 4.33.1, the latest stable release checked
on 13 September 2026. The initial migration checked 14 standalone proof files
and five generated certificate files; see [the migration record](results/lean-4.33.1/README.md).
Later range lemmas and finite mechanical-word certificates have
[their own verification record](results/mechanical-one-swap/verification.json).
The stronger distance result and direct convergence check have
[a newer verification record](results/mechanical-distance/verification.json),
including the expanded rational-bracket file.
The later kernel packing-transfer lemmas, entropy comparisons, and native-checked mechanical-mask witness have
[a separate verification record](results/packing-bootstrap/verification.json).
The subsequent exact mask arithmetic and catalog-cutoff comparisons have
[their own kernel verification record](results/mask-obstructions/verification.json).
The complete subset decoder and its two all-mask certificates have
[a later verification record](results/mask-decoder/verification.json).
The prefix-repetition criterion and mask-transition arithmetic have
[a kernel verification record](results/structural-restrictions/verification.json);
their analytic applications and the no-descent ballot bound are written proofs.
The later density and folded-order lemmas have
[their own record](results/folded-density/verification.json), with the full
cycle-order, entropy, and boundary-count arguments marked as written.
The Rust launchers embed this pin at build time, and the Python reference reads
the same file when verifying. Rebuild Rust after changing the pin.
For current reproduction commands,
see [ATTEMPT.md](ATTEMPT.md); historical CUDA commands are in §7 of [REPORT.md](REPORT.md).
