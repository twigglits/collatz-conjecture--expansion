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
| `lean/CoalescenceDescent.lean` | Kernel coalescence induction, depth-eight residue certificates, and impossibility of a uniform bound on both meeting times; [verification](results/coalescence/verification.json) |
| `lean/CoalescenceHeight.lean` | Kernel logarithmic lower bound on required meeting horizons and exact step-59 obstruction at 27; [verification](results/coalescence-height/verification.json) |
| `lean/CoalescenceEnvelope.lean` | Kernel two-sided affine envelope and sufficient graph-rank criterion; written finite-affine rank obstruction and SMT search have [separate scopes](results/coalescence-envelope/verification.json) |
| `lean/ValuationGraphRank.lean` | Kernel progression identities and 108 exact certificates supporting a written four-feature valuation rank obstruction; [scope and verification](results/valuation-graph-rank/verification.json) |
| `lean/GraphRankNecessity.lean` / `lean/QuadraticValuationRank.lean` | Kernel forced forward descent for natural graph ranks on multiples of three; six patterns and 162 exact certificates support a written proper quadratic valuation rank exclusion; [verification](results/quadratic-valuation-rank/verification.json) |
| `lean/GraphRankOrientation.lean` | Kernel functional-graph theorem forcing forward descent outside a forward-closed base; excludes natural graph ranks monotone on matching valuation features; broader written corollary and [verification](results/graph-rank-orientation/verification.json) |
| `lean/DigitBlockRank.lean` | Kernel obstruction to separated-block integer ranks; a written counting argument applies it to zero-padded weighted binary windows of every fixed width; [verification](results/digit-block-rank/verification.json) |
| `lean/InverseBasinAudit.lean` | Kernel basin classification at multiples of three, collisions at other roots, and chain restriction for injective forward-closed basin subsets; [verification and literature-audit scope](results/inverse-basin-audit/verification.json) |
| `lean/InverseFibreGrowth.lean` | Kernel same-weight fibre translation and 48 colliding residues in every aligned block; written exponential multiplicity lower bound and [verification](results/inverse-fibre-growth/verification.json) |
| `lean/UniformInverseBranching.lean` | Kernel binary inverse trees for every root coprime to three: 2^h distinct leaves with time 6h, weight h and explicit height bound; [verification](results/uniform-inverse-branching/verification.json) |
| `lean/BasinResidueShadow.lean` | Kernel conditional arithmetic transport into mixed residue cylinders; written inverse-basin density and one-class convergence criterion; [verification](results/basin-residue-shadow/verification.json) |
| `lean/ResidueShadowCost.lean` | Kernel conditional size bounds and odd-root injectivity; written bounded-time linear-cost embeddings and sharp fixed-prefix limitation; [verification](results/residue-shadow-cost/verification.json) |
| `lean/AdaptiveInverseBarrier.lean` | Kernel complete inverse-level transport at roots 1 modulo 3^K and exclusion of smaller ancestors through depth K; written unit-root two-sided extension; [verification](results/adaptive-inverse-barrier/verification.json) |
| `lean/HalfSlopeDescent.lean` | Kernel additive-error bound: a first half-multiplier crossing with 2w<3n, or any half crossing by time n, guarantees descent; universal crossing existence remains unproved; [verification](results/half-slope-descent/verification.json) |
| `lean/FirstSlopeBudget.lean` | Kernel first-drop additive bound, exact coefficient-gap criterion and polynomial budget; a written logarithm estimate supplies a large-time sufficient bound, without proving universal stopping; [verification](results/first-slope-budget/verification.json) |
| `CollatzPeriodic.lean` | Kernel-checked integrality obstruction: an endlessly repeated halving block forces a cycle |
| `CollatzPacking.lean` / `APERIODIC-ATTEMPT.md` | Checked finite packing lemmas and written summability restrictions on divergent orbits |
| `docs/ORBIT-PACKING-BOOTSTRAP.md` / `lean/PackingExponent.lean` | Written recursive interval bound with exponent H₂(log₃2), stronger universal escape restrictions, and checked exact supporting inequalities |
| `docs/ORBIT-PACKING-LOG.md` | Written uniform square-root-logarithm refinement and exclusion of the endpoint cumulative growth bound |
| `docs/NO-DESCENT-BALLOT.md` | Written sharper interval count and critical-power summability for starts that never descend, using a published ballot theorem |
| `docs/FOLDED-CYCLES.md` / `lean/FoldedCycleBounds.lean` | Written coprime-count restriction for integer cycles of odd spread below eight; kernel-checked finite order and rotation lemmas |
| `docs/FOLDED-CYCLE-INVERSIONS.md` / `lean/FoldedCycleNine.lean` | Written coprimality extension to odd maximum \(M<9m+2\), with inversion-count restrictions below spread sixteen; kernel-checked inversion classification and forward-closure lemmas |
| `docs/NARROW-CYCLE-MASKS.md` / `lean/NarrowCycleMasks.lean` | Written reduction of every nontrivial integer cycle with \(3M+1<8m\) to the critical mask family, extending its period exclusions to arbitrary narrow cycles; kernel-checked count, power, and local layer arguments |
| `docs/MASK-FOLDED-ORDER.md` / `lean/MaskFoldedOrder.lean` | Kernel-checked automatic rank order for arbitrary positive forcing at close coprime counts; written application showing that ordering does not reject the surviving mask range |
| `CollatzRepetition.lean` / `STURMIAN-ATTEMPT.md` | Checked finite parity-collision criterion and written exclusions of mechanical and substitution-generated itineraries |
| `lean/PrefixRepetition.lean` / `docs/PREFIX-REPETITION.md` | Kernel-checked growth and repeated-prefix return criterion; written exclusion of unbounded prefix squares in nonrepeating trajectories |
| `CollatzComplexity.lean` / `COMPLEXITY-GROWTH.md` | Checked growth bound using cumulative odd counts, finite descent-or-repeat criteria, and written density/complexity restrictions |
| `ORBIT-ESCAPE.md` / `CollatzEscapeBounds.lean` | Written inverse-power summability and running-maximum bounds; kernel-checked integer comparisons for a rational exponent |
| `CYCLE-ATTEMPT.md` | Written cycle-minimum bounds independent of period, with the remaining ordered-divisibility gap |
| `CollatzCycleBlocks.lean` / `CYCLE-WORDS.md` | Checked repeated-block divisibility obstruction and written exclusions of ordered cycle-word families |
| `CollatzCycleCriterion.lean` | Kernel-checked necessary and sufficient ordered cycle test for every nonempty positive halving word |
| `docs/CYCLE-LOCAL-LIFTS.md` / `lean/CycleLocalLifts.lean` | Kernel-checked exact residue-cycle witnesses for every positive-denominator word modulo every \(2^a3^b\), showing the limitation of congruence consistency alone; a fixed-height lemma recovers integer divisibility |
| `CollatzCycleBudget.lean` / `GENERAL-CYCLE-DEFECTS.md` | Checked joint budget for arbitrary halving exponents; written period, exponent, and height bounds |
| `CollatzCycleExtrema.lean` / `CYCLE-EXTREMA.md` | Checked prefix-rotation lemma and written sharp cycle-minimum extrema with explicit rational candidates |
| `docs/MECHANICAL-SWAP-EXCLUSION.md` / `lean/MechanicalDefectFinite.lean` / `lean/MechanicalLogBracket.lean` | Written exclusion of every single adjacent swap of a mechanical cycle word, supported by checked finite word and rational arithmetic; necessary distance bounds for arbitrary primitive cycles |
| `docs/MECHANICAL-DISTANCE-EXCLUSION.md` / `lean/MechanicalDistanceFinite.lean` | Written exclusion through half-Hamming distance 31 from every same-count cyclic mechanical word of slope p/N, supported by exact count-pair certificates |
| `docs/MECHANICAL-MASKS.md` / `lean/MechanicalMaskWitness.lean` | Written rational families showing limits of bounded discrepancy; checked distance-35 witness with 289 length-32 factors and failed integer divisibility |
| `docs/MASK-CYCLE-OBSTRUCTIONS.md` / `lean/MechanicalMaskArithmetic.lean` / `lean/MaskCatalogBounds.lean` | Kernel-checked mask divisibility normal form; written exclusions for two independently edited families, now covering every period through the later explicit logarithm argument |
| `docs/MASK-RANK-ARITHMETIC.md` / `lean/MaskRankArithmetic.lean` | Kernel-checked geometric coefficient arithmetic and normalized binary mask equation; written mechanical reindexing, exact gcd corollary, and limitation of fixed small-divisor tests |
| `lean/MaskSubsetDecoder.lean` / `lean/MaskSubsetFinite.lean` | Kernel-checked complete subset decoder; native finite certificates exclude all \(2^{80}\) and \(2^{1231}\) masks at two specified count pairs |
| `docs/MASK-TRANSITIONS.md` / `lean/MaskTransitionBounds.lean` | Written lower bound on adjacent halving-1 occurrences in surviving long masks; kernel-checked local repairs and supporting arithmetic |
| `docs/MASK-DENSITY.md` / `lean/MaskDensityBounds.lean` | Written empirical-entropy bound and positive densities of both good and bad blocks in surviving masks; checked finite distributions and power comparisons |
| `docs/MASK-RESONANCE.md` / `lean/MaskResonance.lean` | Written exclusion of every independent critical 21-to-12 mask for \(2^{21}\le N\le10^{1000}\), with an exact native rational cover and kernel checker soundness; the published Eliahou bound closes the smaller range using external computation |
| `docs/EXPLICIT-LOG-GAP.md` / `lean/ExplicitLogConstants.lean` / `lean/MaskResonanceExtended.lean` | Written explicit logarithm bound and exact cover through \(10^{4000}\); all-period exclusions of three mask subclasses, numerical transition and density cutoffs, and the arbitrary-cycle bound \(4M\ge9m+5\); finite arithmetic checked in Lean, with external prime and small-period inputs |
| `docs/MASK-SPAN-BOUND.md` / `lean/MaskSpanBounds.lean` | Written stronger all-period odd-span bound \(20M>49m\), from a geometric restriction on edit positions; kernel-checked phase, grid, block-count, and exact cutoff arithmetic, with the existing external inputs |
| `docs/NATURAL-DENSITY-ALMOST-BOUNDED.md` / `verify_natural_density.py` | Written natural-density upgrade of Tao's almost-bounded-orbits theorem via joint fine-scale mixing and a renewal lemma; numerical sanity checks only, external inputs from Tao's paper; [record](results/natural-density/verification.json) |
| `docs/DENSITY-TO-POINTWISE.md` | Written limiting minimum law and component densities; an overshoot bound extends predecessor densities to every target, with summed packing bounds and increase along forward orbits; convergence to one remains unproved |
| `docs/PREDECESSOR-DENSITY-REVIEW.md` | Independent source replay passed for all 389 modules of the external positive predecessor-density theorem; upper-density-one convergence would suffice for Collatz, but remains unproved; [verification](results/predecessor-density-review/verification.json) |
| `docs/PREDECESSOR-DENSITY-FLOW.md` | Written decay of predecessor densities within each fixed basin and countable inverse-branch flow at nonperiodic roots; kernel bounded-time fibre and graph lemmas; no decay along all divergent forward orbits proved; [verification](results/predecessor-density-flow/verification.json) |
| `docs/UNIFORM-PREDECESSOR-APPROXIMATION.md` / `lean/PassageApproximation.lean` | Written convergence of predecessor proportions uniformly over all targets, with a finite-mixture approximation; kernel first-passage comparison; moving-target smallness remains unproved; [verification](results/uniform-predecessor-approximation/verification.json) |
| `docs/DENSITY-BRANCH-LEAKAGE.md` / `verify_density_branch_leakage.py` | Written summability of unused-branch densities on a hypothetical divergent orbit; an unproved relative logarithmic lower bound would exclude divergence, while absolute reciprocal-target bounds are summable; exact finite branch counts, with no asymptotic ratio claim; [verification](results/density-branch-leakage/verification.json) |
| `docs/DENSITY-COUNTERMODEL.md` / `lean/DensityCountermodel.lean` | An explicitly different map retains even halving, the known cycle, diffuse first passage, and positive predecessor densities while half its starts escape; kernel escaping family, written density formulas, and exact finite replay; not a Collatz counterexample; [verification](results/density-countermodel/verification.json) |
| `docs/DENSITY-TIME-TRUNCATION.md` / `lean/DensityTimeTruncation.lean` | Kernel maximum of 38 twelve-step predecessors and all-depth fibre bounds; written necessary clock, density accumulation values, and exact obstruction to truncating eventual hits; no sufficient clock or exclusion of divergence; [verification](results/density-time-truncation/verification.json) |
| `docs/CLOCKED-MINIMUM.md` / `lean/ClockedMinimum.lean` | Conditional written typical minimum-attainment time `(3/log(4/3)) log n`; 22 kernel minimum and clock-transfer lemmas, with exact finite replay; a fixed `11 log X` clock captures each target's density, while the uniform defect still equals the unknown divergent-component mass; [verification](results/clocked-minimum/verification.json) |
| `docs/PREFIX-COALESCENCE-AUDIT.md` / `lean/ReflectedCoalescence.lean` | Seven kernel lemmas show exact plus/minus reflection and identical adjacent coalescence counts; written bounds distinguish complete parity periods from the actual logarithmic-clock source interval; neither statistic proves convergence density one; [verification](results/prefix-coalescence/verification.json) |
| `docs/SPARSE-COLLATZ-PERTURBATION.md` / `lean/SparseCollatzPerturbation.lean` | An explicitly altered map swaps only logarithmically many odd inputs, retains inverse congruences and unit-target predecessor positivity, and has a kernel-proved escaping path; conditional written passage stability shows why the shared density inputs do not exclude escape; 20 audited kernel roots; [verification](results/sparse-collatz-perturbation/verification.json) |
| `docs/WEIGHTED-DISSIPATION.md` / `lean/WeightedDissipation.lean` | Eighteen audited kernel roots verify actual-map loss accounting and cycle weights; a conditional written probability law identifies an unresolved escape mass, also measured by the mean remaining weight at a fixed logarithmic clock; exact finite rational checks do not establish that this mass is zero; [verification](results/weighted-dissipation/verification.json) |
| `docs/COALESCENCE-TAIL.md` / `lean/CoalescenceTail.lean` | Twenty-three audited kernel roots prove exact stopped odd-count mass and an all-depth `1/H` lower bound on balanced noncoalescence, separately for both initial parities; written arguments give infinite mean fusion time and a weighted dyadic criterion whose unweighted sufficient condition is ruled out in the following audit; [verification](results/coalescence-tail/verification.json) |
| `docs/DYADIC-COALESCENCE-DEFECTS.md` / `lean/DyadicCoalescenceDefects.lean` | Eighteen audited kernel roots give strict first-arrival contraction, grade transport, and a three-odd-step bound for balanced descendants of one; written counting plus replayed positive basin density proves the actual unweighted dyadic errors are nonsummable, without determining the weighted escape mass; [verification](results/dyadic-coalescence-defects/verification.json) |
| `docs/GRADE-WEIGHT-MOMENTS.md` / `lean/GradeWeightMoments.lean` | Thirteen audited kernel roots give exact affine moments; an unconditional written bound makes the auxiliary grade-weight mean decay as `O(X^(-log₂(8/7)))`, uniformly after `ceil(log₂ X)` steps; the separate escape-weight variation bound remains unproved; [verification](results/grade-weight-moments/verification.json) |
| `docs/ESCAPE-WEIGHT-REFINEMENTS.md` / `lean/EscapeWeightRefinements.lean` | Twenty-one audited kernel roots give actual escape-weight refinement arithmetic, reciprocal moments, and infinitely many large individual jumps; written bounds make every fixed-offset energy finite but disprove monotone energy contraction; a stronger rigidity argument removes passage mixing from the sufficient escape-exclusion criterion, whose required limiting energy bound remains open; [verification](results/escape-weight-refinements/verification.json) |
| `docs/COALESCENCE-ENERGY-CAPS.md` / `lean/CoalescenceEnergyCaps.lean` | Seventeen kernel roots give coalescence transport on actual source annuli and an exact time cutoff; written bounds improve to `E_s <= 0.542s+6`, but prove that combining these unweighted caps with the current tail cannot yield bounded energy; an even-pair family separates equal odd counts from fusion; [verification](results/coalescence-energy-caps/verification.json) |
| `docs/ORDERED-WEIGHT-DRIFT.md` / `lean/OrderedWeightDrift.lean` | Thirty-one kernel roots give shifted-weight order, first-return endpoint order, exact one-turn parity counts, and a reversed-count jump family; a written argument bounds the total ordered negative drift over all offsets by 14; the reversal contribution remains open and cannot have a uniform pointwise charge to immediate parent losses; [verification](results/ordered-weight-drift/verification.json) |
| `docs/REVERSAL-PERSISTENCE.md` / `lean/ReversalPersistence.lean` | Eight kernel roots prove endpoint retention and reversed jumps lasting linearly many steps; written bounds rule out fixed future-step charges and charging a cell's accumulated drift to all its future parent losses; whole-annulus charging remains open, with exact finite comparisons recorded separately; [verification](results/reversal-persistence/verification.json) |
| `docs/COUNT-RETURN-CONTROL.md` / `lean/CountReturnControl.lean` | Twelve kernel roots check restart accounting, return-descent transitions, and constants; a separate written probability proof bounds the full count-gap mean, gives polynomial balanced coalescence, and improves actual energy growth to `O(s^(4/5))`; bounded energy and Collatz remain open; [verification](results/count-return-control/verification.json) |
| `docs/ANNULUS-HEIGHT-COUPLING.md` / `lean/AnnulusHeightCoupling.lean` | Twelve kernel roots give an exponentially small normalized-height error and signed count mean one on actual source intervals; written bounds control logarithmic height separation and cumulative return costs; exact weight transport retains a ternary progression whose averaging remains open; [verification](results/annulus-height-coupling/verification.json) |
| `docs/COUNT-RETURN-CLOCK.md` / `lean/CountReturnClock.lean` | Fifteen kernel arithmetic roots support a written square-root count-return tail, balanced noncoalescence of order `H^(-1/2)`, and actual energy `O(sqrt(s))`; return-separation costs are summable for every power below `1/3`; raw image coefficients are unbounded, and bounded actual energy remains open; [verification](results/count-return-clock/verification.json) |
| `docs/RETURN-IMAGE-BOUNDS.md` / `lean/ReturnImageBounds.lean` | Twelve kernel roots support written logarithmic moments of separation-weighted return-image densities and controlled truncation bounds on finite integer intervals; the pairing with actual future weighted gradients remains open; [verification](results/return-image-bounds/verification.json) |
| `docs/RETURN-CORRECTION-MOMENTS.md` / `lean/ReturnCorrectionMoments.lean` | Twelve kernel roots check affine correction and finite stopping identities; the written boundary-stop argument extends return-separation moments to every power below `1/2`, gives the image truncation rate `7 H^(beta-1/2)/(1-2 beta)`, and reduces the explicit return-cycle constant; bounded energy and Collatz remain open; [verification](results/return-correction-moments/verification.json) |
| `docs/RETURN-OCCUPATION-DENSITY.md` / `lean/ReturnOccupationDensity.lean` | Fifteen kernel roots support a written exponential cycle-count moment and logarithmic bounds for the density accumulated over all nonfused returns; a fixed separation-one return has unbounded pointwise excursion cost; actual weighted energy remains open; [verification](results/return-occupation-density/verification.json) |
| `docs/GRADIENT-ORLICZ-OBSTRUCTION.md` / `lean/GradientOrliczObstruction.lean` | Eight kernel roots support a written failure of uniform `exp((G/C)^p)` moments, `p>1`, for accumulated actual returned gradients on both their intervals and progressions; this blocks a direct complementary-norm use of the current logarithmic density bounds, without disproving an averaged energy bound; [verification](results/gradient-orlicz-obstruction/verification.json) |
| `docs/BINARY-IMAGE-ENERGY.md` / `lean/BinaryImageEnergy.lean` | Eleven kernel roots give image-fibre injection and exact numerator mass; written quadratic image energy and interpolation prove all-return `K*_beta in Lp` for `p<10/(9+2beta)`, `0<=beta<1/2`, with finite interval transfer; the actual gradient pairing remains open; [verification](results/binary-image-energy/verification.json) |
| `docs/ANNULUS-TIME-BUDGETS.md` / `lean/AnnulusTimeBudgets.lean` / `lean/BinaryConePredecessors.lean` | Twelve kernel roots support exact all-time costs on fifteen finite annuli and an explicit convergent inverse spine; written binary-cone density makes sublinear reversed drift at each fixed level sufficient to exclude escape without PLD, but that universal hypothesis remains open; [verification](results/annulus-time-budgets/verification.json) |
| `docs/BUDGET-AXIOM-AUDIT.md` / `lean/BudgetAxiomAudit.lean` | Kernel counterexample to a public claimed proof's added 200-step budget axiom; the witness itself reaches 1; [exact replay and build](results/budget-axiom-audit/verification.json) |
| `docs/WEIGHTED-SURVIVORS.md` / `lean/WeightedSurvivors.lean` | Kernel inverse-cone and fixed-floor foundations; written weighted contraction criteria and timing implications; exact finite replay disproves the naive one-third share bound, with the required recurrent gap still unproved; [verification](results/weighted-survivors/verification.json) |
| `docs/WEIGHTED-BASIN-BARRIER.md` / `lean/WeightedBasinBarrier.lean` | Kernel convergent rising families and single-exit basins; written obstruction to uniform aggregate contraction from backward closure, even for cofinite populations with absorbed complements; rules out power loss bounds below log₂3 on that class; [verification](results/weighted-basin-barrier/verification.json) |
| `docs/FINITE-PATH-PACKING.md` / `lean/FinitePathPacking.lean` | Kernel finite-prefix transport and first-entry distinctness; written packing bound for all simple finite paths and a correction estimate independent of entry time; universal entry remains unproved; [verification](results/finite-path-packing/verification.json) |
| `docs/EQUAL-WEIGHT-FIBRES.md` / `lean/EqualWeightFibres.lean` | Kernel inverse-fibre bounds and conditional stabilization; written divergence restriction; complete finite plateau and all-time exclusion of a smaller equal-weight mate for the convergent start 27; [verification](results/equal-weight-fibres/verification.json) |
| `docs/COALESCENCE-GRADES.md` / `lean/CoalescenceGrades.lean` | Kernel arrival-grade classification, explicit power-of-two minima, sharp clock/count gaps for 27, and a conditional integer rank; finite per-source odd/even credit is equivalent to full Collatz and remains unproved; [verification](results/coalescence-grades/verification.json) |
| `docs/PARITY-SURVIVAL.md` / `lean/ParitySurvival.lean` | Kernel survivor parity bounds and the improved conditional hitting time `4A+5b+71`; logarithmic credit is equivalent to logarithmic total time, and neither universal bound is proved; [verification](results/parity-survival/verification.json) |
| `docs/FIBRE-PREFIX-BOUND.md` / `lean/FibrePrefixBound.lean` | Kernel all-depth inverse-fibre counting recurrence and sharp two-even bound; written exponential upper bound with base about 1.72654 and square-root coefficient moment; [verification](results/fibre-prefix-bound/verification.json) |
| `docs/SURVIVOR-EXIT-MASS.md` / `verify_survivor_exit_mass.py` | Exact forward first-entry checks and written tail bounds certify actual infinite survivor-mass contraction at 128 finite horizons; no infinite extension is proved; [verification](results/survivor-exit-mass/verification.json) |
| `docs/EXIT-CERTIFICATE-BUDGET.md` / `lean/ExitCertificateBudget.lean` | Kernel integer telescoping and product budgets; written cutoff and precision growth requirements for infinitely many exit certificates, with no guarantee of further successes; [verification](results/exit-certificate-budget/verification.json) |
| `docs/KILLED-OPERATOR-BOUNDS.md` / `lean/KilledOperatorBounds.lean` | Kernel source-weight comparisons and convergent all-depth witnesses; written exact spectral and essential spectral radius `(3/2)^s` on the summably weighted function space, which does not decide decay of the actual survivor mass; [verification](results/killed-operator-bounds/verification.json) |
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
The forward-closure extension and inversion classification have
[a Linux verification record](results/folded-inversions/verification.json);
their full cycle-order and permutation arguments remain written.
The unrestricted-mask resonance result has
[an exact arithmetic verification record](results/mask-resonance/verification.json),
including the complete rational cover and an independent Python replay.
Its real logarithm and cycle arguments, and the external small-period input,
are distinguished from the local Lean checks.
The narrow-cycle reduction and the preceding automatic-order theorem have
[a further verification record](results/narrow-cycle-masks/verification.json).
Their new finite algebra is kernel checked; the global cycle sorting and
applications of earlier analytic results remain written arguments.
The explicit logarithm bound and extended cover have
[a subsequent verification record](results/explicit-log-gap/verification.json).
It separates the finite kernel and native checks from the written all-index
integral and denominator arguments and the published external inputs.
The stronger span bound has [its own verification record](results/mask-span/verification.json).
Its new arithmetic is kernel checked; the real rotation and complete cycle
arguments remain written, with finite Python checks of boundary cases and
nonintegral rational examples.
The local-lift theorem has [a separate verification record](results/cycle-local-lifts/verification.json).
Its arbitrary-word construction, precision loss during division, exact
valuations, and complementary height lemma are all kernel checked.
The mask rank arithmetic has [its own verification record](results/mask-rank-arithmetic/verification.json).
Its modular algebra and exponent bridge use kernel proofs; the full mechanical
reindexing and fixed-modulus coverage argument remain written proofs.
The Rust launchers embed this pin at build time, and the Python reference reads
the same file when verifying. Rebuild Rust after changing the pin.
For current reproduction commands,
see [ATTEMPT.md](ATTEMPT.md); historical CUDA commands are in §7 of [REPORT.md](REPORT.md).
