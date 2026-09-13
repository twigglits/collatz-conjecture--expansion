# Attempt to disprove or prove the positive-integer Collatz conjecture

**Status: unresolved.** No counterexample or complete proof has been found.
The objective is still convergence for **every positive integer** under
`C(n) = 3n+1` for odd n and `C(n) = n/2` for even n. Structural theorems,
finite computations, and obstructions to particular constructions are partial
results. They do not establish that finding a counterexample is impossible.

## Counterexample search

The current search uses arbitrary-precision integers and ordinary Collatz steps.
The Rust implementation is in [`src/`](src/); the Python implementation is kept
as an independent reference for output comparison and benchmarking.

The initial dataset contains **1,257 distinct odd starts above 2^71**, spanning
**72–8,198 bits**. It combines offsets around powers of two, starts of the form
`q·2^k−1`, prescribed parity prefixes whose affine slope never drops below one,
and deterministic SHAKE256 controls. The longest prescribed prefixes contain
8,192 shortcut steps. This is a selected dataset, not verification of an interval.

All 1,257 reached 1. Their trajectories contain **12,417,483 ordinary steps** in
total; the largest encountered value has **12,996 bits**. The hardest tested seed,
`11·2^8192−1`, first fell below its start after **52,367 steps** and reached 1 after
**111,072 steps**. These numbers are independently replayed and checked in Lean,
including the first descent, first arrival at 1, and peak bit length.

The fuel limit is 300,000 ordinary steps per start. Reaching that limit is
explicitly **unresolved**, never proof of divergence. Brent detection flags a
nontrivial repeated value for an additional cycle certificate; no such case
occurred. There is no machine-word escape window and no reliance on an externally
verified range to conclude convergence of these starts.

The Python baseline is [`results/counterexample_search.json`](results/counterexample_search.json)
with [`CollatzSearchCerts.lean`](CollatzSearchCerts.lean). The Rust replay produces
`results/counterexample_search_rust.json` and `CollatzSearchCertsRust.lean`.
The generic checker-soundness theorem has no axioms. The finite computations use
`native_decide`, so they trust Lean's compiler and native runtime in addition to
the logical checker. This distinction is recorded in the logs and manifests.

The much larger *continuous interval* verification in the literature is separate:
Barina's project reports all starts below `2075·2^60` verified when checked on
12 September 2026. Large isolated starts here do not extend that continuous
bound. [Project status](https://pcbarina.fit.vutbr.cz/)

## Exact descent over infinite residue classes

The Rust [`residue-sieve`](src/bin/residue-sieve.rs) explores exact identities
`U^k(2^k*q+r) = A*q+b`. When `A < 2^k`, the smallest quotient guaranteeing
strict descent is zero if `b < r`, and otherwise
`floor((b-r)/(2^k-A))+1`. The additive term is included. The sieve closes a
whole class only when all its members greater than 1 descend; it continues
splitting classes with nontrivial finite exceptions.

At depth 26, **66,071,490 of the 67,108,864 residue classes** are accepted.
Every member greater than 1 of an accepted class descends within 26 shortcut
steps. The other **1,037,374 classes remain unresolved** by this certificate.
This is a statement about infinite classes, not merely the first block of
starting values, and it proves descent rather than full convergence of each
accepted start.

[`CollatzResidueCerts.lean`](CollatzResidueCerts.lean) independently recomputes
the accepted count. It includes the kernel proofs from
[`CollatzAffine.lean`](CollatzAffine.lean) and
[`lean/ResidueSieveBody.lean`](lean/ResidueSieveBody.lean): exact affine
thresholds, whole-class soundness, periodicity of the acceptance predicate,
and equality of the pruned tree count with the actual residue count in every
aligned block. Only the numeric count uses `native_decide`. The verified
manifest is [`results/residue_sieve_rust.json`](results/residue_sieve_rust.json);
other Rust diagnostics are explicitly marked as uncertified.

## Attempt by contradiction

[`CollatzContradiction.lean`](CollatzContradiction.lean) proves the exact equivalence

\[
 (\forall n>0,\;\exists t,\ C^t(n)=1)
 \quad\Longleftrightarrow\quad
 (\forall n>1,\;\exists t,\ C^t(n)<n).
\]

The reverse implication uses strong induction: a smaller positive iterate
converges by the induction hypothesis, so its predecessor does too. No uniform
bound on t is assumed. The file also proves the correspondence with the shortcut
map `U(n)=(3n+1)/2` for odd n and `n/2` for even n.

If the conjecture is false, well-ordering gives a smallest counterexample N.
Every forward iterate of N stays at least N, and no smaller positive integer
can reach N. These two directions yield infinite-family exclusions:

- Even starts descend immediately.
- `4q+1` reaches `3q+1` in three ordinary steps, giving descent for q>0.
- `16q+3` reaches `9q+2` in six ordinary steps, giving descent for all q≥0.
- `6q+5` has the smaller predecessor `4q+3`, which reaches it in two steps.

Consequently a smallest counterexample must satisfy

\[
 N\bmod48\in\{7,15,27,31,39,43\}.
\]

Lean proves that universal eventual descent restricted to these six classes is
still equivalent to the full conjecture. **The missing proof is descent for
every member of those infinite classes.** Their finite set of residue labels
does not make that a finite problem.

## Why arbitrarily long growth does not disprove the conjecture

[`CollatzGrowth.lean`](CollatzGrowth.lean) proves, for q>0,

\[
 U^k(2^{k+m}q-1)=2^m3^kq-1.
\]

In particular, for every chosen horizon K there is a positive start that does
not descend in its first K shortcut steps. Thus a proof based on one fixed
descent horizon for all starting values cannot work.

This does not provide a single start that grows forever. The compatible residue
conditions `n ≡ −1 (mod 2^k)` for all k would require every power of two to divide
the positive integer n+1. Lean also proves this impossible for every natural n.
The quantifiers `for every K, some n` cannot be swapped to `some n, for every K`.

## Attempt to construct divergence with repeating or growing patterns

For an accelerated odd orbit write `2^h_i n_(i+1)=3n_i+1`, where h_i≥1.
[`CollatzPeriodic.lean`](CollatzPeriodic.lean) proves that an eventually periodic
halving schedule forces an eventually periodic integer orbit. A positive period
is required for the cycle interpretation. No boundedness assumption is used.

For a fixed block, let P=3^k, Q=2^H, and W be its positive affine correction.
Successive block boundaries satisfy `Qx_(j+1)=Px_j+W`. Differences therefore obey
`Q^r d_r=P^r d_0`. Since P and Q are coprime, every Q^r divides d_0, forcing
d_0=0. Thus repeating an expanding real affine formula cannot construct an
infinite divergent integer Collatz orbit. The formal file also proves that an
arbitrary infinite positive halving schedule has at most one integer realization.

The written proof in [`PERIODIC-OBSTRUCTION.md`](PERIODIC-OBSTRUCTION.md) goes
further for a specific nonperiodic construction. A run of L exponents equal to
one beginning at odd-step time t requires

\[
 2^{L+t+1}\le3^t(n_0+1).
\]

The schedule formed by concatenating `(2,1)`, `(2,1,1)`, `(2,1,1,1,1)`, and so on
violates that inequality for every fixed positive n_0. It cannot be an integer
counterexample. This last exclusion is a written mathematical proof, not a
claim of Lean verification. Other aperiodic schedules remain possible under the
constraints proved here.

These periodicity principles are classical; the contribution here is their
explicit derivation, application to proposed counterexamples, and formal
checking, without a claim of mathematical novelty.
[Bernstein–Lagarias](https://websites.umich.edu/~lagarias/doc/bernstein.pdf)

## Nonperiodic patterns: growth and word complexity

The written [`APERIODIC-ATTEMPT.md`](APERIODIC-ATTEMPT.md) proves a power
bound on how many values a nonrepeating orbit can occupy in an interval.
It yields a finite sum of reciprocals and a bounded multiplicative correction:
for an accelerated divergent orbit, `3^k / 2^H_k` must tend to infinity.
[`CollatzPacking.lean`](CollatzPacking.lean) now checks the finite ingredients:
the sharp residue-image bound `U^k(r) < 3^wt(k,r)` and a corresponding
fixed-weight packing theorem. The summability and limit arguments remain
written proofs.

[`ORBIT-ESCAPE.md`](ORBIT-ESCAPE.md) strengthens the counting estimate to
`#(O ∩ [a,a+X)) ≤ 10 X^θ`, where θ is defined by an entropy equation and is
approximately 0.96538. It follows that `Σ A_k^(-s)` converges for every
`s>θ`, and the running maximum of `A_k=3^k/2^H_k` is at least a constant
times `k^(1/θ)`. Hence any orbit with `A_k=O(k^β)`, `β<1/θ`, eventually
repeats. This is an aggregate growth restriction, not a bound on every
individual iterate. Exponential growth remains compatible. A rational
exponent 31/32 suffices for a weaker version; its two integer comparisons
are kernel-checked in [`CollatzEscapeBounds.lean`](CollatzEscapeBounds.lean),
while the full counting and analytic proof remains written.

The [recursive packing proof](docs/ORBIT-PACKING-BOOTSTRAP.md) now improves
this to `#(S ∩ [a,a+L)) ≤ 128 L^σ` for integer intervals, with
`σ=H₂(log₃2)≈0.94996`. It applies to arbitrary forward-invariant sets where
the shortcut map is injective, including every nonrepeating orbit and every
cycle. Its running-maximum exponent is `1/σ≈1.05268`; in particular,
`A_k=O(k^(20/19))` forces eventual repetition. The new finite image-transfer
lemmas and rational-exponent comparisons are kernel checked. Entropy,
strong-induction assembly, and the limit consequences remain written.
The same note also proves, using the mechanical-word exclusion, that every
nontrivial integer cycle has odd maximum greater than twice its odd minimum.
Neither result provides a universal upper bound on growth or cycle spread.

The [mechanical-mask construction](docs/MECHANICAL-MASKS.md) identifies a
limitation of bounded-discrepancy arguments: exponentially many primitive
rational cycle words have prefix error at most one and odd-state spread
below eight, while some have linear distance from every mechanical word
and large factor catalogs. A concrete Lean witness has nearest half-Hamming
distance 35 and 289 distinct length-32 factors. Its numerator is not divisible
by its denominator, so it is not an integer counterexample. The general
family leaves an explicit modular subset-sum condition unresolved.

The [mask obstruction analysis](docs/MASK-CYCLE-OBSTRUCTIONS.md) now proves
the exact normal form `D | (4C-X)` in Lean, including the coefficient
construction and all-edited rotation identity. A written combination of
Wu–Wang's effective logarithm theorem and parity catalogs excludes every
sufficiently long primitive cycle in the independent `22→13` mask family
and in the family allowing `21→12` edits at alternating eligible positions.
These permit linearly many edits. The exclusions begin at
`max(H₀, 2^40)` and `max(H₀, 2^192)` respectively; the source's effective
threshold `H₀` has not been made numerical here, so neither is a complete
all-length exclusion. The unrestricted `21→12` family remains open.

A separate finite obstruction is checked in
[`CollatzRepetition.lean`](CollatzRepetition.lean). Two starts agreeing for
k parity steps differ by a multiple of `2^k`. If the difference is smaller
than `2^k`, the starts are identical. The file also proves that P+1 small
orbit states covered by a catalog of P parity words force an actual repeat.
This is a conditional theorem; it does not supply the required catalog or
height bound for every orbit.

[`CollatzComplexity.lean`](CollatzComplexity.lean) adds a checked bound using
the actual number `w_t` of odd steps. If preceding states are at least M,
then `2^t M^w_t U^t(n) ≤ n(3M+1)^w_t`. Combined with a parity catalog, it
gives a sufficient finite condition for descent below the seed or repetition.
The catalog coverage and weight bounds remain explicit premises.

The written [`COMPLEXITY-GROWTH.md`](COMPLEXITY-GROWTH.md) derives a stronger
complexity requirement from the upper odd density. At critical odd density,
the number `p(m)` of distinct parity factors must satisfy `p(m)/m → ∞`.
More generally, a divergent orbit cannot combine polynomial upper growth
with a zero-entropy parity word. This excludes further joint classes without
assuming all itineraries have low complexity.

The written [`STURMIAN-ATTEMPT.md`](STURMIAN-ATTEMPT.md) excludes every
irrational mechanical halving schedule and every mechanical halving slope
at most `log_2(3)`. It also excludes the substitution `1→110, 0→011`.
Mechanical words have at most k+1 factors of length k. For the substitution, the factor count is
less than 12k, while aligned three-step growth is at most 9/8; the exact
inequality `(9/8)^4 < 2` closes the collision argument. These exclusions
also hold after finite initial segments. The rational extension, factor
counts, and asymptotic steps are written proofs, not locally compiled Lean
claims. The complexity method is classical; see
[Dubickas, Theorem 5 and its proof](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C40C0C07FEC20797475BB2899C436C9A/S0017089508004655a.pdf/on_integer_sequences_generated_by_linear_maps.pdf).

For positive cycles, [`CYCLE-ATTEMPT.md`](CYCLE-ATTEMPT.md) applies the
packing idea to the distinct members of one primitive cycle. It obtains
`0 < H log 2 - k log 3 < C m^(-δ)`, where m is the cycle minimum, C is
explicit, and `δ=log_32(3456/3125)>0`, independently of the period k.
The note also shows exactly why this fails to prove cycle uniqueness:
infinitely many integer pairs (H,k) remain compatible with the scalar
inequalities. The ordered divisibility conditions are still missing.
This cycle bound is a written proof and is not claimed as a competitive
numerical exclusion record.

[`CYCLE-WORDS.md`](CYCLE-WORDS.md) attacks the ordered condition directly.
For a cycle word consisting of r repeats of a fixed block followed by a fixed
connector, its denominator must divide a constant determined by those two
blocks. [`CollatzCycleBlocks.lean`](CollatzCycleBlocks.lean) checks the finite
affine elimination, cancellation, and the zero-constant case. The written
note derives finite-candidate results and excludes additional word families.
It supplies no bound on the complexity of every possible cycle word.

The cycle analysis now extends to arbitrary positive halving exponents.
[`CollatzCycleBudget.lean`](CollatzCycleBudget.lean) checks the exact centered
budget `3^q 2^(2R+E) ≤ 5^q 3^R`, where q counts exponent-1 steps, R counts
the other steps, and E sums their excess above two. The explicit premises
are the cycle equations, closure, positive exponents, and states at least
seven. The written [`GENERAL-CYCLE-DEFECTS.md`](GENERAL-CYCLE-DEFECTS.md)
establishes that minimum restriction for a nontrivial integer cycle and
derives `k<3q`, `H<5q`, a bound on every exponent, and a height bound.
This supersedes the earlier quadratic count estimate with a stronger linear
one. The parameter q remains unbounded.

[`CYCLE-EXTREMA.md`](CYCLE-EXTREMA.md) solves the ordering optimization for
fixed `(k,H)` over rational cycles: mechanical words maximize the smallest
cycle value, with a quantified loss for every other word. Its generic
prefix-rotation step is checked in
[`CollatzCycleExtrema.lean`](CollatzCycleExtrema.lean); the weighted extrema
and equality cases are written proofs. The notes construct primitive,
nonmechanical positive rational cycles with unbounded minimum. Those satisfy
the real inequalities and expose why integer divisibility remains essential.

The constructed one-swap families are now excluded as integer cycles in
[MECHANICAL-SWAP-EXCLUSION.md](docs/MECHANICAL-SWAP-EXCLUSION.md), at every
length. A mechanical binary word with one adjacent unequal-bit swap has few
distinct parity factors, forcing any integer cycle to have an exponentially
large diameter. Its rational height bound then forces exponentially close
powers of two and three. Matveev's published bound, exact rational separation,
and finite certificates close this family. The complete argument is written;
the generic range lemmas and identified arithmetic are checked in Lean.

The same note obtains a necessary condition for every primitive cycle:
if its parity word differs from a same-count mechanical word at 2h positions,
then its period is effectively bounded for each fixed h. In any hypothetical
family with periods N tending to infinity,
liminf h/√N ≥ √(log 2/(2 log 3)). This argument supplies no uniform bound on h.

[MECHANICAL-DISTANCE-EXCLUSION.md](docs/MECHANICAL-DISTANCE-EXCLUSION.md)
now excludes h≤31 at every period: every nontrivial primitive cycle must
differ from every same-count cyclic mechanical word of slope p/N in at least 64 positions.
Matveev and exact rational separation reduce this family to N<12288. Lean
checks that each remaining count pair either contradicts the diameter bound
or forces an odd state below one million. A new direct Lean certificate
proves convergence for every start 1 through 1,000,000, with no escape-window
alternative, and kernel soundness then excludes the cycle. The all-period
argument is written; its finite arithmetic and reachability components are
formalized. It gives no upper bound on h and does not address divergence.

The separate [local separation proofs](results/cycle_separation_notes.md)
exclude single transfers in repeated blocks and single-copy replacements
when at least three copies were present.

## The two unresolved possibilities

A counterexample must either enter a nontrivial positive cycle or have an
unbounded orbit. If no value repeats, the orbit eventually leaves every finite
set, since revisiting any value would make the subsequent trajectory periodic.

The cycle equation is exact. For a positive exponent word, set

\[
 D=2^H-3^k,\qquad
 W=\sum_{i=0}^{k-1}3^{k-1-i}2^{h_0+\cdots+h_{i-1}}.
\]

Such a word gives a positive integer cycle precisely when D>0 and D divides W;
[`CollatzCycleCriterion.lean`](CollatzCycleCriterion.lean) now proves this
equivalence for every nonempty positive halving word, including intermediate
integrality, positive odd states, and the exact halving exponent at each step.
The theorem permits imprimitive repetitions of the known cycle. What remains
unproved is that every solution gives only the known cycle. Even proving cycle
uniqueness would leave aperiodic divergence to exclude. Published lower bounds
already make any nontrivial cycle enormous; these searches do not supersede
those bounds. [Hercher](https://arxiv.org/abs/2201.00406)

Negative expected drift and density-one results do not close the universal gap.
Tao proves almost-bounded orbit minima in logarithmic density, which is not a
theorem that almost every orbit reaches 1 or becomes periodic.
[Tao's theorem](https://arxiv.org/abs/1909.03562)

## Reproduction

```sh
cargo test --locked
cargo run --release --locked -- --verify-lean
cargo run --release --locked -- --bench 5
# Optional parallel search, reported separately from the single-thread comparison:
cargo run --release --locked -- --threads 8 --verify-lean
cargo run --release --locked --bin residue-sieve -- --depth 26 --verify-lean

lean CollatzContradiction.lean
lean CollatzGrowth.lean
lean CollatzPeriodic.lean
lean CollatzAffine.lean
lean CollatzPacking.lean
lean CollatzRepetition.lean
lean CollatzComplexity.lean
lean CollatzCycleBlocks.lean
lean CollatzEscapeBounds.lean
lean CollatzCycleBudget.lean
lean CollatzCycleExtrema.lean
lean CollatzCycleCriterion.lean
lean CollatzCycleSeparation.lean
# Finite word exclusions and exact rational comparisons:
lean lean/MechanicalDefectFinite.lean
lean lean/MechanicalLogBracket.lean
lean lean/MechanicalDistanceFinite.lean
lean lean/BoundedStandardCycle.lean
lean lean/PackingExponent.lean
lean lean/MechanicalMaskWitness.lean
lean lean/MechanicalMaskArithmetic.lean
lean lean/MaskCatalogBounds.lean
```

The repository pins Lean 4.33.1. The current proof files and existing generated
certificates passed this release; [verification records](results/lean-4.33.1/README.md)
include exact source hashes, compiler version, commands, and logs. Older result
files retain their original 4.31.0 provenance. The top-level structural files listed above use kernel proofs
without `sorry`, `native_decide`, or added axioms. Their only printed dependencies
are the standard logical axioms `propext`, `Quot.sound`, and, where used,
`Classical.choice`. Runtime benchmarks are measurements, not mathematical proof
certificates. See [RUST-PORT.md](RUST-PORT.md) for the port and performance results.
The first range lemmas and two finite files have a historical
[separate verification record](results/mechanical-one-swap/verification.json).
Those two finite files explicitly use native_decide; their analytic and
combinatorial applications are written proofs, not complete local formalizations.
The stronger distance exclusion, expanded rational bracket, and direct
one-million convergence check have a [current verification record](results/mechanical-distance/verification.json).
The later packing-transfer lemmas and entropy comparisons have
[their own record](results/packing-bootstrap/verification.json); these use
kernel proofs without native evaluation. The same record includes the
concrete mechanical-mask witness, whose finite computations use native_decide.
The later exact mask arithmetic and elementary catalog-cutoff comparisons
have a [separate kernel verification record](results/mask-obstructions/verification.json).
The published logarithm input and its analytic/combinatorial applications
remain written mathematical dependencies.

## Corrections to the earlier study

The earlier report and Markdown paper have been corrected where they overstated
the scope of results. In particular, generalized undecidability concerns a broader
class of residue-dependent affine maps; it proves neither undecidability of this
specific problem nor impossibility of an elementary proof. Window escapes in the
universal-family catalog remain unresolved. Opposite-parity divergence theorems
do not apply to both-even parameters. The historical PDF has not been regenerated
and does not include these corrections.

The objective remains active: proving the displayed universal descent statement,
or finding a rigorously verified positive-integer counterexample, would settle it.
None of the current artifacts claims either outcome.
