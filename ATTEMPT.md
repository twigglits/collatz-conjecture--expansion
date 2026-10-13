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

The [logarithmic refinement](docs/ORBIT-PACKING-LOG.md) retains the
square-root binomial factor and proves the additional uniform bound
\(32768L^\sigma/\sqrt{1+\log L}\). Its running-maximum lower bound gains
\((\log N)^{1/(2\sigma)}\), so even \(A_k=O(k^{1/\sigma})\) forces repetition.
This closes the endpoint left by the earlier power-only estimate.
The full refinement is a reviewed written proof using the existing finite
Lean transfer lemmas and Robbins's factorial inequalities.

The [no-descent ballot argument](docs/NO-DESCENT-BALLOT.md) separately gives
\(\#(E\cap[a,a+L))\le C L^\sigma/(1+\log L)^{3/2}\) for starts that never
fall below themselves. It uses a published ballot theorem and implies
\(\sum_{n\in E}n^{-\sigma}<\infty\). Future-tail minima of a divergent orbit
obey the resulting count bound, but their frequency in time is unknown.
The set E is not forward invariant, so this does not strengthen the
all-state running-maximum bound by itself. This is a reviewed written proof.
The same note now bounds all visits of a nonrepeating orbit to \([m,2m)\)
when its entire tail stays above m. It forces a first crossing of 2m within
\(O(m^\sigma/(1+\log m)^{3/2})\) steps, but crossing does not establish a
new permanent lower floor.

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
Wu–Wang's effective logarithm bound and parity catalogs excludes every
sufficiently long primitive cycle in the independent `22→13` mask family
and in the family allowing `21→12` edits at alternating eligible positions.
These permit linearly many edits. That argument gives exclusions beginning at
`max(H₀, 2^40)` and `max(H₀, 2^192)` respectively, where `H₀` is the
threshold of that logarithm bound. The later argument below
closes these two gaps. The unrestricted `21→12` family remains open.

The later [explicit logarithm argument](docs/EXPLICIT-LOG-GAP.md) now closes
both family exclusions at every period. It proves
\(\lambda>N^{-21/5}\) for the required critical counts once
\(N\ge10^{4000}\); this is the bound the earlier argument actually needs.
An extended exact resonance cover closes the finite range; its catalog also
dominates the independent \(22\to13\) family. The small-period conclusion
retains the published Eliahou input described below. The full integral,
all-index denominator, and family arguments are written proofs with checked
finite arithmetic.

A [further transition bound](docs/MASK-TRANSITIONS.md) proves that an integer
primitive cycle in this unrestricted family, at
\(N\ge10^{4000}\), must contain more than \(N/(24\log_2N)\)
cyclic halving-11 occurrences. This excludes the entire no-11 subclass and
any family with \(o(N/\log N)\) such occurrences. Its elementary comparisons
and local repairs are kernel checked; the uniform catalog argument is written.
The [empirical-diversity refinement](docs/MASK-DENSITY.md) strengthens this
to \(N/8192<q<(2N-3k)-N/8192\) for
\(N\ge2^{16384}\). It counts many windows with few marked blocks,
and gives a finite conditional-entropy bound without an independence
assumption. Frequent good and bad blocks remain possible.

These numerical cutoffs use the new explicit logarithm bound in the earlier
transition and density proofs. Together with the finite cover, the argument
excludes the no-halving-11 mask subclass at every period. The displayed
statements no longer depend on an unspecified \(H_0\).

The exact subset decoder is now kernel checked in
[MaskSubsetDecoder.lean](lean/MaskSubsetDecoder.lean). Its completeness theorem
supports [finite all-mask certificates](lean/MaskSubsetFinite.lean) at
\((k,N)=(193,306)\) and \((2966,4701)\), covering \(2^{80}\) and \(2^{1231}\)
independent masks respectively. The larger certificate checks 315555 quotient
targets and rejects them all. These fixed-count exclusions do not depend on
the unknown \(H_0\); their finite computations explicitly use native_decide.

The [resonance argument](docs/MASK-RESONANCE.md) now excludes every
primitive positive integer cycle in the full critical \(21\to12\) mask
family throughout \(2^{21}\le N\le10^{4000}\), using the
[extended cover](lean/MaskResonanceExtended.lean). A uniform parity-factor
catalog and the integer collision lemma force a rational approximation
too close to \(\log2/\log3\); an exact dyadic logarithm enclosure and checked
Farey brackets reject it for every denominator in the interval. The local
certificate uses no unknown \(H_0\). Its finite cover uses native evaluation,
its checker soundness and Farey arithmetic are kernel proved, and the
catalog, real logarithm bounds, and cycle assembly are written.
Eliahou's published lower cycle-length bound, with its cited external
convergence computation, closes the range below \(2^{21}\). With that
external input, any nontrivial primitive cycle in this full mask family
would have \(N>10^{4000}\). Infinitely many larger periods, arbitrary other
halving words, and divergent trajectories remain unresolved.

The extension uses 32,768-bit dyadic arithmetic and the same kernel cover checker.
The original \(10^{1000}\) certificate is retained for provenance.

A separate finite obstruction is checked in
[`CollatzRepetition.lean`](CollatzRepetition.lean). Two starts agreeing for
k parity steps differ by a multiple of `2^k`. If the difference is smaller
than `2^k`, the starts are identical. The file also proves that P+1 small
orbit states covered by a catalog of P parity words force an actual repeat.
This is a conditional theorem; it does not supply the required catalog or
height bound for every orbit.

[PrefixRepetition.lean](lean/PrefixRepetition.lean) now combines that
congruence with universal shortcut growth: agreement for m parity bits
between n and \(U^\ell(n)\), together with \(3^\ell(n+1)\le2^{m+\ell}\),
forces \(U^\ell(n)=n\). The [written consequences](docs/PREFIX-REPETITION.md)
exclude aperiodic itineraries with arbitrarily large prefix squares, including
an explicit word with full factor complexity. Arbitrary itineraries need not
have those repetitions.

The [folded-cycle argument](docs/FOLDED-CYCLES.md) shows that odd spread
\(M/m<8\) forces \(\gcd(k,H)=1\). Its normalized successor ranks rotate
mechanically, but three possible scale layers leave many actual halving
words. The finite arithmetic, rotation-coprimality implication, and a local
order reversal just above spread eight are kernel checked. The full cycle
assembly and its remaining divisibility test are written.

The [forward-closure extension](docs/FOLDED-CYCLE-INVERSIONS.md) strengthens
the coprimality conclusion to \(M<9m+2\). For \(M<16m\), if \(t\) counts
pairs \(x,8x+1\) in the odd cycle and \(g=\gcd(k,H)\), it proves the
necessary conditions \(t\ge g-1\) and \(t\equiv g-1\pmod2\). Exact local
inversion classification and forced successor paths are kernel checked in
[FoldedCycleNine.lean](lean/FoldedCycleNine.lean); sorting, permutation
cycle counting, and the full cycle conclusions remain written proofs.
The narrow coprime mechanical-mask families still survive these conditions.

The [narrow-cycle reduction](docs/NARROW-CYCLE-MASKS.md) now proves that
every nontrivial primitive integer cycle satisfying \(3M+1<8m\) belongs
to the full critical \(21\to12\) mask family. Odd spacing forces \(k\le m\),
an integer power bound forces the critical total count, and every state
at least \(2m\) selects an isolated edit of the folded mechanical word.
Thus for \(2^{21}\le N\le10^{4000}\), every nontrivial cycle satisfies
\(3M+1\ge8m\). The same bound covers smaller periods with the external
Eliahou input already identified above. Sorting and global cycle assembly remain written proofs,
with the new local arithmetic and power bounds checked in Lean.

The explicit logarithm argument also removes the earlier span bound's dependency on \(H_0\):
every nontrivial positive integer cycle satisfies
\[
 \boxed{4M\ge9m+5.}
\]
The all-period conclusion combines the narrow-cycle classification, the
complete no-halving-11 mask exclusion, and the two-rise identity.
It retains the identified published prime estimates and external small-period
input, and its full analytic and cycle assembly remains a written proof.
The stronger finite-range bound \(3M+1\ge8m\) now holds through \(10^{4000}\);
an all-period \(8/3\) span bound is not proved.

The later [restriction on edit positions](docs/MASK-SPAN-BOUND.md) now proves
\(20M>49m\), or \(M/m>2.45\), at every period. Under the contrary maximum
bound, selected edits must lie in a short rotation interval. Every 1054
consecutive positions then admit at most 196 possible edit centers, giving
a factor catalog too small for the existing height bound. The extended
finite exclusion covers the initial range. The new integer arithmetic is
kernel checked; the circle counting, logarithms, and complete cycle
deduction remain written proofs with the same external inputs.

The [automatic-order theorem](docs/MASK-FOLDED-ORDER.md) also makes a
limitation precise. At the close counts required of any surviving integer
mask, positive forcing already gives the prescribed folded rank order
for every edit choice. Those masks have odd spread below four, but this
does not settle their integer divisibility.

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

## Audit of a proposed non-divergence route (2026-10-08)

The search result for Eltgroth's [v1.2 manuscript](https://zenodo.org/records/19054281)
claims non-divergence for every positive integer. Its
[v1.3 replacement](https://zenodo.org/records/19058317) explicitly retreats to
a density statement and acknowledges the missing pointwise implication.
Neither version supplies an accepted dependency for this repository.

There is also an independently checked obstruction to the finite-modulus
argument used in its tower re-entry analysis. Distinguish the odd map
\(F(n)=\operatorname{odd}(3n+1)\) from its first-return map \(R\) to
\(1\bmod4\). Put \(\rho(k)=(2^k-5)/3\), for odd \(k\ge5\).
Direct iteration gives
\[
 R(\rho(k))=2\cdot3^{k-3}-1,\qquad
 R^2(\rho(k))=(3^{k-2}-1)/2.
\]
For completeness, the first odd step from \(\rho(k)\) removes two
factors of two and lands at \(2^{k-2}-1\). The next \(r\) odd steps
give \(2^{k-2-r}3^r-1\), for \(0\le r\le k-3\).
All values before the last are 3 modulo 4; the last is 1 modulo 4.
Thus the first return uses \(k-2\) odd steps with deposits
\((2,1,\ldots,1)\). Its output is 1 modulo 8, and one more odd step
with deposit 2 gives the displayed second return, which is 1 modulo 4.

Now choose \(k=2^{s+1}+1\), \(s\ge1\), and write
\(x_s=R^2(\rho(k))\). Then
\[
 \boxed{\nu_2(3x_s+1)=s+2.}
\]
An elementary induction proves
\(3^{2^{s+1}}=1+2^{s+3}q_s\) with \(q_s\) odd:
\(q_0=1\) and \(q_{s+1}=q_s+2^{s+2}q_s^2\).
Also \(3x_s+1=(3^{2^{s+1}}-1)/2\), proving the box.
[TowerDepositObstruction.lean](lean/TowerDepositObstruction.lean) kernel
checks this induction, the equation for the explicitly defined \(x_s\),
and divisibility by \(2^{s+2}\) but not by \(2^{s+3}\), for every \(s\).
The identification with the two first returns is the written argument above.

Consequently no finite modulus in \(k\) can fix even the **first deposit
of the third contracting return** on every residue class: a finite table
would have bounded entries, whereas these deposits are unbounded. The first
contracting return itself already has an unbounded number of odd steps.
Pointwise finite dependence on binary digits therefore does not provide
the uniform finite partition needed for the manuscript's fixed-coefficient
argument. A fixed number of odd steps and a fixed number of contracting
returns cannot be interchanged. This identifies a gap in that proposed
proof; it does not disprove tower re-entry finiteness by another method.

The independent [Python replay](verify_tower_deposits.py) checks the actual
first-return stopping rule for \(s=1,\ldots,13\), including a 16,384-bit
seed. All checks passed. The [verification record](results/tower-deposits/verification.json)
separates the universal kernel arithmetic from the written orbit argument
and these finite examples. Reproduce with `lean lean/TowerDepositObstruction.lean`
and `python3 verify_tower_deposits.py`.

The audit rules out importing this proposed shortcut to non-divergence.
It neither produces a divergent orbit nor removes either unresolved
possibility below. A repaired re-entry argument would have to handle
unbounded deposit patterns, and a density estimate would still need a
separate pointwise argument.

## Audit of a claimed universal 200-step budget

The [CollatzLayerA v8.1 source audit](docs/BUDGET-AXIOM-AUDIT.md) found
that its claimed complete proof imports an axiom asserting at most
44 odd and at least 71 even ordinary steps in some prefix of length
at most 200, for every large start congruent to 3 modulo 4.
The explicit start `2^111−1` contradicts it: every such prefix has
`ceil(k/2)` odd and `floor(k/2)` even steps.
[BudgetAxiomAudit.lean](lean/BudgetAxiomAudit.lean) kernel checks all
201 counts and negates the stated universal axiom. It also proves that
this witness reaches 1 after 1,476 steps. This is a counterexample to
the imported assumption, not to Collatz. An independent exact replay
checks 105 instances of the growing-prefix family; no full foreign
repository build or convergence proof for all those instances is claimed.
[Verification](results/budget-axiom-audit/verification.json).

## Real-series density argument: a necessary source correction

An explicit symbolic construction now demonstrates the real/2-adic gap
described earlier in [APERIODIC-ATTEMPT.md, Section 6](APERIODIC-ATTEMPT.md#6-an-explicit-counterexample-to-identifying-real-and-2-adic-series-limits).
It has an aperiodic word of lower one-density strictly above \(\log_3 2\),
yet its real Collatz-series sum is exactly \(-2\). The same series has an
odd 2-adic limit, so the two limits cannot be identified.

This contradicts an intermediate real-irrationality inference and the
limit-identification argument in the [López–Stoll 2021 preprint](https://arxiv.org/html/2101.12747),
Sections 2 and 6. It does not disprove that preprint's stated theorem about
rational Collatz trajectories. That theorem is not imported here to claim
exact critical lower density or to exclude all automatic itineraries.
The independently proved restrictions in this repository remain valid.

[RealShadowObstruction.lean](lean/RealShadowObstruction.lean) checks the
all-index integer invariants and density inequality. Real convergence,
aperiodicity, and the two-metric conclusion remain written deductions;
2,000-step exact replay and four parity-prefix reconstructions passed.
The [verification record](results/real-shadow/verification.json) separates
these scopes. This construction is not a positive-integer orbit and is
not a counterexample to Collatz.

## First-passage refinement of the orbit bound

The [first-passage argument](docs/ORBIT-PACKING-LOG.md#6-first-passage-refinement-2026-10-08)
strengthens the uniform interval count for every nonrepeating orbit and
every cycle. With \(\sigma=H_2(\log_3 2)\), it proves the written bound
\[
 \#(S\cap[a,a+L))\le C\,
 \frac{L^\sigma[1+\log(1+\log L)]}{(1+\log L)^\beta},
 \qquad
 \beta=\frac32-
 \frac{\log(\log_3 2/(1-\log_3 2))}{\sigma\log3}
 \approx0.9862105455.
\]
In particular the earlier square-root logarithmic denominator can be
replaced by exponent \(9/10\), with an unspecified absolute constant.
The proof groups states by their first coefficient crossing below a chosen
threshold, rather than only by the weight at the final observation time.
Each group maps into a shorter interval; a uniform ballot estimate counts
the remaining parity words.

[FirstPassagePacking.lean](lean/FirstPassagePacking.lean) kernel checks the
new exact transport, crossing-weight uniqueness, and power comparisons.
The external probability estimate and the complete analytic induction
remain written dependencies. The [verification record](results/first-passage/verification.json)
records 454,632 finite image checks and 135 independent partition checks.
This gives stronger necessary growth and summability restrictions, but no
upper bound contradicting all divergent orbits and no full cycle exclusion.

## Büchi models and arithmetic repetition certificates

The [automata investigation](APERIODIC-ATTEMPT.md#7-büchi-automata-and-exact-arithmetic-for-repeated-blocks)
proves in writing that the complete positive-integer parity language is
not omega-regular. It also proves that every Büchi language consisting
entirely of genuine positive-integer parity streams contains only
eventually cyclic orbits. These statements restrict exact recognizers
and sound sublanguages; they do not exclude useful overapproximations
or automata with additional arithmetic state.

For a block \(F(x)=(Ax+B)/D\), its defect
\(\Delta(x)=(D-A)x-B\) gives finite certificates:
an integer prehistory of \(r\) copies ending at \(m\) requires
\(A^r\mid\Delta(m)\), and a forward history starting at \(n\) requires
\(D^r\mid\Delta(n)\). [BuchiArithmetic.lean](lean/BuchiArithmetic.lean)
checks these necessities, the finite cutoff, and fixed-point rigidity
under arbitrarily long inverse pumping. The sufficiency of the tests
for actual parity blocks and the automata arguments remain written.
The [verification record](results/buchi-arithmetic/verification.json)
includes 783,360 directional checks and 2,048 forbidden odd-prefix
extensions. A changing block changes the defect, so these individual
counters do not yet give a ranking function for an arbitrary orbit.
The kernel-checked family \(2(2^k-1)\to2^k-1\) shows that switching
from the even-block counter to the odd-block counter can raise it
from 1 to \(k\) in one step. A uniform bound on such resets is therefore
unavailable; an additional size-dependent argument is needed.

The [subsequent size-ranking test](APERIODIC-ATTEMPT.md#8-why-finitely-many-valuation-corrections-do-not-repair-a-size-ranking)
rules out a specific proposed repair. The genuine path
\(192s-5\to288s-7\to432s-10\to216s-5\) grows overall while preserving
the endpoint valuations of \(n,n+1\) at 2 and 3; taking \(s\) divisible
by a chosen modulus also preserves that residue. Its finite arithmetic
is kernel checked. A written extension constructs such growing paths
for any fixed finite collection of polynomial valuations and residues.
Consequently no rank nondecreasing in size when these features are
held fixed can strictly decrease at every step outside a finite set.
This eliminates that class of ranking attempts, without excluding
more general ranks or proving convergence.

## Coalescence induction and an unbounded horizon

[CoalescenceDescent.lean](lean/CoalescenceDescent.lean) proves that Collatz
is equivalent to every start above 1 sharing an iterate with a smaller
positive start, allowing different times on the two orbits. This extends
the available induction certificates beyond direct descent. At depth eight,
the kernel verifies 240 of 256 residue classes, including three additional
classes obtained by coalescence. Sixteen infinite classes remain; the
reduction does not prove convergence for them.

The same module proves a universal limitation: **for every fixed horizon,
some positive start cannot meet any smaller start within that many steps
on either orbit.** This includes unequal meeting times and arbitrary
smaller positive starts. The proof uses starts that are -1 modulo a large
power of 2 and 0 modulo a corresponding power of 3. It does not construct
an orbit that fails to converge; the chosen start depends on the horizon.

The [argument and remaining classes](APERIODIC-ATTEMPT.md#9-coalescence-induction-and-its-finite-horizon-limit)
and [verification record](results/coalescence/verification.json) separate
the universal kernel theorems, the kernel depth-eight table, and independent
Python checks at larger depths. A universal coalescence proof still needs
an unbounded, start-dependent argument; expanding a fixed table cannot
settle the conjecture by itself.

[CoalescenceHeight.lean](lean/CoalescenceHeight.lean) sharpens this limitation:
for every K≥1 there is a start between `3^K` and `6^K` that cannot meet
any smaller start within K steps on either side. Thus a uniform search
bound growing more slowly than the logarithm of the start is impossible.
The module also proves that 27 has no smaller-start meeting before its
own step 59, allowing arbitrarily long time on the smaller orbit.
These are kernel results; the [separate verification record](results/coalescence-height/verification.json)
distinguishes them from finite tests of possible logarithmic upper bounds.
No universal upper bound or first-multiplier-drop-to-coalescence theorem
has been established.

The subsequent [bidirectional rank search](APERIODIC-ATTEMPT.md#11-bidirectional-ranking-search-and-a-finite-affine-obstruction)
tested global ranks that may decrease along either direction of a Collatz
edge. [CoalescenceEnvelope.lean](lean/CoalescenceEnvelope.lean) proves the
sufficient rank criterion and a two-sided affine envelope on the growing
CRT classes. Exact SMT searches rejected all 22 tested residue moduli.
A written argument using the envelope excludes every finite family of
positive-slope affine rank formulas, even with arbitrary assignments to
integers and finite exceptional ranges. The full finite-family argument
is not Lean formalized; [the verification record](results/coalescence-envelope/verification.json)
separates it from the kernel lemmas and SMT checks. Nonlinear or infinitely
parameterized ranks remain possible; none has yet proved convergence.

The [four-feature valuation follow-up](APERIODIC-ATTEMPT.md#12-a-four-feature-valuation-rank-obstruction)
also excludes bounded-below ranks of the form
`C log₂n + a ν₂(n) + b ν₂(n+1) + c ν₃(n) + d ν₃(n+1)`, `C>0`,
from supplying a decreasing adjacent edge outside any finite base.
Five infinite progression patterns lead to 108 exhaustive linear
contradictions. Their finite certificates and progression identities are
kernel checked; the full real/logarithmic deduction is written. The
[verification record](results/valuation-graph-rank/verification.json)
keeps these scopes separate. General nonlinear valuation ranks remain open.

The [quadratic follow-up](APERIODIC-ATTEMPT.md#13-proper-nonlinear-ranks-and-a-quadratic-obstruction)
extends the written exclusion to every quadratic polynomial of the same
four valuations plus `C log₂n`, `C>0`, when the rank has finite sublevel
sets. This condition prevents infinite descending paths, which boundedness
below alone does not do for real ranks. A new kernel graph lemma forces
natural-valued ranks to decrease forward on multiples of three; its
written proper-real extension supplies necessary coefficient restrictions.
Six progression patterns and 162 kernel-checked arithmetic certificates
then contradict local progress. The [verification scope](results/quadratic-valuation-rank/verification.json)
separates the formal inputs from the written real and polynomial arguments.

The subsequent [graph orientation theorem](APERIODIC-ATTEMPT.md#14-graph-ranks-must-follow-the-forward-map-outside-the-base-closure)
is stronger for proofs with a verified finite base: well-founded local
graph descent necessarily follows the forward map outside the base's
forward closure. Combining its kernel proof with the earlier growing
feature-matched paths excludes arbitrary nonlinear corrections from any
fixed finite list of polynomial valuations and residues, when the rank
is nondecreasing in size at fixed features. The broad corollary is written;
the natural-rank four-valuation case is kernel checked. This requires
bounded forward closure of the base and does not prove Collatz or exclude
all possible ranks. [Verification scope](results/graph-rank-orientation/verification.json).

The [binary-digit follow-up](APERIODIC-ATTEMPT.md#15-separated-binary-blocks-and-weighted-digit-pattern-ranks)
tests information outside the polynomial-valuation class. Four infinite
families rule out weighted bit length plus zero-padded binary-window
counts, for every fixed window width and arbitrary real coefficients.
Their rank changes cancel with positive weights `(2,1,1,1)`.
The separated-block integer-rank theorem is kernel checked; the universal
window-count and real-score interpretation is written. [Verification](results/digit-block-rank/verification.json).
General boundary-dependent and non-additive digital ranks remain open.

The [inverse-basin audit](APERIODIC-ATTEMPT.md#16-inverse-basin-counts-do-not-supply-an-injective-orbit-packing-contradiction)
checks a different proposed route: combining inverse-tree lower bounds
with the project's orbit-packing upper bound. Kernel results show why
the injectivity hypothesis prevents that direct comparison: roots not
divisible by three have basin collisions, while forward-closed injective
subsets of a single basin must be chains. In the basin of one, such
subsets contain only the two shortcut cycle states. A new branching-set
estimate or an injective-chain lower bound is still missing; no density
contradiction follows. [Verification](results/inverse-basin-audit/verification.json).

The [quantitative follow-up](APERIODIC-ATTEMPT.md#17-the-inverse-fibre-multiplicity-loss-is-exponentially-large)
shows that the worst same-time, same-weight fibre at depth k has at least
`ceil(4^k/((k+1)3^k))` members. The written pigeonhole proof uses parity-word
counts and the exact residue-image bound. Kernel lemmas show that fibre
partitions repeat in every aligned block, and certify 48 colliding starts
per block at depth 16. Thus a uniformly small collision correction cannot
repair the basin-packing comparison.
[Verification](results/inverse-fibre-growth/verification.json).

The [uniform branching result](APERIODIC-ATTEMPT.md#19-uniform-inverse-branching-within-every-unit-root-basin)
strengthens this obstruction inside each fixed unit-root basin. Lean proves
that every a not divisible by three has 2^h distinct positive unit ancestors
at time 6h and weight h, with `3^h*n≤64^h*a`. Thus even a hypothetical
exceptional component cannot have subexponential unrestricted fibre sizes.
These trees also exist in the known basin of one; they do not give a
lower bound on one forward orbit or prove convergence.
[Fresh builds and replay](results/uniform-inverse-branching/verification.json).

A [targeted review of openai/math](APERIODIC-ATTEMPT.md#18-methods-reviewed-from-the-openai-mathematics-collection)
identifies collision-aware entropy accounting and scale-dependent trapping
as methodological leads, and records their missing Collatz hypotheses.
No theorem from that external collection is used as a proof dependency.

The subsequent [mixed-residue construction](APERIODIC-ATTEMPT.md#20-every-unit-root-basin-meets-every-mixed-residue-cylinder)
shows, in a written proof, that the inverse basin of every root coprime
to three has arbitrarily large members in every residue class modulo
`2^A*3^B`. Hence convergence of an entire tail of even one such class
would imply the full conjecture. If a counterexample exists, every class
instead has both convergent and nonconvergent starts. Lean verifies the
conditional arithmetic transport; the universal modular lifting is
written. This gives no sufficiently small predecessor or trapping bound.
[Verification](results/basin-residue-shadow/verification.json).

The [quantitative refinement](APERIODIC-ATTEMPT.md#21-linear-cost-residue-embeddings-and-their-sharp-fixed-prefix-limitation)
gives bounded time and a linear size cost for each fixed cylinder, with
an injective construction on odd unit roots. It can transfer counts of
bad roots into any cylinder with only a constant size rescaling. The
sharp worst multiplier of the fixed-prefix/pure-halving scheme exceeds
one, and infinitely many roots admit no smaller value anywhere on its
constructed path. Other paths are not excluded. Size and injectivity
lemmas are kernel checked; the existence and sharpness arguments are
written. [Verification](results/residue-shadow-cost/verification.json).

The [adaptive inverse audit](APERIODIC-ATTEMPT.md#22-all-bounded-inverse-paths-and-a-unit-root-meeting-obstruction)
checks all inverse branches: every ancestor of `3^K*q+1` within K
steps is an explicit lift of an ancestor of one, and is at least its
root. This is kernel proved. A written extension excludes every
smaller-start meeting with both times at most K when additionally
`2^K` divides `n+1`. These witnesses are coprime to three, unlike
the earlier CRT witnesses divisible by three. No unbounded adaptive return
rule is excluded. [Verification](results/adaptive-inverse-barrier/verification.json).

The [half-multiplier criterion](APERIODIC-ATTEMPT.md#23-a-half-multiplier-margin-that-guarantees-actual-descent)
supplies a positive sufficient estimate. At the first time k with
`3^wt(k,n)/2^k≤1/2`, Lean proves
`3*2^k*U^k(n)≤3^wt(k,n)*(3*n+2*wt(k,n))`. At that crossing,
`2*wt(k,n)<3*n` guarantees actual descent. In particular, any half
crossing by time n guarantees descent by that time. A kernel theorem
combines this with a convergent finite base to give a sufficient global
certificate. Existence of these crossings within the required budget
remains unproved. Exact Python checks cover starts 1..32768 and 3,072
CRT-family instances; they do not supply the universal premise.
[Verification](results/half-slope-descent/verification.json).

The [first-drop budget](APERIODIC-ATTEMPT.md#24-a-size-budget-for-a-first-multiplier-drop-below-one)
also permits smaller coefficient margins. With `A=3^wt(k,n)`,
`D=2^k`, and k a first drop below one, Lean proves
`3*D*U^k(n)≤A*(3*n+wt(k,n))` and descent when
`A*wt(k,n)<3*n*(D-A)`. A kernel power-budget theorem and the written
logarithm estimate give the sufficient size condition
`k^26≤(3*n)^5` for first drops with `k≥10^4000`.
The exact integer gap can also be checked directly at smaller times.
Neither a universal first-drop time nor the unrestricted coefficient
stopping-time claim is proved.
[Verification](results/first-slope-budget/verification.json).

The [weighted survivor investigation](docs/WEIGHTED-SURVIVORS.md) keeps
one certified floor, H=64, and the finite mass
`M_k=sum_{tau_64(n)>k} n^(-3/2)`. Vanishing mass is equivalent to every
start reaching that floor. Exact predecessor transport retains the
odd-source cutoff and affine correction. The kernel checks the inverse
branches, finite inverse-cone characterization, base convergence, and
integer comparisons used in the conditional contraction bound.

The written analysis distinguishes two targets. An exponential mass
envelope is equivalent to a universal `O(log n)` floor-hitting bound.
A fixed contraction at merely infinitely many horizons already suffices
for convergence, without that timing conclusion. Specifically, if the
eligible residue-2 mass `Q_k` is at most `69 M_k/200` infinitely often,
then full Collatz follows. The unconditional critical bias bound gives
strict positive loss at each horizon, but does not prove that the sum of
relative losses diverges. That is the remaining global estimate.

Exact Python enclosures independently refute `Q_k<=M_k/3` at k=19
and verify the weaker 69/200 bound only for k=0,...,36. The last cone
contains 2,510,783 absorbed starts. No all-time or infinitely recurrent
share bound is proved. A written all-odd-path argument also excludes
pointwise inverse contraction for every weight uniformly comparable to
`n^(-s)`, while leaving aggregate contraction open.
[Verification](results/weighted-survivors/verification.json).

The [closure obstruction](docs/WEIGHTED-BASIN-BARRIER.md) tests a possible
way to prove the missing aggregate estimate. Backward closure, cofiniteness,
and a provably absorbed finite complement do not imply uniform weighted
contraction. A written construction gives counterexamples for every fixed
block length, even after any fixed amount of survival information. Its
supporting all-index rising paths end at powers of two and converge;
their integer arithmetic and ancestor-basin boundary are kernel checked.
The constructed populations need not be actual survivor sets S_k.

The same construction rules out a uniform lost-mass bound `c*mass^p` on
that class whenever `1<=p<log_2(3)`. A concrete counterexample to the
`p=3/2,c=1` estimate uses a source and target that the kernel checks reach
one in 560 and 496 shortcut steps. Bounds with larger exponents are not
excluded here, and none is established. The proof must retain additional
information about the actual common clock, or obtain a weaker loss
estimate that still forces the mass to zero.
[Verification and scope](results/weighted-basin-barrier/verification.json).

The [finite-path extension](docs/FINITE-PATH-PACKING.md) retains information
about exact first-entry paths. The packing induction now applies to every
finite trajectory with distinct states, giving `256 L^sigma` states in
any interval of length L, where `sigma=H_2(log_3 2)<19/20`. At each
scale, discarding only the final observation-length positions restores
the required injective image inside the same prefix. The kernel checks
that finite transfer and proves distinctness up to first entry.

The written shell estimate then bounds the reverse correction sum before
first entry below Y by `4096 Y^(-1/20)`, independently of the entry time.
This gives a bound for each fixed-time, fixed-landing fibre in a dyadic
source interval, with kernel-checked odd-count uniqueness. The explicit
constant gives a useful margin only at an enormous floor. Exact replay
checks 19,082 finite first-entry paths and a separate 6,270-step large-floor
witness. Neither a union bound over all times nor universal first entry
follows. The mass of eternal survivors remains uncontrolled.
[Verification and scope](results/finite-path-packing/verification.json).

The [equal-weight fibre analysis](docs/EQUAL-WEIGHT-FIBRES.md) gives two
kernel affine envelopes after shifting states by one. A complete inverse
fibre with k steps and j odd steps contains at most `2^(k-j)` starts;
with at most one even step it contains at most one. A written consequence
gives the sharp uniform exponential rate of the inverse coefficient
moment, which is not a survivor-mass contraction.

Along a divergent trajectory, reciprocal summability supplies a bounded
normalized endpoint. The nested sets of starts that merge with it at
equal time and odd count must therefore eventually stabilize. The finite
cap and conditional stabilization are kernel checked; the divergence
bridge remains written analysis. No universal growth theorem for these
particular fibres is proved.

Two complete examples prevent overclaiming the approach. The kernel
proves `F_34(1)={1}` and `F_35(1)={1,159}`, so a finite plateau does
not certify stabilization. It also proves that 27 reaches one but has
no positive smaller equal-time, equal-weight mate at any time. A written
arrival-label argument supplies unboundedly many convergent examples of
this latter obstruction. Thus a universal smaller-mate induction cannot
require equal times and equal odd counts, even beyond a finite base.
The broader coalescence criterion remains available.
[Verification and scope](results/equal-weight-fibres/verification.json).

The [arrival-grade extension](docs/COALESCENCE-GRADES.md) now kernel-checks
the classification and makes the nonnegative minimal representatives
explicit: the least convergent start of grade `a>=0` is exactly `2^a`.
It also proves that allowing either unequal odd counts at a common clock,
or unequal clocks with equal odd counts, restores a criterion equivalent
to the full conjecture. Both universal meeting premises remain unproved.
For 27, any smaller partner at a common clock must have at least six fewer
odd steps; at equal odd counts its clock must be at least twelve steps
later. Both all-time lower bounds are sharp and kernel checked.

There is also a kernel termination bound conditional on finite odd/even
credit. If `2*wt(k,n)<=k+A` at every index, then the rank
`R(x,g)=2^(g+1)*(x-1)+g`, with `g=A+k-2*wt(k,n)`, strictly decreases
until one is reached. The hitting time is at most `2^(A+1)*(n-1)+A`.
A finite credit for each positive source is equivalent to full Collatz,
including exclusion of nontrivial cycles. A counterexample would exceed
each proposed credit A by time `R(n,A)+1`. No general source-dependent
credit bound is proved. A Python census through 2,000,000 and independent
direct replay supplement the kernel implications; neither finite check
supplies the missing universal bound.
[Verification and scope](results/coalescence-grades/verification.json).

The [parity-survival follow-up](docs/PARITY-SURVIVAL.md) strengthens that
conditional time bound to `4A+5b+71` when `n<=2^b`. In fact, the single
endpoint condition `2*wt(K,n)<=K+A` at `K=4A+5b+1` suffices; earlier
violations of the same allowance are permitted. The proof uses exact
growth while avoiding the kernel-certified base 1..64. A counterexample
would satisfy `5k<=8*wt(k,n)+5b` at every clock, hence would have lower
limiting odd frequency at least 5/8. The finite inequalities and time
bound are kernel checked; the limiting statement is their written
consequence. No individual-orbit estimate crossing this threshold is
proved. The exact inequalities also show that a proposed uniform
`O(log n)` credit bound is equivalent to a uniform `O(log n)` total
stopping-time bound, rather than an easier quantitative target.
[Verification and scope](results/parity-survival/verification.json).

The [parity-prefix fibre bound](docs/FIBRE-PREFIX-BOUND.md) improves the
universal multiplicity estimate. A kernel-checked recurrence `B(e,a)`
tracks both the number `e` of remaining even steps and the grid spacing
`3^a`. It stops at one member when `3^a+1>=2^e`, and otherwise splits
as `B(e-1,a)+B(e,a+1)`. Every same-time, same-weight fibre has at most
`B(e,0)` members. In particular, two even steps permit at most two
members, with a kernel all-index family attaining two at arbitrarily
large targets.

Written analysis bounds this recurrence by `2*alpha^e`, where
`alpha=1.726541...` and `alpha=2^delta`, `2^(-delta)+3^(-delta)=1`.
This extends the optimal uniform-target time-exponential rate for
coefficient moments to `s>0.497100...`, including the explicit bound
`Z(k,1/2,y)<=4000*(3/2)^(k/2)`. The kernel certifies the integer
comparisons supporting that explicit constant; the real-analysis
deduction is written. This remains a coefficient estimate whose right
side grows with time, not contraction of actual survivor mass. The
upper bound does not force new merging starts along an individual
orbit. No convergence conclusion is inferred.
[Verification and scope](results/fibre-prefix-bound/verification.json).

An [independent exit-mass replay](docs/SURVIVOR-EXIT-MASS.md) certifies
`M(k+1)<=0.993*M(k)` for the actual infinite survivor mass at floor64,
exponent3/2, for `k=0..126` and `k=128`. It uses exact first-entry times
through 2,000,000 and a written infinite-tail bound: known exit mass
divided by a full mass upper bound gives a lower bound on relative
loss. All numerical comparisons are exact integer Python checks, not
new Lean proofs. The first inconclusive test, at k=127, does not refute
the actual contraction inequality. The 128 certified horizons do not
establish infinitely many contractions, vanishing survivor mass, or
Collatz. [Verification and scope](results/survivor-exit-mass/verification.json).

A [certificate budget](docs/EXIT-CERTIFICATE-BUDGET.md) now quantifies
what an infinite extension of that test would require. Certifying the
factor 993/1000 at G distinct horizons requires a largest cutoff
`R >= 64*(1000/993)^(2G)`, even for an adaptive schedule. If the exit
lower bounds use integer scales at most S, then
`S > 4*(1000/993)^(G-1)` for G>=1. The abstract integer telescoping
theorem is kernel checked; the integral-tail and real-mass applications
are written. Exact comparisons bound the success count by 736 when all
cutoffs are at most 2,000,000, and by 9276 when all scales are at most
2^96. These necessary bounds do not predict attainable counts. Growing
cutoffs and scales still do not force new successful horizons, and the
existing 128 certificates remain the full certified scope.
[Verification and scope](results/exit-certificate-budget/verification.json).

A [weighted operator calculation](docs/KILLED-OPERATOR-BOUNDS.md) now
converts inverse coefficient estimates into bounds for actual source
weights. For killed composition `K_H f(n)=1_{U(n)>H} f(U(n))` on
`l1(n^(-s),n>H)`, with fixed H>=1 and s>1, the written proof gives both
spectral radius and essential spectral radius exactly `(3/2)^s`. At
H64,s3/2, its kth operator norm lies between `(3/2)^(3k/2)` and five
times that quantity. The kernel verifies the integer comparisons and
arbitrarily large surviving column witnesses; the Banach-space and
spectral arguments remain written analysis.

An explicit positive function of finite weighted norm, supported on
powers of two, has iterates that eventually vanish at each fixed source
while their norms tend to infinity. Its contributing sources all have
certified paths to one. This rules out uniform contraction on that whole
function space, even after finite-rank corrections or an equivalent
renorming. The actual mass is the norm of `K_H^k` applied to the constant
function, and its decay remains open. The result does not refute that
decay or add a successful survivor horizon.
[Verification and scope](results/killed-operator-bounds/verification.json).

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

The [local-lift theorem](docs/CYCLE-LOCAL-LIFTS.md) rules out one proposed
way to close the divisibility gap: every positive-denominator word admits
exact residue-cycle witnesses modulo every \(2^a3^b\). The new Lean proof
checks actual integer edge witnesses, their exact halving exponents, and
the precision lost during division. These witnesses close only modulo
the chosen modulus. A complementary kernel lemma recovers \(D\mid W\)
when a fixed integer height bound makes the congruence an equality.
Thus larger residue-consistency graphs alone do not exclude the masks;
global integer information must remain in the test.

The [rank arithmetic](docs/MASK-RANK-ARITHMETIC.md) now gives a simpler
form of the mask equation at coprime counts. With `s=2k-N` and an explicit
unit `z` modulo `D`, the edit coefficients in mechanical rank order are
`c_j = 2^(N-2) z^j` modulo `D`. Their total satisfies `gcd(C,D)=1`, and
integer realizability is equivalent to
`(1-z) sum_j epsilon_j z^j = 1` modulo `D`.
The modular algebra and phase-exponent identity are kernel checked; the
mechanical reindexing is a written bridge. This is an equivalent condition,
not an all-mask exclusion. A separate written subset-sum argument shows
that divisibility tests with a fixed bounded combined modulus eventually
allow some mask, so those tests alone cannot settle the unbounded family.

Negative expected drift and almost-bounded-minimum results do not establish
convergence to one.
Tao proves almost-bounded orbit minima in logarithmic density, which is not a
theorem that almost every orbit reaches 1 or becomes periodic.
[Tao's theorem](https://arxiv.org/abs/1909.03562)

A [written natural-density version](docs/NATURAL-DENSITY-ALMOST-BOUNDED.md)
now gives `#{N≤X: Col_min(N)>N₀} ≪ X(log N₀)^(-c)`, so almost bounded
minima hold outside a set of natural density zero. The proof follows
Tao's Remark 1.16. His Fourier bound survives a tilt by `e(θ|a|)`, which
gives fine-scale mixing jointly with the total valuation. A renewal lemma
for `{k log₂3}` then recovers his first-passage constant `2/ln(4/3)`.
Tao's propositions and an irrationality exponent for `log₂3` are external
inputs. The [numerical checks](results/natural-density/verification.json)
are floating-point and Monte Carlo sanity checks only. The audit supplies
the uniform harmonic counting bound and renewal tail estimate explicitly.
Stabilisation throughout the interval of scales also gives a written
proof that each set `Col_min(N)≤B` has a natural density, and that these
densities tend to one as B grows. This written argument alone does not
establish positive density for the basin of 1. The exceptional set still
need not be empty.

The [total-variation deduction](docs/DENSITY-TO-POINTWISE.md) strengthens
this written consequence: the full distribution of orbit minima among
starts up to X approaches a probability law p at rate `O((log X)^(-c))`,
uniformly over all sets of minima. It also gives a direct proof of the
almost-bounded-minima estimate from first-passage stabilisation.
Coalescence-component densities form a countably additive probability
distribution. This does not determine `p_1`, the density of convergence
to one. With only the older published `X^0.84` inverse-basin bound,
even `p_1=1` would have needed a better exceptional-count estimate for
that comparison to exclude a counterexample.

The newer [positive predecessor-density theorem has passed independent
source replay](docs/PREDECESSOR-DENSITY-REVIEW.md). Both published
archives and all 404 assembled files were authenticated; all 389 Lean
modules passed and the three public roots report only `propext`,
`Classical.choice`, and `Quot.sound`. Pinned third-party compiled
libraries were reused. The external theorem is now a verified input
within that scope. It proves that upper natural density one for
convergence excludes every positive counterexample. With the written
minimum law, `p_1=1` suffices without an improved error rate; `p_1>0`
also follows. The remaining premise `p_1=1` is still unproved.

The written first-passage argument also gives natural densities `r_a`
for predecessor sets of each fixed odd target. An early-valuation bound
puts the first-passage landing above `x^(7/10)` with probability
`1-O(x^(-c))`, extending the profile argument to every positive target.
Finite orbit packing implies `sum r_a ≤ 256 L^σ` over odd targets in
any length-L integer interval, and `≤512 L^σ` over all targets, where
`σ<19/20`; uniform positive target-independent lower bounds are therefore
impossible. Along a forward orbit these densities increase to its
component density. Targets divisible by three have density zero because
their predecessors are only repeated doublings; the external PLD theorem
makes all other target densities positive. Neither the summed upper bound
nor positivity excludes a sparse divergent orbit. These are
[written deductions](docs/DENSITY-TO-POINTWISE.md#4-densities-of-odd-target-predecessor-sets),
not new kernel proofs or a proof of the remaining density-one premise.

A [further first-passage argument](docs/PREDECESSOR-DENSITY-FLOW.md)
gives a limiting landing law whose largest atom tends to zero as the
floor grows. Combining it with finitely many first-hit paths below the
floor proves `r_b -> 0` uniformly for large targets b within each fixed
predecessor basin `P_a`. In particular `r_(2^j a) -> 0`. For an odd
nonperiodic root this removes the remainder from the finite inverse-branch
partition and proves `r_a = sum_k r_((2^k a-1)/3)` over eligible k.
The finite fibre bound and nonperiodic branch-disjointness are kernel
checked; the limiting laws and infinite sum remain written analysis.
The threshold depends on the fixed basin. Later states of a divergent
forward orbit lie outside every earlier fixed basin, so this new decay
does not yet contradict their increasing densities or prove `p_1=1`.

A [target-uniform approximation](docs/UNIFORM-PREDECESSOR-APPROXIMATION.md)
now strengthens the written density limit to
`sup_a |#{n<=X: n reaches a}/floor(X) - r_a| = O((log X)^(-c))`.
The new kernel comparison says that a hit is either after first passage
or shares the target's passage mark, including nonentry. The earlier
small-atom bound then gives a Cauchy estimate uniform over all targets.
It also approximates the entire function `a -> r_a` by a finite weighted
sum of the actual forward-orbit indicators of small seeds. Eleven new
Lean theorems and separate finite checks passed; the analytic limits and
rate remain written, conditional on the earlier first-passage estimates.
Uniformity permits a moving target but does not make its density small:
in a hypothetical divergent component, a sufficiently late target can
receive every component start below X. Its observed proportion and r_a
can both approach the positive component density. That missing smallness
bound, and exclusion of nontrivial cycles, remain unresolved.

A [branch-density audit](docs/DENSITY-BRANCH-LEAKAGE.md) makes the missing
comparison more precise. Along a hypothetical divergent Syracuse orbit
`b_j`, the unused ordinary branches `u_j=2(3b_j+1)` have summable densities
and summable ratios `r_(u_j)/r_(b_j)`. A lower bound on those ratios by
`kappa/(1+log b_j)` would contradict summability and exclude divergence;
no such bound is established. Even a target-uniform absolute lower bound
`r_a >= c/a` would not give this contradiction, because the existing
packing estimate makes reciprocal orbit values summable. The exact
finite replay passed 4551000 parent partitions, but its strongly unequal
branch counts are not certified asymptotic density ratios. These written
deductions do not exclude divergent orbits or nontrivial cycles.

An [explicit comparison map](docs/DENSITY-COUNTERMODEL.md) now shows
that these general density properties alone cannot supply the missing
comparison. It keeps even halving and the cycle `1 -> 4 -> 2 -> 1`,
but changes the odd branch. Half its starts escape despite a written
uniform lower bound `r_a >= 1/(2a)`, small first-passage atoms, a uniform
density limit, and logarithmic orbit packing. Fourteen kernel theorems
verify its escaping family and distinguish its map from ordinary Collatz.
Its density and packing calculations remain written, with separate exact
finite checks. It does not retain the `3n+1` odd-parent arithmetic or the
zero-density predecessor property at multiples of three. Those additional
arithmetic constraints remain potential inputs to the actual open problem;
this comparison is not a positive-integer Collatz counterexample.

A [finite-clock audit](docs/DENSITY-TIME-TRUNCATION.md) uses the actual
ordinary inverse congruences. Seventeen kernel theorems prove that every
target has at most 38 distinct twelve-step predecessors, with equality
at target 364, and give bounds at every even depth. A written corollary
bounds all sources hitting a target by time T by `195 * 38^(T/12)`.
Capturing a fixed positive fraction of starts through X at one target
therefore needs at least `(12/log 38) log X - O(1)` ordinary steps,
approximately `3.29889 log X`. This is a necessary clock, not a time
by which convergence has been established.

The same note proves in writing, under the preceding density inputs,
that positive accumulation values of `r_a` as `a -> infinity` are exactly
the densities of divergent components. For a fixed source sample, the
uniform error from truncating eventual hits is eventually exactly its
largest divergent-component fraction. Consequently, existence of a clock
whose uniform truncation error tends to zero is equivalent to exclusion
of divergence, using external predecessor positivity. The earlier uniform
limit over targets does not already supply this clock. Cycles remain a
separate problem. The independent replay checked 455 complete forward
fibres, 2184 residue fibres, and 24 finite clock comparisons; its sample
orbits all converge and make no assertion about infinite trajectories.

A [minimum-clock argument](docs/CLOCKED-MINIMUM.md) now retains both
passage times when coupling sources with a common first odd landing.
Conditional on the existing written first-passage stabilization, the
first attainment time of the **global orbit minimum**, divided by `log n`,
tends in natural density to `3/log(4/3)`, approximately `10.42818`.
The minimum exists even for a divergent orbit; its equality to one is
not asserted. Twenty-two kernel theorems establish exact minimum and
clock transfer, including the signed difference of first-minimum times.
The concentration and density arguments remain written analysis.

For any fixed target, the fraction hitting it by `c log n` tends to zero
below that coefficient and to its full predecessor density above it.
For the population clock `c log X`, the uniform truncation defect tends
to the largest component density below the coefficient and to the largest
divergent-component density above it. The equality case is undetermined.
In particular `11 log X` gives a concrete sufficient clock for each
fixed target's limiting density. Full Collatz would require the density
of hitting one within that clock to tend to one, using external PLD;
the argument only identifies this limit with the still-unknown `p_1`.
The finite replay passed 8192 complete trajectories, 57344 coupled clocks,
480 one-sided and 640 centered probability comparisons. These checks
do not certify the asymptotic conclusions or exclude divergent orbits.

A [coalescence and source-interval audit](docs/PREFIX-COALESCENCE-AUDIT.md)
tests whether whole-period parity statistics can determine that missing
`p_1`. Seven new kernel lemmas prove an all-depth reflection between the
shortcut `3n+1` and `3n-1` maps: endpoints sum to a power of three and
odd counts agree. This makes their adjacent weighted coalescence counts
identical at every depth, although the minus map has the separate cycle
`5 -> 7 -> 10 -> 5`. The first twenty counts match the known
[OEIS A398792](https://oeis.org/A398792); no novelty is claimed.

The earlier kernel fibre bound also gives the unconditional written
bound `F_(2^(6q))(6q) <= 390*(19/32)^q -> 0`, where `F_X(k)` is the
proportion through `X` entering the shortcut cycle by time `k`.
In contrast, the prior conditional clock argument gives
`F_X(ceil(11 log X)) -> p_1 > 0`. At that clock, the actual source
interval occupies only `Theta(X^(1-11 log 2))` of a full parity period.
The full-period average therefore cannot replace the required estimate
on the initial interval. The exact finite replay checks both maps through
depth 20 and entry times for all starts through 65536; it proves no
asymptotic density. The new audit supplies neither `p_1=1` nor a
counterexample to positive-integer Collatz.

A [sparse-perturbation construction](docs/SPARSE-COLLATZ-PERTURBATION.md)
tests the remaining inverse-congruence argument more sharply. It exchanges
two ordinary odd outputs at each of a geometrically spaced sequence of
inputs, changing only `O(log X)` values through `X`. The altered map
retains even halving, the known cycle, the allowed odd-image congruence,
at most two parents, and pure-doubling predecessor sets at multiples of
three. Its explicit path from `21845` escapes; actual Collatz sends that
same start to `65536` and then to one. The construction can preserve any
prescribed finite set of checked Collatz trajectories by delaying the swaps.

Twenty main kernel theorem roots were audited, including an exact
inclusion of an original unit-target basin into every altered unit-target
basin. External PLD therefore supplies positive lower density of both
convergence and escape in the altered map. A separate written coupling
argument transfers the existing large-floor passage premise: the chance
of encountering a changed input before the early old-map passage is
`O(x^(-c)) + O(x^(-3/5))`. Fixed-depth parity frequencies and the written
packing exponent also persist. Consequently the proposed logarithmic
relative-branch bound cannot follow from these shared properties alone.
The exact odd-parent value changes at the swapped images, so this supplies
no counterexample for actual Collatz. All finite checks passed, including
1048592 forward-source inverse checks and classification of the altered
map through 262144. No asymptotic fraction is inferred from those counts.

The follow-up [weighted loss identity](docs/WEIGHTED-DISSIPATION.md) returns
to the exact ordinary map. Multiplying a weight by `3n/(3n+1)` at each
odd input gives an exact finite conservation law: remaining weight plus
all preceding losses is one. Eighteen kernel roots verify the integer
accounting, its affine formula, concatenation, and geometric repetition
on any positive cycle. Using the earlier written packing estimate, the
infinite remaining weight is positive exactly for divergent orbits.

Conditional on the written passage premise, the entire distribution of
losses over odd targets, with remaining weight assigned to an infinity
symbol, has a natural-source total-variation limit. If `D_N` is weighted
first-hit density and `B_N` the cycle repetition factor, its mass identity
is `d + sum_(N odd) B_N*D_N/(3N+1) = 1`. External PLD makes `d=0`
equivalent to universal eventual periodicity; **the equality `d=0`
remains unproved**, and additional cycles are not excluded. The earlier
written clock theorem gives mean remaining weight tending to one below
`(3/log(4/3))*log X`, and to `d` above it, including clock `11 log X`.
Exact checks cover 2048 full sample paths and 436800 source-clock pairs
through source cutoff 65536. Their rational enclosures have no certified
asymptotic error. A related public weighted-density manuscript was read
as context; its new claims and formal audits were not adopted or replayed.

The [coalescence-tail follow-up](docs/COALESCENCE-TAIL.md) tests whether
balanced merging of adjacent inputs could make the remaining weight
vanish through dyadic refinement. The odd-count difference of two
adjacent shortcut trajectories holds or makes a fair unit step as each
new input bit is exposed. Stop its absolute value at the first zero.
Twenty-three audited kernel roots prove that its sum over `2^H` residues
is exactly `2^H`, and its sum over either initial-parity half is `2^(H-1)`.
Since its value is at most `H` and it vanishes on balanced-coalescent
pairs, the unmerged fraction is at least `1/H`, separately for either
initial parity. Thus the whole-period errors are not summable. A written
simple-walk coupling strengthens this to a central-binomial lower bound
of order `H^(-1/2)`; the coherent fair-bit fusion time has infinite mean.
Neither conclusion asserts divergence of a positive Collatz orbit.

A separate written argument shows that summable measures of changes in
the dyadic functions `2^k*W_infinity(floor(2^k*x))/floor(2^k*x)`, for
`1<=x<2`, would force `d=0`, assuming its previously conditional natural
mean exists. Balanced even adjacent pairs give exact stability on the
odd half-cells, but the full-period estimates cannot supply a summable
bound at depths within the source scale. This does not prove that the
actual refinement errors are nonsummable: later merging or equal zero
weights can make them much smaller. Exact checks through depth 20,
including 48151 independent direct pair paths and 456 nonzero quotient
lifts, passed. The missing actual-weight estimate and other-cycle
exclusion remain open; no new external density-one input was adopted.

The [next dyadic audit](docs/DYADIC-COALESCENCE-DEFECTS.md) rules out the
unweighted summability premise itself, on the actual source intervals.
For a convergent start with grade `g=t-2a`, the auxiliary weight
`V(n)=2^g/n` is at most `(5/6)^a`, where `a` counts odd inputs before
the first arrival at one. Each uninterrupted balanced binary refinement
increases the grade by one while keeping `V` bounded below. Its descendants
therefore have a uniformly bounded number of odd inputs. Eighteen kernel
roots check this arithmetic, finite parity-word injectivity, and the
sharper cap of three odd inputs for balanced descendants of one.

A written counting argument bounds such descendants by a polynomial
in their binary depth, so their fraction among all descendants tends to
zero. It follows that binary paths eventually using only balanced
refinements can visit the known basin later only on a null set. Reusing
the external theorem's positive lower density at one proves that the
actual eventual-unbalanced even-pair fractions `B_k` have divergent sum.
This uses neither the written natural-passage premise nor density-one
convergence. If full Collatz holds, almost every binary path still has
infinitely many such grade defects, while all infinite weights are zero.
Thus the earlier implication from summable `B_k` remains valid but has
a false premise under the replayed input. The smaller, actually weighted
change sets remain the relevant unresolved quantity. Fresh builds and
an exact first-arrival census through 524288 passed; all 389 external
project source, object, and log hashes were revalidated without a rebuild.

The [grade-weight moment follow-up](docs/GRADE-WEIGHT-MOMENTS.md) supplies
an unconditional quantitative bound for that auxiliary weight. Its finite
extension is `V_t(n)=2^t*U^t(n)/(4^a*n)`, where `a` counts odd inputs.
It decreases to the arrival-grade weight on the known basin and to zero
on every orbit that never reaches one. Thirteen kernel roots prove exact
integer affine identities and full-period moments: the principal mass is
`7^t`, and the scaled correction mass is `(10^t-7^t)/3`. A written source
split controls the correction separately, giving mean `V_T` through `X`
at most `(14/3)*X^(-log₂(8/7))` for every `T>=ceil(log₂ X)`, and the same
bound for its limit. No external density or passage theorem enters this
bound. It also makes auxiliary dyadic amplitudes summable almost surely.

The exact identity `V_t*W_t=(3/4)^a` prevents transferring that upper
bound to the escape weight. A separate written criterion weakens the
earlier finite-change condition: assuming the prior natural component
law and external PLD, any divergent orbit would force infinite squared
variation of the actual escape-weight dyadic refinements almost surely.
The required finite-variation estimate for `W_infinity` remains unproved,
as do vanishing escape mass and exclusion of other cycles. Fresh builds
and exact finite moment checks through depth 20 and source cutoff 1048576
passed; the new asymptotic auxiliary bound is a written deduction from
all-depth identities, not an extrapolation from those finite data.

The [actual escape-weight refinement audit](docs/ESCAPE-WEIGHT-REFINEMENTS.md)
uses `H_(s,k)=2^k*W_(s+k)(floor(2^k*x))/floor(2^k*x)` for `1<=x<2`.
Matching one extra time step to each binary refinement makes the even
child copy its parent exactly. Twenty-one kernel roots prove the finite
path arithmetic, reciprocal affine moments, and an explicit family of
parent-to-odd-child decreases at least `27/512` at arbitrarily fine
levels, even with offset `s=6` fixed. The refinements are not a
martingale, and their maximum jump does not tend to zero.

A written geometric tail gives finite total squared-increment energy
`E_s` at every fixed offset, with `E_s<=3s/2+23/4`. Exact rational
checks through binary level 12, together with that tail bound, give
`E_0<1/7` and `E_16>1/4`, disproving monotone energy contraction.
Neither fact excludes a larger bound independent of the offset.

The limiting criterion now needs no written passage-mixing premise.
A written rigidity argument shows that an actual Collatz-invariant
binary label with an almost-everywhere limit along binary prefixes has
a constant zero-or-one limit: exact odd arithmetic makes the real
scaling limit invariant under both multiplication by two and by three.
Applied to divergence, finite limiting squared variation would force
density zero or one. Replayed PLD at a divergent target and at one would
contradict either alternative. Thus a bounded subsequence of `E_s` at
offsets tending to infinity would exclude escape by Fatou, but that bound
is **unproved**. Other cycles also remain unexcluded. Fresh builds and
finite checks passed; the real energy and rigidity arguments are written.

The [coalescence energy caps](docs/COALESCENCE-ENERGY-CAPS.md) sharpen
the written estimate to `E_s <= (28401483/52428800)*s+6`, below
`0.542s+6`. Seventeen new kernel roots transport balanced coalescence
to the actual dyadic annuli and verify an all-offset integer cutoff.
A separate direct census through depth twenty supplies the finite
coalescence constants. The strongest levelwise certificate formed from
these counts and the existing geometric tail must itself grow at least
on the order of `sqrt(s)`, by the earlier written walk comparison.
This is a lower bound on that **upper-bound certificate**, not on `E_s`.
Thus deeper full-period counts alone cannot establish the bounded-energy
subsequence. The actual weights of unmerged pairs remain uncontrolled.
An even-input residue class also reaches equal odd counts at time eleven
without fusion; its base pair `6,7` is kernel proved never balanced,
although both starts reach one. Equal-count absorption therefore cannot
replace balanced coalescence in the energy cap. No divergent orbit or
additional positive cycle is excluded by this refinement.

The [ordered weight drift argument](docs/ORDERED-WEIGHT-DRIFT.md) now
controls one part of that actual weighted contribution. Before the odd
member of an adjacent even/odd pair has accumulated fewer odd steps than
the even member, a downward weight change requires a parent parity prefix
consisting of odd steps followed by even steps. Thirty-one new kernel
roots check the transition arithmetic, first-return endpoint order,
shifted reciprocal moments, and exactly `k+1` such prefixes on every
depth-`k` source annulus. A written source-height bound and nonnegative
summation give `sum_s N_ordered(s) <= 14` over **all** offsets and levels.
This is an actual weighted drift bound, not a coalescence-only cap.

The negative contribution after count reversal remains unbounded by the
present argument. An exact infinite family at offset six makes its
downward product tend to `81/1024` while both immediate parent time losses
tend to zero, excluding any uniform pointwise loss-charge constant.
The exhibited cells have summable lengths, so this does not refute a
bound on the integrated reversal contribution. A bounded subsequence of
its Cesaro means would suffice for the prior escape-exclusion criterion;
that estimate and the exclusion of additional cycles are still open.
Fresh kernel builds and independent finite rational checks passed. The
real drift estimates and all-offset sum remain written deductions.

The [reversal persistence argument](docs/REVERSAL-PERSISTENCE.md) strengthens
that obstruction. Eight new kernel roots prove original and shifted
endpoint-retention bounds, then show that every even-indexed family member
has parent value at least `1/2` and odd-child value at most `27/64` for
`3j-4` consecutive offsets. Its unaveraged negative drift over those
offsets is at least `5(3j-4)/128`, while the parent's entire future loss
budget is less than `45/16`. Thus no uniform multiplier can charge that
accumulated drift to all future parent losses. Even charging just the
initial jump to a fixed block of future steps fails; the failure extends
to the displayed horizons proportional to source bit length. These are
written consequences of the kernel endpoint comparisons, not divergent
orbits. The guaranteed persistence rectangles have finite total measure.

A precise remaining sufficient estimate compares each level's reversal
drift with the losses averaged over its whole source annulus. A universal
constant `C` would imply a Cesaro energy bound `1/2 + 121C/10` and feed the
existing conditional escape-exclusion route. Exact rational checks verify
`C=8` only for `k<=10,s<=96`; `C=6` fails at `k=5,s=46`. No uniform
constant is established. The new verification record preserves and
revalidates the earlier ordered-drift record. Collatz remains unresolved.

The [count-return control argument](docs/COUNT-RETURN-CONTROL.md) now
provides a different positive input. Its written probability proof bounds
the first positive count-return tail uniformly in endpoint separation,
then proves a contraction with a bounded additive term for the separation's
`1/16` power at returns. A finite-set return argument and explicit paths
to balanced fusion give a finite expected number of count-return cycles.
Consequently the full, unstopped odd-count gap has bounded mean over
every complete residue period, and balanced noncoalescence is
`O(H^(-1/5))`. No external coalescence theorem is imported.

Combining this with the existing actual-annulus energy cap yields
`E_s = O(s^(4/5)) = o(s)`, improving the growth order of the previous
linear bound. The explicit constant is extremely large; the old linear
bound remains useful numerically. Twelve new Lean roots check the exact
restart identity, deterministic return transitions, and integer constants.
The stopping-time, fractional-moment, finite-set, and real-energy arguments
remain written proofs, with exact finite distributions checked separately.
Sublinear energy growth still does not imply the bounded subsequence
required to exclude escape. The whole-annulus reversal charge and the
exclusion of additional cycles remain open.

The [actual-annulus height coupling](docs/ANNULUS-HEIGHT-COUPLING.md)
now transfers that count control to a real endpoint-height bound. For
even `m` in `[2^t,2^(t+1))`, let `X=U^t(m),Y=U^t(m+1)` and let `a,b`
be their odd counts. Twelve new kernel roots give integer forms of
`mean |X/3^a-Y/3^b| <= (2/3)^t` and `mean(b-a)=1`. A written logarithm
comparison then gives
`mean |log(Y/X)-(b-a)log(3)| <= (2/3)^t`, hence a bounded mean logarithmic
height separation using the earlier count-return constant. The integral
of disagreement over all logarithmic height thresholds is bounded too.

The signed logarithmic mean tends to `log(3)`, although coalescence makes
the difference vanish in probability. Thus these differences are not
uniformly integrable. A separate written telescoping argument bounds the
expected sum of `D_j^(1/16)` over all Haar count returns. Exact weight
transport after a return puts actual endpoints in a progression of spacing
`3^a`; recovering its binary branch probability from an interval average
requires controlling that progression. The new finite replay retains the
progression and verifies its factor exactly. No such averaging estimate,
uniform later-clock weight bound, or escape exclusion is claimed.
An exact progression example already requires a multiplier greater than
eleven: the first-return prefix `r=200,tau=10,a=4` samples endpoints
`98,97` inside an interval of 81 terms, and at continuation clock 128 its
normalized squared-difference ratio is `10453976883/926254009`.
This is a finite obstruction to small constants in that comparison,
not a disproof of every uniform constant or of the distinct parent-loss
averaging estimate.

The [sharper count-return clock argument](docs/COUNT-RETURN-CLOCK.md)
now improves that energy estimate to `E_s=O(sqrt(s))`. Instead of stopping
the embedded count-gap walk after a prescribed number of active steps,
it stops on reaching gap zero or a height boundary `K`. The exact
valuation formula for `3^d-1` and the finite walk's Green function bound
the expected physical clock by `9K-8`. The probability of reaching `K`
is `1/K`, giving the written uniform return tail `7/sqrt(H)`.
The previous return-cycle budget then gives balanced noncoalescence
`O(H^(-1/2))`, with the same decay order as the earlier lower bound.

Fifteen new Lean roots check the cofactors, valuation-sum arithmetic,
and finite Green equations; the stopping and energy deductions remain
written. Independent exact finite checks passed. The same argument
also bounds the expected sum of return-separation powers for every
exponent strictly between zero and `1/3`. An exact first-return family
with returned separation four has multiplier `(243/256)*(3/2)^m`, so
the raw aggregate endpoint coefficients have no uniform constant bound.
This does not rule out bounds for the actual weighted gradients.

The coalescence-only cap and geometric-tail method now has a matching
square-root growth order for its upper-bound certificate. This is not
a lower bound on actual energy. Bounded actual energy, the weighted
progression comparison, escape exclusion, and other-cycle exclusion
all remain open; the full Collatz objective remains active.

The [return-image bounds](docs/RETURN-IMAGE-BOUNDS.md) now give positive
sampling control despite those unbounded coefficients. If `K_beta` is
the ternary image density weighted by the returned separation's `beta`
power, the written joint-moment argument gives
`K_beta in L(log L)^alpha` whenever `beta>=0`, `alpha>0`, and
`3beta+2alpha<1`. It also gives a quantitative coarse-cylinder
approximation and a modulus of absolute continuity.

Twelve new kernel arithmetic roots check prefix weights, endpoint caps,
and integer residue counts. A tilted prefix inequality yields
`sum_(tau<=H) lambda <=2^H`. Consequently the truncated density's mean
over any integer interval of length `M` differs from its Haar mean by
at most `2^beta*(2*3^beta)^H/M`. The logarithmic moment transfers with
the corresponding extra `(H+1)^alpha` factor. For the unweighted density,
depth `H=floor((1-epsilon)log_2 M)` gives uniform integrability on these
finite intervals. Infinite integration and convexity are written steps;
the finite integer checks passed independently.
An explicit unweighted logarithmic quarter-moment is less than `80`
under Haar and less than `82` on any such integer interval whenever
`2^H(H+1)<=M`; these constants do not use the large return-cycle budget.

These bounds do not permit an infinite return cutoff at a fixed integer
interval, and they do not control the density's pairing with the actual
future weight differences. Thus the actual energy bound remains
`O(sqrt(s))`, and the full convergence objective is still unresolved.

The [stopped-correction argument](docs/RETURN-CORRECTION-MOMENTS.md)
now improves the return-separation moment range to every `0<beta<1/2`.
Each affine correction has conditional drift `1/4`. Stop at the first
count return or gap boundary `K`: the previous expected clock bound
`9K-8`, finite stopping, and Fatou give
`Pr(B_tau>L)<=7/(2 sqrt(L))`. Applying the same calculation to the
slope and both corrections yields
`Pr(D'>L)<=(D+6)/sqrt(L)`, with coefficient seven for adjacent starts.
Twelve new kernel arithmetic roots and independent exact stopped-law
checks support these written probability arguments.

The resulting quarter-power drift gives the smaller explicit cycle
budget `E N<=540*2^5180`, and the expected sum of `D_j^beta` over all
needed return cycles is finite for `0<beta<1/2`. The image-density
logarithmic-moment region improves to `beta+alpha<1/2`. Its Haar
truncation error is now at most
`7 H^(beta-1/2)/(1-2 beta)` for `0<=beta<1/2`, including that endpoint
decay rate. The finite-interval sampling formulas retain their necessary
depth/length errors. None of this proves a bounded actual-energy
subsequence or closes the escaping-orbit and other-cycle gaps.

The [all-return occupation argument](docs/RETURN-OCCUPATION-DENSITY.md)
now gives the written exponential cycle moment
`E[(1+2^(-5192))^N]<=2^5182`. This concerns the number of return
cycles; the physical fusion clock still has infinite mean. It permits
counting every nonfused return, including nested prefixes, and proves
that the resulting ternary density `K*_beta` lies in `L(log L)^alpha`
when `beta>=0`, `alpha>0`, and `beta+alpha<1/2`. Its Haar clock
truncation error is `O_beta((1+log H) H^(beta-1/2))`; its finite
integer-interval estimates retain explicit depth/length errors.

Fifteen new kernel arithmetic roots and exact independent finite checks
support these written arguments. The same module shows that the
persistent family always first returns at clock six, common count two,
and separation one, followed by a second excursion of unbounded
pointwise drift cost. Thus a return cost depending only on those data
cannot replace averaging over the returned endpoints. The comparison
with actual future weighted gradients and a bounded-energy subsequence
remains unproved.

The [gradient norm obstruction](docs/GRADIENT-ORLICZ-OBSTRUCTION.md)
now rules out one direct use of those logarithmic density bounds.
On actual returned intervals of length `M=9*2^(12m+6)`, a finite sum
`G_m` of squared future gradients is at least `25(6m+2)/4096` at one
point of the sampled progression. Therefore the interval and progression
averages of `exp((G_m/C)^p)` are unbounded for every fixed `C>0,p>1`.
The corresponding Luxemburg norms grow at least as `m^(1-1/p)`.

Eight new kernel arithmetic roots and exact finite replay support the
written exponential and convex-conjugate deductions. In particular,
summing time contributions and then applying a single uniform
complementary norm against `L(log L)^alpha`, `alpha<1`, cannot work.
The exceptional point's contribution to the ordinary mean still tends
to zero; no failure of a direct averaged density-gradient estimate or
of a bounded-energy subsequence follows.

The [binary image energy argument](docs/BINARY-IMAGE-ENERGY.md) now
provides stronger density integrability. At fixed clock and odd count,
the affine numerator identifies each source in a full binary period.
Within one ternary image fibre, its quotient by `3^a` is therefore
injective. Counting these distinct nonnegative quotients, together with
the exact identity `4 sum_(r<2^t) N_t(r)=t*4^t`, gives the written
bound `||rho_t||_2^2<=(t+1)(t+4)/2` for the full image density.

Every return layer is a subset of this law. Thus the all-return
truncation has `L2` norm at most `3H^2`. Interpolating dyadic increments
against the established `L1` truncation error
`O((1+log H)/sqrt(H))` proves `K*_0 in Lp` for `1<=p<10/9`.
Column Hölder then gives `K*_beta in Lp` for
`0<=beta<1/2`, `1<=p<10/(9+2beta)`. In particular, every finite
logarithmic moment order is now allowed for each such separation
weight. The truncated density's integer-interval `p`th mean is bounded
by `(1+3^H/M)` times the full Haar `p`th moment.

Eleven new kernel arithmetic roots and exact complete-period checks
support these written analytic deductions. No new external theorem is
used. A uniform complementary power norm of the actual gradients is
still unproved, and their prefix-dependent clocks and image scales
still have to be handled in the pairing. The actual energy estimate
remains `O(sqrt(s))`; escape, other cycles, and full Collatz remain open.

The [temporal budget argument](docs/ANNULUS-TIME-BUDGETS.md) now gives
a weaker sufficient escape criterion: at each fixed source level `k`,
the time average `S^(-1) sum_(s<S) N^rev_(s,k)` need only tend to
zero, with no uniformity across `k`. The ordered negative contribution
already tends to zero. Since every cell's weights and history indicator
have limits, this would force the limiting refinements to be
nondecreasing, with total limiting squared energy at most `1/2`.

For this criterion, an explicit inverse spine removes the external
predecessor-density dependency. Starting at one and repeatedly choosing
the earlier six-step inverse child gives `U^(6j)(v_j)=1` and
`3v_(j+1)=64v_j-d_j`, `4<=d_j<=32`. Kernel bounds place
`3^j v_j/64^j` between `29/61` and one; it decreases to a positive
limit. A written irrational-rotation argument makes its leading binary
digits dense, so every binary cone contains a known convergent member.
Under the proposed temporal condition, a positive limiting weight
would persist through both binary children and contradict this cone
intersection. This implication uses no PLD or mixing theorem. Its
universal temporal hypothesis remains unproved, and other cycles
remain a separate gap.

Twelve new kernel roots and exact finite checks passed. The census
includes every future offset for all parents `1<=n<32768`, using
certified known-cycle entry and exact two-phase geometric tails. It
checks temporal energy below four and reversed drift below `5/4` on
each of those fifteen annuli, as well as the weaker charge made only
after time summation. Actual returned progressions and containing
intervals have separate complete-time moment checks. None of these
finite-source results is extrapolated to all source levels.

The [cumulative affine budget](docs/RETURN-AFFINE-BUDGET.md) strengthens
the available return-density estimate to `K*_beta in Lp` for
`0<=beta<1/2`, `1<=p<6/(5+2beta)`. In particular the unweighted
range improves from `p<10/9` to `p<6/5`. Write the formal affine
coefficient as `C_t=(3^a_t+N_t)/2^t`. Its composition across a return
is `C_next=lambda*C_current+b`. The existing conditional slope and
correction estimates now give a summable budget for `C^eta` over all
nonfused returns, for every `eta<1/2`.

Fractional fibre counting bounds each clock/count density component by
this coefficient cost. A written binomial concentration bound removes
atypical counts; the remaining dyadic clock block has only
`O(H^(3/2)*sqrt(log H))` components. Combining their costs with the
occupation-clock tail proves the improved range. The proof includes
the overlap between components, rather than inferring an `Lp` bound
from summability of their separate `p`th powers.

Eight new kernel arithmetic roots and exact finite checks passed. The
fractional moments, concentration, and infinite-density theorem remain
written. For the unweighted density a complementary power strictly
above six could now suffice, in place of one strictly above ten. No
such uniform bound for the actual accumulated gradients is proved;
infinite-cutoff integer sampling also remains unresolved. The temporal
criterion, escape exclusion, and other-cycle exclusion are still open.

The [local obstruction-repository review](docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md)
examines Lucas Valbuena's clone at commit `a7275d5a7381`. It finds a direct
written connection: our full binary image density `b_t` is `L^t 1` for
its binary transfer operator. Its external positive stationary envelope
therefore gives `b_t<=2^(-t)+(3/c)(1-2^(-t))E`, hence uniform full-image
`Lp` norms for every `1<=p<2` and a bound at each fixed positive integer.
The majorant depends on the integer trace. Summing selected return layers
with the existing clock tail recovers `p<6/5`; it does not improve the
local range or control actual gradients and infinite-cutoff sampling.

The clone also isolates a finite masked cylinder energy whose sublinearity
is equivalent to universal eventual periodicity, and an occupation upper
bound that would exclude escape. Their remaining small-ancestor and upper
estimates are unproved, and eventual periodicity still allows other cycles.
Its Fourier selection theorem conditions on total exponent, not arbitrary
paired return histories. This review authenticated 7,493 distributed files
and checked the binary transfer identity on all ternary residues through
depth ten. It did not replay the external Lean bundles; these analytic
inputs remain external dependencies, not additional local kernel results.

The subsequent [active-gap potential](docs/ACTIVE-GAP-POTENTIAL.md) gives
an independent written improvement. At absolute count gap `d`, use
`F(B,d)=q^d B^eta+h_q(d)`, where `r_eta<q<1` and
`h_q(d)=2 sum_(j>=1) min(d,j)q^(j-1)(j+3)` is bounded. Its discrete
curvature pays for the expected affine correction during the next active
block. Nonnegative stopping at active epochs proves returned correction
moments for every `eta<1`, extending the previous `eta<1/2` range.

Killing at balanced fusion then gives summable `C^eta` and `D^eta` over
all nonfused returns. The fractional-fibre and concentration argument
therefore improves to `K*_beta in Lp` for `0<=beta<1` and
`1<=p<5/(4+beta)`, in particular `p<5/4` unweighted. Weighted clock
truncation is `O_beta(H^(-(1-beta)/2)(1+log H)^(1+2beta))`.
Nine kernel arithmetic roots and exact finite stopping checks support
this result; the probability and infinite analysis remain written.
No new external theorem is used. Complementary actual-gradient powers
above five, infinite-cutoff integer sampling, and the global Collatz
conclusion remain unproved.

The [integer return Cesaro argument](docs/INTEGER-RETURN-CESARO.md) now
uses two analytic results from the local clone: periodic weighted
first-hit source means and the first-hit shortcut clock on odd basin
sources. A dyadic valuation split extends the clock to all sources;
partial summation and the finite source cutoff then give marked
physical-time first-hit means. Repeated visits to periodic targets add
the usual finite geometric factor. Thus every fixed periodic source
mark `p` gives `H^-1 sum_(t<=H) B_t^p(n) -> g(n) mean(p)` at each
fixed positive target `n`.

Taking `p` to be nonfusion by a fixed clock `L`, then sending `H` and
afterward `L` to infinity, proves `K*_(0,H)(n)/H -> 0` for every fixed
positive integer. Nine new local kernel roots and exact finite checks
verify the integer correspondence and mask inputs. The analytic limits
are written deductions from external results, without a fresh external
Lean replay. This establishes sublinear truncated occupation at fixed
targets, not finite total occupation, a growing-interval estimate, the
actual-gradient criterion, or the Collatz conjecture.

The [harmonic return trace proof](docs/HARMONIC-RETURN-TRACE.md) now
strengthens that conclusion independently of the clone's analytic
theorems. Bounded-clock predecessors of any target have a uniformly
bounded ratio of largest to smallest source. On a binary source range,
use the earlier of its range index and the nonfusion clock: its
reciprocal-weighted mask mass is at most that earlier mask's full-period
probability. This includes the small sources, where using only the
later mask's mean would fail.

The written square-root fusion tail then gives, uniformly in every
positive target and H>=1,
`K*_(0,H)(n)<=Z_H(n)<=350 C_star n G_n sqrt(H)`, where `Z_H` counts
all nonfused visits. The cycle factor is one for nonperiodic targets
and at most `3n+1` always, by new kernel arithmetic. Ten kernel roots
and exact finite rational checks passed. This provides a quantitative
fixed-target limit and normalized moving-target control without an
external density or clock theorem. Time-discounted return occupation
is finite at each integer for every discount power greater than one half.
The bound still allows a positive single
column along a divergent moving target; the actual-gradient criterion
and full Collatz remain unproved.

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
lean lean/MaskTransitionBounds.lean
# The finite prefix theorem imports the parity-collision module:
mkdir -p /tmp/collatz-prefix-lean
lean -o /tmp/collatz-prefix-lean/CollatzRepetition.olean CollatzRepetition.lean
LEAN_PATH=/tmp/collatz-prefix-lean lean lean/PrefixRepetition.lean
# Later density and folded-order modules have explicit imports:
mkdir -p /tmp/collatz-folded-density
lean -o /tmp/collatz-folded-density/MaskTransitionBounds.olean lean/MaskTransitionBounds.lean
LEAN_PATH=/tmp/collatz-folded-density lean lean/MaskDensityBounds.lean
lean -o /tmp/collatz-folded-density/CollatzCycleCriterion.olean CollatzCycleCriterion.lean
LEAN_PATH=/tmp/collatz-folded-density lean lean/FoldedCycleBounds.lean
# Forward closure extends the folded-order result:
LEAN_PATH=/tmp/collatz-folded-density lean -o /tmp/collatz-folded-density/FoldedCycleBounds.olean lean/FoldedCycleBounds.lean
LEAN_PATH=/tmp/collatz-folded-density lean lean/FoldedCycleNine.lean
# Narrow-cycle arithmetic and automatic rank order are standalone:
lean lean/NarrowCycleMasks.lean
lean lean/MaskFoldedOrder.lean
# Explicit logarithm constants and the extended rational cover:
lean lean/ExplicitLogConstants.lean
mkdir -p /tmp/collatz-explicit-log
lean -o /tmp/collatz-explicit-log/MaskResonance.olean lean/MaskResonance.lean
LEAN_PATH=/tmp/collatz-explicit-log lean lean/MaskResonanceExtended.lean
python3 verify_explicit_log_gap.py --cover
# The rank arithmetic imports the local-lift Bezout proof:
mkdir -p /tmp/collatz-mask-rank
lean -o /tmp/collatz-mask-rank/CollatzCycleCriterion.olean CollatzCycleCriterion.lean
LEAN_PATH=/tmp/collatz-mask-rank lean -o /tmp/collatz-mask-rank/CycleLocalLifts.olean lean/CycleLocalLifts.lean
LEAN_PATH=/tmp/collatz-mask-rank lean lean/MaskRankArithmetic.lean
python3 verify_mask_rank_arithmetic.py
# Exact first-passage comparisons and finite predecessor checks:
python3 verify_predecessor_flow.py
python3 verify_uniform_predecessor_approximation.py
python3 verify_density_branch_leakage.py
python3 verify_density_countermodel.py
python3 verify_density_time_truncation.py
python3 verify_clocked_minimum.py
python3 verify_prefix_coalescence.py
python3 verify_sparse_collatz_perturbation.py
python3 verify_weighted_dissipation.py
python3 verify_coalescence_tail.py
python3 verify_dyadic_coalescence_defects.py
python3 verify_grade_weight_moments.py
python3 verify_escape_weight_refinements.py
python3 verify_coalescence_energy_caps.py
python3 verify_ordered_weight_drift.py
python3 verify_reversal_persistence.py
python3 verify_count_return_control.py
python3 verify_annulus_height_coupling.py
python3 verify_count_return_clock.py
python3 verify_return_image_bounds.py
python3 verify_return_correction_moments.py
python3 verify_return_occupation_density.py
python3 verify_gradient_orlicz_obstruction.py
python3 verify_binary_image_energy.py
python3 verify_annulus_time_budgets.py
python3 verify_return_affine_budget.py
python3 verify_two_coordinate_review.py
python3 verify_active_gap_potential.py
# The subset decoder imports the exact mask-arithmetic module:
mkdir -p /tmp/collatz-mask-lean
lean -o /tmp/collatz-mask-lean/MechanicalMaskArithmetic.olean lean/MechanicalMaskArithmetic.lean
LEAN_PATH=/tmp/collatz-mask-lean lean -o /tmp/collatz-mask-lean/MaskSubsetDecoder.olean lean/MaskSubsetDecoder.lean
LEAN_PATH=/tmp/collatz-mask-lean lean lean/MaskSubsetFinite.lean
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
The complete subset decoder and its two finite all-mask checks have
[a fresh verification record](results/mask-decoder/verification.json), including
the imported source and build hashes. It also records the written logarithmic
packing refinement without claiming that its analytic proof was Lean checked.
The prefix-repetition theorem, local mask repairs, and transition-cutoff
arithmetic have a [new kernel verification record](results/structural-restrictions/verification.json).
That record also identifies the three reviewed written deductions and their
external dependencies; it does not treat their full analytic proofs as Lean checked.
The later density comparisons and folded-order lemmas have a
[separate kernel record](results/folded-density/verification.json), which also
identifies the written entropy, cycle-order, and boundary-count arguments.
The later forward-closure and inversion lemmas have a
[fresh kernel verification record](results/folded-inversions/verification.json)
on Linux with the same pinned Lean release. Its cycle-order and permutation
applications are explicitly recorded as written deductions.
The unrestricted-mask resonance result has
[a separate verification record](results/mask-resonance/verification.json).
Its rational-cover checker and integer inequalities are kernel proved;
finite arithmetic uses native evaluation. The full catalog, logarithm,
and cycle deductions are written, and Eliahou's small-period bound retains
its external computational dependency.
The narrow-cycle arithmetic and automatic rank-order theorem have
[a newer verification record](results/narrow-cycle-masks/verification.json).
It checks the new algebra without native evaluation and distinguishes it
from the written cycle classification and the reused analytic deductions.
The explicit logarithm argument and extended cover have
[a further record](results/explicit-log-gap/verification.json), including an
independent exact Python replay. The all-index integral and denominator proof,
the published prime estimates, and the all-period family and span deductions
are explicitly distinguished from the finite Lean checks.

The stronger span bound has [its own verification record](results/mask-span/verification.json).
Its new Lean arithmetic uses kernel proofs only. The independent Python
checks include circle-boundary cases and nonintegral rational mask cycles
below span 2.45; these finite examples are distinguished from the written
all-period integer-cycle theorem.

The arbitrary-word local-lift theorem has
[a kernel verification record](results/cycle-local-lifts/verification.json).
It also records independent exact checks of 2,883 small words, four larger
masks, and an explicit nontrivial residue walk that is not an integer cycle.

The mask rank arithmetic has
[a separate kernel verification record](results/mask-rank-arithmetic/verification.json).
Its independent replay checks 42,158 rank coefficients and rejects 30,436
exhaustively enumerated masks in the recorded small critical count pairs.
The complete mechanical reindexing, repeated-word gcd consequence, and
fixed-modulus coverage theorem are identified as written arguments.

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
