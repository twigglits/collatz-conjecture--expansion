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
a logarithm bound (originally misattributed to Wu–Wang; corrected in that
note) and parity catalogs excludes every
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
