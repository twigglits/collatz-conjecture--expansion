# Collatz project memory

Last updated: 2026-10-13, after independently strengthening the integer return bound to K*_(0,H)(n)<=350 C_star n G_n sqrt(H), uniformly in the target after normalization. Ten new kernel roots and exact finite checks passed. This quantitative Cesaro result uses no external analytic theorem; actual-gradient control and Collatz remain unresolved.

**Current status: active following the user's resumption.** Collatz remains
unresolved. The external predecessor-density replay has passed all 389
modules and all three public theorem audits, with standard axioms only.
There is no live external replay to resume. Upper natural density one of
convergence would now suffice; it remains unproved. A further written
argument gives decay of target predecessor densities within each fixed
basin, but does not apply to a divergent forward orbit. Its finite fibre
and graph inputs have twelve new kernel proofs. The latest written
argument strengthens predecessor-density convergence to a supremum over
all targets, including moving targets, using eleven new kernel passage
lemmas. Uniform convergence does not make moving-target densities small;
a hypothetical divergent component can still carry positive mass to a
late target. The analytic density limits and rates remain written,
not kernel checked. The latest branch audit shows that a divergent orbit
would have summable unused-branch density ratios. A relative lower bound
of order 1/log(target) would exclude divergence but is unproved; an
absolute lower bound of order 1/target is summable by the existing
packing result and gives no contradiction by this argument. Exact finite
branch counts passed, without certifying asymptotic ratios. The latest
comparison-map audit now gives a concrete obstruction to deducing the
missing relative bound from those general properties alone. Its altered
odd branch allows half the starts to escape, with an explicit r_a>=1/(2a)
bound and diffuse first passage. Fourteen kernel theorems verify its
escaping family. This is not the Collatz map: its odd-parent arithmetic
and its behavior at multiples of three differ. The preceding
operator result still leaves decay of the constant starting function open.
The 128 existing finite-horizon contractions remain that route's full
certified scope. See the last entry for provenance and the remaining gaps.

The latest actual-Collatz arithmetic gives at most 38 distinct predecessors
at twelve ordinary steps, attained at target 364, and all-depth bounds.
Seventeen kernel theorems passed. Its written clock consequence is a
necessary lower bound about 3.29889 log X for hitting one target from a
fixed positive fraction of starts through X. It is not a sufficient clock.
The written density-spectrum argument identifies every positive
accumulation value of r_a with a divergent component's mass. Uniform
finite-time approximation with vanishing error remains unproved.

The newest clock result, conditional on the existing WRITTEN first-passage
mixing premise, gives tau_M(n)/log n -> kappa=3/log(4/3) in natural density,
approximately 10.42818. Here tau_M is first attainment of the actual global
minimum; it does not identify that minimum with one. Twenty-two kernel
theorems check minimum attainment and exact clock transfer, and independent
finite checks passed. The asymptotic statement is not kernel formalized.
For each fixed target, clock c log n captures zero limiting density when
c<kappa and its full predecessor density when c>kappa. The uniform
truncation defect at c log X tends to the largest component mass below
kappa and the largest divergent-component mass above it. Neither mass is
determined; the critical clock is also undetermined. In particular the
fixed clock 11 log X captures the one-target density p_1. Proving this
finite-clock proportion tends to one would imply full Collatz via external
PLD, but p_1=1 remains unproved. Nontrivial cycles and escape remain open.

The newest audit shows why full-period coalescence counts do not supply
that missing initial-interval estimate. Seven kernel lemmas prove exact
reflection between the plus and minus shortcut maps and identical
adjacent weighted coalescence counts at every depth, although the minus
map has the separate cycle 5,7,10. The earlier fibre bound gives an
unconditional written limit zero for cycle entry at depth k averaged over
1..2^k; the conditional logarithmic-clock limit on 1..X remains p_1>0.
The actual interval occupies a vanishing fraction of its parity period.
This is a limitation of the tested route, not evidence that p_1=1 or a
counterexample to Collatz. Fresh builds and exact finite replay passed.

The latest comparison strengthens the earlier altered-map obstruction:
swapping only O(log X) odd inputs through X preserves even halving, the
known cycle, allowed odd-image congruences, at most two parents, and
zero predecessor density at multiples of three. Kernel basin inclusions
inherit external PLD at every unit target, giving positive lower density
of both convergence and escape for this DIFFERENT map. A written early
coupling preserves the conditional large-floor passage estimates and
fixed-depth parity laws. Twenty main kernel theorem roots passed fresh
builds. The exact odd-parent values change at the swapped images; the
actual Collatz conjecture is still unresolved. See the last entry.

The latest actual-map calculation assigns loss W/(3n+1) at each odd
input and retains weight W*3n/(3n+1). Eighteen main kernel roots check
finite conservation, affine product identities, and geometric cycle
repetition. The written packing bound makes infinite remaining weight
positive exactly on divergent orbits. Conditional written passage
mixing gives a total-variation limit of the whole loss distribution,
including an infinity atom d. Its exact mass identity is
  d + sum_(N positive odd) B_N*D_N/(3N+1) = 1,
with weighted first-hit means D_N and cycle factors B_N. External PLD
makes d=0 equivalent to universal eventual periodicity, but d=0 is
unproved and additional cycles are still allowed. Under the prior
written clock theorem, the mean remaining weight at c log X tends to
one for c<3/log(4/3) and to d for larger c. Exact finite clock means,
including c=11, do not determine d. See the newest entry for scope.

The newest actual-map result proves that the stopped absolute difference
of adjacent odd counts has mean one over every full parity period, even
after conditioning on either initial input parity. Twenty-three audited
kernel roots yield an unmerged fraction at least 1/H at every depth H.
Thus whole-period balanced-coalescence errors cannot be summable; the
fair-bit fusion time has infinite mean. A stronger central-binomial
lower bound and a conditional dyadic criterion for d=0 are written.
Summability of the ACTUAL infinite-weight refinement changes remains
unproved and is not disproved by this lower bound on a larger finite-time
exception set. No external coalescence-density theorem was adopted.

The latest follow-up now proves that the actual eventual-unbalanced
even-pair fractions B_k are themselves nonsummable, using positive lower
density of the known basin from the replayed external theorem. It uses
no natural-passage premise. Eighteen kernel roots prove grade transport,
a strict pre-arrival contraction, and a three-odd-step cap for balanced
descendants of one. Written counting shows that uninterrupted balanced
refinements from any convergent root occupy zero limiting fraction.
If full Collatz holds, almost every binary path still has infinitely
many unweighted grade defects, although its infinite weights are all
zero. Thus the unweighted sufficient criterion has a false premise;
the actual WEIGHTED refinement criterion remains open. See the last
entry for the external dependency, finite scope, and verification.

The newest follow-up gives a quantitative unconditional mean bound for
the auxiliary V: mean(V_T, n<=X) <= (14/3)*X^(-log_2(8/7)) for every
T>=ceil(log_2 X), and the same bound for V_infinity. Thirteen new kernel
roots prove the finite affine identities and all-depth moments; the
source split, real power bound, and limit identification are WRITTEN.
No external PLD or passage assumption is used for this bound. Auxiliary
dyadic amplitudes are consequently summable almost surely. The exact
duality V_T*W_T=(3/4)^a does NOT give an upper bound on the escape weight.
Under the prior written natural component law and replayed PLD, any
divergent orbit would force infinite squared dyadic variation of W_infinity
almost surely. No upper bound proving finite such variation is established.
Fresh local builds and finite checks through depth 20 passed. Neither
escape nor other cycles are excluded; see the newest entry for details.

The newest actual-weight audit defines time-matched binary refinements
H_(s,k)=2^k*W_(s+k)(floor(2^k*x))/floor(2^k*x). Twenty-one kernel roots
give exact child formulas, reciprocal affine moments, and a fixed-offset
family of individual jumps >=27/512 at arbitrarily fine levels. A WRITTEN
tail makes E_s=sum_k integral|H_(s,k+1)-H_(s,k)|^2 finite for each s,
with E_s<=3s/2+23/4. Exact finite rational checks plus that written tail
give E_0<1/7 and E_16>1/4: the energies do not contract monotonically.
The required bounded subsequence as s tends to infinity remains unproved.
A WRITTEN real-scaling rigidity argument now removes the natural-passage
premise from the sufficient limiting-energy criterion. Binary stabilization
of a Collatz-invariant indicator gives a measurable limit invariant under
both x->2x and x->3x, hence a constant zero-or-one limit and natural density.
The positive gap of W_infinity converts finite squared variation into
such stabilization for the divergence indicator. Replayed PLD then excludes
escape if that finite-energy premise holds. No finite-energy premise is
established for W_infinity, and other positive cycles remain open.

The latest coalescence refinement improves the WRITTEN all-offset bound
to E_s <= (28401483/52428800)*s+6 <= 0.542s+6. Seventeen new kernel
roots give exact source-annulus transport, later equality of refinement
data, and the cutoff ceil(121s/50); independent direct counts through
depth twenty supply its constants. The strongest levelwise combination
of full-period noncoalescence caps and the existing geometric tail has
an upper-bound certificate that grows at least harmonically (using the
kernel tail), and at square-root order (using the written walk bound).
These are NOT lower bounds on E_s. Thus deeper counts alone cannot
prove bounded energy; the actual weighted contribution of unmerged
pairs still needs control. The even pair 6,7 first has equal odd counts
at positive time eleven but never merges at a common clock, and a
whole residue class has the same finite absorption-without-fusion defect.
The bounded subsequence and all other full-Collatz gaps remain open.

The newest actual-weight argument bounds the total negative refinement
drift before a reversal of the adjacent odd-count order by fourteen,
summed over ALL time offsets and binary levels. Thirty-one new kernel
roots prove shifted-weight order, first-return endpoint order, reciprocal
moments, positive-offset transitions, and exactly k+1 one-turn parity
prefixes on each depth-k source annulus. The classification induction,
source-height cutoff, and real sum are WRITTEN. The negative contribution
after a count reversal remains uncontrolled. An exact family at offset
six makes its downward product tend to 81/1024 while the immediate parent
time losses tend to zero, so no fixed pointwise charge of that kind can
cover it. The family cells have summable lengths and do not refute an
integrated bound. All fresh builds and independent checks passed; the
full escape and other-cycle gaps remain open. See the latest entry.

The newest clock argument uses the exact valuations of `3^d-1` and a
finite symmetric-walk Green function to give the WRITTEN uniform
first count-return tail `7/sqrt(H)`. The existing finite return-cycle
budget then gives balanced noncoalescence of order `H^(-1/2)` and
actual refinement energy `E_s=O(sqrt(s))`. Fifteen new kernel roots
check arithmetic inputs; the probability and energy arguments remain
written. The return-separation power budget now holds for every
`0<beta<1/3`. A separate written first-return family has separation four
and unbounded multiplier `(243/256)*(3/2)^m`, ruling out a constant bound
on raw aggregate image coefficients, but not on the actual weighted
gradients. The square-root order matches the previously proved lower
order of the coalescence-only upper-bound certificate, not a lower bound
on actual energy. Bounded actual energy and full Collatz remain open.

The newest return-image argument gives WRITTEN logarithmic moments for
the ternary density K_beta weighted by return separation: it lies in
L(log L)^alpha whenever beta>=0, alpha>0, and 3beta+2alpha<1. Twelve
new kernel roots verify prefix-weight bounds, endpoint caps, and integer
residue-count discrepancy. The resulting truncated density bounds also
hold on actual finite integer intervals, with an explicit depth/length
error. These do not permit an infinite cutoff at a fixed interval or
bound pairing with the actual future weighted gradients. The actual
energy estimate remains O(sqrt(s)), and Collatz remains unresolved.

The newest boundary-stop argument improves those WRITTEN return moments
to every power below 1/2. The affine correction has drift 1/4; combining
bounded stopping with the gap-boundary clock bound and Fatou gives
Pr(B_tau>L)<=7/(2 sqrt(L)). For returned separation from initial D,
Pr(D'>L)<=(D+6)/sqrt(L). Twelve new kernel roots check the actual
numerator and finite stopping identities and constants. The improved
cycle budget is E N<=540*2^5180. The return-image logarithmic-moment
region is now beta+alpha<1/2, and its Haar truncation error is at most
7 H^(beta-1/2)/(1-2 beta) for 0<=beta<1/2. All infinite probability
and real-analysis steps remain written. The pairing with actual weighted
gradients and bounded energy remain unproved; Collatz is unresolved.

The newest all-return argument gives the WRITTEN exponential cycle
moment E[(1+2^-5192)^N]<=2^5182. This counts cycles, not physical time.
The occupation measure over every nonfused return has clock and
separation tails O((1+log H)/sqrt(H)), giving L(log L)^alpha control
of the accumulated ternary density K*_beta for beta+alpha<1/2.
Its Haar truncation rate is O_beta((1+log H)H^(beta-1/2)). Fifteen
new kernel roots also show that the persistent family first returns
at (clock,count,separation)=(6,2,1), then has an arbitrarily costly
second excursion pointwise. Averaging remains necessary. The actual
future-gradient pairing, bounded energy, escape, and other cycles
remain unresolved; all infinite probability steps remain written.

The newest actual-gradient result rules out uniform moments
exp((G_m/C)^p) for p>1 and fixed C, on both actual returned intervals
and their progressions. The persistent family makes G_m grow linearly
at one point while the interval length grows exponentially. Eight new
kernel roots support this written norm obstruction. Thus a single
uniform complementary Orlicz norm after summing time contributions
cannot use the earlier L(log L)^alpha density estimates with alpha<1.
Ordinary averaged energy is not shown unbounded. The next result
improves the available density moments and changes the complementary
estimate that could suffice; it does not invalidate this obstruction.

The newest binary-image argument now gives the WRITTEN theorem
K*_beta in Lp for 0<=beta<1/2 and 1<=p<10/(9+2beta), counting all
nonfused returns. Eleven new kernel roots prove affine-numerator
injection on each image fibre, the exact numerator mass t*4^t/4,
and the required polynomial arithmetic. Written fibre counting yields
||rho_t||_2^2<=(t+1)(t+4)/2, hence a 3H^2 norm bound for the
all-return truncation. Its existing L1 tail then gives the Lp theorem
by dyadic interpolation. This permits every finite logarithmic moment
order for each beta<1/2. Truncated pth moments transfer to integer
intervals with factor 1+3^H/M. No bound for the actual gradient pairing
or bounded-energy subsequence follows yet; Collatz remains unresolved.

The newest temporal argument gives a weaker WRITTEN conditional escape
criterion: for every fixed k, the time average of N^rev_(s,k) tends
to zero, with no uniformity across source levels. This would make the
limiting refinements nondecreasing and their limiting energy at most
1/2. An explicit convergent inverse spine now removes PLD from this
particular implication: its normalized growth has a positive limit,
so irrational rotation makes its binary significands dense. Every
binary cone therefore contains a known predecessor of one. A positive
limiting weight cannot be closed under both binary children, proving
zero limiting weights under the proposed condition. The condition
is unproved for all levels. Twelve new kernel roots and exact full
future-time checks on fifteen finite annuli passed. Neither absence
of escape nor exclusion of other cycles has been established.

The latest density improvement controls the cumulative affine coefficient
C_t=(3^a_t+N_t)/2^t at ALL nonfused returns. Its continuation identity
C_next=lambda*C_current+b and the existing conditional return moments
give a finite summed C^eta budget for every eta<1/2. Fractional fibre
counting and binomial concentration then prove the WRITTEN improvement
K*_beta in Lp for 0<=beta<1/2 and 1<=p<6/(5+2beta), in particular
p<6/5 when beta=0. Eight new kernel roots and exact finite checks passed.
For the unweighted density, a complementary power above six could now
suffice; neither that actual-gradient estimate nor the required ordinary
integer sampling bound is proved. The temporal criterion Q and both
parts of full Collatz remain unresolved. See the last dated entry.

This file records continuity, not an additional mathematical proof. Check
current source files and their verification manifests before relying on a
specific result. The historical session transcript has already been analyzed;
the current repository contains substantial subsequent work.

## Objective and honest status

The long-term objective is a proof or disproof of the positive-integer
Collatz conjecture. No complete proof or positive-integer counterexample has
been found. Follow the latest user request when deciding what work to do next.

Two broad possibilities still require exclusion: nontrivial positive integer
cycles and nonperiodic divergent orbits. Ruling out the remaining mechanical
mask family would not by itself settle either broader problem completely.

On 2026-09-13 the user asked whether progress felt nearer 30% or 70%.
The assistant's explicitly subjective answer was nearer 30%, possibly below,
as a description of the maturity of the approach. This is **not** a measured
completion percentage, a probability of success, or a mathematical result.
We have useful restrictions but no convincing complete proof strategy with
only a few manageable gaps. Preserve this candid assessment rather than
inferring that a proof is imminent from the user's encouragement.

## Working preferences and environment

- The user wants continuity with the research direction in
  [codex-session-transcript.md](codex-session-transcript.md), rather than
  repeatedly restarting the initial analysis. Search relevant transcript
  sections when needed; current corrected notes supersede historical claims.
- The user stages and commits during ongoing work. HEAD and the index can
  change between commands. Inspect status, preserve their work, and leave
  staging/committing to them unless they explicitly request otherwise.
- Current workspace: `/Users/jean/Personal/collatz-conjecture--expansion`,
  macOS, zsh, timezone Africa/Johannesburg. Earlier Linux paths and hardware
  descriptions in dated entries are historical. Allow longer Rust/Lean
  runs and avoid concurrent heavy compiles. A short tool timeout is not
  a mathematical or build failure.
- The user has cloned `/Users/jean/Personal/collatz-two-coordinate-obstruction`.
  Prefer this local source for further review. On 2026-10-13 its clean HEAD
  was `a7275d5a73814d3d9a400c6fe6577de9542b03a3`. The local review and
  exact source/finite-check scope are in `docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md`.
- [lean-toolchain](lean-toolchain) pins `leanprover/lean4:v4.33.1`.
  The last verified compiler commit is
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
  The current local executable is `/opt/homebrew/bin/lean`.
  Recheck the Rust version if needed.
- The research Lean modules use standalone Lean without Mathlib or a Lake
  project. Build imported `.olean` files into a temporary directory and
  supply that directory through `LEAN_PATH`.
- The user said the local `.env` contains a `SUDO` credential and authorized
  its use for necessary package installations. The password itself has not
  been copied into this memory. Access it only when needed for an authorized
  installation; never echo it, embed it in visible command arguments or
  artifacts, or stage the file. Recent research checks needed no installs.

## Where to resume reading

1. [ATTEMPT.md](ATTEMPT.md): overall status, exact gaps, and reproduction.
2. [README.md](README.md): module map and links to verification records.
3. [MASK-RANK-ARITHMETIC.md](docs/MASK-RANK-ARITHMETIC.md): latest completed
   arithmetic step and its limitations.
4. [CYCLE-LOCAL-LIFTS.md](docs/CYCLE-LOCAL-LIFTS.md): preceding general
   obstruction to residue-consistency-only arguments.
5. [MASK-SPAN-BOUND.md](docs/MASK-SPAN-BOUND.md) and
   [EXPLICIT-LOG-GAP.md](docs/EXPLICIT-LOG-GAP.md): stronger written span
   restriction and explicit analytic/finite inputs.

## Established structure and remaining gaps

- [CollatzContradiction.lean](CollatzContradiction.lean) proves convergence
  equivalent to eventual strict descent for every start above one. A least
  counterexample must lie in residues `{7,15,27,31,39,43}` modulo 48.
  Universal descent in those infinite classes is still unproved.
- [CollatzCycleCriterion.lean](CollatzCycleCriterion.lean) gives a kernel
  necessary-and-sufficient test for every nonempty positive halving word:
  `D=2^H-3^k>0` and `D | W`, where
  `W=sum_i 3^(k-1-i) 2^(h_0+...+h_(i-1))`.
  Intermediate integrality, positivity, oddness, and exact valuations are
  proved. The criterion permits repetitions of the known cycle.
- Packing, ballot, growth, and repeated-prefix results constrain divergent
  trajectories but do not exclude all of them. Relevant notes include
  [ORBIT-PACKING-BOOTSTRAP.md](docs/ORBIT-PACKING-BOOTSTRAP.md),
  [ORBIT-PACKING-LOG.md](docs/ORBIT-PACKING-LOG.md), and
  [NO-DESCENT-BALLOT.md](docs/NO-DESCENT-BALLOT.md).
- The mechanical distance work excludes the specified cycle words through
  nearest half-Hamming distance 31. Full critical `21→12` mask families
  contain positive rational cycles far beyond that distance; rational
  realization does not establish integer realization.
- [MechanicalMaskArithmetic.lean](lean/MechanicalMaskArithmetic.lean)
  proves `W_mask = D + 4C-X`, with `0 ≤ X ≤ C`, for tokenized independent
  `21→12` edits. Integrality is exactly `D | (4C-X)`.
- [MaskSubsetDecoder.lean](lean/MaskSubsetDecoder.lean) proves complete
  decoding of the possible integer subset targets. Native finite
  certificates reject all `2^80` masks at `(k,N)=(193,306)` and all
  `2^1231` at `(2966,4701)`. This is not an all-count theorem.
- The repository's written resonance/logarithm arguments exclude the full
  critical mask family through `N=10^4000`, using the recorded finite cover
  and external small-period input. They also exclude the specified pure
  `22→13`, alternating `21→12`, and no-adjacent-halving-ones subclasses at
  every period. The all-index analytic proofs are written, not wholly
  formalized; read [the scope record](results/explicit-log-gap/verification.json).
- The narrow-cycle classification is a written reduction of primitive
  integer cycles satisfying `3M+1<8m` to critical masks. Here `m,M` are
  the minimum and maximum odd states. The stronger written all-period
  conclusion is `20M>49m` for nontrivial integer cycles, with the
  dependencies in [the span record](results/mask-span/verification.json).
  These inequalities do not exclude arbitrary wider cycles.
- Automatic folded rank order holds for the surviving close count regime.
  It is compatible with arbitrary positive rational mask forcing, so
  ordering alone does not reject the remaining masks.

## General local lifts: completed preceding step

[CycleLocalLifts.lean](lean/CycleLocalLifts.lean) proves that every nonempty
positive halving word with `D>0` has positive odd integer edge witnesses
forming a closed residue walk modulo every `2^a 3^b`, for `a>0,b≥0`.
The actual accelerated map at each witness has the prescribed exact
halving exponent. Successive chosen witnesses need agree only modulo the
chosen modulus, not as integers.

This theorem does not assume `D | W`. Therefore pure residue consistency
at powers of two and three cannot reject any such word. A complementary
kernel lemma recovers integer divisibility when a fixed height bound makes
the congruence an equality. This does not invalidate the residue sieve,
which retains actual descent inequalities.

The explicit modulus-64 walk is `43→33→57→43`, with integer edge witnesses
`107,161,57`. Their actual successors are `161,121,43`, so these witnesses
are not an integer cycle.

[Verification](results/cycle-local-lifts/verification.json) records kernel
proofs and independent checks of 2,883 small words at four precisions,
75,016 actual integer edges, and four larger masks.

## Latest result: mechanical rank normalization

Sources:
[MaskRankArithmetic.lean](lean/MaskRankArithmetic.lean),
[written argument](docs/MASK-RANK-ARITHMETIC.md),
[independent replay](verify_mask_rank_arithmetic.py), and
[verification manifest](results/mask-rank-arithmetic/verification.json).

For coprime counts `k,N` with `k>1`, `3k≤2N<4k` and `D=2^N-3^k>0`:

- Set `s=2k-N`. Cut the lower mechanical halving word after its first
  symbol. Eligible pair midpoints have ranks `j=0,...,s-1`.
- Choose `qN=kt+1` and `z=2^t(3^q)^(-1) mod D`.
  Then `2z^k=1`, `3z^N=1`, and `4z^s=3` modulo `D`.
- In this rank order, `c_j=2^(N-2)z^j mod D`.
  If `G_s=1+z+...+z^(s-1)`, then `4(1-z)G_s=1 mod D`.
  Hence the total coefficient satisfies `gcd(C,D)=1`.
- With `E(z)=sum_j epsilon_j z^j` and `epsilon_j∈{0,1}`, the exact mask
  condition becomes `(1-z)E(z)=1 mod D`.
  This is an equivalent reformulation; no all-mask exclusion follows yet.

The modular algebra, explicit phase/exponent implication, unit-to-gcd
conversion, and equation equivalence are kernel checked. Full mechanical
floor/permutation reindexing and specialization are written bridges.

Written consequences include the exact gcd formula for repeated mechanical
words and recovery of the unedited mechanical-cycle exclusion. A separate
written lemma says that `M-1` arbitrary unit coefficients modulo `M`
have subset sums covering every residue. Thus tests at divisors of `D`
with combined least common multiple `M≤s+1` cannot reject every mask.
Separate smallness of each divisor is insufficient for this conclusion.
The combined modulus matters.

Large multiplicative order does not imply linear independence of powers.
The checked example `k=11,N=18,D=84997` has divisor 11 and `z=6 mod 11`
of order 10, but `4+3z+4z²+3z³=814` vanishes modulo 11.
The corresponding mask fails divisibility by the full denominator.

Latest fresh verification used sequential Lean 4.33.1 builds of
`CollatzCycleCriterion`, `CycleLocalLifts`, and `MaskRankArithmetic`.
All passed without warnings, admitted proofs, or native evaluation.
Only standard logical axioms were printed.
The Python replay passed 42,158 rank-coefficient checks, rejected 30,436
exhaustively enumerated masks at the recorded small coprime critical
count pairs, and checked further masks, repeated-word gcds, and modular
coverage instances. File hashes and local links were checked.
No Rust code changed in this latest research step.

To reproduce just this step:

```sh
rank_build_dir=$(mktemp -d /tmp/collatz-mask-rank.XXXXXX)
lean -o "$rank_build_dir/CollatzCycleCriterion.olean" CollatzCycleCriterion.lean
LEAN_PATH="$rank_build_dir" lean -o "$rank_build_dir/CycleLocalLifts.olean" lean/CycleLocalLifts.lean
LEAN_PATH="$rank_build_dir" lean lean/MaskRankArithmetic.lean
python3 verify_mask_rank_arithmetic.py
```

## Known implementation issues and research cautions

Two tooling issues were reproduced during the initial analysis and remain
unfixed in the code inspected on this date:

- [src/bin/residue-sieve.rs](src/bin/residue-sieve.rs): canonical-path
  comparison misses distinct hard links to the same inode. Aliased
  certificate and manifest destinations can overwrite the certificate.
- [bench/compare.py](bench/compare.py): the certificate path from a
  historical manifest can be an absolute path from the previous Mac.
  The check-only path then fails on Linux.

These are separate from the current mathematical research. Recheck their
current status before fixing them.

Keep these distinctions explicit when continuing:

- Distinct subset sums as ordinary integers need not be distinct modulo `D`.
- Compatible local residues and positive rational cycles are not integer cycles.
- An equivalent normalized equation is not a new exclusion.
- Finite bounds, however large, do not measure distance to a universal proof.
- Kernel lemmas do not automatically certify the written analytic or
  combinatorial arguments that use them.
- Progress on a restricted cycle family does not settle wider cycles or
  nonperiodic divergence.

The next research advance must address the remaining full-denominator
equation or add an argument covering every positive-integer orbit. Fixed
small-modulus consistency alone has the limitations recorded above.
Treat this as a direction to investigate, not a promised proof strategy.

## Persistence mechanism

[AGENTS.md](AGENTS.md) points future repository sessions to this file.
Repository-level AGENTS.md discovery is documented in
[the official OpenAI instructions guide](https://learn.chatgpt.com/docs/agent-configuration/agents-md).
This is explicit file-based project memory, not a claim that a separate
account-level memory service was updated.

## 2026-10-08 update: current workspace and coalescence

The September environment and latest-result descriptions above are historical.
The current workspace is `/Users/jean/Personal/collatz-conjecture--expansion`,
macOS with zsh and the same Lean 4.33.1 pin. The user pulled remote research;
merge commit `23e746a` integrated it. The requested conflict check found no
unmerged index entries or conflict markers. Preserve untracked `.DS_Store`
and `CLAUDE.md`; the latter prohibits Git writes without explicit consent.
No staging or committing was performed during this work.

[CoalescenceDescent.lean](lean/CoalescenceDescent.lean) now kernel proves:

- Convergence is equivalent to every `n>1` meeting an orbit from some
  `0<m<n`, with potentially different meeting times. Strong induction
  transfers convergence from the smaller start.
- Exact affine certificate soundness, combining direct descent and
  equal-time/equal-weight merging of residue classes.
- The complete depth-eight table covers 240/256 classes, compared with
  237 for direct descent alone. New residues are 63, 207, and 223.
  A least counterexample must belong to the remaining 16 residue classes
  listed in Section 9 of APERIODIC-ATTEMPT.md.
- For every fixed horizon K there is a start above one that cannot meet
  any smaller natural start within K steps on either orbit. The theorem
  allows unequal times and is a universal kernel proof, not an inference
  from finite testing. It does not provide one orbit that never merges.

The key obstruction uses `2^K | n+1` and `3^K | n`. For a hypothetical
meeting `U^(c+a)(m)=U^a(n)`, split the smaller orbit into a prefix with
odd weight i and a suffix with odd weight h. The suffix's maximal additive
bound and exact all-odd growth force its start to be at least
`3^(a-h)*n`. Divisibility by `3^i` and the discrete orbit bound then pull
this back to `m >= 2^c*T`. The lower additive bound yields `A <= B`, where
`A=3^(i+h)` and `B=2^c*3^a`, and therefore `m>=n`.
The formal existence proof recursively cubes `n+1`, starting at n=3,
to increase both divisibilities. No CRT library or outside theorem is needed.

[verify_coalescence.py](verify_coalescence.py) independently checks 1,198
large and small lifts of the depth-eight certificates. At depths 12, 16,
and 18, coalescence adds 44, 394, and 1,391 classes respectively beyond
direct descent at the same depth. These larger counts are Python-only.
An exhaustive inverse-tree replay for horizons 1 through 24 checks 716,286
nodes and 571,137 shifted-start identities. All passed.

Reproduction and hashes are in
[results/coalescence/verification.json](results/coalescence/verification.json).
Build CollatzAffine, CollatzContradiction, and CollatzGrowth into LEAN_PATH
before building the new module. No admitted proofs or native evaluation
are used in this module. The universal Collatz claim is still unresolved.

The immediate research implication is that coalescence is a sound broader
induction tool, but a fixed bound on both orbit lengths cannot close it.
Further work must give a genuinely start-dependent argument or another
global constraint. Do not mistake the 16 remaining residue labels for
a finite set of unresolved integers.

## 2026-10-08 follow-up: horizon versus input size

[CoalescenceHeight.lean](lean/CoalescenceHeight.lean) imports the preceding
module and proves that its witnesses can be chosen with
`3^K <= n < 6^K` for every K≥1. Reduce the constructive large witness
modulo `2^K*3^K`; the two divisibilities survive, and the residue is
nonzero. This gives a universal logarithmic lower bound on the necessary
meeting horizon along an unbounded sequence. It does not disprove a
logarithmic upper bound, which remains unproved.

The same module proves an exact example with no cap on the smaller orbit:
for 0<m<27, a<59, and every b≥0, `U^a(27) != U^b(m)`.
All smaller starts lie in the 34-element invariant set
`{1,...,26,29,32,35,38,40,44,53,80}`, disjoint from the first 59 states
of the orbit of 27. At time 59 it reaches 23. The first coefficient
drop is also 59. These are kernel proofs without admitted terms or
native evaluation.

[verify_coalescence_height.py](verify_coalescence_height.py) independently
checks the invariant set and CRT representatives for horizons 1–256.
It also computes exact minimum values of max(a,b) for smaller-start
meetings for n=2,...,32768, searching through 192 steps. Every start
finds a meeting, making the minimum exact within this finite range.
The largest observed ratio to ceil(log2(n)) is 59/5 at 27. This supplies
no universal upper bound. The verification manifest is
[results/coalescence-height/verification.json](results/coalescence-height/verification.json).

The attempted bridge from first multiplier drop to smaller coalescence
remains unproved. The direct-descent version is the coefficient stopping
time conjecture already recorded in CollatzAffine.lean; the new work must
not silently assume it. A universal finite first-drop theorem is also
missing. Section 10 of APERIODIC-ATTEMPT.md records these gaps and the
primary literature reference. The objective remains the full conjecture.

## 2026-10-08 follow-up: bidirectional ranks

The next attempt allowed a rank to decrease along either a forward or
inverse Collatz edge. Strong induction on a natural-valued rank, plus a
finite verified base, would prove the full conjecture. This sufficient
criterion is kernel proved in
[CoalescenceEnvelope.lean](lean/CoalescenceEnvelope.lean).

The same module strengthens the CRT-class obstruction to exact inequalities:
if `U^a(n)=U^b(m)`, a,b≤K, `2^K | n+1`, and `3^K | n`, set
`A=2^a*3^wt(b,m)` and `B=2^b*3^a`. Then `B*n <= A*m` and
`A*(m+1) <= B*(n+1)`. Thus `m=q*n+c` with `q=B/A >=1` and
`0<=c<=q-1`. Both time orderings are kernel checked. Independent Python
replay checks 716,286 inverse nodes.

[search_graph_ranks.py](search_graph_ranks.py) uses exact Z3 linear-real
constraints for `R(n)=a_r*n+b_r`, r modulo M, with positive slopes.
It allows neutral leading slopes with strictly negative constant change,
and arbitrary finite exceptional ranges. All 22 tested moduli through
the recorded maximum 144 returned unsat. These are SMT results, not Lean
certificates. The user approved downloading z3-solver into
`/tmp/collatz-rank-solver`; version 5.1.0.0 was installed with uv. No
repository environment or dependency file was changed. Use PYTHONPATH
pointing there, or install that package in a chosen environment for replay.

Section 11 of APERIODIC-ATTEMPT.md gives a broader written obstruction:
no rank selected from a finite set of positive-slope affine formulas can
offer a decreasing adjacent edge at every sufficiently large integer.
The assignment of formulas need not be periodic. This complete theorem
is written, not fully Lean checked. Its proof uses the kernel envelope:
a strictly decreasing path is forward then backward (no reversal after
the first inverse edge), and its normalized leading rank stays between
the smallest and largest palette slopes. Strict leading drops have a
fixed multiplicative gap; neutral oriented runs cannot revisit a formula,
since that would require `2^length=3^odd_count` with positive length.
These give a fixed path-length bound contradicted by a sufficiently
deep, sufficiently large CRT start.

[results/coalescence-envelope/verification.json](results/coalescence-envelope/verification.json)
records all scopes, hashes, builds, independent replay, and SMT outcomes.
The full conjecture remains unresolved. The finite-affine bidirectional
rank template is exhausted by the written obstruction; repeating that
search at larger moduli is not a useful next step. Nonlinear ranks or
unbounded arithmetic features are not excluded by this theorem.

## 2026-10-08 follow-up: four-feature valuation ranks

APERIODIC-ATTEMPT section 12 gives a written exclusion of every bounded-below
rank `C log₂n+a ν₂(n)+b ν₂(n+1)+c ν₃(n)+d ν₃(n+1)`, `C>0`,
that supplies a decreasing shortcut-graph neighbor at all sufficiently
large integers. Along `3·2^k`, boundedness below forces `C+a≥0`.
Use a single shared `L=C log₂(3/2)`, with `7C<12L` and `5L<3C`.
Treating forward and inverse logarithms as independent bounds can create
false feasibility; the shared variable is essential.

Five stable progression patterns, with seeds 131,134,137,142,147 and
moduli 432,1296,216,864,72, give exhaustive neighbor alternatives.
Their odd forward limit conditions are strict; odd inverse conditions
are weak because the true ratio tends to 2/3 from below. All 108 ways
to select an alternative contradict the common background inequalities.
Each contradiction has nonnegative integer weights with identically zero
coefficient sum and a positive weight on a strict inequality.

[ValuationGraphRank.lean](lean/ValuationGraphRank.lean) kernel-checks the
five universal feature/edge progression lemmas, the two logarithm-bound
power comparisons, and all 108 finite certificate identities and selection
coverage. The all-real weighted-sum interpretation and logarithmic limit
argument are written bridges. No full real-valued rank theorem is claimed
as kernel formalized. The independent
[verifier](verify_valuation_graph_rank.py) reconstructs the constraint rows
and checks the integer certificates without Z3. Files and hashes are in
[the verification record](results/valuation-graph-rank/verification.json).

Boundedness below alone does not ensure termination of a decreasing
real-valued rank; finite sublevel sets would be a sufficient extra condition.
Here even the local decreasing-edge property fails under the weaker
bounded-below assumption. This does not exclude arbitrary nonlinear
functions of valuations or additional features. Exploratory larger-feature
SMT results were not promoted to verified universal theorems. The full
Collatz objective remains unresolved and active.

## 2026-10-08 follow-up: proper nonlinear and quadratic ranks

An unrestricted nonlinear bounded-below rank is not enough:
`R(n)=log₂n-ν₂(n)+2^(-ν₂(n))` is positive and decreases on every doubling
edge. Along powers of two it tends to zero. A useful real rank needs a
well-founded decrease condition; finite sublevel sets (properness) suffice.

[GraphRankNecessity.lean](lean/GraphRankNecessity.lean) proves that any
natural-valued graph rank with local descent beyond N has
`R(2n)>R(n)` and `R(U(n))<R(n)` for every `n>N` divisible by three.
Such n have no odd predecessor. If doubling failed to increase rank,
local descent on the degree-two doubling ray would force an infinite
strict rank descent. The Lean proof uses strong induction on the rank.
The written extension to proper real ranks takes a rank minimum on the
ray, whose sublevel sets are finite.

APERIODIC-ATTEMPT section 13 uses this graph restriction to exclude every
proper `C log₂n+P(ν₂(n),ν₂(n+1),ν₃(n),ν₃(n+1))`, C>0, with P of total
degree at most two. Let the variables be x,y,z,w. Terms xy and zw vanish
identically. Properness plus the graph restriction forces coefficients
of x² and y² to vanish. For linear coefficients A of x and B of y and
cross coefficients G_yw,G_xw, necessary inequalities are
`C+A≥0`, `B≤0`, `G_yw≥0`, `A+G_xw≤0`. The written proof also derives
G_yz=0, but the finite contradiction does not need that constraint.
These restrictions use explicit unbounded valuation families, not a
finite sample inference. A finite quadratic fit otherwise evades every
sample by placing its eventual turning point beyond the tested range.

Six stable patterns at seeds 151,153,155,170,230,233, plus those inequalities
and `12L>7C` for L=C log₂(3/2), contradict all 162 possible edge selections.
At seed 153 the forced forward condition replaces bidirectional choice.
Nonnegative integer certificate weights have maximum 36. No numerical
logarithms or trusted SMT answers enter the final replay.

[QuadraticValuationRank.lean](lean/QuadraticValuationRank.lean) proves all
six universal feature/edge progressions and checks all finite certificate
identities and their exhaustive selections. The independent
[Python verifier](verify_quadratic_valuation_rank.py) reconstructs the
quadratic differences and checks all 162 certificates. The universal
properness/coefficient/logarithm argument and weighted-sum interpretation
over reals remain written bridges; this is not a full Lean real-rank theorem.
The [manifest](results/quadratic-valuation-rank/verification.json) records
fresh builds, logs, hashes, and exact scope.

Do not repeat the quadratic synthesis search without a new feature or
changed hypothesis: this whole proper template is excluded by the written
argument. General nonlinear functions, additional features, and unrelated
global proof strategies remain open. No full proof or counterexample has
been found; the original Collatz goal stays active.

## 2026-10-08 follow-up: graph orientation and the broader rank obstruction

[GraphRankOrientation.lean](lean/GraphRankOrientation.lean) proves a generic
functional-graph theorem: if S is forward closed and a well-founded relation
offers a decreasing adjacent neighbor outside S, then the forward successor
itself decreases outside S. Well-founded induction: a smaller predecessor
outside S must decrease back to the original vertex, a forbidden two-cycle.
The generic theorem and its asymmetry lemma have no axioms.

For a Collatz proof with a **verified convergent finite base** 1..N,
enlarge the base to its entire forward closure plus zero. This is finite,
closed, and bounded by some B. Any natural graph rank, or proper real graph
rank, therefore decreases forward at every integer above B. Bounded-below
real ranks alone do not suffice. Existence/boundedness of this closed base
must not be assumed for an unverified arbitrary N.

Combining with section 8's exact growing path
`192s-5 → 288s-7 → 432s-10 → 216s-5` gives a kernel obstruction for
natural ranks monotone between matching four-valuation/residue features.
Take s a sufficiently large multiple of the modulus so the whole path
lies above B. The endpoints have valuations (0,2,0,0), equal residues,
and increasing size, contradicting forced forward rank decrease.

APERIODIC-ATTEMPT section 14 combines the generic orientation theorem with
section 8's written all-polynomial valuation construction. The written
corollary excludes **any** size-monotone well-founded graph rank built from
a fixed finite set of polynomial valuations at finitely many primes and
fixed-modulus residues, with a bounded closed base. In particular, proper
`C log₂n+G(features)` ranks are excluded for arbitrary nonlinear G, C>0.
This closes the larger proof strategy rather than only quadratic formulas.
Unlike the earlier quadratic exclusion, this argument explicitly uses
bounded forward closure of the exceptional base; keep that hypothesis.

The proper-real well-foundedness bridge, constructing the finite closure
from verified base convergence, and the full polynomial-feature corollary
are written. The general well-founded graph theorem and natural-rank
four-feature obstruction are kernel proved. The independent replay checks
six closed finite bases through 32768 and 42 growing witnesses above their
maxima. [Manifest](results/graph-rank-orientation/verification.json).

Do not continue enlarging polynomial degree or adding finitely many
polynomial valuation features to this size-monotone graph-rank template.
For this proof strategy these changes are excluded by the written corollary.
Other magnitude dependence, different information, or a non-ranking global
argument remains open. The actual Collatz objective remains unresolved.

## 2026-10-08 follow-up: separated binary blocks

The next attempt used binary digit counts, outside the preceding finite
polynomial-valuation theorem. Weighted counts of zero-padded windows
failed exact SMT synthesis at widths 1–9. The final proof does not trust
SMT: four families supply an all-width positive-weight cancellation.

For a window width w, pad the usual binary word on both ends by w-1 zeros.
A score `R(n)=β+α bitlength(n)+Σ λ_v count_v(n)` satisfies
`R(2n)=R(n)+z`, z=α+λ_zero, and for a,b>0 with k-bitlength(b)≥w-1,
`R(a·2^k+b)=R(a)+R(b)+(k-bitlength(b))z-c`,
c=β+(w-1)λ_zero. The written counting proof separates windows meeting
the two blocks; only the extra all-zero windows remain.

For q=2^k and sufficiently large k, the edges and rank differences are:
`2q+2 → q+1`: -z;
`2q+21 → 3q+32`: R(3)-R(21)+3z;
`6q+9 → 9q+14`: R(7)-R(3);
`14q+1 → 21q+2`: R(21)-R(7)-z.
The first requires z>0; the other three sum to 2z. Their weighted sum
with weights (2,1,1,1) is zero, so strict decrease on all four is impossible.
All sources grow without bound. No finite exception range fixes this.

[DigitBlockRank.lean](lean/DigitBlockRank.lean) kernel-proves the four
edges and no eventual forward descent for any integer score satisfying
the two structural laws, at any fixed gap threshold. The window-count
interpretation for all widths and extension to real scores are written
bridges in APERIODIC-ATTEMPT section 15. The independent replay checks
widths 1–64, minimum and larger gaps, and the exact feature-vector
cancellation up to exponent 4096. [Manifest](results/digit-block-rank/verification.json).

This also excludes well-founded graph ranks of this form with a bounded
forward-closed verified base, by section 14. Do not overgeneralize:
independent prefix/suffix corrections, nonlinear counts, distant-block
interactions, and varying return times are not covered. The particular
zero-padding/additivity hypotheses matter. No Collatz proof or positive
counterexample has been found; the full goal remains active.

## 2026-10-08 follow-up: inverse basins versus orbit packing

Do not compare an inverse-basin lower bound directly with the project's
orbit-packing upper bound. The latter requires a forward-closed set with
injective U. A branching inverse basin does not satisfy that hypothesis.

[InverseBasinAudit.lean](lean/InverseBasinAudit.lean) proves:
for 3|a, B(a) is exactly {2^k a}; for 3∤a, explicit distinct positive
basin points have the same immediate image and reach a within two steps.
Every forward-closed injective subset of B(a) is a chain under forward
iteration, by cancellation of equal iterates. In B(1), such a subset
contains only 1 and 2; the last theorem has no axioms. This shows why
even large basin cardinality does not provide the injective orbit count
needed for a contradiction. No universal nonconvergent-basin upper bound
or sufficient injective-chain lower bound has been established.

The chain conclusion is also proved for forward-closed injective subsets
of the full coalescence component C(a)={n: some iterate of n equals some
iterate of a}. For a nonperiodic a, B(a) contains no nonempty forward-closed
subset at all: closure would include U(a), whose return to a would make a
periodic. This additional closure issue is kernel checked. Switching to
C(a) restores forward closure but not injectivity or branching counts.

The literature check used the original Krasikov–Lagarias paper
https://arxiv.org/pdf/math/0205002 only for scope: its x^0.84 count is an
inverse-basin count for roots coprime to three, not a single-orbit count.
No claim about the current best exponent is made.

Search metadata for arXiv:2512.13760 still showed v1's claimed x^0.946
improvement, but the current v2 (17 December 2025) reports x^0.3227.
The audit kernel-checks a counterexample to v1 Lemma 2.2: u=(3,1) allows
v1=5 or 6 and v2=1 or 2, none satisfying its congruence modulo nine.
It also checks failure of uniqueness as stated in v2 Lemma 3.1: at level
one and u1=2, exponents 8 and 10 both meet the displayed conditions and
yield 85 and 341. This does NOT refute the weaker final density bound
or every possible repaired argument. Neither version is a dependency.
Use versioned primary links in APERIODIC-ATTEMPT section 16, not stale
search snippets, for these claims.

The independent Python replay checks 21,846 small-root collisions, six
large roots, 325 dyadic basin examples, and the congruence examples. The universal structure results
are kernel checked separately. [Manifest](results/inverse-basin-audit/verification.json).
The full Collatz conjecture remains unresolved and the goal remains active.

## 2026-10-08 follow-up: quantitative fibre multiplicity

The largest fibre of U^k among residues below 2^k **at a fixed parity
weight** has size D_k at least
`max_j ceil(binom(k,j)/3^j) ≥ ceil(4^k/((k+1)3^k))`.
There are binom(k,j) weight-j parity residues and only 3^j possible images.
For the second bound multiply binom(k,j)≤D_k 3^j by 3^(k-j), sum, and
use the binomial theorem. This all-depth proof is written, not fully Lean.
It excludes any constant, polynomial, or subexponential universal bound
on this multiplicity; it does not give an upper bound or the exact rate.

[InverseFibreGrowth.lean](lean/InverseFibreGrowth.lean) proves weight
periodicity under shifts by 2^k, and equivalence of same-weight fibre
equalities between all aligned blocks. It certifies 48 distinct positive
residues r below 65536 with wt(16,r)=4 and U^16(r)=2. For every q≥0,
65536q+r therefore share weight four and endpoint 81q+2. No convergence
claim about arbitrary shifted endpoints is made.

The Python replay enumerates all 2,097,150 residue inputs at depths 1–20,
checks binomial histograms and exact weighted identities, and determines
the finite maxima: 48 at depth 16; 140 at depth 20 (weight 5, endpoint 47).
Maximality is Python evidence; the Lean certificate only proves the
48-member family and its universal lifts. It also replays 288 shifted
certificate members, including large quotients.
[Manifest](results/inverse-fibre-growth/verification.json), APERIODIC-ATTEMPT section 17.

This rules out fixing the previous inverse-basin packing mismatch with
a uniformly small collision multiplier. It does not show that any of
these large fibres lie in a nonconvergent component. A bound using special
properties of an exceptional component, or a different global argument,
is still missing. Do not equate generic fibre growth with Collatz failure.
The full objective remains unresolved and active.

## 2026-10-08: external method review and fixed-root branching

The user suggested https://github.com/openai/math as methodological inspiration.
APERIODIC-ATTEMPT section 18 records the targeted review and source links.
The main leads are: explicitly account for information lost by collisions;
investigate scale-dependent trapping with variable return times; and audit
conditioning and quantifiers rather than replacing every-start claims with
almost-everywhere statements. No external theorem from the collection is
adopted as a premise. Its mass-action scope covers initial-state-dependent
bounds, not necessarily the stronger later common absorbing-set statement.
Comparator challenge `sorry` placeholders are statement specifications;
separate solution modules are selected by their JSON configurations. We
did not build those external solutions or validate all manuscript proofs.

The previous suggestion that exceptional components might avoid large
collisions is now excluded for unrestricted fixed-root fibres.
`lean/UniformInverseBranching.lean` proves that for every a%3≠0, its binary
inverse tree has 2^h distinct positive unit leaves n with time 6h, weight h,
endpoint a, and 3^h*n≤64^h*a. Children are 192*(a/9)+d with pairs
r1:(16,20), r2:(32,40), r4:(80,85), r5:(104,106), r7:(148,149),
r8:(160,170). They arise by synchronizing the two valid inverse exponents
in 1..6; every child is greater than its parent and reaches it in six steps.

Written corollaries: if a<3^h all leaves are below 2^(6h); a bad root
would make every leaf bad; a uniform leaf distribution loses exactly h
bits when mapped to its common endpoint. Every hypothetical counterexample
eventually has a unit iterate, so this applies to every hypothetical bad
component. Do not confuse this with an upper bound, with entropy of whole
affine maps, or with a count along one orbit. Basin1 has these trees too.

`python3 verify_uniform_inverse_branching.py` passed 6,679 root checks,
36,846 leaf checks, and three fresh Lean builds. The manifest is
`results/uniform-inverse-branching/verification.json`; APERIODIC section19.
Lean's printed dependencies have no sorryAx or native evaluator axioms.
The all-depth counting, distinctness, weight, endpoint and height bound
are kernel checked; the entropy and exceptional-component interpretations
are written. Full Collatz remains unresolved; the goal stays active.

Local merge audit at this point: HEAD7590f75, tracked tree initially clean,
no unmerged index entries, no MERGE_HEAD, and no conflict markers found
in the source/document scan. `.DS_Store` and `CLAUDE.md` were untracked
and were preserved. No staging, commits, pull or other Git mutations.

## 2026-10-08: residue shadows and the scale-dependent certificate gap

The previous goal turn was progress: universal binary inverse trees were
kernel verified. This turn examined what finite residue information can
contribute to the proposed variable-return trapping approach.

APERIODIC section 20 proves in writing that every positive unit root a
has arbitrarily large ancestors in every residue class modulo `2^A*3^B`.
Choose positive n in the class and k≥A with n<2^k. Then j=wt(k,n)>0
and y=U^k(n) is coprime to three. Solve a2^e≡y mod3^(j+B), increase e by
period `2*3^(j+B−1)` until Q=(a2^e−y)/3^(j+B)>0, and put
N=2^k3^B Q+n. The affine identity gives U^k(N)=a2^e, hence
U^(k+e)(N)=a; increasing e gives arbitrarily large N. A full elementary
modular-lifting proof is included via `4^(3^s)=1+3^(s+1)c_s`, with `c_s≡1 (mod 3)`.

Consequently, convergence of all sufficiently large members of ANY one
fixed mixed residue class would imply full Collatz. If a counterexample
exists, both convergent and nonconvergent starts occur arbitrarily high
in every class. This is congruence/topological density, not positive
natural density. It does not refute whole-class descent certificates or
scale-dependent arithmetic certificates. The ancestors can be enormous;
no smaller predecessor or quantitative trapping estimate follows.

`lean/BasinResidueShadow.lean` proves unit preservation and the exact
transport identities conditional on the displayed power equality, plus
capture by a forward-closed set containing that cylinder. Universal power
lifting, density and the one-class equivalence are WRITTEN, not kernel
proved. No admitted theorem/extra axiom supplies existence.

`python3 verify_basin_residue_shadow.py` passed 3,276 ancestor checks,
2,184 modular lifts and three fresh Lean builds. Four unit roots include
2^128+1; all residue classes with A=0..5 and B=0..2 are checked. Largest constructed
ancestor: 39,098 bits. Pure-halving tails use the separately kernel-proved
identity rather than enumerating every halving. Manifest:
`results/basin-residue-shadow/verification.json`.

Next research still requires an actual size-sensitive progress estimate
for variable return times. Repeating the density argument or merely
restating a descent equivalence would not supply that estimate. Both
nontrivial cycles and divergent orbits remain unresolved; goal active.

## 2026-10-08: quantitative residue transport and fixed-prefix cost

Previous goal turn classified as progress: the mixed-residue construction
and conditional transport were checked. This turn quantified its size
and tested whether it could produce smaller values for induction.

APERIODIC section 21: fix positive representative n<2^k, j=wt(k,n)>0,
y=U^k(n), J=j+B, T=2*3^(J-1), 2^L>y, E=L+T-1. The minimal
admissible power exponent e satisfies e≤E for every unit root a. The
constructed ancestor F(a) reaches a by time k+E and obeys
3^j F(a)+D=2^(k+e)a, D=2^k y-3^j n>0; hence F(a)≤C a with
C=2^(k+E)/3^j fixed for the cylinder. On odd roots the map is injective,
because 2^e a=2^f c forces a=c. This transfers counts from the odd unit
part of any predecessor-closed set to every cylinder without changing
the count exponent. It does not apply directly to a single forward orbit.

For the FIXED prefix followed only by halvings, the sharp worst
asymptotic multiplier is C*=2^(k+T-1)/3^j>1. Infinitely many odd roots
in a fixed class modulo3^J force e=T-1. Every prefix intermediate has
slope at least (4/3)^j>1 as a function of these roots; the halving tail
stays at least a. For sufficiently large roots in that class, the whole
constructed path contains no value below a. This excludes using the
same construction alone as a universal descent certificate. It does not
exclude other inverse paths or prefixes chosen adaptively for each root.

`lean/ResidueShadowCost.lean` kernel-proves conditional size bounds,
odd dyadic uniqueness, shadow injectivity and that the prescribed prefix
ends at least as high as its root. Universal modular existence, counting
transfer, sharp asymptotics and intermediate-slope argument are WRITTEN.
`python3 verify_residue_shadow_cost.py` checks 42,532 ancestors, 343
odd roots across 124 cylinders, and 248 sharp witnesses with complete
path checks. Four fresh Lean builds pass; standard propext/Quot.sound
only in printed dependencies. Manifest: `results/residue-shadow-cost/verification.json`.

Next work must supply a genuine progress estimate, potentially through
root-dependent path selection. A fixed-cylinder linear upper cost is
not a contraction, and count transfer alone does not defeat the basin
versus injective-orbit obstruction. Full objective unresolved and active.

## 2026-10-08: adaptive inverse paths on unit roots

Previous turn was progress: the fixed-prefix cost was quantified and
checked. This turn permitted every inverse path within a chosen depth.
`lean/AdaptiveInverseBarrier.lean` kernel-proves the exact positive
inverse level at a=3^K*q+1 for k≤K:
m=r+2^k*3^(K-j)*q, with 0<r≤2^k, U^k(r)=1, j=wt(k,r)=wt(k,m).
Use the unique positive remainder r modulo 2^k, whose image is in
[1,3^j]; the image's congruence to 1 modulo 3^j forces it to equal 1.
The converse affine lift is proved too, and 3^j*r≤2^k gives m≥a.
Strict m>a for q>0,k>0 is a written corollary. Hence even the odd
unit roots 2*3^K+1 have no smaller ancestor within K inverse steps.

APERIODIC section 22 additionally proves in writing: if n>1 is 1 modulo
3^K and −1 modulo 2^K, no m<n has U^a(n)=U^b(m) with a,b≤K.
For b≥a, c=b−a, z=U^c(m), i=wt(c,m), h=wt(a,z), P=3^i,
d=3^(a−h), the old intercept bounds give d*n≤z≤d*(n+1)−1.
If P≤d, scaled-image bounds give m≥n. Otherwise P≥3d; positive
residue reduction of m modulo 2^c gives s=U^c(r) in [d,2d−1] and
the exact quotient Q=d*3^(K−i)q where n=3^Kq+1. If 2^c*d<P,
the coefficient bound forces r=1. Its cycle {1,2} forces d=s=1,
contradicting P>2^c*d. Thus 2^c*d≥P, yielding m≥n. This extends
the earlier nonunit CRT obstruction to unit roots. For K≥2 the least
CRT witness lies between 3^K and 6^K, giving logarithmic lower bounds.

The inverse-level statement is KERNEL checked; the unit-root two-sided
extension and logarithmic consequence are WRITTEN. Do not merge their
verification scopes. `python3 verify_adaptive_inverse_barrier.py`
checks 30,188 inverse ancestors for 80 roots through depth 20, then all
397,752 inverse nodes for 72 two-sided witnesses through K=18. Five
fresh Lean builds pass. Manifest:
`results/adaptive-inverse-barrier/verification.json`.

The obstruction concerns bounded depth, even with adaptive branch
selection. It does not exclude unbounded rules whose depth grows with
input size. No such universally successful rule or other complete proof
has been found. The Collatz objective remains unresolved and active.

## 2026-10-08: openai/math review II, citation correction, mask barrier

A review of openai/math in update order found no manuscript on Collatz.
Its μ(π)=2 method was adapted on 2026-10-08 to μ(log α)=2 for rational α
(github.com/jdb19937/log-irrationality-measure). That paper explains why
ratios such as log₂3 are out of reach (Baker regime), so it gives no input
for cycles.

**Superseded source assessment:** this review incorrectly concluded that
Wu–Wang proves only μ(log 3) ≤5.1163051 and removed the three-term
theorem attribution. A subsequent primary-source check, recorded below,
confirms that Theorem 1 is precisely the three-term bound. The original
attribution and the historical verification records were correct on that
point. EXPLICIT-LOG-GAP still supplies the explicit cutoff used later.

An independent exact replay (even n=2..14) confirmed EXPLICIT-LOG-GAP's
partial fractions, zero residue at −1, Q_n·B_n integrality, A_n bounds
and A_n log z + B_n(z) = 70J_n, 70(J_n+K_n). The bound implies
μ(log₂3) ≲ 5.2. The claim that no stronger published bound was found is
superseded: Wu–Wang's Theorem 1 implies μ(log₂3) ≤5.1163051. Do not
suggest that the local 5.2 consequence is a new irrationality record.

Barrier, now in EXPLICIT-LOG-GAP §8: the unrestricted 21→12 family has
selection entropy h → 0.26186, so the distinct-factor route needs c < 2.8188,
an effective μ(log₂3) < 3.8188. Do not spend effort shaving c below 4.2.
Neither cycles nor divergence is resolved; the objective remains active.

## 2026-10-08: half-multiplier descent certificate

The previous bounded-depth obstruction led to a positive sufficient
estimate, now kernel checked in `lean/HalfSlopeDescent.lean`.
Let A_t=3^wt(t,n)/2^t. If A_t≥1/2 for t<k, then
`3*2^k*U^k(n)≤3^wt(k,n)*(3*n+2*wt(k,n))`. Each odd step adds
1/(3A_t)≤2/3 to U^t(n)/A_t. At a first half crossing this gives
`U^k(n)≤n/2+wt(k,n)/3`, hence descent if `2*wt(k,n)<3*n`.
The additive terms are included and no first-coefficient-drop claim
is used. Any half crossing K≤n for n>0 implies some descent by K,
by selecting the first crossing and using weight≤K≤n.

`conjecture_of_half_certificate` proves that a convergent base through
N plus such crossings for every n>N would imply full Collatz. Its
universal crossing premise is NOT proved, nor claimed necessary.
Kernel certificates include n=27,k=65,w=40,endpoint10,budget80<81,
and n=1,k=6,w=3,endpoint1, which demonstrates the need for the budget.

`python3 verify_half_slope_descent.py` passes six fresh Lean builds,
all starts 1..32768 and 3,072 CRT-family cases through depth512.
No search exhausts its fuel. Only n=1 fails the odd-step budget in
the interval; none of the family cases fail it. The stronger k≤n
fails at interval starts1,3,7,27,31,41,47,55 and five family cases.
These are exact finite Python checks; they stop at the half crossing,
not necessarily at one. Universal statements and two example
certificates are kernel checked without native evaluation or sorryAx.
Manifest: `results/half-slope-descent/verification.json`; explanation:
APERIODIC section23. No mathematical novelty is asserted.

The universal early-crossing estimate remains the substantive gap.
A universal logarithmic bound would suffice eventually, but is not
known here. Both cycles and divergence remain unresolved; goal active.
Local merge audit: no unmerged index entries, no MERGE_HEAD, no source
conflict markers, and `git diff --check` clean before these additions.
Existing logarithm-note corrections and untracked local files were
preserved. No staging, commits or other Git writes were performed.

## 2026-10-08: source recheck and a first-drop polynomial budget

Previous goal turn was progress: the half-margin theorem, builds and
replay were completed. This turn examined the missing crossing argument.
The current packing and first-passage estimates still permit exponential
escape; no new contradiction from those estimates was established.

A primary-source recheck corrected the intervening literature edit.
Wu–Wang, JNT142 (2014), DOI10.1016/j.jnt.2014.03.007, Theorem1,
DOES bound |p+q1 log2+q2 log3| by H^(-4.1163051-epsilon) beyond an
effective threshold. The publisher's indexed theorem statement was read;
the full proof was not independently formalized. Its log3 irrationality
measure is a corollary, not the paper's entire scope. The earlier
"misattribution" correction was incorrect. MASK-CYCLE-OBSTRUCTIONS,
MASK-TRANSITIONS, MASK-DENSITY, EXPLICIT-LOG-GAP and ATTEMPT now reflect
this, and the superseded memory entry is marked. In particular, the
local 5.2 consequence is not a new irrationality-measure record.
The catalog limitation in EXPLICIT-LOG-GAP is also explicitly phrased
as a limitation of those upper bounds, not of every counting method.

New `lean/FirstSlopeBudget.lean` kernel-proves, for a first coefficient
drop k, w=wt(k,n), A=3^w,D=2^k,G=D-A>0:
`3*D*U^k(n)≤A*(3*n+w)` and descent if `A*w<3*n*G`.
More generally, `A^q<k^p*G^q` and `k^(p+q)≤(3*n)^q` imply descent.
The (p,q)=(21,5) specialization uses `k^26≤(3*n)^5`.
No logarithm theorem is imported as a Lean axiom or proved there.

Written bridge in APERIODIC§24: lambda=log(D/A)≥k^(-21/5) implies
G/A=exp(lambda)-1>lambda and therefore the integer power gap above.
Wu–Wang gives this eventually. EXPLICIT-LOG-GAP supplies the explicit
cutoff k≥10^4000; every first drop k≥5 satisfies its cone
11w≤7k and k<2w (full elementary argument in§24). Thus
n≥k^(26/5)/3 guarantees descent at such a first drop. No existence or
upper-time bound for every start has been proved. This complements the
half-margin criterion; neither is asserted necessary or uniformly stronger.

Kernel example n30913060423816076283,k65,w41 has multiplier about.989,
endpoint30560730293104027237, and passes the exact power criterion.
n27,k59 descends but fails the simpler sufficient gap budget.
`python3 verify_first_slope_budget.py` passes six fresh Lean builds,
all starts1..32768 and969 prescribed near-critical first-drop/lift cases
throughk512. No fuel exhaustion. Gap-budget passes32764 interval starts
(failures1,27,47,63) and968 family cases (failure1). Power certificates
pass13184 and933 respectively. These are finite Python counts, not
universal stopping proofs. Manifest: results/first-slope-budget/verification.json.
All printed kernel dependencies are standard logical axioms; no sorryAx
or native evaluator axiom. The Collatz goal remains unresolved and active.

Concurrent work added the natural-density note recorded below. This
first-drop turn read it but did not independently validate its transfer
of Tao's joint mixing, uniform-start stabilization, or final iteration.
Those analytic steps are a useful next audit target; its finite numerical
checks cannot certify the universal density theorem. Preserve that work
and distinguish its written claim from the kernel results above.

## 2026-10-08: natural-density almost bounded orbits (written)

Jean asked for "project 3": upgrade Tao's log-density theorem to natural
density. docs/NATURAL-DENSITY-ALMOST-BOUNDED.md gives a written proof of
`#{N≤X: Col_min(N)>N₀} ≪ X(log N₀)^(-c)`, hence almost bounded minima
outside a natural-density-zero set. There are two new ingredients:

1. Tao's (74) takes absolute values after conditioning on b_j, so the
   tilt e(θ|a|) drops out (Lemma 2.1). This gives fine-scale mixing
   jointly with |a| (Proposition 2.3), which is his Remark 1.16 route.
2. A renewal lemma for {kβ}, β=log₂3, with weights P(S_k=⌈kβ+τ⌉). It
   uses the local CLT, Erdős–Turán–Koksma, and any finite irrationality
   exponent for β. The constant 1/ln(4/3) matches Tao's log formula.

Uniform starts U_y on [y,2y) replace log-uniform ones, and Tao's Section 3
iteration then runs verbatim.

The original `python3 verify_natural_density.py` run checked three things.
Tilted / product bound ≤ 0.913 for n=2..5. R(τ) was within 4e-4 of
1/ln(4/3) at four tested values above 300, not uniformly for τ≥300.
At x=2^40, the reported TVs compared coarsened Monte Carlo histograms,
not the full passage laws. The later audit below corrects the sampler
and numerical labels. These are sanity checks only; there is no Lean.
Unrefereed 2026 claims of the same upgrade exist, so novelty is not
asserted. Collatz itself remains unresolved, because the zero-density
exceptional set need not be empty. Goal active.

The earlier Wu–Wang "misquote" claim (review II above) is superseded by
the primary-source recheck. Astra's wording in the mask notes stands.

## 2026-10-08: natural-density audit and limiting minima

The previous goal turn was progress: the first-drop certificate and
source correction passed their checks. This turn audited the concurrent
natural-density note against Tao's v7 HTML, especially Sections 3, 5,
6 and 7. The paired conditioning removes the unit-modulus total-sum
tilt; the unnormalised sum slices then pass through the collision bound
and telescoping. No failure of this joint-mixing step was found.

The written note now supplies details needed for uniform-start transfer:
support of c_(n,s) implies 2^s/y≪x^(-.8); the renewal sum is bounded for
every real shift, including negative atypical shifts; and its Gaussian
mass is computed by an integral. The reduced-modulus harmonic bound is
proved with weights 2^(-A)(a_m+1), whose sum is 3. For A>H=.5 log₂x,
the extra term is bounded by 3^(2m)P(S_m>H)≤18^m(3/4)^H=o(1).
This avoids using the nonuniform coarse sum (sqrt(2)+1)^m. The strict
f(N) corollary now uses f/2, and the dyadic cover includes the final
partial block. Formula numbers and a reversed-word notation were fixed.

Proposition 4.1 holds uniformly for every y in [x^α,x^(α²)], not just
the endpoints: all size and renewal-centre estimates are uniform there.
New Section 6 deduces a further WRITTEN result. For fixed B, let
h_B(y)=P(Syr_min(U_y)≤B). For Y≥B^α and Y≤Z≤Y^α,
|h_B(Z)-h_B(Y)|≪(log Y)^(-c). Telescoping along Y^(α^j) makes h_B
Cauchy as y→∞. Dyadic summation and the even-part decomposition give
a natural density d_B for {Col_min≤B}. ND implies d_B→1, so the
differences p_m=d_m-d_(m-1) form a limiting distribution of minima.
This does not establish d_1>0 or d_1=1, and even d_1=1 would not prove
Collatz for every integer. No novelty or kernel verification is claimed.

The verifier now labels floating-point truncation and uncertified
roundoff, and the Monte Carlo TV applies only to the 108 defined bins.
Logarithmic samples are odd from the proposal stage and accepted by
integer rejection; under ideal uniform randomness this is exactly the
1/n law. The earlier sample-then-round-to-odd procedure was not exact.
Every trajectory has 10,000 Syracuse steps of fuel; exhaustion is
recorded as unresolved and fails the check. The rerun passed: 240,000
trajectories, none exhausted, maximum 322 steps; coarse pairwise TVs
0.014667–0.017483 versus same-law 0.015717. Tilt ratios and four renewal
values are unchanged. The numerical tests do not certify the theorem.

Git audit found no unmerged index entries, MERGE_HEAD, or source
conflict markers. Existing changes and the index were preserved; no Git
writes were performed. The OpenAI collection remains methodological
inspiration (APERIODIC§18), not an imported Collatz proof. The full
objective is unresolved and remains active.

## 2026-10-08: total variation, component masses, and a false external axiom

The preceding goal turn was progress: it audited the natural-density
argument and repaired its verifier. This turn checked the route from
that result to individual exceptions. New docs/DENSITY-TO-POINTWISE.md
proves a stronger WRITTEN consequence of the same Proposition 4.1.
If first passage below x is finite, the global orbit minimum equals
the minimum of the passage state. Data processing therefore transfers
stabilisation to the entire law of the minimum, uniformly over all
subsets of possible minima. Telescoping across Y^(α^j) gives a Cauchy
bound O((log Y)^(-c)) in total variation. Finite support at one scale
proves the limiting measure p has total mass one. Dyadic decomposition
and conditioning on ν₂ give the same rate for all starts up to X.
This also proves Theorem ND directly from first-passage stabilisation,
without a separate adaptation of Tao's Section 3 iteration.

Pushing p through the component label π(minimum) gives countably
additive natural densities for coalescence components and their unions.
At least one component has positive density; the union of zero-density
components has density zero. Divergent starts also have a natural
density. None of these densities is evaluated, and p_1>0 or p_1=1
is still unproved. Even assuming p_1=1 yields only X/(log X)^c bad
starts, compatible with the external Krasikov–Lagarias lower bound
X^0.84 for an eligible root's inverse basin. A bound o(X^0.84) for
the ENTIRE bad set would instead rule out every exceptional component.
The primary paper's abstract was rechecked; its computational proof
is not locally replayed. No claimed 0.901 improvement was imported.

A source search encountered AIDoctrine/CollatzLayerA's v8.1 claim of
a complete Lean proof. Its actual source declares odd_steps_certificate
as an axiom: all n≥2^71, n≡3 mod4 have a prefix k≤200 with ≤44 odd
and ≥71 even ordinary steps. This is FALSE. The new standalone
lean/BudgetAxiomAudit.lean uses the source's map/count equations and
kernel checks n=2^111−1=2596148429267413814265248164610047. For all
k≤200 its odd count is ceil(k/2), so the asserted budget never holds.
The witness exceeds even 2^109. Lean also checks it reaches 1 in1476
steps; it is not a Collatz counterexample. Printed dependencies are
only propext/Quot.sound where needed, with no foreign or native axiom.

python3 verify_budget_axiom.py passes a fresh standalone Lean build
and 105 exact finite family instances (L=101..132,201,512,1024;
q=1,3,5 in 2^L*q−1). Only the main witness's full trajectory is
replayed: first arrival1476, peak177bits, no fuel exhaustion. The
foreign repository was not built. Sources, scope and hashes are in
results/budget-axiom-audit/verification.json; explanation is in
docs/BUDGET-AXIOM-AUDIT.md. This excludes an invalid proposed shortcut
while leaving the universal descent problem open.

The user committed the preceding work during this turn; Git status
was rechecked and that new HEAD preserved. No Git writes were made.
The current verified compiler is Lean4.33.1, arm64-apple-darwin24.6.0,
/opt/homebrew/bin/lean, in /Users/jean/Personal/collatz-conjecture--expansion.
The earlier Linux environment entry is historical. Goal remains active
and unresolved; no external-state blocker prevents further research.

## 2026-10-08: user-requested pause and exact resumption point

The user explicitly stopped the research and requested this next task:
"examine a weighted counting approach that would rule out every orbit
staying above a verified finite range, if its required contraction bound
can be proved". The goal service confirms status PAUSED. The full
objective is unchanged and unresolved, not completed or blocked.

The interrupted weighted-counting turn only re-read current files and
searched existing notes. No weighted-counting computation, new theorem,
or kernel proof was completed. Its starting formulation is:

- Use the shortcut map U(n)=n/2 for even n and (3n+1)/2 for odd n.
- Fix a cutoff H for which convergence of every positive n≤H has an
  actual certificate. Let χ_k(n) indicate U^j(n)>H for every 0≤j≤k.
- For s>1 consider the finite weighted mass M_k(s)=Σ_n χ_k(n)n^(-s).
  The intended target is an eventual uniform contraction
  M_(k+1)≤ρ M_k with ρ<1, or another rigorous argument forcing M_k→0.
  Any eternal survivor would contribute its fixed positive weight for
  every k, so such a limit would exclude every survivor above H.
- First derive the exact predecessor identity, retaining the cutoff:
  M_(k+1)=Σ_(y>H) χ_k(y)[(2y)^(-s) +
  1_(y≡2 mod3 and (2y−1)/3>H)·((2y−1)/3)^(-s)].
  The odd-predecessor eligibility and its +1 correction must stay in
  the calculation. This is a proposed starting derivation, not an
  already verified contraction certificate.
- Do not assume residue classes are independent after conditioning on
  survival. Finite horizon estimates or finite experiments alone cannot
  establish the required all-future contraction. Check the existing
  rank obstructions before searching for fixed residue-dependent
  pointwise weights; an aggregate mass estimate is a different claim.

A possible external lead, read only at README level in the preceding
turn, is https://github.com/GettysburgResearch/collatz/blob/main/research/integrated/exceptional-mass/README.md .
It reports failure of a naive one-third weighted residue-share bound
and describes conditional alternatives. Those claims and calculations
have NOT been independently replayed here and are not proof inputs.
Read their exact definitions and source proofs before using them.

Resume from ATTEMPT.md, docs/DENSITY-TO-POINTWISE.md, and the latest
verification records. The density argument's pointwise gap and the
kernel counterexample to the external 200-step axiom remain as recorded
above. Existing local changes and untracked research artifacts were
preserved. No staging, commits, or other Git writes were performed.
All commands started in the interrupted turn had finished; no live
research process was identified at the pause.

## 2026-10-09: weighted survivor mass after resumption

The user resumed the full active goal. The preceding interrupted research
turn had only read files and searched notes; it made no mathematical
progress. This turn took the next safe action from that handoff and
completed the exact weighted-counting investigation below. No claim of
solving Collatz is made, and the goal remains active.

`docs/WEIGHTED-SURVIVORS.md` derives the exact predecessor identity for
`M_k(s)=sum_{tau_H(n)>k}n^(-s)`, keeping the odd-predecessor cutoff and
the factor `(1-1/(2y))^(-s)`. For a certified floor, M_k tending to zero
is equivalent to universal convergence. Define corrected residue mass
Qtilde and `kappa_s=(2^s-1)/3^s`. Nested survival proves the unconditional
strict bound `Qtilde_k/M_k<kappa_s`, but only summable lower bounds for
the relative loss are currently available. The full conjecture is
equivalent to divergence of the sum of these positive bias deficits.

Two WRITTEN implications sharpen the research target:

- An exponential envelope M_k<=C exp(-delta k) is equivalent to a
  universal O(log n) hitting-time bound for this fixed floor. A uniform
  eventual ratio contraction implies it; the converse gives an envelope,
  not necessarily contraction at every step.
- A fixed contraction at infinitely many horizons suffices, even without
  positive frequency. For H64,s3/2 and eligible endpoints y>=98,y=2 mod3,
  `Q_k<=69 M_k/200` at infinitely many k would settle Collatz. Each such
  horizon gives M_(k+1)<.993 M_k. Neither this recurrent bound nor the
  stronger eventual bound has been proved. Finite strict loss alone does
  not establish divergent total relative loss.

A separate WRITTEN all-odd-path argument excludes every pointwise killed
inverse supersolution comparable above and below to n^(-s), even with
arbitrary bounded multiplicative modulation and a non-strict factor one.
This leaves aggregate survivor-mass contraction open.

`lean/WeightedSurvivors.lean` KERNEL checks the exact killed inverse
branches, complete finite inverse-cone membership, the height bound
n<=2^k H, universal survival for n>2^k H, convergence of all positive
n<=64 within71 shortcut steps, the equivalence of full Collatz with
eventual absorption there, and the integer contraction comparisons.
It does not formalize infinite sums, analytic tails, or the all-time
estimate. Two fresh Lean4.33.1 builds pass with no warnings, admitted
proofs, or native evaluator axioms; only standard logical axioms appear.

`python3 verify_weighted_survivors.py` independently reconstructs the
external Mellin note's finite test using integer square roots, a common
denominator2^96, and simple directed integral tails at65536. It constructs
all37 complete inverse cones k0..36; k19 has18847 starts and k36 has
2510783. It certifies 3Q19>M19, refuting the naive one-third ceiling,
while all37 levels satisfy200Qk<69Mk. The largest share is at k34,
with outward decimal enclosure [.34110155,.34110313], checked against
the exact rational endpoints in replay.json. The more detailed printed
decimal values are display approximations, not proof inputs.

The numerical definitions and test were independently reconstructed from
https://github.com/GettysburgResearch/collatz/blob/main/research/astra-three-routes/ROUTE1_MELLIN.md .
No foreign code was run and no external convergence range was assumed.
Independent forward checks cover all n1..2^18 plus4316 larger frontier
members, totaling266460 starts. Sources, scope, logs, exact intervals and hashes are in
`results/weighted-survivors/verification.json`. The infinite-tail integral
inequalities remain written proofs, not kernel-certified analysis.

Next pursue an arithmetic reason that the critical bias deficits cannot
be summable, possibly by proving recurrent separation rather than a
uniform eventual gap. Neither unconditioned residue equidistribution nor
more finite levels establishes that premise. Both nontrivial cycles and
nonperiodic divergence remain unresolved. No staging or commits were
performed; earlier modifications and untracked files were preserved.

## 2026-10-09: backward closure cannot supply the aggregate contraction

The previous goal turn was progress: its source hashes and successful
build records were rechecked. This turn tested whether predecessor
closure, cofiniteness, and known absorption of omitted starts could force
the missing weighted gap. No blocker required user input.

New `docs/WEIGHTED-BASIN-BARRIER.md` gives a WRITTEN obstruction. Let
P A={n>H:U(n) in A}, mu(A)=sum_A n^(-s). For every H>=1,s>1, fixed
k>=0,r>=1 and rho<1 (rho>0), there is a cofinite backward-closed A with
S_T subset A subset S_k for some finite T, yet mu(P^r A)>rho mu(A).
Every omitted positive start provably hits the floor within T steps.
These populations need NOT equal any actual S_j. This does not refute
recurrent contraction along the actual survivor sequence.

The construction first uses K odd steps from x=2^K q-1 to b=3^K q-1.
For a convergent all-index family take a=3^(K-1), b=2^a, q=(b+1)/3^K.
The source then halves to one after reaching b, and x/b<=(2/3)^K.
Its killed ancestor basin B_b consists entirely of convergent starts and
has exact boundary B_b minus P B_b={b}. Hence relative mass loss is at
most(2/3)^(sK), arbitrarily small. The K9 witness uses b=2^6561 and a
6556-bit source, reaching one in6570 shortcut steps; its basin retains
more than.993 of its weight in one step.

For cofiniteness, remove only starts that reach H before hitting b or
[R,infinity). This removed set is finite and has a verified-by-construction
hitting bound R; cycles trapped below R are retained, never labeled
absorbed. The remaining exit set is contained in {b} plus even integers
in[R,2R). Choose R with sum_(n>=R)n^(-s)<=b^(-s). Fixed iterates of P
cost at most powers of Gamma_s=2^(-s)+2^s, so long enough rising prefixes
give the fixed-block obstruction and the sandwich S_(k+R) subset A subset S_k.
This infinite weighted analysis and the huge cofinite construction are
WRITTEN, not full Lean theorems or explicit giant enumerations.

A further WRITTEN restriction rules out every uniform loss profile
mu(A minus P A)>=c*mu(A)^p on this class when1<=p<log_2(3). Use fixed
q=H+2 and arbitrary K, without assuming convergence of that whole family;
the loss/mass^p ratio is at most a constant times(2^p/3)^(sK).
For H64,s=p=3/2,c1, a manageable witness uses K64,q66:
x=1217485108864830406655 and b=226623132139305823987418039892545.
The exact inequality16*x^9<b^6 and the choice R=4*b^3+1 refute that
profile. Both x and b themselves reach one in560 and496 shortcut steps.
No loss estimate with p>=log_2(3) is established or excluded here.

`lean/WeightedBasinBarrier.lean` KERNEL checks the universal basin
boundary/convergence statements, power-of-two nonreturn and convergence,
all-index divisibility3^(k+1) divides2^(3^k)+1, growth paths and ratios,
the K9 parameters and hitting certificate, and the finite power-profile
witness's arithmetic and convergence. The all-index division theorem
uses an elementary polynomial identity, with no external lifting result.
Only standard logical axioms occur; no admitted proofs or native checks.

`python3 verify_weighted_basin_barrier.py` passes four fresh sequential
Lean4.33.1 builds. It independently checks K1..12 arithmetic (largest
source177140 bits), fully replays the first10 trajectory certificates,
and checks the two profile-witness trajectories with first arrivals and
peaks. It builds12 moderate cofinite examples, directly replays49245
removed starts (with repetitions across examples), and makes611343
direct loss-layer membership checks. Every finite exit and five complete
inverse loss layers per example are checked. No trapped positive cycle
was found. The directed mass enclosures reuse the previous written
integral tail bounds; they are not Lean real-analysis proofs.
Manifest: `results/weighted-basin-barrier/verification.json`.

Next investigate information tied to the exact common clock S_k=P^k S_0,
or a weaker state-dependent boundary loss beyond the excluded powers.
Simply extending the static closure argument cannot justify the proposed
uniform gap. No such remaining estimate has been proved; both cycles
and divergence remain unresolved and the full goal is active. Existing
changes and the index were preserved; no staging or commits were made.

## 2026-10-09: finite trajectories give a time-independent entry correction

The goal remains active and unresolved. This turn extended the orbit-packing
argument to finite simple trajectories.
The preceding weighted-survivor and basin manifests were rechecked against
their source hashes; their successful heavy checks were reused.

New `docs/FINITE-PATH-PACKING.md` gives a WRITTEN uniform bound
`#(path values in [a,a+L)) <= 256 L^sigma`, sigma=H_2(log_3 2)<19/20,
for every finite prefix whose states are distinct. The prefix need not be
forward closed, and its later orbit may converge. At scale ell=ceil(log_2 L),
discard at most ell terminal positions. The other ell-step images remain
inside the same prefix and are distinct, so the previous strong induction
applies at each shorter image interval. Its low/high contributions are
less than 128 L^sigma and 64 L^sigma; the terminal cost is at most 2 L^sigma.
This also bounds the distinct value set of every individual orbit, but
does not bound a branching ancestor basin.

Dyadic shells give the WRITTEN estimate sum_(distinct v>=Y)1/v
<8192 Y^(-1/20). The exact integer inequality 32^20<2*31^20 supplies
the loose geometric-series constant. Before finite first entry below Y,
all states are distinct, the final step is even, and the landing y lies
in(Y/2,Y]. If h is the entry time and j the odd count, then
`n=(2^h*y/3^j)*R`, where
`R=product_(odd steps i)(1-1/(2*x_(i+1)))`.
All successors in this product are distinct and above Y. Therefore its
correction sum Lambda is less than epsilon(Y)=4096 Y^(-1/20), and
`1-epsilon(Y)<R<=1`, independently of h. The bound is not for a trajectory
with repeated cycle traversals. The explicit useful margin R>2/3 begins
only at Y>=12288^20; no small-floor numerical improvement is claimed.

For fixed h,y and a source shell[X,2X), sources with R>=1-delta,
0<=delta<=1/3, have the same odd count. Their common uncorrected value
B=2^h*y/3^j is less than 3X, and they lie in [(1-delta)B,B]. Hence their
number is at most 1+3delta X. Combining this with the new correction bound
gives 1+12288 X Y^(-1/20) for each fixed h,y above the explicit threshold.
No union over unbounded times is controlled by that estimate.

`lean/FinitePathPacking.lean` KERNEL checks first-entry distinctness,
terminal-position counts, finite-prefix image membership/injectivity,
local packing transfer, even entry and its landing interval, the integer
odd-count uniqueness implication, and the new constant comparison.
The entropy induction, reciprocal sums, products, real interval counts,
and analytic fibre estimate remain WRITTEN. Four fresh sequential builds
pass, including CollatzPacking, FirstPassagePacking, and PackingExponent.
Only standard logical axioms occur; no native evaluation or admitted proof.

`python3 verify_finite_path_packing.py` checks 18 complete source shells at
floors 1,2,16,64,256,1024: 19,082 starts and 312,115 shortcut steps.
It checks exact rational products/correction sums and 11,494 qualified
fixed-time fibres. There are 199 selected paths, including shortened
prefixes, with 18,417 image checks, 16,708 fixed-weight groups, 3,093 terminal
counts, and 59,802 sampled interval counts. These interval samples do not
prove the all-length packing theorem. The largest qualified fibre in
these shells has 10 sources, at floor 256, shell [2048,4096), time 22,
landing 173 and odd count 11. A separate rising-to-power-of-two witness
has 6,556 source bits and first reaches the floor 2^300 after 6,270 steps;
its product and correction sum were replayed exactly.
Manifest: `results/finite-path-packing/verification.json`.

The elementary fixed-time fibre idea was inspected in Section 4 of the
Shaik first-passage draft at
https://raw.githubusercontent.com/shaikidris/FirstPassageLinearTransport/main/paper/collatz_first_passage_natural_density.md .
The local proof is given in full. No global density claim from that draft
was assumed, no foreign Lean code was executed, and no novelty is claimed.
The functional-operator paper https://arxiv.org/html/2106.11859 was also
inspected: its Hardy-space fixed-point statement does not apply to the
summably weighted survivor indicators. It did not supply the needed gap.

The exact losses S_k minus S_(k+1)=P^k D_0 have a common first-entry time,
with D_0 the even integers in(H,2H]. The new result removes elapsed time
from their relative additive correction, but only controls paths that
enter. It neither forces entry nor proves that these loss layers exhaust
the initial weighted mass. Next work must control the unabsorbed starts
or justify a useful sum over possible entry times; more upper bounds on
already absorbed paths alone do not close this gap. Both cycles and
divergence remain unresolved. No staging or commits were performed.

## 2026-10-09: equal-weight fibres, divergence, and an all-time induction obstruction

The previous turn was progress: the finite-path packing sources and
verification hashes were rechecked unchanged. This continuation sought
constraints on unabsorbed trajectories. No external blocker occurred;
the goal stays active and the full conjecture remains unresolved.

New `lean/EqualWeightFibres.lean` KERNEL proves two integer envelopes.
For y=U^k(n), j=wt(k,n), e=k-j:
`3^j*(n+1) <= 2^k*y+2^j` and
`2^k*(y+1) <= 3^j*(n+2^e)`.
In reverse coordinates z=n+1, odd steps multiply by 2/3, while even
steps send z to 2z-1. The full inverse error lies between
`(2/3)^j*(2^e-1)` and `2^e-1`. Thus fixed k,j,y sources have diameter
at most `(1-(2/3)^j)*(2^e-1)` and cardinality at most 2^e. The cardinality
and uniqueness when e<=1 are kernel checked; these are bounds for every
finite time, not a uniform-in-time constant.

`docs/EQUAL-WEIGHT-FIBRES.md` gives a WRITTEN coefficient-moment consequence.
For s>log_3(2), sum_(U^k(m)=y)(3^wt(k,m)/2^k)^s is at most
`(3/2)^(s*k)/(1-2/3^s)`. All-odd paths to targets varying with k give
the matching exponential rate (3/2)^s. This is a coefficient moment,
not actual m^(-s) weights or a killed survivor contraction. No global
conclusion follows by exchanging those quantities.

Define F_k(n)={m>0:U^k(m)=U^k(n), wt(k,m)=wt(k,n)}. These sets are
nested. The kernel proves the complete endpoint cap
`m <= floor((2^k*U^k(n)+2^wt(k,n))/3^wt(k,n))-1`, and eventual
stabilization if a uniform integer M bounds
`2^k*(U^k(n)+1) <= 3^wt(k,n)*(M+1)`.
The finite-set stabilization proof is general and contains no analytic
or convergence axiom.

WRITTEN divergence bridge: on a nonrepeating orbit, reciprocal summability
gives P_k=product_odd(1+1/(3*x_i)) tending to finite P_inf. Then
C_k=3^wt/2^k=x_k/(n*P_k) tends to infinity, and
B_k=(x_k+1)/C_k tends to L=n*P_inf. B_k is nondecreasing: an odd step
leaves it fixed; an even step adds 1/C_k. Thus B_k<=L supplies the
kernel's boundedness hypothesis and forces F_k(n) eventually constant.
Proving unbounded growth of these particular fibres for every start
would exclude divergence, but no such premise is proved. Maximum fibre
growth at independently chosen targets/weights cannot be substituted.

Also WRITTEN: divergence exists iff some positive start has every
coefficient prefix at least one. For a divergent orbit choose a time
of global minimum of C_k, which exists since C_k tends to infinity.
Conversely such a supercritical start cannot eventually cycle, because
the coefficient around a positive cycle is strictly below one. This
does not prove universal coefficient stopping, and even that statement
would still leave nontrivial cycles to exclude.

Two complete KERNEL examples constrain the search. F_34(1)={1} but
F_35(1)={1,159}; the endpoint caps 132 and 176 make the finite tables
complete for every source. The start 159 reaches one at time 36. Thus a
finite plateau is not evidence of permanent stabilization.
The start 27 reaches one at time 70 yet has no positive smaller
equal-time, equal-weight mate at ANY time. At time 72 all starts 1..27
are in {1,2}, and all smaller starts have a different state/count pair.
Earlier mates would persist to 72; later mates cancel back to 72 because
the map is injective on the standard cycle and cannot erase a count
difference. The kernel proves this all-time cancellation and exclusion.

The WRITTEN classification for convergent starts is by integer arrival
label d(n)=T-2*wt(T,n), with U^T(n)=1. Extra cycles do not change d.
Two convergent starts eventually become equal-time/equal-weight mates
iff their labels agree. Here d(27)=-12, unlike every smaller start.
There are unboundedly many convergent starts with no smaller mate of
this restricted type: each label a>=0 is realized by 2^a; its least
convergent representative has no smaller mate, and distinct labels give
distinct representatives. This all-index corollary is WRITTEN. It
rules out repairing the restricted induction with a larger finite base.
The broader coalescence criterion allowing different clocks/counts is
not refuted, nor is unbounded growth of each entire fibre refuted.

`python3 verify_equal_weight_fibres.py` passes four fresh sequential
Lean 4.33.1 builds with only standard logical axioms and no native
evaluation or admitted proofs. It checks 131,071 canonical residue
envelopes through depth 16, 774 large affine lifts, and 88,573 complete
target residue classes for coefficient moments at exponents 1 and 2
through depth 10. It makes 8,454,144 direct source/time checks in the
source window 1..65536 through time 128 for four tracked fibres. Every
snapshot says whether the endpoint cap makes that window complete.
For example F_76(1) has 1,655 members with complete cap 55,932; later
window counts are not silently called complete. First-one times and
arrival labels are independently replayed for all starts 1..27.
Manifest: `results/equal-weight-fibres/verification.json`.

Next retain the all-source cap and variable odd-count/time information
when seeking useful merges. Requiring a smaller mate with both clock
and odd count unchanged is false even on arbitrarily large convergent
starts. The new necessary stabilization condition does not construct
the missing merges or settle the weighted-loss estimate. Both cycles
and divergence remain open. Source files, existing changes, and the
index were preserved; no staging or commits were performed.

## 2026-10-09: coalescence grades and a conditional odd/even credit rank

The previous turn was progress: all-index equal-weight fibre bounds and
the induction obstruction were proved and recorded. This turn continues
that work; it is not a blocked audit. The full Collatz goal remains active
and unresolved. No sub-agents were used.

New files: `docs/COALESCENCE-GRADES.md`,
`lean/CoalescenceGrades.lean`, `verify_coalescence_grades.py`, and
`results/coalescence-grades/`. The Lean module imports EqualWeightFibres
and CollatzContradiction; earlier verified sources and manifests are
unchanged. All claims below described as kernel have no added axioms,
admitted proofs, or native-decision axiom.

KERNEL: dyadic envelope `2^k*orbit(k,n)<=2^(2*wt(k,n))*n` for n>0.
For any arrival U^T(n)=1 of nonnegative integer grade a=T-2*wt(T,n),
this gives `2^a<=n`. Powers of two realize equality, so the least
convergent representative of grade a>=0 is EXACTLY 2^a. The earlier
nonconstructive unbounded-minima argument is now explicit and kernel
checked: for every a,k and positive m, an equal-time/equal-weight mate
of 2^a at time k satisfies m>=2^a. Increasing a finite base still cannot
repair induction with both restrictions.

KERNEL: the core identity is `k+orbit(k,x)=2*wt(k,x)+x` for x=1 or 2.
Two convergent starts eventually have an equal-time/equal-weight meeting
iff their integer arrival grades agree. For ANY physical meeting
U^a(n)=U^b(m) of convergent starts,
`d(n)-d(m)=a-b-2*(wt(a,n)-wt(b,m))`.
Lean writes this using natural-number cross-sums, with no truncated
negative grades. Every positive m<27 has nonnegative grade, whereas
d(27)=-12. Thus a same-clock meeting of 27 with such m needs at least
six more odd steps on 27's side; an equal-weight meeting needs the
partner's clock at least twelve steps later. Both are sharp:
U^70(27)=U^70(1)=1 with weights 41 and 35;
U^70(27)=U^82(1)=1 with weights 41 and 41.
The complete small table is kernel reduced and the all-time extension
uses the general meeting identity.

KERNEL full equivalences, retaining physical ordinary paths:

- Collatz iff each n>2 has a positive smaller same-clock meeting partner,
  with odd counts unrestricted. Under known convergence, partner 1 or 2
  supplies the phase; 2 must be included in the base.
- Collatz iff each n>1 has a positive smaller equal-weight meeting partner,
  with clocks unrestricted. Under known convergence at time T with j odd
  steps, partner 1 at clock 2j works.

Both reverse implications are strong induction. Neither universal
meeting premise is proved; these equivalences bypass the earlier
restricted-method obstruction without resolving the conjecture.

KERNEL conditional rank: credit A means `2*wt(k,n)<=k+A`, so odd steps
never outnumber even steps by more than A. Remaining credit is
`g=A+k-2*wt(k,n)>=0`. The natural rank
`R(x,g)=2^(g+1)*(x-1)+g` strictly decreases while x>1 and credit remains
nonnegative. On an even step its drop is `2^(g+1)-1`; on an odd step
with g>=1 the drop is `2^(g-1)*(x-3)+1`. Consequently an all-time credit A
implies hitting one by `R(n,A)=2^(A+1)*(n-1)+A` steps. Checking the credit
only through time R(n,A)+1 also suffices. Any hypothetical nonconvergent
positive source must exceed EVERY proposed credit A at some time at most
R(n,A)+1. This applies to both cycles and divergence, with no analytic
packing dependency in its proof.

KERNEL: a certified arrival at time T gives full-orbit credit A=T+1.
Thus convergence of each positive start is equivalent to existence of
a finite credit for that start. This is still an EXACT REFORMULATION,
not the missing proof: using the arrival time to choose A is circular
as a universal convergence strategy. A fixed credit for all sources is
impossible, since `2^K*q-1` with q>0 has K initial odd steps and requires
credit at least K. No universal formula A(n) is proved.

Verification: six fresh sequential Lean 4.33.1 builds passed, with only
standard logical axioms and no warnings. The independent Python census
certifies first arrivals, arrival grades, and minimum FULL-ORBIT credits
for every source 1..2,000,000. This larger range is PYTHON, not a kernel
range theorem. Its lowest grade is -65 and largest minimum credit is 74,
both attained at 1,723,519. The difference matters: credit records the
largest odd excess anywhere along the path, not just at arrival.
Independent direct replay covers sources 1..8192 with 476,621 step checks,
including dyadic envelopes and exact rank drops. At common clock 165,
the grade and state/weight partitions of those 8192 sources coincide
(40 classes, thus 67,108,864 ordered pairs classified by partition equality).
The finite 27 replay checks 900 same-clock meetings and 1185 equal-weight
meetings through clock 128. There are 1024 large all-odd checks with
lengths 1..256 and four positive quotients. These finite scopes do not
imply a universal credit bound.
Manifest: `results/coalescence-grades/verification.json`.

Next: the useful open target is an independently justified finite credit
for EVERY positive source, or a complete relaxed physical-coalescence
selector. The integer rank verifies the consequence of such a bound;
further finite censuses or the grade equivalences alone cannot supply it.
Both nontrivial positive cycles and divergence remain open. Preserve the
index and all existing changes; no staging or commits were performed.

## 2026-10-09: survivor parity bounds and the strength of a credit estimate

The previous goal turn was progress: it added the kernel arrival-grade
classification and conditional credit rank. This turn revalidated all
16 hashes in that manifest before extending the argument. The full
Collatz goal remains active and unresolved; no sub-agents were used.

New files: `docs/PARITY-SURVIVAL.md`, `lean/ParitySurvival.lean`,
`verify_parity_survival.py`, and `results/parity-survival/`.
Earlier verified source files and manifests were preserved. The new
module imports CoalescenceGrades and WeightedSurvivors, reusing the
kernel table that every positive start at most 64 reaches one within
71 shortcut steps. No analytic packing or external theorem is an input.

KERNEL: `AvoidsFloor H k n` means U^i(n)>H for i<k, so the endpoint
may be the first floor entry. A generic induction on an odd-step bound
`2P*U(x)<=Q*x` gives `P^j*2^k*U^k(n)<=Q^j*n`, where j=wt(k,n).
For avoiding one use P=3,Q=10; for avoiding 1..64 use P=65,Q=196.
The exact power comparisons `10^4<3^4*2^7` and
`196^5<65^5*2^8`, together with n<=2^b and positive endpoint, give:

- `4k<=7*wt(k,n)+4b` on prefixes avoiding one;
- `5k<=8*wt(k,n)+5b` on prefixes avoiding 1..64.

The generic power-to-count conversion and both specializations are
kernel checked using only natural-number arithmetic.

KERNEL: put K=4A+5b+1. The SINGLE endpoint condition
`2*wt(K,n)<=K+A` forces an entry into 1..64 by time K-1;
otherwise the second inequality above gives K<=4A+5b, a contradiction.
The certified base then gives an arrival at one by `4A+5b+71`.
This condition does NOT require that credit A held at earlier indices.
In particular, full-orbit credit A now implies this LINEAR bound in A
and b, improving the earlier exponential-in-A bound. The earlier theorem
remains valid; this new module does not change its manifest.

KERNEL: a hypothetical positive counterexample avoids 1..64 forever,
so `5k<=8*wt(k,n)+5b` holds at EVERY clock. In integer terms its excess
D_k=2*wt(k,n)-k satisfies D_k>=(k-5b)/4. Thus each proposed A is exceeded
at the specific clock K=4A+5b+1, stronger than the earlier bounded-time
existence of some excess witness. Both nontrivial cycles and divergent
counterexamples are included. A single sparse prefix satisfying
`8*wt(k,n)+5b<5k` proves ordinary convergence.

WRITTEN consequence: every hypothetical counterexample has lower
limiting odd frequency at least 5/8. Convergent trajectories have limiting
odd frequency 1/2. A universal individual-orbit estimate crossing 5/8
would suffice, but none is proved. Density-one results about source sets
do not supply this pointwise estimate; long parity prefixes also cannot
be counted as uniform independent bits beyond their justified modulus.

KERNEL quantitative implications: a full-orbit credit A<=C*b+D gives
a hitting certificate T<=(4C+5)*b+(4D+71). Conversely a hitting certificate
T<=C*b+D gives credit A=T+1<=C*b+(D+1). Thus, as a WRITTEN interpretation
of these exact formulas with b=ceil(log2 n), uniform O(log n) credit is
equivalent to uniform O(log n) TOTAL stopping time. This changes the next
research action: fitting a logarithmic credit formula is not a weaker
quantitative escape from the strong stopping-time conjecture. The full
ordinary Collatz conjecture alone supplies no such uniform constants.

Verification: eight fresh sequential Lean 4.33.1 builds passed, with
only standard logical axioms, no warnings, no admitted proofs and no
native-decision axiom. Python checks 131,054 positive canonical
source/depth pairs through depth 16; 130,271 avoid one and 115,979 avoid
1..64 over the required prefixes. Independent direct trajectories for
all sources 1..32768 give 2,142,640 index checks. Nine selected sources
produce 260 endpoint tests: 79 valid certificates, 181 failed conditions
on convergent sources, and 52 valid certificates despite an earlier
violation of that same allowance. For example, n=27, A=12, b=5 gives
K=74 and wt=43, so the endpoint condition holds even though the full
orbit's minimum credit is 21. A failed endpoint test is not a
counterexample to convergence.

There are 1024 large all-odd prefix checks through length 256, plus eight
explicit convergent family checks with K=2..9:
a=3^(K-1), q=(2^a+1)/3^K, n=2^K*q-1. They reach 2^a after K odd steps,
then one after a halvings, and have full-orbit credit K. The largest
source has 6556 bits, arrives at one at 6570, and satisfies the new
conditional bound 32887. No convergence of arbitrary all-odd prefix
realizers is inferred. Manifest: `results/parity-survival/verification.json`.

External directions read but NOT adopted as proof inputs: Inselmann's
arXiv:2402.03276v2 states density-one approximation over a logarithmic
time range and explicitly treats uniform logarithmic total time as an
additional hypothesis. The Gettysburg `research/integrated/rank-merging/`
guide and `research/astra-three-routes/pass4/MOVING_GHOST_RANK.md` describe
an input-dependent four-candidate envelope rank; they still have no
universal successful merger selector, and the rank is not globally
decreasing. The Trikoz repository's exposed deep-brake and block-length
scripts are finite random-sample tests, not a pointwise proof used here.
No universal theorem was imported from those claims.

Next: obtain an independently justified parity estimate for EACH
positive orbit, an actual dynamically reusable survivor-mass estimate,
or a complete physical coalescence selector. More conditional bounds
and finite censuses alone will not resolve that obligation. The present
result quantifies the strength of the credit route; it does not prove
its missing premise. Both nontrivial cycles and divergence remain open.
No staging or commits were performed; preserve the user's index.

## 2026-10-09 — All-depth parity-prefix inverse-fibre bound

Substantive progress on the inverse-fibre estimate; no proof or disproof
of Collatz. The active user goal remains unchanged. Files:
`docs/FIBRE-PREFIX-BOUND.md`, `lean/FibrePrefixBound.lean`,
`verify_fibre_prefix_bound.py`, and `results/fibre-prefix-bound/`.
README and ATTEMPT link this follow-up. Earlier source files and manifests
were preserved; their results remain valid.

KERNEL: for same-time, same-weight mates with e=k-j>0, the two shifted
bounds imply m+1<n+2^e. Thus a grid of spacing at least 2^e-1 contains at
most one fibre member. On a grid 3^a*x+r, splitting x by source parity
and mapping x to floor(x/2) gives an even image grid of spacing 3^a,
and an odd image grid of spacing 3^(a+1); each part maps injectively.
The even branch consumes one even step, the odd branch increases a.
Define B(e,a)=1 if 3^a+1>=2^e, otherwise
B(e,a)=B(e-1,a)+B(e,a+1). Both calls decrease e-a. The universal theorem
`grid_fibre_cardinality` bounds ANY finite Nodup index list on this grid
by B(k-j,a). Setting a=r=0 bounds all finite same-time, same-weight
fibres by B(e,0), at every depth and target. The existing endpoint cap
also establishes finiteness of each complete fibre.

KERNEL: B(2,0)=2, so two even steps allow at most two sources. The bound
is sharp at arbitrarily large targets: for every q>=0, 8q+4 and 8q+5
both reach 3q+2 in three steps with odd count one. No all-index exact
maximum is asserted for e>=3. Python recurrence values include
B(6,0)=31, B(10,0)=341, B(16,0)=9389, B(20,0)=80386 and
B(30,0)=18721780. Those numerical evaluations are Python checks; the
applicability of the recurrence is the kernel theorem.

WRITTEN analysis: majorize B by the leaf count L(T) of a binary tree
with children T/2,T/3, stopped at T<=1. Then L(T)<=2*T^delta for T>=1,
where 2^(-delta)+3^(-delta)=1. The base intervals 1<T<=2 and 2<T<=3
have respectively two and three leaves; the defining equation closes
the induction above three. Therefore N(k,j,y)<=2*alpha^e,
alpha=2^delta=1.726541379..., delta=0.787884911... . This improves the
previous 2^e exponential rate. It is not asserted to be optimal.

WRITTEN consequence: the coefficient moment Z(k,s,y), summing
(3^j/2^k)^s over positive k-step preimages of y, is at most
2/(1-alpha/3^s)*(3/2)^(s*k) for s>log_3(alpha)=0.497100032... .
This includes s=1/2. An explicit bound is
Z(k,1/2,y)<=4000*(3/2)^(k/2). The new Lean module kernel checks
1000^24<2^19*579^24, 1000^24<3^19*421^24, and
2^19*2000^24<3^12*1999^24. Written positive-root extraction gives
delta<19/24 and 2^(19/24)/sqrt(3)<1999/2000, establishing the constant.
The real-analysis statements are NOT themselves Lean theorems.

The all-odd affine sources retain the matching uniform-target lower
exponential rate (targets vary with k). A separate WRITTEN averaging
identity over a complete high target interval of length 3^k is
average Z(k,s,y)=((1+3^(s-1))/2^s)^k. Hence a uniform constant times
(3/2)^(s*k) is impossible when s<log_3(3/2)=0.369070246... . The gap
between this obstruction and the proved threshold remains open.

Verification: five fresh sequential Lean 4.33.1 builds passed with only
standard logical axioms, no warnings, no admitted proofs and no native
reduction axiom. Python directly checked all 524287 canonical
source/depth pairs at k=0..18, including the exact shifted error formula.
The separate even-position word algorithm agreed with all 8191
canonical words through depth 12. It enumerated 8215772 additional
selected words with up to 64 odd steps, reconstructed complete maximal
canonical fibres, and directly replayed 3621 witnesses and affine lifts,
including q=2^100+37. These are complete fixed-depth, fixed-weight
maxima for all target classes, not bounds on the supremum over depths.
Nine even steps give maximum 25 at j=7 but 26 at j=8, demonstrating why
an earlier plateau must not be extrapolated.

There are 91392 finite source/depth checks on grids with spacing
3^a for a=0..6 and several small/large offsets, plus eight two-even
sharp-family checks. Exact integer square-root enclosures checked the
moment and combinatorial average over all 29524 target classes at
k=0..9. No floating-point decisions enter these checks. All 14 new
manifest hashes match; the previous equal-weight (13 hashes) and
parity-survival (21 hashes) records also still match.

LIMITATION: this is a coefficient moment whose upper bound GROWS with
k, not actual source-weight mass and not a dynamically reusable killed
survivor contraction. An upper bound on fibre size also does not force
new mates along an individual forward orbit, so conditional fibre
stabilization under divergence is not contradicted. Both nontrivial
positive cycles and divergent positive orbits remain unresolved. No
external theorem or claimed online proof was adopted as an input.

Next research should retain the grid-spacing information while deriving
an estimate for the ACTUAL surviving layers, or obtain a physical
coalescence selector/parity estimate for each source. Improving the
uniform coefficient exponent alone does not close the pointwise gap.
No staging or commits were performed; preserve the user's index.

## 2026-10-09 — Direct exit mass certifies 128 actual survivor horizons

The preceding goal turn was substantive progress: its all-depth kernel
fibre recurrence is valid (all 14 manifest hashes were rechecked). This
turn produced a further finite result for the ACTUAL weighted survivor
sequence, without treating the coefficient moment as a contraction.
Collatz remains unresolved and the full user goal remains active.

New files: `docs/SURVIVOR-EXIT-MASS.md`,
`verify_survivor_exit_mass.py`, `results/survivor-exit-mass/`.
README and ATTEMPT link the result. There are NO new Lean theorems in
this milestone. Previous kernel verification for inverse branches and
floor64 convergence is reused, with hashes checked, not rebuilt or
reclassified. The numerical certification is independent exact Python;
the infinite-sum and integral-tail arguments are written analysis.

For H=64 and s=3/2, let D_k=M_k-M_(k+1) be the weight of the exact
first-entry layer tau_H(n)=k+1. With a finite cutoff R, let P_k(R) be
survivor mass from n<=R and E_k(R) the exit mass from n<=R. Then
M_k<=V_k=P_k(R)+2/sqrt(R), D_k>=E_k(R), and
M_(k+1)/M_k<=1-E_k(R)/V_k. This retains actual time labels and uses
known exit mass; it does not subtract independent unknown-tail errors.
The integer test 1000*exit_lower>=7*mass_upper certifies the full
infinite-mass contraction M_(k+1)<=.993*M_k, without assuming anything
about convergence of n>R.

At R=2000000 and scale 2^96, the exact test passes at ALL k=0..126,
and also k=128: 128 finite successful horizons. The old inverse-cone
replay's sufficient eligible-share bound covered k=0..36. At k=128,
the certified relative-loss lower bound exceeds .00711966. The test
first fails at k=127, with lower bound .0067158801... . That is an
INCONCLUSIVE sufficient test, NOT a refutation of actual contraction.
At k=128 the full mass is enclosed between approximately .0002084957
and .0016227093; its numerator includes only known exits. Decimal
values are explanatory; every decision was made with exact integers.

The Python table gives the FIRST entry into 1..64 for every start
1..2000000. Its maximum time is 335, at 1723519. Table rows use the
format source,first_floor_entry followed by newline; SHA256:
6356252123ad73d8a8c57a2eea7ff5326918aa8da9c0ab5ab8e177f7c4a98277.
A guard failure would stop certification, not assert divergence.

Independent full-trajectory replay covers all starts1..65536 plus
2306 extra samples, including endpoints of all 290 attained time
layers, for 3097900 direct steps. An additional complete certificate
check covers EVERY one of the 1999936 nonbase table rows: follow its
actual path to first return into 1..R and verify that the time label
falls by the excursion length. There are 1666603 immediate returns,
333333 outside excursions, and 3370618 physical steps in these checks.
All intermediate outside states exceed the floor. Induction on the
strictly decreasing nonnegative labels certifies the exact first-entry
times; this full finite certificate is checked in Python, not Lean.

Each n^(-3/2) is enclosed by integer square roots, with its squared
inequalities verified. The unknown tail above R is bounded by the
integral 2/sqrt(R). For a lower mass bound, n>max(R,64*2^k) are known
survivors, giving an integral lower tail from that threshold plus one.
This positive tail can round down to zero at scale2^96 at very large
k; zero is a valid numerical lower bound, not a claim that mass vanishes.
All 37 previous complete inverse-cone mass intervals and 36 exit-mass
intervals overlap the new bounds at shared horizons.

The new six-file manifest matches. The previous weighted-survivor
(seven hashes) and fibre-prefix (14 hashes) verifications still match.
Whitespace and document links were checked. No staging or commits.

The earlier natural-density proof was reread; no new mathematical
correction or extension was established. Its unconditional first-passage
law was NOT assumed to hold after arbitrary survivor conditioning.
No external claimed proof was adopted as an input to this new result.

NEXT: an analytic exit-mass lower bound valid at arbitrarily large
horizons, or a proof that a specified growing cutoff schedule supplies
infinitely many successful tests. A larger finite census by itself
cannot settle this obligation and should not be mistaken for an
infinite extension. The grid-spacing moment still has no established
bridge to this exit lower bound. Both nontrivial cycles and divergent
positive trajectories remain open; the goal is not complete or blocked.

## 2026-10-09 — Cutoff and precision budgets for exit certificates

The preceding goal turn made substantive progress with 128 finite
exit-mass certificates. Their six hashes, the seven weighted-survivor
hashes, and all 14 fibre-prefix hashes were revalidated. This turn
proved a limitation on extending that certificate method. It did NOT
certify additional horizons or prove the missing infinite extension.
The full Collatz goal remains active and unresolved.

New files: `docs/EXIT-CERTIFICATE-BUDGET.md`,
`lean/ExitCertificateBudget.lean`, `verify_exit_certificate_budget.py`,
and `results/exit-certificate-budget/`. README and ATTEMPT link them.
The earlier exit-mass source, document, and manifests are unchanged.

KERNEL: for integer envelopes U(k), exit lower numerators L(k), and
good-index flags, U(k+1)+L(k)<=U(k) and (q+h)*L(k)>=h*U(k) imply
(q+h)*U(k+1)<=q*U(k) at good indices. At all horizons K,
(q+h)^G(K)*U(K)<=q^G(K)*U(0), where G counts good indices below K,
even when they are not consecutive. A retained floor B<=U(K) gives
the same product bound with B. With B>0 and h>0, a separate weaker
kernel bound gives G(K)<=U(0)-B. Seven theorems passed a fresh
standalone Lean build, using only propext and Quot.sound; no native
evaluation or admitted proofs. These are abstract integer theorems,
not Lean theorems about real infinite mass or adaptive source cutoffs.

WRITTEN: for general H>=1, s>1, T(R)=R^(1-s)/(s-1), exact partial
survivor/exit masses P_k(R),E_k(R), and V_k(R)=P_k(R)+T(R),
V_(k+1)=V_k-E_k. For R' >= R, integration proves V_k(R')<=V_k(R),
whereas E_k(R')>=E_k(R). This monotonicity is for EXACT real bounds;
rounded integer envelopes need not be monotone in R. Each implemented
integer success nevertheless implies the exact real test at its R.

For G successful DISTINCT horizons, take R_* as their largest cutoff.
Every success transfers to R_*. Telescoping gives
T(R_*)<=rho^G*V_0(R_*)<=rho^G*T(H), hence
R_*>=H*rho^(-G/(s-1)). At H64,s3/2,rho993/1000 this is
64*1000^(2G)<=R_* *993^(2G). The schedule need not be monotone.
Variable certified losses ell_i obey
sum[-log(1-ell_i)] <= (s-1)*log(R_*/H), also bounding sum ell_i.
A method using a sharper omitted-tail estimate than the entire
power-sum integral would need separate analysis; it is not excluded.

WRITTEN independent precision bound: a successful positive integer
exit numerator is at least one. At the last of G successes,
1/S_*<=D_k<=M_k<=rho^(G-1)*M_0, and M_0<T(H). Thus
S_*>(s-1)*H^(s-1)*rho^(-(G-1)). In this case,
S_*>4*(1000/993)^(G-1). A bounded integer scale cannot provide
infinitely many successes even if source cutoffs grow without limit.
This reasoning uses actual masses; it is written, not kernel checked.

EXACT PYTHON: all 336 saved envelope transitions satisfy
U(k)-U(k+1)=L(k)+known_exit_count, with a constant-tail extension
after the final row. Every prefix satisfies the product theorem's
inequality; all and only the previous 128 successful horizons pass.
At R2000000, B=112045541949572279837463878 and
U0=19729971610812289723786322775. Exact powers allow G736 and
exclude G737. The real adaptive-cutoff bound also excludes G737
whenever every cutoff is <=2000000, at any precision. These are
necessary upper bounds, NOT achievable counts: the existing finite
table already has no exits after first-entry time335, so it has no
possible successful horizon beyond334. For scales <=2^96, exact
powers allow G9276 and exclude G9277, regardless of the cutoff.
The full old trajectory table was reused by hash, not recomputed.

CONSEQUENCE: polynomial cutoffs through K permit at most O(log K)
fixed-factor successful horizons, which still leaves infinitely many
sparse successes possible. If the actual mass has exponential decay,
however, E_k/V_k is eventually below every fixed positive threshold
when R_k is polynomial: E_k<=M_k decays exponentially while V_k
retains a polynomial tail. Failure of such tests would then occur
even though the desired actual decay holds. No actual exponential
decay has been established here.

Scope remains a METHOD LIMITATION, not a Collatz counterexample or
a disproof of eventual contraction. Growing cutoff and scale are
necessary, not sufficient, for an infinite fixed-factor certificate
extension. The exact integer theorem and source records are checked;
the analytic bridge is written. A brief primary-literature search
supplied no new proof input; no online proof claim was adopted.

NEXT: the missing work remains a lower bound on ACTUAL exit mass at
arbitrarily large horizons, or an individual-orbit descent argument.
Do not repeat a fixed-cutoff or fixed-precision census expecting an
infinite conclusion. A polynomial cutoff alone cannot track even a
hypothetically exponential mass decrease with this tail enclosure.
Both nontrivial positive cycles and divergent positive orbits remain
unresolved. No staging or commits; preserve the user's index.

## 2026-10-12 — Actual source weights and the killed operator spectrum

The preceding goal turn was progress: the cutoff/precision budget and
its seven manifest hashes were revalidated, along with all 13 equal-weight
fibre hashes, 14 fibre-prefix hashes and 12 weighted-basin hashes.
The full Collatz goal remains active and unresolved. No sub-agents were
used. This turn did not enlarge a source census or certify new mass
contractions; it addressed the missing conversion from coefficient
weights to actual source weights.

New files: `docs/KILLED-OPERATOR-BOUNDS.md`,
`lean/KilledOperatorBounds.lean`, `verify_killed_operator_bounds.py`,
and `results/killed-operator-bounds/`. README and ATTEMPT link them.
Earlier sources and verification records were preserved.

KERNEL: for y=U^k(n), j=wt(k,n), the shifted envelope implies
`2^k*y <= 3^j*n+3^k`. If `2*3^k<=2^k*y`, then
`2^k*y<=2*3^j*n`. Also `2^k*y<=3^k*(n+1)`, so sources of targets
tending to infinity at a fixed depth escape every bounded interval.
These statements apply even to paths that might repeat above a floor;
there is no unproved distinctness or convergence premise.

KERNEL: for every H,k,B there are x,y>B with a surviving length-k
path above H and `3^k*x<=2^k*y`. Use x=2^k*q-1,y=3^k*q-1 with
q=H+B+2. A separate all-index theorem for K>=7 uses
a=3^(K-1), b=2^a, q=(b+1)/3^K, x=2^K*q-1. The previous divisibility
theorem makes q a positive integer. The path stays above 64 for K steps,
reaches b at K, and reaches one at K+a. Thus the norm-growth witnesses
can all be chosen among provably convergent starts.

WRITTEN: define X_(H,s) by norm sum_(n>H)|f(n)|*n^(-s), s>1, and
K_H f(n)=1_(U(n)>H) f(U(n)), n>H. This is composition on functions,
not forward transport of probability masses. Its kth norm is exactly
sup_(y>H) y^s sum_(U^k(n)=y, tau_H(n)>k) n^(-s).
For y>=2*(3/2)^k, the kernel comparison converts this to at most
2^s times the old coefficient moment. For smaller y, the full summable
source tail bounds it. Consequently
`(3/2)^(s*k) <= ||K_H^k|| <= C_(H,s)*(3/2)^(s*k)`.
At H=64, s=3/2 the constant C can be replaced by5, using the kernel
integer comparisons 8<9 and 25<27. This is an actual-weight norm bound,
but its exponential rate is greater than one.

WRITTEN: at fixed k, every target residue modulo3^k has a coefficient
sum Z_k(r) from the canonical residues a modulo2^k. Along that target
class, actual column masses tend to Z_k(r) as the target tends to
infinity; every finite killing condition eventually disappears.
The essential norm is exactly max_r Z_k(r). Finite column truncations
prove the upper bound. For the lower bound, disjoint image columns
and a Cauchy subsequence of their images under any compact operator
give the matching bound. The proof does NOT assume that normalized
coordinate vectors in l1 are weakly null. The old fibre moment bound
and the all-odd column give
`r_ess(K_H)=r(K_H)=(3/2)^s` by the spectral radius formula.
Thus this space has no gap between spectral and essential spectral
radius; equivalent norms and compact corrections do not repair that.
A different stronger space would need separate justification.

WRITTEN explicit example at H64,s3/2: for the power targets b_K above,
set f(b_K)=(3/4)^K*b_K^(3/2), K>=7, and f=0 elsewhere. Its norm is
2187/4096, but `||K_64^K f|| >= (243/128)^(K/2)`, tending to infinity.
For every fixed n, K_64^k f(n) is nevertheless eventually zero: if
the orbit ever hits the support it reaches a power of two and then
the floor; otherwise all values are zero. Every contributing source
converges. The real infinite function and its norm are written; the
support paths and cubic ratio inequality are kernel checked.

VERIFICATION: nine dependency/final modules passed sequential Lean
4.33.1 builds in this turn. The final replay reused the first eight
after matching source/log/olean hashes and freshly built the new
module, which prints ten theorem dependencies. Only standard logical
axioms occur; no admitted proof, native reduction axiom or warnings.
Default reproduction makes all nine builds fresh.

Exact Python checks cover 32767 canonical sources through depth 14,
98301 large affine lifts, 90939 qualified high-target comparisons,
and 159056 source-escape implications. At depths 0..12 and floors 1,64,256,
5211 complete killed fibres (43886 members) agree between inverse
branching and independent canonical lifting. Actual power3/2 column
bounds use integer square roots at scale 2^112. There are 144 coefficient
limit checks in selected complete target classes; 48 large-target
intervals certify relative discrepancy below 2^(-70). These finite
checks do not prove the infinite spectral argument.

There are 771 all-odd column witnesses through k=256 and 98688 direct
steps, plus six convergent power-target witnesses K=7..12. Their first
four pure-halving suffixes are fully replayed (29160 steps); the last
two use the exact power-of-two endpoint and the reused kernel power
hitting identity. The largest source has 177140 bits. All 25 hashes in
the new manifest match. No external Collatz theorem is a proof input.
Standard infinite-sum and Banach-algebra facts remain written analysis.

A primary-source renewal paper was inspected at
https://arxiv.org/html/2606.27488v1 . Its Section 2 hypotheses assume
the requisite killed induced contraction/renewal bounds; no such
bound for Collatz was imported. The Gettysburg exceptional-mass guide
likewise retains a survivor-specific hypothesis. Neither supplies the
missing estimate for the actual constant-vector orbit.

The old external predecessor-density audit's progress file still says
running, but an authorized process-list inspection on 2026-10-12 found
no live Lean/lake or collatz-density audit process. It has 121 recorded
successful modules out of 389, with no completed theorem audit. Its
existing progress changes and untracked logs were left intact; it was
not restarted and no result from it was adopted.

NEXT: focus on the specific bounded functions K_H^k(1), or prove a
usable regularity condition preserved along that orbit. Global operator
contraction on X_(H,s) or an equivalent renorming cannot work. Removing
finitely many target columns does not remove the obstruction. The scalar survivor masses remain nonincreasing
and may still vanish; the norm-growth theorem neither proves nor
refutes this. No nontrivial cycle or divergent orbit has been found.
No staging, commits, or other Git writes were performed.

## 2026-10-12: authenticated predecessor-density source and resumed replay

The universal proof/disproof goal remains active, with no token budget.
No complete proof or positive counterexample was found. No blocker was
declared. This entry concerns an external result under verification,
not an adopted theorem or a completed Collatz proof.

The public Mazur predecessor-density claim and formalization were read:
https://www.proofatlas.ai/proofs/artifact.collatz.predecessors_positive_lower_density.v001.html
https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/
The public roots assert positive lower natural density for predecessors
of each fixed positive target not divisible by three, amplification of
any positive counterexample to a positive-lower-density nonconvergent
set, and universal convergence conditional on upper-density-one
convergence. That last density-one premise is not proved.

Source semantics were inspected directly: the ordinary map is even n/2,
odd 3n+1; Reaches means existence of an iterate, including zero steps;
predecessor sets contain positive starts; natCount counts distinct n<X.
The target-dependent constants need not be uniform. A static scan found
no custom axioms, sorry/admit, native_decide, unsafe declarations, kernel
bypass options, or environment mutation. The only run_cmd traverses and
reports public theorem dependencies in Verification.ReleaseAudit.
These inspections are not substitutes for the pending kernel replay.

New `verify_predecessor_density_archives.py` authenticated both published
ZIP hashes and compared all 404 assembled files byte for byte against
archive members. The Lean sources are 377 baseline modules plus 12
companion modules (10 support/implementation modules, public interface,
and release audit). The public interface closure has 388 modules, the
whole replay 389. Record:
`results/predecessor-density-review/archive-authentication.json`.
Baseline `/private/tmp/collatz-positive-density-baseline.zip`:
914975 bytes, SHA256
23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f.
Companion `/private/tmp/collatz-predecessor-density-source.zip`:
55103 bytes, SHA256
55ceb4df0cca17ae728dc65b30bf5077000e1b47f2dc322454eea9f637ac75b3.
The separately downloaded `collatz-positive-density-source.zip` is an
older/differently packaged checked source and is NOT the pinned slim
baseline archive for this replay; do not substitute it.

The stale replay was confirmed not live with an authorized process-list
inspection. All 121 existing source/log/olean hashes matched; there
were exactly 121 project objects and no unrecorded project objects.
`verify_predecessor_density_source.py` now has `--resume`: it checks
the exact topological successful prefix, all those hashes, compiler
commands, toolchain, pinned dependency revisions, and absence of extra
project objects. It uses atomic progress writes, a per-assembly flock,
and records each resumed session's prior progress and verifier hashes.

The replay was actually launched, sequentially with one Lean worker,
at 2026-10-12 13:47:45 UTC. As of the latest poll while writing this
entry, 133/389 modules had passed; the current module was
`Erdos1135.Tao.Fourier.Lemma74CanonicalClaimStar`. This number will grow:
read `results/predecessor-density-review/progress.json` for the current
state. No compiler failure has occurred in this resumed run so far.
The runner PID is 65674 and the unified tool session is 93435; prefer
polling that session, then inspect live processes if it is unavailable.
Do not launch another replay while this one is running.

Assembled tree: `/private/tmp/collatz-density-audit/assembled`.
Assembly SHA256:
9da50833f18f8427523da5cd89ff4a0dbf1198fe09a9a4acccf4583898ac2ec3.
Compiler: Lean4.30.0-rc2, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc.
Pinned official third-party compiled libraries are reused; they are
not rebuilt from source and no independent Lean checker is being run.
The verifier writes `verification.json` only after all 389 modules
pass and all three public root axiom reports contain exactly propext,
Classical.choice, Quot.sound. A status of running with a dead process
is not success. If interrupted, first establish that no audit is live,
then use:
`python3 verify_predecessor_density_source.py /private/tmp/collatz-density-audit/assembled --resume`.

New `docs/PREDECESSOR-DENSITY-REVIEW.md` records the exact statements,
provenance, pending scope, and conditional connection to the written
minimum law. Assuming both the external PLD theorem and that law,
universal convergence is equivalent to p_1=1, with no improved error
rate required; p_1>0 follows from PLD at target1. Every coalescence
component would have positive density, not merely some component.
This does not prove there is only one component or establish p_1=1.
ATTEMPT, README, and the older DENSITY-TO-POINTWISE note now link this
pending review without adopting the external theorem prematurely.

A notation typo in the killed-operator note's introduction was fixed
(stray commas in two exponents). Its manifest records the old/new
document hash and reuse of the unchanged Lean/Python evidence. All
25 manifest hashes matched afterward; no heavy replay was repeated.

NEXT: continue the existing external replay, inspect all three public
statements/axioms after completion, and update the review's status only
if the whole check passes. Then the remaining density route is to
prove p_1=1, not to seek a faster rate assuming it. Until completion,
PLD remains a conditional external input in this project. The actual
weighted survivor functions remain another possible direction; whole
operator contraction on the previous space is ruled out. Preserve the
index and user changes. No staging, commits, or Git writes were done.

## 2026-10-12: completed predecessor-density audit and fixed-target densities

The universal proof/disproof goal remains active, with no token budget.
No complete proof or positive counterexample was found. No blocker was
declared. This entry supersedes the preceding entry's pending replay
status. The audit processes have finished; sessions 93435 and 11119 are
not live work to resume.

### Completed external Lean replay

The source replay completed all 389 modules: the previously validated
121-module prefix plus 268 further successful compilations, including
CollatzPredecessorDensity and Verification.ReleaseAudit. The accumulated
compiler time in the module records is 3536.928 seconds. All return codes
are zero. The three public roots use exactly propext, Classical.choice,
and Quot.sound. Their printed types were read and match the ordinary
positive-integer predecessor-density and conditional convergence claims.
The release audit enumerates 4717 project declarations in their combined
dependency closure and rejects an imported unproved universal Collatz
declaration. Linter/deprecation warnings are present, without proof
admissions or extra axioms.

After all Lean compilations passed, the Python script initially exited 1
because it parsed only the first line of a wrapped axiom list. The actual
multiline lists all contained the three standard axioms. The parser now
reads complete bracketed blocks. Two valid formats were accepted, and
seven invalid cases were rejected: sorry axiom, native reduction axiom,
extra custom axiom, missing root, duplicate root, wrong root name, and
missing standard axiom. Record:
`results/predecessor-density-review/axiom-parser-check.json`.
This was a report-formatting failure, not a Lean proof failure.

The final `--resume` validated all 389 source/log/olean records and exact
compiler commands, toolchain, manifest, and dependency revisions. It
compiled zero modules, then passed the corrected final gate at
2026-10-12T14:44:35.318300+00:00. The final record is
`results/predecessor-density-review/verification.json`, SHA256
fa39ce531d0cf5d3e6f11f8de159a50709bca37536bea7762e2c5d22562e3582.
`progress.json` also says passed. Verifier SHA256:
0359ff5a2f5aa4882e32f964160b775619b9211c67116ef80d303529f31376ad.
ReleaseAudit log SHA256:
943c598e4bf3d55f6ce45ce4a01c75249d2b76ff488e54df0b91992773a798a7.
The two resume sessions preserve the prior-progress hashes. The parser
record separately preserves the initial post-build failure provenance.

The authenticated assembly and archive hashes are those in the preceding
entry. The compiler was Lean4.30.0-rc2, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc. Pinned official third-party
compiled libraries were reused; they were not rebuilt from source and
no independent kernel implementation was used. Within that stated scope,
the external PLD theorem is now adopted as an independently replayed
proof input. This is separate from the local standalone Lean4.33.1 work.

For each fixed positive target a with 3 not dividing a, PLD says that
the distinct positive starts whose ordinary Collatz orbit reaches a have
positive lower natural density. Its constants depend on a. A positive
counterexample therefore forces the entire nonconvergent set to have
positive lower natural density. Upper natural density one of convergence
would exclude every counterexample, both a nontrivial cycle and a
divergent orbit. The upper-density-one premise is not proved.

`docs/PREDECESSOR-DENSITY-REVIEW.md`, ATTEMPT, README, and the current
density-to-pointwise note have been updated to this completed scope.
Historical memory entries remain unchanged. Under the separate written
minimum law, PLD gives p_1>0 and makes p_1=1 sufficient without a faster
error rate. The older X^0.84 comparison alone had needed more; that rate
requirement is superseded by the linear predecessor lower bound.

### New written deductions and their limits

`docs/DENSITY-TO-POINTWISE.md` now includes:

- From the written uniform first-passage Proposition 4.1, every finite
  odd-target visitation profile has a limiting law. Thus every fixed odd
  target a has a natural predecessor density r_a.
- Summing the written finite-orbit packing bound over a finite target
  interval and then taking densities gives sum r_a <= 256 L^sigma over
  odd targets, with sigma=H_2(log_3 2)<19/20. In particular no uniform
  positive lower bound over all eligible targets is possible.
- Along a forward Syracuse orbit a_j, r_(a_j) increases to the density
  lambda of its coalescence component. This uses tightness of the written
  minimum law: the finitely many possible minima <=B eventually merge
  with a_j, and the minimum-law tail tends to zero. It does not assume
  arbitrary countable additivity of natural density.
- A separate coarse overshoot estimate extends the profile result to
  every positive target, including even targets. With alpha=1.001 and
  n0=floor(log_2(x)/10), Tao Proposition 1.9 and Chernoff give
  19n0/10 <= S <= 3n0 except on an O(x^(-c)) event. The affine formula
  gives entry by n0, because 3^5<2^8 and
  alpha^2-3/100=972001/1000000<1. The last valuation is <=3n0, so the
  odd landing exceeds x^(7/10). For x^(7/10)>max A no target in a finite
  set A is visited in the prior ordinary halving segments. The added
  error is summable in the same scale telescope. Initial halving of an
  even source changes a profile for only O_A(log X) starts up to X.
- Every ordinary orbit value lies in V union 2V for the shortcut value
  set V. Thus sum r_a <=512 L^sigma over all positive targets in a
  length-L interval. The forward-density limit extends to ordinary
  orbits as well. Targets divisible by three have only repeated-doubling
  predecessors and density zero. PLD makes all other r_a positive.

All of these new conclusions are written analysis, not new Lean or
native certificates. The older odd-target proof alone still does not
handle even targets; Section 5 explicitly supplies the additional bound.
The record `results/density-to-pointwise/written-review.json` contains
12 source/evidence hashes and the exact dependency distinctions. The
prior natural-density manifest's 2 hashes and finite-path-packing
manifest's 12 hashes were checked; no old numerical or Lean suite was
rerun unnecessarily. The natural-density numerical checks remain only
floating-point and Monte Carlo sanity checks.

The written first-passage argument was reread against Tao arXiv v7,
https://arxiv.org/html/1909.03562v7 (July 2026). The paired-sum Fourier
tilt, weighted submeasure mixing, renewal mass 1/(2-log_2 3), and harmonic
sum bounds were rechecked. The shifted renewal parameter has the factor
2*m0*(2-log_2 3), correctly accounting for the E-prime scale; do not
replace it by a single m0. No new analytic gap was found in that review,
but this does not turn the written adaptation into a kernel proof.

NEXT: the density route needs p_1=1, not merely positivity or existence
of density. A divergent component would have lambda>0 and r_(a_j)
increasing to lambda along its unbounded forward orbit. A bound forcing
these particular densities to tend to zero would exclude divergence,
but the summed target-interval bound does not supply it: a sparse orbit
is compatible with that bound. Nontrivial cycles also remain open.
The actual bounded weighted survivor functions remain another route;
global contraction on the previously studied weighted space is already
ruled out. No staging, commits, or Git writes were performed.

## 2026-10-12: first-passage atoms and density flow inside a fixed basin

The full proof/disproof goal remains active and unresolved. The preceding
turn was progress: it completed the external 389-module proof replay and
added written fixed-target density results. This turn strengthens the
density argument, without finding a complete proof or counterexample.
There is no blocker and no live compiler left to poll at the end of this
entry. The completed verifier session was 88164.

New `docs/PREDECESSOR-DENSITY-FLOW.md` proves, under the written uniform
first-passage Proposition 4.1 and its early-valuation estimates, that

  for each fixed a>0, sup {r_b : b>R and b reaches a} tends to zero
  as R tends to infinity.

Here r_b is the already established written natural density of the
ordinary predecessor basin P_b. The threshold depends on the fixed root
and finite first-hit paths. It is not a bound uniform over all targets
or all roots. The proof has three steps:

1. At most 2^(k+1)-1 distinct positive starts can hit any fixed positive
   target by k shortcut steps. This is now kernel checked for all k and
   all targets, using an exact list of inverse predecessors. No factor
   depending on the target's magnitude is present.
2. For each fixed floor x, F_x(n)=SyracusePass_x(oddpart(n)), including
   an infinity mark, has a limiting law nu_x for uniform positive starts.
   The exact identity F_x(n)=F_x(Pass_u(n)) for u>=x allows the same
   scale telescope. Its error at an odd source scale Y>=x^alpha is
   O((log Y)^(-c)). On the early-valuation good event at Y=x^alpha,
   T_x<=n0 and total valuation <=3n0, so entry uses <=3n0 shortcut steps.
   The finite fibre bound makes every atom of that base passage law
   O(x^(-c)). Thus max_z nu_x({z})=O((log x)^(-c)), including infinity.
3. Fix a, choose a large x>=a, and if a is periodic include its whole
   finite cycle below x. Let Q_x be the finite union of paths from each
   z<=x that actually reaches a, stopped at its first hit of a. It does
   not assume that all z reach a. If b in P_a lies above max Q_x, no
   source reaching b can visit any z<=x before b; otherwise that retained
   path would contain b. Nor can it visit a before b, since b is outside
   a's cycle. Therefore P_b is contained in one atom of F_x, namely
   F_x(b). This gives r_b<=max_z nu_x({z}), proving the fixed-basin limit.

The new limit applies to every simple infinite inverse chain and in
particular to the doubling ray: r_(2^j a)->0 for each fixed a. This
removes the explicit remainder from a finite branch partition. For a
nonperiodic ordinary root,

  r_a = r_(2a) + 1_(a mod 6 = 4) r_((a-1)/3).

For an odd nonperiodic a, telescope along its doubling chain:

  r_a = r_(2^K a) + sum_(1<=k<K, 3 divides 2^k a-1) r_((2^k a-1)/3).

Letting K tend to infinity now proves the countable inverse Syracuse
flow identity, with no assumed interchange of a density limit and an
arbitrary infinite union. Nonperiodicity is essential: the ordinary
root 4 has parents 8 and 1 whose basins overlap (witness start 8), and
the Syracuse self-parent 1 cannot precede a first hit of 1.

New `lean/BoundedHitFibres.lean` has twelve checked theorems. In addition
to the finite fibre bound and exact inverse-list membership, it proves
first-hit uniqueness/recursion, uniqueness of hit times at a nonperiodic
ordinary root, disjointness of distinct immediate predecessor basins
there, ordinary predecessor arithmetic, and the one-step decomposition.
These use only propext, Classical.choice, Quot.sound (some use a subset),
with no native evaluation, sorry, warnings, or extra axioms in the final
build. Compiler: the local Lean4.33.1 at commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

New `verify_predecessor_flow.py` accepts optional --reuse-build-dir. In
the completed run it copied three dependency objects from
`/tmp/collatz-killed-operator-build` only after checking compiler version,
source/object/log hashes, and successful records. The new module was
compiled afresh, in an isolated temporary directory. The older cache has
no compilation command fields, so reused records use null for that field
rather than inventing executed commands. Default reproduction rebuilds
all four modules sequentially. No external PLD modules were rebuilt.

The independent Python replay passed these exact finite scopes:

- 288 complete bounded-time fibres: targets 1..32, depths 0..8; 135168
  forward-simulated sources, using the earlier kernel inequality
  n<=2^k U^k(n) for a complete source bound.
- 4096 ordinary trajectories followed through their first repeated
  state, all ending in the known cycle; 311850 ordinary steps.
- 47463 terminal halving marks, 1298432 doubling-tail identities,
  and 491520 finite inverse-branch partitions.
- 89680 finite-basin first-passage transport checks, using retained
  first-hit paths at roots 1,5,27 and floors 32,64,128.

Records: `results/predecessor-density-flow/verification.json` and
`results/predecessor-density-flow/replay.json`, plus four Lean logs.
The density-law arguments and infinite branch sum are written analysis;
the finite checks do not prove those limiting statements. PLD is used
only for positivity and the comparison with a hypothetical divergent
component, and retains the preceding entry's external trust scope.
The preceding written-review record's 12 dependency hashes were checked;
its DENSITY-TO-POINTWISE hash was updated with explicit provenance for
the appended follow-up link, while Sections 1-5 and their evidence were
left unchanged. ATTEMPT and README now link the new result.

NEXT: (fixed-basin decay) and (r_(a_j) increasing to lambda>0 along a
divergent forward orbit) do not contradict one another. Later a_j leave
every earlier P_(a_J), since a return would create a cycle. Changing the
root with j loses the fixed-basin threshold. The next density question
is what additional control on moving targets or conditional first-passage
laws could bridge that distinction. A weaker statistical reformulation
alone would not prove p_1=1. Nontrivial cycles and divergent orbits both
remain unexcluded. No staging, commits, or Git writes were performed.

## 2026-10-12: approximation uniform over every predecessor target

The full proof/disproof goal remains active and unresolved. There is no
blocker or live compiler to resume. The completed verifier session was
41536; its final record reports passed at
2026-10-12T15:52:39.109292+00:00. No positive counterexample was found.

New `docs/UNIFORM-PREDECESSOR-APPROXIMATION.md` proves, conditional on
the earlier written uniform first-passage estimates, that

  sup_(a>=1) |R_X(a)-r_a| = O((log X)^(-c)),
  R_X(a) = #{1<=n<=X: n reaches a}/floor(X).

This constructs the limits directly and strengthens the earlier
fixed-target density statement. The constants are independent of a, so
targets may vary with X. The result does not assert that r_a is small
when a varies. It is uniform convergence of the target-indexed function,
not total variation convergence of whole orbit-value sets.

The exact argument works for any passage predicate. Let F_H(n) be the
first ordinary odd state <=H, or infinity if no entry occurs. If n
reaches a, either the landing itself reaches a or F_H(n)=F_H(a). Thus
for any source law with passage law q,

  0 <= P(n reaches a) - sum_(odd b<=H) q(b) 1_(b reaches a)
    <= q(F_H(a)) <= maxatom(q).

This includes even and cyclic targets and nonentry. It assumes no
independence between landing and future behavior. The earlier flow
note's Section 2 supplies nu_H, with TV error O((log Y)^(-c)) for odd
source intervals [Y,2Y), Y>=H^alpha, alpha=1.001, and maximum atom
delta_H=O((log H)^(-c)), including infinity. Choosing H=floor(Y^(1/alpha))
gives a target-uniform Cauchy estimate for every larger source scale Z.
Dyadic mixing and initial valuations transfer it to positive sources.
The initial-halving discrepancy for any single target lies among the
starts 2^j a and is bounded uniformly by 1+floor(log_2 X) counts.

For each fixed H this also gives the finite-mixture formula

  0 <= r_a - sum_(odd b<=H) nu_H(b) 1_(b reaches a)
    <= nu_H(F_H(a)) <= delta_H, uniformly in a.

The mixture retains the actual seed orbits. Certifying all seeds up to
one tested floor gives a bound outside their finite orbit union, but
does not certify arbitrarily large floors or yield a numerical analytic
error constant. No general decay along divergent orbits follows.

New `lean/PassageApproximation.lean` imports only CollatzContradiction.
It constructs a noncomputable first-passage mark and checks eleven
theorems: first-entry existence and uniqueness; finite/nonentry mark
characterizations; reachability transitivity; suffix transport; nonentry
after a hit; landing-hit inclusion; the passage comparison; early-hit
mark equality; and its odd-floor specialization. Standard axioms only
(propext, Classical.choice, Quot.sound, or subsets), without sorry,
native evaluation, extra axioms, or warnings. The analytic convergence
and rates are not Lean theorems. The noncomputable mark does not decide
whether an arbitrary orbit ever enters.

New `verify_uniform_predecessor_approximation.py` compiled the new module
afresh with Lean4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, in an isolated temporary
directory. Only CollatzContradiction was reused from the validated
`/tmp/collatz-killed-operator-build` cache, checking compiler version and
source, object, and log hashes. Default reproduction builds both modules
sequentially. No external PLD modules were rebuilt.

The independent exact Python replay followed all 2048 original source
orbits through their first repeat, obtaining a closed universe of 4457
reachable targets (maximum value 1276936). It checked source cutoffs
32,128,512,2048 and ten predicates, including empty and partial-entry
sets. Across those 40 population/predicate comparisons it passed:

- 17828 initial-halving target bounds;
- 27200 landing-orbit inclusion checks;
- 1469630 early-hit passage-mark equalities;
- 178280 target histogram comparisons.

Both finite-population target vectors vanish outside the complete closed
universe, so those comparisons cover every possible target for the
represented populations. This is a finite replay, not an asymptotic or
universal convergence certificate. Records and two Lean logs are under
`results/uniform-predecessor-approximation/`; the verification record
has 11 dependency hashes. It also revalidated all 14 hashes in the
preceding flow record and all 12 in the density written-review record.
README and ATTEMPT link the new result; prior analytic notes and their
records were not modified in this turn.

NEXT: uniformity alone does not bridge the remaining gap. In a hypothetical
divergent component of density lambda>0, choose a forward target a_(j_X)
beyond all meeting points of its finitely many starts <=X and with
a_(j_X)>X. Then R_X(a_(j_X)) equals that component's proportion up to X,
so both it and r_(a_(j_X)) can tend to lambda. First-passage uniformity
therefore supplies no smallness at such targets. A separate estimate
must rule out the possible divergent seed orbits in the finite mixture,
or establish r_1=p_1=1; nontrivial cycles also remain unexcluded.
No staging, commits, or Git writes were performed.

## 2026-10-12: unused branch mass and the reciprocal-density barrier

The full proof/disproof goal remains active and unresolved. The previous
turn was progress: its passage comparison and uniform-density deduction
were saved and verified within their stated scopes. This turn examined
whether the inverse density flow could force mass toward a finite cycle.
No complete proof, positive counterexample, or external blocker was found.

New `docs/DENSITY-BRANCH-LEAKAGE.md` makes the remaining density comparison
precise. On a hypothetical divergent Syracuse orbit b_j, discard the first
state if needed so that all b_j are odd and not divisible by three. Put
v_j=3b_j+1 and u_j=2v_j. The exact nonperiodic parent partition gives
r_(v_j)=r_(b_j)+r_(u_j); the following halving segment can add further
branches, so r_(b_(j+1))>=r_(b_j)+r_(u_j). All these densities are positive
by the already replayed external PLD theorem. Since r_(b_j) increases to
the component density lambda, the written consequences are

  sum_j r_(u_j) <= lambda-r_(b_0),
  sum_j rho_j <= (lambda-r_(b_0))/r_(b_0),
  product_(j<N)(1+rho_j) <= lambda/r_(b_0),
  rho_j = r_(u_j)/r_(b_j).

Thus a divergent component would require summable relative increases.
A bound rho(b)>=kappa/(1+log b), for all sufficiently large nonperiodic
odd b not divisible by three, would exclude divergence: Syr(b)<=2b
gives log b_j<=log b_0+j log 2, making those contributions nonsummable.
The bound is not proved. In particular divergence would force
liminf_j (1+log b_j) rho_j=0. This condition does not address cycles,
where the nonperiodic parent partition fails.

The finite-path packing bound supplies an obstruction to a tempting
weaker route. With sigma=H_2(log_3 2)<19/20 and s>sigma,

  sum_(j: b_j>=R) b_j^(-s)
    <= 256 R^(sigma-s)/(1-2^(sigma-s))  (integer R>=1).

This is a dyadic sum of the existing bound for distinct orbit values,
valid on any hypothetical divergent orbit. In particular sum_j 1/u_j is
finite. Even granting a target-uniform absolute lower bound r_a>=c/a
would therefore give only summable lower contributions at unused branches.
A scalar sequence d_(j+1)=d_j+c/u_j stays bounded on a sufficiently late
tail, illustrating that these inequalities alone do not contradict one
another. That sequence is not an actual Collatz density construction.
The same summability issue affects relative polynomial bounds with an
exponent s>sigma. A nonsummable cumulative relative estimate is needed.

A current primary-source search found and inspected Renato Augusto
Tavares, arXiv:2608.27617v1 (27 August 2026),
`https://arxiv.org/html/2608.27617`, on Wirsching's predecessor-density
program. It describes the c/a lower bound as the program's target and
leaves its condition (star 3), approached by Conjecture 2, open. Its new
theorems were not adopted as inputs or replayed here. Even the proposed
stronger lower bound would not close the above summation argument.
The existing written joint-mixing adaptation was also reread; no new
gap or new verification claim resulted, and those sources were unchanged.

New `verify_density_branch_leakage.py` builds the complete ordinary
forward graph of sources 1..524288, then aggregates distinct-source
weights through its acyclic part. The only remaining cycle is {1,2,4}.
The graph contains 1137753 vertices, maximum value 24648077896. A separate
direct replay for all starts 1..4096 took 311850 ordinary steps and
matched all 1137753 graph target counts, including zeros. The exact
parent partition was checked for all 1137750 noncycle vertices at
cutoffs 4096,8192,65536,524288: 4551000 checks in total.

The fixed example b=3077, v=9232, u=18464 has counts at X=524288:
206048 used-branch sources, 39 unused-branch sources, and 206088 sources
reaching v (including v itself). The exact finite ratio is 39/206048,
below 1/1000. At X=65536 the two branch counts are 25511 and 6; at
X=8192 they are 3263 and 0. The example converges. These observations
show finite branch imbalance, not an asymptotic upper bound on r_u/r_b,
nor a disproof of every possible logarithmic balance constant.

Verifier session 80826 finished successfully; the final record is
`results/density-branch-leakage/verification.json`, dated
2026-10-12T16:18:31.609227+00:00, with 11 dependency hashes. It revalidated
the preceding flow, uniform approximation, and finite-path packing
records (14,11,12 hashes respectively). No new Lean theorem or Lean
compilation is claimed. The old nonperiodic partition supplies the
kernel input; density limits, the logarithmic criterion, and the
summability argument remain written deductions. There is no live
process to resume. README and ATTEMPT now link this audit.

NEXT: an absolute predecessor-density improvement alone is not the
missing step. Investigate arithmetic or conditional information that
forces a nonsummable total of relative unused-branch masses, or a
different direct route to r_1=1. Do not replace actual natural-density
ratios by the recorded finite ratios without error bounds. Divergent
orbits and nontrivial positive cycles remain unexcluded. No staging,
commits, or Git writes were performed.

## 2026-10-12: an explicit density countermodel with ordinary even halving

The full Collatz proof/disproof goal remains active and unresolved. The
previous branch-density turn was progress, and this turn tests which
properties can force its missing relative inequality. No actual Collatz
counterexample, complete proof, or external blocker was found. There is
no live process to resume; verifier session 92289 finished successfully.

New `docs/DENSITY-COUNTERMODEL.md` gives an explicitly DIFFERENT map F.
Its even branch is n/2, and F(1)=4, F(4)=2, F(2)=1. Its odd branch is
changed; for example F(3)=14, whereas ordinary Collatz C(3)=10. Keep
this distinction prominent. This is a counterexample only to a proposed
deduction from general density/passage/packing properties.

Odd states are g_m=4m-3 and d_m=4m-1. For non-power m, their odd index
map removes the highest binary one, m -> m-2^floor(log_2 m). At powers,
the g-index halves toward one, whereas the d-index doubles forever.
Ordinary odd steps insert powers of two so that every target still has
at most one odd parent in addition to its even parent. The exact clocks
and special g-index-one handling are in the source and note.

Every start whose odd part is 1 mod 4 reaches the known cycle; every
start whose odd part is 3 mod 4 escapes. Both sets have density 1/2.
The escaping spine b_k=4*2^k-1 obeys F(b_k)=2*b_(k+1) and F^2(b_k)=b_(k+1).
The minimum law is p_1=1/2 and p_(b_k)=2^(-k-2), with no other atoms.

The written predecessor densities are explicit. For odd targets:

  r_(g_(2^k)) = 2^(-k-1),
  r_(d_(2^k)) = 1/2 - 2^(-k-2),
  r_(4m-c) = 2^(-k-2) for 2^k < m < 2^(k+1), c in {1,3}.

For a=2^v q with q odd and q's index in binary level k:

  r_(2q)=r_q; r_4=1/2;
  r_(2^v)=2^(1-v) for v>=3;
  r_(2^v q)=2^(-k-v) for v>=2 and q!=1.

These come from single residue classes or their complements among odd
source indices, with at most one excluded source. The even-target formulas
use a residue characterization of all possible incoming odd parents,
not an assumed exchange of an infinite union with a density limit.
Conditioning on initial valuations gives the same natural densities.
In particular every target has r_a>=1/(2a), and the target-uniform
finite-count error is <=8*(1+floor(log_2 X))/X.

First odd passage below H>=7 is explicitly periodic among odd sources
above H. For type c, use h=floor((H+c)/4), q=2^floor(log_2 h), Q=2q,
and z=m mod Q. A nonzero residue lands at z if z<=h, else z-q; zero
lands at q in the g component and never enters in the d component.
Convert indices back with 4z-c. A period P<=4H gives a limiting law
with maximum atom <=8/H, including infinity, and TV error <=4H/Y for
uniform odd sources in integer intervals [Y,2Y), Y>H. Full positive
sources have the same limit because even halving changes no passage mark.
This is stronger stabilisation than the earlier written Collatz input,
yet escape has density 1/2 in this comparison map.

Every orbit has at most ten distinct values per dyadic band: the odd
levels strictly descend before the terminal cycle or escaping spine,
each ordinary descent spike is <4 times its odd start, and a halving
block contributes at most one even value per band. The explicit spine
adds at most two values per band. Thus an arbitrary length-L integer
interval contains <=10*(log_2 L+2) distinct orbit values. Also r_a<=8/a
outside the escaping odd spine and its doubled targets; only finitely
many of those can reach a fixed target. This proves decay inside each
fixed predecessor basin while r_(b_k) increases to 1/2 along escape.

At merge 2*b_(k+1), the unused even parent is u_k=4*b_(k+1). Its density
is 2^(-k-3), and r_(u_k)/r_(b_k)=1/(b_k-1). Hence even the global lower
bound r_a>=1/(2a) coexists with summable relative branch contributions
and failure of any positive logarithmic relative lower bound along this
spine. This map does not preserve the actual Collatz odd-parent congruence
or r_a=0 at multiples of three, so it is not a countermodel to all of the
project's arithmetic statements.

New `lean/DensityCountermodel.lean` has fourteen kernel theorems: even
halving, the three known cycle edges, a positive spine bound, its one-
and two-step identities, iteration addition and both parity formulas,
nonarrival at one, a power lower bound, unboundedness, and the explicit
disagreement with C at 3. All report only standard axioms (or none).
No native evaluation, sorry, warnings, or extra axioms remain. The
density, passage, orbit classification, parent classification, and packing
arguments are written, not claimed as additional kernel proofs.

New `verify_density_countermodel.py` compiled the module afresh using
Lean4.33.1, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Only CollatzContradiction was reused after checking the cached compiler
and source/object/log hashes. Default reproduction builds both modules
sequentially. The finite replay passed:

- 512 inverse-parent targets and 393984 forward source checks;
- 8192 classified sources and 8437760 exact target-membership comparisons;
- 8192 rational density-formula targets, with parent flow checked at
  the 8189 noncycle targets;
- 129 explicit spine parameters;
- 504 first-passage residue classes and 1152 interval spot checks;
- the recorded rational finite-density and total-variation bounds.

The direct traces terminate at the known cycle or a symbolic escaping
tail proved by the new Lean module. No timeout is treated as escape or
nonentry. Records and two Lean logs are under `results/density-countermodel/`.
The final record passed at 2026-10-12T16:53:27.940017+00:00 and has nine
dependency hashes. A notation-only accidental comma in the earlier
branch note's subscript was removed; that record and the new record
track the corresponding hash updates with explicit provenance. No
mathematical statement or executable check changed in that correction.

NEXT: focus on the actual 3n+1 odd-parent arithmetic, including the
zero-density multiples-of-three property and unit preservation after
odd steps, rather than deriving the relative inequality from the general
properties refuted here. The comparison-map formulas cannot be imported
as formulas for actual Collatz densities. Both divergent ordinary Collatz
orbits and nontrivial cycles remain unexcluded. No staging, commits, or
Git writes were performed.

## 2026-10-12: actual inverse congruences and the finite-clock gap

The follow-up examined the actual odd-parent restrictions and the sibling
map b -> 4b+1. No relative density lower bound was obtained. Smaller-source
coalescence and bidirectional ranks were checked against the existing
sections 9–14 and 20–24 of APERIODIC-ATTEMPT; do not restart the excluded
fixed-horizon or finite-affine searches. No new external theorem was
adopted from this turn's literature searches.

New files:

- `docs/DENSITY-TIME-TRUNCATION.md`
- `lean/DensityTimeTruncation.lean`
- `verify_density_time_truncation.py`
- `results/density-time-truncation/{verification,replay}.json` and two Lean logs.

For ordinary C, the exact two-step parents of a are 4a, and at most one
additional source: (2a-1)/3 if a%3=2, or 2*((a-1)/3) if a%6=4.
These optional cases are mutually exclusive. The recursive inverse-list
length f_k(a), at time 2k, is periodic modulo 2*3^k. Under a shift by
2*3^k*q, its primary child shifts by 2*3^(k-1)*(12q), and its optional
child by 2*3^(k-1)*(2q). This supports the kernel induction.

Kernel evaluation of all 1458 residues proves f_6(a)<=38 for every a.
The target 364 attains 38 with a separately checked duplicate-free list.
Composition gives, for every k and target a,
  # {n : C^(2k)(n)=a} <= 2^(k mod 6) * 38^(k/6).
The exact formal cardinality statement bounds every finite distinct
source list; the inverse enumeration supplies a finite cover. Seventeen
kernel theorems passed with only standard axioms. The finite certificates
use `decide`, not `native_decide`. No added axiom or admitted proof.

Written clock corollary: at j=12q+s, 0<=s<12, the exact-time fibre has
at most 2^ceil(s/2)*38^q sources. Summing over j<=T gives fewer than
195*38^(T/12) sources reaching one target by T, uniformly in the target.
A fraction p>0 among starts through X therefore requires
  T >= (12/log 38)*log(p*X/195),
with coefficient approximately 3.29889093291 for the natural logarithm.
This is a necessary lower bound, not a sufficient time to converge or
reach a growing set. Improving the finite block maximum alone would only
improve this lower bound; it would not solve the missing termination step.

The new written density result uses the previously established written
uniform target approximation delta_X=sup_a|R_X(a)-r_a| -> 0, the written
component law, and external PLD positivity. For epsilon>0 choose delta_X
<epsilon. Then every target with r_a>=epsilon lies on one of the finitely
many complete forward orbits of starts 1..X. Outside finitely many prefix
values these form finitely many divergent tails; cyclic parts are finite.
On each divergent tail r_a tends to its component mass lambda_C. Hence
the positive accumulation values of r_a as a->infinity are exactly the
divergent component masses. In particular,
  lim_A sup_(a>A) r_a = lambda_div,
where lambda_div is the largest divergent component density, or zero
if none exist. Positivity and summability of all component masses make
a nonzero supremum a maximum. Global r_a -> 0 would exclude divergence
but allow other cycles. It has not been proved.

Let R_(X,T) count sources hitting a by time T, and
Delta_X(T)=sup_a(R_X(a)-R_(X,T)(a)). At fixed X, this defect is eventually
exactly d_X, the largest sampled fraction in one divergent component.
The lower bound holds for EVERY finite T: a late common target beyond
all sampled T-prefixes receives every source from that component.
For the upper bound, eventually the finite orbit sets of all sampled
cyclic sources have been covered. A missed target then belongs to just
one divergent component. The threshold is not supplied as a usable bound.

Thus the two iterated limits are
  lim_X lim_T Delta_X(T) = lambda_div,
  lim_T lim_X Delta_X(T) = lambda_* = max_C lambda_C.
For fixed T, the finite-fibre bound makes sup_a R_(X,T)(a) -> 0,
which proves the second equality. If full Collatz were true, the two
limits would be 0 and 1. A clock below (1-eta)*(12/log38)*log X leaves
defect tending to lambda_*. Existence of ANY clock with Delta_X(T(X))->0
is equivalent to no divergent positive orbit under the density inputs
and PLD. This is not a construction of that clock or a proof of its
existence. It does not exclude nontrivial cycles.

The verifier passed at 2026-10-12T17:26:43.837589+00:00, with thirteen
artifact/dependency hashes. It validated eleven hashes from the uniform
predecessor record and twelve from the written density record. Only the
CollatzContradiction dependency was reused after matching compiler and
source/object/log hashes; the new module was compiled afresh in 7.51s.
The compiler is the pinned Lean 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The replay passed:

- 2184 residue fibres by ordinary one-step inversion, 28632 source entries;
- 546 residue lifts, including quotients above 2^65;
- 455 complete forward fibres at roots 0..64, times 0,2,...,12;
- 349511 forward source enumerations, with 3961386 ordinary steps;
- 95 all-depth composition checks through 36 ordinary steps;
- 4096 complete known-cycle paths, with 311850 distinct path entries
  counted separately per source;
- 93224 target comparisons across 24 finite-clock populations.

The sample cutoffs are 256,1024,4096 and their complete orbit-cover
times are 127,178,237. Their eventual defect is zero; no divergent sample
is asserted. The density limits, the spectrum, and the interchange-of-
limits analysis remain WRITTEN, not Lean theorems. The external PLD
source was not rebuilt. No current verifier or Lean process is live.

NEXT: the remaining task needs an upper estimate on the mass persisting
beyond a finite clock, or a relative unused-branch estimate, or a new
arithmetic argument. The target-uniform density limit alone supplies
neither; interpreting its finite source sample as finite-time support
would already assume away divergence. Nontrivial cycles remain a second
unresolved case. The full goal stays active. No Git writes were made.

## 2026-10-12: a typical logarithmic clock for the actual global minimum

The follow-up retained passage times while telescoping the existing
WRITTEN natural-density passage laws. It gives a new written consequence
conditional on the same unformalized Proposition 4.1, not an independent
validation of that proposition and not a proof of Collatz. No novelty is
claimed. New files are:

- `docs/CLOCKED-MINIMUM.md`
- `lean/ClockedMinimum.lean`
- `verify_clocked_minimum.py`
- `results/clocked-minimum/{verification,replay}.json` and two Lean logs.

For each positive n, M(n)=min_t C^t(n) exists and is attained at some
finite time tau_M(n), even if n diverges afterward. Every finite population
therefore has a finite common minimum-attainment clock T_B. Its existence
uses well-ordering, not convergence; no computable bound is supplied.
First ODD passage is a strict record low in the ordinary path, so entry
at time i with landing b gives M(n)=M(b), tau_M(n)=i+tau_M(b). Do not
claim that every previous ordinary state exceeds the floor: at source
85 and floor 31, odd landing 1 occurs at time 9, but even 16 is already below
the floor at time 5. Those earlier values still exceed the landing.

The first version of the argument used n0=floor(log x/(10 log2)), the
existing entry bound by n0 Syracuse steps, and the upper valuation tail
S_n0 <=(201/100)n0 outside a power-small event. Its Chernoff certificate
is the exact inequality
  101^100 * 201^201 < 100^100 * 202^201.
With r=202/201, the tail is at most q^(n0/100), where q is the ratio of
the two sides. Ordinary passage time is at most
L(x)=301 log x/(1000 log2). A test on the landing's remaining minimum
time uses g(infinity)=0, with source nonentry already charged to the
exceptional event. Nonentry is NOT inferred to imply a late minimum.

For alpha=1001/1000, descend Y_i=Y^(alpha^-i), shared floors
x_i=Y^(alpha^(-i-2)), until Y_J in [B,B^alpha). Clock sums give
E(Y,K log Y+T_B) <= C (log B)^(-c), where
  K=301000/(1001 log2)=433.817389917660... <435.
The rational checks use log2>53056/76545>693/1000. This proves the
coarse 435 log n upper clock in natural density. The later sharper
argument in Section 6 retains the clock spent by BOTH sources:

Put d=log(4/3), kappa=3/d=10.428178490346623.... For each fixed eta>0,
the ordinary first odd passage time from U_y to floor x is within
eta log x of kappa log(y/x), except with probability O_eta(x^-c_eta),
uniformly for y in [x^alpha,x^(alpha^2)]. Tao's Proposition 1.9 and
Lemma 2.2 were rechecked at https://arxiv.org/html/1909.03562v7.
Uniform residues mod 2^(3n0) give the required valuation law; a union
of Chernoff bounds gives |S_j-2j|<=h log x for every j<=n0 outside
a power-small event. Until first Syracuse entry k, exact logarithms give
  log N_j = log n - d*j - (S_j-2j)*log2 + e_j,
  0<=e_j<=j/(3x),
because all previous ODD states exceed x. Compare j=k and k-1 to
bound k, then use ordinary time k+S_k. Choose h in terms of eta.
No stochastic assertion after this first passage is needed.

Couple landing marks using their TV distance, then lift to full source
marginals by conditional distributions given each mark. When marks
match and both clocks are good,
  tau_M(n)-tau_M(m)=I_x(n)-I_x(m),
so centered times tau_M(U_y)-kappa log y and tau_M(U_z)-kappa log z
differ by at most 2 eta log x. No independence or new joint clock/landing
mixing claim is used. For D_y(w)=P(|tau_M(U_y)-kappa log y|>w), this gives
  D_y(w+2 eta log x)<=D_z(w)+C_eta(log x)^(-c).
At the final scale the centered times are bounded by the finite constant
W_B=T_B+kappa*alpha*log B. Summing clocks gives
  D_Y(W_B+2 eta log Y/(alpha*(alpha-1)))<=C_eta(log B)^(-c).
Fix eta sufficiently small for a requested epsilon, then let Y->infinity
first and B->infinity second. Odd dyadic decomposition and the initial
even-halving identity prove the written conclusion
  #{2<=n<=X: |tau_M(n)/log n-kappa|>epsilon}=o(X).
The initial even valuation a contributes only the fixed centered shift
a*(1-kappa log2); truncate large a before taking the density limit.

For a fixed positive target a, first hitting time tau_a on its actual
predecessors differs from tau_M by bounded constants depending on a:
  tau_M(n)-tau_M(a) <= tau_a(n) <= tau_M(n)+V_a.
Here V_a is the largest first hitting time of a from the finitely many
m<=a that actually reach it. If a is visited before the minimum the upper
bound is immediate; otherwise begin at that minimum. Thus a fixed target's
density captured by c log n, or the population clock c log X, tends to
zero for 0<=c<kappa and to r_a for c>kappa. Finite target profiles follow.
The case c=kappa and an effective convergence rate are NOT determined.

For Delta_X(T)=sup_a(R_X(a)-R_(X,T)(a)), the written conclusion is now
  Delta_X(floor(c log X)) -> lambda_*   if 0<=c<kappa,
  Delta_X(floor(c log X)) -> lambda_div if c>kappa.
Above kappa, choose an intermediate minimum clock and cover the finitely
many cyclic tails from minima<=B. Divergent targets receive at most the
largest sampled divergent-component fraction d_X, and a late common
target always gives the lower bound d_X. Below kappa, each FIXED target's
clocked proportion tends to zero; choose fixed targets with r_a arbitrarily
close to lambda_*, and use sup_a R_X(a)->lambda_* for the upper bound.
This avoids claiming a uniform vanishing bound on clocked proportions.

Since log(4/3)>2/7, kappa<10.5<11. Hence the computable finite-clock
proportion of starts through X reaching 1 by floor(11 log X) tends to p_1.
External PLD makes full Collatz equivalent to this specific limit being 1.
It remains unknown: a typical minimum clock does not force the minimum
to be 1, and the optimal uniform defect may still be lambda_div>0.

The Lean module has 22 kernel theorems, including minimum existence,
finite-population clocks, strict record entry, exact first-minimum suffix
transport, uniqueness, and the equality s+j=t+i for two sources meeting
at record times i,j with first minimum times s,t. It also proves finite
minimum-time equivalence with hitting 1 for an ALREADY CONVERGENT start.
The analytic concentration, real logarithms, infinite sums, and all density
limits remain WRITTEN. Only standard axioms or none are reported; no
native evaluation, sorry, warnings, or extra axioms were introduced.

Final verification passed at 2026-10-12T18:11:02.855342+00:00. The new
module compiled afresh in 1.541s with pinned Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Only CollatzContradiction was
reused after validating compiler/source/object/log hashes. The manifest
has 13 artifact/dependency hashes, all revalidated, and validates 13 prior
time-truncation hashes and 12 prior written-density hashes. Finite replay:

- 8192 complete known-cycle trajectories, with 684579 distinct path entries
  counted separately per source;
- 57344 first-record/minimum-time checks and 57344 coupled clock checks;
- 436408 target-before-or-after comparisons;
- 480 exact one-sided and 640 exact centered probability inequalities;
- 129 rational geometric clock sums and 771 ordinary budget comparisons;
- 8192 nonentry marks at the empty floor 0, not inferred from timeouts.

The exact finite maximum minimum times at cutoffs 64, 256, 1024, 4096, 8192
are 112, 127, 178, 237, 261; all those sources reach the known cycle. These
finite data do not certify an asymptotic error, rate, or divergent orbit.
The external PLD source was not rebuilt. The final verifier exited 0;
there is no live build to resume. README and ATTEMPT now link the result.

NEXT: the finite clock is now concrete, but its limiting convergence
fraction p_1 remains unidentified. Further work must constrain component
mass or use new 3n+1 arithmetic; merely improving the logarithmic time
coefficient, or treating attainment of a minimum as convergence to 1,
cannot settle the goal. Nontrivial cycles remain a separate obstruction
when studying divergence alone. The full goal stays active. No staging,
commits, or Git writes were performed.

## 2026-10-12: reflected coalescence and the actual source interval

The preceding clock turn is classified as progress: it supplied a
conditional written typical minimum clock and 22 exact kernel lemmas,
while leaving the convergence density p_1 unknown. This turn tested
whether complete-period adjacent coalescence could constrain that mass.
It found an exact limitation of the proposed statistic, not the missing
density estimate. The full Collatz goal remains active and unresolved.

New artifacts:

- docs/PREFIX-COALESCENCE-AUDIT.md
- lean/ReflectedCoalescence.lean
- verify_prefix_coalescence.py
- results/prefix-coalescence/verification.json and replay.json
- results/prefix-coalescence/CollatzAffine.log and ReflectedCoalescence.log

Let U_+ be the shortcut map and U_- its odd-offset-minus counterpart;
both halve even inputs and fix zero. Let w count odd inputs in k steps.
The kernel induction proves, whenever n+m=2^k*q,
  U_-^k(n)+U_+^k(m)=3^(w_-(k,n))*q,
  w_-(k,n)=w_+(k,m).
The current states have equal parity until the remaining factor of two
is exhausted, and the odd +/-1 offsets cancel in their sum. Specializing
to n=r, m=2^k-r gives reflection of endpoints and odd counts on the full
residue interval. The bijection r -> 2^k-1-r therefore identifies the
adjacent weighted coalescence masks of the two maps at EVERY depth.
Both endpoint agreement and equal odd counts are required for the
all-progression identity supplied by CollatzAffine.affine.

The kernel also proves that U_- traps 5 in the cycle 5,7,10 and never
reaches 1, whereas U_+^4(5)=1. Identical whole-period coalescence counts
alone do not select the basin containing one. This does not rule out
all coalescence methods and does not transfer external plus-map PLD to
the minus map. The counts through k=20 match OEIS A398792, which already
records the sign symmetry; no novelty is claimed. Primary comparison:
https://oeis.org/A398792. The first twenty counts are
  0,0,1,3,8,18,39,82,170,351,721,1476,3012,6130,12450,25241,
  51105,103358,208840,421643.

For F_X(k)=X^-1 #{1<=n<=X: U_+^k(n) in {1,2}}, every shortcut step
uses at most two ordinary steps. The earlier ordinary finite-hit bound
<195*38^(T/12) per target therefore implies the WRITTEN unconditional
bound
  F_(2^(6q))(6q) <= 390*(19/32)^q -> 0.
The same argument extends to every k=6q+s, 0<=s<6, with an absolute
constant factor. This counting consequence of a previous kernel bound
is not a new Lean theorem about real limits.

In contrast, the preceding WRITTEN density and clock arguments give
  F_X(ceil(11 log X)) -> p_1 > 0.
Sandwich ordinary first hits of 1 by floor(11 log X) below this shortcut
cycle-entry fraction, and eventual hits of 1 above it; positivity uses
external PLD. The parity period at this clock is between
X^(11 log2) and 2*X^(11 log2), so the actual source interval occupies
Theta(X^(1-11 log2)), with exponent approximately -6.62462. Averaging over
that whole period does not estimate the much shorter initial interval.
The required estimate remains
  #{n<=X: U_+^ceil(11 log X)(n)>2}=o(X).
Together with existing inputs it would settle Collatz, but this turn
does not prove it. No existence of a divergent orbit is inferred.

Fresh verification passed at 2026-10-12T18:45:01.853783+00:00 with
pinned Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. CollatzAffine compiled afresh
in 1.840s and ReflectedCoalescence in 0.439s. All seven new theorem
reports use standard axioms or none, with no native evaluation, sorry,
warnings, or extra axioms. The final record contains 12 artifact hashes,
all independently revalidated, and validates 13 hashes from each of the
clocked-minimum and time-truncation records. The verifier exited 0;
there is no live build or verification job to resume.

Independent exact finite replay checked:

- 2097170 reflected endpoint/odd-count identities;
- 2097150 reflected adjacent mask comparisons, through depth 20;
- ordinary first-one times for starts through 65536, with 142216 stored
  time rows checked by the exact step and strict decrement;
- shortcut first-{1,2} times for those starts, with 104146 such rows;
- independent direct trajectories for 4096 starts in both maps,
  totaling 307751 ordinary and 201676 shortcut steps;
- clocks at thirteen populations X=2^j, j=4..16, decided using exact
  rational upper/lower bounds on log 2 rather than floating point.

At X=65536, the ordinary floor clock is 121 and captures 41607 sources;
the shortcut ceiling clock is 122 and captures 62444. The largest entry
times in that finite interval are respectively 339 and 213. These are
finite known-cycle data, not certified asymptotic errors or rates.

The external PLD explicit coefficient construction was read locally:
b=2^80, choose a large target-dependent seed r>=16^b, m=132*r*C+1,
eta=9*(2/3)/(16*3^m), and c_a=eta/(32*r). It supplies no established
relative sibling-density estimate. No external source was rebuilt.
The public natural-density page advertises a 599-file Lean package at
https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/.
That package was NOT downloaded, replayed, or adopted. Our passage
premise and analytic consequences remain explicitly WRITTEN.

NEXT: retain the initial-interval location and actual 3n+1 arithmetic
when seeking control of p_1 or component masses. Do not replace the
needed initial-interval estimate by a full parity-period average, or
infer a density zero-one law from 2-adic Haar ergodicity. Neither this
audit nor the known coalescence sequence establishes density one.
README and ATTEMPT link the audit and its reproduction command. No
staging, commits, or Git writes were performed.

## 2026-10-12: sparse odd-output swaps retain the density inputs

The preceding coalescence turn is classified as progress: seven kernel
lemmas and exact finite data ruled out a specific inference from full
parity periods to the needed source interval. This turn tried to derive
the missing relative branch bound using actual inverse congruences.
The new evidence is a stronger comparison map: the residue restrictions,
unit-target positivity, zero density at multiples of three, and the
existing passage inputs still do not force convergence. The exact odd
parent formula at EVERY target remains an essential available distinction.
The full goal is active, with neither a proof nor a counterexample for C.

New artifacts:

- docs/SPARSE-COLLATZ-PERTURBATION.md
- lean/SparseCollatzPerturbation.lean
- verify_sparse_collatz_perturbation.py
- results/sparse-collatz-perturbation/verification.json and replay.json
- results/sparse-collatz-perturbation/CollatzContradiction.log and
  SparseCollatzPerturbation.log

Define A_j=(4^(3j+8)-1)/3, so A_0=21845 and A_(j+1)=64*A_j+21.
Let B_j=(2*A_(j+1)-1)/3; B_0=932067. We have A_j=5 mod12,
B_j=3 mod4, and A_j<B_j<A_(j+1). For t>=0, let pi_t exchange
A_j and B_j for j>=t and fix everything else. The altered map is
F_t(n)=C(pi_t(n)). Its changed input set has at most
2*(1+floor(log_64 X)) members through X. It agrees with C below A_t.
The Lean definition uses classical choice of a unique index; a finite
geometric search computes it, separately checked in Python.

The ordinary formulas are F_t(A_j)=2*A_(j+1), F_t(B_j)=4^(3j+8).
Even halving and 1,4,2 remain unchanged. The kernel proves
  F_t^(2k)(A_t)=A_(t+k),
  F_t^(2k+1)(A_t)=2*A_(t+k+1),
and never-one for this path or any source that reaches A_t. The displayed
values tend to infinity. By contrast C(A_t)=4^(3t+8), so A_t itself
is an explicitly convergent actual-Collatz start. This is NOT a positive
counterexample to C. The F_0 replay preserves every checked trajectory
from 1..64, whose largest ordinary state is 9232<A_0. Any prescribed
finite collection of trajectories is preserved by choosing a larger t.

The exact inverse formula, also kernel checked, is
  F_t(n)=a iff n=2a OR (a=4 mod6 AND n=pi_t((a-1)/3)).
Hence the allowed ordinary odd images, their uniqueness, and the
two-parent maximum remain exactly as for C. The shortcut odd parent
is pi_t((2a-1)/3), allowed precisely when a=2 mod3. Nevertheless its
VALUE differs at swapped images. For 3|a the kernel proves
  F_t^k(n)=a iff n=2^k*a.
The predecessor density there is zero by written dyadic counting.

Unit-target PLD is inherited by an exact inclusion, without the written
natural-density premise. Under the ORIGINAL C, the set of all powers
of two and all A_j, B_j, 2*A_j is forward invariant. Every c>1 with
c=1 mod12 lies outside it. Thus original paths reaching c avoid every
modified input before that hit and have the SAME hitting time under F_t.
For any positive unit a, choose e in 6..11 with 2^e*a=4 mod9 and
c=(2^e*a-1)/3. Then c>1, c=1 mod12, and F_t^(e+1)(c)=a by one
unchanged odd step and e halvings. The kernel proves
  P_c^C subset P_a^(F_t).
External PLD at this original unit c proves positive lower density at
every modified-map unit a. At a=1 it gives positive lower density of
convergence; at a=A_t it gives positive lower density of escape. No
exact fraction is asserted. Existence of modified-map natural densities
uses the additional written passage theory, not PLD alone.

WRITTEN stability of the large-floor passage input: sample odd n from
[y,2y), with x^alpha<=y<=x^(alpha^2), alpha=1.001. On the old-map
good event, first odd passage below x takes at most T=4*n0 ordinary
steps, n0=floor(log x/(10 log2)); its failure probability is O(x^-c0).
Until the first modified input the two paths coincide, and a modified
odd value <=x is already a landing, before its changed outgoing step.
Any discrepancy therefore hits a modified input above x by old time T.
All old states lie below B=2*y*4^T, with log B=O(log x). Only O(log x)
modified inputs lie there. At most 2^(T+1)-1 positive sources hit any
one target by T, and 2^T<=x^(2/5). Thus the coupling error is
  O(x^-c0)+O((log x)*x^(2/5-alpha))
  = O(x^-c0)+O(x^(-3/5)).
This transfers nonentry and uniform TV stabilization, with constants
independent of t. The clocks coincide on the coupled good event too.
It compares GROWING floors and nearby source scales, not fixed-small-
floor limiting laws or eventual basin probabilities. The asymptotic
claim remains WRITTEN and conditional on the existing C passage input.

For each FIXED shortcut depth k, only O_k(log X) sources through X
can encounter a modified input, using the same inverse-fibre union
bound and the old upper envelope 2^k X. Thus all fixed-length shortcut
parity words retain density 2^-k. This is not infinite-path randomness.
Orbit packing with the old sigma<1 also persists in writing: an F_t
path is a C prefix followed by either the explicit geometric escape or
halving into the known cycle. The additional distinct values contribute
O(1+log L) in any length-L interval.

With target densities r'_a supplied by the transferred passage theory,
the escaping odd spine satisfies the exact nonperiodic partition
  r'_(A_(j+1))=r'_(A_j)+r'_(4*A_(j+1)).
The unused/used ratios are summable, while log A_j=O(j+1). Consequently
a uniform lower ratio kappa/log A_j with kappa>0 fails in this system.
Such a relative bound cannot follow from the shared density, passage,
packing, and inverse-congruence properties alone. Every odd step on
the explicit escaping tail uses a modified input: sparsity among source
integers gives no control of concentration along an individual orbit.

Final verification passed at 2026-10-12T19:23:30.975017+00:00. The
new module contains 44 theorem declarations, with 20 main theorem roots
explicitly audited. Fresh sequential builds used Lean 4.33.1, compiler
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:
CollatzContradiction 0.486s, SparseCollatzPerturbation 0.886s.
Only propext, Classical.choice, Quot.sound (or subsets) occur. No native
evaluation, sorry, warning, or new axiom is present. The final manifest
has 12 artifact/dependency hashes. The verifier also revalidated all
389 source/object/log triples from the COMPLETED external PLD replay
without rebuilding it, and the preceding audit's 12 artifact hashes.
All verifier processes are terminal with exit 0; nothing is live to resume.
The record's later written_scope_review adds the explicit odd-step
growth-bound limitation and refreshes only the note's hash; compiled
and finite-check artifacts are unchanged and were not rerun for that edit.

Exact finite scope:

- 384 large-index swap cases, 3072 support cutoffs through 1024 bits,
  and 768 explicit escaping-path states;
- 1048592 forward sources, compared against inverse formulas at 65536
  ordinary targets and 32768 shortcut targets;
- 16404 safe-ancestor paths, 18196 safe-target occurrences, and 252473
  unchanged safe-prefix states;
- classification of starts through 262144, using 568838 state rows
  checked by strict time decrease to either one or a proved spine;
- independent direct traces for 4096 sources, totaling 307751 steps;
- 786432 source-step comparisons for shortcut prefix coupling and
  exact finite histogram/union-bound inequalities.

At cutoffs 64,1024,16384,65536,262144 the classified escaping counts
are 0,0,1,26,123, respectively. These are finite altered-map data, not
estimates of its eventual density and not exceptional actual-Collatz
starts. No timeout is treated as an infinite orbit.

The public natural-density page and the 2026 Wirsching-program preprint
were read as scope checks; neither supplied a new adopted theorem.
The 599-file external natural-density package is still NOT downloaded
or replayed, and our analytic passage premise remains written.

NEXT: an actual-Collatz exclusion must use the exact odd-parent values
or an equally strong property that this sparse perturbation violates.
Do not infer the relative logarithmic branch lower bound from the shared
properties, finite parity statistics, or positivity alone. The original
map's upper odd-step growth bound is also violated at the upward swaps;
this construction does not test an argument that uses that bound in an
essential way. No p_1=1 estimate was obtained. README and ATTEMPT link
the result. No staging, commits, or Git writes were performed.

## 2026-10-12: weighted loss accounting for the actual Collatz formula

The preceding turn made progress: the sparse-perturbation record's twelve
hashes were revalidated before continuing. Its comparison-map result is
not an actual counterexample. This turn returned to C(n)=3n+1 for odd n
and derived an exact finite accounting identity, then a conditional
weighted escape diagnostic. The full goal remains ACTIVE and unresolved.

New artifacts:

- docs/WEIGHTED-DISSIPATION.md
- lean/WeightedDissipation.lean
- verify_weighted_dissipation.py
- results/weighted-dissipation/verification.json and replay.json
- results/weighted-dissipation/CollatzContradiction.log and
  WeightedDissipation.log

Write x_j=C^j(n), W_0=1, and multiply W by 3*x_j/(3*x_j+1) at each
odd input, leaving it unchanged at even inputs. The exact loss then is
ell_j=W_j/(3*x_j+1) at odd inputs, zero otherwise. For EVERY finite
prefix, including repeated cycle traversals,
  W_T + sum_(j<T) ell_j = 1,
  W_T = n*3^(odd inputs)/(2^(even inputs)*C^T(n)).
The Lean module defines integer numerator A, denominator B, and a
common-denominator loss L, proves A+L=B, positive denominators/numerators,
concatenation, and the affine identity with recursively defined slope
products. Reading those products as powers of three/two is written.
Positive returns necessarily include an odd input, have A<B, and their
weights repeat geometrically. The known ordinary cycle has A=3,B=4.
There are nineteen theorem declarations and eighteen audited main roots.

WRITTEN, using the existing finite-path packing estimate: W_infinity
exists by monotonicity. It is zero on every eventually periodic orbit
and satisfies exp(-8192/3)<=W_infinity<=1 on every divergent orbit.
The latter uses the reciprocal sum over DISTINCT odd orbit values.
Do not apply that packing estimate to infinitely repeated cycle visits.

Define mu_n on positive odd targets plus a separate infinity symbol by
putting every loss ell_j at x_j and placing W_infinity at infinity.
Finite telescoping plus monotone summation makes this a probability
measure. At any time i,
  mu_n = prefix_loss_measure + W_i(n)*mu_(C^i(n)),
so TV(mu_n,mu_(C^i(n)))<=1-W_i(n). For first ODD passage below H,
the prefix loss is <=(8192/3)*H^(-1/20), independently of its duration.
Only prior odd inputs need exceed H; intermediate even values may not.

CONDITIONAL WRITTEN on local natural passage Proposition 4.1: the
natural averages X^-1 sum_(n<=X) mu_n converge in TV at a logarithmic
rate to a countably additive probability measure mu. The nearby-scale
coupling and telescope work for probability-valued observables. A fixed
reference mu_n may have INFINITE support, but its finite heads are tight;
completeness in TV therefore still preserves mass one. Initial halving
does not change mu_n. No new external density premise is adopted.

For odd N, w_N(n) is its first-hit weight, zero when unreachable.
B_N=1 for nonperiodic N, and B_N=1/(1-beta_N) on a cycle, where beta_N
is its full-cycle weight. Exact pointwise geometric summation gives
  mu_n(N)=B_N*w_N(n)/(3N+1).
The TV limit supplies natural weighted means D_N=mean(w_N); partial
summation gives the same logarithmic means. In particular
  d + sum_(N positive odd) B_N*D_N/(3N+1) = 1,
  d = mean(W_infinity).
The series interchange uses TV, not only individual-coordinate limits.
At N=1, B_1=4 and the charge is D_1, not D_1/4. Positivity gives
D_1>0 and hence d<1. If Lambda_div is the TOTAL density of divergent
starts, exp(-8192/3)*Lambda_div <= d <= Lambda_div. External PLD means
any divergent orbit forces Lambda_div>0. Thus d=0 is equivalent to
universal eventual periodicity, but d=0 remains UNPROVED. This does
not exclude additional cycles or establish full Collatz.

CONDITIONAL WRITTEN on the prior ordinary clock theorem, with
kappa=3/log(4/3): mean W_floor(c log X) tends to 1 for c<kappa and to
d for c>kappa, for both population and individual log clocks. The
critical coefficient and an effective error remain undetermined.
Below the clock, omit early hits of finitely many small odd targets and
the minimum-law tail; a repeated prefix without a small hit would be a
cycle entirely above the floor and belongs to that tail. This cycle
exception is required before using distinct-prefix packing. Above the
clock, first reach the global minimum in time c' log n, kappa<c'<c;
W_t(m)->W_infinity(m) uniformly over the FINITE set m<=H, without
classifying those orbits. Tightness of minima then finishes the limit.

For fixed T, C^j(n)>=n/2^j gives
  1-W_T(n)<=(2^T-1)/(3n),
so lim_T lim_X mean(W_T)=1 while lim_X lim_T mean(W_T)=d<1.
This noncommutation persists even if all positive starts converge.

Verification passed at 2026-10-12T19:53:36.591815+00:00. Fresh sequential
Lean 4.33.1 builds (compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6)
took 0.488s for CollatzContradiction and 0.268s for the new module.
The eighteen audited roots use only standard propext, Classical.choice,
and Quot.sound, or subsets. No native computation, sorry, new axiom,
or warning occurred. Fifteen artifact/dependency hashes are recorded.
Prior records' 12 finite-path, 13 clocked-minimum, and 12 density-law
hashes were checked. The completed 389-module external PLD build was
not rerun. The later written-scope review refreshes only the new note's
hash after adding sample counts and the consequence d<1; builds and
finite replay are unchanged. All jobs are terminal with exit zero.

Independent exact rational checks:

- 2048 complete paths to the known cycle, 138104 forward prefixes;
- 1092 reverse integer recursions, 1019 concatenations;
- 4352 geometric cycle repetitions with visit multiplicity;
- 106345 full-measure cocycle coordinate comparisons;
- 5120 passage TV/product inequalities, 2196 first-hit charge coordinates,
  and 28 finite charge partitions;
- 436800 source-clock pairs at cutoffs 64,256,1024,4096,16384,65536,
  including 1920 independent direct Fraction comparisons.

At X=65536, coefficients 4,8,11,16 give ordinary clocks44,88,121,177
and mean weights approximately .92162543,.57855998,.38637200,.11060250.
The finite means have exact rational enclosures of width <=2^-48.
The clocks' floors are bounded by rational atanh-series intervals for
log 2. None of these finite intervals bounds the asymptotic error or
determines d. Sample infinite measures only use completely verified
paths into 1,4,2; no timeout was classified as escape.

External context reviewed, NOT adopted: Lucas Valbuena's public
collatz-two-coordinate-obstruction README and paper/tao-basin-densities.tex
describe uniform reciprocal predecessor bounds, stationary traces,
an occupation lower bound with divergent excess, and an inverse-path
clock. The manuscript explicitly leaves the occupation upper bound open.
The source downloaded to /tmp/collatz-tao-basin-densities.tex has SHA256
fa4e6c790002bdbb32c1679eb0b833574e110f0462f16a0e2303594137822850.
Its claimed formal bundles were not downloaded, replayed, or imported.
The local proof above uses only the already recorded written premises
and the previously replayed target-dependent PLD theorem. Do not treat
the public uniform c/N claim or its claimed audits as a new local input.

NEXT: a concrete remaining target is to prove mean W_floor(11 log X)
goes to zero for the ACTUAL map, or prove the full charge series equals
one. Both are open, and finite decay at chosen clocks is insufficient.
The conservation identity alone cannot force loss of all weight: the
packing estimate explains precisely how an escaping path could retain
a positive product. Seek an actual-map estimate on this finite mean,
not another claim that identifying the infinity atom removes it. README
and ATTEMPT link the result. No staging, commits, or Git writes occurred.

## 2026-10-12: stopped odd-count mass and the coalescence tail

The preceding goal turn made progress: all fifteen weighted-dissipation
hashes were revalidated before this follow-up. This turn tested a concrete
route to the missing mean d=0, using exact balanced adjacent coalescence
and dyadic refinement. It produced an unconditional all-depth lower
bound that prevents the simplest summable-error argument. Full Collatz
remains unresolved and the goal remains ACTIVE.

New artifacts:

- docs/COALESCENCE-TAIL.md
- lean/CoalescenceTail.lean
- verify_coalescence_tail.py
- results/coalescence-tail/verification.json and replay.json
- results/coalescence-tail/CollatzAffine.log and CoalescenceTail.log

For the ACTUAL shortcut map, Delta_H(r)=wt H r-wt H(r+1). Adding
the next source bit 2^H preserves the first H odd counts and flips
both time-H endpoint parities, since the affine slopes 3^wt are odd.
Thus the next gap either holds for both children, or is Delta_H+1
and Delta_H-1 with equal multiplicity. This remains valid at the
boundary r=2^H-1: the affine theorem permits r+1=2^H.

Define G_H=abs(Delta_H) until its first zero at time >=1, and keep
G zero thereafter. Delta_1 is always +/-1. The two children of every
depth-H node, H>=1, have G-values summing to twice the parent's value.
The kernel proves ALL-DEPTH identities
  sum_(r<2^H) G_H(r) = 2^H,
  sum_(s<2^(H-1)) G_H(2s+e) = 2^(H-1), e=0,1.
Also 0<=G_H<=H, and balanced coalescence (equal endpoint AND equal
odd count) forces G_H=0. Consequently the full-period unmerged
fraction is at least 1/H, separately for each initial parity. These
are universal integer theorems, not finite-count extrapolations.
The kernel also verifies odd-count periodicity, balanced periodicity,
and persistence of balanced coalescence with time.

Stopping is essential. For the actual pair (1,2), the signed odd-count
gaps at depths 1,2,3 are [1,0,1]. The raw absolute gap can reactivate
and does not have conserved mean. G stays zero after depth two.

WRITTEN: the coherent uniform-bit/Haar law gives a balanced fusion
time T with P(T>H)=1-p_H. The harmonic tail implies E T=infinity,
also conditioned on the first bit. This does NOT say P(T=infinity)>0,
does not use a uniform probability on all positive integers, and does
not imply any actual positive orbit escapes. It remains compatible
with p_H tending to one; no external theorem asserting that limit is
adopted here.

WRITTEN stronger bound: orient the initial gap to +1 and generate
active increments and holding bits with two independent fair-coin
stacks. Activity is determined before the next bit, and active input
orientation preserves conditional fairness. At most H-1 active steps
have occurred by depth H. Survival of a simple walk for H-1 steps
therefore ensures G_H>0. Reflection/telescoping gives
  1-p_H^(e) >= P(G_H>0|e)
             >= binom(H-1,floor((H-1)/2))/2^(H-1), e=0,1,
of order H^(-1/2). This coupling and binomial formula are NOT Lean
formalized. Python only checks their finite instances through H=20.

WRITTEN sufficient criterion for d=0: write w(n)=W_infinity(n),
f(n)=w(n)/n and h_k(x)=2^k*f(floor(2^k*x)) for 1<=x<2. The weight
cocycle gives f(n)=3^(wt H n)/2^H * f(U^H n), so balanced adjacent
starts have equal f. Since w(2n)=w(n), even dyadic children exactly
retain the parent's h-value. Odd children also do so when (2n,2n+1)
eventually balance. Let B_k be the fraction of n in [2^k,2^(k+1))
whose even pair never balances. The actual changed-cell measure is
at most B_k/2. If sum B_k is finite, Borel--Cantelli makes h_k
eventually EXACTLY constant almost everywhere. Its limit has countable
range. Existence of the prior conditional natural mean d of w gives,
by partial summation, integral_a^b h_k -> d*log(b/a). Bounded convergence
identifies that limit with d/x. For d>0 the latter cannot have countable
range almost everywhere; hence summability would force d=0.

No such summability was proved. At any finite depth H<=k+1 the dyadic
even-input interval samples whole even residue periods exactly, giving
B_k<=1-p_H^(0). Each such upper-bound VALUE is at least 1/(k+1), so
these certificates cannot be summable over k. This is NOT a lower
bound on B_k or on the actual weight-change measure. Pairs unmerged
at H can balance later, and zero infinite weights can agree without
balanced coalescence. H>k+1 returns to the proper-source-subinterval
problem in the earlier audit. Even proving d=0 would leave additional
cycle exclusion before full Collatz.

Verification passed at 2026-10-12T20:35:20.537311+00:00. Fresh sequential
Lean 4.33.1 builds used compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, taking 0.382s for the affine
import and 0.516s for the new module. Twenty-three main roots were
audited; their dependencies are propext/Quot.sound or subsets, with
orbit_snoc using no axioms. No warnings, native computation, sorry,
or added axiom occurred. Twelve new artifact/dependency hashes are
recorded. The previous coalescence record's 12 hashes and weighted
record's 15 hashes were validated. No external replay was restarted.

Independent finite checks:

- 1,048,575 affine parity-flip pairs;
- 1,048,574 local stopped-mass identities;
- 2,097,150 pointwise gap bounds over all periods through depth 20;
- 826,010 balanced child-persistence checks;
- 48,151 direct integer pair paths, without affine recursion;
- 456 direct lifted paths at nonzero quotients 1,3,29,2^20.

At depth 20, each parity half has 524288 residues and stopped-gap
mass 524288. Positive stopped gaps occur for 133209 even and 122214
odd representatives; balanced counts are 289565 even and 132078 odd,
total 421643 as in the earlier independent enumeration. The complete
unmerged fraction is 626933/1048576. The written walk lower bound is
46189/262144, while the kernel harmonic bound is 1/20. All jobs are
terminal with exit zero.

NEXT: seek a bound on ACTUAL weighted dyadic changes (or an equivalent
finite-clock mean on the actual source interval), not a summable claim
for whole-period noncoalescence. The lower bound above closes that
specific shortcut but does not determine d. The original targets of
zero escaping mass and other-cycle exclusion remain open. README and
ATTEMPT link the new proof and reproduction command. No staging,
commits, or Git writes were performed.

## 2026-10-12: actual dyadic coalescence defects inside the known basin

The preceding goal turn made progress, with 23 audited kernel roots for
the complete-period tail. Its twelve hashes and all fifteen weighted-loss
hashes were revalidated before this follow-up. This turn strengthened
the route audit: under the already replayed positive-lower-density theorem
at one, the ACTUAL eventual-unbalanced dyadic fractions B_k are themselves
nonsummable. The weighted refinement criterion remains open. Full Collatz
is unresolved and the goal remains ACTIVE.

New artifacts:

- docs/DYADIC-COALESCENCE-DEFECTS.md
- lean/DyadicCoalescenceDefects.lean
- verify_dyadic_coalescence_defects.py
- results/dyadic-coalescence-defects/verification.json and replay.json
- seven fresh local build logs in that results directory

For a start known to reach one, define its arrival grade g(n)=t-2a,
where t is shortcut arrival time and a its odd count. The earlier grade
theorem makes this independent of the chosen arrival. Define the auxiliary
V(n)=2^g(n)/n on this basin and zero outside it. V is NOT W_infinity:
W_infinity vanishes on the entire known basin, while V is positive there.
Even steps preserve V. At an odd input before FIRST arrival, n>=3, so
  V(n)=(3n+1)/(4n)*V(U n) <=(5/6)*V(U n).
Thus 0<V(n)<=(5/6)^a<=1. The new kernel module proves the integer
strict prefix envelope
  3^(wt t n)*2^t*U^t(n) <=10^(wt t n)*n,
for positive prefixes avoiding one before time t. This avoidance cannot
be omitted: the odd input one does not have the strict factor 5/6.

The existing dyadic envelope, now specialized in a new kernel theorem,
gives t<=L+2A for any arrival from n<=2^L with a<=A. The kernel also
proves that endpoint plus the complete parity word determine the source,
and checks word length, binary entries, and odd count.

WRITTEN counting: encode the arrival length t and its at most A
one-positions, padded by zeros, using positions 1..t. With t<=L+2A,
this is an injection into (L+2A+1)^(A+1) tuples. Hence the number of
sources <=2^L with at most A odd inputs before first arrival is at most
that polynomial. No classification of other starts is used. This also
proves the natural mean of V is zero, by first fixing A and letting the
source cutoff grow, then letting A grow.

A binary refinement is called safe in the Lean module if it goes to
2n, or to 2n+1 when (2n,2n+1) eventually balances at a common time
and odd count. Kernel grade transport proves: a safe child of a
convergent root converges, with grade increased by one. Consequently
an uninterrupted safe descendant n of a fixed convergent root m at
depth k has grade g(m)+k and lies in [2^k*m,2^k*(m+1)). Thus
  V(n)>c_m=2^g(m)/(m+1)>0.
Choose A_m with (5/6)^(A_m+1)<=c_m. Its first-arrival odd count is
at most A_m, uniformly in depth. The tuple bound then shows there
are only polynomially many safe descendants versus 2^k binary choices.
The probability of remaining safe forever from any convergent root
is zero. The count and probability limits are written, not Lean formalized.

At root one c_1=1/2 and A_1=3. A separate KERNEL theorem proves the
stronger finite statement: n<2^(k+1), g(n)=k, and a FIRST arrival imply
a<=3. The proof yields 6^a<2*5^a, while 2*5^a<=6^a for a>=4.
Thus uninterrupted safe descendants from one number at most (k+8)^4
at depth k; their fraction is bounded by min(1,(k+8)^4/2^k).
This does not assert that an unsafe child fails to converge.

WRITTEN actual-interval consequence: let n_k(x)=floor(2^k*x) for
uniform x in [1,2), and let D_k be the event that the next bit is 1
AND the pair (2n_k,2n_k+1) never balances. Its measure is B_k/2,
where B_k is the fraction defined in the previous coalescence-tail note.
On S={only finitely many D_k}, all sufficiently late refinements are
safe. If such a path later visits a convergent prefix, it is then a
forever-safe chain from a convergent root. Section 3 makes each such
binary cylinder event null; the countable union over prefixes is null.
Thus on S the known-basin indicators of n_k tend to zero almost surely.
Dominated convergence gives
  limsup q_k <= P(D_k infinitely often),
where q_k is the known-basin fraction in [2^k,2^(k+1)). Positive lower
natural density delta at one implies limsup q_k>=delta. The replayed
external PLD theorem supplies delta>0, so the first Borel--Cantelli
lemma yields sum B_k=infinity. This uses NO natural-passage premise,
no natural-density existence, and no external coalescence-density-one
claim. If full Collatz holds, q_k=1 and the defects occur infinitely
often almost everywhere, while all actual infinite weights are zero.

This rules out the unweighted summability premise itself, not merely
the preceding whole-period upper-bound method. The prior implication
from sum B_k finite to d=0 remains logically valid but has a false
premise under the replayed input. The smaller actual weighted-change
sets could still be summable. A forward pointer in COALESCENCE-TAIL.md
and its document-only hash review record this development; no earlier
kernel theorem or finite replay changed.

Verification passed at 2026-10-12T21:00:26.609704+00:00. Fresh sequential
Lean 4.33.1 builds used compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Build times were 0.346s
CollatzPacking, 0.478s CollatzContradiction, 0.197s FirstPassagePacking,
0.212s FinitePathPacking, 0.923s EqualWeightFibres, 0.628s
CoalescenceGrades, and 0.298s DyadicCoalescenceDefects. Eighteen main
roots use standard propext/Classical.choice/Quot.sound or subsets;
grade_one has no axioms. No warnings, native computation, sorry, or
added axiom occurred. Twenty-two artifact/dependency hashes are recorded.
The prior records' 16 grade, 12 tail, and 15 weighted-loss hashes were
checked. All 389 external PLD module source/object/log hashes and its
lake manifest were revalidated. The completed external package and
its third-party caches were not rebuilt; this is the same adopted PLD
input, used only at one. All jobs are terminal with exit zero.

Finite checks:

- 524288 complete first-arrival integer bounds;
- 262144 doubling-grade identities and 311 leading-grade odd caps;
- 190 non-root safe descendants of one in the census;
- 4096 independent direct first-arrival paths and 205771 prefix bounds;
- 142 independently reversed parity-word certificates;
- 96 finite low-odd-count bounds and 944 direct Fraction comparisons;
- 379 safe leaf checks across roots 1,3,5,13,27 through depth 12.

At binary depth 18, there are 19 uninterrupted safe descendants of one
among 262144 possibilities. This finite count is not extrapolated to
an all-depth exact formula; the proved written bound is polynomial.
The auxiliary V mean there is approximately 0.00429495; exact rational
enclosures have width at most 2^-48. These values are NOT estimates of
d or W_infinity. All sampled starts explicitly reach one.

NEXT: actual weighted defects must exclude the many grade defects inside
the known basin. The unweighted Borel--Cantelli proxy is now ruled out.
Seek an actual-weight or finite-clock estimate that uses this distinction;
do not infer positive escaping mass from persistent unweighted defects.
Both zero escaping mass and other-cycle exclusion remain open. README
and ATTEMPT link the result and reproduction command. No staging,
commits, or Git writes were performed.

## 2026-10-12: quantitative auxiliary grade-weight moments

The preceding turn is classified as progress: it ruled out the actual
unweighted dyadic summability premise, with eighteen audited kernel roots.
This turn first returned to the weighted occupation and inverse-density
approaches. The exact inverse recursion still did not supply a uniform
upper bound over growing targets or a sharp logarithmic occupation bound.
The cached public basin manuscript was reviewed as context only: its
claimed inverse-linear floor, Green trace, and occupation assertions were
not replayed or adopted. No uniform C/N upper bound was proved or refuted.
The substantive new result is instead an unconditional power bound for
the auxiliary grade weight; it does not bound the remaining escape mass.

Added:

- docs/GRADE-WEIGHT-MOMENTS.md;
- lean/GradeWeightMoments.lean;
- verify_grade_weight_moments.py;
- results/grade-weight-moments/verification.json and replay.json;
- three fresh local Lean build logs in that result directory.

For the shortcut path x_t=U^t(n), with a_t odd inputs, define
  V_t(n)=2^t*x_t/(4^a_t*n).
An even step preserves V_t; an odd input x multiplies it by
(3x+1)/(4x)<=1. At x!=1 this is at most 5/6. Positive infinite paths
have infinitely many odd inputs, so the WRITTEN limit is the previously
defined arrival-grade V on the known basin, and zero on every orbit
never reaching one, including hypothetical other cycles and divergence.
Once one is reached the shortcut cycle preserves V_t exactly.

KERNEL integer moments: with 2^t*x_t=3^a_t*n+b_t, put
E_t=4^(t-a_t), P_t=3^a_t*E_t, Q_t=b_t*E_t. The new module defines
these recursively without rational arithmetic and proves their identities,
periodicity, envelope, and cross-multiplied monotonicity. The two next-bit
children sum to (7P,5E,7Q+2^t E). Over 0<=n<2^t it proves exactly
  sum P_t=7^t, sum E_t=5^t, 3*sum Q_t+7^t=10^t.
Periodicity permits the positive representatives 1..2^t instead.
All thirteen audited roots use standard propext/Quot.sound, with
Classical.choice also in the child and moment roots. No native evaluation,
warnings, sorry, or new axioms occur in the successful fresh builds.

WRITTEN quantitative deduction: V_t=P_t/4^t+Q_t/(4^t*n). If
c_t=Q_t/4^t then 0<=c_t/n<=1 and
sum c_t=((5/2)^t-(7/4)^t)/3 over the positive period. Split sources
at the real Y=(8/5)^t. The correction sum is at most Y+(sum c_t)/Y.
Consequently the mean of V_t on 1..2^t is at most
  (7/8)^t+(4/5)^t+(1/3)*(25/32)^t <= (7/3)*(7/8)^t.
Nonnegativity and monotonicity then give, for every integer X>=1,
  mean_(n<=X) V_T(n) <= (14/3)*X^(-eta),
  eta=log_2(8/7)=0.192645...,
whenever T>=ceil(log_2 X). The same bound holds for V_infinity.
This controls the actual initial interval, is uniform over all later
times, and uses no passage/density assumption or external PLD. The real
source split, powers, and limits are written, not additional kernel claims.
The associated dyadic amplitudes V(floor(2^k*x)) are summable for almost
every x in [1,2), by the integral bound and Tonelli. Their normalized
refinements have finite total amplitude variation; this does NOT imply
summability of the sets on which their exact values change.

The shortcut correction weight satisfies W_t=n*3^a_t/(2^t*x_t), hence
  V_t*W_t=(3/4)^a_t.
Small V_t gives no upper bound on W_t. V is positive on every convergent
start and can have zero mean even if full Collatz holds. Do not call the
new power bound a decay theorem for escape or for nonconvergent density.

A further WRITTEN criterion uses the actual escape refinements
h_k=2^k*W_infinity(floor(2^k*x))/floor(2^k*x). Under the prior natural
component law and external PLD, existence of a divergent orbit makes
the natural density lambda of divergence lie strictly between zero and
one. For any set E of natural density lambda, its dyadic-prefix indicators
converge weakly against L1 tests to lambda. Testing the set of paths with
only finitely many visits shows that set is null when lambda>0; apply the
same argument to the complement when lambda<1. Thus almost every binary
path switches between divergent and nondivergent prefixes infinitely
often. The uniform positive gap for W_infinity gives a squared h-increment
at least exp(-16384/3)/4 at every such switch. Therefore any divergent
orbit would force sum_k |h_(k+1)-h_k|^2=infinity almost everywhere.
A finite integrated squared-variation bound would exclude divergence,
but NO such bound is proved. The unconditional amplitude estimate above
is for V, not W. This criterion also leaves other cycles untouched.

Verification passed at 2026-10-12T21:35:23.422954+00:00 with pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Fresh
sequential build times were 0.372s CollatzAffine, 0.476s CoalescenceTail,
and 0.354s GradeWeightMoments. Fourteen new artifact/dependency hashes
were independently revalidated. The verifier also revalidated 22 dyadic,
12 coalescence-tail, and 15 weighted-dissipation hashes. It did not
rebuild external PLD or third-party modules; none is needed for the new
unconditional bound. All verification jobs have exited zero.

Independent finite replay checked:

- 2097150 affine data rows and the same number of positive-source weights;
- 1048575 paired next-bit moment identities;
- all twenty complete-period moment triples through depth 20;
- 41878 direct residue paths and 41858 exact Fraction dualities;
- 384 nonzero-quotient lifted data rows;
- 4096 first-arrival paths, 205771 monotonicity steps, and 101980 strict
  pre-arrival odd steps;
- 49152 known-cycle plateau steps.

At depth 20 and cutoff 1048576, the finite mean V_20 is enclosed between
0.06947364531946555 and 0.0694736453194691, with exact rational endpoints
and width below 2^-48. This is a finite-time auxiliary mean, not the
terminal V mean and not an escape estimate. The all-depth rate follows
from the identities and source split, not extrapolation of this number.

NEXT: return to actual W_infinity, or another estimate controlling p_1.
The auxiliary moment contraction has factor 7/8; its exact duality does
not transfer that contraction to W. A finite integrated squared-variation
bound is sufficient for excluding escape under the existing conditional
inputs, but no upper bound is currently available. Sharp occupation
control, vanishing escape mass, and exclusion of other cycles remain open.
The goal stays active. README and ATTEMPT include the result and command.
No staging, commits, credentials, installations, or Git writes occurred.

## 2026-10-13: actual escape-weight refinements and real-scaling rigidity

The previous turn is classified as progress: thirteen kernel roots and
the written initial-interval power bound quantified the auxiliary V, while
explicitly leaving the actual W uncontrolled. This turn returned to W.
It obtains finite-offset energy bounds, disproves two overly strong
contraction ideas, and removes an analytic premise from the sufficient
limiting-energy criterion. The needed bound itself is still unproved.
The full positive-integer Collatz goal remains active.

Added docs/ESCAPE-WEIGHT-REFINEMENTS.md,
lean/EscapeWeightRefinements.lean, verify_escape_weight_refinements.py,
and results/escape-weight-refinements/{verification,replay}.json with
three fresh local build logs. README and ATTEMPT include the new note
and reproduction command. Older checked source files and manifests were
not modified.

For shortcut x_t=U^t(n), odd count a_t, write
W_t(n)=n*3^a_t/(2^t*x_t), f_t=W_t/n. Define, for x in [1,2),
  n_k=floor(2^k*x),
  H_(s,k)(x)=2^k*f_(s+k)(n_k)=3^a_(s+k)/(2^s*x_(s+k)).
The integer offset s is fixed while k indexes binary refinement.
KERNEL even/odd path formulas yield the following WRITTEN rational
relations: the even child equals the parent exactly; the odd child is
3*2^k*f_(s+k)(3n_k+2). Both values lie in [0,1]. They are not a
martingale. With parent a and odd child b, the conditional squared
increment is (b-a)^2/2=(b^2-a^2)/2-a*(b-a); the drift has both signs.

KERNEL reciprocal affine moments: 2^t*x_t=3^a_t*n+b_t. Define
D_t=3^(t-a_t), Q_t=b_t*D_t recursively with integers. The two next-bit
children sum to (4D_t,6Q_t+2^t D_t). At every depth, over one period,
  sum D_t=4^t, 2*sum Q_t+6^t=8^t.
The scaled affine identity and periodicity are proved as well. Thus,
WRITTEN, c_t=b_t/3^a_t=Q_t/3^t has period 2^t and total
((8/3)^t-2^t)/2 over that period. Since 1-W_t=c_t/(n+c_t)<=c_t/n,
the actual-annulus mean L_(s,k) of 1-W_(s+k) satisfies
  L_(s,k) <= (1/2)*(8/3)^s*(2/3)^k.
For s>=1 the annulus lies inside one period; for s=0 it is a translated
whole period. In particular, for EACH FIXED s, H_(s,k)->1/x almost
everywhere and in L2 as k->infinity. No limit uniform in s follows.

WRITTEN energy: e_(s,k)=integral |H_(s,k+1)-H_(s,k)|^2,
E_s=sum_k e_(s,k). Compare H_(s,k) with g_k=2^k/n_k. The baseline
odd-child jump is <=2^(-k-1), and its deficit is <=1-W_(s+k).
Using the three-term square inequality gives
  e_(s,k) <= (3/8)*4^-k + (7/4)*(8/3)^s*(2/3)^k,
  sum_(k>=K) e_(s,k) <= (1/2)*4^-K + (21/4)*(8/3)^s*(2/3)^K.
Also e_(s,k)<=1/2, since even children do not change. Taking K=3s
gives E_s<=3s/2+23/4. This is an unconditional fixed-offset bound for
the ACTUAL W. Its linear dependence on s is insufficient for the needed
limiting-energy argument.

An actual infinite family rules out uniform decay of individual jumps.
For j>=1 set
  n_j=8*(64^j-1)/9, q_j=3n_j+2,
  k_j=6j-1, t_j=k_j+6=6j+5, A_j=3^(3j-1).
KERNEL formulas, with the divisible seed constructed for every j, give
  U^(t_j-2)(n_j)=A_j+1, odd_count=3j+1,
  U^(t_j-2)(q_j)=1, odd_count=1,
  2^k_j<=n_j<2^(k_j+1).
The first five steps from n_j reach 2^(6j-2)+1, then an exact affine
lift of the known cycle supplies the remaining path. q_j reaches a power
of two in two steps and halves to one. No long-term convergence claim is
made for ALL n_j. Only the stated finite trajectories are used.

At s=6 the odd child of n_j has normalized value 27/64. The parent is
9A/(16(A+1)) for even j, and 27A/(16(3A+5)) for odd j. A kernel
two-step bound for odd A>=9 yields, after written rational division,
  parent-minus-odd-child >= 27/512,
and the difference tends to 9/64. Thus maximum individual jumps do not
vanish even at fixed offset six. Their exhibited half-cells have summable
length, so this does NOT refute a uniform INTEGRATED energy bound.

The energies themselves are not nonincreasing in s. Exact finite rational
enclosures through k=12, combined with the WRITTEN tail bound for s=0,
prove E_0<1/7 and E_16>1/4. The certified upper/lower values used are
approximately 0.129820327955 and 0.258372418074. The latter is already
a finite partial sum; the former includes every later level via the
geometric tail. This disproves monotone energy contraction, not a larger
uniform bound or a bounded subsequence.

WRITTEN real-scaling rigidity removes the prior natural-passage premise
from the escape criterion. Let a(n) in {0,1} be U-invariant, and suppose
a(floor(2^k*x)) converges a.e. on [1,2). Its bounded measurable limit A
extends to all positive x with A(2x)=A(x). There is L1 convergence on
compact subintervals. Even-child invariance gives
||a(2*floor(2^k*x)+1)-a(floor(2^k*x))||_1
 =2||a_(k+1)-a_k||_1 ->0.
By the exact odd rule the first label is a(3*floor(2^k*x)+2).
Map each parent cell linearly with slope one into its corresponding
third cell. This map S_k has disjoint images, uniformly tends to 3x,
and has bounded pullback of L1 errors. Continuous approximation of A
therefore gives A(x)=A(3x) almost everywhere. In log_2 coordinates A
is periodic and invariant under irrational rotation log_2(3); Fourier
uniqueness makes it constant zero or one. L1 control of partial annuli,
not just complete annuli, then gives ordinary natural density zero or one.

Apply this to the divergence indicator. The previous WRITTEN packing
bound gives W_infinity>=exp(-8192/3) on divergence and W_infinity=0
elsewhere. A binary switch of the indicator costs at least
exp(-16384/3)/4 in squared normalized W increment. Thus finite squared
variation almost everywhere gives indicator stabilization. The rigidity
argument supplies density zero or one WITHOUT the natural-passage law.
If a divergent orbit existed, replayed PLD would give positive lower
density both to its predecessors at a unit target and to the known basin
of one, excluding both zero and one. Finite limiting energy would
therefore exclude escape using PLD and packing alone. The same rigidity
can be used for the indicator of failure to reach one, but no summability
bound for that stronger indicator is proved either.

For each fixed k, H_(s,k)->h_k=2^k*W_infinity(n_k)/n_k as s->infinity.
Fatou shows that liminf_(s->infinity) E_s<infinity would suffice for
finite integrated limiting energy. It is enough to find a bounded
subsequence at offsets tending to infinity; a supremum bound over all s
is stronger than needed. NEITHER is proved. Other positive cycles remain
unexcluded even if escape were removed.

The primary operator papers were reviewed at
https://arxiv.org/html/2106.11859v9 and
https://arxiv.org/html/2303.03203v1 . Their unweighted coefficient operator
does not equal the weighted 1/2,3/2 operator for f_t. The Hardy fixed-point
argument cannot be applied to f_infinity merely because f_infinity<=1/n.
Nonzero W_infinity is itself not square summable along a doubling ray.
No new operator theorem or other external result was adopted or replayed.

Exploratory prototypes /tmp/collatz_escape_energy.cpp and
/tmp/collatz_escape_energy_sample.cpp produced floating-point energy
data in the corresponding .csv files. The first enumerated through
level 19; the second used a fixed pseudorandom seed at larger levels
through 60. These estimates motivated investigating bounded energy, but
are NOT certificates for any uniform bound or asymptotic behavior.
Both prototype jobs exited zero. The exact new verifier supersedes their
finite scope for all quantitative claims made in the note.

Fresh verification passed at 2026-10-13T00:20:50.567988+00:00 with
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Sequential
builds took 0.360s CollatzAffine, 0.447s CoalescenceTail, and 0.492s
EscapeWeightRefinements. All twenty-one audited roots use only standard
propext/Classical.choice/Quot.sound or subsets, with no warnings, native
evaluation, sorry, or new axioms. Sixteen artifact/dependency hashes were
independently revalidated. Prior 14 grade-weight, 15 weighted-dissipation,
and 22 dyadic-defect hashes were revalidated. The external PLD record is
hashed and reused; its already replayed 389 modules and third-party
caches were not rebuilt this turn. All verification jobs are terminal.

Exact finite replay checked 524286 reciprocal affine rows, 262143 paired
moment identities, all eighteen complete-period moment pairs, 18825
independent direct paths, and 258 nonzero quotient lifts. It checked
128 jump-family members and 4092 independent two-step bounds. Energy
checks cover offsets 0,4,8,16,32,48,64 through level 12, with 114681
weight enclosures, 57337 binary energy cells, 665 independent Fraction
cells, and 91 mean-loss bounds. Enclosures use scale 2^60, not floats;
floating-point numbers are display-only. The all-depth tail and rigidity
argument remain written, not additional Lean claims.

NEXT: pursue a bounded subsequence of E_s at arbitrarily late offsets,
or a direct limiting-energy bound. Do not infer it from finiteness at
each fixed offset or from exploratory O(1)-sized samples. A martingale
argument, monotone contraction in s, and uniformly small individual
jumps are unavailable as stated. The exact drift term in the energy
identity is a possible next quantity to control on average. No escape
exclusion, other-cycle exclusion, staging, commits, installations,
credentials, or Git writes occurred. The goal remains active.

## 2026-10-13: coalescence energy caps and their unavoidable growth

The preceding completed refinement turn is progress: it gave twenty-one
kernel roots, actual-weight bounds, and a stronger written rigidity
criterion. The intervening drift, time-average, and weighted-operator
investigations did not establish the needed bounded subsequence. The
current milestone is progress: it supplies a sharper valid energy bound
and proves that a proposed method of improving it cannot remove its
growth. Full positive-integer Collatz remains unresolved and active.

Added docs/COALESCENCE-ENERGY-CAPS.md, lean/CoalescenceEnergyCaps.lean,
verify_coalescence_energy_caps.py, and results/coalescence-energy-caps
with verification/replay JSON and four fresh local build logs. README
and ATTEMPT include the result and reproduction command. Prior checked
modules, notes, and manifests were preserved.

Write p_H^(0) for balanced coalescence of even adjacent residues at
depth H, and q_H=(1-p_H^(0))/2. KERNEL persistence, refinement data
equality, and exact repeated-period counts on every dyadic source
annulus give the WRITTEN energy cap
  e_(s,k) <= q_H for every s>=0 and 1<=H<=k+1.
The depth is limited by the actual source period, not by the potentially
much longer evaluation time. The even child equals the parent; balanced
pairs have exactly equal odd-child data as well. Other jumps have square
at most one. No infinite-time fusion assumption is used.

A new independent direct census through depth twenty, without the old
high-bit lift recursion, reproduces all prior parity-conditioned counts:
  p_20^(0)=289565/524288, q_20=234723/1048576,
  sum_(H=1..19)q_H=699653/131072.
These are Python finite checks, not kernel evaluations of a million
residues. All-depth source transport is separately kernel proved.

KERNEL J(s)=ceil(121s/50) satisfies 121s<=50J<121s+50 and
  2^(3s+J(s)) <= 3^(s+J(s)).
The proof uses 2^271<=3^171 and fifty exact remainder cases, all kernel
decide, without native_decide. It follows WRITTEN that
(8/3)^s*(2/3)^J<=1. Split the energy at K=19+J, sum the first nineteen
caps, use q_20 for the next J levels, and apply the prior geometric tail:
  E_s <= (699653/131072)+(234723/1048576)*J(s)+T_19,
  T_19=(1/2)*4^-19+(21/4)*(2/3)^19.
The exact additive constant after bounding J is approximately 5.5641463,
giving E_s <= (28401483/52428800)*s+6 <= 0.542*s+6.
This improves the earlier 1.5*s+5.75 bound for sufficiently large s,
but is still insufficient for the limiting-energy criterion.

The WRITTEN obstruction concerns the strongest levelwise certificate
from these two estimates, not the actual energy:
  B_s=sum_k min(q_(k+1), (3/8)*4^-k+(7/4)*(8/3)^s*(2/3)^k).
For k<=2s the tail expression exceeds 1/2, so the minimum is q_(k+1).
The old kernel harmonic bound gives B_s >= (1/2)*sum_(j<=2s+1)1/j.
The old WRITTEN walk comparison sharpens this to
  B_s >= (2s+1)*binomial(2s,s)/4^s-1/2 ~ 2*sqrt(s/pi).
The central-binomial finite-sum identity is written and independently
checked on 257 finite cases. Thus B_s and its Cesaro means diverge even
if exact coalescence counts at EVERY depth were available. This does
NOT show E_s diverges. Actual unmerged weights can be small or zero.
Next work must retain those weights, or add information beyond these
caps and this tail; deeper full-period counts alone cannot suffice.

For any fixed H, the same argument bounds limsup E_s/s by (121/50)*q_H.
If an additional theorem establishes p_H^(0)->1, this would imply
E_s=o(s), still insufficient. That coalescence limit was not adopted.
The cited Said Duran/Gao pages at Zenodo records 23003524 and 23003500
were inaccessible through the web tool; no source was downloaded or
replayed and no external result was added. The already cached basin
manuscript remains unadopted. The unrelated OpenAI multiplicative
two-point-correlation result was not used.

KERNEL even-pair obstruction: the first POSITIVE time of equal odd
counts for 6,7 is eleven; the endpoints are then 2,1 and both counts
are five. The pair never has equal endpoints at a common clock, hence
is never balanced, although both starts reach one. For every q>=0,
the pair 2048q+6,2048q+7 has its first positive count equality at eleven
with endpoints 243q+2,243q+1 and counts five. Its stopped gap is zero
but its noncoalescence indicator is one. This one residue class is
1/1024 of even inputs modulo 2048. Eternal nonfusion is asserted only
for q=0. Equal-count absorption cannot replace actual fusion in a cap.

WRITTEN exact drift formulation: the ordinary partial-sum limit
  D_s=lim_m sum_(k<m) integral H_(s,k)*(H_(s,k+1)-H_(s,k))
exists, since the finite energy identity telescopes and fixed-offset
H_(s,k)->1/x in L2. It satisfies E_s=1/2-W_s(1)^2-2D_s.
Absolute convergence of the drift series is not asserted. A lower bound
on D_s along arbitrarily late offsets, or bounded Cesaro energy means,
would suffice for the existing bounded-subsequence criterion; both
remain unproved. Other positive cycles remain a separate open gap.

Fresh verification passed at 2026-10-13T07:39:26.462211+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Builds
were sequential: CollatzAffine 0.370s, CoalescenceTail 0.444s,
EscapeWeightRefinements 0.495s, CoalescenceEnergyCaps 0.221s. All seventeen
new roots have standard axioms only, with no native evaluator, sorry,
warnings, or added axioms. The new record has sixteen artifact hashes;
twelve coalescence-tail and sixteen actual-refinement hashes were also
revalidated. Subsequent note-only formula-formatting corrections and a
non-strict decimal comparison did not change code or theorem statements;
the record explicitly refreshes that one documentation digest.

Finite checks: 20,971,540 exact shortcut updates; 2,097,150 adjacent
residue comparisons; 4,103 first-return lifts including 2048-bit inputs;
4,096 base-pair clocks; 24,570 independent rational refinement cells at
offsets 0,7,16,32,64,128 and levels 0..11; 1,024 cutoff instances; and
257 walk-tail sum identities. All jobs exited zero. No installation,
credentials, staging, commits, or other Git writes occurred.

Exploratory follow-up after this certificate (NOT incorporated into its
verified scope): /tmp/collatz-first-count-return-moments.json contains
exact finite prefix-tree moments of endpoint separation at the first
positive equality of odd counts. Through depth twenty, conditioning on
an initial even input, the returned mass is 391079/524288, absolute
distance moment 364626/524288, and squared-distance moment
2700594/524288. The latter already exceeds one. Initial-odd values are
402074/524288, 740776/524288, and 4593136/524288 respectively.

A second exploratory state aggregation in
/tmp/collatz-count-return-state-moments.json matched those prefix data.
Until count equality, orient the lower-count endpoint as x and write
the higher-count endpoint as y=3^d*x+c, d>=1. The two fair endpoint
parities give these transitions:
  c even: (d,c/2), (d,(3c+1-3^d)/2);
  c odd:  (d+1,(3c+1)/2), (d-1,(c-3^(d-1))/2).
Initial states are (1,2) for an even pair and (1,-1) after swapping an
odd pair. At d=0 the signed offset is the return separation. The tested
invariant c<=3^d-1 gives c<=0 at return. The aggregated finite even
absolute-distance numerator already exceeds its probability denominator
at depth 27: 68790693/67108864. This calculation stopped both branches at
its planned 400000-state threshold and exited 0; their last recorded
moment rows are at depth 28.
It is not a verified all-depth moment or contraction result. Retaining
only unweighted separation moments looks inadequate for the desired
energy bound; any further use needs an exact bridge and actual weights.

Potential next algebraic input: U(n)+1=3^(n mod 2)*(floor(n/2)+1).
If y+1<=P*(x+1), then floor(y/2)+1<=P*(floor(x/2)+1).
Together these preserve y+1<=3^d*(x+1) while the count difference d
stays nonnegative, proving the observed endpoint order at first return.
This was derived on paper only in this follow-up, not added as a new
kernel theorem or used to claim an energy estimate. The missing weighted
cancellation, escape exclusion, and remaining-cycle exclusion are open.

## 2026-10-13: summable ordered drift and the remaining count reversals

The preceding turn is classified as progress: it established the sharper
energy caps and a verified obstruction to using those caps with the old
tail to get bounded energy. This turn is also progress. It controls an
infinite part of the ACTUAL weighted drift, and proves why the same
pointwise charge cannot cover its complement. Collatz is still unresolved;
the active goal is neither completed nor blocked.

Added docs/ORDERED-WEIGHT-DRIFT.md, lean/OrderedWeightDrift.lean,
verify_ordered_weight_drift.py, and results/ordered-weight-drift with
verification/replay JSON and four fresh local build logs. README and
ATTEMPT include the result and reproduction command. Older checked
source files, notes, and manifests were preserved.

For positive n, put f_t=3^a/(2^t*x_t) and z_t=3^a/(2^t*(x_t+1)).
KERNEL U(x)+1=3^(x mod 2)*(floor(x/2)+1). The WRITTEN fractions give
two decreasing sequences: f loses f/(3x+1) on odd inputs and zero on
even inputs; z loses f*x/((x+1)(x+2)) on even inputs and zero on odds.
For n_k=floor(2^k*x), write A_(s,k)=2^k*f_(s+k)(n_k)=H_(s,k),
Z_(s,k)=2^k*z_(s+k)(n_k), and g_k=2^k/n_k. Both refinements copy
their even children. They satisfy 0<Z<=A<=g<=1 on the source annulus.

Call the pair 2n,2n+1 ordered through T when its odd member's count b_i
has never fallen below its even member's count a_i for 1<=i<=T.
KERNEL all-depth propagation gives Y_T+1<=3^(b_T-a_T)*(X_T+1).
It also proves Y_T<=X_T at the first positive return of equal counts,
without identifying count equality with fusion. The exact cross product
then gives, WRITTEN, A*(A-B)_+<=A^2/(X+1), where B is the odd child
and X the parent endpoint. This is bounded by
  3*(A_(s,k)-A_(s+1,k))+2*(Z_(s,k)-Z_(s+1,k)).
The kernel checks the reciprocal cross inequality and the elementary
denominator bounds used here.

KERNEL shifted affine correction: R_t=Q_t+2^t*D_t, with the earlier
D=3^(t-a), Q=b*D, has period 2^t and satisfies
  D_t*2^t*(x_t+1)=3^t*n+R_t,
  2*sum_(n<2^t)R_t(n)+6^t=3*8^t.
WRITTEN source-annulus bounds give finite deficits
  M_s=sum_k integral(g_k-A_(s,k)) <= J(s)+3/2,
  Mtilde_s=sum_k integral(g_k-Z_(s,k)) <= J(s)+9/2,
where J(s)=ceil(121s/50) uses the previously checked cutoff. The ordered
negative drift N_ord_s is at most (3/2)*(M_(s+1)-M_s) plus
Mtilde_(s+1)-Mtilde_s. Thus its first S offsets sum to at most
(5/2)*J(S)+27/4 < (121/20)*S+37/4. This estimate is valid but is
superseded by the stronger summable bound below.

KERNEL positive-offset transitions: in an ordered downward refinement,
write Y=3^d*X+c. Initially (d,c)=(1,2). Odd parent steps keep that
state. The first even parent step gives (1,1). Subsequent even steps
alternate (d,1)->(d+1,2) and (d,2)->(d,1). An odd step after the first
even gives Y'<=3^d'*X', so closes the negative difference. KERNEL
unshifted order persists while the count difference remains nonnegative.
The WRITTEN induction therefore confines every ordered downward cell
at parent time t to a parity word 1^L 0^(t-L).

KERNEL exact count: precisely k+1 residues at depth k have a parity word
consisting of an initial odd run followed by even steps; the same count
holds on [2^k,2^(k+1)). Two next-bit children have opposite final
parities. The count recurrence is c_(k+1)=c_k+1, since appending zero
keeps every admissible prefix while appending one keeps just the unique
all-odd prefix. This is an all-depth proof, not a census extrapolation.

WRITTEN source clock: a positive n in that annulus with word 1^L0^(t-L)
satisfies 2^t*U^t(n)+2^L=3^L*(n+1) and 2^L divides n+1. Hence L<=k+1,
2^t<2^(3k+3), and t<=3k+2. For t=s+k, any ordered downward cell thus
requires s<=2k+2. Since A*(A-B)_+<=1, its integrated level contribution
is at most (k+1)/2^(k+1). Nonnegative sums give the strongest new bound
  N_ord_s <= 2 for all s,
  sum_(s>=0) N_ord_s <= sum_k (2k+3)*(k+1)/2^(k+1) = 14.
Also N_ord_s <= (K+2)/2^K for K=max(0,ceil(s/2)-1). It tends to zero
exponentially. The classification induction, height deduction, and real
summation are WRITTEN, using the new finite-step and counting kernels.
No PLD, passage law, or other external input is used for this estimate.

The full fixed-offset drift series is now shown WRITTEN absolutely
convergent: the earlier geometric bound makes sum_k sqrt(e_(s,k))
finite, and Cauchy--Schwarz bounds each absolute drift integral by that
square root. The old note only asserted ordinary convergence, which
remains true. This is not a bound uniform in s.

N_rev_s is the complementary negative drift from cells whose odd-count
order has reversed at some earlier or current clock. The energy identity
gives E_s<=1/2+2*N_ord_s+2*N_rev_s. Thus bounded Cesaro means of N_rev
along an unbounded sequence of offset counts would suffice for the prior
bounded-energy-subsequence criterion and, using prior packing and the
replayed external PLD, exclude escape. This estimate is OPEN. It is a
sufficient criterion, not asserted necessary: positive drift might also
cancel an unbounded negative part. Other positive cycles remain open.

KERNEL n=37,k=5,s=6 has reversed pair counts 5,4 and endpoints 5,2;
its downward values are 243/320 and 81/128. Both sources reach one.
A KERNEL specialization of the earlier jump family gives a stronger
WRITTEN obstruction to an immediate parent-loss estimate. For even j>=2,
  n=8*(64^j-1)/9, k=6j-1, s=6, Astar=3^(3j-1),
the parent endpoint is the odd number (Astar+1)/4, its count is 3j+1,
and the odd child's count at the matched pair clock is three. The parent
value P=9*Astar/(16*(Astar+1)) and child B=27/64 satisfy
  P*(P-B)/(P-A_(7,k))
    =9*(Astar-3)*(3*Astar+7)/(256*(Astar+1)) -> infinity.
The shifted parent loss is exactly zero. P*(P-B)->81/1024 while the
unshifted loss tends to zero. Thus NO fixed multiplier of the two
immediate parent losses bounds all reversed downward cells. The family
half-cells have summable lengths, so this does not refute an INTEGRATED
bound. No universal eventual behavior of that family is asserted.

Fresh verification passed at 2026-10-13T14:22:16.286386+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All
31 audited new roots use standard axioms only, with no warnings, sorry,
native evaluator, or new axioms. The four builds were sequential.
Sixteen hashes in each of the preceding refinement and energy-cap
records were revalidated. No external replay or installation was needed.

Independent exact checks covered 1048576 adjacent pair clocks, 805599
ordered endpoint/cross-product checks, 6820 first positive count returns,
32770 ordered negative parity/height checks, 524287 shifted affine rows,
524287 annulus parity rows, 405 nonzero quotient lifts, all moment and
one-turn counts through depth 18, 200606 rational refinement/time-loss
cells, 157635 ordered time charges, 2156 annulus deficit bounds,
97 cumulative budgets, 64 even-indexed jump-family members, and 1024
cutoff/constant checks. Integrated finite sums use rational enclosures
at scale 2^64; floats are display-only. These checks do not establish
any late-offset bound on N_rev. Every verification job is terminal.

The external basin repository's current README was reviewed through
the web tool, including newer stationary-density claims. None was
replayed or adopted, and none is an input to the new result.

NEXT: control the actual reversal contribution over source intervals,
or its cancellation with positive drift. Do not revisit the ordered
part as though it were still an unbounded error. A uniform pointwise
charge to the parent's next time step is impossible by the family above.
Earlier unweighted first-count-return distance moments are also not
contractions; any induced-pair estimate must retain the actual weights.
The full Collatz goal remains active. No staging, commits, credentials,
installations, or other Git writes occurred.

## 2026-10-13: persistent reversals require averaging across source cells

This follow-up is progress, not completion of the Collatz goal. It proves
a stronger obstruction to the parent-loss approach and records a precise
remaining averaging question. Escape and additional cycles remain open.
The prior ordered-drift result and its verification record were preserved.

Added docs/REVERSAL-PERSISTENCE.md, lean/ReversalPersistence.lean,
verify_reversal_persistence.py, and results/reversal-persistence. README
and ATTEMPT link the result and reproduction command. Eight new kernel
roots use standard axioms only. No new external theorem was adopted.

KERNEL, for all h,x, with a=wt(h,x), y=U^h(x):
  3*2^h*y+3^a <= 3^a*(3x+2^h),
  2^h*(y+1) <= 3^a*(x+2^h).
WRITTEN these give W_h(x)>=3x/(3x+2^h-1), z_h(x)>=1/(x+2^h).
For a parent value P at endpoint X and its shifted value Z=PX/(X+1),
after h more steps the cumulative parent charge satisfies
  3*(P-P_h)+2*(Z-Z_h) <= 3P*(2^h-1)/X.
It tends to zero whenever 2^h/X tends to zero, not only at fixed h.

Use the prior family, even j>=2:
  n=8*(64^j-1)/9, k=6j-1, R=3^(3j-1), X=(R+1)/4.
At s=6 its parent is P=9R/[16(R+1)] and its odd child B=27/64.
Set H=3j-5. KERNEL: for every 0<=h<=H, 4*2^h<=X,
the actual parent at offset 6+h is >=1/2, the actual odd child is
<=27/64, and the history includes a count reversal. The parent lower
bound and child ceiling are checked as integer cross products of actual
orbit/weight expressions, not just arithmetic on assumed endpoints.

WRITTEN each such cell has negative product >=5/128 and square gap
>=25/4096. The 3j-4 consecutive offsets therefore have accumulated
negative drift >=5*(3j-4)/128. Yet the entire future parent charge
telescopes to at most 3P+2Z<45/16, regardless of the parent's eventual
behavior. No uniform multiplier can charge a cell's accumulated drift
to all that parent's future losses; it would have to exceed (3j-4)/72.
Also no fixed lookahead charges the initial jump, whose negative product
tends to 81/1024. Even the displayed linear-in-bit-length horizons fail
to charge the initial jump, since 2^H/X tends to zero. Thus replacing
the failed immediate charge with a bounded block is insufficient.

The guaranteed persistence rectangles have total source/offset measure
sum_(m>=0)(6m+2)/2^(12m+12)=2q(1+2q)/(1-q)^2, q=2^-12, finite.
This is only the measure of the stated finite horizons. It is NOT a
proof of all-time integrability of this family's contribution. These
obstructions still do not disprove an averaged source-interval bound.

Precise OPEN sufficient estimate: let L_(s,k) be the sum of
3*(A_(s,k)-A_(s+1,k))+2*(Z_(s,k)-Z_(s+1,k)) over all parent sources
2^k<=n<2^(k+1), multiplied by the half-cell length 2^(-k-1).
If N_rev_(s,k)<=C*L_(s,k) uniformly, the earlier deficits give
sum_(s<S,k)L_(s,k)<=(5/2)*ceil(121S/50)+27/4. Together with the
ordered total <=14, this yields the WRITTEN conditional conclusion
limsup_S (1/S)*sum_(s<S)E_s <= 1/2+121C/10. This would feed the prior
escape criterion, but no such C is proved and other cycles remain open.

Independent exact finite annulus checks support C=8 only on
0<=k<=10, 0<=s<=96. They certify that C=6 already fails at k=5,s=46,
where the exact ratio is approximately 6.607568163248772. Decisions
use fractions and rational enclosures at scale 2^64; decimals are
display-only. This is not evidence of a verified all-level constant.

Fresh verification passed at 2026-10-13T15:10:45.976999+00:00 on
pinned Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All five local modules were freshly compiled sequentially. The eight
new roots use only propext/Quot.sound; no warnings, sorry, native
evaluation, or extra axioms. All 16 prior ordered-drift hashes were
revalidated. New independent checks cover 528384 endpoint clocks,
36876 retained-half comparisons, 64 family members and 12224 persistent
offset cells, 198559 rational annulus cells, and 1067 finite C=8 bounds.
The first replay reached all checks but hit Python's decimal-digit limit
when serializing huge exact sum denominators. Cumulative family sums
were changed to exact rational enclosures, and the full replay passed.
This was a reporting-size issue, not a failed mathematical inequality.

Uncertified exploratory files, NOT inputs to the result:
/tmp/collatz-reversal-average-charge.cpp and its two CSV outputs scan
floating normalized weights through k=20,s=1024. The levelwise maximum
ratio there decreases from 6.607568 at k=5 to about 1.02274 at k=20.
There is no all-level estimate. /tmp/collatz-time-area-samples.py and
its JSON sample 2000 sources at each bit length 20,40,80,160,320,640,1280.
Exact integer trajectories but floating weight sums give mean all-time
per-level energies approximately 3.47,4.32,5.77,7.44,8.54,10.39,10.15;
all samples reached {1,2}, with an explicit two-step geometric tail.
These samples are not a uniform bound, nor a proof about untested sources.
Do not mistake time summability at every cell for an easy substitute:
it would already force equality of the limiting adjacent weights.

The external basin manuscript and quadratic-cylinder-energy manuscript
were browsed again for quantitative coalescence or occupation input.
No newly reviewed claim was replayed or adopted. Zenodo 23003500 and
the GitHub formal-periodic-census directory/README remained inaccessible
through the web tool. The former source's almost-sure inverse-height law
explicitly lacks the expectation/occupation upper bound needed to close
its separate route. Its Haar stationary-density claims concern a
different measure from actual integer trace values.

NEXT: attack the whole-source averaging estimate or signed cancellation.
Do not retry immediate, fixed-block, or cell-by-cell total-future loss
charges: the new all-parameter family rules them out. The ordered part
is already summable. All verification jobs have terminated; no agents,
installations, staging, commits, or credentials were involved.

## 2026-10-13: count-return control and sublinear actual energy

The previous reversal-persistence turn was progress and its fourteen
recorded hashes were revalidated at this turn's start. This turn makes
further progress: a new WRITTEN probability argument bounds repeated
count-gap restarts and gives actual energy E_s=O(s^(4/5))=o(s).
This is not bounded energy, escape exclusion, or a solution of Collatz.
The full goal remains active; no blocked condition has been declared.

Added docs/COUNT-RETURN-CONTROL.md, lean/CountReturnControl.lean,
verify_count_return_control.py, and results/count-return-control.
README and ATTEMPT describe the result and reproduction command.
The twelve kernel roots are arithmetic inputs. The stopping-time,
fractional-moment, finite-set, probability, and real-energy proofs are
WRITTEN, not completely Lean formalized. No external coalescence theorem
was assumed, installed, or replayed, and no novelty claim is made.

The probability law is Haar-uniform binary input, equivalently uniform
complete residue periods. After any exposed prefix, both endpoints are
odd affine functions of the remaining Haar input. Each marginal next
parity is fair; the pair is dependent. Countably partitioning by finite
prefixes gives the same property at an almost-surely finite stopping time.
These are not probabilities uniformly sampling all positive integers.

KERNEL exact unstopped gap accounting: the two next-bit absolute gaps
sum to twice the current absolute gap, plus two exactly when the current
gap is zero and the endpoint parities differ. Thus the normalized
full-period first moment increases by the departure-from-zero probability.
This includes all restarts, unlike the old stopped-gap identity.

WRITTEN uniform first positive count-return tail:
  Pr(tau>H) <= 16 H^(-1/5), for every starting separation D>0.
While counts differ by d>=1, orient Y=3^d X+c. The lower-count endpoint
X is conditionally Haar. Holding for h steps is equivalent to
  (3^d-1)X+c == 0 mod 2^h.
If v=nu_2(3^d-1), this event has probability <=min(1,2^(v-h)).
KERNEL 0<3^d-1<2^(2d), so v<=2d-1. The expected clock until the next
active gap step is <=v+2<=2d+1, uniformly in c. The active gap is a
simple symmetric walk absorbed at zero. Up to m active steps it has
physical expected clock <=3(m+1)^2 and survival <=2/sqrt(m+1).
Markov with m=floor(H^(2/5)) yields the displayed tail and proves the
first return is finite almost surely. An initial even separation returns
after one step; an odd one departs to absolute gap one.

WRITTEN stopped moment, with all stopping justified rather than inferred
from fixed-time bounds: U^t(X)=lambda_t X+B_t,
lambda_t=3^a/2^t, B_(t+1)=m_t B_t+epsilon_t/2. Marginal parities are
independent fair bits. At alpha=1/2, r_alpha<31/32 gives E B_t^alpha<=16.
For beta=1/16, Holder on dyadic events 2^(j-1)<tau<=2^j gives
E[B_tau^beta; event] <=64*2^(-j/20). The tau=1 contribution is <=2;
sum 2^(-j/20)<50, so E B_tau^beta<=3202 for either endpoint, uniformly
in D. The nonnegative supermartingale lambda_t^beta and optional stopping
give E lambda_tau^beta<=r_beta<509/512. At equal counts the slopes agree,
so the new separation D' satisfies the WRITTEN drift inequality
  E[(D')^(1/16) | D] <= (509/512) D^(1/16)+6404.
No independence between the two corrections is used.

WRITTEN finite expected number of count-return cycles:
take V(D)=D^(1/16), R=1093120^16<2^336. Outside D<=R, the drift is
at most -1, so expected return cycles to that finite set are <=V(D).
KERNEL prescribed descent transitions: for even D choose both even to
get D/2. For odd D choose the lower endpoint even to obtain count gap one
and c=(3D+1)/2; keep choosing both even until c is odd, then choose the
lower-count endpoint odd. This first count return has D'=(c-1)/2<=
(3D-1)/4. Thus prescribed returns decrease separation by factor <=3/4.
From D<=R, 1344 returns suffice for fusion, using <=338 bits per return.
The success probability is >=2^(-454272). After an attempt, expected
V is <2186070. Including the next visit to D<=R, each attempt has
expected length <=2187414 return cycles. Conditional success is uniformly
positive, so from adjacent starts the expected number N of return cycles
until balanced fusion is bounded by
  C_star = 2187414 * 2^454272.
This enormous explicit constant is finite; no numerical optimization is
claimed. The integer comparisons for all constants are kernel checked.

WRITTEN consequences:
  E|a_t(x)-a_t(x+1)| <= C_star for every complete-period depth t;
  1-p_H <= 21*C_star*H^(-1/5).
For the latter, E min(tau,H)<=21H^(4/5) uniformly at each return. Whether
cycle j is needed is determined before it starts. Conditional expectation
and Tonelli therefore bound E sum_(j<=N) min(tau_j,H) by
21*C_star*H^(4/5); on T>H this sum is >=H. This avoids any independence
assumption about return times or the number of returns. Conditioning on
either first parity doubles these bounds. The existing H^(-1/2) lower
bound and infinite physical mean coalescence clock are compatible.

Apply the old KERNEL actual-annulus cap e_(s,k)<=q_(k+1), where
q_H=(1-p_H^even)/2, plus its WRITTEN geometric tail. For
J(s)=ceil(121s/50), the new WRITTEN actual energy bound is
  E_s <= (105/4)*C_star*J(s)^(4/5)+23/4.
Thus E_s=o(s), without adopting any new external result. The old
0.542s+6 bound remains much better at practical offsets because C_star
is huge. Neither estimate supplies a bounded-energy subsequence.

Fresh verification passed at 2026-10-13T15:49:07.064642+00:00 using
pinned Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Four local modules were freshly compiled sequentially. All twelve new
roots use standard axioms only; no warnings, sorry, added axioms, or
native evaluation. The sixteen energy-cap and fourteen reversal-persistence
hashes were revalidated. No previous source or manifest was rewritten.

Independent exact checks: 131056 actual pair residue paths, 208 complete
state distributions for initial separations 1..16 through depth 12,
25 exact raw-gap recurrences through depth 24, 216189 state nodes,
270072 holding-prefix/congruence comparisons, 1320 exact congruence counts,
and actual balanced-fusion witnesses for every separation 1..8192. Those
witnesses use 173305 prescribed bits and 86026 strictly descending return
cycles in total; maximum witness clock 33 and return count 19. They were
recomputed as actual integer orbits, not only as offset-state transitions.
The full adjacent depth-24 law has raw gap mass 32206350, restart mass
421301, and balanced mass 6966495 over denominator 16777216. Finite checks
do not substitute for the all-depth probability proof.

Uncertified exploration retained in /tmp/collatz-full-gap-moments.json
(initial even branch, state aggregation through 29 further clocks) and
/tmp/collatz-full-gap-samples.json (5000 random state paths, seed
2026101302, through 32768 clocks). The samples suggested bounded mean
restart count and motivated the fractional-moment argument; neither file
is an input to the new theorem or verification record.

NEXT: use the uniform FULL count-gap moment and return-separation moment
to control the actual weighted reversal contribution, or its signed
cancellation, across source intervals. Do not treat the old stopped-gap
mean-one identity as if it included restarts. Optimizing the unweighted
coalescence exponent alone cannot establish bounded energy: the earlier
cap-plus-tail obstruction still applies. Full escape and cycle exclusion
remain open. All checks are terminal; no agents, staging, commits,
installations, credentials, or other Git writes were used.

## 2026-10-13: actual-annulus logarithmic height coupling and return transport

The preceding count-return turn was progress; its fourteen recorded
hashes were revalidated before use. This turn is progress as well: it
transfers the full count-gap control to actual real endpoint heights,
adds a cumulative return-separation budget, and identifies the exact
arithmetic-progression factor in a prospective weighted-energy transfer.
The full Collatz goal remains active and unresolved.

Added docs/ANNULUS-HEIGHT-COUPLING.md, lean/AnnulusHeightCoupling.lean,
verify_annulus_height_coupling.py, and results/annulus-height-coupling.
README and ATTEMPT link the result and reproduction command. Twelve
new kernel roots cover integer height and count identities. Logarithm,
threshold, probability, and cumulative-return consequences are WRITTEN.
No new external theorem or package was used.

Let t>=1, N=2^t, m=N+2r for 0<=r<N/2, X=U^t(m), Y=U^t(m+1),
and a,b their odd counts. These are actual even/odd refinement pairs
at source level k=t-1 and offset zero, not arbitrary later clocks.
Set u=X/3^a, v=Y/3^b. The KERNEL normalized-height comparison gives,
after WRITTEN division,
  mean |u-v| <= (2/3)^t,   u,v>=1.
It uses the earlier exact correction moment
2*sum_(n<N)Q_t(n)+6^t=8^t. The checked integer form is
  2^(t+1)*sum_(r<N/2)|h_t(N+2r+1)-h_t(N+2r)| <= 8^t,
where h_t(n)=3^(t-a_t(n))*U^t(n). Height lifts add the same 3^t*q
to both scaled endpoints, so the gap transports exactly to the annulus.
The individual difference is bounded by the two nonnegative affine
corrections plus the source increment; the correction moment cancels
the remaining source-increment term in the complete even/odd sum.

WRITTEN log comparison, because u,v>=1:
  mean |log(Y/X)-(b-a)*log(3)| <= (2/3)^t.
The earlier full-gap bound conditioned on even input yields
  mean |log(Y/X)| <= 2*C_star*log(3)+(2/3)^t.
Equivalently, integrate over all logarithmic height thresholds z the
probability that exp(z) lies between X and Y; that total disagreement
has the same uniform bound. This gives an actual height-coupling budget.
It does not claim future weight is a monotone function of height.

KERNEL signed count mean is exactly one: mean(b-a)=1 on every such
actual annulus. Hence WRITTEN
  |mean log(Y/X)-log(3)| <= (2/3)^t.
Meanwhile the earlier written coalescence rate gives probability
log(Y/X)!=0 <=42*C_star*t^(-1/5), tending to zero. These logarithmic
differences are therefore NOT uniformly integrable, even though their
first absolute moment is bounded. For every 0<theta<1, Holder gives
mean |log(Y/X)|^theta=O(t^(-(1-theta)/5)). Do not replace the first
moment bound by first-mean convergence; its signed limit is log(3).
None of this lower-bounds actual refinement energy.

Additional WRITTEN return budget under the Haar binary law: let D_j
be the separation at count-return cycle boundaries, D_0=1, with N
cycles until fusion. Applying the earlier drift with absorption at zero
and telescoping deterministic truncations gives
  E sum_(j<N) D_j^(1/16) <= (512/3)*(1+6404*C_star).
Also log(1+D)<=16D^(1/16), so the total expected logarithmic separation
cost over all these returns is finite. This is NOT asserted for a
finite uniform integer interval followed indefinitely past the end of
its source bits. The distinction between those laws remains essential.

Exact return transport: if r,r+1 first have equal counts a at clock tau
and endpoints x0,y0, then for every q>=0 their lifted endpoints are
  X(q)=3^a*q+x0, Y(q)=3^a*q+y0.
With lambda=3^a/2^tau and f_h(n)=3^a_h/(2^h U^h(n)), the difference
at clock tau+h is lambda*(f_h(X(q))-f_h(Y(q))). For source annulus
[A,2A), A=2^K,K>=tau, a fixed even prefix has q=Q..2Q-1, Q=A/2^tau.
Put M=3^a Q=lambda*A. Its normalized squared contribution is
  lambda*M*sum_(q=Q..2Q-1) G_h(3^a*q+x0)^2,
where G_h(x)=f_h(x)-f_h(x+y0-x0).
The endpoint sample is one progression of spacing 3^a inside an interval
of length M. To recover the binary branch factor 2^(-tau) by interval
averaging requires paying for that spacing. Trivial inclusion instead
retains lambda, larger by 3^a. The note gives an explicit unproved
progression-versus-interval inequality, while also warning that this
inequality alone would not settle the other transport and tail issues.

An independent exact finite witness shows substantial progression bias.
For tau=10,r=200,a=4, first-return endpoints are 17,16. At Q=1 the
progression samples 98,97, with containing interval 98<=x<179. At
continuation clock h=128,
  81*(f_128(98)-f_128(97))^2 /
     sum_(x=98..178)(f_128(x)-f_128(x-1))^2
  =10453976883/926254009 >11.
All 82 sources 97..178 are checked to lie in {1,2} by this clock. Thus
even a factor of eleven fails for this finite progression comparison.
It does not exclude every possible uniform constant, and it is NOT the
earlier, different whole-annulus parent-loss inequality with tested C=8.

Fresh verification passed at 2026-10-13T16:27:34.956994+00:00 on
pinned Lean 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Five local modules were built
sequentially; the twelve new roots use standard axioms only, without
warnings, sorry, extra axioms, or native computation. The previous
count-return record's fourteen hashes were checked without modifying it.
Independent exact checks cover 524287 actual even-annulus pairs through
clock 19, 284 quotient lifts, nineteen full mass/count identities,
5540 first-return prefix-tree edges and 245 first-return prefixes,
960 exact lifted weight factorizations, 384 progression-energy transports,
and the 82 cycle endpoints in the finite bias example. Floating logarithm
table columns are diagnostic only and make no verification decisions.

Exploratory /tmp/collatz-return-progression-late-ratios.json computes
late-even-clock ratios for 64 nonfused prefixes using known-basin arrival
grades. Its largest observed ratio motivated the independently replayed
h=128 example above; the exploratory file is not a proof input. No claim
of an all-prefix progression bound is made.

NEXT: control the actual weighted progression averages, possibly after
aggregating several returned residues, using the available total return
cost. The bounded logarithmic height coupling covers the source-bit
boundary only and cannot by itself propagate to arbitrary later clocks.
Do not silently turn a ternary progression into an interval average or
replace bounded first moments by uniform integrability. The actual
energy bound remains O(s^(4/5)); bounded energy, escape exclusion, and
additional-cycle exclusion remain open. All jobs are terminal; no agents,
installations, credentials, staging, commits, or other Git writes occurred.

## 2026-10-13: square-root count-return clock and the remaining sampling gap

The preceding actual-annulus height-coupling turn was progress, and its
fifteen hashes were authenticated. This turn is progress too: it improves
the WRITTEN clock and energy exponents, strengthens the return-separation
moment range, and gives an all-parameter obstruction to a raw image-column
bound. Collatz remains unresolved, and the full goal remains active.
No unchanged blocker was declared.

Added docs/COUNT-RETURN-CLOCK.md, lean/CountReturnClock.lean,
verify_count_return_clock.py, and results/count-return-clock. README and
ATTEMPT include the result and reproduction command. Fifteen new kernel
roots are arithmetic inputs; the probability, real-energy, moment, and
raw image-density deductions are WRITTEN. The prior source files and
verification records were authenticated without modification.

WRITTEN uniform first positive count-return tail, for every separation D>0:
  Pr(tau>H) <=7/sqrt(H), H>=1.
Even D has tau=1. For odd D, the first step gives absolute count gap one.
At a nonzero gap d, orient Y=3^d X+c with X conditionally Haar. The prior
congruence gives expected wait to the next active step <=v(d)+2, uniformly
in c. The exact valuation is v(d)=1 for odd d and 2+nu_2(d) for even d.
KERNEL cofactors prove 3^u=3 mod8 for odd u, then
3^(2^(j+1)u)-1=2^(j+3)*q with q odd, and nondivisibility by the next power.
Decomposition of d and the valuation interpretation are written.

Count multiples of powers of two to get
  B(n)=sum_(d=1..n) nu_2(d)=sum_(r>=1) floor(n/2^r)<=n,
  C(n)=sum_(d=1..n)(v(d)+2)=3n+floor(n/2)+B(n), 2C(n)<=9n.
The repeated-halving bound and integer cost bound are kernel checked;
the finite double-sum interpretation is written.

Stop the embedded active simple symmetric walk, starting at one, when
it hits 0 or K. Its upper-exit probability is 1/K, and expected visits
to d before exit are G(1,d)=2(K-d)/K<=2, 1<=d<K. The kernel checks the
cross-multiplied finite Green equations, boundaries, and cap. The finite
walk interpretation and uniqueness are written. Conditioning before
each holding wait and using Tonelli gives, including the initial step,
  E sigma_K <=1+sum_d G(1,d)(v(d)+2)<=1+2C(K-1)<=9K-8.
No independence of holding times and subsequent exit events is assumed.
Then Pr(tau>H)<=1/K+(9K-8)/H. Set K=floor(sqrt(H)/3)+1 to obtain
7/sqrt(H). This replaces the earlier, weaker H^(-1/5) bound without
changing that prior authenticated proof or its constants.

WRITTEN consequences using the existing C_star=2187414*2^454272:
  E min(tau,H)<=14sqrt(H),
  Pr(balanced fusion clock T>H)<=14*C_star/sqrt(H).
Conditioning on either first input parity doubles the latter bound.
Predictable cycle gating and the existing E N<=C_star justify the sum
of truncated waits; no independent-cycle assumption is used. The old
central-binomial lower bound has the same H^(-1/2) order. Infinite mean
physical coalescence time is still consistent with these estimates.

With the existing actual-annulus cap and J(s)=ceil(121s/50),
  E_s <=28*C_star*sqrt(J(s))+23/4 =O(sqrt(s)).
The old 0.542s+6 bound still has a much smaller practical constant. The
coalescence-cap-plus-tail certificate now has matching square-root upper
and lower orders. This is NOT a square-root lower bound for actual E_s.
Further improvement to bounded actual energy needs the weights or signed
cancellation, not a better power in unweighted coalescence alone.

WRITTEN stronger return-separation budget: for every 0<beta<1/3,
  E sum_(j<N) D_j^beta <infinity.
Choose 3beta<alpha<1. Fixed-time alpha moments of the affine correction
B_t are bounded by M_alpha=2^(-alpha-1)/(1-r_alpha), r_alpha<1. On a
dyadic stopping block, Holder plus the new return tail gives decay
2^(-j(1-3beta/alpha)/2). Thus E B_tau^beta<=B_beta<infinity uniformly
in starting separation, and optional stopping gives
E lambda_tau^beta<=r_beta<1. Consequently
  E[(D')^beta|D]<=r_beta D^beta+2B_beta,
  E sum_(j<N) D_j^beta <=(1+2B_beta*C_star)/(1-r_beta).
No endpoint result at beta=1/3 is proved, and this budget is under the
Haar binary law, not indefinite continuation of a finite integer interval.

WRITTEN raw image-coefficient obstruction, independently checked on
finite family members: choose v_m odd in 1..127 with
3^m v_m=125 mod128; r_m=2^(m+1)v_m-2; tau=m+8; a=m+5. Parent parity
word is 0, then m ones, then 0011111; child word is 1, then m ones,
then 0110110. After the initial and common-odd steps, X=128z+124,
Y=384z+374. The seven-step suffix returns first to equal counts at
endpoints 243z+242 and 243z+238. Their separation is four, while
  lambda=3^a/2^tau=(243/256)*(3/2)^m ->infinity.
The larger base endpoint is (3^(m+5)*v_m+601)/128. This family is not
among the fifteen new Lean roots; its all-parameter proof is written.

For nonfused even first-return prefixes, the raw ternary density
K_H(z)=sum_(tau<=H)lambda*1_(z=x0 mod3^a) has Haar integral
sum2^(-tau)<=1/2 by prefix freeness. Its increasing limit is integrable.
But the displayed family makes its essential supremum unbounded, and
also makes the raw positive-integer columns unbounded using the q=1
annulus lifts. A simple constant column bound therefore cannot repair
the earlier progression transfer. This does NOT disprove a bound for
actual weighted gradients, which can offset a large coefficient.

Fresh verification passed at 2026-10-13T16:57:55.756923+00:00, pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. One new
standalone module was freshly built, fifteen roots use standard axioms
only, and there were no warnings, admitted proofs, or native evaluation.
The prior count-return, energy-cap, and height-coupling records had
14, 16, and 15 hashes authenticated respectively; their builds were
reused rather than repeated.

Independent exact finite replay: 8192 coefficient valuations, 352
structured dyadic odd cofactors, 65536 valuation/cost mass identities,
197376 holding congruence counts with 16448 exact wait expectations,
384 rational finite-walk systems, 14012 Green equations, 132 stopped
clock envelopes, 98304 actual stopped residue paths in 24 full-period
laws, 65536 exact squared horizon comparisons, and 516 actual lifts
of the expanding return family. No floating decisions were used.

Exploration before the new argument: /tmp/collatz-return-image-columns.json
scanned raw columns through first-return depth 22, and
/tmp/collatz-return-max-slope.json found the displayed family's pattern
through depth 24. Those exploratory float tables are not proof inputs;
the family was separately replayed using exact integers. A web review of
https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/tao-basin-densities.tex
looked at the external masked quadratic-cylinder energy criterion. Its
E'_K uses canonical inverse-word densities at integer targets, not this
project's dyadic E_s. No bridge between the energies, new external theorem,
or external replay was adopted. Sublinear bounds on our E_s do not satisfy
that other criterion automatically.

NEXT: use the strengthened return-separation budget with the actual
weighted progression samples or signed cancellation. Raw image columns
cannot have a uniform constant bound; ternary Haar integrability does
not control positive-integer trace samples. The coalescence-only energy
certificate already has its square-root growth order, so do not try to
obtain bounded energy merely by optimizing its constants or tail power.
Bounded actual energy, full escape exclusion, and additional-cycle
exclusion remain open. All jobs have terminated. No agents, installations,
credentials, staging, commits, or other Git writes were used.

## 2026-10-13: return-image logarithmic moments and finite integer sampling

The previous square-root-clock turn was progress; its eleven recorded
hashes were revalidated at this turn's start. This turn is progress too:
it proves a WRITTEN logarithmic-moment bound for return-image densities
and transfers its truncated version to finite integer intervals. This
provides positive sampling control after the raw coefficient obstruction.
It does not settle the pairing with actual future gradients. The full
Collatz goal remains active and unresolved; no blocked condition applies.

Added docs/RETURN-IMAGE-BOUNDS.md, lean/ReturnImageBounds.lean,
verify_return_image_bounds.py, and results/return-image-bounds. README
and ATTEMPT include the result and reproduction. Twelve kernel roots
supply arithmetic. Integration, convexity, logarithms, Holder estimates,
and all infinite probability consequences remain WRITTEN.

Use nonfused first positive count-return prefixes i for adjacent even
sources, with clock tau_i, even residue r_i, common count a_i, endpoints
x_i,y_i, and separation D_i=|x_i-y_i|>0. Let p_i=2^(-tau_i), the
UNCONDITIONAL binary prefix mass, so sum p_i<=1/2. Put
  lambda_i=3^a_i/2^tau_i,
  F_i(z)=3^a_i * 1_(z=x_i mod3^a_i),
  K_beta(z)=sum_i p_i D_i^beta F_i(z).
F_i has ternary additive Haar integral one. M_beta=integral K_beta is
finite for 0<=beta<1/3 by the prior written return-separation moment.
K_(beta,H) retains only tau_i<=H. The density is periodic for every finite
H and includes all integer representatives of each cylinder; requiring
an additional allowed source quotient only reduces its positive columns.

WRITTEN joint first-return moment:
  sum_i p_i D_i^beta (1+tau_i)^alpha <infinity
whenever beta>=0, alpha>0, and 3beta+2alpha<1. The clock tail gives
E(1+tau)^q<infinity for q<1/2. For beta>0 choose
beta/(1-2alpha)<beta'<1/3, then apply Holder using the beta' separation
moment and q=alpha beta'/(beta'-beta)<1/2. No independence is assumed.
For beta=0 use the clock moment alone. Also
  ||K_beta-K_(beta,H)||_1 <=C_(beta,eta) H^(-eta)
for every 0<eta<(1-3beta)/2; beta=0 permits eta=1/2 directly.

WRITTEN logarithmic moment: Phi_alpha(t)=t(log(1+t))^alpha is convex
for alpha>0. With Mbar_beta=max(1,M_beta), apply finite-mixture Jensen
to weights p_iD_i^beta/Mbar_beta and add unused weight at zero, then use
monotone convergence. The result is
  integral K_beta [log(1+K_beta/Mbar_beta)]^alpha <=A_(beta,alpha),
  A_(beta,alpha)=(log3)^alpha sum_i p_iD_i^beta(1+tau_i)^alpha<infinity.
Thus K_beta is in L(log L)^alpha for 3beta+2alpha<1. This is NOT an
L^p bound for p>1 or an essential-supremum bound.

The moment gives an explicit modulus of absolute continuity on a Haar
set A of measure delta>0:
  integral_A K_beta <=Mbar_beta sqrt(delta)
     + A_(beta,alpha)/[log(1+delta^(-1/2))]^alpha.
Ternary cylinder averaging P_L fixes each F_i with a_i<=L. Since
otherwise tau_i>L, its L1 contraction and the truncation tail give
  ||K_beta-P_L K_beta||_1<=2C_(beta,eta)L^(-eta).
These are ternary Haar assertions; the finite-integer result below is
separate. Do not confuse this uniformly integrable image-density family
with the non-uniformly-integrable endpoint log-height differences from
the earlier annulus note. They have different values and sampling laws.

KERNEL cubic child identity: 3^a_(t+1)(r)+3^a_(t+1)(r+2^t)=4*3^a_t(r),
and complete-period cubic mass is 4^t. Parent parity words give a binary
prefix tree, because each source-prefix split has opposite new endpoint
parities. Giving its even/odd branches tilted weights 1/4 and 3/4, the
prefix-free stopped mass satisfies sum_i 3^a_i/4^tau_i<=1. Thus
  sum_(tau_i<=H) lambda_i<=2^H.
The abstract pruned-tree integer inequalities and cubic identities are
kernel checked; their probability/word interpretation is written.

KERNEL endpoint comparison: orbit_t(r)<2*3^a_t(r) for r<2^t, via the
previous shifted retention bound. For the equal-count pair this gives
D_i<2*3^a_i. Therefore, in WRITTEN real powers,
  sum_(tau_i<=H)lambda_i D_i^beta<=2^beta(2*3^beta)^H.
The kernel also checks an integer floor counter's discrepancy
|q*count-M|<q. Its identification with the number of representatives of
one residue in an interval is elementary written counting, independently
replayed by direct enumeration.

For any interval I of M>=1 nonnegative integers, WRITTEN division and
summation give the actual finite-integer bound
  |mean_I K_(beta,H)-sum_(tau_i<=H)p_iD_i^beta|
       <=2^beta(2*3^beta)^H/M.
Applying the pointwise convex-mixture bound before counting gives
  mean_I K_(beta,H) [log(1+K_(beta,H)/Mbar_beta)]^alpha
       <=A_(beta,alpha)
          +2^beta[(H+1)log3]^alpha(2*3^beta)^H/M.
For beta=0 and H=floor((1-epsilon)log_2 M), epsilon fixed in (0,1),
these are uniform logarithmic moments on the actual finite intervals.
For general beta use H=floor(c log M), c<1/log(2*3^beta). This improves
on a Haar-only mass bound but retains the essential truncation error.
It is invalid to fix M and pass H to infinity in these estimates.

An explicit unweighted version does not use the huge C_star constant:
  integral K_0[log(1+K_0)]^(1/4) <80,
  mean_I K_(0,H)[log(1+K_(0,H))]^(1/4)<82
whenever 2^H(H+1)<=M. This permits H=log_2 M-log_2 log_2 M+O(1).
The associated finite-interval mass above coefficient R is at most
82/[log(1+R)]^(1/4). The exact rational root comparisons give
E(1+tau)^(1/4)<356/5 and (log3)^(1/4)<11/10, so the Haar bound is
<3916/50<80. The logarithm comparison uses the written inequality
exp(4/3)>1+4/3+8/9=29/9>3. Seven exact constant comparisons accompany
the finite verifier; the real steps remain written.

Fresh verification passed at 2026-10-13T17:40:34.195980+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Six modules
were freshly built sequentially; all twelve new roots use standard
axioms only, with no warnings, admitted proofs, or native evaluation.
The prior clock, height, and persistence records had 11, 15, and 14
hashes authenticated respectively without rewriting the prior records.

Independent exact replay: 32767 actual cubic-child/endpoint comparisons,
15 full-period masses, 75562 first-return tree edges, 2494 first-return
prefixes (2478 nonfused) through depth 18, 17 pruned-tree identities,
51 finite integer-power column bounds, 30240 direct interval residue
counts, 12 exact ternary projection comparisons covering 2125764 residue
values, and 160 truncated-density interval comparisons covering 174840
integer values. The finite integer-power checks at powers 1 and 2 test
counting algebra, not infinite separation moments of those powers.
No floating arithmetic was used in the verification decisions.

Exploration only: /tmp/collatz-annulus-charge-scan.rs and its CSV scan
whole-annulus reversal drift/parent-loss ratios through k=18,s=512 using
floating weights and checked u64 orbit arithmetic. The largest observed
ratio remains about 6.607568 at k=5,s=46 (the old exact witness). At k=18
the largest observed ratio is about 1.039756 at s=81. These new larger
ranges are NOT certified C=8 inequalities; the earlier exact certified
rectangle remains k<=10,s<=96. The scan's finite-level energy peaks
near 0.702683 at s=50 through level 18, but does not bound omitted levels.
The process terminated; no job is left running.

External reading used primary sources: Tao's 2020 post
https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/
and the recent archimedean almost-boundedness preprint
https://arxiv.org/html/2609.33018v1 . No new external theorem or estimate
was adopted, replayed, or used in the new result. The latter's announced
almost-boundedness conclusion would not itself supply the weighted
progression comparison or full convergence.

NEXT: exploit the new logarithmic-moment control in the actual pairing
with [f_h(x)-f_h(x-D_i)]^2, or find a direct bound for that pairing.
Its continuation clock and endpoint interval depend on the prefix.
Neither Haar L(log L) integrability nor the truncated finite-interval
bound allows replacing it by an interval energy with a fixed constant.
The actual energy bound remains O(sqrt(s)); bounded energy, escape
exclusion, and additional-cycle exclusion remain open. All jobs are
terminal; no agents, package installs, credentials, staging, commits,
or other Git writes occurred.

## 2026-10-13: corrections stopped at gap boundaries and half-power moments

The preceding return-image turn was progress. At this turn's start its
twenty recorded hashes and the clock record's eleven hashes matched.
This turn also made progress: a different stopping argument improves
the moment range, the explicit return-cycle constant, and the image
truncation rate. No full proof or counterexample was found. The user's
unbounded Collatz goal remains active; no blocker requires user input.

Added docs/RETURN-CORRECTION-MOMENTS.md,
lean/ReturnCorrectionMoments.lean,
verify_return_correction_moments.py, and
results/return-correction-moments. README and ATTEMPT were updated.
The earlier hashed notes, source files, and records were not rewritten.

The probability law is still the coherent full binary residue law,
equivalently Haar binary input. After each finite stopping prefix each
endpoint's next parity is conditionally fair; paired parities are
dependent. No infinite-time uniform law on a fixed finite integer
interval is assumed. For the actual affine coefficients
  U^t(X)=lambda_t X+B_t, lambda_t=3^a/2^t, B_0=0,
the conditional identities are
  E(lambda_(t+1)|F_t)=lambda_t,
  E(B_(t+1)|F_t)=B_t+1/4.

NEW KERNEL inputs (twelve audited roots): actual additive numerator
recurrence, residue lift, and two-child sum; the algebraic power identity;
an exact finite stopping-tree correction identity, clock bound, and
slope identity; named reuse of the prior gap-boundary clock budget;
quarter-root comparisons, drift/small-set constants, prescribed-attempt
constants, and the odd-offset bit bound. The correction tree has
P=d4^h E B_terminal, Q=2^h E extra_clock, initial B=N/d, and satisfies
4P=4^(h+1)N+d2^h Q. The stopped slope numerator is 4^h A from A/d.
Their probability interpretation and infinite stopping are WRITTEN.

WRITTEN boundary-stop proof: for odd initial separation D, sigma_K is
the physical time of first gap-walk exit from 0..K, including the first
departure step. The earlier proof gives upper-exit probability 1/K and
E sigma_K<=9K-8. For K=1, sigma_K=1. Even D has tau=1 and can use
sigma_K=1 without an upper exit. For S=sigma_K truncated at n,
  E B_S=E S/4, E lambda_S=1.
Fatou, nonnegativity, and monotone convergence give only the inequalities
  E B_sigmaK<=(9K-8)/4, E lambda_sigmaK<=1.
Do not claim equality at the unbounded stop or assume uniform
integrability. On lower exit sigma_K=tau, the first positive count
return. Therefore, for L>=1,
  Pr(B_tau>L)<=1/K+(9K-8)/(4L).
Taking K=floor(sqrt(L))+1 proves
  Pr(B_tau>L)<=7/(2 sqrt(L)),
  E B_tau^beta<=m_beta=1+7beta/(1-2beta), 0<beta<1/2.
Each endpoint's quarter-power moment is at most 9/2, uniformly in D
and conditionally at every return boundary. No independence is used.

WRITTEN direct returned-separation tail: at equal counts,
  D'<=D lambda_tau+B_tau^(1)+B_tau^(2).
The nonnegative process Z_t=D lambda_t^(1)+B_t^(1)+B_t^(2) has drift
1/2. The same stopped calculation yields
  E Z_sigmaK<=D+(9K-8)/2,
  Pr(D'>L)<=1/K+[D+(9K-8)/2]/L<=(D+6)/sqrt(L).
For adjacent starts D=1 the coefficient is seven. This is under the
full unconditioned binary law; restricting nonnegative sums to even,
nonfused return prefixes decreases them.

WRITTEN improved cycle budget: for beta<1/2,
  E (D')^beta<=r_beta D^beta+2m_beta,
  r_beta=(2^(-beta)+(3/2)^beta)/2<1.
Use nonnegative stopped slope powers after time one to get
E lambda_tau^beta<=r_beta, since tau>=1. At beta=1/4, the exact root
comparisons 120^4<2*101^4 and 3*120^4<2*133^4 imply r_beta<39/40:
  E (D')^(1/4)<=(39/40)D^(1/4)+9.
With V=D^(1/4) and R=400^4=25,600,000,000<2^35, the drift is at
most minus one outside R, so expected return-cycle time to R is <=V.
The existing prescribed descent paths shrink separation by at most
3/4 each cycle; (3/4)^4<1/2 gives at most 140 cycles from D<=R.
Each uses at most 37 bits because c=(3D+1)/2<2^36. Thus each attempt
succeeds with conditional probability >=2^-5180. From V<=400,
the expected V after any number of cycles stays <=400, using
(39/40)*400+9=399. Attempt plus reentry therefore costs at most 540
in conditional expectation. Summing over the geometric bound for
reached attempts proves
  E N<=C_quarter:=540*2^5180.
Attempts are not assumed independent. This supersedes the numeric
constant 2187414*2^454272, not the existing valid exponent bounds.
It also gives
  E sum_(j<N) D_j^beta<=[1+2m_beta C_quarter]/(1-r_beta), beta<1/2,
and at beta=1/4 the bound 40(1+9 C_quarter).
The fusion-clock upper tail can use 14 C_quarter/sqrt(H), and the
actual-energy bound 28 C_quarter sqrt(ceil(121s/50))+23/4. The
physical mean fusion time remains infinite, and bounded energy is open.

WRITTEN image consequences: the logarithmic-moment parameter region
is now beta>=0, alpha>0, beta+alpha<1/2. Choose
beta/(1-2alpha)<beta'<1/2 and reuse the prior Holder and Jensen proofs.
More sharply, from the two adjacent-pair tails
Pr(tau>H)<=7/sqrt(H) and Pr(D'>u)<=7/sqrt(u), integration split at H
gives
  E[(D')^beta 1_(tau>H)]<=7 H^(beta-1/2)/(1-2beta).
For beta=0 use the clock tail on nonfused prefixes. Thus, for H>=1,
  ||K_beta-K_(beta,H)||_1<=7 H^(beta-1/2)/(1-2beta), 0<=beta<1/2.
This reaches the endpoint decay rate, improving the prior strict
Holder exponent. Ternary conditional projection at depth L>=1 has
L1 error at most 14 L^(beta-1/2)/(1-2beta). The finite-integer-interval
formulas and their depth/length errors are unchanged; the unweighted
quarter-logarithmic constants 80 and 82 remain valid. No beta=1/2
moment, L^p density bound for p>1, or actual-gradient pairing is proved.

Fresh verification passed at 2026-10-13T18:04:21.422785+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Six modules
were freshly built sequentially. All twelve roots use only standard
axioms; there were no warnings, admitted proofs, or native evaluation.
The control, clock, and image records had 14, 11, and 20 hashes
authenticated respectively. The new verification manifest has 21 hashes.

Exact finite replay passed: 16383 direct affine child identities;
14 full-period correction/slope masses; 12130 independently recomputed
stopped endpoint trajectories; 272774 actual stopping-tree edges;
1092 bounded stopped laws; 4992 finite correction-tail comparisons;
78 finite returned-separation tail checks; 41524 prescribed return
cycles across 4167 fusion paths; nine constant comparisons;
20405 rational tail-bound comparisons; and 2450 exact truncation
coefficient identities. Stopping trees used thirteen separations,
including values near R and 2^35, six gap barriers, and horizon 14.
Prescribed fusion samples included all D<=4096, dyadic boundary values,
and values near R; the observed maximum was 42 cycles and 81 bits.
These finite observations do not replace the general written bounds.
No floating arithmetic was used in verification decisions.

Exploration only: /tmp/collatz-return-image-l2.rs and its executable/CSV
enumerate the nonfused even-prefix image density through depth 24. The
trie evaluates exactly
  integral K_H^2=sum_(i,j) p_i p_j 3^min(a_i,a_j)
                    1_(compatible ternary image cylinders).
The CSV stores binary-mass numerator over 2^24 and squared-density
numerator over 2^48. Diagnostic floating values were about 0.002197 at
H=6, 0.056691 at H=10, 0.168366 at H=14, 0.274069 at H=18, and
0.416410 at H=24. At depth 24 there were 1,931,482 live prefixes and
54,364 trie nodes. No convergence or divergence conclusion follows,
and this exploration is not part of the new verification manifest.

NEXT: use the stronger separation-weighted image estimates in the
actual future-gradient pairing, or prove a direct integrated return
comparison. The unweighted coalescence-only certificate already has
its square-root growth order. Merely improving its constants, or
sampling deeper L2 image densities, does not establish bounded energy.
A possible additional route is exponential moments of the number of
return cycles from the multiplicative drift outside R; this has not
been adopted or verified. The exploratory tilted-slope return-law idea
is also unproved and unused. Escape and additional cycles remain open.
All processes are terminal. No agents, installations, credentials,
staging, commits, or other Git writes occurred.

## 2026-10-13: exponential cycle count and the all-return occupation density

The previous stopped-correction turn was progress. This turn authenticated
its 21 hashes, the image record's 20, and the ordered-drift record's 16
before proceeding. The new work is also progress: it controls the
sampling density accumulated over every nonfused count return, and
rules out a scalar pointwise charge at a return. The full user objective
remains active and unresolved. There is no genuine user/external blocker.

Added docs/RETURN-OCCUPATION-DENSITY.md,
lean/ReturnOccupationDensity.lean,
verify_return_occupation_density.py, and
results/return-occupation-density. Updated README and ATTEMPT.
Earlier hashed sources and records were not changed.

NEW KERNEL arithmetic (fifteen roots):
- The fixed even first-return cylinder r=48 mod 64 has tau=6,
  common count two, and endpoints 9q+8,9q+7; alive through time five.
- The persistent family 2n_j=16(64^j-1)/9, even j>=2, returns at
  six to X=2^(6j-2)+1 and Y=2^(6j-2).
- Odd counts are nondecreasing in the clock; for a>=2 and
  0<t<=3a-2, wt_t(2^(2a)+1)>wt_t(2^(2a)). This verifies that the
  whole known persistent window lies within the SECOND count excursion.
- Multiplicative drift arithmetic outside V>=400; a general finite
  inverse Bernoulli inequality and its exponential linearization;
  the rational denominator and failed-attempt contraction inequalities;
  half-power root comparisons and the total attempt constant.
- Selected all-return cubic weights are bounded by full-period cubic
  mass; cumulative slope-column numerator plus 2^(H+1) is <=2*4^H.

WRITTEN obstruction: the earlier family has unaveraged negative drift
at least 5(3j-4)/128 during that second excursion. Its first-return
data (tau,a,D) are always (6,2,1), with common multiplier 9/64.
Thus no finite function of these data alone bounds the accumulated
pointwise excursion cost. Separation moments do not repair that
pointwise approach, even when the separation is exactly one. The
displayed source cells are rare; this does not refute integrated bounds.

WRITTEN exponential cycle moment, now adopted (superseding the previous
entry's tentative suggestion): retain D_j, N, V=D^(1/4), R=400^4,
and the conditional drift E V_next<=(39/40)V+9. Outside D<=R,
this is at most qV with q=399/400. If sigma is the cycle count to
reach D<=R, the killed potential gives
  Pr(sigma>n)<=V(D)q^n/400,
  E s^sigma<=1+(s-1)V(D)/[400(1-sq)], 1<s<1/q.
These are conditional estimates given any finite return history;
neither Markov independence nor independent attempts is needed.

Take the previous attempt length M=140 and success lower bound
p=2^-5180. Set delta=p/4096=2^-5192 and s=1+delta. An attempt
starts in the positive part of D<=R, runs M cycles with zero absorbing,
then waits to reach D<=R again if needed. It can fuse during this
reentry. Use the upper-bound attempt length L=M+sigma, even when
fusion occurred earlier. Since E V(D_M)<=400,
  E[s^L 1_failed | attempt start]
       <=s^M[1-p+delta/(1-sq)]<=1-p/2=:rho<1.
The arithmetic uses 1-sq>=1/800, s^140<=1+280delta, and
(1+280delta)(1-p+800delta)<=1-p/2. The last inequality is proved
with cleared rational denominators for arbitrary 0<=p<=1.

IMPORTANT: fusion during reentry can take MORE than M cycles. Do not
bound successful length by M. Instead bound the entire attempt:
  E s^L<=s^M[1+delta/(1-sq)]
         <=(1+280delta)(1+800delta)<=2.
The discounted probability of reaching attempt k is <=rho^(k-1).
Summing the successful contributions gives
  E(1+2^-5192)^N<=A:=4/p=2^5182.
This is a WRITTEN probability theorem. It concerns return-cycle count,
not physical clock. The physical fusion time still has infinite mean.

WRITTEN occupation measure: for physical return clocks S_j, fusion
clock T=S_N, and C=540*2^5180, define
  integral g dnu = E sum_(1<=j<N) g(D_j,S_j).
Its total mass is <=C. From the prior Pr(T>H)<=14C/sqrt(H) and
the new exponential cycle moment, for integer ell>=1,
  nu(S>H)<=14C ell/sqrt(H)+A s^(1-ell)/delta.
Taking ell=max(1,ceil(logH/[2logs])) gives
  nu(S>H)<=[A_T+B_T logH]/sqrt(H), H>=1,
  A_T=14C+A s/delta, B_T=7C/logs.

For gamma in [1/4,1/2), convexity of r_gamma and the two endpoint
root comparisons give r_gamma<=39/40. Since
2m_gamma<=7/(1-2gamma), the summed separation moment obeys
  integral D^gamma dnu<=B/(1-2gamma), B=40(1+7C).
For u>=16 choose gamma=1/2-1/log_2(u), and for u<16 use mass<=C:
  nu(D>u)<=B(1+log_2 u)/sqrt(u), u>=1.
Consequently D+1+S has every nu moment below 1/2, and
  E sum_(1<=j<N) D_j^beta(1+S_j)^alpha<infinity
for beta>=0, alpha>0, beta+alpha<1/2. No independence is assumed.

WRITTEN all-return density: index EVERY nonfused even-source return
prefix i, not just first returns. Ancestors and descendants can both
appear. Let t_i be its total source clock, a_i its common total odd
count, x_i=U^t_i(r_i), D_i>0 its separation, p_i=2^-t_i, and
  F_i(z)=3^a_i 1_(z=x_i mod 3^a_i),
  K*_beta=sum_i p_i D_i^beta F_i.
Its Haar mass M*_beta is finite for beta<1/2. With
Mbar=max(1,M*_beta), the same convex mixture/Jensen proof gives
  integral K*_beta[log(1+K*_beta/Mbar)]^alpha
       <=A*_(beta,alpha)<infinity, beta+alpha<1/2,
  A*=(log3)^alpha sum_i p_i D_i^beta(1+t_i)^alpha.
Prefix disjointness is not needed; the finite occupation mass supplies
the mixture normalization.

WRITTEN all-return truncation: for 0<=beta<1/2, c=1/2-beta, H>=1,
  ||K*_beta-K*_(beta,H)||_1 <= H^(beta-1/2) times
    [A_T+B_T logH
       +beta B{(1+logH/log2)/c+1/(c^2 log2)}].
At beta=0 the final term is zero. This is
O_beta((1+logH)H^(beta-1/2)); the logarithm has not been removed.
It follows by splitting the layer-cake integral at H and using the
two occupation tails. Ternary projection at depth L has error at most
twice this bound with H=L. First-return bounds remain stronger for
their smaller density; do not confuse the two objects.

WRITTEN finite integer sampling: each level's return slopes have sum
<=2^t, and all levels through H have sum <=2^(H+1)-2. The kernel
cumulative-column recurrence checks the latter's integer form. Since
D_i<2*3^a_i, for any beta>=0 the finite coefficient sum is bounded by
  sum_(t_i<=H) lambda_i D_i^beta<=2^(beta+1)(2*3^beta)^H.
Thus the all-return truncated mean on any integer interval of length M
differs from its Haar mean by at most this quantity divided by M.
The logarithmic-moment transfer has the additional [(H+1)log3]^alpha
factor. No infinite separation moment at beta>=1/2 is asserted.
The old explicit logarithmic constants 80 and 82 are first-return
constants and are NOT asserted for this larger occupation density.

Fresh verification passed at 2026-10-13T18:31:07.233846+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten modules
were freshly built sequentially. All fifteen new roots use only the
standard axioms; no warnings, admitted proofs, or native evaluation.
The correction, image, and persistence records had 21, 20, and 14
hashes authenticated respectively. The new manifest records 29 hashes.

Independent exact finite checks passed: 4112 fixed-return cylinders,
16 full persistent second excursions, 752 persistent drift offsets,
19305 inverse-Bernoulli cases, 5241 exponential linearizations,
8384 failed-attempt rational comparisons, five explicit cycle-constant
checks, and 1249 near-half moment coefficient comparisons. The exact
comparison at the actual delta=2^-5192 was checked with integers.

The all-return tree through depth 16 had 30750 edges and 2552 nonfused
return prefixes: 744 first returns and 1808 later returns, up to return
index seven. All were independently matched against 32768 directly
iterated even inputs in the full period. Sixteen occupation identities
and 45 finite column bounds passed. The finite occupation mass was
13623/65536, and balanced-fused mass 17685/65536; these are finite
values, not claimed limiting masses. Also passed: 36 ternary projection
checks covering 117936 density values, 16752 direct interval residue
counts, and 72 interval bounds covering 5328 density values. Finite
integer-power checks at beta=1 or 2 verify counting algebra only,
not infinite moments. No floating arithmetic was used in decisions.

NEXT: the sampling weight over all returns is now controlled. The
remaining obstacle is its pairing with the actual future squared
weight differences, at prefix-dependent continuation clocks and
endpoint intervals. Prove complementary integrability or a direct
averaged charge. A separation-only cost per excursion is now excluded
pointwise even at fixed return clock and count. Improving unweighted
coalescence tails or cycle constants again would not settle bounded
energy. The tilted-slope idea remains unproved and unused. Escape and
other cycles remain open; the full Collatz goal stays active.
All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes occurred.

## 2026-10-13: actual-gradient complementary-norm obstruction

The previous occupation-density turn was progress. Its 29 hashes,
the correction record's 21 hashes, and the energy-cap record's 16
hashes matched at this turn's start. This turn also made progress:
it rules out the proposed uniform complementary norm for accumulated
actual gradients, then identifies a candidate replacement below.
The full Collatz goal remains active and unresolved; no user or
external blocker prevents further research.

Added docs/GRADIENT-ORLICZ-OBSTRUCTION.md,
lean/GradientOrliczObstruction.lean,
verify_gradient_orlicz_obstruction.py, and
results/gradient-orlicz-obstruction. Updated README and ATTEMPT.
Earlier hashed sources and records were not rewritten.

For m>=0 define Q=2^(12m+6), M=9Q, and the actual image interval
I=[9Q+8,18Q+8), length M. The fixed return cylinder r=48 mod64
maps source quotients Q<=q<2Q to paired endpoints 9q+8,9q+7.
Q=1 mod9, q_m=16 floor(Q/9)+1 lies in that quotient interval, and
x_m=9q_m+8=16Q+1=2^(12m+10)+1 belongs to the sampled progression.
Its paired endpoint is x_m-1. This is the earlier persistent family
with j=2m+2 and fixed first-return data (tau,a,D)=(6,2,1).

Define the FINITE accumulated returned squared gradient
  G_m(x)=sum_(h=0)^(6m+1)
       [M(f_(12m+12+h)(x)-f_(12m+12+h)(x-1))]^2.
It is defined on all of I and its actual progression; no eventual
orbit convergence or infinite time sum is required. The exact scale
identity is M/2^(12m+12+h)=9/2^(h+6). New kernel versions of the
retained-parent and child-ceiling bounds give throughout this window
  M f_(12m+12+h)(x_m)>=1/2,
  M f_(12m+12+h)(x_m-1)<=27/64.
Therefore the written squared sum is
  G_m(x_m)>=L_m:=25(6m+2)/4096.
The window lies entirely in the second count excursion.

NEW KERNEL roots (eight): Q mod9, actual interval/progression location,
the returned scale identity, returned parent retention, returned child
ceiling, a general cross-product gap lower bound, its squared version,
and an exact large quadratic-exponential integer comparison. The real
division, finite sum, exponential growth, and norm consequences are
WRITTEN, not full Lean formalizations.

WRITTEN obstruction: for any p>1,C>0, the interval average of
exp((G_m/C)^p) is at least exp((L_m/C)^p)/M, which tends to infinity
because log M=(12m+6)log2+log9 grows linearly and (L_m/C)^p grows
superlinearly. The actual progression has Q elements and yields the
same conclusion with Q in the denominator. Under the convention
mean(exp((G/C)^p)-1)<=1, the Luxemburg norm is at least
  L_m/[log(M+1)]^(1/p),
or L_m/[log(Q+1)]^(1/p) on the progression. It grows at least as
m^(1-1/p). At m=16384,p=2,C=1, the kernel integer comparison and
the written log2<1, log9<3 bounds imply an average >exp(100000).
That large example uses the general family proof, NOT an orbit replay
at the huge source size.

For Phi_alpha(u)=u[log(1+u)]^alpha, define the convex conjugate
Psi_alpha(v)=sup_u(uv-Phi_alpha(u)). Taking
u=exp((v/2)^(1/alpha))-1 gives, for v>=2,
  Psi_alpha(v)>=(v/4)exp((v/2)^(1/alpha))
              >=(1/2)exp((v/2)^(1/alpha)).
Thus mean Psi_alpha(G_m/C) is unbounded for every alpha<1 and C>0.
In particular, the available density exponents alpha<1/2 demand an
exponential power >2 whose uniform norm fails. This excludes the
specific method of first accumulating time contributions and then
using ONE uniform complementary norm. It does not exclude clockwise
estimates, support-sensitive estimates, or use of actual correlation.

IMPORTANT scope: the exceptional point contributes only L_m/M to
the ordinary mean lower bound, which tends to zero and is summable
over m. This does NOT show unbounded ordinary means, failure of an
averaged density-gradient pairing, or unbounded actual energy. The
single return column has bounded value 9/64 on the residue 8 mod9.
An ordinary exponential norm (p=1) at sufficiently large scale is
not excluded by this family; no such uniform bound is proved.

Fresh verification passed at 2026-10-13T18:50:44.028881+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eleven
modules were freshly built sequentially. All eight new roots use only
standard axioms, with no warnings, admitted proofs, or native evaluation.
The occupation and persistence records had 29 and 14 hashes verified.
The new manifest records 29 hashes.

Independent exact replay checked 21 image/family instances through
m=64, 84 direct original-source transport identities, 1866 returned
gradient offsets, all 576 gradients on the smallest interval [584,1160),
and all 64 sampled progression gradients there. The exceptional x=1025
has G_0=39778923825/516006608896. Exact ordinary mean enclosures are
saved; they concern only that finite interval. Five large quadratic
exponential comparisons and two elementary exponential constants also
passed. No floating arithmetic was used in verification decisions.

External reading was limited to primary sources. Tao's 2019/2020
Syracuse-law discussion and the OpenAI ordinary-correlation catalogue
did not supply the stopped weighted-gradient comparison. A more useful
lead is Lucas Valbuena's 8 October paper:
https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/quadratic-cylinder-energy.tex
It uses distinct offset quotients to obtain polynomial cylinder energy
for the stationary Syracuse law, then combines it with Tao mixing to
obtain subcritical L^p integrability. Its stationary result is NOT our
return density; no external proof bundle was replayed or adopted here.

NEXT — PROMISING CANDIDATE, NOT YET ADOPTED OR VERIFIED:
Adapt that quotient-counting idea to our finite binary image law.
For ALL r<2^t, let a=wt_t(r), N=2^t U^t(r)-3^a r, and
  rho_t(z)=sum_(r<2^t) 2^-t 3^a 1_(z=U^t(r) mod3^a).
This has Haar integral one and dominates the selected return density
at total clock t. At fixed (t,a,image residue v), N has fixed residue
mod3^a. Distinct r give distinct N: the exact affine equation plus
gcd(3^a,2^t)=1 forces r=r' if N=N' within the full binary period.
Thus q=floor(N/3^a) is injective on such a fibre and q<=Y=N/3^a.
If its cardinality is m_f, the elementary distinct-quotient count gives
  m_f^2<=2 sum_fibre(1+Y).
Summing and using Cauchy over a=0..t should give
  ||rho_t||_2^2 <=2(t+1) sum_(r<2^t) 3^a4^-t(1+N/3^a)
                 =2(t+1)(1+t/4)=(t+1)(t+4)/2.
The exact inputs are sum3^a=4^t (already kernel) and
4 sumN=t4^t. The latter follows from the new numerator child sum
4N+2^t, but currently needs its own all-depth kernel proof if used.
No Tao mixing or external stationary theorem is needed for this
finite-binary argument. Check the fibre injection carefully before
adopting it, especially t=0,a=0.

If that quadratic bound holds, each selected return layer kappa_t is
pointwise <=rho_t and ||kappa_t||_2<=t+2. Hence the all-return
truncation has
  ||K*_(0,H)||_2<=H(H+5)/2<=3H^2 for H>=1.
Combine it with the VERIFIED WRITTEN L1 clock-truncation error
O((1+log H)H^-1/2). Dyadic increments at H=2^j have L1 size
O(j2^-j/2) and L2 size O(2^(2j)). Interpolation gives Lp increment
exponent [-(2-p)/2+4(p-1)]/p = (9p/2-5)/p.
This is summable in j for 1<p<10/9. Thus a prospective result is
K*_0 in Lp for every 1<=p<10/9, substantially stronger than the
currently adopted logarithmic moments. This has NOT yet been promoted
to a proved project result or checked by a verifier.

Possible extensions once the unweighted claim is verified:
- Pointwise Holder over columns gives
  K*_beta <=(K*_gamma)^(beta/gamma)(K*_0)^(1-beta/gamma).
  With gamma<1/2, K*_gamma in L1 and K*_0 in Lp0, this would give
  K*_beta in Lp for 1<=p<10/(9+2beta), 0<=beta<1/2.
- K*_(beta,H) is periodic mod3^H, so any interval mean of its pth
  power is <=(1+3^H/M) times its Haar pth moment. This may transfer
  uniform power bounds when 3^H<=M, using actual finite intervals.
- A first-return-only variant may improve the L2 growth to H^(3/2)
  using stopped slope/correction budgets and then allow p<8/7; this
  is more tentative and is not needed for the all-return result.

The weighted-gradient comparison remains the actual objective of this
route. Even a new Lp density theorem would still require control of
the complementary power moment of the accumulated gradients, or an
estimate retaining their correlation. Do not treat density integrability
as bounded actual energy or escape exclusion. All processes are
terminal. No agents, installs, credentials, staging, commits, or other
Git writes occurred.

## 2026-10-13: quadratic binary image energy and all-return Lp moments

The candidate in the preceding entry is now ADOPTED as a WRITTEN
analytic theorem with fresh kernel arithmetic and independent exact
finite verification. This supersedes the preceding candidate status.
Added docs/BINARY-IMAGE-ENERGY.md, lean/BinaryImageEnergy.lean,
verify_binary_image_energy.py, and results/binary-image-energy/.
README and ATTEMPT include the result and reproduction command.

For r<2^t put a=wt_t(r), x=U^t(r), and N=2^t*x-3^a*r>=0.
Define the full ternary Haar image density
  rho_t(z)=sum_(r<2^t) 2^-t*3^a*1_(z=x mod3^a).
It has mass one. At fixed t and a, equal N forces equal r: subtract
the affine equations and use coprimality of 2^t and 3^a. At fixed
image residue v, N=2^t*v mod3^a, so floor(N/3^a) is injective
on that fibre. This includes t=0 and a=0; no exceptional case is
left unproved. If the fibre has m sources, sorting its quotients
gives q_j>=j for j=0,...,m-1 and
  3^a*m^2 <= 2 sum_fibre(3^a+N).
The injection, residue, and ranked cost lemmas are kernel checked;
the sorting/existence of a ranked finite enumeration is written.

The new all-depth kernel identity is
  4 sum_(r<2^t) N_t(r) = t*4^t.
Its induction sums the previous numerator children 4N+2^t. Combining
it with the existing cubic mass sum3^a=4^t gives
  4 sum(3^a+N)=(t+4)*4^t.
Group rho_t by count a, apply the fibre square bound, then Cauchy
over the t+1 possible counts. The WRITTEN Haar consequence is
  ||rho_t||_2^2 <= (t+1)(t+4)/2,
  ||rho_t||_2 <= t+2.
This is a bound at every finite depth, not an asymptotic extrapolation
from the enumerated periods.

At total clock t, the selected even nonfused return layer kappa_t
is pointwise <=rho_t. Its first endpoint is consistently U^t(r),
not reordered by size, so the domination matches the occupation
density definition exactly. Nested returns at different clocks are
allowed; each r at a fixed clock appears at most once. Minkowski
and the new finite sum roots give
  ||K*_(0,H)||_2 <= H(H+5)/2 <=3H^2 for H>=1.
Use the prior WRITTEN occupation tail
  ||K*_0-K*_(0,H)||_1 <=(A_T+B_T log H)/sqrt(H).
For Delta_j=K*_(0,2^(j+1))-K*_(0,2^j),
  ||Delta_j||_1 <=(A_T+B_T*j*log2)*2^(-j/2),
  ||Delta_j||_2 <=12*2^(2j).
For theta=(2-p)/p, eta=2(p-1)/p, interpolation yields
  ||Delta_j||_p <=12^eta (A_T+B_T*j*log2)^theta
                    *2^[-j(5/p-9/2)].
This is summable for 1<p<10/9. Positive partial sums, Minkowski,
and monotone convergence prove K*_0 in Lp in that range. No endpoint
claim is made. An explicit norm bound recorded in the note is
  C_p=3+12^eta*(A_T+B_T*log2)^theta
                  /[1-2^(-(5/p-9/2))]^2.

For 0<beta<gamma<1/2, pointwise column Holder gives
  K*_beta <=(K*_gamma)^(beta/gamma)*(K*_0)^(1-beta/gamma).
The prior separation occupation budget makes K*_gamma integrable.
Combining this with any base p0<10/9 and taking gamma towards 1/2
proves the WRITTEN result
  K*_beta in Lp for 0<=beta<1/2, 1<=p<10/(9+2beta).
Consequently every finite logarithmic moment order alpha is allowed
for each fixed beta<1/2. The earlier beta+alpha<1/2 region remains
valid but is no longer the best membership statement. Its earlier
explicit bounds and cutoff errors remain in their original scope.

The truncated density K*_(beta,H) is periodic modulo 3^H. Every
residue occurs at most M/3^H+1 times in an integer interval I of
length M. Therefore
  mean_I K*_(beta,H)^p <=(1+3^H/M)||K*_beta||_p^p.
This is uniform in interval location when 3^H<=M, but it is NOT an
infinite-cutoff integer trace theorem. Haar sets also gain a power
absolute-continuity modulus from ordinary Holder.

Fresh verification passed 2026-10-13T19:07:39.164678+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten
modules were freshly built sequentially; eleven new roots have only
standard axioms, without warnings, sorry, or native evaluation.
The occupation and image records had 29 and 20 hashes authenticated.
The new record contains 26 hashes, all reauthenticated after the run.

Exact replay covered 131071 sources over all binary periods t=0..16,
41109 injective fibres and rank bounds, 17 complete image energies,
and 9841 direct ternary density values through depth eight. Independent
direct adjacent trajectories numbered 65535 through depth sixteen,
including 2552 nonfused return prefixes; all 16 selected-layer
dominations and 16 cumulative energy bounds passed. Further checks:
66339 exact column Holder inequalities, 180 finite periodic interval
power bounds, 4950 interpolation exponent identities, and twelve
weighted exponent examples. All decisions used exact arithmetic.
The finite interval tests use integer beta=0,1,2 and p=2,3 only
to check finite counting; no infinite moment is claimed there.

At t=16 the full image squared norm is
  15611322797/2147483648,
against the general upper bound 170; its largest fibre has 48 sources.
The all-return truncation at H=16 has mass 13623/65536 and squared
norm 3820172355/4294967296. These examples are not asymptotic claims.

Provenance: the distinct-quotient counting idea is attributed to
Valbuena's primary paper linked in the preceding entry and the new
note. No external theorem, stationary Syracuse result, or Tao mixing
result is imported. The proof is the binary-period adaptation above
plus the project's earlier WRITTEN return occupation estimates.

NEXT: return to the actual weighted-gradient pairing with the stronger
density class available. In the unweighted case a complementary Lq
bound would require q>10; for beta it would require q>10/(1-2beta).
The known exceptional point makes an exponential-power norm fail but
does NOT make any fixed polynomial moment fail: its single-point
contribution is a polynomial in m divided by an exponential in m.
One must still handle prefix-dependent image scales and clocks, and
retain correlations as needed. Finite power-moment experiments should
use the actual returned progressions/intervals and exact weights,
without replacing full-period laws by uncontrolled integer sampling.
The first-return-only p<8/7 refinement mentioned in the prior entry
remains a candidate, not a verified theorem and not needed here.

The actual energy bound is still O(sqrt(s)), with no bounded subsequence
proved. Escape and additional cycles remain open. The user's full
Collatz goal remains active. All processes are terminal. No agents,
installs, credentials, staging, commits, or other Git writes occurred.

## 2026-10-13: complete temporal budgets and a PLD-free escape criterion

The previous goal turn was verified progress (binary-image Lp theorem).
This turn made further progress on the actual-gradient question, without
proving the universal condition or full Collatz. Added:
  docs/ANNULUS-TIME-BUDGETS.md
  lean/AnnulusTimeBudgets.lean
  lean/BinaryConePredecessors.lean
  verify_annulus_time_budgets.py
  results/annulus-time-budgets/
README and ATTEMPT contain the result and reproduction command.

NEW WRITTEN SUFFICIENT CONDITION Q:
For every fixed source level k,
  (1/S) sum_(s<S) N^rev_(s,k) -> 0 as S -> infinity.
There is NO uniformity requirement across k. This is weaker than the
previous uniform complementary power norm or a uniform all-time budget.
It is NOT proved for all k. The proof of its implication is:
- On each fixed cell, parent and odd-child weights A_s,B_s decrease
  to limits, and the historical reversal flag is either always zero
  or eventually one. Thus the finite annulus reversed-negative average
  has a limit. Q makes that limit zero.
- The ordered negative averages also tend to zero, using the existing
  sum_(s,k) N^ord_(s,k)<=14. Nonnegativity of the finitely many cells
  yields A_inf*(A_inf-B_inf)_+=0 on every cell. Hence B_inf>=A_inf,
  including when A_inf=0.
- With exact even-child copying, h_k(x)=2^k f_inf(floor(2^k x))
  is nondecreasing in k. It starts at h_0=0 and its limit is <=1/x.
  Sum of squares of nonnegative increments is <= square of their sum,
  so sum_k integral(h_(k+1)-h_k)^2 <=1/2. This is limiting energy,
  NOT an assertion of a bounded subsequence of finite-offset E_s.

The criterion now has a more direct escape implication WITHOUT PLD,
real-scaling measure rigidity, or an external mixing theorem. Reuse
the old six-step inverse child from UniformInverseBranching, choosing
the false branch, and define v_0=1, v_(j+1)=child(v_j,false).
The new kernel induction proves:
  v_j>0, v_j%3!=0, U^(6j)(v_j)=1, wt_(6j)(v_j)=j,
  3 v_(j+1)=64 v_j-d_j with 4<=d_j<=32,
  29*64^j+32*3^j <=61*3^j*v_j <=61*64^j.
The child table for residue r=1,2,4,5,7,8 mod9 has offsets
16,32,80,104,148,160 after 192*floor(v/9), and errors
16,32,16,8,4,32 respectively. The construction works at every depth.

WRITTEN: r_j=3^j v_j/64^j decreases to c in [29/61,1], with
  0<=r_j-c<=(32/61)*(3/64)^j.
Therefore log2(v_j)=j*(6-log2(3))+log2(c)+o(1). Irrational rotation
(log2(3) irrational by prime factorization) and a shrinking error
make the binary significands dense, with arbitrarily late visits to
every open subinterval of [1,2]. Every binary cone
  C(n)={2^ell*n+r : ell>=0, 0<=r<2^ell}
therefore contains arbitrarily large known predecessors v_j of one.
This is leading-digit density, NOT positive natural density.

Under Q, positivity of f_inf(n) propagates to both 2n and 2n+1.
The new kernel binary_cone_closed lemma propagates such closure to
every member of C(n). A spine member in that cone has f_inf=0,
so f_inf(n)>0 is impossible. Thus Q implies W_inf=0 everywhere.
Only the prior WRITTEN packing/weight characterization is then needed
to exclude escape. Other cycles are NOT detected by W_inf and remain
open. Do not conflate this conditional reduction with proving Q.

Quantitative alternatives are also recorded. Define possibly infinite
  T_k=sum_s e_(s,k), R_k=sum_s N^rev_(s,k), L_k=sum_s L_(s,k).
Always L_k<=5/2, by telescoping parent and shifted-parent losses.
For J(S)=ceil(121S/50), K>=J(S), S>=1, the prior geometric tail
and N^rev_(s,k)<=sqrt(e_(s,k)/2) give the WRITTEN inequalities
  sum_(s<S) E_s <=sum_(k<K) T_k+73/20,
  sum_(s<S) E_s <=S/2+2 sum_(k<K) R_k+54.
Consequently a finite lower Cesaro source-level average a of T_k
gives an upper bound 121*a/50 for the lower Cesaro offset energy;
the corresponding average b of R_k gives 1/2+121*b/25. The weaker
charge R_k<=C L_k after summing time would give 1/2+121*C/10.
These hypotheses also imply Q, hence their escape implications now
avoid PLD. None is proved over unbounded source levels.

Exact all-time census: every sampled endpoint is directly checked to
enter {1,2}. Two further cycle steps settle the historical reversal
flag. Both weights multiply by 3/4 every two steps; the squared gap
and reversed negative product multiply by 9/16. The remaining tail
is exactly (16/7)*(cost_phase_0+cost_phase_1). Six new kernel roots
check known-cycle continuation, periodic count comparison, weight
data, and the finite geometric identity. Infinite sums remain written.

For all 32767 parent pairs n,3n+2 with 1<=n<32768 (levels 0..14),
the exact census includes EVERY future offset and verifies
  T_k<4, R_k<5/4, R_k<=L_k.
It also proves R_13>1. Selected display values, backed by rational
enclosures: T_14 about 3.146954, R_14 about 0.963368,
L_14 about 1.729177, and R_13 about 1.010606. The latest tail start
at level 14 is parent clock 214. No universal k bound follows.

The actual return cylinder r=48 mod64 was checked separately at
Q=2^L, M=9Q, L=0,2,4,6,8,10. It uses source [64Q,128Q), image
[M+8,2M+8), and progression x=9q+8, Q<=q<2Q. Its full future field
  G_L(x)=sum_(s>=0)[M*(f_(L+s)(x)-f_(L+s)(x-1))]^2
contributes (1/64)*mean_progression G_L to T_(L+5). This exact
original-source transport was checked. Certified moment enclosures
for p=1,2,4,8,12 are stored on both the progression and full interval.
The pairing with 9*1_(x=8 mod9) is retained exactly. At L=10 the
display means are interval 8.454073/progression 8.683249, and display
L12 norms are 60.893131/48.677974. This neither proves nor disproves
a uniform high power norm as L grows.

Fresh verification passed 2026-10-13T19:42:30.582547+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Seven
modules were built sequentially, and all twelve new roots use only
standard axioms, without warnings, sorry, or native evaluation.
Prior records reauthenticated: persistence 14 hashes, energy caps 16,
escape refinements 16, binary image 26, uniform inverse branching 8.
The final new manifest has 24 hashes, all reauthenticated.

Finite counts: 45052 pairs with certified cycle entry (32767 source
pairs plus 12285 returned-interval pairs), 2906007 exact pre-tail cost
terms, 180208 terminal-phase ratio checks, three complete rational
cross-checks, 45 annulus bounds, 1365 original-source transports, and
60 exact progression/interval pairings. Rounded aggregation used
outward enclosures with denominator 2^96; no floating decisions.
The inverse spine checked 1226 normalized growth bounds and 1225 direct
six-step links; 68 full trajectories were checked separately. By index
1225 it supplies exact cone witnesses for every root 1..1023. The last
new prefix 1023 uses binary shift 5398. Universal cone density remains
the WRITTEN irrational-rotation proof, not finite extrapolation.

Exploratory f64 scouts in /tmp/collatz-gradient-power-scout.rs and
/tmp/collatz-actual-energy-scout.rs ran to level 21 and are terminal.
They suggested testing correlated temporal means instead of assuming
uniform high moments. Their larger-range displays were not adopted as
certified results. A brief primary-source literature search supplied
no external theorem used here. No packages were installed.

NEXT: use the weaker local temporal condition Q as a direct target.
The required statement is now zero limiting reversed negative drift
on each fixed source annulus, or any proved sublinear temporal bound
there. Uniform high moments across annuli are unnecessary for this
criterion. Correlated mean estimates using the Lp return densities
remain possible, and the time-summed whole-annulus charge R_k<=C L_k
is still an alternative, supported only on the finite range above.
The spine/cone lemma applies to any set closed under both binary
children and disjoint from the basin of one; proving such closure
for the full nonconvergence set would also exclude other cycles, but
that closure is NOT proved. Preserve the distinction between escape
and all counterexamples.

Collatz remains unresolved and the full user goal remains active.
All jobs are terminal. No agents, installs, credentials, staging,
commits, or other Git writes occurred in this turn.

## 2026-10-13: cumulative affine return budgets and the 6/5 density range

The previous goal turn was progress. The full conjecture remains
unresolved and the active goal is unchanged. The new substantive result
is WRITTEN, with eight kernel arithmetic roots and exact finite support:

  K*_beta in Lp(mu_3) for 0<=beta<1/2, 1<=p<6/(5+2beta).

For beta=0 this improves p<10/9 to p<6/5. It does not prove the actual
gradient pairing, the temporal criterion Q, escape exclusion, or absence
of other cycles. The grade-sensitive weight considered at the beginning
of this turn was already exactly V_t in GRADE-WEIGHT-MOMENTS.md; no new
result was claimed for that duplicate construction.

Files:
  docs/RETURN-AFFINE-BUDGET.md
  lean/ReturnAffineBudget.lean
  verify_return_affine_budget.py
  results/return-affine-budget/verification.json
  results/return-affine-budget/replay.json and eleven build logs.

Let C_t=lambda_t+B_t=(3^a_t+N_t)/2^t. This is the formal affine image
of one under the sampled parity prefix, NOT generally the actual orbit
of the integer one. New KERNEL identities prove augmented-numerator
recurrence and lifting, exact composition
  C_(t+h)=lambda_continuation*C_t+B_continuation,
the parity-count generating polynomial for every natural argument,
finite drift telescoping with denominators cleared, and the sorted
fibre rank inequality 3^a*(j+1)<=3^a+N_j.

WRITTEN fixed-time moment: for 0<eta<1,
  r_eta=(2^(-eta)+(3/2)^eta)/2<1,
  sup_t E C_t^eta <= A_eta=1+2^(-eta-1)/(1-r_eta).
At a count return the existing fresh-prefix estimates give
  E lambda_tau^eta<=r_eta,
  E B_tau^eta<=m_eta=1+7eta/(1-2eta), for eta<1/2.
Killing at balanced fusion, composing C, and telescoping gives
  E sum_(j<N) C_(S_j)^eta
    <=M_eta=(1+m_eta*C_*)/(1-r_eta), eta<1/2,
  C_*=540*2^5180.
At eta=1/4 the bound is <=40+180*C_*. The sum includes j=0;
the occupation measure uses 1<=j<N and so is also bounded. No
independence between the continuation slope and correction is assumed.

WRITTEN fractional fibre estimate, alpha=p-1>0:
  ||kappa_(t,a)||_p^p <= p*2^(-t)*sum_selected C_t^alpha.
Sort the injective numerator quotients, use
  m^p<=p*sum_(j=1)^m j^(p-1),
then integrate each ternary fibre. Combining all t,a without paying
for their overlap would be invalid; the proof does pay that cost.

The full-period count is Binomial(t,1/2). Define typical counts by
  |a-t/2|<=2*sqrt(t*log(t+2)).
The elementary exponential-moment proof gives atypical mass
<=2*(t+2)^(-8). Holder against the fixed-clock half moment makes
the selected atypical density satisfy
  ||psi_t||_p^p << (t+2)^(17alpha-8),
so these norms are summable for p<6/5.
There are O(H^(3/2)*sqrt(log H)) typical (t,a) components in H<=t<2H.
Using the all-return C^eta budget and the prior occupation-clock tail
O((1+log H)/sqrt H), their combined density Delta_H satisfies
  ||Delta_H||_p^p << H^[3alpha/2-1/2+alpha/(2eta)]
                     *log(H+1)^[alpha/2+1-alpha/eta].
Choosing alpha/(1-3alpha)<eta<1/2 is possible exactly for alpha<1/5.
Dyadic Minkowski and monotone convergence give p<6/5. Column Holder
with the prior separation moments then gives p<6/(5+2beta).
Neither the endpoint nor optimality is claimed.

For beta=0 a complementary power strictly above six could suffice,
instead of strictly above ten. The actual accumulated gradient norm
is still unproved, and the Haar estimate is not an infinite-cutoff
trace bound on a fixed ordinary integer interval. The finite transfer
factor 1+3^H/M remains. This is the same substantive arithmetic gap.

Verification passed 2026-10-13T20:12:43.907413+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Eleven sequential fresh builds took 6.282 seconds; all eight new roots
have only standard axioms and no warnings, sorry, or native evaluation.
The manifest authenticates 28 files. Prior records reauthenticated:
binary image energy 26 hashes, return correction 21, occupation 29.

Exact finite replay checks 36864 compositions, 12288 lifts,
131071 full-period rows through clock sixteen, 102 generating-polynomial
identities, 17 fourth moments, 41109 full and 2232 selected image fibres,
459 full and 174 selected fractional component bounds, 65535 adjacent
return tests, and 2552 nonfused even return prefixes. A full source
period through clock fourteen checks 14109 cumulative return
compositions and eight finite killed-drift inequalities. Direct ternary
moments use 81162 power evaluations, plus 2480 exact dyadic/atypical
exponent checks and twelve weighted exponent checks. Fractional powers
are enclosed with integer roots at denominator 2^48. No floating
comparison decides a claim. Finite p=3/2 checks are explicitly NOT an
infinite integrability result at that exponent.

An editorial correction in ANNULUS-TIME-BUDGETS.md now states correctly
that source-level average budgets are weaker than its uniform charge
(3), but stronger than its qualitative condition Q. The complete
annulus verifier was rerun and passed at
2026-10-13T20:15:34.293783+00:00; its 24 hashes were reauthenticated.
The finite all-future cost results are unchanged. Both final manifests
were independently rehashed after these checks.

### Next candidate: a bounded potential at active gap steps (NOT adopted)

A potentially stronger stopping estimate was derived after the verified
6/5 milestone. It has not yet been written as a reviewed theorem,
formalized, or added to any verification manifest. Check it next rather
than rediscovering it. It may extend returned correction moments to
all eta<1, but no such extension is claimed in the authoritative note.

At absolute count gap d>=1, let W be the wait INCLUDING the next active
step. COUNT-RETURN-CLOCK gives E[W|prefix]<=v(d)+2 with
v(d)=v_2(3^d-1)<=d+1. The next active sign is fair, although W and
the coefficient data can be correlated. The holding time is NOT bounded
deterministically; only this uniform conditional expectation is needed.

For the affine coefficients lambda_W,b_W of either endpoint during
that block, bounded stopping followed by Fatou should give
  E lambda_W^eta <= r_eta,  0<eta<1, W>=1,
  E b_W <= E W/4,
  E b_W^eta <= ((v(d)+2)/4)^eta <= d+3.
Choose r_eta<q<1 and define the bounded half-line Green potential
  h(d)=2 sum_(j>=1) min(d,j)*q^(j-1)*(j+3).
Then h(0)=0, h>=0, and
  [h(d-1)+h(d+1)]/2 = h(d)-q^(d-1)*(d+3).
It is bounded by h(infinity)=(8-4q)/(1-q)^3, with
  h(1)=(8-6q)/(1-q)^2.
The correct closed form is
  h(d)=[8-4q-2*q^d*((d+4)-(d+2)*q)]/(1-q)^3.
A terminal exact rational calculation checked the finite-sum curvature
at d=1,2,7,31 with q=9/10; that calculation alone is not a global proof.

If a current cumulative coefficient is B>=0, put
  F(B,d)=q^d*B^eta+h(d).
Across the active block, B'=lambda_W*B+b_W and d'=d+-1. Thus
  E[q^d'*(B')^eta]
    <=q^(d-1)*(r_eta*B^eta+d+3)
    <=q^d*B^eta+q^(d-1)*(d+3).
The h term cancels the last cost exactly, suggesting F is a
nonnegative supermartingale at active epochs. Stop at gap zero or K
and use nonnegativity at K, then let K increase. The known a.s. finite
return would give E B_return^eta <= F(B_start,d_start).
For a fresh count-return cycle, even D returns in one step; odd D
departs to gap one after one step, with E b_1^eta=2^(-eta-1).
The prospective uniform conclusion is
  E b_tau^eta <= q*2^(-eta-1)+h(1) <= 1+h(1), eta<1.

If this audit succeeds, reuse E lambda_tau^eta<=r_eta to obtain
returned separation drift and all-return C and D moment budgets for
every eta<1, retaining the already proved C_* as the cycle-count
constant. In the present density proof, replacing eta<1/2 by eta<1
would improve the unweighted range to p<5/4 and the separation-weighted
range to beta<1, p<5/(4+beta). Atypical estimate (13) still works for
alpha<1/4. These are prospective consequences, NOT current results.
They would still leave ordinary-integer sampling and actual gradients
uncontrolled, so even a successful potential does not settle Collatz.

All jobs are terminal. A primary-source literature check added no new
external theorem. No agents, installations, credentials, staging,
commits, or other Git writes were used by the assistant. The user
committed the preceding milestone while work continued; preserve the
index and their concurrent changes.

## 2026-10-13: local two-coordinate-obstruction source review

The user explicitly pointed out their local clone and asked whether its
code could help solve Collatz. Reviewed the clean clone at
  /Users/jean/Personal/collatz-two-coordinate-obstruction
  a7275d5a73814d3d9a400c6fe6577de9542b03a3 (2026-10-08).
Use this source rather than redownloading the same manuscripts. The clone
was read only. No new external theorem was replayed or imported into the
local Lean dependency graph. Collatz remains unresolved; the goal is active.

Added:
  docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md
  verify_two_coordinate_review.py
  results/two-coordinate-review/verification.json
README and ATTEMPT link the review and distinguish its external inputs.

The review reads all four paper summaries, the envelope proof, the relevant
energy/occupation/Fourier sections, theorem maps, and selected Lean endpoint
proofs. Independent published-inventory checks authenticate 7,493 distinct
files in eight packages plus four paper/source/map sets. The module manifests
check 2,457 source entries; broader inventories contain 2,522 Lean files,
including audit/provenance sources. These are integrity checks, NOT fresh
Lean compilation or authentication of external compiled libraries. Seven
retained upstream execution records report PASS and are hash authenticated.
Density bundles use Lean 4.30.0-rc2; Fourier uses 4.35.0-rc3. Do not confuse
these records with our earlier completed 389-module PLD replay.

NEW WRITTEN EXTERNAL DEDUCTION: denote our full binary image density by b_t
to distinguish it from their Syracuse cylinder rho^S_k. Exact parity-word
enumeration gives b_0=1 and b_(t+1)=L b_t, where
  Lf(z)=f(2z)/2+(3/2)1_(z=2 mod3)f((2z-1)/3).
The new external envelope satisfies LE<=E POINTWISE, E>=c>0 on units,
E(n)=g(n)=delta G_n n D_n at every positive integer, and E in Lp for p<2.
Here delta=log(4/3)/2, G_n is the periodic Green factor, D_n the actual
weighted first-hit density. Write h=(3/2)1_(z=2 mod3). Then
  b_t=2^-t+sum_(j<t)2^(-(t-1-j)) L^j h
     <=2^-t+(3/c)(1-2^-t)E.
This proves externally dependent uniform full-image Lp bounds for every
1<=p<2 and b_t(n)<=2^-t+(3/c)g(n) at fixed positive integers. It improves
the previous time-growing bound for the full law, not the all-return law.
The integer majorant g is unbounded in every unit residue class.

A common-noise coupling with a stationary binary affine chain gives weak
convergence of b_t to the stationary law: the difference acquires a factor
3^a with a~Binomial(t,1/2). Uniform L2 bounds would then bound all stationary
cylinder L2 norms and contradict the external non-L2 theorem. This is a
written external consequence, not a local kernel theorem or a claim about
the optimal exponent of our selected return density.

For dyadic all-return block Delta_H, uniform per-clock Lq gives ||Delta_H||q
<=C_q H, while the existing L1 clock tail is O(H^-1/2 log H).
Interpolation yields p<3q/(2q+1); taking q<2 recovers p<6/5 only.
Our prior independent RETURN-AFFINE-BUDGET proof is unchanged. No stronger
all-return exponent, actual-gradient estimate, or infinite-cutoff integer
sampling bound follows from this review.

MOST USEFUL TARGETS IN THE CLONE:
- GammaFreeFirstHitCoefficient.lean discharges its reciprocal-density floor
  in the public endpoint; exact first-hit coefficients satisfy a_k(N)<=L N D_N
  at positive odd depths, including periodic targets. Its finite fan selects
  a unit nonperiodic predecessor with exponent <=6 and uses disjoint basins.
- MaskedEnergyPeriodicityEquivalence.lean proves E_K/(K+1)->0 iff every
  positive orbit is eventually periodic. E_K is the squared normalized
  Syracuse cylinder density at odd N<3^K with no return in <=K odd steps.
  This is NOT our dyadic E_s. The decomposition controls the no-small-ancestor
  portion by L epsilon(M)(2+3K+(64/81)^K(1+2K)), epsilon(M)->0. The remaining
  small-ancestor portion is on actual forward orbits of bounded seeds and
  remains open. Even a successful estimate permits additional cycles.
- RawOccupationDivergentExcess.lean proves that a divergent odd unit root
  forces liminf sum_(odd N<=R)D_N/log R >=1/log(4/3)
  +D_u/(P_infinity(u)log(3/2)), with a strictly positive additional term.
  The matching upper bound is open. ActualInverseHeightClock.lean proves an
  a.s. inverse-path height rate at fixed nonperiodic unit roots, without the
  expectation/uniform-integrability estimate needed for that upper bound.
- The Fourier theorem selects exact TOTAL-EXPONENT slices, uniformly in
  affine seed and total-exponent phase. It does not select arbitrary paired
  return histories. Polynomial slice mass does not repair this distinction:
  conditioning a uniform cyclic law on its first third of residues gives
  probability 1/3 and a primitive Fourier coefficient with modulus >=1/2.

Exact local finite checks passed: 2,047 direct binary residue rows, 2,047
independently generated affine words, 88,572 full ternary transfer values
through depth ten, 2,816 actual positive-target inverse-tree comparisons,
and four rational interpolation exponent tests. These certify finite
identities only. The written all-depth operator argument is in the review.

CURRENT UNADOPTED CANDIDATE: before the clone review, added
lean/ActiveGapPotential.lean. Its nine standalone kernel arithmetic roots
passed a development build using the existing temporary dependency objects:
min/Green curvature, nonnegative Green cap, two geometric polynomial
identities and caps, and exact fractional-slope constants. This has no final
verification manifest or completed analytic note yet. The prospective
eta<1 return moment and p<5/4 all-return range in the preceding entry are
still NOT adopted. Resume that audit without mistaking the development
module for a complete verified milestone.

No agents, installations, credentials, staging, commits, or other Git
writes were used. Preserve the user's index and existing changes. The next
research step can use the external majorant as an explicitly stated input,
or continue the independent active-gap potential; neither route has closed
the actual-gradient/integer-sampling gap.

## 2026-10-13: active-gap potential and the 5/4 density range

The previous local-clone review turn was progress. This turn completed
the formerly unadopted active-gap potential. The new infinite results are
WRITTEN, with nine kernel arithmetic roots and independent exact finite
checks. The Collatz objective remains active and unresolved.

Files:
  docs/ACTIVE-GAP-POTENTIAL.md
  lean/ActiveGapPotential.lean
  verify_active_gap_potential.py
  results/active-gap-potential/verification.json
  results/active-gap-potential/replay.json and twelve build logs.
README and ATTEMPT link the new result. The prior 6/5 note remains intact
as a verified earlier result. The local-clone review now links this later,
independent improvement; its own new stationary comparison is still an
external deduction and is not used in the active-gap proof.

At a nonzero absolute count gap d, the physical wait W INCLUDING the next
active step has conditional mean <=v_2(3^d-1)+2. Bounded physical stopping
and Fatou give, for either endpoint and every 0<eta<1,
  E lambda_W^eta <=r_eta=(2^-eta+(3/2)^eta)/2<1,
  E b_W <= E W/4,
  E b_W^eta <=d+3.
The last bound needs only v(d)<2d and concavity; no deterministic wait
bound is used. The two endpoint parities, wait, and active sign can be
correlated. Each marginal next parity is fair, and the next active sign
is conditionally fair under the coherent binary residue law.

Choose r_eta<q<1. The bounded half-line Green potential is
  h_q(d)=2 sum_(j>=1)min(d,j)q^(j-1)(j+3),
  h_q(0)=0, h_q(1)=(8-6q)/(1-q)^2,
  0<=h_q(d)<=(8-4q)/(1-q)^3,
  [h_q(d-1)+h_q(d+1)]/2=h_q(d)-q^(d-1)(d+3).
For current cumulative correction B, define F(B,d)=q^d B^eta+h_q(d).
Across an active block B'=lambda_W B+b_W and d'=d+-1. Using
q^d'<=q^(d-1) gives
  E[q^d' B'^eta]<=q^d B^eta+q^(d-1)(d+3).
The h curvature cancels this cost exactly. Thus F is a nonnegative
supermartingale at ACTIVE epochs. Finite active-step cutoffs followed
by Fatou are sufficient: the fair gap walk hits zero a.s. from every
finite gap, and every wait is finite a.s. by its finite expectation.
No optional-stopping equality or integrability of the full physical
return time is assumed.

For a fresh count-return cycle, even separation returns in one step.
Odd separation first departs to gap one. Both cases give the uniform
conditional bound
  E b_tau^eta<=b_eta:=1+h_q(1), all 0<eta<1.
This replaces eta<1/2. For eta=1/2,3/4,7/8 take q=63/64,127/128,255/256
and obtain b_eta=8577,33537,132609 respectively. These are coarse constants;
retain the older quarter-power constants when using the old EN estimate.

Use C_t=lambda_t+B_t, the FORMAL image of one under the sampled parity
word, and retain C_*=540*2^5180 as the bound on E N. Killing at balanced
fusion and finite drift telescoping prove
  E sum_(j<N) C_(S_j)^eta <=(1+b_eta C_*)/(1-r_eta),
  E sum_(j<N) D_j^eta <=(1+2b_eta C_*)/(1-r_eta), 0<eta<1.
These sums include j=0; the occupation measure uses 1<=j<N. Restricting
to even initial sources only decreases nonnegative integrals.

For eta>=1/2, concavity of 1-r_eta and the exact half-moment cap imply
1-r_eta>=(1-eta)/16. Choose q=1-(1-eta)/32. Then
  b_eta<=8193/(1-eta)^2,
  both occupation moment budgets <=B/(1-eta)^3,
  B=16(1+16386 C_*).
Choosing eta=1-1/log_2 u for u>=4 gives
  nu(C>u),nu(D>u)<=2B(log_2 u)^3/u,
  Pr(b_tau>u)<=16386(log_2 u)^2/u.
No endpoint first moment is asserted.

The previous fractional-fibre and binomial-concentration proof now takes
alpha/(1-3alpha)<eta<1, alpha=p-1, which is possible iff alpha<1/4.
The atypical exponent (17alpha-8)/p is still <-1. Dyadic Minkowski yields
  K*_0 in Lp for 1<=p<5/4.
Column Holder with D^gamma moments for gamma<1 gives the stronger range
  K*_beta in Lp for 0<=beta<1, 1<=p<5/(4+beta).
The method's limiting dyadic exponent is 2alpha-1/2. Its range is not
claimed optimal; stronger overlap or joint clock/coefficient control would
be needed to improve this component-counting argument further.

Holder against the existing O(H^-1/2 log H) clock tail and the near-one
moment constants also gives the written truncation rate
  ||K*_beta-K*_(beta,H)||1
    =O_beta(H^(-(1-beta)/2)(1+log H)^(1+2beta)), beta<1.
The unweighted complementary gradient exponent can now be any q>5.
Actual accumulated-gradient power bounds and infinite-cutoff integer trace
sampling are still unproved. The finite transfer still has its
1+3^H/M factor. The temporal criterion Q and exclusion of other cycles
remain open. No external stationary result was needed for these bounds.

Final verification passed 2026-10-13T21:00:53.975945+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Twelve sequential fresh builds took 4.729 seconds. All nine new roots
use standard axioms only; no warnings, admitted proof or native evaluation
occurred. The manifest authenticates 31 files. The affine-budget,
occupation, and count-clock prior records had 28,29,11 hashes checked.

Exact finite replay checked 1,584 integer Green curvatures, 375 geometric
identity pairs, 1,152 exact series remainders, 384 rational curvatures/caps,
three fractional slope/budget constants, and 31 near-one chord comparisons.
It checked 270,816 actual active-block paths at gaps 1,2,3,4,8,16,31,32 and
varied affine offsets, retaining unfinished paths through clock caps
4,8,12; 404 bounded-stop slope/correction identity pairs; 1,488 active-time
sign balances; 3,348 partial terminal potential bounds with initial
correction 0,1,16; and 1,116 partial block moment comparisons.
Fresh-return tests covered 34,816 paths at eight starting separations,
plus 96 moment bounds. A complete binary period through clock fourteen
checked 20,239 cumulative compositions (including terminal fusion),
84,654 fractional moment values at nonfused returns, 48 killed drift
bounds and six finite total budgets. There are 3,120 exact density-exponent
and fifteen weighted-exponent checks. Fractional roots use outward rational
enclosures at denominator 2^48, reusing and authenticating the earlier
integer-root implementation. No float decides a verification inequality.

The review verifier was rerun after its follow-up link changed, passing at
2026-10-13T21:00:48.377013+00:00. Final independent rehashes checked all
31 potential files and all four review-local hashes; local links passed.

NEXT: the active-gap candidate is now completed, so do not restart it as
unadopted. The remaining problem needs information about actual gradients
or integer sampling, or a sharper structural treatment of the selected
return columns. A possible identity to audit if grouping by common odd
count helps: let A f=f(2z)/2 and B f=(3/2)1_(z=2 mod3)f((2z-1)/3).
For the FULL binary density pieces rho_(t,a), summing over t at fixed a
formally gives Sigma_0=2 and Sigma_a=(I-A)^(-1)B Sigma_(a-1), suggesting
Sigma_a=2 rho^S_a for the canonical Syracuse cylinder density. This is
only a recorded lead, not a new theorem or verification claim. A uniform
norm per count alone would still recover only p<6/5 with the current
clock tail; any improvement needs the selected-return structure as well.

All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's concurrent
work and index. The full positive-integer conjecture remains unresolved.

## 2026-10-13: fixed-integer return Cesaro limit from the local clone

This goal turn is progress. It completed a new WRITTEN, externally
dependent arithmetic consequence of the local obstruction repository:
  K*_(0,H)(n)/H -> 0 for EVERY FIXED positive integer n.
Here K*_(0,H)=sum_(1<=t<=H)kappa_t is the unweighted density accumulated
over all nonfused equal-count returns of even initial adjacent pairs.
This is a fixed ordinary-integer trace statement, not just Haar-a.e.
It is sublinearity of a truncated sum, NOT finite total occupation,
pointwise decay of kappa_t, uniformity for growing target intervals,
the temporal criterion Q, or the Collatz conjecture.

Files:
  docs/INTEGER-RETURN-CESARO.md
  lean/IntegerReturnCesaro.lean
  verify_integer_return_cesaro.py
  results/integer-return-cesaro/verification.json
  results/integer-return-cesaro/replay.json and four build logs.
README, ATTEMPT, and the local-clone review link this follow-up.

EXACT INTEGER BRIDGE:
Existing CollatzPacking.residue_image_bound already proves
  U^t(r)<3^a for r<2^t, a=wt(t,r).
It was NOT necessary to rediscover that bound. New kernel roots transfer
the packing definitions to CollatzAffine and prove that a matching
positive target column n=U^t(r) mod3^a has a unique nonnegative quotient
q=floor(n/3^a), hence a positive actual source m=2^t q+r reaching n.
Conversely every positive predecessor has this residue and quotient.
Thus b_t(n)=sum_(m>0,U^t(m)=n)3^wt(t,m)/2^t exactly. Balanced fusion
and count equality lift with the residue. Kernel source bound m<=2^t n
makes every finite-clock inverse sum finite. Balanced fusion persists,
so nonfusion at t implies nonfusion at every L<=t; its mask has period 2^L.

EXTERNAL INPUTS, NOT LOCALLY REPLAYED:
Clone still clean at a7275d5a73814d3d9a400c6fe6577de9542b03a3.
WeightedSourcePeriodicMean.lean proves, for ANY fixed periodic p in[0,1],
  X^-1 sum_(m<=X) w_n(m)p(m) -> D_n mean(p).
There is NO odd/unit support restriction in this source-mean theorem.
FirstHitWordWeights.lean gives lambda_firsthit=n*w_n(m)/m, w in[0,1].
ActualUnconditionalCanonicalTrace.lean proves zero logarithmic density
of first-hit ELAPSED SHORTCUT clock exceptions among odd basin sources,
with drift delta=log(4/3)/2. Its sources may be divisible by three.

IMPORTANT SUPPORT AUDIT:
PeriodicMarkedFirstHitMeanFromSources.lean's PUBLIC marked theorem has
odd-unit support and an odd-count clock. It is not directly applicable
to our nonfusion masks. The new deduction explicitly uses the more
general source mean plus the separate elapsed clock, not an unstated
strengthening of the public marked theorem.

WRITTEN PROOF:
For m=2^ell q with q odd and q>n, first-hit clocks satisfy
tau_n(m)=ell+tau_n(q). At fixed ell, the difference from
log(m)/delta is a fixed shift of the odd clock error. Thus each fixed
valuation layer inherits zero logarithmic exception density. The
remaining layers have harmonic mass at most 2^-J(1+log X). Take X->infinity
first and J->infinity next to extend the clock law to all positive sources.
Initial-halving hits are finite exceptions on each retained layer.

Partial summation gives sum_(m<=X)w_n(m)p(m)/m
=D_n mean(p)logX+o(logX). Squeeze the finite first-hit mass F_H^p(n)
using good-clock cutoffs exp(delta H/(1+-epsilon)); bad sources contribute
o(H) because every hit by H has m<=2^H n. Thus
  F_H^p(n)/H -> delta*n*D_n*mean(p).
No new unbounded-source tail estimate is needed.

Let B_t^p(n)=sum_(m>0,U^t(m)=n)lambda_t(m)p(m).
At a nonperiodic target, total visits through H equal first hits.
At a periodic target of least period R and ratio rho=3^a/2^R<1,
  sum_(t<=H)B_t^p(n)=sum_(jR<=H)rho^j F_(H-jR)^p(n).
The convergent first-hit mean gives F_h<=C(h+1), so geometric dominated
convergence proves
  H^-1 sum_(t<=H)B_t^p(n) -> g(n)mean(p),
  g(n)=delta*G_n*n*D_n, G_n=(1-rho)^-1 if periodic and 1 otherwise.
This is physical-time Cesaro, not the external Syracuse-depth statement.
Setting p=1 also identifies the Cesaro limit of our full b_t(n).

Now p_L(m)=nonfusion of (m,m+1) by L is periodic modulo 2^L with mean
q_L=Pr(T>L)->0 by our existing WRITTEN coherent-binary clock bound.
For t>=L, selected actual returns satisfy kappa_t(n)<=B_t^(p_L)(n).
Hence limsup_H K*_(0,H)(n)/H<=g(n)q_L for each fixed L. Send L->infinity.
This proves the claimed fixed-target limit. It is uniform over each
FIXED finite target set, implies zero time density of kappa_t(n)>=epsilon,
and implies the corresponding vanishing Abel average. There is no rate
uniform in the period 2^L or target n. The old proposed fixed-odd-count
identity Sigma_a=2rho^S_a was bypassed and remains only a recorded lead.

VERIFICATION:
Final record passed 2026-10-13T21:18:28.322266+00:00 on pinned Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Four fresh sequential
builds took 1.327 seconds. All nine audited roots use standard axioms only;
no warning, admitted proof, or native computation. Thirteen local hashes,
eleven prior clock hashes, four review-local hashes, and nine specific
external source hashes were authenticated. The review was refreshed at
2026-10-13T21:18:26.254688+00:00 after the new link; all 7,493 distributed
hashes and its existing exact finite transfer checks passed again.

Exact finite checks through clock 12 and targets 1..128:
8,191 residue endpoint bounds; 15,832 positive column preimages;
1,664 complete residue/inverse-tree bijections; 15,615 first-hit weight
identities; 101,364 lifted mask/selection checks; 7,424 marked selection
bounds; 19,968 finite all-visit reconstructions with twelve periodic marks;
the known periodic targets 1 and 2; 10,668 dyadic first-hit clock transports;
2,322 exact dyadic harmonic tail identities. Rational finite averages are
diagnostics only, with no convergence-rate claim or nonperiodicity
inference from a finite search. No floating value decides a check.

NEXT GAP:
The new theorem handles fixed inverse targets. It does not control the
moving endpoints of a hypothetical divergent forward orbit, nor sum
actual gradient costs. Their target dependence can grow while every
fixed-target Cesaro limit still vanishes. A moving-target or joint
source/target estimate is still needed; do not infer Q from (1). The
external inverse Doob height clock likewise lacks the expectation/UI
bound needed for the raw occupation upper estimate. The independent
active-gap potential and p<5/(4+beta) range remain completed and valid.

All work is terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's index and
existing changes. The Collatz goal remains active and unresolved.

## 2026-10-13: independent uniform harmonic return trace bound

This goal turn is progress. A new WRITTEN argument strengthens the last
integer Cesaro conclusion and REMOVES its external analytic dependencies
for that conclusion. It proves, for EVERY n>0 and integer H>=1,
  K*_(0,H)(n) <= Z_H(n) <= 350 C_star n G_n sqrt(H),
  C_star=540*2^5180.
Z_H counts ALL nonfused inverse visits, not just even-source equal-count
returns. G_n=1 for nonperiodic n and (1-rho)^-1 for a periodic target,
rho=3^a_R(n)/2^R at its least positive shortcut period R.
New kernel arithmetic proves G_n<=3n+1 in all cases. No unknown cycle
is assumed absent. The Collatz goal remains active and unresolved.

Files:
  docs/HARMONIC-RETURN-TRACE.md
  lean/HarmonicReturnTrace.lean
  verify_harmonic_return_trace.py
  results/harmonic-return-trace/verification.json
  results/harmonic-return-trace/replay.json and five build logs.
README, ATTEMPT, the earlier integer Cesaro note, and the clone review
link this stronger follow-up. The older marked full-image identification
g(n)*mean(p) REMAINS an external deduction; it was not reclassified.

NEW WRITTEN PROOF:
Let p_L(m) be nonfusion of (m,m+1) by clock L, and q_L its full binary
period mean. p_T<=p_L for L<=T; p_L has period 2^L; q_0=1.
Reuse the existing local WRITTEN fusion tail q_L<=A/sqrt(L), L>=1,
with A=14 C_star. No external density, clock or envelope input is used.

For any hit U^t(m)=n with t<=h, local arithmetic gives
  m<=2^h n,   2^h(n+1)<=3^h(m+1).
Thus any two positive sources u,v reaching n by h satisfy
  v<=3^h(u+1)<=2*3^h*u.
Their complete source interval meets at most 2h+2 binary ranges
[2^j,2^(j+1)), independently of n. This controls the RATIO of source
sizes, so no log(n) term or fixed-target asymptotic is needed.
The affine lower bound also gives lambda_t(m)/n<=1/m.

For a binary SOURCE range j and mask clock T, put L=min(j,T).
The mask p_L has exactly 2^j q_L marked points in that full range;
p_T<=p_L and 1/m<=2^-j imply
  sum_(2^j<=m<2^(j+1)) p_T(m)/m <= q_min(j,T).
The earlier mask is essential for small sources. At m=1, p_12(1)=1,
while q_12=655/1024. Replacing every band bound by q_T is false.
Write Q_T=sum_(j<T) q_j. Any interval meeting B source ranges has
harmonic p_T mass <=Q_T+B*q_T. From the square-root tail,
Q_T<=2 A sqrt(T) for T>=1 (the initial j=0 term is included).

Let F_H(n) count FIRST hits through H with coefficient lambda_tau and
mask p_tau. In a clock block T<=tau<2T, the sources lie in P_(2T-1)(n),
whose interval meets at most 4T binary ranges. Hence
  block mass/n <=Q_T+4T*q_T <=6 A sqrt(T).
Sum blocks T=1,2,4,...<=H. Their square roots sum to less than 4sqrt(H).
The clock-zero source m=n adds at most one after division by n.
Therefore F_H(n)<=25 A n sqrt(H), uniformly over n.

If n is nonperiodic, Z_H(n)=F_H(n). If it is periodic, each source's
later visits acquire factors rho^j and their nonfusion masks can only
decrease. Thus Z_H(n)<=G_n F_H(n). An actual positive cycle has an odd
step; the new positive-count coefficient inequality
  (3m+1)3^a_t(m)<=3*2^t*U^t(m) whenever a_t(m)>0
gives rho<=3n/(3n+1)<1 and G_n<=3n+1. This proves the stated bound.

CONSEQUENCES:
- sup_(n>0) K*_(0,H)(n)/(H n G_n)<=350 C_star/sqrt(H).
- For each fixed positive target, the previous vanishing Cesaro limit
  now has an independent O_n(H^-1/2) proof, also for the larger Z_H.
- Unnormalized convergence is uniform on all-target windows
  n<=R(H)=o(H^(1/4)); on nonperiodic targets, R(H)=o(sqrt(H)) suffices.
- For every sigma>1/2, the ACTUAL integer trace with a time discount
  sum_(t>=1)t^-sigma kappa_t(n) is finite, bounded by
  350 sqrt(2) C_star n G_n / (1-2^(1/2-sigma)).
- Its Abel average satisfies
  (1-z)sum_(t>=1)kappa_t(n)z^t
     <=350 C_star n G_n sqrt(z(1-z)), 0<z<1.
These are written consequences, not additional kernel real-analysis claims.

VERIFICATION:
Final record passed 2026-10-13T21:37:01.446836+00:00. Five fresh sequential
builds took 2.649 seconds on pinned Lean 4.33.1 commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten audited roots use standard
axioms only, with no warnings, admitted proofs, or native computation.
The manifest has fourteen local hashes and authenticates all eleven
hashes of the prior count-return-clock record. No external source or
compiled external library is needed for this proof.

Exact finite checks at clock cap 16 and 134 targets, including targets
2^40+1 and 2^80+17, passed:
131,071 direct residue masks; 983,041 positive-count correction bounds;
187 nested range population checks and 187 exact harmonic range bounds;
882 rational harmonic interval comparisons; 52,173 actual inverse paths
and coefficient checks; 2,278 predecessor span bounds; 670 first-hit
clock blocks; both known periodic targets 1 and 2; 2,144 nonfusion and
selected-return trace comparisons. A finite-table coefficient A=3 fits
the tested mask table ONLY; it is not an all-depth constant claim.
All verification decisions use integers or exact fractions.

The older review was refreshed after its new follow-up link at
2026-10-13T21:35:54.949033+00:00 (all 7,493 source hashes passed again).
The original integer Cesaro record was refreshed at
2026-10-13T21:35:58.316654+00:00 after the historical note gained the
independent-proof link. Its original full marked limit still depends
on the external theorems. No external Lean replay was done.

REMAINING GAP / NEXT RESEARCH:
The sqrt(H) bound still allows a persistent individual contribution at
a moving divergent-orbit target: lambda_t(m)/U^t(m)=W_t(m)/m may tend
to a positive number. Thus this does not prove Q or absence of escape.
Time-discounting the inverse returns does not pay for an arbitrarily
long future excursion following one fixed return prefix; actual gradient
costs and their correlations remain the issue. Finite total undiscounted
occupation at a fixed integer also remains open. The source/count
grouping lead Sigma_a=2rho^S_a remains unused, not adopted.

All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's index and
concurrent changes. The full Collatz goal remains active and unresolved.
