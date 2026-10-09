# Collatz project memory

Last updated: 2026-10-09, after cutoff and precision budgets for exit-mass certificates.

**Current status: active following the user's resumption.** Collatz remains
unresolved. The latest entry quantifies necessary cutoff and precision
growth for an infinite exit-certificate extension. The 128 existing
finite-horizon contractions remain the full certified scope.

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
