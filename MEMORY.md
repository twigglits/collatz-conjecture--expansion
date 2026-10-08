# Collatz project memory

Last updated: 2026-10-08, after the mixed-residue inverse-basin construction.

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
- Current workspace:
  `/home/jeannaude/Documents/collatz-conjecture--expansion`.
  Linux, Bash, timezone Africa/Johannesburg. The current machine is weaker
  than the previous session's machine; recorded hardware is an i7-8550U
  with 16 GB RAM. Allow longer Rust/Lean runs and avoid concurrent heavy
  compiles. A short tool timeout is not a mathematical or build failure.
- [lean-toolchain](lean-toolchain) pins `leanprover/lean4:v4.33.1`.
  The last verified compiler commit is
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
  The local executable is `/home/jeannaude/.elan/bin/lean`.
  Rust 1.94 was available in this session; recheck if needed.
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
