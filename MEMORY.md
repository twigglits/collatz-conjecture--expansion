# Collatz project memory

Last updated: 2026-09-13, after the mask rank arithmetic verification and the
user's request to preserve project context.

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
