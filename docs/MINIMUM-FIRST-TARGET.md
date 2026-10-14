# Near-source exclusions and a sharp first-target obstruction

The mixed-predecessor method gives a stronger restriction near a
hypothetical least counterexample, but reaching an improved target
class for the first time does not itself supply a smaller source.
Both conclusions now have parameterized kernel proofs.
Combining the new exit restriction with the earlier least-source
restrictions also determines the first target of a hypothetical least
counterexample: the best zero/one-even inverse word recovers exactly
that source. This general deduction is written out in Section 5.

The [new Lean module](../lean/MinimumFirstTarget.lean) contains 23
audited roots. Its explicit convergence examples use axiom-free
kernel computation. There is no new external premise and no novelty
claim. **The positive-integer Collatz conjecture remains unresolved.**

## 1. An exact meeting with a source half as large

Let k>=1, q>0, and suppose

    3^k q = 4v+3.

Set

    p = 2^k q-1,    n = 2^(k+1)q-1 = 2p+1.

The kernel proves the two ordinary-clock identities

    C^(2k+3)(p) = 3v+2 = C^(2k+4)(n).             (1)

The larger source makes k+1 odd shortcut steps, followed by two
even-input shortcut steps. The smaller source makes k odd shortcut
steps, then one even step and one odd step. In detail, their block
endpoints are

    n -> 3^(k+1)q-1 = 4(3v+2) -> 2(3v+2) -> 3v+2,
    p -> 3^k q-1 = 2(2v+1) -> 2v+1 -> 3v+2.

The arrows for odd blocks stand for their stated number of shortcut
steps; each final odd shortcut comprises two ordinary steps. This
accounts for the one-step difference between the ordinary clocks
in (1). There is no claim that either finite path is globally minimal.
The endpoint identity also holds at k=0, though the near-source
corollary below retains k>=1 and positive p.

For example, 35 and 17 meet at 20 after six and five ordinary steps.
The smaller source need not occur on the larger source's forward
path; coalescence is enough for leastness.

## 2. A restriction throughout a band above the least source

Let A be a least positive counterexample. Every positive source
whose orbit meets its component is at least A, by the earlier
[component-minimality theorem](MINIMUM-ROOT-PREDECESSORS.md).
If n=C^t(A) has the form in Section 1, (1) forces p>=A. Therefore

    n >= 2A+1.                                    (2)

This is kernel checked. It applies at any actual ordinary time t;
no first coefficient contraction or chosen return time is required.

Equivalently, suppose an orbit value y<=2A has a maximal initial odd
shortcut block of length K>=2. Write y=2^K q-1 with q odd. Its
post-block even value is 3^K q-1. The kernel proves

    3^K q = 3 mod4.                               (3)

Thus it has exactly one even-input shortcut step before the next odd
step. A post-block value divisible by four would give the forbidden
half-sized coalescing source. In particular (3) holds for y=A.

The hypotheses matter. This result does not assert K>=2 for every
orbit value below 2A. Nor does it impose the same condition on values
above the band in (2). It constrains possible returns near A without
proving that enough such returns occur.

A related initial-block/near-return restriction is described in a
[public near-return note](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/main/proof-search/lemmas/L11_Near_Return_Hard_Exit_Inheritance.md).
That note uses a coefficient-contraction hypothesis and treats odd
and even block lengths separately. The local proof here derives the
meeting (1) directly for both parities and uses only component
leastness and the band y<=2A. No claims about coefficient stopping
times, external convergence ranges, or the note's other lemmas enter
the kernel proof.

## 3. Why first occurrence of an improved target is insufficient

The previous [mixed ancestry note](MINIMUM-MIXED-ANCESTRY.md) identifies
targets for which one even-input shortcut step gives a predecessor
smaller than every all-odd predecessor. The class 20 modulo 27 is
contained in that target set.

The primary [sufficient-set paper](https://arxiv.org/html/1204.3904v2)
states that every nontrivial cycle or divergent orbit meets this
class. That occurrence theorem alone does not compare the new
predecessor with the original least source. It is context only here;
our next construction and its first-visit proof are independent of it.

For h>=0 define

    K = 6h+3,
    n_h = 5*2^K-1,
    v_h = (5*3^K+1)/4,
    b_h = 3v_h-1 = (5*3^(K+1)-1)/4,
    T_h = 2K+3.

All these quantities are integers. The kernel proves

    C^T_h(n_h) = b_h,    m_T_h(n_h) = n_h,
    b_h = 20 mod27,
    C^t(n_h) != 20 mod27 for every t<T_h.           (4)

The shortcut parity word is exactly K odd inputs, one even input,
then one odd input. Its endpoint and odd count are independently
formalized from the ordinary-clock proof.

The first-visit argument is explicit. The starting source is divisible
by three; the first completed odd pair gives residue 5 modulo 27.
Every later completed pair in the initial odd block is 8 modulo 9,
and every intervening ordinary odd image is 1 modulo 3. The two
remaining ordinary states before b_h also avoid 20 modulo 27. Thus
(4) concerns the first ordinary visit, not just a sampled clock.

## 4. The best one-even predecessor equals the original source

For the targets in (4), the new module proves these universal bounds:

    b_h=3^j v-1, v>0
        => 2^j v-1 >= n_h;                        (5)

    b_h=3^j v-1, v>0, 3^k q+1=2^(j+1)v
        => 2^k q-1 >= n_h.                        (6)

They cover every all-odd inverse block and every pair of odd blocks
separated by one even input. Equation (4) itself gives an actual
one-even predecessor equal to n_h. Consequently the complete minimum
over these two word classes is exactly n_h. The parameterized bounds,
attaining path and parity count are kernel results; identifying an
arbitrary zero/one-even word with one of these forms is a written
finite-word decomposition.

The arithmetic explains the equality. Since b_h=20 modulo 27,
the last all-odd inverse block has length at most one. With length
zero, the intervening doubling has no odd inverse parent. With length
one, the equation for the preceding block becomes

    3^k q = 5*3^K.

The kernel proves that this implies 5*2^K<=2^k q. Equality occurs at
k=K,q=5, recovering n_h. Thus the first encounter can recognize the
source's existing path rather than give a new smaller coalescing source.

This remains true at unbounded relative target heights. The kernel
also proves

    (h+1)(n_h+1) <= b_h+1,    h<n_h.               (7)

Taking h arbitrarily large disproves an unconditional constant bound
on the first target's height relative to its source, and disproves
the unconditional claim that its best one-even predecessor is always
strictly smaller than that source. These witnesses are not least
counterexamples. The next argument separately applies the known
least-source restrictions themselves.

## 5. The first target of a least counterexample is already determined

Here is a written generalization of the first-target calculation.
For a positive source n write n+1=2^K q with q odd, and assume

    K>=2,    3^K q=3 mod4,    n!=2 mod3,    n!=4 mod9.       (8)

Put v=(3^K q+1)/4 and b=3v-1. The first ordinary visit to
20 modulo 27 is then

    C^(2K+3)(n)=b=(3^(K+1)q-1)/4.                           (9)

Moreover, the minimum of all predecessors of b using at most one
even-input shortcut step is exactly n. These are finite-word
statements; neither presumes that n fails to converge.

To prove (9), the shortcut path is K odd steps, one even step, then
one odd step. The existing `one_even_block` theorem supplies its
endpoint and prefix minimum n. Its final value satisfies
4b+1=3^(K+1)q, so b=20 modulo 27. The earlier states avoid this
class for the following reasons:

- The starting value is not 2 modulo 3 by (8).
- The first completed odd pair, (3n+1)/2, is 20 modulo 27 exactly
  when the odd n is 13 modulo 18, equivalently 4 modulo 9. This is
  excluded by (8).
- At every completed pair with index 2<=i<=K, the value plus one
  is 2^(K-i)3^i q, hence divisible by nine. The value is therefore
  8 modulo 9. Every intervening odd-image state is 1 modulo 3.
- The remaining two ordinary states are 2v-1 and 2b. Since
  4v=3^K q+1 implies v=1 modulo 3, both are 1 modulo 3.

For the inverse minimum, b+1 has ternary valuation exactly one:
the complete all-odd inverse chain consists of b and c=2v-1.
The condition n!=2 modulo 3 means 3 does not divide q. Doubling
b gives 2b, which has no odd inverse parent. Doubling c gives

    2c=3^K q-1.

Its complete odd-inverse chain has the values

    2^i*3^(K-i)q-1,    0<=i<=K.

They strictly decrease to 2^K q-1=n, and the chain stops there
because 3 does not divide q. The pure-chain minimum c is larger
than n: 3^K>=2^(K+1) for K>=2, and
c+1=(3^K q+1)/2>2^K q. Thus no other candidate is smaller and n
is attained. This enumerates every possible position of the single
inverse doubling, so it proves the claimed complete minimum.

Every hypothetical least counterexample A satisfies (8). The existing
kernel results `least_mod4`, `least_not_two_mod3`, and
`least_not_four_mod_nine` supply three conditions; the new
`least_initial_exit_constraint` supplies the remaining modulo-four
exit condition. Factoring A+1 by its maximal power of two then gives
(9) with n=A and inverse minimum exactly A.

This last general assembly, including maximal factorization and
complete inverse-word enumeration, is **written mathematics**, not
an additional theorem among the 23 audited kernel roots. Its first
target is obtained directly, without importing a sufficient-set
occurrence theorem. Consequently, first occurrence in this class
cannot produce a strict contradiction by the zero/one-even inverse
test under the very leastness hypotheses needed for that contradiction.
Later visits and longer inverse words remain separate possibilities.

## 6. Explicit convergent witnesses and independent checks

At h=0, source 39 first reaches the target class at 101, at ordinary
clock 9. Its smallest one-even predecessor is 39. At h=1, source
2,559 first reaches it at 73,811, at clock 21, and its smallest
one-even predecessor is 2,559. The second target exceeds twenty
times the source.

The axiom-free kernel example checks both endpoints and every earlier
residue. It separately proves arrivals at one from 39, 101, 2,559
and 73,811 at clocks 34, 25, 115 and 94. Python independently checks
the trajectories and first-arrival minimality. No convergence claim
for every member of the parameterized family is made.

The [verifier](../verify_minimum_first_target.py) checks the half-source
identity over a complete parameter rectangle, traverses all family
prefixes for h=0 through 256, and enumerates their complete inverse
words with at most one even input. It also traces every source from
1 through 65,536 until its first target-class visit, arrival at one,
or the explicit ordinary-clock cutoff. It records whether the best
one-even predecessor at that first target is below, equal to, or
above the starting source. Unfinished paths are retained as such.

In the completed census, 60,949 sources have a strictly smaller
predecessor at their first target, 4,551 recover the original source,
and 36 reach one before any target. There are zero above-source
outcomes and zero unfinished paths at the cutoff. All 4,551 equality
cases satisfy (8), and every source satisfying (8) has the exact
clock, endpoint and minimum in (9). This equivalence was checked for
all 65,536 sources; its converse outside this finite interval is not
claimed as a theorem.

These are finite-path and bounded-word checks. A finite prefix minimum
is never substituted for an unknown global minimum; no least
counterexample is instantiated numerically.

Run python3 verify_minimum_first_target.py. The
[manifest](../results/minimum-first-target/verification.json) and
[replay](../results/minimum-first-target/replay.json) separate 27 fresh
sequential Lean builds, 23 new roots, exact finite evidence, written
assemblies, and external context.

The final full run completed at 2026-10-14T22:17:16.827471Z using
Lean 4.33.1, with 14.570 seconds of sequential build time and 58
file hashes. It authenticated all 58 entries in the preceding mixed
ancestry manifest. The half-source rectangle contains 4,160 pairs
and 561,600 ordinary steps. The 257 family prefixes use 397,065
ordinary steps and enumerate 199,175 inverse candidates. The complete
first-hit census uses 670,655 ordinary steps, 5,204 distinct targets
and 36,257 inverse candidates. Four explicit convergence witnesses
are independently replayed over 268 steps. No native finite axiom is
used by the new roots.

The remaining ancestry task needs more than first occurrence: for
example, an estimate forcing a useful predecessor below A at a later
actual visit, or control of longer inverse words along the orbit.
The near-source restriction (3) gives necessary arithmetic when a
return is available. It supplies neither such a return theorem nor
a universal cap bound, cycle exclusion, or full Collatz proof.
