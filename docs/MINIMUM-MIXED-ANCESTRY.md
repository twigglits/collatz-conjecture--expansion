# Mixed predecessors beyond the all-odd height barrier

**One even-input shortcut step changes the previous ancestry test.**
There are arbitrarily large sources with a finite path to a target far
above the all-odd height threshold, although every all-odd predecessor
of that target is larger than the source. The improvement factor is
unbounded. The new construction is a kernel theorem about actual paths.

It does not prove that a hypothetical least counterexample encounters
one of these targets. That occurrence problem remains the missing step.
**Collatz remains unresolved.** No novelty claim or new external proof
premise is made.

The [Lean module](../lean/MinimumMixedAncestry.lean) has 30 audited roots.
The two numerical examples use axiom-free kernel computation; general
statements use only standard logical axioms and local dependencies.

## 1. The exact condition for a mixed inverse word

For a positive odd-state valuation word w, let l be its length, s its
sum, and B_w its affine numerator. The earlier
[inversion audit](MARKED-PREIMAGE-AUDIT.md) proves that, for an odd
target b, a natural-number solution p of

    2^s b = 3^l p + B_w

is an actual positive odd predecessor, with ordinary clock l+s.
The new kernel module combines this with leastness throughout a
coalescence component. If A is a least positive counterexample and
b=C^t(A), then

    p >= A,    2^s b >= 3^l A + B_w.                 (1)

The same module gives the global-minimum splice

    m(p) = min(m_(l+s)(p), m(b)).                   (2)

Here the first minimum on the right is finite and the second is global.
Admissibility, the additive numerator, and the actual meeting point
are all retained. A formal inverse expression without those conditions
is insufficient.

For context, the primary
[Monks et al. sufficient-set paper, Section 4](https://arxiv.org/html/1204.3904v2)
proves backward reachability into prescribed arithmetic progressions
and bounds the number of odd inverse operations. Such congruence
reachability does not assert that the resulting predecessor lies below
a given least source. We use this distinction only for research
direction; no theorem from that paper is imported here.

## 2. Two growing blocks separated by one extra halving

Write U(n)=(3n+1)/2 for odd n and n/2 for even n. An **even-input
shortcut step** means the latter operation. The mandatory halving
after each odd ordinary step is already included in U and is not
counted as an extra even-input step.

Suppose k>=2, j>=0, q,v>0 and

    3^k q + 1 = 2^(j+1) v.                         (3)

Put p=2^k q-1 and b=3^j v-1. The actual path consists of k odd
shortcut steps, one even shortcut step, and j odd shortcut steps:

    p -> 3^k q-1 = 2(2^j v-1) -> 2^j v-1 -> b.

The kernel proves

    C^(2k+1+2j)(p) = b,
    m_(2k+1+2j)(p) = p,
    U^(k+1+j)(p) = b,    wt_(k+1+j)(p) = k+j.       (4)

Thus exactly one of those shortcut inputs is even. The middle state
is at least p because 2*2^k<=3^k for k>=2. Combining (2) and (4),

    m(p)=min(p,m(b)),    m(b)=b => m(p)=p.          (5)

For a least counterexample A whose orbit reaches b, the new necessary
restriction is

    A+1 <= 2^k q.                                  (6)

This applies also when b is even; the actual ordinary path in (4)
does not require b to be an odd endpoint of an accelerated valuation
word. No unknown global minimum is evaluated by the construction.

At k=2,j=0, the target 9r+4 has predecessor 8r+3 at ordinary
clock five. The latter is strictly smaller. The module consequently
also proves that a least counterexample cannot be 4 modulo 9.

## 3. An infinite family that defeats the previous threshold

Construct integers a_j<2^j by binary lifting so that

    15*9^a_j + 1 = 0 mod 2^(j+3).

Start with a_0=0. At each stage retain a_j if the next quotient bit
is even, and otherwise add 2^j. The earlier kernel identity

    9^(2^j) = 1 + 2^(j+3)*(an odd integer)

proves that this toggles precisely the required bit. Define

    K_j = 2(a_j+2^j)+1,
    v_j = (5*3^K_j+1)/2^(j+3),
    p_j = 5*2^K_j-1,
    b_j = 3^(j+2)*v_j-1,
    T_j = 2K_j+1+2(j+2).

The kernel proves v_j>0 and integrality, and

    2^(j+1)+1 <= K_j < 2^(j+2)+1,
    C^T_j(p_j)=b_j,    m_T_j(p_j)=p_j,
    p_j+2 < 2^(K_j+3),    j < p_j.                 (7)

The all-odd threshold for the floor p_j+2 can therefore be taken as
3^(K_j+3), by the [preceding height theorem](MINIMUM-ROOT-PREDECESSORS.md).
The exact target scale is

    2^(j+3)(b_j+1) = 3^(j+2)(5*3^K_j+1).          (8)

Consequently the ratio (b_j+1)/3^(K_j+3) is at least
(5/24)(3/2)^j. Equation (8) and the denominator-cleared comparison
are kernel statements; writing the comparison as a ratio is elementary
arithmetic. A convenient entirely integer consequence is

    10h <= j => h*3^(K_j+3) <= b_j+1.              (9)

The proof uses the kernel inequality (j+2)2^j<=2*3^j.

For j>=10, **every** all-odd predecessor 2^s q-1 of b_j satisfies

    2^s q-1 >= p_j+2,                              (10)

whereas the one-even predecessor is p_j itself. The final existential
kernel theorem makes both quantifiers explicit: given any factor h
and source bound B, there are n>B, b, d, t with

    n+2 < 2^d,    C^t(n)=b,    m_t(n)=n,
    (h+1)*3^d <= b+1,

and every all-odd predecessor of b is at least n+2. It chooses
j=10(h+B+1). This is an unbounded improvement over the earlier
inverse family, not a divergent orbit. The source changes with j.

Every p_j is divisible by three: K_j is odd, so 5*2^K_j-1 is
zero modulo three. This last observation is written here. By the
existing [inverse-basin analysis](../lean/InverseBasinAudit.lean), each such
source has only a doubling ray of predecessors and hence a basin
of natural density zero. The construction therefore does not itself
supply the missing positive branch-density increment.

## 4. Two numerical examples, both separately proved to converge

At j=0, the family has p=39, b=152 and T=11. In shortcut form,

    39 -> 59 -> 89 -> 134 -> 67 -> 101 -> 152.

Only the input 134 is even. The minimum over the corresponding
ordinary prefix is 39. Kernel computation proves arrivals at one
from 39 and 152 at clocks 34 and 23 respectively.

The j=4 example already exceeds the all-odd threshold, even though
the convenient general cutoff in (10) is ten:

    p = 45,035,996,273,704,959,
    b = 551,968,206,708,544,316,592,375,437,
    K = 53,    T = 119,    p+2 < 2^56,    3^56 <= b+1.

The kernel checks the endpoint, the prefix minimum, and both height
inequalities. The preceding general all-odd barrier then says every
all-odd predecessor of b is at least p+2. The same axiom-free theorem
proves that p and b reach one at clocks 751 and 632. Independent
Python replay additionally checks that all four arrivals are first
arrivals. None of these finite minima is a nontrivial global root.

## 5. Exact optimization over the one-even family

For a fixed positive target b, all-odd inverses have lengths
0<=j<=v_3(b+1). Fix one such j and set v=(b+1)/3^j. Inserting an
inverse even step gives the integer 2^(j+1)v-2. Its possible preceding
odd-block lengths are

    0<=k<=v_3(2^(j+1)v-1).

For each fixed j, the smallest source uses the largest allowed k,
because its value plus one is multiplied by 2/3 whenever k increases.
The minimum over these candidates and the all-odd candidates is the
smallest predecessor using at most one even-input shortcut step.
This finite optimization and its completeness are written arguments;
the individual valid block identities and parity counts are kernel.

In fact only the last all-odd inverse point can improve the minimum.
Set s=v_3(b+1) and c=2^s(b+1)/3^s-1. Before reaching c, each
all-odd inverse point is 2 modulo 3; doubling it cannot have an odd
inverse parent, as a kernel lemma checks. At c, write

    2c+1 = 3^k q,    3 does not divide q.

The kernel proves both

    2^k q-1 < c iff k>=2,    k>=2 iff c=4 mod 9.

Together with the preceding finite optimization, these give the exact
**written** criterion: the one-even minimum improves on the all-odd
minimum if and only if c is 4 modulo 9. The kernel verifies the
constituent arithmetic; it does not define the minimum over the full
inverse-word set or formalize this assembly.

The improved targets have natural density **1/6**, by a written
counting argument. For each s>=0 they occupy one residue class
modulo 9*3^s, determined by

    b+1=3^s q,    q=5*2^(-s) mod 9.

These classes are disjoint because their ternary valuations differ.
The tail with s>=S is contained in 3^S dividing b+1, so its upper
density is at most 3^(-S). Thus the full density is the convergent
sum of 1/(9*3^s), which equals 1/6. This is a statement about target
integers, not their frequency along an individual Collatz orbit.

The verifier evaluates this inverse optimization for every b from
1 through 65,536. Independently, it traverses the forward orbit of
every possible minimizing source p<=65,536, stopping before its second
even-input shortcut step, and records every in-range endpoint. The
two arrays of minima agree exactly, both for zero and for at most one
even step. The residue criterion and its progression counts also agree.
Sources above the cutoff cannot minimize a target below
the cutoff, since that target is its own zero-length predecessor.

Every strict improvement is also replayed as an ordinary path and
as a shortcut path with its exact parity word. These are exhaustive
finite predecessor minima in the stated word class, not global
orbit minima, density estimates, or a complete convergence interval.

## 6. The remaining height and occurrence problems

The improvement does not give arbitrarily high targets from a fixed
small source using a bounded number of even inputs. Here is an
elementary **written** bound, not a new kernel theorem.

If n+1<=2^d with d>=1, any initial all-odd block has endpoint y with
y+1<=3^d. Indeed, writing n+1=2^k q gives k<=d and
3^k q<=3^k 2^(d-k)<=3^d. After the next even-input shortcut step,
the new value z satisfies

    z+1 <= (3^d+1)/2 <= 2^(2d-1).

Iterating this estimate, every shortcut endpoint reached with at
most r even-input steps satisfies

    endpoint+1 <= 3^[2^r(d-1)+1].                  (11)

For a fixed source bound and fixed r, this is a finite height ceiling.
For intermediate ordinary odd peaks, twice that bound suffices.
The family in Section 3 is compatible with (11): it uses different,
rapidly increasing sources, and improves the smaller all-odd ceiling.

More fundamentally, (6) excludes a least-counterexample orbit only
if it actually visits an admissible target with 2^k q<A+1. The new
family establishes that such efficient predecessors exist at large
heights; it does not force an unknown exceptional orbit to meet them.
Congruence reachability alone, finite frequencies, and the density of
unrelated target families do not provide that missing occurrence or
height comparison. Even the sufficient-set paper's guarantee that
every nontrivial cycle or divergent orbit meets 20 modulo 27, a
subset of the improved targets, supplies no bound making the new
predecessor smaller than the original least source. This is an
external comparison of scope, not a premise of the kernel results.
A useful next step must control this along the
actual orbit, or supply a separate cap or residual estimate. Nontrivial
cycles and divergence both remain open.

## 7. Reproduction and evidence

Run python3 verify_minimum_mixed_ancestry.py using the
[verifier](../verify_minimum_mixed_ancestry.py). It authenticates the
three prerequisite manifests, freshly builds all 26 local Lean modules
sequentially, audits every new theorem root, and runs the independent
forward/inverse census and lifting checks.

Complete small exponent periods are checked separately from large-index
modular lifting. Exact source paths are traversed only for lift indices
0 through 10. Modular tests through index 128 do not construct those
astronomically large sources. The
[manifest](../results/minimum-mixed-ancestry/verification.json) and
[replay](../results/minimum-mixed-ancestry/replay.json) record exact
counts, source hashes, compiler version, and scope distinctions.

The completed run at 2026-10-14T21:57:16.224949Z passed all 30 roots
in 26 fresh sequential builds taking 12.980 seconds, with 58 hashes.
It authenticated 50, 28 and 14 entries in the three prerequisite
manifests, with possible overlap. There is no native computation axiom.

The census examined 98,298 inverse branches for 65,536 targets and
196,606 forward shortcut steps for all 65,536 candidate sources.
The 131,072 minimum comparisons agree, as do 65,536 residue-criterion
checks and 17 progression counts. There are 10,922 strict improvements,
independently replayed over 76,434 ordinary steps. The lift checks
cover 129 modular indices and all 8,191 exponent residues in 13 small
periods. Eleven exact family prefixes use 12,767 ordinary steps;
seven already exceed the all-odd height threshold. Separate large-
index arithmetic is not a source census. All four kernel arrival
witnesses were independently replayed over 1,440 ordinary steps.
