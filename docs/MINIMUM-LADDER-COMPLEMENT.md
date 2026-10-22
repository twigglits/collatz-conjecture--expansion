# A complementary ladder exit and the remaining exponent class

The previously surviving progression R=512h+5 now has a positive,
strictly smaller coalescing source. More generally, a second construction
handles every failed post-ladder exit with block length k>=2. Combined
with the earlier exclusions, a possible least counterexample of the form
N=8^R-5, R>=3, must have **R=9 modulo 16**.

For k>=3, both exit cases now have a useful **first residue-20 visit
after the growing prefix**. The new predecessor uses R+4 even inverse
operations. Its cost grows with R; the previous construction uses five.
Neither this result nor the necessary exponent restriction proves
convergence of the whole family or the positive-integer Collatz conjecture.

The [Lean module](../lean/MinimumLadderComplement.lean) has 21 audited
kernel roots. The finite residue-injection certificate is axiom-free;
the other roots use only standard logical axioms. No native computation
or external mathematical premise enters the unconditional results.
The final merger criterion below is explicitly conditional.

## A weighted ladder gives the second source

Write X=9^R. The existing growing prefix sends N to X-5 at ordinary
clock 5R and has prefix minimum N. The new weighted identity, restricted
here to positive paths, is

    C^(5r)(8^r*q-5) = 9^r*q-5,       q>=6,
    Backtrack(r,2r,9^r*q-5,8^r*q-5).

This follows by repeating the shortcut word OOE. Its one-block form is
8q-5 -> 9q-5. Here O includes an odd ordinary operation and its forced
halving; E is one ordinary halving.

Choose

    P = 6*8^(R-1)-5.

For R>=3, the kernel proves

    0<P<N,                  4(P+5)=3(N+5).

The weighted prefix takes P to 6*9^(R-1)-5 at clock 5(R-1). For odd R,
one can write X=48u+9 and 6*9^(R-1)=32u+6. The two endpoints are
therefore 48u+4 and 32u+1. Their short bridges give

    C^5(48u+4)=9u+1,
    C^8(32u+1)=27u+2.

The [preceding factorization](MINIMUM-LADDER-BLOCK-EXIT.md) is

    3X+5 = 2^(k+4)*q,       q>0, q odd,
    2^k*q = 9u+2.

The first bridge ends at d=2^k*q-1. The second ends at 3d-1.
When k>=2, two halvings of the latter give

    2^(k-2)*(3q)-1.

Its k-2 odd shortcut operations end at 3^(k-1)*q-1. Under the
complementary condition

    3^k*q = 1 mod4,                                      (1)

this endpoint is 2 modulo 4. One even and one odd shortcut operation
reach the same value as two halvings after N's k-operation odd block.

## The exact meeting and first later target

For odd R>=3, k>=2 and condition (1), the kernel proves

    b=(3^k*q-1)/4,
    C^(5R+2k+4)(P) = C^(5R+2k+7)(N) = b,
    Backtrack(R+4,2R+k,b,P).                            (2)

The forward shortcut words are

    N: (OOE)^R      EEOE O^k EE,
    P: (OOE)^(R-1) OEOEO EE O^(k-2) EO.

Their ordinary clocks and inverse counts agree with (2). No optimal
inverse cost or earliest coalescence claim is made.

When k>=3, 4b+1=3^k*q is divisible by 27, so b is 20 modulo 27.
The earlier bridge and odd-block avoidance lemmas exclude every
ordinary clock from 5R through the odd-block endpoint. The two final
halvings have residues 26,13,20. Consequently

    C^(5R+2k+7)(N)=20 mod27,
    C^t(N)!=20 mod27 for 5R<=t<5R+2k+7.                 (3)

Together with the earlier successful-exit theorem, every odd
factorization with k>=3 has a smaller source joining its first later
residue-20 target. Its delay after clock 5R is 2k+7 under (1), and
2k+8 under the other exit condition. The two source constructions have
different sizes and inverse costs.

For the whole progression R=512h+5, the earlier arithmetic certificate
gives k=6 and condition (1). Thus (2)--(3) apply to every h>=0, with
clocks 5R+16 for P and 5R+19 for N. This resolves that progression
as possible least counterexamples; it does not prove that every member
converges.

## Arbitrarily long complementary blocks

The kernel also proves that adding 2^(k+2) to an exponent with the
previous successful exit flips it to condition (1). The exact top-bit
identity gives

    9^(2^(k+2)) = 1 + 2^(k+5)*a,       a odd.

If the old quotient is q, the new quotient is

    Q = q + 2*(3*9^R*a).

It stays positive and odd, while 3^k*Q changes from 3 to 1 modulo 4.
Applying this to the earlier unbounded lifts constructs arbitrarily
large complementary exponents for every k. For every k>=3 and source
bound, the kernel supplies a larger source satisfying (2)--(3).

The first small modular seeds for k=2..8 are 29,21,101,197,5,901,1157,
with exponent period 2^(k+3). These finite seed values are independent
checks. The general existence and unboundedness statements are kernel
proofs. No universal uniqueness theorem is claimed.

## What remains

The earlier least-source restriction required R=1 modulo 4, k>0,
and condition (1). The new path excludes k>=2, leaving k=1. Then
q=3 modulo 4 and 3X+5=32q force X=73 modulo 128. The kernel checks
the sixteen exponent residues and derives

    N least, R>=3  ==>  R=9 mod16,
    3*9^R+5=32q,       q>0, q=3 mod4.                  (4)

Thus seven of the eight odd exponent classes modulo 16 are excluded
as least counterexamples. This is a restriction on this parameterized
family, not a density claim about arbitrary positive integers.

The remaining progression R=16h+9 satisfies (4) arithmetically. This
is compatibility with the post-ladder condition; it does not establish
compatibility with every other restriction in the project. Its R=9
member reaches 1 in 309 ordinary steps in the independent Python replay.
That finite convergence check is not a new Lean convergence certificate.

For every remaining exponent, the kernel obtains the precise pair

    b=(9*9^R-17)/128,       b=14 mod27,
    C^(5R+9)(N)=b,
    C^(5R+4)(P)=4b-1.                                  (5)

A later merger of these two endpoints would exclude N as a least
counterexample. The theorem `remaining_merge_suffices` proves this
implication with the merger as a hypothesis. A merger for every
remaining exponent has **not** been proved. Neither the finite path
search nor the R=9 convergence example supplies that missing theorem.

The useful-return question for arbitrary least-counterexample orbits,
universal family convergence, the cap/residual bounds, nontrivial cycles,
and divergence remain unresolved. No general intersection theorem with
every earlier ternary whole-window progression is added here.

## Verification

Run

    python3 verify_minimum_ladder_complement.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_ladder_complement.py) authenticates the
73 preceding manifest hashes and builds 35 modules afresh in dependency
order, using 16 threads per process. It audits all 21 new theorem roots.

Independent checks distinguish generic weighted ladders and affine
paths, complete positive paths, exact first later residue-20 visits,
half-period flips, modular-only lifts, larger coordinate-only tails,
and the two different remaining endpoints in (5). Their ranges and
counts are recorded in the [manifest](../results/minimum-ladder-complement/verification.json)
and [replay](../results/minimum-ladder-complement/replay.json).
