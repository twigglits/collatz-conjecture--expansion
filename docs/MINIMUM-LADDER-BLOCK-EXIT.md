# A useful first return after a variable post-ladder block

There are arbitrarily large return-ladder sources whose **first visit to
20 modulo 27 after the growing prefix** has a smaller predecessor using
only five even inverse operations. The delay from the end of the prefix
to that first later visit is exactly 2k+8, and k can be arbitrarily large.

These are parameterized kernel proofs under an explicit arithmetic
condition. A separate new path excludes every exponent R=3 modulo 16
by joining the preceding ladder source. Together with earlier results,
a possible least counterexample of the form N=8^R-5, R>=3, must have
R=1 modulo 4 and satisfy the failed-exit condition below. An infinite
progression satisfies those necessary conditions, so the argument does
not settle this family or the positive-integer Collatz conjecture.

The [Lean module](../lean/MinimumLadderBlockExit.lean) has 25 audited
kernel roots, including one axiom-free period certificate. All paths,
first-return statements, lift constructions, and least-counterexample
restrictions are kernel proved. No native reduction axiom or external
mathematical premise enters the chain.

## The variable-length meeting

Let R>=3 be odd, N=8^R-5, and X=9^R. The earlier
[ladder theorem](MINIMUM-RETURN-LADDER.md) gives

    C^(5R)(N)=X-5,       prefix minimum through 5R = N.

Five more ordinary steps reach

    d=(3X-11)/16.

Write

    3X+5 = 2^(k+4)*q,       q>0 and q odd,
    d = 2^k*q-1.                                          (1)

The new sufficient condition is

    3^k*q = 3 mod4.                                       (2)

The first k shortcut operations from d are odd. Their endpoint
z=3^k*q-1 is 2 modulo 4 under (2), so one even operation followed
by an odd operation reaches b=(3^(k+1)*q-1)/4.

The kernel proves that P=2^(2R+1)-1 is positive, smaller than N, and

    C^(4R+2k+9)(P) = C^(5R+2k+8)(N) = b,
    Backtrack(5,2R+k+2,b,P).                              (3)

The inverse word is

    E E O^k E E O E O^(2R+1).

Here O is a shortcut odd inverse and E is an even inverse. There is
no fixed bound on the odd count. The earlier cubic size identity
(P+1)^3=8*(N+5)^2 still applies.

This reuses the project's
[half-source meeting theorem](MINIMUM-FIRST-TARGET.md). The initial
five-step bridge takes X-5 to d, while five steps from 3X-1 reach
3d+2. The paired odd blocks from d and 3d+2 then meet after the
specified even exit. The preceding
[R=7 mod8 and R=1 mod16 paths](MINIMUM-LADDER-EXIT.md) are the k=0
and k=1 cases of this construction, respectively.

## The first later residue-20 visit

For k>=2, the meeting value in (3) is 20 modulo 27, because
4b+1=3^(k+1)*q is divisible by 27. The kernel proves the stronger
clock statement

    C^(5R+2k+8)(N)=20 mod27,
    C^t(N)!=20 mod27 for every 5R<=t<5R+2k+8.             (4)

The five-step bridge has residues 22,11,19,4,2,1 modulo 27.
During the odd block, shortcut endpoints stay in {1,2,17,26};
the intervening ordinary odd steps also avoid 20. The final three
ordinary steps are checked separately. This proves (4) for every
block length, rather than checking a finite range of k.

Thus the first later residue-20 target is useful for these sources,
with only five even inverse operations. The first later return can
be arbitrarily delayed. This does not assert that (3) is the earliest
coalescence by any method, or that no forward descent occurs before it.

## A kernel construction for every block length

The construction first proves a general binary lifting statement:
if A is odd and A+C is divisible by eight, then for every j there
is r<2^j with

    2^(j+3) divides A*9^r+C.

The preceding exact top-bit identity for 9^(2^j) shows that adding
2^j to r flips the next bit while preserving the lower bits. This
is an algebraic induction, not a numerical extrapolation.

Apply it with the suitable offset for

    3*9^r+5 = 2^(k+4)*epsilon mod 2^(k+6),
    epsilon = 3 if k is even, and 1 if k is odd.

It yields a seed r<2^(k+3) satisfying (1)--(2). Adding a multiple
of 2^(k+3) to r preserves the condition. The kernel constructs
arbitrarily large odd R>=3 in this way, for every k>=0.

The first seeds from the independent modular calculation are:

| k | Seed r | Exponent period |
|---:|---:|---:|
| 0 | 7 | 8 |
| 1 | 1 | 16 |
| 2 | 13 | 32 |
| 3 | 53 | 64 |
| 4 | 37 | 128 |
| 5 | 69 | 256 |
| 6 | 261 | 512 |

The R>=3 hypothesis remains necessary; the seed R=1 does not give
a smaller source. For every k>=2 and source bound B, a new kernel
existential theorem supplies N>B with the first useful later visit
in (4). These sources are not asserted to belong to every earlier
ternary whole-window obstruction progression. No such general
intersection theorem is included here.

## A path to the preceding ladder

For R>=3 and R=3 modulo 16, the kernel proves

    P=8^(R-1)-5 > 0,
    N=8P+35,
    C^(5R+5)(P)=C^(5R+8)(N).                             (5)

The short affine identity behind (5) is

    C^8(1152u+724)=C^10(128u+76)=27u+17.

The lower exponent R-1 is even; the earlier growing-block endpoint
identity applies to even exponents as well. Equation (5) is a
strictly smaller coalescing source, but it does not give an induction
proving convergence for every exponent.

Combining (5) with the earlier R=7 mod8 and R=11 mod16 paths excludes
every R=3 modulo 4 as a least-counterexample exponent. Even R is
already excluded by the basic least-source residue restriction.

## What the criterion still leaves open

The kernel now proves that if N=8^R-5 with R>=3 were a least
counterexample, then R=1 modulo 4 and there would be k,q satisfying

    k>0, q>0, q odd,
    3*9^R+5=2^(k+4)*q,
    3^k*q=1 mod4.                                       (6)

Thus the corresponding odd block ends at a multiple of four,
rather than the 2mod4 exit used in (2).

These necessary conditions are compatible with an unbounded exponent
progression. For every h>=0, R=512h+5 has

    3*9^R+5=2^10*q,       q=1 mod4,

so k=6 and (6) holds. This is a kernel arithmetic statement about
compatibility, not evidence of a counterexample or of failure of every
other method. The first member R=5 is already kernel checked to
converge in the earlier ladder module.

Further work must handle these longer even exits or a different
coalescing source. Universal convergence of the covered families,
a useful later target on every possible least-counterexample orbit,
the cap/residual bounds, and the full Collatz conjecture remain open.

## Verification

Run

    python3 verify_minimum_ladder_block_exit.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_ladder_block_exit.py) authenticates the
71 preceding ladder-exit hashes, builds 34 Lean modules afresh in
dependency order with 16 threads per process, and audits all 25 roots.

Independent checks separate generic affine paths, complete positive
coalescing paths, the first later residue-20 visits, exact small lifting
examples, larger coordinate-only paths, and modular-only families.
The [manifest](../results/minimum-ladder-block-exit/verification.json)
and [replay](../results/minimum-ladder-block-exit/replay.json) record
their ranges and counts. Finite evidence is not substituted for the
parameterized kernel statements.

