# Three smaller sources exclude every pure ladder as a least counterexample

For **every positive R**, the number 8^R-5 cannot be the least positive
Collatz counterexample. The new kernel proof closes the previously
remaining R=9 modulo 16 class with a three-source construction. It also
works for arbitrary positive weights q satisfying the residue condition
below.

This is a universal least-counterexample exclusion for the family.
It does **not** prove that every member converges. An arbitrary least
counterexample has not been forced into this family or the covered
weighted classes, and the positive-integer Collatz conjecture remains
unresolved.

The [Lean module](../lean/MinimumLadderCover.lean) has 17 audited kernel
roots. The two small convergence certificates are axiom-free; the other
roots use only standard logical axioms. No native reduction axiom,
unproved merger hypothesis, or external mathematical premise enters
the exclusion.

## The three-source construction

Let R>=3 and q>0, and write

    N=8^R*q-5,       X=9^R*q.

Assume the explicit condition

    X=73 mod128.                                          (1)

The weighted growing prefix reaches X-5 at ordinary clock 5R. Nine
more operations reach

    b=(9X-17)/128,       b=14 mod27.

The new construction uses three sources:

    M=2^(2R-1)*q-1,
    P=8^(R-1)*q-5,
    D=2*8^(R-2)*q-5.

The kernel proves that all three are positive and strictly smaller
than N. Their sizes also satisfy

    N+5 = 8(P+5) = 32(D+5).

They reach three different partners of b:

| Source | Ordinary clock | Endpoint |
|---|---:|---|
| N | 5R+9 | b |
| M | 4R+7 | 2b+1 |
| P | 5R+6 | b-1 |
| D | 5R+2 | a=(b-5)/9 |

Here a is a nonnegative integer and b=9a+5. In this weighted family
all source and endpoint coordinates used in the paths are positive.

The identities follow from four affine bridges:

    C^9(384u+196)=27u+14,
    C^9(128u+66)=54u+29,
    C^11(128u+60)=81u+40,
    C^12(256u+237)=81u+76.

Condition (1) gives the required coordinates for X/3, X/9 and X/81.
Their denominators divide X because R>=3. The prefixes are the existing
all-odd Mersenne path and the weighted OOE ladder path, both kernel
proved for arbitrary positive weights.

## Why one partner always joins b

The scalar cover is universal: for every b=9a+5, at least one of
2b+1, b-1 and a coalesces with b. All clocks here count ordinary
operations.

| Case | Partner | Partner clock | Clock from b |
|---|---|---:|---:|
| b=2 mod4 | 2b+1 | 3 | 2 |
| b=0 mod4 | a | 4 | 2 |
| b odd, 3^k*v=3 mod4 | 2b+1 | 2k+4 | 2k+3 |
| b odd, 3^k*v=1 mod4 | b-1 | 2k+2 | 2k+2 |

In the last two rows, write b+1=2^k*v with v positive and odd.
Such a factorization always exists, and k>=1 because b is odd.
The product 3^k*v is odd, so the two exit residues exhaust the cases.

For b=2 mod4, the first row is a three-step affine identity. If b=0
mod4, then a=3 mod4 and two odd shortcut operations from a agree with
two halvings from b=9a+5.

For the odd successful exit, the existing half-source meeting theorem
joins 2^k*v-1 and 2^(k+1)*v-1. These are b and 2b+1. For the other
exit, b-1=2*(2^(k-1)*v-1). Its first halving exposes a shorter odd
block, and the same theorem gives equal iterates after 2k+2 ordinary
operations. The proof applies to every k; it has no bounded block-length
assumption or numerical extrapolation.

Combining the scalar cover with the source identities gives a kernel
existence theorem for a positive Q<N, chosen from {M,P,D}, that
coalesces with N. Consequently every weighted source satisfying (1)
is excluded as a least counterexample.

## Closing the pure ladder family

The [preceding result](MINIMUM-LADDER-COMPLEMENT.md) already proves
that if 8^R-5 were least, with R>=3, then R=9 modulo 16. That exponent
condition forces 9^R=73 modulo 128, so the new weighted theorem applies
with q=1 and gives a contradiction.

The two smaller exponents are handled directly:

    C^7(3)=1,       C^32(59)=1.

These computations are checked by Lean's kernel. The final theorem is

    R>0  ==>  not LeastCounterexample(8^R-5).              (2)

The older conditional merger between b and 4b-1 remains unproved as
a universal statement. The new cover uses three different partners
and establishes (2) without that hypothesis.

The smaller sources need not belong to the pure ladder family.
Convergence of all those sources has not been established, so (2)
cannot be turned into convergence of every 8^R-5 by induction on R.
The distinction between least-source exclusion and convergence is
essential here.

## Scope of verification and next gap

Run

    python3 verify_minimum_ladder_cover.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_ladder_cover.py) authenticates all 76
preceding manifest hashes and builds 36 Lean modules afresh in dependency
order, using 16 threads per process. It audits all 17 new theorem roots.

Independent checks exercise all four scalar branches, the three bridges,
complete weighted and pure-ladder paths, secondary odd blocks through
length 128 and additional lengths 512, 1024 and 4096, and the two small
convergence cases. Larger coordinate-only checks replay short tails;
modular-only examples do not materialize their enormous sources. The
[manifest](../results/minimum-ladder-cover/verification.json) and
[replay](../results/minimum-ladder-cover/replay.json) record these scopes
separately.

The next gap is extending the construction beyond condition (1) and
the pure coefficient q=1, while controlling the cases with shorter
initial growing blocks. No theorem places every possible least
counterexample in the classes proved here. Universal convergence,
the cap/residual estimates, nontrivial cycles and divergence remain open.
