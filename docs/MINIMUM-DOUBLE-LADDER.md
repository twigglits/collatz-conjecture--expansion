# A variable-length exit excludes further doubled ladders as least sources

The new kernel proof excludes additional members of the family

    N = 2*8^R-5

as least positive Collatz counterexamples. Every odd R is excluded by
the smaller-predecessor restriction modulo 3. For even R, write

    R=2^k*s,       k>0,       s>0 odd.

The new sufficient condition is

    3^k*s = 1 mod4.                                      (1)

Under (1), the smaller positive source P=8^R-5 coalesces with N at
the exact ordinary clocks

    C^(5R+2k+7)(P) = C^(5R+2k+8)(N).                    (2)

The proof holds for every k, with no bound on the secondary odd block.
It does not prove convergence of either source. The opposite exit
3^k*s=3 modulo 4 remains unresolved by this construction; so do the
full doubled family, the remaining quadrupled family, and the
positive-integer Collatz conjecture.

The [Lean module](../lean/MinimumDoubleLadder.lean) has twelve audited
kernel roots. They use only standard logical axioms. There is no
native reduction, added mathematical premise, or unproved merger
hypothesis in these exclusions.

## Exact exponent arithmetic

For every natural k and s, Lean proves that there is a natural u with

    9^(2^k*s) = 1 + 2^(k+3)*u,       u=s mod4.           (3)

The unit u is positive when s>0, and odd when s is odd. Thus, for
positive odd s, the exact power of two dividing 9^(2^k*s)-1 is
2^(k+3). The proof includes the residue of the odd quotient modulo 4,
which determines the exit in (1).

At k=0 the quotient in 9^s=1+8u satisfies u=s modulo 4 by induction
on s. Doubling the exponent replaces u by

    u + 2^(k+2)*u^2.

The added term is divisible by 4. Induction on k therefore preserves
the quotient residue. This proves (3) without an external valuation
theorem or a finite check of exponents.

## The weighted meeting

The construction is stronger than the pure coefficient case. Let
R,w,k,u be positive naturals, and assume

    X=9^R*w = 1 + 2^(k+3)*u,       3^k*u=1 mod4.        (4)

Set

    N=2*8^R*w-5,       P=8^R*w-5,
    a=2^k*u,          b=9a-1.

Then 0<P<N and N+5=2(P+5). The two weighted growing prefixes have
ordinary length 5R, reaching 2X-5 and X-5. Since k>0, a is even.
Two affine bridges give

    C^(5R+6)(N) = b,
    C^(5R+5)(P) = b-1.

The bridges are kernel identities for every natural v:

    C^6(32v+29)=18v+17,
    C^5(16v+12)=18v+16.

Here a=2v+2. The secondary odd block of b has length k because
b+1=2^k*(9u), with u odd under (4). Its exit is
3^k*(9u)=1 modulo 4. The previously proved adjacent-block meeting
therefore gives

    C^(2k+2)(b-1)=C^(2k+2)(b).

Adding the prefix clocks proves (2), now for the weighted N and P.
Both local paths meet at (9*3^k*u-1)/4. The complete shortcut words
are

    N: (OOE)^R OEEO O^k EE,
    P: (OOE)^R EE O^(k+1) EO.

An O is an odd operation followed by its forced halving, and an E
is one halving. The ordinary clocks count an O twice. The verifier
checks these complete words forwards and backwards independently.
No earliest-meeting or optimal-cost claim is made.

## What a remaining least source would require

Applying (3) with w=1 turns (4) into condition (1). Separately, for
odd R the source N is 2 modulo 3, contradicting the established
least-source restriction. Hence Lean proves the necessary condition

    LeastCounterexample(2*8^R-5), R>0
      ==> R=2^k*s, k>0, s>0 odd, 3^k*s=3 mod4.          (5)

In elementary residue terms, the remaining cases in (5) are
k odd with s=1 modulo 4, or k even with s=3 modulo 4. These are
conditions left open by the construction, not counterexamples.

Examples of exponents excluded by (1) are R=4 and R=6. The exclusions
also include R=2^k for every positive even k, and R=3*2^k for every
positive odd k. Thus the secondary block lengths in the proved
family are unbounded.

The [earlier pure-ladder theorem](MINIMUM-LADDER-COVER.md) already
excludes every 8^R-5 as least. Its statement alone does not prove
that P converges. In the present contradiction argument, convergence
of P follows from the hypothetical minimality of N and P<N.

## Reproduction and evidence limits

Run

    python3 verify_minimum_double_ladder.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_double_ladder.py) authenticates the
preceding manifest and builds all 37 modules in dependency order,
with 16 threads per process. It audits all twelve new theorem roots.
The [manifest](../results/minimum-double-ladder/verification.json)
and [independent replay](../results/minimum-double-ladder/replay.json)
record source hashes, compiler version, build logs, and finite ranges.

The independent checks include complete meetings for pure and weighted
sources, weighted secondary blocks through length 4096, the two affine
bridges, exact quotient identities, and smaller predecessors for odd
exponents. Opposite-exit examples test nonmeeting at the specified
clocks only; they establish no failure of eventual coalescence.

At R=65536 and R=1048576, the verifier materializes source and endpoint
coordinates and replays only the tails after the growing prefixes.
It does not iterate the full prefixes there. At R=2^k*s for k through
256 and small odd s, a separate check computes only modular powers;
the enormous sources are not materialized.

No theorem forces an arbitrary least counterexample into these
families. Removing the remaining exit condition, handling the
quadrupled phase, proving universal convergence, and settling
nontrivial cycles or divergence all remain open.
