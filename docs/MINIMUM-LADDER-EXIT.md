# Smaller sources after a growing return ladder

Selected return ladders have a much smaller coalescing source just after
their growing prefixes end. For odd R>=3 and N=8^R-5, the new kernel
proofs cover R=7 modulo 8, R=11 modulo 16, and R=1 modulo 16.
Together these are four of the eight odd residue classes modulo 16.

The smaller source is a Mersenne number, P=2^j-1. It joins the orbit
of N eight, nine, or ten ordinary steps after clock 5R. Consequently
none of these N is a least positive counterexample. This is a
least-counterexample exclusion, not a convergence theorem for the
whole family. The positive-integer Collatz conjecture remains unresolved.

The [Lean module](../lean/MinimumLadderExit.lean) has 21 audited kernel
roots, including one axiom-free finite period certificate. The path
identities, size bounds, residue restrictions, and parameterized
exclusions use no native reduction axiom or external mathematical premise.

## Exact paths and their clocks

The preceding [return-ladder theorem](MINIMUM-RETURN-LADDER.md) gives

    C^(5R)(N) = 9^R-5,       N=8^R-5,

with prefix minimum N through clock 5R. Write X=9^R. The new paths are:

| Condition on R, with R>=3 | Smaller source P | Clock from N | Clock from P | Meeting value |
|---|---|---:|---:|---|
| R=7 mod8 | 2^(2R+1)-1 | 5R+8 | 4R+9 | (9X-1)/64 |
| R=11 mod16 | 2^(2R-1)-1 | 5R+9 | 4R+8 | (9X+31)/128 |
| R=1 mod16 | 2^(2R+1)-1 | 5R+10 | 4R+11 | (27X+13)/128 |

Every quotient displayed in the applicable row is integral. The kernel
proves 0<P<N and equality of the two ordinary iterates. The meeting
clocks differ; coalescence does not require synchronous orbits.

The inverse shortcut costs at those meeting values are respectively

    (e,o) = (5,2R+2), (4,2R+2), (5,2R+3).

Thus only four or five even inverse operations are needed at these
later meeting values. The odd counts grow with R. No assertion of
optimal inverse cost is made.

These meetings are not visits to 20 modulo 27. In the first row the
meeting value is 8 modulo 9. In the second and third rows it is 11
and 2 modulo 27, respectively. The exclusion uses direct coalescence
and does not require a residue-20 meeting.

## The short arithmetic behind the paths

A pure odd shortcut block has the kernel identity

    C^(2j)(2^j-1) = 3^j-1.

Three short ordinary paths then supply the meeting:

| Parameter u>=0 | Path from the ladder endpoint | Path from the Mersenne block endpoint |
|---|---|---|
| First row | C^8(64u+52)=9u+8 | C^7(192u+170)=9u+8 |
| Second row | C^9(384u+148)=27u+11 | C^10(128u+50)=27u+11 |
| Third row | C^10(128u+4)=27u+2 | C^9(384u+26)=27u+2 |

The first column of paths uses the shortcut words EEOEEO, EEOEEEO,
and EEOEOEO, respectively. Here O includes an ordinary odd step
and its following halving, and E is a single even halving.
The inverse words from the meeting value to the right-hand source
are EEEEOE, EEOOEOE, and EEOEEOE. Appending j odd inverses gives
the exact costs in the preceding section.

The applicable coordinates follow from

    R=7 mod8    ==> 9^R=57 mod64,
    R=11 mod16  ==> 3^(2R-1)=51 mod128,
    R=1 mod16   ==> 9^R=9 mod128.

The finite period identities are axiom-free kernel computations;
their extension to all exponents is proved algebraically. The
short path proofs check each parity and every inverse guard.

The size improvement also has exact power identities:

    (P+1)^3 = 8*(N+5)^2       in the first and third rows,
    8*(P+1)^3 = (N+5)^2       in the second row.

These follow from the kernel power identities and the definitions
of N and P. In particular, the smaller source has about two thirds
as many binary digits as N as R grows. This estimate concerns
coalescing source size, not a forward stopping-time bound.

If N were a least counterexample, the positive smaller P would
reach one. Their actual coalescence would then force N to reach one.
The kernel formalizes this contradiction for each of the three rows.
It does not independently establish convergence of every P.

## An escape after an arbitrarily long obstructed prefix

The [whole-window result](MINIMUM-LADDER-WINDOW.md) constructed

    K=2*(s+3),       R=1+2*3^K*(h+1),       N=8^R-5,

with exact inverse minimum M_(i+s)(b_i)=N simultaneously at all
0<=i<R. Its R-1 actual residue-20 visits occur before clock 5R.

Now restrict h=4a+2, with a>=0. Since 3^K=1 modulo 4, R=7 modulo 8.
The first new path applies, with

    P=2^(2R+1)-1 < N,
    C^(4R+9)(P) = C^(5R+8)(N).

This combines two kernel statements about the same source. Every
target in its growing prefix resists the chosen extra budget s,
but eight ordinary steps after that prefix a smaller source joins
with only five even inverse operations.

For every s, every visit-count bound L, and every source bound B,
the kernel constructs one such R with R-1>L and N>B. The entire
prefix obstruction and the later escape hold simultaneously.
The family is therefore not a family of least counterexamples,
despite its arbitrarily long obstruction. This does not extend
the late escape to all h or all odd R.

For example, s=0,a=0 gives R=4375. The source has 13,125 binary
digits, while P has 8,751. The ordinary meeting clocks are 21,883
from N and 17,509 from P. The independent replay checks these
complete paths, rather than just their congruences.

## Verification and remaining work

Run

    python3 verify_minimum_ladder_exit.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_ladder_exit.py) authenticates the
69 preceding whole-window hashes, freshly builds 33 modules in
dependency order, and audits all 21 new roots. Lean uses the
requested thread count within each process. The preceding sources
and verification records are preserved.

Independent Python checks replay the generic short paths, the
period conditions, and complete positive coalescing paths over
specified exponent ranges. Actual whole-window examples include
complete forward prefixes and the full Mersenne paths. Larger
examples have only algebraic coordinates and their short tails
checked; a separate modular census does not construct the huge
sources. The [manifest](../results/minimum-ladder-exit/verification.json)
and [replay](../results/minimum-ladder-exit/replay.json) record
these scopes separately, with exact counts and hashes.

The missing universal step remains substantial: the new paths do
not cover all odd exponents, all h in the whole-window family, or
arbitrary positive starts. They do not prove convergence of the
covered infinite families, exclude every possible least counterexample,
or settle nontrivial cycles or divergence. The full Collatz goal
remains active.

