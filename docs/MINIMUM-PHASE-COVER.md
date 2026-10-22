# Two partners cover every endpoint that is two modulo three

For every natural a and b with b=3a+2, at least one of a and 2b+1
coalesces with b. This kernel theorem strengthens the earlier cover
for endpoints 9a+5 and needs only two partners. Its odd case covers
every odd-block length.

Two weighted constructions apply the cover to smaller original sources.
For pure coefficients, they exclude

    2*8^R-5 when R=26 mod32,
    4*8^R-5 when R=35 mod64

as least positive Collatz counterexamples. The first class lies in the
opposite doubled exit left open by the preceding result. The second
is a new exclusion in the quadrupled phase. Other exponent classes
remain open, and the positive-integer Collatz conjecture is unresolved.
No universal convergence of either family is claimed.

The [Lean module](../lean/MinimumPhaseCover.lean) has nineteen audited
kernel roots. The four finite modular equalities are axiom-free;
the other roots use only standard logical axioms. There is no native
reduction, added mathematical premise, or unproved merger hypothesis.

## The scalar cover

Let b=3a+2. All clocks below count ordinary Collatz operations.

| Case | Partner | Partner clock | Clock from b |
|---|---:|---:|---:|
| b=0 mod4 | a | 3 | 2 |
| b=2 mod4 | 2b+1 | 3 | 2 |
| b odd, 3^k*q=1 mod4 | a | 2k+3 | 2k+2 |
| b odd, 3^k*q=3 mod4 | 2b+1 | 2k+4 | 2k+3 |

In the odd rows, b+1=2^k*q with k>0 and q positive odd. The two
exit residues exhaust the possibilities. The preceding odd-block
cover already joins b to either b-1 or 2b+1. When b is odd, a is
odd too and C(a)=b-1, so a supplies the adjacent partner with one
additional step. When b is divisible by four, write a=4v+2 and
b=12v+8: C^3(a)=C^2(b)=3v+2.

The partner 2b+1 is larger than b. Consequently the scalar theorem
alone is not a universal descent theorem. Its application here uses
an original source smaller than N that reaches 2b+1.

The independent full-word replay uses clocks 4 and 3 in the second
row by appending one common halving. This completes the forced
halving after the last odd operation on the path from b.

## The doubled construction

Let R>=2, w>0, X=9^R*w, and assume X=17 modulo 256. Set

    N=2*8^R*w-5,
    P=2^(2R+1)*w-1,
    Q=3*8^(R-1)*w-5,
    b=(81X-97)/256,       a=(b-2)/3.

The kernel proves 0<P<N, 0<Q<N, and 3(N+5)=16(Q+5), together with

| Source | Ordinary clock | Endpoint |
|---|---:|---:|
| N | 5R+13 | b |
| P | 4R+12 | 2b+1 |
| Q | 5R+7 | a |

The residue condition and divisibility of X by three give coordinates

    X=768u+273,       X/3=256u+91,
    b=243u+86,        a=81u+28.

Thus b=3a+2. The two-partner cover yields a positive source smaller
than N that coalesces with N, excluding N as least.

The growing prefixes are the existing weighted OOE path and the
all-odd path. Three kernel bridges finish the source coordinates:

    C^13(1536u+541)=243u+86,
    C^10(2304u+818)=486u+173,
    C^12(256u+86)=81u+28.

For w=1, the kernel checks 9^32=1 and 9^26=17 modulo 256, giving
the pure exponent class R=26 modulo 32. Such R has k=1 and odd
part s=1 modulo 4, so 3^k*s=3 modulo 4. This is a class left open
by the [preceding doubled-ladder exclusion](MINIMUM-DOUBLE-LADDER.md).

## The quadrupled construction

Let R>=2, w>0, X=9^R*w, and assume X=473 modulo 512. Set

    N=4*8^R*w-5,
    P=2*8^R*w-5,
    Q=2*8^(R-1)*w-5,
    b=(243X-251)/512,       a=(b-2)/3.

The kernel proves 0<P<N, 0<Q<N, and N+5=2(P+5)=16(Q+5), with

| Source | Ordinary clock | Endpoint |
|---|---:|---:|
| N | 5R+16 | b |
| P | 5R+14 | 2b+1 |
| Q | 5R+11 | a |

Here X=4608u+3033 and X/9=512u+337. Consequently
b=2187u+1439 and a=729u+479, so again b=3a+2. These endpoints
are 8 modulo 9, outside the earlier scalar cover for 9a+5.

The bridges are

    C^16(18432u+12127)=2187u+1439,
    C^14(9216u+6061)=4374u+2879,
    C^16(1024u+669)=729u+479.

For w=1, the kernel checks 9^64=1 and 9^35=473 modulo 512.
This excludes every pure quadrupled source with R=35 modulo 64
as least. The argument covers all parities of b, including either
exit of any subsequent odd block.

## Verification and remaining scope

Run a fresh dependency build with

    python3 verify_minimum_phase_cover.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

If the earlier verified objects remain available, add

    --cache /tmp/collatz-locality-dev

The [verifier](../verify_minimum_phase_cover.py) authenticates the
preceding manifest. A cached dependency is reused only when its
source, prior log, and object bytes match that verified record and
the compiler version agrees. It copies the authenticated object
into an isolated import directory; mismatches are rebuilt. The new
module is always built afresh. The current run reused 37 verified
dependency objects and freshly built the new module with 16 threads.

The [manifest](../results/minimum-phase-cover/verification.json) records
fresh and reused builds separately. The [independent replay](../results/minimum-phase-cover/replay.json)
checks all scalar branches, the six bridges, complete weighted and
pure meetings, and constructed subsequent odd blocks through length
4096 at both exits. Every complete selected path is checked with
ordinary operations, shortcut operations, and reversed inverse steps.

Larger examples materialize source and endpoint coordinates but replay
only the bridges and local meetings; their growing prefixes are not
numerically iterated. A separate modular-only section does not
materialize its enormous sources. None of these finite checks is
substituted for a universal kernel proof.

These constructions do not cover every doubled or quadrupled
exponent, every weight, or every possible least counterexample.
Family convergence, universal cap/residual estimates, nontrivial
cycles, divergence, and the full Collatz conjecture remain open.
