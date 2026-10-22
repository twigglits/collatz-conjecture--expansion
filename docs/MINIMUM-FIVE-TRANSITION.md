# A variable negative-five block crosses both separated windows

The normalized secondary obstruction has a later escape. A third
variable block carries the endpoints 4b-17 and 3b-17 to 3d-5 and
2d-5. If d=5 modulo 16, these two paths merge. This yields new
least-counterexample exclusions inside arbitrarily long secondary
separated windows, with all three block lengths allowed to grow.

The [Lean module](../lean/MinimumFiveTransition.lean) has nineteen
audited kernel roots. It constructs suitable pure exponents beyond
every bound and suitable weights at any fixed initial exponent.
It does not cover every final exit residue or prove convergence of
the whole family. The positive-integer Collatz conjecture remains
unresolved.

## The third block

Start with the earlier coordinates

    R>=14, r>=5, w,u,q>0,
    9^R*w+7=2^(57+11r)*u,       a=3^(33+7r)*u,
    9a+1=2^(9+11j)*q,         b=3^(6+7j)*q.

The main source and its positive smaller fourth partner are

    N=4*8^R*w-5,       S=2^(2R+13)*w-1.

Their secondary endpoints are

| Source | Ordinary clock | Endpoint |
|---|---:|---:|
| N | 5R+107+18r+18j | 4b-17 |
| S | 4R+121+18r+18j | 3b-17 |

Now suppose k>=0 and v>0 satisfy

    b=1+2^(3k+4)*v,       d=9^(k+1)*v.                  (1)

The new kernel profiles are

    C^(9+5k)(4b-17)=3d-5,
    C^(4+5k)(3b-17)=2d-5.                               (2)

They use the two short bridges

    C^9(64x-13)=27x-5,
    C^4(48x-14)=18x-5,       x>0.

Their shortcut words are OOEEOE and EOE, where O is (3n+1)/2
at an odd input and E is n/2 at an even input. Substituting
x=8^k*v into the bridges gives 8^k*(27v)-5 and 8^k*(18v)-5.
The existing weighted-ladder identity then applies:

    C^(5k)(8^k*z-5)=9^k*z-5,       z>0.

Each cycle copy has shortcut word OOE and five ordinary steps.
This proves (2). All actual inputs and iterates are positive;
the negative-five cycle supplies an auxiliary parity pattern.

## The final local merger

The sufficient exit condition is

    d=5 modulo 16.                                     (3)

Write d=16t+5. The small affine profiles are

    C^4(48t+10)=18t+4=C^6(32t+5).

Combining these with (2) gives

    C^(13+5k)(4b-17)=C^(10+5k)(3b-17).

The full source clocks are therefore

    C^(5R+120+18r+18j+5k)(N)
      =C^(4R+131+18r+18j+5k)(S).                        (4)

Since 0<S<N, N cannot be a least positive counterexample.
No convergence theorem for every S is needed for this deduction:
under the least-counterexample assumption, a smaller positive
source already converges. Equation (4) is a specified meeting,
not a claim about the earliest one.

The coordinate equations and condition (3) force u,q,v all odd.
Consequently the three exact binary valuations are

    v2(9^R*w+7)=57+11r,
    v2(9a+1)=9+11j,
    v2(b-1)=3k+4.

In particular the new delay is present after q has been normalized.
This family lies at b=1 modulo 16, disjoint from the earlier
successful exit b=23 modulo 64. The final condition (3) is still
a restriction; it is not a cover of all normalized secondary units.

## Both obstructions coexist with the later merger

The preceding [phase theorem](MINIMUM-SEVENTEEN-PHASE.md) separates
the secondary windows whenever 2^(H+6) divides b-1. Condition (1)
therefore gives that separation for every

    H+6<=3k+4.

For k>0 this includes H=3k-2. Every pair of additional clocks
s,t<=H satisfies

    C^s(3b-17) != C^t(4b-17).

The specified later N-clock in (4), measured from its secondary
endpoint, is 13+5k, which exceeds 3k-2. There is no contradiction.

For j>0, the primary four-source windows are also separated through
11j-4. These windows start at the earlier transition endpoints
72a-17,81a-17,64a-17,48a-17, at their respective base clocks.
They say nothing about meetings before those bases.

For any requested H, choose j=k=H+1. The kernel constructs both
primary and secondary separation through H together with the
later fourth-source merger and the least-source exclusion.
Suitable pure exponents are unbounded for every fixed r>=5;
weights are unbounded at every fixed R>=14 and r>=5. Thus
neither of the two fixed-window obstructions rules out useful
meetings at variable later clocks.

## Unbounded pure and weighted realizations

For every r,j,k and exponent bound B, the kernel constructs
R>B, R>=14 and positive u,q,v satisfying all three coordinate
equations and (3) with w=1. The lift itself does not require
r>=5; that hypothesis is needed for the fourth-source profile.

Put

    m=57+11r, K=9+11j, D=2^m, E=2^K, T=2^(3k+4),
    A=3^(35+7r), c=3^(6+7j), f=9^(k+1).

The elementary scale inequality E<=c follows from
512<=729 and 2048<=2187. A finite kernel lemma chooses odd
0<eps<16 with

    f*eps=5 modulo 16.

Set

    F=7cA+D(c-E)+(16-eps)*D*E*T.

The expression cA+F is divisible by eight, and cA is odd.
The existing unbounded affine exponent lift at precision index
m+K+3k+5 gives

    cA*9^R+F=16*D*E*T*Q,       Q>0.

Define v=16(Q-1)+eps. Cancelling the padding gives

    cA*(9^R+7)+D(c-E)=D*E*T*v.                           (5)

Odd-factor cancellation modulo D supplies the positive quotient
u=(9^R+7)/D. Adding D*E to (5) and cancelling D gives

    c*(A*u+1)=E*(1+T*v).

Cancel the odd c modulo E to obtain a positive q with

    A*u+1=E*q.

Cancelling E from the previous equality yields c*q=1+T*v,
which is (1). Since A*u=9a, this also supplies the secondary
coordinate equation. The residue of v gives (3). These are
kernel proofs using natural-number arithmetic.

For a fixed initial R, choose a larger pure exponent L and set
w=9^(L-R). Taking L>R+B+1 ensures w>B and preserves all the
coordinate equations. The same smaller source S remains below N
when R>=14.

## Verification and remaining gap

Run the [verifier](../verify_minimum_five_transition.py) with

    python3 verify_minimum_five_transition.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 --cache /tmp/collatz-locality-dev

The [manifest](../results/minimum-five-transition/verification.json)
records a fresh build of the new module and authenticated reuse of
its dependencies. Omitting --cache rebuilds the dependencies
sequentially. All nineteen audited roots use only standard logical
axioms; none is axiom-free. The finite unit lemma uses propext
and Quot.sound. No native reduction or external mathematical
premise is used.

The [independent Python replay](../results/minimum-five-transition/replay.json)
checks the short bridges, generic third-block profiles, local merger,
and full weighted source meetings. It compares ordinary, shortcut
and inverse operations and checks all three intermediate endpoints.
The two older partners also have their complete primary prefixes
replayed. Full shortcut meetings add one common halving to (4),
ending at 9t+2.

For positive j and k, the replay checks both preceding separated
windows using exact phase signatures; small windows also compare
actual integer-value sets. Complete examples include R=16384,
r=4096, j=4096 and k=4096, in different cases. Larger examples
R=65536 and 1048576 have only their transition tails, later
merger and windows replayed. Pure examples use modular powers
without materializing their enormous starting values or trajectories.

A universal cover of the final negative-five exits is still missing.
These results do not establish family convergence, exclude arbitrary
least counterexamples, settle nontrivial cycles or divergence, or
prove the full positive-integer Collatz conjecture.
