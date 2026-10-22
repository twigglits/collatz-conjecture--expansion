# Exact halving phases obstruct fixed exit windows

The fourth smaller source does not provide a universal fixed exit-clock
bound. For every horizon H, all three partners can have transition
windows disjoint from the main source's window, even though the fourth
partner and the main source have reference patterns on the same
negative-seventeen cycle. Exact powers of two distinguish their phases.

A second obstruction persists after the next block has ended: the
quotient q can already be odd, while the two secondary windows remain
separated for an arbitrarily long horizon. Both obstructions have pure
and fixed-prefix weighted realizations. Neither proves separation for
all time or divergence.

The [Lean module](../lean/MinimumSeventeenPhase.lean) has twenty-two
audited kernel roots. It also preserves examples with later mergers
and certifies a concrete separated example in which all four sources
reach one. The positive-integer Collatz conjecture remains unresolved.

## The primary four-source windows

Use the [fourth-source coordinates](MINIMUM-SEVENTEEN-FOURTH.md):

    R>=14, r>=5, w,u>0,
    9^R*w+7=2^(57+11r)*u,       a=3^(33+7r)*u,

    N=4*8^R*w-5,
    P=2^(2R+5)*w-1,
    Q=2^(2R+15)*w-1,
    S=2^(2R+13)*w-1.

All three partners are positive and smaller than N. Their transition
profiles are:

| Source | Ordinary base clock | Endpoint |
|---|---:|---:|
| N | 5R+91+18r | 72a-17 |
| P | 4R+99+18r | 81a-17 |
| Q | 4R+99+18r | 64a-17 |
| S | 4R+100+18r | 48a-17 |

If

    2^(H+13) divides 9a+1,                               (1)

then every pair of additional ordinary clocks s,t<=H satisfies

    C^s(81a-17) != C^t(72a-17),
    C^s(64a-17) != C^t(72a-17),
    C^s(48a-17) != C^t(72a-17).                          (2)

The first two inequalities follow from the earlier disjoint shadow
sets. The third requires the new phase argument. The source windows
start at the base clocks in the table; nothing here excludes meetings
before those windows or beyond their horizons. There is also no claim
that the three partner windows are disjoint from each other.

For every fixed r>=5, every horizon H and every exponent bound B,
the kernel constructs R>B, R>=14 and u>0 satisfying the pure
coordinates w=1 and (2). At every fixed R>=14 and r>=5, weights
beyond every bound satisfy the same conclusions. The existing
unbounded shadow lift applies with its horizon increased by one.

## Why overlapping reference cycles can still separate

For an odd scale M, define

    D_M(c)=3c-M if c is odd, and c/2 if c is even.

Suppose c>=M and M*n+c=2^e*v with e>0 and v odd. The parities
of n and c agree. An ordinary step gives:

| Branch | New scaled sum | New binary exponent |
|---|---:|---:|
| Odd | M*C(n)+D_M(c)=3*(M*n+c) | e |
| Even | M*C(n)+D_M(c)=(M*n+c)/2 | e-1 |

Thus each halving reduces the exact binary exponent by one; an odd
step preserves it. The kernel proves this rule, uniqueness of the
binary exponent, and an induction through any finite closed table
of pairs (reference constant, halving count modulo a period).

If all table constants lie below 2^B and at least B binary digits
remain, equal positive iterates must have equal reference constants:
their scaled values have residues -c modulo 2^B. Their exact binary
exponents must then also agree. A phase mismatch rules out equality
even when the reference constants themselves occur in both tables.

For the primary comparison use M=9 and

    9(72a-17)+225=72(9a+1),
    9(48a-17)+201=48(9a+1).

If the exact binary exponent of 9a+1 is K, these two sums start
with exponents K+3 and K+4. The negative-seventeen reference cycle
has eleven halvings in eighteen ordinary steps. The table beginning
at 225 has eighteen states; the table beginning at 201 has thirty-one
states, with thirteen before the cycle.

Both tables contain the same eighteen cycle constants. At their
first common constant 1098, the main table has used four halvings
and the fourth table seven. Throughout the shared cycle their
halving phases therefore differ by three modulo eleven. Equality
of positive values would instead require a difference of one,
from the initial exponents K+3 and K+4. This is impossible.

All constants in these tables are at least 9 and below 8192; the
largest is 4392. Condition (1) retains enough binary precision
through every time in the window. The finite table closure and
phase incompatibility are checked in the kernel, not by native
computation.

## A normalized secondary exit also has unbounded delays

Suppose additionally

    9a+1=2^(9+11j)*q,       b=3^(6+7j)*q,       q>0.

The previous kernel profiles give

    C^(16+18j)(72a-17)=4b-17,
    C^(21+18j)(48a-17)=3b-17.

For b>=6, the new scalar theorem says that

    2^(H+6) divides b-1                                  (3)

implies

    C^s(3b-17) != C^t(4b-17) for all s,t<=H.              (4)

This time take M=1 and reference constants 13 and 14:

    (4b-17)+13=4(b-1),       (3b-17)+14=3(b-1).

The first reference path is

    13,38,19,56,28,14,7,20,10,5,14,...

The second starts at 14 on the shared five-step cycle. That cycle
has three halvings. Reaching 14 from 13 also uses three halvings.
Hence equal reference constants have equal halving phases modulo
three. The initial binary exponents differ by two, preventing
equality of the corresponding positive values. All constants lie
below 64.

The full secondary windows in (4) begin at ordinary clocks

    N: 5R+107+18r+18j,
    S: 4R+121+18r+18j.

For EVERY fixed r>=5 and j, every H and every exponent bound,
pure exponents beyond that bound satisfy the transition equations,
condition (3), and q positive odd. At every fixed R>=14, weights
beyond every bound satisfy the same statements. The quotient is
already odd: v2(9a+1)=9+11j exactly. The extra delay therefore
cannot be attributed to an unremoved factor of two in q.

These existence statements and the absence of a uniform secondary
exit-clock bound are kernel proofs. They leave open meetings at
later clocks depending on the source.

## Lifting the secondary unit

A new elementary binary inverse lemma proves that, for every odd c
and k>=0, there are odd e and q with

    0<e<2^(k+1),       c*e=1+2^(k+1)*q.

The induction either keeps e or adds 2^(k+1), according to the parity
of q. It supplies an inverse modulo an arbitrary power of two.

For the secondary lift put

    m=57+11r, K=9+11j, D=2^m, E=2^K, V=2^(H+6),
    A=3^(35+7r), c=3^(6+7j).

Choose odd 0<eps<V with c*eps=1+V*z. Apply the existing unbounded
affine exponent lift to

    F=7A+D+(V-eps)*D*E,

obtaining R beyond the requested bound and

    A*9^R+F=V*D*E*Q,       Q>0.

Set q=V*(Q-1)+eps. Cancelling the padding gives

    A*(9^R+7)+D=D*E*q.

Cancelling the odd A modulo D gives the positive quotient
u=(9^R+7)/D; cancelling D then gives A*u+1=E*q. Finally,
c*q=1+V*(c*(Q-1)+z), which is (3). The construction also proves
q odd. Fixed-prefix weights follow by replacing a larger pure
exponent T with w=9^(T-R).

## Separation and later success coexist

The successful secondary exit b=23 modulo 64 still gives the earlier
fourth-source merger. Choosing its block count j=H+1 also supplies
condition (1). Thus the kernel constructs arbitrarily large pure
exponents, and weights beyond every bound at a fixed initial R,
for which all three primary windows are separated through H but
the fourth source later meets N. The full merger clocks remain

    N: 5R+117+18r+18j,       S: 4R+128+18r+18j.

These are specified meetings, not claims of earliest meetings.

There is also a concrete convergent example with R=14, r=5, j=1
and secondary horizon H=128. The named witness constants in Lean
give these source sizes and ordinary arrival clocks:

| Source | Binary digits | Arrival at one |
|---|---:|---:|
| N | 308 | 2683 |
| P | 297 | 3675 |
| Q | 307 | 2682 |
| S | 305 | 2680 |

Lean certifies positivity, the two coordinate equations, the odd
quotient, condition (3), and all four arrivals. Python additionally
checks that these are the first arrivals. The primary windows
are separated through seven steps and the secondary N,S windows
through 128 steps.

## Verification and remaining requirement

Run the [verifier](../verify_minimum_seventeen_phase.py) with

    python3 verify_minimum_seventeen_phase.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 --cache /tmp/collatz-locality-dev

The [manifest](../results/minimum-seventeen-phase/verification.json)
records a fresh new-module build and authenticated reuse of prior
dependencies. Omitting --cache rebuilds every dependency sequentially.
All twenty-two roots use only standard logical axioms; none is
axiom-free. The phase-table root uses propext and Quot.sound.
No native reduction or external mathematical premise is used.

The [independent replay](../results/minimum-seventeen-phase/replay.json)
checks finite phase closure, binary inverses, complete weighted
source prefixes, both kinds of separated windows, delayed meetings
and the convergent witness. Ordinary, shortcut and inverse paths
are compared for the complete prefixes. Exact residues and binary
exponents produce disjoint phase signatures; small windows also
compare actual value sets. This proves all cross-time inequalities
without a quadratic enumeration of clock pairs.

Complete examples include R=16384, r=4096, j=4096 and H=16384,
in different cases. Larger R=65536 and 1048576 cases replay only
transition tails, secondary tails and windows. Pure lift examples
use modular powers without constructing the enormous pure sources
or trajectories. The main primary window is replayed in both the
old three-source and new phase checks; those state counts are
not counts of distinct visits.

A successful cover must allow source-dependent later clocks or
use additional partners with compatible phases. These obstructions
do not rule out such a cover. They do not prove family convergence,
exclude arbitrary least counterexamples, settle nontrivial cycles
or divergence, or solve the full Collatz conjecture.
