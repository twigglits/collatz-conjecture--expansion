# A fourth source crosses arbitrarily long separated exit windows

A fourth, smaller positive source gives new least-counterexample
exclusions inside the class where the two earlier transition partners
have arbitrarily long separated exit windows. The new merger allows
an arbitrary second block of negative-seventeen parity cycles. A
specific residue condition at its exit supplies the final meeting.

The [Lean module](../lean/MinimumSeventeenFourth.lean) has eighteen
audited kernel roots. For every first block count r>=5 and horizon H,
the conditions occur at arbitrarily large pure exponents, and at
arbitrarily large weights for every fixed initial exponent R>=14.
They do not cover every exit residue or prove convergence of the
whole family. The positive-integer Collatz conjecture remains unresolved.

## Four source profiles

Let R>=14, r>=5 and w,u>0 satisfy

    X=9^R*w,       X+7=2^(57+11r)*u,
    a=3^(33+7r)*u.                                      (1)

Define the four positive sources

    N=4*8^R*w-5,
    P=2^(2R+5)*w-1,
    Q=2^(2R+15)*w-1,
    S=2^(2R+13)*w-1.

The new source S is strictly smaller than N. Together with the
[preceding transition](MINIMUM-SEVENTEEN-TRANSITION.md), the new
kernel proof gives these ordinary Collatz clocks:

| Source | Clock | Endpoint |
|---|---:|---:|
| N | 5R+91+18r | 72a-17 |
| P | 4R+99+18r | 81a-17 |
| Q | 4R+99+18r | 64a-17 |
| S | 4R+100+18r | 48a-17 |
| S | 4R+102+18r | 72a-25 |

Thus two more ordinary steps from S's first endpoint give a value
eight below N's transition endpoint. The source comparison only
requires R>=14 and w>0; the profile requires r>=5.

The new bridge, valid for every q>0, is

    C^164(2^108*q-11160262)=3^56*q-17,                    (2)

where 11160262=7*3^13+1. Its inverse description has 52 extra
even operations and 56 odd operations, hence 108 shortcut steps
and 164 ordinary steps. The all-odd prefix of S has ordinary length
4R+26 and reaches 3^13*X-1. Under (1), bridge (2) applies and is
followed by r-5 copies of the existing eighteen-step cycle pattern.
The total clock is 4R+26+164+18(r-5)=4R+100+18r.

Negative reference orbits determine these parity patterns. All sources
and iterates asserted in the profile theorems are positive integers.

## A second block and a local meeting

Suppose additionally that j>=0 and q>0 satisfy

    9a+1=2^(9+11j)*q,
    b=3^(6+7j)*q.                                      (3)

The new rotated bridge

    C^16(4096q-25)=2916q-17

has shortcut word OOOEOOOEEE, with O denoting (3n+1)/2 at an
odd input and E denoting n/2 at an even input. Combining this bridge
with j copies of the negative-seventeen cycle gives

    C^(16+18j)(72a-17)=4b-17,
    C^(21+18j)(48a-17)=3b-17.                            (4)

For the second equation, take two steps to 72a-25, then the earlier
nineteen-step bridge from 4096v-33 and j cycle copies. These are
kernel identities for every block count j, without a fixed clock bound.

The final exit condition is

    b=23 modulo 64.                                    (5)

Writing b=64v+23, the two paths meet at

    C^10(256v+75)=54v+16=C^7(192v+52).

Consequently the full source clocks satisfy

    C^(5R+117+18r+18j)(N)=C^(4R+128+18r+18j)(S).         (6)

Since 0<S<N, equation (6) excludes N as a least positive
counterexample. This inference does not require proving convergence
of every member of the S family. Neither (6) nor the finite checks
claim an earliest meeting.

## Compatibility with the earlier separation

When j>0, condition (3) supplies the previous
[separation theorem](MINIMUM-SEVENTEEN-SEPARATION.md) with horizon

    H0=11j-3,       H0+12=9+11j.

Every pair of clocks s,t<=H0 therefore satisfies

    C^s(81a-17) != C^t(72a-17),
    C^s(64a-17) != C^t(72a-17).                          (7)

These are windows after the respective transition clocks in the
table. They say nothing about meetings before or after those windows.
The new fourth source is outside the two partners covered by (7),
and its specified meeting with N has additional N-clock 26+18j,
which is greater than H0. There is no contradiction between (6)
and (7). In particular, merely enlarging a fixed window for P,Q
still cannot cover all the transition sources.

## Unbounded pure exponents and weights

For every r,j and exponent bound B, a kernel lift constructs
R>B, R>=14 and positive u,q satisfying (1), (3), (5) with w=1.
The lift itself does not require r>=5; that assumption is used for
the fourth-source merger and least-counterexample exclusion.

Put

    m=57+11r, K=9+11j, D=2^m, E=2^K,
    A=3^(35+7r), c=3^(6+7j).

A finite kernel lemma chooses an odd eps with 0<eps<64 and
c*eps=23 modulo 64. Define

    F=7A+D+(64-eps)*D*E.

The existing unbounded affine exponent lift applies because A is
odd and A+F is divisible by eight. At precision m+K+3 it gives

    A*9^R+F=64*D*E*Q,       Q>0.

Set q=64(Q-1)+eps. Cancelling the padding gives

    A*(9^R+7)+D=D*E*q.

Odd-factor cancellation shows D divides 9^R+7. Calling its positive
quotient u and cancelling D yields A*u+1=E*q, which is (3),
since A*u=9a. The residue of q gives (5).

At any fixed initial R, apply the pure lift at a larger exponent T
and set w=9^(T-R). Taking T beyond R+B+1 ensures w>B and
9^R*w=9^T. This proves unbounded weights with the same exit condition.

Finally, choosing j=H+1 makes (7) hold through any requested horizon
H. For every r>=5 there are therefore pure exponents beyond every
bound satisfying the new least exclusion and the old separation.
The same holds for weights beyond every bound at any fixed R>=14.
All these existence and exclusion statements are kernel theorems.

## Verification and remaining gap

Run the [verifier](../verify_minimum_seventeen_fourth.py) with

    python3 verify_minimum_seventeen_fourth.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 --cache /tmp/collatz-locality-dev

The [manifest](../results/minimum-seventeen-fourth/verification.json)
records a fresh build of the new module and separately authenticated
dependency reuse. Omit --cache to build all dependencies sequentially.
All eighteen audited roots use only standard logical axioms; none is
axiom-free. The finite exit-unit lemma uses propext and Quot.sound.
There is no native reduction or external mathematical premise.

The [independent Python replay](../results/minimum-seventeen-fourth/replay.json)
checks the new generic bridges, second-block profiles and local merger.
Complete weighted examples replay N and S from their starts to a
common value by ordinary, shortcut and inverse operations; they also
replay the complete P,Q transition prefixes. One shared halving is
added to the kernel meeting clocks to finish both shortcut words.
For j>0 the older separated windows are checked as well, using exact
congruences and disjoint residue sets, with actual value sets also
compared for horizons at most 128.

Complete examples include R=16384, r=4096 and j=4096, in different
cases. Larger coordinates R=65536 and 1048576 have only their four
transition tails, later merger and old exit windows replayed; their
growing prefixes are not iterated. Pure examples are checked with
modular powers without materializing enormous sources or trajectories.
These finite scopes supplement the universal kernel proofs.

The remaining second-block residues are not covered by condition (5).
In particular, this construction does not handle every a=7 modulo 64,
every transition source or arbitrary least counterexamples. Full family
convergence, nontrivial cycles, divergence and the full Collatz
conjecture remain open.
