# No fixed exit window covers the three transition sources

For every finite horizon H, the three sources in the
[negative-seventeen transition](MINIMUM-SEVENTEEN-TRANSITION.md) have
examples whose exit windows remain disjoint: neither smaller partner
meets the main source at any pair of additional ordinary clocks s,t<=H.
This holds for arbitrarily large pure exponents, and for arbitrarily
large weights even when both initial block lengths are fixed.

The [Lean module](../lean/MinimumSeventeenSeparation.lean) has fourteen
audited kernel roots. The result rules out a uniform bound on these
exit clocks. It leaves open coalescence at unbounded later clocks and
constructions using additional partners. It is not a nonconvergence
result: an explicit separated triple is also kernel-certified to reach
one. The positive-integer Collatz conjecture remains unresolved.

## The scalar separation

Let a>0 and suppose

    2^(H+12) divides 9a+1.                                  (1)

Then, for every pair of ordinary clocks s,t<=H,

    C^s(81a-17) != C^t(72a-17),
    C^s(64a-17) != C^t(72a-17).                            (2)

These are inequalities across all pairs of clocks in the windows,
including clock zero. Condition (1) implies a=7 modulo 64, outside
the two exits a=13 and 61 modulo 64 already covered by the merger
construction. There is no claim of separation beyond H.

The proof uses natural-number constants c and the auxiliary map

    D(c)=3c-9 if c is odd, and c/2 if c is even.

For c>=9, one ordinary Collatz step has the exact divisibility rule

    2d divides 9n+c  ==>  d divides 9C(n)+D(c).            (3)

The premise fixes the parity of n to that of c. In the odd case,
the new expression is 3(9n+c); in the even case it is (9n+c)/2.
Induction loses at most one binary digit of precision per ordinary
step. Starting with (1) therefore retains precision modulo 4096
through every time t<=H.

## Three disjoint sets of constants

The initial constants are 225, 234 and 217 because

    9(72a-17)+225=72(9a+1),
    9(81a-17)+234=81(9a+1),
    9(64a-17)+217=64(9a+1).

Their finite D-orbits are

    225,666,333,990,495,1476,738,369,1098,549,1638,819,
    2448,1224,612,306,153,450;

    234,117,342,171,504,252,126,63,180,90,45;

    217,642,321,954,477,1422,711,2124,1062,531,1584,
    792,396,198,99,288,144,72,36,18,9.

The first list cycles from its start. The second enters a cycle at
126; the third at 18. Lean checks closure, the bounds 9<=c<4096,
and disjointness of the first list from each of the other two.

At the formal reference a=-1/9, the scalar values are -25, -26 and
-217/9. Their patterns lead respectively to the negative seventeen,
five and one cycles. The third reference is rational; the formal proof
uses the integer constants and rule (3), entirely over natural numbers.
It does not apply the ordinary integer map to a noninteger input.

Every positive iterate in the three windows has 9 times its value
congruent to -c modulo 4096 for a constant in the corresponding list.
Disjoint lists in that modulus give disjoint residue sets. Equal
positive values would have equal residues, proving (2).

## Pure exponents and fixed weighted prefixes

Fix any transition block count r, horizon H and exponent bound B.
The kernel constructs R>B, R>=14 and u>0 such that

    9^R+7=2^(57+11r)*u,
    a=3^(33+7r)*u,
    2^(H+12) divides 9a+1.                                (4)

The preceding transition theorem gives positive smaller partners

    N=4*8^R-5,       P=2^(2R+5)-1,       Q=2^(2R+15)-1,

with endpoints 72a-17, 81a-17 and 64a-17. Consequently the windows
from N at clocks 5R+91+18r through 5R+91+18r+H are disjoint from
the windows from either partner at clocks 4R+99+18r through
4R+99+18r+H. This does not exclude meetings before these windows.

To obtain (4), put m=57+11r, D=2^m and A=3^(35+7r). The earlier
odd affine exponent lift applies to

    A*9^R+(7A+D),

because A is odd and A+(7A+D) is divisible by eight. An unbounded
version makes this expression divisible by D*2^(H+12) beyond any
exponent bound. Cancelling the odd factor A proves D divides 9^R+7.
Writing that quotient as u and cancelling D gives

    A*u+1=2^(H+12)*q,

which is exactly the last condition in (4). Odd-factor cancellation
and the unbounded affine lift are also kernel roots.

There is a stronger weighted statement. For every fixed R>=14 and r,
every H and every weight bound B, there exist w>B and u>0 satisfying

    9^R*w+7=2^(57+11r)*u

and the same shadow divisibility and window separation. The partners
2^(2R+5)*w-1 and 2^(2R+15)*w-1 remain positive and smaller than
4*8^R*w-5. The proof takes a larger pure exponent S and sets
w=9^(S-R). Thus the obstruction persists without increasing either
initial block count R or r.

## A convergent separated example

The named constants witnessWeight and witnessUnit in Lean specify
an example with R=14, r=0 and H=128. Its three source sizes and
ordinary arrival clocks are

| Source | Binary digits | Arrival at one |
|---|---:|---:|
| N | 239 | 1795 |
| P | 228 | 1978 |
| Q | 238 | 2660 |

The kernel certifies the coordinate conditions, shadow divisibility,
and these three arrivals. The general theorem separates the 129-state
exit windows. Python independently replays all three arrivals and
checks that they are the first visits to one.

## Verification and next requirement

Run the [verifier](../verify_minimum_seventeen_separation.py) with

    python3 verify_minimum_seventeen_separation.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 --cache /tmp/collatz-locality-dev

The cache requires exact compiler, source, prior-log and object
authentication. Verified dependency objects are copied into an isolated
import directory, and the new module is freshly built. Omit --cache
to build all dependencies afresh. The [manifest](../results/minimum-seventeen-separation/verification.json)
distinguishes reused and fresh builds and records their provenance.
All new roots use only standard logical axioms; none uses native
reduction or an external mathematical premise.

The [independent replay](../results/minimum-seventeen-separation/replay.json)
checks complete weighted source prefixes, every state of the specified
exit windows, shadow congruences and disjoint residues. Complete cases
include R=16384, r=4096 and H=16384, in different examples. Larger
coordinate cases replay only transition and exit tails. Pure exponent
examples use modular powers without constructing their enormous
starting integers or trajectories.

Extending the two-partner construction requires an argument that allows
unbounded later clocks, or additional partners that escape this
separation. The theorem does not rule out either route. Arbitrary
least-counterexample exclusion, full family convergence, nontrivial
cycles, divergence and the full Collatz conjecture remain open.
