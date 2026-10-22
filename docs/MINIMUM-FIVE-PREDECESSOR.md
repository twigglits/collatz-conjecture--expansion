# An immediate predecessor and its exact size boundary

The third endpoint 3d-5 has the positive immediate predecessor
U=d-2 whenever d is odd. This gives least-source exclusions throughout
an explicit finite region of block parameters, with weights unbounded
in every permitted parameter quadruple. The final odd-block residue
from the [previous result](MINIMUM-FIVE-ODD-EXIT.md) is unnecessary.

Outside that region U is strictly larger than the original source.
Every pure source in the coordinate family lies outside. For k>=6,
a kernel certificate also proves that inverse paths into U with at
most fourteen even-input shortcut steps cannot improve U. This
obstruction concerns this particular target and budget, not all ways
of finding a smaller coalescing source. Collatz remains unresolved.

The [Lean module](../lean/MinimumFivePredecessor.lean) contains twenty-one
audited theorem roots. The finite size-boundary theorem is axiom-free;
the remaining roots use only standard logical axioms. All finite
certificate computation is checked by the kernel, with no native
reduction or external mathematical premise.

## The immediate merger

Keep the earlier coordinates, with R>=14, r>=5 and w,u,q,v positive:

    X=9^R*w,                 X+7=2^(57+11r)*u,
    a=3^(33+7r)*u,           9a+1=2^(9+11j)*q,
    b=3^(6+7j)*q,            b=1+2^(3k+4)*v,
    d=9^(k+1)*v,             N=4*8^R*w-5.

The earlier third profile gives

    C^(5R+116+18r+18j+5k)(N)=3d-5.                       (1)

If v is odd, then d and U=d-2 are odd, U>=7, and

    C(U)=3U+1=3d-5.                                      (2)

Thus U and N coalesce. This includes d=3 mod4 and both final
odd-block exits when d=1 mod4. An even v is outside the one-step
merger hypothesis, although the size comparison below still holds.

## Exact size comparison

Set s=r+j and t=R+k. For every positive weight satisfying the
coordinate equations, U<N if and only if the following table applies:

| s | Permitted t for U<N |
|---|---|
| 5 or 6 | 14 through 19 |
| 7 or 8 | 14 through 18 |
| 9 or 10 | 14 through 17 |
| 11 | 14 through 16 |
| 12 or 13 | 14 through 15 |
| 14 or 15 | 14 |

In every other case with s>=5 and t>=14, N<U strictly. There is
no equality case. These are 39 pairs (s,t), corresponding to 392
quadruples (R,r,j,k) under the original lower bounds. The theorem
quantifies over all admissible positive weights, not just the replay
samples.

For a positive odd v inside the region, (2) and U<N exclude N as
a least positive counterexample. At every fixed parameter quadruple
in the table, such weights exist beyond every bound. The proof uses
the previous general residue lift with v=1 modulo 2, then transports
a larger pure exponent L to the weight w=9^(L-R).

This does not produce pure-source exclusions. If w=1, r>=5 and
u>0, then

    9^R+7=2^(57+11r)*u >= 2^112.

The kernel checks `9^35+7<2^112`, hence R>=36. Such a source lies
outside the table, so its U is always larger than N.

## Why the boundary is uniform in the weight

Write

    D=2^(57+11r), E=2^(9+11j), T=2^(3k+4),
    L=D*E*T=2^(70+11(r+j)+3k),
    M=3^(43+7(r+j)+2k),
    P=7M+9^(k+1)*D*(3^(6+7j)-E).

The coordinate equations give the exact natural-number identity

    L*d=M*9^R*w+P.                                       (3)

All subtractions have the required bounds. For r>=5,

    D<=3*3^(35+7r),       P<=10M.

The two coefficients relevant to comparison with 4*8^R*w are

    A(s,t)=3^(43+7s+2t),   B(s,t)=2^(72+11s+3t).

An axiom-free finite kernel calculation proves `1000A<=993B`
inside the table and `B<=A` outside it on the bounded grid, together
with the two outside boundary points (16,14) and (5,20).
The inequalities 2^11<=3^7 and 2^3<=3^2 transport the outside
comparison to all larger parameters.

Inside the table, X>=10000 bounds the padding in (3) by
`1000P<=M*X`. It follows that `1000d<=3976*8^R*w`.
Since 8^R*w>=512, the gap also absorbs the offsets in U=d-2 and
N=4*8^R*w-5. Outside the table, (3) directly gives
`d>=4*8^R*w`, hence N<U. These bounds prove the exact comparison
without an asymptotic approximation or a weight threshold.

## The inverse certificate

Use O=(3n+1)/2 at an odd input and E=n/2 at an even input.
`Backtrack e o B p` means that p reaches B by a legal shortcut word
with e even-input steps and o odd-input steps. Its ordinary clock
is e+2o. The compulsory halving in each O is not counted in e.

For the target `B=3^K*v-2`, inverse arithmetic can be tracked by an
offset m. Start at (e,o,m)=(0,0,2). The reference transitions are

    E inverse: (e,o,m) -> (e+1,o,2m),
    O inverse: (e,o,m) -> (e,o+1,(2m+1)/3),
               allowed when 3 divides 2m+1.

The kernel checks a list of 683 states, closed under all allowed
transitions with e<=14. Every listed state satisfies

    o<14,    m>=2,
    m+3^14 <= 2+2^(e+o)*3^(14-o).                        (4)

The generic certificate-lift theorem proves that, for K>=14, every
actual inverse path with e<=14 corresponds to one of these states,
with the exact relation

    p+m=2^(e+o)*3^(K-o)*v.                               (5)

No odd-count or total-depth bound is assumed on the actual path;
the certificate supplies o<=13. Multiplying (4) by
`3^(K-14)*v>=1` and using (5) gives B<=p. The empty path attains B,
so the inverse minimum under this budget is exactly B.

Apply this with K=2(k+1), B=U=d-2. For k>=6 and any positive v,
all predecessors with e<=14 are at least U. Also R+k>=20, so
U>N under the source hypotheses. None of those paths gives a
smaller original source.

This does not cover other inverse branches into 3d-5, later targets,
or paths with a larger even-input budget. In particular, the earlier
successful final exit can still merge N with the smaller source S
while this obstruction holds at U. A bounded obstruction is not a
counterexample to Collatz or a proof of permanent separation.

## Verification

The [verifier](../verify_minimum_five_predecessor.py) authenticates the
[previous manifest](../results/minimum-five-odd-exit/verification.json)
and builds the new module freshly with Lean 4.33.1. It audits all
root dependencies and the absence of unproved declarations or native
reduction. Dependency reuse authenticates compiler, source, log and
object before copying imports into an isolated directory.

Independent Python checks reconstruct the certificate graph and
compare it with the Lean table. Complete actual inverse trees are
enumerated without an imposed odd-count cap, compared with (5), and
replayed forward. These include even and odd units; the inverse
minimum itself does not require v odd.

Full weighted N/U paths check every parameter quadruple in the
smaller-source region with two weights, plus outside and large cases.
The shortcut replay adds one shared halving to (1) and (2), ending at
(3d-5)/2. Pure lifts are checked with modular powers only. Larger
weighted examples check the three transition tails and the immediate
merger without replaying the initial growing prefix or enumerating
their inverse trees. Exact parameters and counts appear in the
[replay](../results/minimum-five-predecessor/replay.json) and
[verification manifest](../results/minimum-five-predecessor/verification.json).

```sh
python3 verify_minimum_five_predecessor.py --threads 16
# Optional authenticated dependency reuse:
python3 verify_minimum_five_predecessor.py \
  --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 \
  --cache /tmp/collatz-locality-dev
```

A smaller-source argument covering the remaining exits, unrestricted
inverse budgets, full family convergence and the positive-integer
Collatz conjecture remain open.
