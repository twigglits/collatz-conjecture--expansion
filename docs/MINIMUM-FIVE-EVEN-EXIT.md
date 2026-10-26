# Later mergers in the third endpoint branch with d equal to 3 modulo 4

There are arbitrarily large pure sources in the current coordinate
family whose known smaller partner merges with them in the previously
untreated `d=3 mod4` branch. The merger follows a contracting pair of
adjacent values and a favorable odd-block exit. It is compatible with
the [earlier inverse obstruction](MINIMUM-FIVE-INVERSE-CONE.md): all
predecessors within that budget at the earlier endpoint can be larger
than the original source, while a smaller source meets it later.

The [Lean module](../lean/MinimumFiveEvenExit.lean) contains twenty-two
audited kernel roots. They prove the merger, unbounded realizations,
the complementary residual pairs and a complete split of `d>3,d=3mod4`
according to the parity of the binary valuation of d-3. This is a
least-counterexample exclusion for specified infinite families, not
convergence of the entire family. Collatz remains unresolved.

## A contracting adjacent pair

For every q>=0, three ordinary Collatz steps give

    4q+2 -> 2q+1 -> 6q+4 -> 3q+2,
    4q+1 -> 12q+4 -> 6q+2 -> 3q+1.

Thus the two values remain adjacent while the variable part contracts
by 3/4. Iterating gives the universal identities

    C^(3t)(4^t*q+2) = 3^t*q+2,
    C^(3t)(4^t*q+1) = 3^t*q+1.                         (1)

These include t=0 and q=0. For the new exit family, take t>=1 and
positive odd z, and impose

    d = 3 + 2*4^t*z,
    1 + 3^t*z = 2^l*y,       l>=1, y positive odd.      (2)

The first equation gives `d=3 mod8`, hence a branch disjoint from
the earlier [odd exit](MINIMUM-FIVE-ODD-EXIT.md), which required
`d=1 mod4`. After the initial one-step and three-step bridges,
formula (1) gives

    C^(1+3t)(3d-5) = 2+3^(t+1)*z = 2^l*(3y)-1,
    C^(3+3t)(2d-5) = 1+3^(t+1)*z = 2^l*(3y)-2.         (3)

The two values in (3) are adjacent, with the upper value odd.

## Favorable and opposite exits

If `3^(l+1)*y=1 mod4`, the existing adjacent odd-block theorem
merges the pair in another `2l+2` ordinary steps. Consequently

    C^(3t+2l+5)(2d-5) = C^(3t+2l+3)(3d-5).              (4)

The common value is `(3^(l+1)*y-1)/4`, as checked in the independent
replay. Equation (4) is the audited kernel merger; it does not assert
that this is the earliest meeting.

If `3^(l+1)*y=3 mod4`, write `3^l*y=4h+1`. The kernel instead
proves

    C^(3t+2l+4)(3d-5) = 9h+2,
    C^(3t+2l+4)(2d-5) = h.                              (5)

This is a residual pair, not a merger. Exact odd factorization of
`1+3^t*z` yields (2) and one of these two alternatives for every
positive odd z. Elementary arithmetic gives h>0 and h=2 modulo 3,
so `9h+2=20 mod27`, returning to the earlier unresolved target class.

## Full sources and exclusion of leastness

Keep R>=14, r>=5 and the earlier positive coordinates:

    X=9^R*w,                 X+7=2^(57+11r)*u,
    a=3^(33+7r)*u,           9a+1=2^(9+11j)*q,
    b=3^(6+7j)*q,            b=1+2^(3k+4)*v,
    d=9^(k+1)*v,
    N=4*8^R*w-5,            S=2^(2R+13)*w-1.

The existing source bounds give `0<S<N`. The ordinary clocks to
the third endpoints are

    C^(5R+116+18r+18j+5k)(N) = 3d-5,
    C^(4R+125+18r+18j+5k)(S) = 2d-5.

Combining them with the favorable exit proves

    C^(4R+130+18r+18j+5k+3t+2l)(S)
      = C^(5R+119+18r+18j+5k+3t+2l)(N).                (6)

Since S is positive and smaller, (6) excludes N as a least positive
counterexample. It does not require S to occur on N's forward path.
No convergence premise is used in proving the meeting itself.

For the opposite exit, the full source clocks are respectively
`5R+120+18r+18j+5k+3t+2l` for N reaching 9h+2 and
`4R+129+18r+18j+5k+3t+2l` for S reaching h.

## Unbounded realizations of both exits

For every r,j,k, every prescribed t>=1,l>=1, either g=1 or g=3,
and every bound B, the kernel constructs a pure exponent R>B,
R>=14, with positive u,q,v,z,y satisfying all coordinates, (2),
z and y odd, and

    3^(l+1)*y = g mod4.

For each fixed initial R it also constructs weights w>B with the
same properties. The lifts permit any r; the least-source exclusion
uses r>=5 and R>=14. Thus favorable exits give unbounded pure and
weighted exclusions, while the opposite residue also survives at
arbitrarily large parameters.

The residue construction is explicit. Choose odd y0<4 with
`3^(l+1)*y0=g mod4`. Let `V=2^(l+2)` and choose the positive odd
residue z0<V satisfying

    3^t*z0 = 2^l*y0-1 mod V.

Set `A=2*4^t`, `M=A*V=2^(2t+l+3)` and `target=3+A*z0<M`.
Invert the odd coefficient `9^(k+1)` modulo M, then apply the
existing pure residue lift to obtain `d=target mod M`. Recover

    z = V*floor(d/M)+z0,
    y = 4*floor((1+3^t*z)/V)+y0.

These identities prove the exact equations and both odd unit
conditions. Fixed-R weights come from a larger pure exponent L
by setting `w=9^(L-R)`.

The equations also give the five exact binary valuations of X+7,
9a+1, b-1, d-3 and 1+3^t*z: respectively
`57+11r`, `9+11j`, `3k+4`, `2t+1` and l. The first three unit
parities follow from the coordinate equations; the last two are
explicit in the new realization theorem. The independent replay
checks all five.

Both earlier separated windows remain valid for either g whenever
`H+13<=9+11j` and `H+6<=3k+4`. In particular, setting j=k=H+1
allows any prescribed window horizon. These are the named earlier
clock windows, not all-time separation.

## A later merger despite the earlier obstruction

The earlier half endpoint is particularly simple in (2):

    H0=(3d-5)/2=2+3*4^t*z.

For R>=26, every predecessor of H0 with at most k even-input
shortcut steps is strictly larger than N, by the preceding inverse
theorem. The new `pure_later_escape` root simultaneously supplies,
beyond every exponent bound, a pure R>=36 with this obstruction and
the later smaller-source meeting (6).

This gives an unbounded family where that earlier search cannot
find a smaller source within its budget, although a later coalescence
does exclude leastness. It does not determine the unrestricted inverse
minimum at H0 or show that S reaches H0.

## The remaining even valuation

Every d>3 with d=3 modulo 4 has exactly one of the two forms obtained
from odd factorization of d-3:

    odd valuation:  d=3+2*4^t*z,  t>=1, z positive odd;
    even valuation: d=3+4^(t+1)*q, t>=0, q positive odd.

The kernel proves this exhaustive split. The first form is treated
by (3)--(5). For the second, put `2u=1+3^(t+1)*q`. After t paired
contractions the adjacent values are 4u and 4u-1. Two halvings of
the upper value and two odd shortcut steps of the lower value give
the kernel identities

    C^(3t+3)(3d-5)=u,
    C^(3t+7)(2d-5)=9u-1.                                (7)

Equation (7) identifies another unresolved pair. Neither (5) nor
(7) establishes a merger. These pairs, later targets and unrestricted
least-counterexample exclusion remain open.

## Verification

The [verifier](../verify_minimum_five_even_exit.py) authenticates the
previous manifest and builds the new module freshly with Lean 4.33.1.
All twenty-two roots use only standard logical axioms; none is
axiom-free. No native reduction, new mathematical axiom or external
mathematical premise is used. Optional dependency reuse checks the
compiler, sources, logs and objects before copying imports into an
isolated directory. Without a cache, all 47 builds run sequentially.

Independent checks replay generic paired contractions, both local
exits and the even-valuation residual. Complete weighted N/S paths
include the initial growing prefixes and all recorded checkpoints.
The earlier windows and inverse trees at H0 are checked separately;
those trees use the recorded budget `min(k,8)`, not always the full k.

Pure lifts use modular exponentiation only. Their enormous starting
values and trajectories are not materialized. The universal pure
claim is the kernel theorem, not an extrapolation from weighted
samples. Exact finite parameters and counts appear in the
[replay](../results/minimum-five-even-exit/replay.json) and
[verification record](../results/minimum-five-even-exit/verification.json).

```sh
python3 verify_minimum_five_even_exit.py --threads 16
# Optional authenticated dependency reuse:
python3 verify_minimum_five_even_exit.py \
  --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 \
  --cache /tmp/collatz-locality-dev
```
