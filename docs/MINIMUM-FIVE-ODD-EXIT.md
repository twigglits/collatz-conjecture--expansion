# Variable odd block exits after the negative five transition

An arbitrarily long odd block now replaces the final condition
`d=5 mod16` from the [negative-five transition](MINIMUM-FIVE-TRANSITION.md).
One exit merges with the existing smaller fourth source and excludes
the main source as least. The opposite exit reaches a precise residual
pair, `9h+2,h`; a related merger uses a companion provably larger than
the main source. Both exits have unbounded pure and weighted realizations.

The [Lean module](../lean/MinimumFiveOddExit.lean) contains twenty kernel
theorems. The positive-integer Collatz conjecture remains unresolved.
The complementary residual pair is not a universal merger or descent.

## Coordinates and the successful exit

Use ordinary Collatz steps C, with odd step 3n+1 and even step n/2.
Keep the previous coordinates, with R>=14, r>=5 and w,u,q,v positive:

    X=9^R*w,                 X+7=2^(57+11r)*u,
    a=3^(33+7r)*u,           9a+1=2^(9+11j)*q,
    b=3^(6+7j)*q,            b=1+2^(3k+4)*v,
    d=9^(k+1)*v.

The original sources are

    N=4*8^R*w-5,             S=2^(2R+13)*w-1,
    P=2^(2R+5)*w-1,          Q=2^(2R+15)*w-1.

Here 0<P<S<Q<N. The earlier transition proves

| Source | Ordinary clock | Endpoint |
|---|---:|---:|
| N | 5R+116+18r+18j+5k | 3d-5 |
| S | 4R+125+18r+18j+5k | 2d-5 |

Suppose now that l>=1, z>0 and

    d=1+2^(l+1)*z,           3^(l+1)*z=1 modulo 4.       (1)

Set A=2^l*(3z)-1. Two short bridges give

    C(3d-5)=A,              C^3(2d-5)=A-1.

The existing adjacent odd-block theorem merges A-1 and A after
2l+2 steps. Consequently

    C^(2l+5)(2d-5)=C^(2l+3)(3d-5),                      (2)
    C^(4R+130+18r+18j+5k+2l)(S)
      =C^(5R+119+18r+18j+5k+2l)(N).                    (3)

Since S is positive and smaller than N, (3) excludes N as a least
positive counterexample. The statement does not assume convergence
of every S or identify the earliest meeting. At l=1, condition (1)
is the earlier d=5 mod16 condition; these clocks include one extra
shared halving relative to that earlier kernel meeting.

In shortcut notation, O=(3n+1)/2 at an odd input and E=n/2 at an
even input. The two final words are

    N: E O^l EE,             S: OEE O^(l-1) EO.

Their common value is `(3^(l+1)*z-1)/4`.

## The complementary exit and its larger companion

For the opposite condition

    d=1+2^(l+1)*z,           3^(l+1)*z=3 modulo 4,       (4)

the companion T=3d-4=2A+1 merges with the N endpoint:

    C^(2l+4)(T)=C^(2l+4)(3d-5),
    C^(2l+4)(T)=C^(5R+120+18r+18j+5k+2l)(N).           (5)

However T>N throughout the stated coordinate family. This is a
kernel inequality, not a numerical observation. The proof uses

    5*2^(167+11s+3t) <= 3^(107+7s+2t),    s,t>=0,

from the base inequality `5*2^167<=3^107` and the comparisons
`2^11<=3^7`, `2^3<=3^2`. With s=r-5+j and t=R-14+k, the coordinate
equations give `5*8^R*w<=3d`, hence `N<3d-4`. Thus (5) supplies
no smaller-source contradiction.

The opposite branch has a more useful exact description. Write

    3^l*z=4h+1.

Then both third endpoints have profiles at the same local clock:

    C^(2l+4)(3d-5)=9h+2,
    C^(2l+4)(2d-5)=h.                                   (6)

For positive odd z and l>=1 under (4), h is positive and h=2 mod3.
The shortcut words are `E O^l EO` and `OEE O^(l-1) EE`.
The larger companion uses `O^(l+1) EE` and ends at 9h+2.
No merger between 9h+2 and h is asserted.

Algebraically, h=2 mod3 puts 9h+2 back in the critical class
20 modulo 27 studied in the [first-target note](MINIMUM-FIRST-TARGET.md).
Also `4*(9h+2)+1=3^(l+2)*z`. Thus the unresolved exit returns to an
earlier target class with explicit ternary divisibility; it does not
leave that class behind. This observation follows from (6) and is a
written arithmetic consequence, not an additional audited theorem.

Exact odd factorization shows that every d>1 with d=1 mod4 has
one of the alternatives (1) or (4), at some l>=1 and positive odd z.
Therefore a least N in these coordinates must take (4).
The d=3 mod4 class is outside this particular dichotomy.

## Unbounded realizations of both residues

For every r,j,k,l and either g=1 or g=3, pure exponents R beyond
every bound admit positive u,q,v,z satisfying all four coordinate
equations, with z odd and `3^(l+1)*z=g mod4`. At each fixed initial
R, weights beyond every bound also do so. The lift allows any r;
using the fourth-source merger requires r>=5 and R>=14.

The reusable `pure_residue_lift` first constructs v in any prescribed
nonzero residue eps modulo V=2^(h+1), where 0<eps<V. Put

    D=2^(57+11r), E=2^(9+11j), T0=2^(3k+4),
    A0=3^(35+7r), c=3^(6+7j),
    F=7cA0+D(c-E)+(V-eps)*D*E*T0.

Here c>=E and cA0 is odd. The affine exponent lift at index
`(57+11r)+(9+11j)+3k+h+2` gives

    cA0*9^R+F=V*D*E*T0*Q,    Q>0.

Taking v=V*(Q-1)+eps and canceling the padding recovers the earlier
three coordinate equations. Odd factors can be canceled modulo
powers of two. All expressions used with natural subtraction have
the needed bounds.

To obtain the fourth coordinate, set V=2^(l+3). Choose odd z0<4
with `3^(l+1)*z0=g mod4`, and choose odd eps<V with

    9^(k+1)*eps = 1+2^(l+1)*z0 modulo V.

The kernel binary inverse theorem gives both choices. The resulting
d has the required form with `z=4*(d/V)+z0`. This proves both exits
have unbounded realizations; the opposite residue cannot be removed
by claiming the coordinate system makes it impossible.

All four quotients u,q,v,z are odd. Thus the exact binary valuations
of X+7, 9a+1, b-1 and d-1 are respectively

    57+11r,                 9+11j,                 3k+4,                 l+1.

## Earlier separated windows

Either residue retains both earlier window statements whenever

    H+13<=9+11j,            H+6<=3k+4.

The four primary windows through H separate N from P,Q,S; the two
secondary windows through H separate N from S. These are cross-time
inequalities inside the specified windows. They are not all-time
noncoalescence statements.

`OddEscape` bundles a successful realization, both windows, the
least-source exclusion and the explicit later meeting. The pure and
weighted escape theorems allow any l>=1 and any j,k satisfying the
horizon inequalities. Choosing j=k=H+1 works for every H and l.

## Verification and scope

The [verifier](../verify_minimum_five_odd_exit.py) authenticates the
[previous manifest](../results/minimum-five-transition/verification.json),
builds the new module freshly with Lean 4.33.1 and audits all twenty
root dependencies. Only the standard logical axioms propext,
Classical.choice and Quot.sound occur; no root is axiom-free. No
native reduction, new mathematical axiom or external premise is used.
The base growth comparison is a kernel computation.

Independent Python checks distinguish generic profiles, full weighted
paths, modular-only pure lifts and larger tail-only examples. Both
residues have complete N,S replays, primary P,Q prefixes, shortcut
and inverse checks, and every applicable earlier separated window.
The opposite branch also replays its larger companion and verifies
both values in (6). Pure starts with enormous exponents are never
materialized; larger prefix cases only replay the stated tails.
Exact counts and parameters are recorded in the
[replay](../results/minimum-five-odd-exit/replay.json) and
[verification manifest](../results/minimum-five-odd-exit/verification.json).

```sh
python3 verify_minimum_five_odd_exit.py --threads 16
# Optional authenticated dependency reuse:
python3 verify_minimum_five_odd_exit.py \
  --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 \
  --cache /tmp/collatz-locality-dev
```

A smaller original source covering every complementary residue,
a merger for every residual pair, the remaining third-unit classes,
full family convergence and unrestricted Collatz remain open.
