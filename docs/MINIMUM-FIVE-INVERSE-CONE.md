# Inverse bounds that grow with the block parameter

For every pure source in the current three-coordinate family, all
predecessors of the half endpoint `H=(3d-5)/2` with at most k
even-input shortcut steps are strictly larger than the original
source N. This covers both possible first inverse branches. The
budget k is unbounded across the family; each individual instance
still has a bounded budget.

The [Lean module](../lean/MinimumFiveInverseCone.lean) proves this by
induction and algebra. It also determines the exact inverse minimum
at `3d-5` with even budget `k+1`. These extend the
[earlier fixed-budget result](MINIMUM-FIVE-PREDECESSOR.md), which
concerned only `U=d-2` and fourteen even steps. They identify an
obstruction to finding a smaller source at this endpoint. They do
not prove convergence or exclude a smaller source at a later target.
The positive-integer Collatz conjecture remains unresolved.

## Inverse paths and reference offsets

Use the shortcut operations O=(3n+1)/2 at odd inputs and E=n/2 at
even inputs. `Backtrack e o b p` means that p reaches b by a legal
shortcut word with e E operations and o O operations. The ordinary
Collatz clock is `e+2o`; the compulsory halving within O is not
counted in e.

For c equal to 2 or 5, start a reference path at `(e,o,m)=(0,0,c)`
and allow the transitions

    (e,o,m) -> (e+1,o,2m),
    (e,o,m) -> (e,o+1,(2m+1)/3), if 3 divides 2m+1.

These offsets encode negative arithmetic. They are not positive
Collatz trajectories. Induction proves the following invariants,
with `D=2e-o`:

| Initial offset c | Lower bound | Odd-count bound | Potential inequality |
|---|---|---|---|
| 2 | m>=2 | o<=2e | `2^D*(m-1)<=2*3^D` |
| 5 | m>=5 | o<=2e | `2^D*(m-1)<=4*3^D` |

For c=2, the only reference states with m<5 are `(0,0,2)`,
`(1,0,4)` and `(1,1,3)`. This classification is also proved by
induction, rather than inferred from a finite search. For m>=5,
an inverse E preserves the inequality because

    4*(2m-1) <= 9*(m-1).

An inverse O preserves the potential through
`3*(m'-1)=2*(m-1)`. The potential and the allowed residues prevent
an O step when D=0. The three small states handle the exceptions
for initial offset 2.

## Lifting all paths within the even budget

Suppose `b+c=3^K*v`, `e<=B` and `2B<K`. Every actual inverse path
has a reference offset m satisfying the exact identity

    p+m = 2^(e+o)*3^(K-o)*v.                            (1)

No bound on o or on total path length is assumed. At each induction
step the reference invariant supplies `o<=2e<K`, leaving a factor
of three available to force the required offset residue.

Multiplying (1) by `2^(2e-o)` and applying the potential yields

    8^e*3^(K-2e)*v <= p+a+1,

where a=2 for c=2 and a=4 for c=5. Since 8<=9 and e<=B,

    c=2:  8^B*3^(K-2B)*v <= p+3,
    c=5:  8^B*3^(K-2B)*v <= p+5.                        (2)

For c=5 and v>0, the second lower bound is attained. The legal
inverse block EOO takes `9q-5` to `8q-5`. Repeating B blocks gives
the exact minimum

    min {p : Backtrack e o b p, e<=B}
      = 8^B*3^(K-2B)*v-5.                              (3)

The first inequality in (2) is a lower bound, not an exact minimum
for offset 2. These statements use no finite state certificate.

The strict precision condition matters. At B=2, K=4 and v=1,
the target is 76. The path from 39 to 76 has shortcut word
`OOOEOOE`, with e=2 and o=5. Thus `o>2e` and
`39<8^2-5=59`. Lean checks this witness, so replacing `2B<K` by
`2B<=K` would make the asserted general bounds false.

## Both branches at the half endpoint

Retain the coordinates

    X=9^R*w,                 X+7=2^(57+11r)*u,
    a=3^(33+7r)*u,           9a+1=2^(9+11j)*q,
    b=3^(6+7j)*q,            b=1+2^(3k+4)*v,
    d=9^(k+1)*v,             N=4*8^R*w-5.

For positive quotients and odd v, H=(3d-5)/2 is an actual iterate:

    C^(5R+117+18r+18j+5k)(N)=H.                          (4)

At the preceding endpoint `3d-5`, formula (3), with
`K=2k+3` and `B=k+1`, gives the exact inverse minimum

    W=3*8^(k+1)*v-5.                                    (5)

It is attained with `k+1` E operations and `2(k+1)` O operations.
In the coordinates above, `2W+13=3b`; this last rewriting is an
elementary consequence of the displayed definitions, independently
checked in the Python replay.

Every nonempty inverse path from H begins with one of two edges:

    inverse O: H -> U=d-2,
    inverse E: H -> 2H=3d-5.

The kernel proves a general first-edge decomposition for Backtrack.
If the total even budget is at most k, the O branch satisfies the
first bound in (2), giving `p+3>=9*8^k*v`. In the E branch, the
second bound gives `p+5>=27*8^k*v`, which is stronger than the
needed comparison. The empty path satisfies the same lower bound.
Consequently, for every such path,

    Backtrack e o H p, e<=k  =>  9*8^k*v <= p+3.         (6)

This covers complete shortcut paths at H. It does not assume that
the original source reaches H with an even budget at most k.

## Comparison with the original source

For R>=26, r>=5, w>0 and the coordinate equations, Lean proves

    N+3 < 9*8^k*v.                                      (7)

Set z=8^k*v. The third coordinate can be rewritten with block
parameter zero as `b=1+16z`. The earlier scaled-coordinate identity
then has third scalar 9z. The coefficient comparison

    2*2^(72+11s+3t) <= 3^(43+7s+2t),   s>=5, t>=26,

follows from the base case (5,26) and multiplication by
`2^11<=3^7` and `2^3<=3^2`. It gives `8*(8^R*w)<=9z`, which
implies (7), including its additive offsets.

Combining (6) and (7) proves `N<p` for every inverse path at H
with e<=k. Every pure source has w=1 and R>=36 by the earlier
bound `9^35+7<2^112`, so the conclusion covers the entire pure
coordinate family with r>=5 and an integral H.

The exact minimum at H is not determined here. Larger even budgets,
later targets and the residual pair `9h+2,h` remain available
directions. The earlier successful odd-exit merger with a smaller
source takes place later and is compatible with this obstruction.

## Verification

All twenty theorem roots in the module pass fresh Lean 4.33.1
kernel dependency audits. They use only the standard logical axioms
`propext`, `Quot.sound` and, where needed, `Classical.choice`. No
root is axiom-free; there is no native reduction, added axiom or
external mathematical premise.

The [verifier](../verify_minimum_five_inverse_cone.py) authenticates
the preceding manifest and the imported sources. Optional cached
objects are reused only after compiler, source, log and object
hashes match. The new module is always built freshly. Without a
cache, all 46 modules are built sequentially.

The independent Python replay constructs complete reference graphs
through even budget 24, reconstructs actual inverse trees without
an odd-count or depth cap, and compares every state with (1).
It checks the exact offset-five minima and both branches at H.
Each actual inverse state is replayed forward with shortcut steps
and two ordinary-step implementations.

Weighted examples replay the complete N, U and W paths, including
their initial prefixes. Their inverse trees are complete at the
recorded budget `min(k,8)`; larger examples do not enumerate the
full k budget. Pure-family coverage is supplied by the kernel
theorem, not by materializing enormous pure starting values.
Exact finite parameters and counts are in the
[replay](../results/minimum-five-inverse-cone/replay.json) and
[verification record](../results/minimum-five-inverse-cone/verification.json).

```sh
python3 verify_minimum_five_inverse_cone.py --threads 16
# Optional authenticated dependency reuse:
python3 verify_minimum_five_inverse_cone.py \
  --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 \
  --cache /tmp/collatz-locality-dev
```
