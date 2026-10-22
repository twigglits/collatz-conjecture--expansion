# Finite inverse budgets at the first residue 20 visit

For every fixed inverse even budget r>=1, there are arbitrarily large
positive starts whose first visit to 20 modulo 27 has inverse minimum
equal to the starting value. This also holds on an explicit progression
of the return-ladder sources `N=8^R-5`, at their first target `b_1`.
Thus increasing a fixed budget cannot guarantee a smaller predecessor
at this first visit, even after excluding any finite set of sources.

The [Lean module](../lean/MinimumInverseLocality.lean) has 26 audited
kernel roots, including an axiom-free finite certificate. The general
inverse-tree transfer, the exact minima, the first-visit statements,
and the unbounded return-ladder family are kernel proofs. No external
mathematical premise or native reduction axiom enters this chain.
**The positive-integer Collatz conjecture remains unresolved.**

## Inverse words and a uniform bound on odd operations

Use the shortcut map U, with `(3n+1)/2` on odd inputs and `n/2` on
even inputs. The [return-ladder relation](MINIMUM-RETURN-LADDER.md)
`Backtrack(e,o,b,p)` includes every legal inverse word with e even
and o odd operations. Its ordinary semantics are

    C^(e+2o)(p)=b.

Write M_r(b) for the minimum over all such positive p with e<=r.
There is no imposed odd-count cutoff. The formal exact-minimum theorems
give both an attaining path and a lower bound for every permitted word.
This is a predecessor minimum at b, distinct from the minimum of b's
future orbit.

For any path from a positive b the kernel proves p>0 and

    3^o*(p+1) <= 2^(e+o)*(b+1).                         (1)

An odd inverse sends x+1 to `2(x+1)/3`; an even inverse sends x+1
to `2x+1<=2(x+1)`. These two inequalities prove (1) by induction.
If `b+1<=2^d`, they also give

    o < 2*(e+d).                                       (2)

Indeed, if `o=2s+t` with `s=e+d` and t>=0, then
`3^o=9^s*3^t>=8^s*2^t=2^(s+o)`. But (1) and p>=1 give
`2*3^o<=2^(s+o)`, a contradiction. The budgeted inverse tree is
therefore finite without assuming convergence of any forward orbit.

## Exact transfer between ternary congruence classes

Fix b>0, `b+1<=2^d`, an even budget r, and `K>=2*(r+d)`.
For any q>=0 set `B=b+3^K*q`. Every path with e<=r from B has
a corresponding path from b, with the same operation counts and

    P = p + 2^(e+o)*3^(K-o)*q,        o<K.              (3)

This is a kernel induction on the complete Backtrack relation.
At each recovered reference prefix, (2) ensures that its odd count
is still below K. The difference in (3) is consequently divisible
by three before an odd inverse, so the reference path has the same
guard. The proof does not assume that the larger target already
satisfies the reference odd-count bound.

Conversely, every reference path with o<=K lifts by (3). Together
these results preserve the entire tree of legal words within the
even budget. Positivity of the reference target and q>=0 matter;
this is an upward congruence transfer, not an assertion about every
integer or an infinite inverse budget.

## The exact anchor at 857

Every positive ordinary predecessor of 857 which is at most 507 is
507 itself, and its hitting clock is exactly seven. The proof uses
a finite checker with a kernel soundness theorem:

- All starts 1 through 506 avoid 857 for 200 steps and end in
  the closed cycle {1,2,4}.
- The path from `C^8(507)` also avoids 857 until that cycle.
- Among clocks zero through seven, 507 hits 857 only at seven.

The certificate is reduced in Lean's kernel. No finite native-compute
axiom is used. The closed-cycle argument extends finite avoidance to
all times. In particular, M_r(857)=507 for every r>=1, and 507 is
also the minimum over unrestricted inverse words. It reaches 1 at
clock 35; this anchor is not an exceptional or divergent source.

A second kernel consequence controls the multiplier of every inverse
word ending at 857:

    27*2^(e+o) >= 16*3^o.                              (4)

If its multiplier were smaller than 16/27, (1) would give
`p+1 < 858*16/27`, hence p<=507. The unique-hit theorem would then
force p=507 and `e+2o=7`. The four nonnegative count pairs at this
clock all have multiplier at least 16/27, a contradiction.
The attaining inverse word is OEOO, with one even and three odd
operations.

## An unbounded family at ordinary clock seven

For r>=1 and q>=0 put

    K = 2*(r+10),
    n = 507 + 16*3^(K-3)*q,
    b = 857 + 3^K*q.                                  (5)

Here `858<=2^10`, so the transfer theorem applies to the anchor.
For every word with e<=r, the reference predecessor is at least
507 and its multiplier is at least 16/27. Equation (3) therefore
gives P>=n. The word OEOO attains n, proving in the kernel

    M_r(b)=n.                                         (6)

Writing `v=3^(K-3)*q`, the complete ordinary prefix is

    507+16v -> 1522+48v -> 761+24v -> 2284+72v
      -> 1142+36v -> 571+18v -> 1714+54v -> 857+27v.

Its minimum is n. Since 27 divides v, the residues modulo 27 are
21,10,5,16,8,4,13,20. Thus b is the first residue-20 visit, at
clock seven. These statements and unboundedness in q are kernel
theorems. Increasing r changes the progression; no fixed source is
claimed to defeat every inverse budget by this construction.

## Return-ladder sources with the same obstruction

For the precision K in (5), define

    R = 3 + 2*3^K*h,       N=8^R-5,       h>=0.         (7)

The preceding negative-cycle module proves
`3^(K+2) | 8^(3^K)+1`. Squaring and taking positive integer powers
gives the new kernel identity

    8^(2*3^K*h) = 1 + 3^K*z                            (8)

for some z>=0. Substitution gives

    N   = 507 + 512*3^K*z,
    b_1 = 857 + 864*3^K*z.

These are exactly (5) with q=864z. The kernel proves R>=3, R odd,
`h<N`, and

    M_r(b_1)=N,
    C^7(N)=b_1,
    C^t(N)=20 mod27 for 0<=t<=7 iff t=7.                (9)

Equivalently, for every extra budget s>=0 and every source bound B,
there is an odd R>=3 with N>B and `M_(1+s)(b_1)=N`.
This rules out a uniform extra budget that works at every ladder
target. It also rules out a uniform budget specifically at the first
visit after removing any finite collection of sources. It does **not**
rule out a fixed extra budget that succeeds at some suitably chosen
later visit for each source; that different quantifier remains open.

The h=0 source is 507. Already at r=1,h=1, R is 62,762,119,221
and N has 188,286,357,663 binary digits. Such ladder sources are
handled symbolically in Lean and modularly in Python. The smaller
arithmetic-progression examples in (5) are separate and can be
materialized.

## Verification and the remaining route

Run

    python3 verify_minimum_inverse_locality.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_inverse_locality.py) authenticates all
64 hashes in the preceding negative-cycle manifest, then freshly builds
31 Lean modules in dependency order. Each Lean process may use the
requested number of threads. The 26 new theorem roots are audited for
axiom dependencies, and the finite anchor must be axiom-free.

Independent Python checks cover the 506 smaller anchor starts, complete
anchor trees through even budget 20, and general locality for all
reference targets 1 through 128 with budgets zero through six and two
positive lifts each. Complete optimization of (5) covers budgets one
through sixteen with q=0,1,2,17. Actual seven-step first-target prefixes
cover budgets one through 64 with q=0 through 31. The period identities
have separate materialized and modular checks; the enormous sources
in (7) are not numerically iterated.

Exact counts, commands, compiler identity, timings and hashes are in the
[manifest](../results/minimum-inverse-locality/verification.json) and
[replay](../results/minimum-inverse-locality/replay.json). Historical
verification records are preserved.

A contradiction using smaller predecessors must control a useful
later visit, allow a budget that depends on the source or visit, or
provide additional restrictions on a least counterexample. The present
obstruction concerns the first visit and finite inverse budgets. It
does not settle those later-visit alternatives, the cap/residual
estimates, or the exclusion of nontrivial cycles and divergent orbits.
