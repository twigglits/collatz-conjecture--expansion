# Escaping the return ladder with three extra even steps

The return ladder's bounded inverse obstruction can be crossed. For every
`R=162h+85`, the source `N=8^R-5` has a strictly smaller positive source
that joins its ordinary orbit after 17 steps, at `C^2(N)`. At the later
targets `b_i=C^(5i+2)(N)`, the same predecessor uses exactly `i+3` even
inverse shortcut operations. These are parameterized kernel proofs.

A written classification also proves sharpness: for every odd `R>=3`
and `0<=i<R`, budgets `i+1` and `i+2` still have minimum `N`. At budget
`i+3`, a smaller predecessor exists exactly when `R=85 mod162`. The
classification uses kernel companion bounds and a small finite negative
orbit table; its full assembly is **written**, not a new Lean theorem.

The [Lean module](../lean/MinimumInverseEscape.lean) has 27 audited roots.
Its two finite witness roots are axiom-free. Independent Python checks
are recorded separately. No external theorem is assumed, and no claim
of novelty is made. **The positive-integer Collatz conjecture remains
unresolved.** In particular, excluding a family of possible *least*
counterexamples does not prove that every member of that family converges.

## 1. A general detour and a least-source residue restriction

Let `U(n)=(3n+1)/2` for odd n and `U(n)=n/2` for even n. As in the
[return-ladder analysis](MINIMUM-RETURN-LADDER.md), an even operation
counts an even input of U. The halving paired with an ordinary odd
step is already included in U.

For any odd positive n there is an actual shortcut path

    8n+2 --E--> 4n+1 --O--> 6n+2 --E--> 3n+1 --E--> (3n+1)/2.

Its ordinary length is five, and its endpoint is `C^2(n)`. If

    3^j*q=8n+3,       q>0,       P=2^j*q-1,

then j additional odd shortcut steps from P reach `8n+2`. Thus the
kernel proves both the inverse-word relation and its ordinary semantics:

    Backtrack(3,j+1,C^2(n),P),
    C^(2j+5)(P)=C^2(n).                                     (1)

For `j>=6`, `8*2^j<3^j` gives `0<P<n`. If n were a least positive
counterexample, the smaller P would converge and (1) would force n
to converge as well. Consequently the kernel proves

    LeastCounterexample(n)  ==>  (8n+3) != 0 mod729,
    LeastCounterexample(n)  ==>  n != 273 mod729.            (2)

The reduction in (2) is an ordinary coalescence argument. It does not
identify the two starting values or require their meeting clocks to agree.

## 2. Applying the detour to the repeated target visits

For odd `R>=3`, recall

    X=8^R,       N=X-5,
    x_i=9^i*8^(R-i)-5,
    b_i=(3x_i+1)/2,              0<=i<R.

The earlier kernel result gives `C^(5i+2)(N)=b_i`, with ordinary
prefix minimum N through clock `5R`. The visits to 20 modulo 27 are
exactly the indices `1<=i<R`; `b_0=C^2(N)` is also useful here, but
is not one of those residue-20 visits.

The inverse shortcut word `(O E O)^i` joins `b_i` to `b_0`, using
i even and 2i odd inverses. Appending the detour in (1) gives

    (O E O)^i E E O E O^j,                                  (3)
    Backtrack(i+3,2i+j+1,b_i,P),
    C^(5i+2j+5)(P)=b_i,

where `3^j*q=8^(R+1)-37` and `P=2^j*q-1`. The general first part
of (3) is obtained by composing the kernel roots `hit_to_initial`
and `detour_predecessor`; the specialized j=6 family below has its
own explicit kernel theorem.

Two axiom-free modular calculations give

    8^162=1 mod729,       8^86=37 mod729.

For `R=162h+85`, define

    q_h=(8^(R+1)-37)/729,       P_h=64q_h-1.

The kernel proves integrality and positivity of q_h, `0<P_h<N`, and

    C^17(P_h)=C^2(N),
    Backtrack(i+3,2i+7,b_i,P_h),
    C^(5i+17)(P_h)=b_i                 for every i<R.        (4)

It follows that no such N is a least counterexample. The kernel also
proves `h<N`, so this is an unbounded family of distinct source sizes.
Universal convergence of the family remains unproved.

## 3. Kernel bounds up to the first escape

Write `L=2i+1`. In the previous proof the negative magnitude companion
was controlled under the assumption `e<=i`. The new root
`truncated_companion` removes that restriction, retaining instead
`o<=L`. For every actual inverse word with those counts, it produces
an integer m satisfying

    Shadow(e,o,m),       5<=m<=7*2^e,       o<=2e+1,
    2^(2e+1-o)*(m-1) <= 4*3^(2e+1-o),
    3^o*(p+m)=2^(e+o)*(b_i+7).                              (5)

The Shadow relation starts at magnitude 7 and uses `m -> 2m` for E,
and `m -> (2m+1)/3` for O when integral. The factor `3^L` in `b_i+7`
ensures that every positive odd inverse before the boundary has an
integral companion. No integrality is assumed after the boundary.

The kernel further proves

    o<=L  ==>  p>=N,
    p<N   ==>  o>L.                                         (6)

For `e<=i`, the earlier inverse-ladder lower bound proves (6). For
`e>i`, cancellation in (5) and `3^(L-o)>=2^(L-o)` give

    p+m >= 2^(e-i)*X.

Since `R>=3` and `i<R`, `14*2^i<=X`. Combining this with
`m<=7*2^e` yields `2m<=2^(e-i)*X`, hence `2p>=2^(e-i)*X>=2X`.
In particular `p>=X>N`. These inequalities are included in the
kernel root `before_escape_lower`.

Any improving path must therefore have a prefix just before its
`(L+1)`st odd inverse. At that prefix `o=L`, put `e=i+f`. The
kernel frontier theorem gives

    Shadow(i+f,L,m),       5<=m,
    4^f*(m-1)<=4*9^f,       p+m=2^f*X.                    (7)

The count inequality in (5) ensures `f>=0`. With at most `i+3`
even inverses, only `f=0,1,2,3` can occur.

## 4. Written classification of the four possible frontiers

The kernel connects Shadow to the deterministic magnitude map

    S(m)=(3m-1)/2 for odd m,       S(m)=m/2 for even m.

Specifically, `S^(e+o)(m)=7`, and that path has o odd inputs. The
kernel also checks the cycles at 1, 7 and 17, including the absence
of 7 from the 17-cycle and the first return time three at 7:

    7 -> 10 -> 5 -> 7,
    17 -> 25 -> 37 -> 55 -> 82 -> 41 -> 61 -> 91
       -> 136 -> 68 -> 34 -> 17.

The bound in (7) limits m to at most 46. For each integer from 5
through 46, iterate S until its first visit to 7 or a repeated state.
If it first reaches 7 with e_0 even and o_0 odd inputs, put
`d_0=2e_0+1-o_0`. Further returns to 7 add one even and two odd
inputs, so d_0 is unchanged. Thus `Shadow(i+f,L,m)` requires
`d_0=2f`. An orbit entering the 1- or 17-cycle cannot reach 7.
The complete table is:

| First-hit d_0 or terminal cycle | Starting magnitudes m |
|---|---|
| 0 | 5 |
| 1 | 7 |
| 2 | 9, 10 |
| 3 | 13, 14 |
| 4 | 18, 19, 20 |
| 5 | 26, 27, 28 |
| 6 | 35, 36, 38, 40 |
| Cycle 1 | 6, 8, 11, 12, 15, 16, 22, 24, 29, 30, 32, 39, 43, 44 |
| Cycle 17 | 17, 21, 23, 25, 31, 33, 34, 37, 41, 42, 45, 46 |

Each first path and its two operation counts are retained in the
independent [replay](../results/minimum-inverse-escape/replay.json).
This finite enumeration and the argument extending it to arbitrary
path lengths are a written proof. They are not silently included in
the kernel theorem count.

Combining the table with (7) gives the following necessary candidates.
Some need more odd operations than are available at very small i;
including them only weakens the lower-bound analysis.

| f | Upper bound on m | Possible m | m permitting the next positive odd inverse |
|---:|---:|---|---|
| 0 | 5 | 5 | None |
| 1 | 10 | 9, 10 | None |
| 2 | 21 | 18, 19, 20 | 18 |
| 3 | 46 | 35, 36, 38, 40 | 35, 38 |

Here `X=8^R=-1 mod9`, because R is odd. An odd inverse at the
frontier `p=2^f*X-m` is legal exactly when `p=2 mod3`.

At `f=2,m=18`, the next predecessor is `(8X-37)/3`. It is larger
than N and divisible by three: `8X-37=0 mod9`. Every subsequent
inverse operation is consequently a doubling. Even if one unit of
even budget remains, this branch never improves on N.

At `f=3,m=35`, the next predecessor is `(16X-71)/3>N`. It is
1 modulo 3, so it has no further odd inverse. There is no even
budget left. This branch also fails to improve.

At `f=3,m=38`, put

    j=v3(8X-37),       Q=(8X-37)/3^j,       P_j=2^j*Q-1.    (8)

Here `j>=2`. With no even budget left, the pure odd inverse chain
has exactly j steps and its smallest value is P_j. The word (3)
attains this branch for every i, with frontier `p=8X-38,m=38`.

Every path below N must cross one of these frontiers by (6), and
every case has now been considered. Since the old path also attains
N with i even inverses, the complete written minimum is

    M_(i+s)(b_i)=N,                          s=0,1,2,
    M_(i+3)(b_i)=min(N,P_j),                 j as in (8).    (9)

The minimum is over all finite legal inverse words with *at most*
the indicated even budget. There is no imposed odd-count cutoff.

If `j>=6`, (1) proves `P_j<N`. Conversely, if `j<=5`, then

    P_j+1 >= (32/243)*(8X-37),
    P_j-N >= (13X-212)/243 > 0,

using `X>=512`. Thus improvement in (9) is equivalent to `j>=6`.
Together with `8^162=1 mod729`, direct enumeration of all 162
exponent residues shows

    j>=6  iff  8^(R+1)=37 mod729  iff  R=85 mod162.         (10)

The finite residue enumeration in the last equivalence is independently
replayed; the full equivalence is written. Equations (9)--(10) show
that **three extra even steps are necessary and sufficient** on this
progression. For other odd R, no smaller predecessor uses at most
`i+3` even steps. Larger budgets are outside this classification.

## 5. Concrete convergent witnesses and remaining work

For `R=85`, both N and P_6 have 255 bits:

    N   = 57896044618658097711785492504343953926634992332820282019728792003956564819963
    P_6 = 40662242585394987693325339042831418944358183915506151432237505495234240312511

The kernel checks `C^17(P_6)=C^2(N)` and `C^22(P_6)=b_1`. It
separately checks arrivals at one at ordinary clocks 2,119 and 2,134.
The smaller example `P=5311<n=7563` also coalesces at clocks 17 and
2, and reaches one at clocks 98 and 83, respectively. Python checks
that these four arrival clocks are the first ones.

For R=247 the valuation in (8) is seven, so the full odd chain
gives a smaller predecessor than the fixed j=6 kernel family formula.
The replay keeps these two choices distinct.

This result resolves the first three budgets beyond the earlier
return-ladder range, with the sharp classification at written-proof
level. It does not force every least-counterexample orbit to encounter
a useful detour, prove convergence for all odd R, settle larger inverse
budgets, or supply the missing universal cap/residual bounds. The
finite examples and changing family sources give no divergent orbit.

## 6. Verification

Run `python3 verify_minimum_inverse_escape.py`. The
[verifier](../verify_minimum_inverse_escape.py) authenticates all 60
hashes in the preceding return-ladder manifest, freshly builds 29 Lean
modules sequentially, and audits all 27 new roots. Only the standard
logical axioms are allowed; both finite witness roots must have no
axiom dependencies. No native reduction axiom is used.

Independent replay covers:

- 672 general detours from the filtered rectangle `j=0..20,q=1..512`,
  including 480 strict improvements with `j>=6`; 2,049 odd sources in
  the residue class `273 mod729` are also checked directly.
- All ordinary prefixes and all 23,460 target visits for the 17
  progression members `h=0..16`, through R=2,677 and 8,031 source bits.
  Five attaining inverse words per source are replayed, totaling
  177,650 ordinary steps. Modular family checks cover `h=0..1024`.
- The complete negative table on `m=5..46`, with 316 steps, and all
  162 exponent residues used in (10).
- 7,292 exact inverse-minimum queries for every odd R=3 through 513
  and R=1,025. All `i=0..R-1` are covered for R<=17; larger sources
  use `i=0..6`. Each target is checked at budgets `i..i+3`.
- Every inverse branch at budget `i+3` for all odd R=3 through 15,
  every `i<R`, and for R=85 with `i=0..6`: 70 queries, 76,304 nodes.
  Companion checks stop at the precise odd-count boundary, while
  positive inverse enumeration continues beyond it.
- Four kernel arrival witnesses, independently replayed over 4,434
  ordinary steps, including the two 255-bit sources.

The [manifest](../results/minimum-inverse-escape/verification.json)
records compiler identity, exact source and log hashes, timings and
scope distinctions. The exact budget classification remains explicitly
listed under written deductions, even where extensive finite searches
agree with it.
