# Complete time sums on finite source annuli

**Collatz remains unresolved.** This note replaces a possible uniform
high power norm of accumulated gradients by a weaker sufficient target:
on each fixed source annulus, its accumulated reversed drift need only
be sublinear in time. There is no uniformity requirement across annuli
in this qualitative criterion. It then certifies full future time sums
on fifteen finite source annuli. The criterion for every source level
is not proved.

The distinction between the two quantifiers is essential: the finite
census below includes **every future offset**, with an exact geometric
tail, but includes only the stated finite source intervals. It assumes
no convergence outside them.

[AnnulusTimeBudgets.lean](../lean/AnnulusTimeBudgets.lean) and
[BinaryConePredecessors.lean](../lean/BinaryConePredecessors.lean) prove
twelve known-cycle, inverse-spine, and arithmetic roots. The infinite
series, density of the spine's binary significands, and conditional
energy implications are written. All finite verification decisions use
integers or rationals.

## 1. Average over time before asking for a charge

Use the original actual refinement notation. For `M=2^k` and
`M<=n<2M`, put

\[
 A_{s,k}(n)=M f_{s+k}(n),\qquad
 B_{s,k}(n)=3M f_{s+k}(3n+2),\qquad
 Z_{s,k}(n)=M z_{s+k}(n).
\]

Both original weights lie in `[0,1]`. Let `R_(s,k)(n)` indicate that
the adjacent pair `2n,2n+1` has already reversed its initial odd-count
order. Thus, at some parent clock `t<=s+k`,
`wt_t(n)>1+wt_t(3n+2)`. The actual level energy and reversed drift are

\[
 e_{s,k}=\frac1{2M}\sum_{n=M}^{2M-1}(A_{s,k}-B_{s,k})^2,
\]
\[
 N^{\rm rev}_{s,k}=\frac1{2M}\sum_{n=M}^{2M-1}
                 R_{s,k}A_{s,k}(A_{s,k}-B_{s,k})_+.
\]

Define nonnegative, possibly infinite, time budgets

\[
 \mathcal T_k=\sum_{s\ge0}e_{s,k},\qquad
 \mathcal R_k=\sum_{s\ge0}N^{\rm rev}_{s,k},\qquad
 \mathcal L_k=\sum_{s\ge0}L_{s,k}.                              \tag{1}
\]

Here `L_(s,k)` is the whole-annulus parent-loss average from
[REVERSAL-PERSISTENCE.md](REVERSAL-PERSISTENCE.md). Monotonicity of
the original and shifted weights gives the unconditional bound

\[
 \mathcal L_k\le\frac1{2M}\sum_{n=M}^{2M-1}(3A_{0,k}+2Z_{0,k})
                      \le\frac52.                             \tag{2}
\]

Equality in the first bound holds if all parents in this finite
annulus reach the known cycle. The finite census explicitly verifies
that hypothesis in each case where it uses equality.

A possible remaining estimate is

\[
                    \mathcal R_k\le C\mathcal L_k
                         \quad\text{for every }k.              \tag{3}
\]

This is weaker than charging each `(s,k)` separately. It permits losses
from other times and other cells in the same annulus. The persistent
one-cell obstruction does not disprove (3). The bound (3), for any
uniform finite `C`, is **unproved**.

## 2. A qualitative criterion without uniformity across source levels

The following is sufficient for escape exclusion. Section 3 gives an
explicit inverse-spine argument that removes the external predecessor
density theorem from this particular implication:

\[
 \boxed{\text{For every fixed }k,\qquad
       \frac1S\sum_{s<S}N^{\rm rev}_{s,k}\longrightarrow0.}     \tag{Q}
\]

In particular, finiteness of each `R_k` would suffice, even if these
finite budgets grow without bound as `k` increases. Here is the written
proof, which passes directly to the limiting refinements instead of
requiring a bounded subsequence of the finite-offset energies `E_s`.

For a fixed cell, both `A_(s,k)` and `B_(s,k)` decrease to limits
`A_infinity,B_infinity`. The historical reversal indicator also has a
limit: it is either always zero or eventually always one. Hence each
reversed negative product has a limit, as does its finite annulus
average `N^rev_(s,k)`. The Cesaro condition (Q) makes this last limit
zero. The ordered negative part also tends to zero, by its previously
proved summability over all offsets and levels. Nonnegativity and the
finite number of cells therefore give, cell by cell,

\[
                    A_\infty(A_\infty-B_\infty)_+=0,
                         \qquad B_\infty\ge A_\infty.          \tag{Q1}
\]

The last conclusion also holds when `A_infinity=0`, since the child
weight is nonnegative. Define

\[
 h_k(x)=2^k f_\infty(\lfloor2^kx\rfloor),\qquad1\le x<2.
\]

The even-child identity passes exactly to the limit, and (Q1) handles
the odd child. Thus `h_(k+1)>=h_k` pointwise. These functions are
bounded; their limit is at most `1/x`, because
`h_k<=2^k/floor(2^kx)`. Also `h_0=0`, since the orbit of one is
the known cycle. For any finite number of nonnegative increments,
the sum of their squares is at most the square of their sum. Passing
monotonically to the infinite sum and integrating proves

\[
 \boxed{\sum_{k\ge0}\int_1^2(h_{k+1}-h_k)^2\,dx
                                      \le\int_1^2 x^{-2}\,dx
                                      =\frac12.}              \tag{Q2}
\]

This is finite **limiting** energy; no exchange of the `s` and `k`
limits is asserted. The earlier written packing/rigidity/PLD argument
would apply, but the following section gives a more direct conclusion:
the limiting weights all vanish. It uses no external density or mixing
theorem.

The hypothesis (Q) remains unproved for all `k`. This conditional
argument does not prove a bounded subsequence of `E_s`, and it does
not exclude additional positive cycles. It identifies a less demanding
temporal condition that would suffice for the escape part of the goal.

## 3. Every binary cone contains a known convergent integer

For `n>=1`, its binary cone is

\[
 \mathcal C(n)=\{2^j n+r:j\ge0,\ 0\le r<2^j\}.
\]

We give a written proof that each cone contains arbitrarily large
integers known to reach one. This is a leading-digit statement, not
a positive-density theorem or a proof that every integer reaches one.

Use the previously kernel-checked six-step inverse child, choosing
its `false` branch, and set `v_0=1`, `v_(j+1)=child(v_j,false)`.
If `v_j=9q+r`, its child is `192q+c_r`, where

| `r` | 1 | 2 | 4 | 5 | 7 | 8 |
|---|---:|---:|---:|---:|---:|---:|
| `c_r` | 16 | 32 | 80 | 104 | 148 | 160 |
| `64r-3c_r` | 16 | 32 | 16 | 8 | 4 | 32 |

The new kernel induction proves, for every `j`,

\[
 v_j>0,\quad3\nmid v_j,\quad U^{6j}(v_j)=1,\quad
 \operatorname{wt}_{6j}(v_j)=j,
\]
\[
 3v_{j+1}=64v_j-d_j,\quad4\le d_j\le32,
\]
\[
 29\,64^j+32\,3^j\le61\,3^jv_j\le61\,64^j.                  \tag{C1}
\]

Let `r_j=3^j v_j/64^j`. It decreases to a limit `c` with
`29/61<=c<=1`, because

\[
 r_j-r_{j+1}=\frac{d_j}{64}(3/64)^j,\qquad
               0\le r_j-c\le\frac{32}{61}(3/64)^j.            \tag{C2}
\]

In particular,

\[
 \log_2 v_j=j(6-\log_2 3)+\log_2 c+o(1).                     \tag{C3}
\]

The number `log_2 3` is irrational, by unique factorization. An
irrational rotation has a dense orbit on the unit circle, and every
tail of that orbit is dense. Therefore adding the `o(1)` error in
(C3) preserves visits to every open arc. The binary significands
`v_j/2^floor(log_2 v_j)` consequently visit every open subinterval of
`[1,2]` at arbitrarily large `j`.

For fixed `2^k<=n<2^(k+1)`, use the open interval
`(n/2^k,(n+1)/2^k)`. A sufficiently large spine member with
significand in that interval lies in
`[2^ell n,2^ell(n+1))` for some `ell>=0`, hence in `C(n)`.
Its convergence to one is already certified by (C1).

Now apply this to (Q1). Let `P(n)` mean `f_infinity(n)>0`.
Exact even refinement and (Q1) show

\[
                 P(n)\Longrightarrow P(2n)\text{ and }P(2n+1).
\]

The new kernel closure lemma propagates this implication to every
member of `C(n)`. But any spine member in that cone reaches one, so
its limiting weight is zero. Thus `P(n)` is impossible for every
positive `n`: under (Q), `W_infinity` vanishes identically. The prior
written packing/weight argument makes this equivalent to absence of
escape. This proof of the conditional implication uses **neither PLD
nor real-scaling measure rigidity**. The universal hypothesis (Q)
remains the unresolved part.

## 4. Quantitative conclusions from averages over source levels

There is an even weaker sufficient hypothesis. The existing written
estimates give

\[
 e_{s,k}\le\frac38 4^{-k}+\frac74(8/3)^s(2/3)^k,
 \qquad E_s\le\frac12+2N_s^{\rm ord}+2N_s^{\rm rev},
 \qquad\sum_{s\ge0}N_s^{\rm ord}\le14.                         \tag{4}
\]

Put `J(S)=ceil(121S/50)`, so the kernel cutoff proves
`(8/3)^S(2/3)^J(S)<=1`, and `J(S)>=S`.
For `K>=J(S)` and integer `S>=1`, sum the energy tail from (4):

\[
 \sum_{s<S}\sum_{k\ge K}e_{s,k}
 \le\frac S2 4^{-K}
     +\frac{63}{20}(8/3)^S(2/3)^K
 \le\frac{73}{20}.                                             \tag{5}
\]

The generous last constant uses `S 4^(-K)<=1`.
Consequently

\[
                \sum_{s<S}E_s
                    \le\sum_{k<K}\mathcal T_k+\frac{73}{20}.
                                                                    \tag{6}
\]

For the reversed drift, Cauchy--Schwarz on the odd half-cells and
`A<=1` give `N^rev_(s,k)<=sqrt(e_(s,k)/2)`. Equation (4) then implies

\[
 N^{\rm rev}_{s,k}
   \le\tfrac12 2^{-k}+(8/3)^{s/2}(2/3)^{k/2}.
\]

Use `sqrt(2/3)<5/6` and `sqrt(8/3)>3/2` to sum both geometric
series. At `K>=J(S)`, their rectangular tail is at most

\[
 S2^{-K}+12(8/3)^{S/2}(2/3)^{K/2}\le13.
\]

Combining this with the ordered bound in (4) gives

\[
             \boxed{\sum_{s<S}E_s
                 \le\frac S2+2\sum_{k<K}\mathcal R_k+54.}      \tag{7}
\]

All infinite sums here are nonnegative. No unproved interchange of
signed series is used. These are bounds on the actual integer source
annuli, without replacement by a longer parity period.

Suppose
`b=liminf_(K->infinity) K^(-1) sum_(k<K) R_k < infinity`.
Along source cutoffs realizing that lower limit, take
`S=floor(50K/121)`. Then `J(S)<=K`, `S` tends to infinity, and
`K/S` tends to `121/50`. Thus (7) proves the conditional conclusion

\[
 \boxed{\liminf_{S\to\infty}\frac1S\sum_{s<S}E_s
                      \le\frac12+\frac{121}{25}b.}             \tag{8}
\]

Likewise, if
`a=liminf_K K^(-1) sum_(k<K) T_k < infinity`, (6) gives a bound
`121a/50` for this lower Cesaro limit. Either implies a bounded
subsequence of individual energies at arbitrarily large offsets.
These hypotheses also imply (Q): finiteness of the lower averages
forces each individual time budget to be finite, and
`N^rev_(s,k)<=sqrt(e_(s,k)/2)`. Thus Section 3 excludes escape without
an external density theorem. Additional positive cycles would still
need exclusion.

In particular, (3) and (2) would give the upper Cesaro bound
`1/2+121C/10`, now from a charge made only after summing time.
No hypothesis in this paragraph or in (8) is established by the
finite census below.

## 5. Exact tails after certified entry into the known cycle

If a positive trajectory is at `1` or `2` at clock `T`, every two
subsequent steps return to that endpoint and add one odd input.
The kernel proves this for an arbitrary number of two-step blocks.
Therefore

\[
                  f_{T+2j}(n)=(3/4)^j f_T(n).                  \tag{9}
\]

For a pair whose two endpoints have entered `{1,2}`, both normalized
weights scale by `3/4` over two steps. Their squared difference, and
their nonnegative product `A(A-B)_+`, scale by `9/16`. The difference
of their odd counts is also periodic with period two. Advance two
extra cycle steps before beginning the tail: this ensures that the
historical reversal indicator has already seen both phases and cannot
change later.

If the two phase costs at that tail start are `c_0,c_1`, the complete
tail is exactly

\[
              \boxed{\sum_{j\ge0}(9/16)^j(c_0+c_1)
                             =\frac{16}{7}(c_0+c_1).}          \tag{10}
\]

The kernel checks the finite geometric identity; its limit is written.
The verifier computes the prefix costs with outward rational bounds,
checks four terminal phases independently, and adds (10) exactly.
It checks actual cycle entry for every sampled pair; a fixed clock
cutoff is never treated as a convergence certificate.

## 6. Finite all-time comparisons and actual returned progressions

The exact census covers all parents `2^k<=n<2^(k+1)` for
`0<=k<=14`, together with their actual children `3n+2`. For these
fifteen annuli it verifies, over **all future offsets**,

\[
                   \mathcal T_k<4,\qquad
                   \mathcal R_k<\frac54,\qquad
                   \mathcal R_k\le\mathcal L_k.                \tag{11}
\]

It also certifies `R_13>1`, so a proposed upper bound of one would
already fail in this finite range. None of (11) is extrapolated to
unbounded `k`.

For a separate test of the density-gradient transport, use the actual
first-return cylinder `r=48 mod64`, with endpoints `(9q+8,9q+7)`.
At `Q=2^L`, `M=9Q`, its source annulus is `[64Q,128Q)`, its image
interval is `[M+8,2M+8)`, and its progression is `9q+8` with
`Q<=q<2Q`. Define the accumulated actual gradient

\[
 G_L(x)=\sum_{s\ge0}
           [M\{f_{L+s}(x)-f_{L+s}(x-1)\}]^2.                   \tag{12}
\]

The original refinement level is `k=L+5`, so the return prefix's
contribution to `T_k` is exactly `1/64` times the progression mean
of (12). The verifier checks the original-source transport directly.
It certifies moments of orders `1,2,4,8,12` of (12) on both the
progression and its containing interval, for `L=0,2,4,6,8,10`.
The full time tail is included using (10).

For each of these powers, multiplication by
`9*1_(x=8 mod9)` gives exactly the progression mean. Thus these
comparisons keep the density-gradient correlation and the actual
integer samples. They do not equate a progression average to its
unweighted interval average. Nor do they assert bounded or unbounded
moments as `L` tends to infinity.

## 7. Verification and next target

Run `python3 verify_annulus_time_budgets.py`. The
[verification record](../results/annulus-time-budgets/verification.json)
authenticates the preceding persistence, energy-cap, and image-energy
records, and distinguishes twelve kernel roots from exact finite-source
checks and written infinite sums. The inverse-spine census also checks
known-cycle witnesses in every binary cone with root `1<=n<=1023`;
this is separate from the written proof for all roots. The census uses a `2^96` denominator
for outward bounds before summing; selected complete sums are also
recomputed as exact rational numbers. Floating values printed during
the run are displays only.

The new [density power bounds](BINARY-IMAGE-ENERGY.md) remain useful,
but they do not force a uniform high power norm of (12). A direct
estimate of the actual correlated mean may be more appropriate. The
weakest target established here is (Q): sublinear temporal reversed
drift separately at each fixed source level. The stronger (3) and
the lower-average hypothesis in (8) would give quantitative control
of finite-offset energies as well. All remain open over unbounded
source levels. The actual established energy bound remains
`O(sqrt(s))`; this finite all-time census proves neither escape
exclusion nor the Collatz conjecture.
