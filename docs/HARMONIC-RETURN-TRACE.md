# A uniform square-root bound for nonfusion inverse occupation

**Collatz remains unresolved.** An elementary harmonic argument strengthens
the [fixed-target Cesaro result](INTEGER-RETURN-CESARO.md), removes its
external analytic dependencies for that conclusion, and gives a rate.
Write `C_star=540*2^5180` and `A=14 C_star`. For every positive integer
target `n` and integer `H>=1`, the written bound is

\[
 \boxed{K^*_{0,H}(n)\le Z_H(n)
       \le25A\,nG_n\sqrt H=350C_*\,nG_n\sqrt H.}              \tag{1}
\]

`Z_H` counts **all nonfused visits**, so dominates the selected equal-count
returns in `K*_(0,H)`. The cycle factor `G_n` is one if `n` is nonperiodic;
if `n` is periodic with least shortcut period `R`, it is
`1/(1-3^(a_R(n))/2^R)`. Always

\[
                              1\le G_n\le3n+1.              \tag{2}
\]

The constant in (1) is independent of the target. In particular,

\[
 \sup_{n\ge1}\frac{K^*_{0,H}(n)}{HnG_n}
       \le\frac{350C_*}{\sqrt H}\longrightarrow0.             \tag{3}
\]

This is not an unnormalized estimate along arbitrarily growing targets.
It does not prove finite total occupation, control actual forward
gradients, exclude escape or other cycles, or solve Collatz.

The proof uses the project's existing **written** coherent-binary fusion
tail and ten new local kernel arithmetic roots. Its infinite real
summations remain written. No external density, clock, envelope, or
predecessor theorem is used in (1)--(3).

## 1. The masks and the larger occupation sum

Use the shortcut map `U`, odd count `a_t(m)`, and coefficient
`lambda_t(m)=3^(a_t(m))/2^t`. Let

\[
 p_t(m)=\mathbf1_{\{(m,m+1)\text{ is not balanced-fused by }t\}},
 \qquad q_t=2^{-t}\sum_{r<2^t}p_t(r).
\]

Balanced fusion means equal endpoints and equal cumulative odd counts.
Its persistence and binary lift identities imply

\[
 p_T(m)\le p_L(m)\quad(L\le T),\qquad
 p_L(m+2^L)=p_L(m),\qquad q_0=1.                             \tag{4}
\]

The previous [fusion-clock proof](COUNT-RETURN-CLOCK.md) gives

\[
                         q_L\le A/\sqrt L\quad(L\ge1).      \tag{5}
\]

Define the finite inverse occupation

\[
 Z_H(n)=\sum_{t=0}^H\sum_{\substack{m>0\\U^t(m)=n}}
                         \lambda_t(m)p_t(m).                \tag{6}
\]

The exact positive-column correspondence from the preceding kernel
module shows that every term of `K*_(0,H)(n)` occurs in (6). Dropping
the even-source and equal-count restrictions increases a nonnegative sum.
No probabilistic independence is used.

## 2. All bounded-clock predecessors occupy few binary ranges

The elementary step inequalities are

\[
                  m\le2U(m),\qquad
                  2(U(m)+1)\le3(m+1).
\]

If `U^t(m)=n` and `t<=h`, they imply

\[
                m\le2^h n,\qquad
                2^h(n+1)\le3^h(m+1).                       \tag{7}
\]

Thus, for any two positive sources `u,v` reaching `n` by clock `h`,

\[
                    v\le3^h(u+1)\le2\,3^h u.               \tag{8}
\]

The set `P_h(n)` of these sources is finite, contains `n`, and hence has
a minimum `a` and maximum `b`. If these lie in binary ranges with indices
`j` and `k`, then

\[
 2^k\le b\le2\,3^h a
      <2\,4^h2^{j+1}=2^{j+2h+2}.
\]

Consequently `k-j+1<=2h+2`. The whole source interval `[a,b]` meets at
most `2h+2` ranges `[2^i,2^(i+1))`, **independently of n**. These growth,
span, and binary-index bounds are new kernel theorems.

We also have the existing exact coefficient inequality

\[
                   \frac{\lambda_t(m)}n\le\frac1m
                         \quad(U^t(m)=n,\ m,n>0).           \tag{9}
\]

It follows directly from the nonnegative affine correction, with no
first-hit density or clock estimate.

## 3. Harmonic mass of a nonfusion mask on a binary range

For `j,T>=0`, (4) and the exact complete-period counts give

\[
 \boxed{\sum_{2^j\le m<2^{j+1}}\frac{p_T(m)}m
                            \le q_{\min(j,T)}.}              \tag{10}
\]

Indeed, put `L=min(j,T)`. We have `p_T<=p_L`, and the source range
consists of exactly `2^(j-L)` complete periods of length `2^L`.
Its `p_L` count is `2^j q_L`; multiplying by `1/m<=2^-j` proves (10).
The mask comparison, repeated-period counts, and resulting numerator
bound are kernel checked for all indices.

The use of the earlier mask when `j<T` is essential. For example,
`p_T(1)=1`: the known cycle keeps 1 and 2 in different phases.
For a clock with `q_T<1`, replacing the right side of (10) by `q_T`
even in the range `{1}` would be false.

Set

\[
                         Q_T=\sum_{j=0}^{T-1}q_j.
\]

On any source interval meeting at most `B` binary ranges, (10) implies

\[
             \sum_{m\text{ in the interval}}\frac{p_T(m)}m
                                \le Q_T+Bq_T.                \tag{11}
\]

All ranges below index `T` together cost at most `Q_T`; the remaining
at most `B` ranges cost at most `q_T` each. This is a bound on actual
integer samples, including the small sources.

Since `A>=1`, (5) and comparison of the decreasing function `x^-1/2`
with its integral give

\[
                              Q_T\le2A\sqrt T\quad(T\ge1). \tag{12}
\]

For clarity, when `T>=2`,
`sum_(j=1)^(T-1) j^-1/2 <= 2 sqrt(T-1)-1`. After adding `q_0=1`
and using `A>=1`, (12) follows. The case `T=1` is immediate.

## 4. First hits in a dyadic clock block

Let `tau_n(m)` be the first hit, or infinity when there is no hit. Define

\[
 F_H(n)=\sum_{\substack{m>0\\\tau_n(m)\le H}}
                       \lambda_{\tau_n(m)}(m)p_{\tau_n(m)}(m).
\]

There is only one first hit per source, including first hit zero for
`m=n`. Fix `T>=1` and restrict to `T<=tau_n(m)<2T`. For these sources,
`p_tau<=p_T`, and all lie in `P_(2T-1)(n)`. By (8), that source
interval meets at most `4T` binary ranges. Equations (9)--(12) give

\[
 \frac1n\sum_{T\le\tau_n(m)<2T}
           \lambda_{\tau_n(m)}(m)p_{\tau_n(m)}(m)
       \le Q_T+4Tq_T\le6A\sqrt T.                           \tag{13}
\]

A partially filled last clock block only reduces the left side. For
`H>=1`, cover the positive clocks by blocks with `T=1,2,4,...,2^J`,
where `2^J<=H<2^(J+1)`. Since

\[
 \sum_{i=0}^J\sqrt{2^i}
       \le(2+\sqrt2)\sqrt{2^J}<4\sqrt H,
\]

and the first-hit-zero term divided by `n` is at most one, we get

\[
                         F_H(n)\le25A n\sqrt H.             \tag{14}
\]

The target-independent constant comes from the source **ratio** bound
in (8), not from a uniform density limit as the target moves.

## 5. Repeated visits and the cycle factor

For a nonperiodic target, a source cannot revisit it, so `Z_H(n)=F_H(n)`.
For a periodic target of least positive period `R`, let
`rho=3^(a_R(n))/2^R`. All visits after the first are at
`tau_n(m)+jR`, with coefficient `lambda_tau(m)rho^j`.
Nonfusion persistence gives `p_(tau+jR)(m)<=p_tau(m)`. Thus

\[
                Z_H(n)\le\frac{F_H(n)}{1-\rho}=G_nF_H(n),  \tag{15}
\]

provided `rho<1`. No assumption about the absence of unknown cycles
is made here.

The new kernel arithmetic proves a useful quantitative bound. A positive
cycle has a positive odd count, and any finite path with positive odd
count satisfies

\[
              (3m+1)3^{a_t(m)}\le3\,2^tU^t(m).              \tag{16}
\]

An odd first step gives (16) immediately from the coefficient lower
bound for the remaining path. An initial even step preserves the
inequality by induction. A path with no odd step satisfies
`2^t U^t(m)=m`, so cannot be a positive cycle of positive length.
Applying (16) to a cycle at `n` gives

\[
              \rho\le\frac{3n}{3n+1}<1,\qquad G_n\le3n+1. \tag{17}
\]

Equations (14)--(17) prove (1)--(3) for all target types, using only
local arithmetic and the earlier written fusion tail.

## 6. What improves, and what remains open

For each fixed positive target, (1) gives the quantitative limit
`K*_(0,H)(n)/H=O_n(H^-1/2)`, and the same holds for the larger `Z_H`.
This independently proves the previous vanishing Cesaro conclusion.
The earlier marked full-image limit `g(n) mean(p)` remains an external
deduction; it is not needed here and is not reclassified as a local proof.

For any moving sequence of nonperiodic targets, the normalized bound
`Z_H(n)/(Hn)<=350 C_star/sqrt(H)` holds. Without deciding periodicity,
the explicit bound `Z_H(n)/H<=350 C_star n(3n+1)/sqrt(H)` is available.
Consequently the unnormalized convergence is uniform on target windows
`1<=n<=R(H)` when `R(H)=o(H^(1/4))`. On nonperiodic targets it is uniform
when `R(H)=o(sqrt(H))`.

There is also an infinite-cutoff integer estimate with a time discount.
For every `sigma>1/2`, grouping positive clocks into binary blocks in (1)
gives the convergent series bound

\[
 \boxed{\sum_{t\ge1}t^{-\sigma}\kappa_t(n)
    \le\frac{350\sqrt2\,C_*\,nG_n}
                 {1-2^{1/2-\sigma}}<\infty.}                \tag{18}
\]

For `0<z<1`, summation by parts and Cauchy--Schwarz give a corresponding
quantitative Abel bound:

\[
 (1-z)\sum_{t\ge1}\kappa_t(n)z^t
   =(1-z)^2\sum_{H\ge0}K^*_{0,H}(n)z^H
   \le350C_*nG_n\sqrt{z(1-z)}.                              \tag{19}
\]

Here `K*_(0,0)=0`, and the last step uses
`sum H z^H=z/(1-z)^2` and `sum z^H=1/(1-z)`. These are written
consequences of the proved bound, not claims that the undiscounted
occupation is finite.

These statements still permit a divergent forward orbit. At its moving
target `n=U^t(m)`, a single inverse column has normalized weight
`lambda_t(m)/n=W_t(m)/m`, which can tend to a positive value. A cumulative
upper bound growing like `sqrt(H)` allows that contribution. The actual
forward gradient criterion `Q` requires additional information about
these paths and their correlations. Neither finite total integer
occupation nor a target-independent bound for the unnormalized sum has
been established.

## Verification

Run `python3 verify_harmonic_return_trace.py`. The
[manifest](../results/harmonic-return-trace/verification.json) separates
ten kernel roots, exact finite rational tests, and the written harmonic
summations. The finite tests cover nested mask populations and harmonic
mass on binary ranges and arbitrary intervals, bounded-clock source spans,
first-hit blocks, all nonfused visits, selected returns, and the geometric
cycle comparison at targets 1 and 2. An explicit small-source test detects
the invalid replacement of `q_min(j,T)` by `q_T`.

All dependencies are local. The verifier authenticates the prior fusion
clock record and freshly builds the local arithmetic dependency chain.
No external source bundle is imported, compiled, or required for the new
analytic conclusion. Finite checks do not certify the written fusion
tail or its infinite harmonic consequence.
