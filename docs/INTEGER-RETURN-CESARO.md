# Vanishing return-image averages at fixed integer targets

**Collatz remains unresolved.** The local obstruction repository supplies
enough arithmetic information to prove the following written deduction:
for every fixed positive integer `n`,

\[
 \boxed{\frac{K^*_{0,H}(n)}H
       =\frac1H\sum_{t=1}^H\kappa_t(n)\longrightarrow0.}       \tag{1}
\]

Here `kappa_t` is our density of nonfused count returns at physical clock
`t`, restricted to even initial sources; `K*_(0,H)` is its unweighted
occupation density through `H`. This is an ordinary-integer trace result,
distinct from an almost-everywhere Haar statement. It does **not** assert
that `K*_0(n)` is finite, that `kappa_t(n)` tends pointwise to zero, or that
the estimate is uniform in a growing target interval.

The analytic proof below depends on the external natural weighted
first-hit mean and first-hit clock theorem, read at clone commit
`a7275d5a73814d3d9a400c6fe6577de9542b03a3`. Those developments have not
been freshly replayed here. Nine local kernel roots prove finite integer
inputs; independent rational checks test the finite identities. Neither
form of finite verification certifies the analytic limits.

**Subsequent independent proof:** the
[harmonic return trace argument](HARMONIC-RETURN-TRACE.md) now proves
`K*_(0,H)(n)<=350 C_star n G_n sqrt(H)` using only our local arithmetic
and written fusion tail. Thus the vanishing limit (1) no longer needs
external analytic results, and has a quantitative rate. This note
preserves the original external derivation; its marked full-image limit
(13) remains external and is not reclassified by the later proof.

## 1. From ternary columns to actual positive predecessors

Write `U(m)=m/2` for even `m`, and `(3m+1)/2` for odd `m`. Put

\[
 a_t(m)=\#\{0\le j<t:U^j(m)\text{ is odd}\},\qquad
 \lambda_t(m)=3^{a_t(m)}/2^t.
\]

For `0<=r<2^t`, our existing kernel arithmetic gives

\[
 U^t(2^tq+r)=3^{a_t(r)}q+U^t(r),\qquad
 0\le U^t(r)<3^{a_t(r)}.                                    \tag{2}
\]

If `n>0` belongs to the column `n=U^t(r) mod 3^a`, there is therefore
one nonnegative quotient `q=(n-U^t(r))/3^a=floor(n/3^a)`.
The integer `m=2^tq+r` is positive and satisfies `U^t(m)=n`.
Conversely every positive predecessor has this form, with residue
`r=m mod 2^t`; its first `t` parities and odd count agree with those of
`r`. Thus the full image density has the exact integer interpretation

\[
 b_t(n)=\sum_{\substack{m>0\\U^t(m)=n}}\lambda_t(m).          \tag{3}
\]

Balanced fusion and equality of adjacent odd counts are also invariant
under this lift. Hence the analogous identity with the return-selection
predicate is exact for `kappa_t(n)`. There are no negative-source terms
or unidentified missing positive predecessors. Finiteness follows from

\[
                         m\le2^tU^t(m)=2^tn.                \tag{4}
\]

The [local Lean module](../lean/IntegerReturnCesaro.lean) transfers the
existing sharp packing bound to our common definitions, proves column
existence and uniqueness, (4), backward nonfusion, and periodicity of the
nonfusion mask. Its external analytic inputs are not Lean imports.

## 2. External inputs and the support issue

Let `tau_n(m)` be the first hit of `n`, with value infinity if there is
no hit, and let `w_n(m)` be zero outside the basin. On the basin, it is the reciprocal correction product up to
that first hit. The exact relation is

\[
 0\le w_n(m)\le1,\qquad
 \lambda_{\tau_n(m)}(m)=\frac{n\,w_n(m)}m.                  \tag{5}
\]

For any fixed periodic `p: N->[0,1]`, with period `M>=1` and mean
`pbar=M^-1 sum_(r<M) p(r)`, the clone proves

\[
 \frac1X\sum_{1\le m\le X}w_n(m)p(m)\longrightarrow D_n\bar p.
                                                                  \tag{6}
\]

This is `actual_firstHitWeight_periodic_sourceMean` in
[`WeightedSourcePeriodicMean.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/WeightedSourcePeriodicMean.lean).
It has no odd-source or unit-source support assumption. Relation (5) is
`first_hit_weight` in
[`FirstHitWordWeights.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/FirstHitWordWeights.lean).

Set `delta=log(4/3)/2`. For every `0<epsilon<1`, the clone also proves
that, among odd sources in the basin, the exception set to

\[
 (1-\epsilon)\frac{\log m}{\delta}\le\tau_n(m)
       \le(1+\epsilon)\frac{\log m}{\delta}                  \tag{7}
\]

has zero logarithmic density. This is
`actual_firstHitElapsed_exception_mean_zero` in
[`ActualUnconditionalCanonicalTrace.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/ActualUnconditionalCanonicalTrace.lean).
Its source predicate is odd **basin** membership; divisibility by three
is unrestricted. Its time is shortcut time, not Syracuse depth or the
ordinary map with a separate step for `3m+1`.

The clone's public `periodic_marked_firstHit_mean` theorem has a stronger
odd-unit support assumption and an odd-count clock. We do not apply it
to our masks, which need not have that support. Instead we use (5)--(7)
and the explicit clock argument below. This distinction avoids silently
strengthening that public theorem.

## 3. Removing the odd-source restriction from the clock

Write `m=2^ell q`, with `q` odd. For each fixed `ell`, once `q>n` no
initial halving can hit `n`. Basin membership then agrees for `m,q`, and

\[
 \tau_n(m)=\ell+\tau_n(q),\qquad
 \log m=\log q+\ell\log2.                                  \tag{8}
\]

The difference between the two clock errors in (7) is the fixed constant
`ell(1-log(2)/delta)`. For sufficiently large `q`, a good odd clock with
tolerance `epsilon/2` therefore implies a good clock for `m` with
tolerance `epsilon`. The remaining sources on this fixed valuation layer
are a finite set plus `2^ell` times the odd exceptional set. Their
harmonic weight through `X`, divided by `log X`, tends to zero.

For a cutoff `J`, the omitted layers satisfy the uniform bound

\[
 \sum_{\substack{m\le X\\2^J\mid m}}\frac1m
       =2^{-J}\sum_{q\le X/2^J}\frac1q
       \le2^{-J}(1+\log X).                                \tag{9}
\]

First let `X` tend to infinity with `J` fixed, and then let `J` tend to
infinity. Thus (7) has zero-logarithmic-density exceptions among **all**
positive sources in the basin. Sources hitting `n` during their initial
halvings are already covered by the finite exceptions on each retained
layer and by (9) on the remaining layers. No uniform clock rate in `ell`
or in `n` is required.

## 4. A marked first-hit mean in physical time

Partial summation of (6) gives

\[
 \sum_{m\le X}\frac{w_n(m)p(m)}m
          =D_n\bar p\log X+o(\log X).                       \tag{10}
\]

Define the finite first-hit mass

\[
 F_H^p(n)=\sum_{\substack{m>0\\\tau_n(m)\le H}}
                  \lambda_{\tau_n(m)}(m)p(m).
\]

On the good clock set, all basin sources
`m<=exp(delta H/(1+epsilon))` hit by `H`, and any source hitting by
`H` satisfies `m<=exp(delta H/(1-epsilon))`. The total contribution
of bad sources is `o(H)`: use (5), `p,w_n<=1`, the full-source clock law,
and the exact cutoff `m<=2^H n` for the upper bound. For the lower bound
use the exponential cutoff just displayed. Both logarithmic cutoffs are
`O_n,epsilon(H)`.

Consequently (10) yields

\[
 \frac{\delta nD_n\bar p}{1+\epsilon}
 \le\liminf_H\frac{F_H^p(n)}H
 \le\limsup_H\frac{F_H^p(n)}H
 \le\frac{\delta nD_n\bar p}{1-\epsilon}.
\]

Letting `epsilon` decrease to zero proves

\[
                    F_H^p(n)/H\longrightarrow\delta nD_n\bar p.
                                                                  \tag{11}
\]

All sums at finite `H` are finite by (4); no first-hit tail integrability
assumption or interchange with an unbounded source sum is needed here.

## 5. All visits, including periodic targets

For the same fixed periodic mark define

\[
 B_t^p(n)=\sum_{\substack{m>0\\U^t(m)=n}}\lambda_t(m)p(m).
\]

If `n` is not periodic, a source visits it at most once, and
`sum_(t<=H) B_t^p(n)=F_H^p(n)`. If `n` is periodic, let `R` be its least
positive shortcut period and `rho=3^(a_R(n))/2^R`. Positivity of the
cycle's affine correction gives `0<rho<1`; every cycle contains an odd
step. All visits are at `tau_n(m)+jR`, with weight multiplied by `rho^j`.
Therefore

\[
 \sum_{t=0}^H B_t^p(n)
       =\sum_{0\le j\le H/R}\rho^j F_{H-jR}^p(n).            \tag{12}
\]

From (11), `F_h^p(n)<=C(h+1)` for a finite constant depending on `n,p`.
After dividing (12) by `H>=1`, the summands are bounded by
`2C rho^j`. Dominated convergence thus gives, in both target cases,

\[
 \boxed{\frac1H\sum_{t=0}^H B_t^p(n)\longrightarrow g(n)\bar p,}
 \qquad
 g(n)=\delta G_n nD_n,\quad
 G_n=\begin{cases}(1-\rho)^{-1}&n\text{ periodic},\\
                  1&n\text{ nonperiodic}.\end{cases}        \tag{13}
\]

This is the same finite integer trace used by the external envelope in
our [local review](LOCAL-OBSTRUCTION-REPO-REVIEW.md). Its cycle definition
and exact weight identities occur in
[`ActualGreenSeries.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/ActualGreenSeries.lean)
and [`ActualCycleWeights.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/ActualCycleWeights.lean).
For `p=1`, (13) also identifies the physical-time Cesaro limit of our full
binary image density with `g(n)`. This differs from merely citing the
clone's Cesaro theorem indexed by Syracuse depth.

## 6. Applying the periodic nonfusion masks

Let `p_L(m)` be one if the pair `(m,m+1)` is not balanced-fused by clock
`L`, and zero otherwise. Balanced fusion means equal endpoints and equal
cumulative odd counts. It persists, and its indicator is periodic modulo
`2^L`, both kernel facts. The mean is

\[
 q_L=2^{-L}\sum_{r<2^L}p_L(r)=\Pr(T>L)\longrightarrow0       \tag{14}
\]

under the coherent binary residue law. The existing written
[fusion-clock estimate](COUNT-RETURN-CLOCK.md) gives the stronger bound
`q_L<=14 C_star/sqrt(L)` for `L>=1`. Only its limit zero is used.

For `t>=L`, every actual source selected by `kappa_t(n)` is still
nonfused at `L`. Discarding its even-source and count-return restrictions
therefore gives the pointwise inequality

\[
                         0\le\kappa_t(n)\le B_t^{p_L}(n).  \tag{15}
\]

The terms with `t<L` form a fixed finite sum. Applying (13) and then
(14) gives

\[
 0\le\limsup_H H^{-1}K^*_{0,H}(n)\le g(n)q_L
       \quad\text{for every fixed }L,
\]

which proves (1). The order of limits is essential: first `H` tends to
infinity at fixed `n,L`; then `L` tends to infinity. No assertion about
the convergence rate of (13) with increasing period is made.

## 7. Consequences and remaining limitations

For any fixed finite set of positive targets, (1) holds uniformly over
that set. Nonnegativity also gives zero time density of clocks where
`kappa_t(n)>=epsilon`, for each fixed `n,epsilon>0`. Standard Abel
averaging gives `(1-z) sum_t kappa_t(n) z^t ->0` as `z` increases to one.

This leaves the following gaps:

- A sublinear partial sum can still diverge. Finiteness of `K*_0(n)` is
  not proved, and the Haar `Lp` result alone does not supply it.
- The constants and onset times in (13) depend on the target and the
  mask. Choosing either to grow with the horizon is not justified.
- The temporal annulus criterion `Q` concerns actual forward gradients
  and moving orbit images. It does not follow from this fixed-target
  inverse-image average. Escape and additional positive cycles remain open.

This result is a concrete use of the clone beyond its stationary
majorant: its weighted arithmetic source means and clock theorem turn
our disappearing periodic source masks into disappearing integer-target
Cesaro averages.

## Verification scope

Run `python3 verify_integer_return_cesaro.py`. The
[manifest](../results/integer-return-cesaro/verification.json) records nine
local kernel roots, fresh sequential builds on the pinned standalone
Lean toolchain, and exact finite checks of residue/predecessor bijections,
source cutoffs, nonfusion masks, marked selection inequalities, first-hit
weights, and the all-visit cycle convolution. The known cycle is tested
at both targets 1 and 2. Finite tests do not assert any density or clock
limit and do not infer nonperiodicity from failure to see a return.

The verifier authenticates the prior local clock record and the clone
review, including the specific external source files used here against
the published source inventory. It does not compile the external Lean
bundles or turn their recorded upstream execution into a local replay.
