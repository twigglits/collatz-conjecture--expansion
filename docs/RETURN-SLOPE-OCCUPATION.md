# Summable slopes over all count returns

**Collatz remains unresolved.** The separation at a fresh return has
infinite mean, but the cumulative slopes over all returns have a small
finite budget. For an initially adjacent pair under the coherent binary
residue law, let `S_j` be its successive positive equal-count return
clocks, `N` the first balanced-fusion index (infinity if absent), and

\[
 \Lambda_j=3^{a_{S_j}}2^{-S_j},\qquad h_j=S_j-S_{j-1},\quad S_0=0.
\]

The new written bounds are

\[
 \boxed{\mathbb E\sum_{j=1}^{N}\Lambda_j\le44,\qquad
        \mathbb E\sum_{j=1}^{N}\Lambda_j h_j\le70.}             \tag{1}
\]

The terminal fusion return is included. The sums also include every
one-step equal-count return while the separation is even. These are
budgets for **cumulative slopes**, not improved bounds for `E N` or
for the unweighted physical fusion clock.

For fresh separation `D_0>0` the respective bounds are

\[
 \frac52\log_2(D_0+1)+\frac{83}2,\qquad
 \frac52\log_2(D_0+1)+\frac{135}2.                            \tag{2}
\]

Thirteen kernel arithmetic roots and exact finite checks support the
argument. All change of measure, conditional hitting laws, logarithms,
and infinite sums below remain **written proofs**. No external analytic
theorem is used. The law is not a fixed ordinary integer input followed
forever.

## 1. The return-conditioned tilted clock

Use the [slope tilt](RETURN-SLOPE-TILT.md) of one fixed endpoint.
On every finite prefix its density relative to the original binary
law is that endpoint's cumulative slope. Denote the resulting law by
\(\widehat{\Pr}\). Its next endpoint parity is odd with probability
`3/4`. Active/holding status is predictable, while the active direction
uses the fresh bit.

From a fresh odd separation, the first step leaves count gap zero.
If the chosen endpoint is odd, its signed count lead is positive;
under the tilt it has outward probability `3/4` and return probability
`1/3` from gap one. If it is even, it starts with negative lead and
returns with probability one. Therefore

\[
          \widehat{\Pr}(\text{return})=\tfrac34\cdot\tfrac13
                                      +\tfrac14=\tfrac12.     \tag{3}
\]

These hitting probabilities hold from every finite prefix, independent
of its affine offset. Original-law return is almost sure; the tilted
law may instead have an infinite count excursion.

Condition now on a return. From a positive signed gap `k` the harmonic
factor is `3^-k`. Conditioning changes the active outward probability
to \((3/4)3^{-k-1}/3^{-k}=1/4\) and the inward probability to `3/4`.
From a negative signed gap the unconditioned walk already moves inward
with probability `3/4`. Thus in both cases the **absolute active gap**
is the walk from one killed at zero with inward probability `3/4`.
The two initial parity cases each have conditional probability `1/2`.

Conditioning on eventual return does not change a holding block's law.
If `R>=h` means at least `h` holds at gap `k`, the future return
probability after those holds is still the same harmonic factor at
`k`. Apply the tower property at that fixed finite clock. The factor
cancels between numerator and denominator of the conditional probability.
This justifies reuse of the tilted holding estimate; no independence
between a waiting time and the following active direction is assumed.

Write `v(k)=v_2(3^k-1)`. The previous cylinder count gives

\[
 \widehat{\Pr}(R\ge h\mid\text{prefix, return})
                  \le\min\{1,2^{v(k)}(3/4)^h\}.
\]

Since \(2^v(3/4)^{3v}\le1\), summing this tail bounds the waiting time
`W=R+1`, including its active step:

\[
             \widehat{\mathbb E}(W\mid\text{prefix, return})
                                      \le3v(k)+4.            \tag{4}
\]

The inward walk's expected visits to `k>=1` before absorption are
`4*3^-k`. One finite derivation kills at `0,K`: its Green row from one
is

\[
          g_K(1,k)=\frac{4(3^{K-k}-1)}{3^K-1},\quad 1\le k<K.
\]

The source equation at one and the homogeneous equations elsewhere
determine this finite Green row. Sending `K` upward gives the asserted
visits. All active waits are finite under the tilt, as checked in the
previous note. Summing (4), using `v(k)<2k`, and adding the initial
departure step proves

\[
 \widehat{\mathbb E}(\tau\mid\text{return})
 \le1+4\sum_{k\ge1}3^{-k}(6k+4)=27.                           \tag{5}
\]

In particular, the fresh odd-separation law satisfies

\[
 \boxed{\mathbb E(\lambda_\tau\tau)\le27/2.}                 \tag{6}
\]

This also holds conditional on either original first input parity:
the initial slope times its tilted return probability is `1/2` in
each case. For an even fresh separation, `tau=1` and the unconditioned
left side is one. Equation (6) follows by summing finite return
cylinders, not by assuming a uniformly integrable stopped martingale.

## 2. Group the consecutive one-step returns

At a nonfused equal-count prefix with separation `D>0`, put
`v=v_2(D)`. Exactly `v` one-step returns occur before the separation
becomes odd. During each of them both endpoint parities agree and

\[
       D'\,=\,D/2\ \text{or}\ 3D/2,
\]

with tilted probabilities `1/4,3/4`. Multiplication by three does not
alter the valuation, so each step removes precisely one factor two.
Fusion cannot occur during these positive-separation steps.

Use the logarithmic size \(\ell(D)=\log_2(D+1)\). The kernel identity

\[
 (3D+2)^3(D+2)+18D^2+28D+11=27(D+1)^4
\]

gives the conditional one-step estimate

\[
 \begin{aligned}
 \widehat{\mathbb E}\ell(D')
 &=\tfrac34\log_2(3D/2+1)+\tfrac14\log_2(D/2+1)\\
 &\le\ell(D)+\tfrac34\log_2 3-1
 <\ell(D)+\tfrac15 .
 \end{aligned}                                             \tag{7}
\]

The last inequality uses `3^5<2^8`. Here `D` is even; the displayed
polynomial identity itself holds for every nonnegative integer `D`.
If \(\bar D\) is the odd separation after all `v` steps, iteration and
`v<=ell(D)` give

\[
                    \widehat{\mathbb E}\ell(\bar D)
                                  \le\tfrac65\ell(D).         \tag{8}
\]

The number `v` is fixed at the start of this block. No estimate is
obtained by pretending that each of its one-step returns contracts
the mean slope.

## 3. Logarithmic drift through an odd-separation excursion

The kernel checks the all-word correction bound
`numerator(t,n)+2^t<=3^t` and the resulting equal-count inequality

\[
             D_{\rm next}+1\le(3/2)^\tau(D+1).               \tag{9}
\]

For (9), both corrections lie between zero and \((3/2)^\tau-1\);
their absolute difference is bounded by that same number. The equal
slopes are at most \((3/2)^\tau\). The inequality is asserted at an
equal-count return, not at an arbitrary intermediate step with
opposite endpoint parities.

Apply (9) to the odd separation \(\bar D\), then use (3), (5), and
\(\log_2(3/2)<3/5\):

\[
 \widehat{\mathbb E}\bigl[
       \ell(D_{\rm next})\mathbf1_{\{\text{return}\}}
       \mid\text{odd-separation prefix}\bigr]
     \le\tfrac12\ell(\bar D)+\tfrac{81}{10}.                  \tag{10}
\]

On fusion \(\ell(0)=0\), so this is also a bound after killing fusion.
Every odd-separation prefix has return probability exactly one half;
consequently no correlation with the preceding zero-gap block is
discarded when combining (8) and (10).

Define a grouped transition to consist of all `v` one-step returns,
followed by departure from odd separation and its next return, if any.
Stop the grouping on fusion or on an excursion that never returns
under the tilted law. Let `A_j` be the event that group `j` starts
at a nonfused equal-count prefix, with separation `D_j`. Put

\[
 q_j=\widehat{\Pr}(A_j),\qquad
 l_j=\widehat{\mathbb E}[\ell(D_j)\mathbf1_{A_j}].
\]

Then `q_0=1`, `l_0=ell(D_0)`, and

\[
 q_{j+1}\le\tfrac12q_j,\qquad
 l_{j+1}\le\tfrac35 l_j+\tfrac{81}{10}q_j.                  \tag{11}
\]

Finite telescoping and nonnegativity, followed by monotone convergence,
give

\[
       \sum_{j\ge0}q_j\le2,\qquad
       \sum_{j\ge0}l_j\le\tfrac52\ell(D_0)+\tfrac{81}2.       \tag{12}
\]

The kernel proves the denominator-cleared finite telescoping
inequalities. No stopping at a non-stopping-time “last return” is used:
all events and costs are sums over ordinary finite return cylinders.

## 4. Count every completed return and its excursion length

Within a group, the zero-gap part supplies exactly `v<=ell(D_j)`
completed returns, each of age one. Its odd-separation excursion
supplies one more return with probability `1/2`, and has expected
returned age at most `27/2` by (5). Include a fusion return in these
costs, although it starts no further group. Under the tilted law,

\[
 \begin{aligned}
 \widehat{\mathbb E}(\text{number of completed returns})
     &\le\sum_j(l_j+q_j/2),\\
 \widehat{\mathbb E}(\text{sum of their excursion lengths})
     &\le\sum_j(l_j+27q_j/2).
 \end{aligned}
\]

At each finite equal-count return the likelihood ratio is exactly
its cumulative slope \(\Lambda_j\), for either endpoint. Tonelli
therefore converts these two displayed quantities into the two
original-law sums in (1). Equation (12) proves (2); `ell(1)=1` gives
the constants `44` and `70`.

In particular, these estimates do not require the large previous bound
`540*2^5180` for the unweighted number of cycles. They do not improve
that different bound.

## 5. What this controls for the image density

For the even-source nonfused return columns, keep

\[
 p_i=2^{-t_i},\quad
 F_i(z)=3^{a_i}\mathbf1_{z\equiv x_i\pmod{3^{a_i}}},
 \quad K^*_0=\sum_i p_iF_i.
\]

Each column's individual squared Haar norm is

\[
                     \|p_iF_i\|_2^2=p_i^2 3^{a_i}
                                             =p_i\Lambda_i.
\]

Restricting (1) to these even-source, nonfused prefixes gives

\[
 \boxed{\sum_i\|p_iF_i\|_2^2\le44,\qquad
        \sum_i h_i\|p_iF_i\|_2^2\le70.}                     \tag{13}
\]

Thus the diagonal squared mass from excursions longer than `L>0`
is at most `70/L`. The age `h_i` is the length since the preceding
count return; it is not the full source clock `t_i`.

Equation (13) is **not** an `L2` bound on `K*_0`. Its squared norm
also contains the nonnegative cross terms
\[
               2\sum_{i<j}p_ip_j\int F_iF_j\,d\mu_3,
\]
which (13) does not control. There is no asserted orthogonality of
overlapping ternary cylinders. For example, the actual first-return
prefixes `(t,r,a,x)=(6,48,2,8)` and `(7,74,3,17)` have nested image
cylinders, and their cross inner product is `9/8192>0`, although their
binary source cylinders are disjoint. The finite replay also computes
the full squared norm, keeping these cross terms.

Likewise, (13) does not yet control
their pairing with actual forward gradients or justify an infinite
cutoff on a fixed finite interval of integer sources.

## Verification and the remaining problem

Run `python3 verify_return_slope_occupation.py`. Its
[record](../results/return-slope-occupation/verification.json) separates
thirteen kernel roots from independent exact finite biased-Green,
holding-block, affine-separation, and all-return checks. Unfinished
paths are retained as unfinished. Infinite stopping and integrability
are written deductions, not inferred from finite partial sums.

The new budget isolates the remaining issue more narrowly: individual
return columns have finite total squared mass, including an excursion
length weight. Their overlaps and correlations with actual future
losses remain uncontrolled. The temporal criterion `Q`, escape
exclusion, additional-cycle exclusion, and full Collatz remain open.
