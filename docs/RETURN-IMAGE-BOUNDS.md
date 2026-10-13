# Logarithmic moments and finite-interval bounds for return images

**Collatz remains unresolved.** Raw returned-endpoint coefficients have
unbounded peaks, but their Haar densities satisfy logarithmic moment
bounds. The same bounds transfer to finite integer intervals when the
return clock is truncated at an explicitly controlled depth. This gives
sampling control beyond a bound on total mass. It does not yet control
pairings with the actual future weighted gradients.

[ReturnImageBounds.lean](../lean/ReturnImageBounds.lean) proves twelve
supporting arithmetic roots. Haar integration, convexity, probability,
and logarithmic moments below are written arguments. The prior written
return estimates are reused; no new external theorem is adopted.

## 1. The image density and its separation weight

Consider nonfused first positive count-return prefixes for adjacent
inputs whose first member is even. For a prefix `i`, write

\[
 (\tau_i,r_i,a_i,x_i,y_i),\qquad
 0\le r_i<r_i+1<2^{\tau_i},\quad
 U^{\tau_i}(r_i)=x_i,\quad U^{\tau_i}(r_i+1)=y_i,
\]

where both odd counts equal `a_i`. Put `D_i=|x_i-y_i|>0`,
`p_i=2^(-tau_i)`, and `lambda_i=3^(a_i)/2^(tau_i)`.
The weights `p_i` are **unconditional binary** probabilities of these
prefixes, so their sum is at most `1/2`.

The affine lift gives endpoints `3^(a_i)q+x_i` and `3^(a_i)q+y_i`.
On ternary integers, with additive Haar probability `mu_3`, define

\[
 F_i(z)=3^{a_i}\mathbf1_{z\equiv x_i\pmod{3^{a_i}}},
 \qquad
 K_\beta(z)=\sum_i p_iD_i^\beta F_i(z),\quad \beta\ge0.             \tag{1}
\]

Each `F_i` has Haar integral one. The density `K_0` is the raw image
density from the previous note. Its separation-weighted version has
mass

\[
 M_\beta=\int K_\beta\,d\mu_3=\sum_i p_iD_i^\beta<\infty
                                      \quad(0\le\beta<1/3),      \tag{2}
\]

by the preceding return-separation moment proof. The separation is an
ordinary integer determined at the return; it does not depend on the
unexposed input. Let `K_(beta,H)` retain only prefixes with `tau_i<=H`.

## 2. Joint return-clock and separation costs

The [square-root clock bound](COUNT-RETURN-CLOCK.md) implies
`E(1+tau)^q<infinity` for every `0<q<1/2`. For instance, splitting into
`tau=1` and the dyadic blocks `2^j<tau<=2^(j+1)` gives the explicit
upper bound

\[
 \mathbb E(1+\tau)^q
 \le 2^q+\frac{7\,2^{2q}}{1-2^{q-1/2}}.                            \tag{3}
\]

Let `alpha>0`, `beta>=0`, and suppose

\[
                              3\beta+2\alpha<1.                  \tag{4}
\]

For `beta>0`, choose
`beta/(1-2alpha)<beta'<1/3`. Hölder, the return-separation
`beta'` moment, and (3), with exponent
`q=alpha beta'/(beta'-beta)<1/2`, give

\[
                  \sum_i p_iD_i^\beta(1+\tau_i)^\alpha<\infty.    \tag{5}
\]

For `beta=0`, (5) follows directly from (3). Restricting the full
first-return law to these even nonfused prefixes can only reduce the
nonnegative sums. No independence of the separation and clock is used.

The same argument without the clock power gives a useful truncation
rate. For any

\[
                       0<\eta<(1-3\beta)/2,
\]

one can choose `beta'<1/3` so that
`eta<(1-beta/beta')/2`. Hölder and the clock tail then show

\[
 \boxed{\|K_\beta-K_{\beta,H}\|_{L^1(\mu_3)}
                 =\sum_{\tau_i>H}p_iD_i^\beta
                 \le C_{\beta,\eta}H^{-\eta}.}                    \tag{6}
\]

For `beta=0`, the endpoint rate `H^(-1/2)` itself follows directly.
These bounds concern the coherent binary law transported to ternary
cylinders, not infinite-time sampling from a finite integer interval.

## 3. A logarithmic moment of the density

Put `Mbar_beta=max(1,M_beta)` and
`Phi_alpha(t)=t[log(1+t)]^alpha` for `t>=0`. This function is convex.
For `t>0`, the sign of its second derivative is that of

\[
                  (t+2)\log(1+t)+(\alpha-1)t>0,
\]

using `log(1+t)>=t/(1+t)`; convexity extends through zero.
The coefficients `p_iD_i^beta/Mbar_beta` sum to at most one. Add the
remaining weight at zero and apply convexity first to finite mixtures,
then pass monotonically to the full sum. Since `F_i` equals `3^(a_i)`
on a set of measure `3^(-a_i)`,

\[
 \begin{split}
 \int K_\beta
       \left[\log\left(1+\frac{K_\beta}{\overline M_\beta}\right)\right]^\alpha
       d\mu_3
 &\le\sum_i p_iD_i^\beta[\log(1+3^{a_i})]^\alpha\\
 &\le(\log3)^\alpha\sum_i p_iD_i^\beta(1+\tau_i)^\alpha
       =:\mathcal A_{\beta,\alpha}<\infty.                        \tag{7}
 \end{split}
\]

Thus

\[
 \boxed{K_\beta\in L(\log L)^\alpha(\mu_3)
                    \quad\text{whenever }3\beta+2\alpha<1.}      \tag{8}
\]

This notation denotes precisely the logarithmic integral in (7);
it does not mean an `L^p` bound for some `p>1`. In particular,
`K_0` has every such logarithmic moment of order below `1/2`, despite
its unbounded essential supremum.

One useful constant is independent of the large return-cycle budget:

\[
                 \int K_0[\log(1+K_0)]^{1/4}\,d\mu_3<80.         \tag{8a}
\]

Indeed `Mbar_0=1`. At `q=1/4`, (3) is less than
`6/5+7(3/2)(20/3)=356/5`, using
`2^(1/4)<6/5`, `sqrt(2)<3/2`, and `2^(-1/4)<17/20`.
Also `log(3)<4/3`, since `exp(4/3)>1+4/3+8/9=29/9>3`, and
`(log 3)^(1/4)<11/10`. Thus (7) is less than
`(356/5)(11/10)=3916/50<80`. The power comparisons are checked
independently with integers; the real exponential and logarithm steps
are written deductions.

For a Haar-measurable set `A` of measure `0<delta<=1`, split at
`R=Mbar_beta/sqrt(delta)`. Equation (7) gives

\[
 \int_A K_\beta\,d\mu_3
 \le\overline M_\beta\sqrt\delta+
    \frac{\mathcal A_{\beta,\alpha}}
         {[\log(1+\delta^{-1/2})]^\alpha}.                         \tag{9}
\]

This supplies an explicit modulus of absolute continuity for the return
image law. Small ternary sets cannot carry a fixed positive amount of
its mass as their Haar measure tends to zero.

There is also a coarse-cylinder approximation. Let `P_L` denote
averaging on residue classes modulo `3^L`. Every term with `a_i<=L`
is already fixed by `P_L`. Since `a_i<=tau_i`, the remainder has mass
at most the right side of (6). The `L^1` contraction of averaging gives

\[
                  \|K_\beta-P_LK_\beta\|_1
                         \le2C_{\beta,\eta}L^{-\eta}.             \tag{10}
\]

The density and all these estimates are under ternary Haar measure.
The next section makes a separate finite-integer statement.

## 4. A prefix bound for finite integer intervals

For **any** pruned parent-parity prefix tree stopped by depth `H`,

\[
              \boxed{\sum_{i:\tau_i\le H}\lambda_i\le2^H.}        \tag{11}
\]

To prove this, give an even branch weight `1/4` and an odd branch
weight `3/4`. The stopped words are prefix-free, so their total tilted
probability `sum 3^(a_i)/4^(tau_i)` is at most one. Multiply each term
by `2^(tau_i)<=2^H` to get (11). The parent's parity words form a
binary prefix tree: at every source-prefix split the two new endpoint
parities are opposite. The kernel checks the corresponding cubic child
identity, its full-period mass `4^t`, and the ordinary and tilted prefix
inequalities using an abstract pruned tree.

The earlier endpoint-retention inequality also gives

\[
 U^\tau(r)<2\,3^{a_\tau(r)}\quad(0\le r<2^\tau),
 \qquad                         D_i<2\,3^{a_i}.                    \tag{12}
\]

Both endpoint comparisons are kernel proved. Consequently (11) gives,
for every `beta>=0`,

\[
 \sum_{\tau_i\le H}\lambda_iD_i^\beta
       \le 2^\beta(2\,3^\beta)^H.                                \tag{13}
\]

Now let `I=[B,B+M)` be any interval of `M>=1` nonnegative integers.
Counting one residue class modulo `q` differs from `M/q` by less
than one. The kernel proves the integer discrepancy for a floor counter;
its elementary identification with this residue count is written and
independently checked by enumeration. Apply the count to each term in
`K_(beta,H)` and use (13):

\[
 \boxed{\left|\frac1M\sum_{n\in I}K_{\beta,H}(n)
           -\sum_{\tau_i\le H}p_iD_i^\beta\right|
       \le\frac{2^\beta(2\,3^\beta)^H}{M}.}                       \tag{14}
\]

In particular the unweighted error is at most `2^H/M`, uniformly in
the interval's location. These periodic columns include all integer
representatives of each residue. An additional constraint on the
source quotient can only reduce their nonnegative values.

The same convex-mixture bound used in (7) is pointwise, before Haar
integration. Apply the residue count to its right side. Since
`log(1+3^(a_i))<=(H+1)log3`, this proves the finite-integer bound

\[
 \begin{split}
 \frac1M\sum_{n\in I}K_{\beta,H}(n)
   \left[\log\left(1+\frac{K_{\beta,H}(n)}{\overline M_\beta}\right)\right]^\alpha
 \le \mathcal A_{\beta,\alpha}
       +\frac{2^\beta[(H+1)\log3]^\alpha(2\,3^\beta)^H}{M}.        \tag{15}
 \end{split}
\]

For `beta=0`, the right side is uniformly bounded, for example, along
`H=floor((1-epsilon)log_2 M)` with any fixed `0<epsilon<1`.
This is uniform integrability of those **truncated densities on the
specified finite integer intervals**, not only of Haar random variables.
For general `beta`, any fixed positive `c<1/log(2*3^beta)` works with
`H=floor(c log M)`. The finite entropy bound also controls subsets of
these intervals by the split used in (9).

There is a concrete version close to the interval's full binary depth.
For the unweighted density, if `2^H(H+1)<=M`, then (8a) and (15) give

\[
 \boxed{\frac1M\sum_{n\in I}K_{0,H}(n)
                 [\log(1+K_{0,H}(n))]^{1/4}<82.}                 \tag{16}
\]

Here the error is less than
`(11/10)(H+1)^(-3/4)<=11/10<2`. The largest allowed depth is
`log_2 M-log_2 log_2 M+O(1)`. In particular the mass on coefficients
larger than `R>0` is at most `82/[log(1+R)]^(1/4)` under these
finite uniform interval laws. This controls the large coefficients
without asserting that they are bounded.

## 5. What is still missing for actual weighted energy

These estimates are compatible with the earlier separation-four family
having multiplier `(243/256)*(3/2)^m`. Uniform integrability permits
unbounded peaks. It also differs from the lack of uniform integrability
of the **endpoint logarithmic-height differences**: those are a different
family under a different sampling law.

The actual return transport pairs these coefficients with
`[f_h(x)-f_h(x-D_i)]^2`, on prefix-dependent intervals and at
prefix-dependent continuation clocks. Equations (7) and (15) do not
bound that pairing by an unweighted energy with a constant multiplier.
The gradients might concentrate where the coefficients are large;
their required complementary integrability has not been proved.

Nor may one fix a finite integer interval and send `H` to infinity in
(14)--(15): their discrepancy term then grows. The Haar limit `K_beta`
does not automatically give control of its individual integer values.

The actual energy estimate remains `O(sqrt(s))`. A bounded subsequence,
escape exclusion, and exclusion of other positive cycles remain open.

## 6. Reproduction and scope

Run `python3 verify_return_image_bounds.py`. The
[record](../results/return-image-bounds/verification.json) authenticates
the previous clock, height-coupling, and persistence records, records
fresh sequential builds and the twelve-root kernel audit, and separates
exact finite counting checks from the written moment arguments.
