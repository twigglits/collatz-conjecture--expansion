# Affine budgets over all returns and a stronger density bound

**Collatz remains unresolved.** The written all-return density theorem
improves to

\[
 \boxed{K^*_\beta\in L^p(\mu_3),\qquad
   0\le\beta<\tfrac12,\quad 1\le p<\frac6{5+2\beta}.}       \tag{1}
\]

In particular, the unweighted density has every power moment below
`6/5`, improving the earlier range below `10/9`. The new input is a
summable budget for the **cumulative affine coefficient at all nonfused
returns**, rather than only the correction during one return cycle.
Concentration of the ordinary parity count reduces the number of
components that have to be combined.

[ReturnAffineBudget.lean](../lean/ReturnAffineBudget.lean) proves eight
arithmetic roots. Fractional moments, stopping arguments, concentration,
Haar integration, and the infinite-series deduction remain **written**.
The argument reuses the existing written return estimates and uses no
new external stationary-law or mixing theorem. It still gives no bound
for the pairing with actual future weighted gradients, no universal
temporal-drift estimate, and no exclusion of escape or additional cycles.

## 1. One coefficient that composes across return cycles

Use the coherent full binary residue law. For the first endpoint write

\[
 U^t(n)=\Lambda_t n+B_t,\qquad
 \Lambda_t=3^{a_t}/2^t,\quad B_t=N_t/2^t,\quad
 C_t=\Lambda_t+B_t=\frac{3^{a_t}+N_t}{2^t}.                  \tag{2}
\]

Here `N_t` is the nonnegative affine numerator. The coefficient `C_t`
is the image of the *formal real input one under that parity word*;
it need not equal the actual orbit of the integer one. It is positive
and determined by the binary prefix. In particular `C_0=1`.

If a continuation of length `h` has slope `lambda` and correction `b`,
then

\[
                     C_{t+h}=\lambda C_t+b.                  \tag{3}
\]

The new kernel proof checks both the numerator and augmented-numerator
versions of (3), along with lift invariance and the one-step identity

\[
 C_{t+1}=\begin{cases}C_t/2,&\text{next parity even},\\
                      (3C_t+1)/2,&\text{next parity odd}.
         \end{cases}                                        \tag{4}
\]

For `0<eta<1`, put

\[
 r_\eta=\tfrac12\bigl(2^{-\eta}+(3/2)^\eta\bigr)<1.
\]

Conditional fairness and subadditivity of the power give

\[
 \mathbb E C_{t+1}^{\eta}
 \le r_\eta\mathbb E C_t^{\eta}+2^{-\eta-1},\qquad
 \sup_{t\ge0}\mathbb E C_t^\eta
 \le A_\eta:=1+\frac{2^{-\eta-1}}{1-r_\eta}.                \tag{5}
\]

The strict inequality for `r_eta` is strict concavity applied to the
two distinct positive slopes of mean one. This fixed-clock estimate
allows `eta<1`. It does not by itself apply at an unbounded stopping
time.

## 2. A summable coefficient budget at the return clocks

Retain `S_j`, `D_j`, and `N` from
[RETURN-OCCUPATION-DENSITY.md](RETURN-OCCUPATION-DENSITY.md): `S_j`
is the physical clock of the `j`th positive count return, and `N` is the
return index at balanced fusion. Start at `S_0=0,D_0=1` and absorb at
fusion. The existing result gives

\[
 \mathbb E N\le C_*:=540\,2^{5180}.
\]

For each new return cycle, conditional on its starting prefix, the
[stopped-correction bounds](RETURN-CORRECTION-MOMENTS.md) give

\[
 \mathbb E\lambda^\eta\le r_\eta,\qquad
 \mathbb E b^\eta\le m_\eta:=1+\frac{7\eta}{1-2\eta}
                                      \quad(0<\eta<1/2).       \tag{6}
\]

These are conditional bounds for fresh binary extensions; the two
endpoint parities are not independent. In (3) the value `C_(S_j)` is
already measurable at that prefix. No independence between the new
slope and correction is required. Subadditivity therefore gives

\[
 \mathbb E[C_{S_{j+1}}^\eta\mid\mathcal F_{S_j}]
       \le r_\eta C_{S_j}^\eta+m_\eta\quad(j<N).             \tag{7}
\]

Kill the coefficient at fusion: set
`V_j=1_(j<N) C_(S_j)^eta`, with zero after killing. Dropping the
nonnegative terminal value in (7) proves

\[
 \mathbb E V_{j+1}\le r_\eta\mathbb E V_j
                             +m_\eta\Pr(j<N).
\]

Sum through a finite index, use `V_0=1`, and then use monotone
convergence. The result is

\[
 \boxed{\mathbb E\sum_{j<N}C_{S_j}^\eta
       \le M_\eta:=\frac{1+m_\eta C_*}{1-r_\eta}<\infty
                              \quad(0<\eta<1/2).}            \tag{8}
\]

The finite rational-drift algebra, after clearing denominators, is a
new kernel lemma. The real-valued expectation inequality and infinite
sum are written steps. For example the prior bound `r_(1/4)<39/40`
gives `M_(1/4)<=40+180 C_*`.

Let `nu` count the nonfused returns with indices `1<=j<N`, as before.
Then (8) gives `integral C^eta dnu<=M_eta`. The existing clock tail
also gives, after increasing a finite constant to include `H=1`,

\[
             \nu(S\ge H)\le A(1+\log(H+1))H^{-1/2}.
                                                               \tag{9}
\]

Restricting to even initial inputs only decreases these nonnegative
quantities. We use this restriction for the density below; we do not
assume that its first parity is conditionally fair after fixing it.

## 3. Fractional cost of a fixed-clock, fixed-count image fibre

At clock `t`, restrict to any selected subset of the full binary period
with odd count `a`. Write

\[
 \kappa_{t,a}(z)=2^{-t}\sum_{r\text{ selected},\ a_t(r)=a}
       3^a\mathbf1_{z\equiv U^t(r)\pmod{3^a}}.
\]

The selected subset can be the nonfused count returns. Within an image
fibre of size `m`, the earlier
[quotient injection](BINARY-IMAGE-ENERGY.md) sorts the numerators so that
`N_j/3^a>=j` for `j=0,...,m-1`. Thus `3^a+N_j>=3^a(j+1)`;
this last integer inequality is also a new kernel root.

For real `p>1`, integration of the increasing function `x^(p-1)` on
`[0,m]` gives `m^p<=p sum_(j=1)^m j^(p-1)`. With `alpha=p-1`,

\[
 (3^a)^\alpha m^p
       \le p\sum_{r\text{ in fibre}}(3^a+N_t(r))^\alpha.
\]

Each ternary fibre has Haar measure `3^(-a)`. Summing and dividing
by `2^(pt)` gives the useful fractional form of the image estimate:

\[
 \boxed{\|\kappa_{t,a}\|_p^p
       \le p\,2^{-t}\sum_{r\text{ selected},\ a_t(r)=a}
                           C_t(r)^{p-1}.}                    \tag{10}
\]

Unlike the earlier quadratic estimate, the right side now has the
summable all-return moment (8) when its exponent is below `1/2`.
For the full image density, (5) and the at-most-`t+1` counts also give
the unconditional fixed-clock bound

\[
 \|\rho_t\|_p^p\le p(t+1)^{p-1}A_{p-1}
                                      \quad(1<p<2).           \tag{11}
\]

Neither (10) nor summability of its right sides alone permits summing
the densities in `L^p`. Their overlapping components still have to be
controlled. The next two steps do that explicitly.

## 4. Remove the atypical parity counts

The full binary period has `a_t` distributed as `Binomial(t,1/2)`.
The kernel identity

\[
           \sum_{r<2^t}z^{a_t(r)}=(1+z)^t\quad(z\in\mathbb N)
\]

checks its generating polynomial. Equivalently, the two children of
every prefix have counts `a` and `a+1`, which gives the binomial law
by induction. For completeness, the written exponential bound follows
from

\[
 \mathbb E e^{u(a_t-t/2)}=(\cosh(u/2))^t\le e^{tu^2/8}.
\]

The inequality `log cosh v<=v^2/2` follows by integrating
`tanh v<=v` for `v>=0`, and symmetry handles negative `v`.
Exponential Markov with `u=4R/t`, applied in both directions, gives
`Pr(|a_t-t/2|>R)<=2 exp(-2R^2/t)`.

Take

\[
 R_t=2\sqrt{t\log(t+2)},\qquad
 \mathcal A_t=\{|a_t-t/2|>R_t\},\qquad
                    \Pr(\mathcal A_t)\le2(t+2)^{-8}.          \tag{12}
\]

Fix `1<p<6/5`, so `0<alpha=p-1<1/5`. Let `psi_t` be the sum
of the selected return densities over these atypical counts. Apply
(10), combine at most `t+1` count components, and use Hölder with
the fixed-clock half-moment in (5):

\[
 \begin{aligned}
 \|\psi_t\|_p^p
 &\le p(t+1)^\alpha\,
                  \mathbb E[\mathbf1_{\mathcal A_t}C_t^\alpha]\\
 &\le p(t+1)^\alpha A_{1/2}^{2\alpha}
                               \Pr(\mathcal A_t)^{1-2\alpha}\\
 &\ll_p(t+2)^{17\alpha-8}.                                \tag{13}
 \end{aligned}
\]

The exponent `(17alpha-8)/p` is strictly below `-1` throughout
this range. Hence `sum_t ||psi_t||_p<infinity`. In particular the
entire atypical part belongs to `L^p`. Discarding the return-selection
indicator in (13) was an upper bound on nonnegative terms, not an
independence assumption about returns and counts.

## 5. Sum the typical returns in dyadic clock blocks

For `H=2^j`, let `Delta_H` collect the typical return components
with `H<=t<2H`. Each clock has at most `2R_t+1` typical counts.
The number of components therefore satisfies

\[
               G_H\le8H^{3/2}\sqrt{\log(2H+2)}.              \tag{14}
\]

Use the finite inequality `(sum_(i=1)^G u_i)^p<=G^(p-1) sum_i u_i^p`,
then (10). For any `alpha<eta<1/2`, Hölder with respect to the
occupation measure, followed by (8)--(9), gives

\[
 \begin{aligned}
 \|\Delta_H\|_p^p
 &\le pG_H^\alpha\int_{H\le S<2H}C^\alpha\,d\nu\\
 &\le pG_H^\alpha M_\eta^{\alpha/\eta}
                                   \nu(S\ge H)^{1-\alpha/\eta}\\
 &\ll_{p,\eta} H^{d(p,\eta)}
                  (1+\log(H+1))^{\alpha/2+1-\alpha/\eta},
 \qquad d(p,\eta)=\frac{3\alpha}{2}-\frac12+
                                          \frac{\alpha}{2\eta}.
                                                               \tag{15}
 \end{aligned}
\]

There exists `eta<1/2` making `d(p,eta)<0` precisely when
`alpha<1/5`: choose

\[
             \frac{\alpha}{1-3\alpha}<\eta<\frac12.
\]

This choice also has `eta>alpha`. The negative power of `H=2^j`
in (15) dominates its logarithmic factor, so
`sum_j ||Delta_(2^j)||_p<infinity`. Finite Minkowski followed by
monotone convergence, together with the atypical part, proves

\[
                         K^*_0\in L^p(\mu_3)
                                      \quad(1<p<6/5).         \tag{16}
\]

The case `p=1` is the existing finite occupation mass. The method
does not give the endpoint `p=6/5` or establish optimality.

## 6. Separation weights and the remaining arithmetic gap

For `0<=beta<gamma<1/2`, apply Hölder inside the positive column
sum, pointwise in the ternary variable:

\[
 K^*_\beta\le(K^*_0)^{1-\beta/\gamma}
                           (K^*_\gamma)^{\beta/\gamma}.
\]

The prior separation budget makes `K*_gamma` integrable. Combining
it with (16) and then taking `gamma` arbitrarily close to `1/2`
and the unweighted exponent arbitrarily close to `6/5` proves (1).
For any exponent strictly below its stated boundary, those two choices
can be made strictly inside their allowed ranges; no endpoint norm is
being used.

For `beta=0`, the conjugate gradient exponent can now be any fixed
number strictly above six, instead of strictly above ten. This reduces
the strength of a sufficient complementary power bound. Such a bound
for the **actual accumulated weighted gradients is still unproved**.
The earlier superlinear exponential-moment obstruction does not disprove
these finite power norms.

Moreover, the norm here is a ternary Haar norm. The previous finite
period transfer applies to each truncated density with its stated
`1+3^H/M` factor. It gives no infinite-cutoff trace bound on a fixed
ordinary integer interval. Both this sampling issue and the gradient
estimate remain; (1) proves neither the annulus criterion (Q) nor the
Collatz conjecture.

## 7. Verification scope

The [verification record](../results/return-affine-budget/verification.json)
separates the eight kernel roots, exact finite replay, and the written
analytic deductions. Finite fractional powers use outward rational
enclosures obtained with integer roots. No floating comparison decides
an inequality. Tests of finite moments are not extrapolated to infinite
ones; the latter use the written argument above.

Reproduce from the repository root:

```sh
python3 verify_return_affine_budget.py
```
