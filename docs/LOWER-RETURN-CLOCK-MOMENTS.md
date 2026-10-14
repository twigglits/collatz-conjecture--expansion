# Joint clock moments and stronger lower-image density bounds

**Collatz remains unresolved.** The lower endpoint at a return carries
more information than its finite total coefficient cost. Its fractional
coefficient moments remain integrable after a power of the **total**
return clock is inserted:

\[
 \boxed{\mathbb E\sum_{1\le j<N}
          P_j^\theta(1+S_j)^q<\infty
       \quad(0\le\theta<1,\ 0\le q<1/2).}                  \tag{1}
\]

Here \(S_j\) runs over every nonfused positive count return, including
the common-parity one-step returns. The probability law is the coherent
full binary residue law. This is not sampling a finite interval of
ordinary integer sources for arbitrarily long times.

Combining (1) with the fibre bound and count concentration gives a
full density estimate, including all overlap terms:

\[
 \boxed{K^{\mathrm{low}}_\beta\in L^p(\mu_3)
     \quad(0\le\beta<1,\ 1\le p<4/(3+\beta)).}              \tag{2}
\]

In particular the unweighted lower-image density has every power
moment below \(4/3\). The earlier range below \(5/4\) was for the
original first-endpoint density. Endpoint relabeling preserves the
squared pair gradient but changes that density; (2) does not silently
upgrade the original density. Neither the endpoint \(4/3\), a full
\(L^2\) bound, nor an actual-gradient pairing estimate is proved.

Seven new kernel arithmetic roots support the argument. Fractional
moments, stopping, logarithms, Holder, concentration, and infinite
norms remain **written proofs**. All analytic inputs are earlier local
written results; no external stationary-density theorem is adopted.

## 1. Occupation with clock powers and logarithms

Let \(\nu\) count all nonfused positive return prefixes under the
original law, and add a unit atom at \(S=0,D=1\) when needed.
The earlier occupation estimates give

\[
 \nu(S\ge H)=O((1+\log(H+1))H^{-1/2}),\qquad
 \int D^\eta\,d\nu<\infty\quad(0<\eta<1).                  \tag{3}
\]

Consequently, with \(L=\log_2(D+1)\),

\[
 \int(1+S)^u L^r\,d\nu<\infty
       \quad(0\le u<1/2,\ 0\le r<\infty).                 \tag{4}
\]

For \(u>0\), choose \(u<u'<1/2\) and apply Holder with exponents
\(u'/u\) and \(u'/(u'-u)\). The clock moment follows by integrating
the tail in (3). Every finite logarithmic moment is bounded by a
constant times \(1+D^\eta\), for any fixed \(0<\eta<1\).
For \(u=0\) only this last observation is needed. This uses no
independence of clock and separation.

Group returns as before: a group starts at an equal-count pair,
performs \(v=v_2(D)\) common-parity steps, and then an odd-separation
excursion. Stop on fusion. Write its start clock as \(T_j\), its
minimum as \(P_j^g\), and its separation as \(D_j^g\).
Every group start is a return or the initial state, so (4) also holds
on this subset. The [preceding argument](ALL-RETURN-LOWER-ENERGY.md)
supplies

\[
 \sum_j\mathbb E P_j^g<\infty,\quad
 \sum_j\mathbb E[P_j^g L_j]<\infty,\quad
 \sum_j\mathbb E(D_j^g)^{3/4}<\infty,                       \tag{5}
\]

always with the group-existence indicator understood.

## 2. The coefficient times a power of one group duration

Fix \(0<q<1/2\). The new fast-correction tail from the preceding
note, conditional on either initial parity, is

\[
 \mathbb E[b_F\mathbf1_{\{\tau>2h\}}]\le107h^{-1/2}.
\]

Dyadic summation therefore gives the uniform fresh bound

\[
 \mathbb E[b_F\tau^q]\le
 F_q:=\frac54\,2^q+\frac{107\,2^{2q}}{1-2^{q-1/2}}<\infty. \tag{6}
\]

The first term covers \(\tau\le2\); on \(2^j<\tau\le2^{j+1}\)
use \(2^{q(j+1)}\) times the displayed tail. This yields exactly the
geometric majorant in (6).

At a fresh odd separation, use \(Q=\min(b_S,\lambda D)\). The
preceding proof supplies

\[
 P'\le\lambda P+b_F+Q,\quad
 \mathbb E[\lambda\tau]\le27/2,\quad
 \mathbb E[Q\tau]\le179D^{3/4}.
\]

Since \(\tau\ge1\), this proves

\[
 \mathbb E[P'\tau^q]
            \le(27/2)P+F_q+179D^{3/4}.                    \tag{7}
\]

For a complete group let \(G=v+\tau\) be its duration, and
\((\bar P,\bar D)\) its odd-separation departure state. The common
block has \(\mathbb E\bar P=P+v/4\) and
\(\mathbb E\bar D^{3/4}\le D^{3/4}\).
Also the old grouped minimum drift is
\[
                \mathbb EP_{\rm next}
                    \le P/2+(49/8)L+5/4.
\]
Use \(G^q\le v^q+\tau^q\), \(v^q\le L^q\le L\),
\(L^{q+1}\le L^2\le64D^{3/4}\), and \(L\le8D^{3/4}\).
Applying (7) after the common block yields

\[
 \boxed{\mathbb E[P_{\rm next}G^q]
       \le\tfrac12PL+\tfrac{27}{2}P+608D^{3/4}+F_q.}       \tag{8}
\]

Indeed the coefficient of \(D^{3/4}\) is
\((49/8)64+(5/4)8+(27/8)8+179=608\).
All these are conditional estimates at the group-start prefix.
A terminal fusion can be included in (8); dropping its nonnegative
cost when killing the next state only strengthens the inequality.

## 3. Total-clock moments at group starts

Define
\[
 R_j=\mathbb E[P_j^g(1+T_j)^q\mathbf1_{\{j\text{ exists}\}}].
\]
The inequality
\((1+T_j+G)^q\le(1+T_j)^q+G^q\), followed by the grouped minimum
drift and (8), gives

\[
\begin{aligned}
 R_{j+1}\le{}&\tfrac12R_j
 +\tfrac{49}{8}\mathbb E[L_j(1+T_j)^q;j\text{ exists}]
 +\tfrac54\mathbb E[(1+T_j)^q;j\text{ exists}]\\
 &+\tfrac12\mathbb E[P_j^g L_j;j\text{ exists}]
 +\tfrac{27}{2}\mathbb E[P_j^g;j\text{ exists}]
 +608\mathbb E[(D_j^g)^{3/4};j\text{ exists}]
 +F_q\Pr(j\text{ exists}).
\end{aligned}                                             \tag{9}
\]

All forcing terms are summable by (4)--(5) and the finite occupation
mass. Finite telescoping, nonnegativity and monotone convergence give

\[
 \boxed{\sum_j\mathbb E[P_j^g(1+T_j)^q;j\text{ exists}]
                       <\infty\quad(0\le q<1/2).}          \tag{10}
\]

The case \(q=0\) is already in (5). The kernel proves the finite
denominator-cleared telescoping identity, not the analytic limit.
Notice that (10) uses the total elapsed clock, including earlier
excursions; it is stronger than a bound on the current group's age.

## 4. Restore every common-parity return

Equation (10) does not itself bound
\(\sum P_j(1+S_j)^q\) over all returns. Restoring a common block
would insert a further factor \(v\). Instead take a coefficient power
\(0<\theta<1\).

At step \(1\le h\le v\) in such a block,
\(\mathbb EP_h=P+h/4\). Concavity and subadditivity imply
\(\mathbb EP_h^\theta\le P^\theta+h^\theta\).
The clocks \(T+h\) and \(v\) are fixed given the group start. Thus

\[
\begin{aligned}
 \mathbb E\sum_{h=1}^v P_h^\theta(1+T+h)^q
 \le{}&L P^\theta(1+T)^q+P^\theta L^{q+1}\\
     &+L^{\theta+1}(1+T)^q+L^{q+\theta+1}.
\end{aligned}                                             \tag{11}
\]

All four group-start integrals are finite. For example, Holder gives
\[
 \int P^\theta(1+T)^q L^r
 \le\left(\int P(1+T)^q\right)^\theta
     \left(\int(1+T)^q L^{r/(1-\theta)}\right)^{1-\theta},
                                                               \tag{12}
\]
with integration over the group occupation measure. Use (10) on the
first factor and (4) on the second. The terms without \(P\) use (4)
directly. The nonfused odd-excursion ends are exactly the positive
group starts, and (12) with \(r=0\) includes them.

This proves (1). For \(\theta=0\) use the occupation clock moment (3);
for \(q=0\) the same proof or the prior coefficient budgets suffice.
The endpoint \(\theta=1\) with positive \(q\) over **all** returns is
not claimed.

## 5. Sum all image overlaps in a subcritical power norm

Restrict to even original sources. Let \(K^{\rm low}_0\) be the sum
of all lower-endpoint columns, and \(\kappa^{\rm low}_{t,a}\) the
fixed-clock/fixed-count component. The previous selected-endpoint
injection and fractional fibre rank give, for \(p>1\) and
\(\alpha=p-1\),

\[
 \|\kappa^{\rm low}_{t,a}\|_p^p
       \le p\sum_{i:t_i=t,a_i=a}2^{-t}P_i^\alpha.           \tag{13}
\]

Keep \(1<p<4/3\), so \(0<\alpha<1/3\). The atypical counts are
\[
 |a-t/2|>2\sqrt{t\log(t+2)}.
\]
Their full binary probability is at most \(2(t+2)^{-8}\), by the
earlier binomial argument. At a return \(P\le C_t\), where
\(C_t=(3^{a_t}+N_t)/2^t\) is the first endpoint's formal coefficient.
The selected endpoint has the same count as that first endpoint;
both facts have new kernel checks.

Combining at most \(t+1\) atypical components, applying Holder with
the existing uniform fixed-clock half-moment of \(C_t\), yields
\[
 \|\psi_t\|_p^p
   \le p(t+1)^\alpha
           \mathbb E[C_t^\alpha\mathbf1_{\rm atypical}]
   \ll_p(t+2)^{17\alpha-8}.                               \tag{14}
\]
Here \((17\alpha-8)/p<-1\), so \(\sum_t\|\psi_t\|_p<\infty\).
Discarding the return indicator is a nonnegative upper bound, not a
conditional binomial assertion.

For a dyadic clock block \(H\le t<2H\), the typical components number
at most \(8H^{3/2}\sqrt{\log(2H+2)}\). Choose
\[
                        3\alpha/2<q<1/2.
\]
Use the finite power-sum inequality, (13), and (1) to obtain
\[
\begin{aligned}
 \|\Delta_H\|_p^p
 &\le p\{8H^{3/2}\sqrt{\log(2H+2)}\}^\alpha
               \int_{H\le S<2H}P^\alpha\,d\nu\\
 &\ll_{p,q} H^{3\alpha/2-q}
                     (1+\log(H+1))^{\alpha/2}.
\end{aligned}                                             \tag{15}
\]
The power is negative. Finite Minkowski and then monotone convergence
show that the full sum, including products between different
components, belongs to \(L^p\). This proves the unweighted case of
(2). It is an upper bound in a norm below two, not an \(L^2\)
conclusion inferred from separate component squared norms.

The same argument for the tail gives
\[
 \|K^{\rm low}_0-K^{\rm low}_{0,H}\|_p
       =O_{p,\delta}(H^{-\delta})
 \quad\left(0<\delta<\frac{4-3p}{2p},\ 1<p<4/3\right).      \tag{16}
\]
The atypical part decays faster: summing (14) gives power
\(-(7-18\alpha)/p\), which is more negative than
\(-(1-3\alpha)/(2p)\) throughout this range. Logarithmic factors
in (15) are absorbed by the strict margin in (16).

## 6. Separation weights, finite sampling, and the remaining gap

Use \(K^{\rm low}_\beta=\sum_i p_iD_i^\beta F_i^{\rm low}\).
For \(0\le\beta<\gamma<1\), the earlier separation moment gives
\(K^{\rm low}_\gamma\in L^1\), because each column has integral one.
Holder within the column sum gives pointwise
\[
 K^{\rm low}_\beta\le
       (K^{\rm low}_0)^{1-\beta/\gamma}
       (K^{\rm low}_\gamma)^{\beta/\gamma}.
\]
Combine with the unweighted \(p<4/3\) result and let the allowed
parameters approach \(4/3\) and one from below. This proves (2),
without claiming the boundary exponent. The previously proved
infinite first separation moment also shows that
\(K^{\rm low}_\beta\notin L^1\) for \(\beta\ge1\).
Changing the endpoint does not change these column masses.

At a finite cutoff \(H\), the density is periodic modulo \(3^H\).
For every integer interval \(I\) of length \(M\ge1\), its nonnegative
power obeys the finite counting bound
\[
 \frac1M\sum_{n\in I}(K^{\rm low}_{\beta,H}(n))^p
       \le(1+3^H/M)\int(K^{\rm low}_{\beta,H})^p\,d\mu_3.   \tag{17}
\]
Thus (2) gives bounded truncated moments when \(3^H/M\) stays
bounded. Neither (16) nor (17) permits sending \(H\) to infinity
at a fixed integer interval. No infinite-cutoff integer trace bound
is asserted.

For the unweighted lower density, a complementary power greater
than four could now suffice in a suitable Holder pairing. No such
bound on the actual accumulated gradients has been proved, nor has
the required transfer on their actual integer progressions. Full
\(L^2\), criterion Q, bounded actual energy, escape exclusion and
additional-cycle exclusion remain open.

## Verification

Run `python3 verify_lower_return_clock_moments.py`. The accompanying
[record](../results/lower-return-clock-moments/verification.json).
It authenticates the earlier inputs, compiles the new kernel arithmetic,
checks actual grouped clock moments and common-block powers with exact
rational enclosures, and computes full finite lower-image power moments,
including their overlaps. Unfinished paths remain unfinished; these
finite checks are not proofs of the infinite moments or norms.
