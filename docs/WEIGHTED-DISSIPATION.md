# An exact loss identity and its unresolved escape mass

**Status: finite integer identities are kernel checked; the infinite-product
arguments are written. The natural-density limits additionally depend on
the existing written first-passage premise. Collatz remains unresolved.**

This note uses the actual ordinary Collatz map, including the exact odd
formula `3n+1`. It constructs a probability distribution of the accumulated
relative `+1` correction. Its mass at infinity detects divergence, but no
argument here proves that this mass is zero. Additional positive cycles
would require a separate exclusion even if it were zero.

## 1. Exact accounting on every finite path

Put \(x_j=C^j(n)\), for \(n>0\), and define
\[
 W_0(n)=1,\qquad
 W_{j+1}(n)=
 \begin{cases}
 W_j(n)\,3x_j/(3x_j+1),&x_j\text{ odd},\\
 W_j(n),&x_j\text{ even}.
 \end{cases}
\]
The loss at time \(j\) is
\[
 \ell_j(n)=\mathbf1_{x_j\text{ odd}}\frac{W_j(n)}{3x_j+1}.
\]
These quantities satisfy, without any distinctness assumption,
\[
 \boxed{W_T(n)+\sum_{j<T}\ell_j(n)=1.}                 \tag{1}
\]
Repeated visits contribute separately. If \(o_T,e_T\) count odd and
even ordinary inputs, respectively, the actual affine formula also gives
\[
 \boxed{W_T(n)=\frac{n3^{o_T}}{2^{e_T}C^T(n)}.}         \tag{2}
\]
For concatenated paths,
\[
 W_{s+t}(n)=W_s(n)W_t(C^s(n)),
\]
and the loss of the concatenation is the first loss plus \(W_s(n)\)
times the loss of the suffix.

[WeightedDissipation.lean](../lean/WeightedDissipation.lean) checks
integer versions of these statements. Its positive integers \(A_T,B_T\)
are the numerator and denominator products, and \(L_T\) is a recursively
accumulated common-denominator loss. The kernel proves
\(A_T+L_T=B_T\), the concatenation identities, and
\(B_TP_Tn=A_TQ_TC^T(n)\), where \(P_T,Q_T\) are the products of
the odd factor three and even factor two. Identifying those products
with the powers in (2) is an elementary written step. It also proves that a positive
return contains an odd step, has strictly positive loss, and repeats its
weight geometrically. Division into real numbers and all limits below
are written steps, not additional kernel claims.

## 2. The remaining weight is positive exactly on divergent orbits

Since \(0<W_{T+1}\le W_T\le1\), the limit
\(W_\infty(n)=\lim_TW_T(n)\) exists. A positive orbit is either
eventually periodic or injective and unbounded. In the periodic case,
each complete cycle multiplies its weight by a fixed \(\beta\in(0,1)\),
so \(W_\infty(n)=0\).

In the injective case, the distinct odd states satisfy the existing
[finite-path packing bound](FINITE-PATH-PACKING.md). Its reciprocal
estimate gives
\[
 \sum_{j:x_j\text{ odd}}\frac1{x_j}\le8192,
 \qquad
 -\log W_\infty(n)
 =\sum_{j:x_j\text{ odd}}\log\left(1+\frac1{3x_j}\right)
 \le8192/3.
\]
Finite prefixes give the inequalities first; monotone limits then give
\[
 \boxed{e^{-8192/3}\mathbf1_{\rm div}(n)
       \le W_\infty(n)\le\mathbf1_{\rm div}(n).}       \tag{3}
\]
The constant is deliberately loose. This does not establish that a
divergent orbit exists, or that none exists. Infinite repetition of a
cycle is not covered by distinct-state packing; its geometric loss was
handled separately.

Define a probability measure on the countable set of positive odd
integers together with a separate symbol \(\infty\):
\[
 \mu_n(\{N\})=\sum_{j:x_j=N}\ell_j(n),\qquad
 \mu_n(\{\infty\})=W_\infty(n).                        \tag{4}
\]
Nonnegative summation and (1) prove that its mass is exactly one. The
symbol represents weight that is never lost; it is not a finite state
of the Collatz map.

For any finite time \(i\), let \(\zeta_{n,i}\) allocate the losses
before \(i\) to their odd states. Then
\[
 \mu_n=\zeta_{n,i}+W_i(n)\mu_{C^i(n)},\qquad
 \zeta_{n,i}(\text{all states})=1-W_i(n).
\]
Consequently
\[
 d_{\rm TV}(\mu_n,\mu_{C^i(n)})\le1-W_i(n).           \tag{5}
\]
This remains valid if the prefix and suffix visit common states.

If \(i\) is the first odd passage to a value at most \(H\), the
prefix before passage is simple and all its odd inputs exceed \(H\).
The reciprocal packing bound and the finite product inequality yield
\[
 1-W_i(n)\le\sum_{j<i:x_j\text{ odd}}\frac1{3x_j+1}
                 \le\varepsilon_H:=\frac{8192}{3}H^{-1/20}.
                                                               \tag{6}
\]
Only the odd inputs are required to exceed \(H\). Intermediate even
values need not do so. For small floors the bound can exceed one.

## 3. Conditional total-variation limit and a charge identity

Assume the written Proposition 4.1 of
[NATURAL-DENSITY-ALMOST-BOUNDED.md](NATURAL-DENSITY-ALMOST-BOUNDED.md).
There is a probability measure \(\mu\) on the same countable set with
\[
 \boxed{d_{\rm TV}\left(\frac1X\sum_{1\le n\le X}\mu_n,\mu\right)
                         \ll(\log X)^{-c}}             \tag{7}
\]
for integer \(X\to\infty\) and some \(c>0\).

Here is the extension of the earlier
[minimum-law argument](DENSITY-TO-POINTWISE.md). At nearby odd source
scales \(Y\le Z\le Y^\alpha\), use first passage at
\(H=Y^{1/\alpha}\). On successful passage (5)--(6) replace each
\(\mu_n\) by the measure of its landing, with error at most
\(\varepsilon_H\). Assign any fixed probability measure to nonentry.
Mixing the landing measures is a Markov kernel and contracts total
variation. The passage failure probabilities and passage-law comparison
therefore bound the difference between the two averaged measures by
\(O((\log Y)^{-c})\). The power error in (6) is smaller.

Telescoping along \(Y,Y^\alpha,Y^{\alpha^2},\ldots\) is summable.
The space of countably additive probability measures on this countable
set is complete in total variation: each fixed reference probability
measure has an arbitrarily large finite head, and the Cauchy estimate
transfers that head bound to later measures. Unlike the minimum law, a
reference \(\mu_n\) need not have finite support; tightness of each
individual countable probability measure is sufficient. Odd dyadic
decomposition and removal of initial powers of two finish (7), since
\(\mu_{2n}=\mu_n\) exactly.

For an odd target \(N\), let \(w_N(n)\) be the weight at its first
visit, and zero if it is never reached. Let
\[
 B_N=\begin{cases}
 1,&N\text{ is nonperiodic},\\
 (1-\beta_N)^{-1},&N\text{ is on a cycle},
 \end{cases}
\]
where \(\beta_N\) is the weight of one full return cycle. A
nonperiodic target is visited at most once. A periodic target is visited
once per cycle after its first hit. Thus the exact pointwise identity is
\[
 \mu_n(\{N\})=\frac{B_N}{3N+1}w_N(n).                 \tag{8}
\]
Equation (7) proves existence of the natural weighted first-hit mean
\[
 D_N=\lim_{X\to\infty}\frac1X\sum_{n\le X}w_N(n).
\]
It also equals its logarithmic mean by partial summation. Distinct-path
packing gives \(e^{-8192/3}r_N\le D_N\le r_N\), including periodic
targets, because only the path before the first hit enters the weight.
Taking coordinates in (7), and using the mass-one limit, now gives
\[
 \boxed{d+\sum_{N\ge1,\ N\text{ odd}}\frac{B_ND_N}{3N+1}=1,
 \qquad d=\lim_{X\to\infty}\frac1X\sum_{n\le X}W_\infty(n).}
                                                               \tag{9}
\]
This exchange of the infinite target sum and the source limit is
justified by total variation, not by coordinatewise convergence alone.
In particular the nonnegative series converges and is at most one.
For the known cycle, \(B_1=4\), so the term at \(N=1\) is \(D_1\).
That factor must not be omitted.

If \(\Lambda_{\rm div}\) denotes the density of all divergent starts,
the earlier countable component law and (3) give
\[
 e^{-8192/3}\Lambda_{\rm div}\le d\le\Lambda_{\rm div}.
\]
The independently replayed [external predecessor theorem](PREDECESSOR-DENSITY-REVIEW.md)
makes \(\Lambda_{\rm div}>0\) whenever any divergent positive orbit
exists: such an orbit reaches a positive unit target, and every
predecessor of that target also diverges. Hence, with these inputs,
\[
 d=0\quad\Longleftrightarrow\quad
 \text{every positive orbit is eventually periodic}.    \tag{10}
\]
**The assertion that the series in (9) equals one is unproved.** Formula
(9) identifies the missing mass; it does not remove it. Eventual
periodicity would still allow additional positive cycles.
External positivity at one does give \(D_1>0\), hence \(d\le1-D_1<1\).

## 4. A finite logarithmic clock measures the same unresolved mass

Let \(\kappa=3/\log(4/3)\). Under the additional written clock result
in [CLOCKED-MINIMUM.md](CLOCKED-MINIMUM.md), for each fixed \(c\ge0\)
away from \(\kappa\),
\[
 \boxed{\frac1X\sum_{n\le X}W_{\lfloor c\log X\rfloor}(n)
    \longrightarrow
    \begin{cases}1,&c<\kappa,\\ d,&c>\kappa.\end{cases}}       \tag{11}
\]
The same statement holds with the individual clock \(\lfloor c\log n\rfloor\).
No assertion is made at the critical coefficient or about an effective
rate.

For \(c<\kappa\), a fixed finite set of odd states \(\{N\le H\}\)
is reached by the clock from a density-zero set of starts, by the
earlier fixed-target clock theorem. On the remaining starts the prefix
is simple unless it is already on a cycle entirely above \(H\).
Such cyclic starts are included among those whose eventual global
minimum exceeds \(H\), apart from prefixes that have not yet completed
their first return. The latter prefixes are simple. The minimum-law
tail bounds the former set and tends to zero with \(H\).
On the simple prefixes, (6) bounds the lost weight by
\(\varepsilon_H\). First let \(X\to\infty\), then \(H\to\infty\),
to get the first limit. This cycle exception is necessary; absence of
a small hit by the clock alone does not guarantee a simple prefix.

For \(c>\kappa\), choose \(\kappa<c'<c\). Outside a set whose
limiting density is at most the minimum-law tail above \(H\), the
global minimum is some \(m\le H\) and is attained by \(c'\log n\).
There are finitely many such \(m\). Each decreasing sequence
\(W_t(m)\) converges to \(W_\infty(m)\), so convergence is uniform
over this finite set, without deciding which of its orbits diverge.
The remaining time tends to infinity. The cocycle therefore bounds
\(W_{\lfloor c\log n\rfloor}(n)-W_\infty(n)\) by a quantity tending
to zero on the good set. Boundedness and then \(H\to\infty\) prove
the second limit. The population clock follows from monotonicity and
discarding \(n\le X^\rho\) in the lower-clock case, with
\(c/\kappa<\rho<1\).

There is also a simpler order-of-limits warning. For each fixed finite
\(T\), \(C^j(n)\ge n/2^j\) and
\(1-W_T(n)\le(2^T-1)/(3n)\), so its mean tends to zero. Consequently
\[
 \lim_{T\to\infty}\lim_{X\to\infty}\frac1X\sum_{n\le X}W_T(n)=1,
 \qquad
 \lim_{X\to\infty}\lim_{T\to\infty}\frac1X\sum_{n\le X}W_T(n)=d.
\]
Under the stated inputs these two limits differ, since \(d<1\).
Finite-time persistence of weight is not evidence of a divergent orbit.

## 5. Source review and verification scope

The related public [basin-density manuscript](https://github.com/x1xhlol/collatz-two-coordinate-obstruction/blob/main/paper/tao-basin-densities.tex)
uses weighted first-hit densities and cycle factors, and gives a lower
bound for their uncapped occupation sum. It explicitly leaves the
matching upper bound open. Its claimed uniform reciprocal density bound
and inverse-path clock have not been replayed here and are not inputs to
this note. The downloaded source's SHA-256 is recorded for provenance.
No novelty is claimed for correction products or weighted densities.

The [verification record](../results/weighted-dissipation/verification.json)
separates 18 audited kernel roots, independent exact rational checks,
and the conditional written limits. The replay checks the integer
certificates against forward rational sums, the affine identity,
concatenation, known-cycle repetition, full loss distributions for
completely resolved sample paths, and passage-mixture inequalities.
Finite population-clock means are enclosed by rational intervals. None
of those intervals estimates the unknown limiting mass with a certified
asymptotic error. Every sampled infinite distribution uses an explicitly
verified path to the known cycle; no timeout is classified as divergence.

The replay covers 2,048 complete source paths, 138,104 exact forward
prefixes, 1,092 independently evaluated reverse certificates, 4,352
cycle repetitions, and 5,120 passage comparisons. It also checks 436,800
finite source-clock pairs. At \(X=65536\), the mean remaining weights
at ordinary clocks 44, 88, 121, and 177 are approximately 0.92162543,
0.57855998, 0.38637200, and 0.11060250, respectively. These correspond
to coefficients 4, 8, 11, and 16; each recorded rational interval has
width at most \(2^{-48}\). They carry no certified error relative to
\(d\) or to the limits in (11).

```sh
python3 verify_weighted_dissipation.py
```
