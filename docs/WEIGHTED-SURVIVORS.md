# Weighted survivor mass and the missing contraction estimate

**Status: a conditional route to the full Collatz conjecture, which remains
unresolved.** The exact integer inverse branches, finite inverse-cone
characterization, and convergent base through 64 are kernel checked in
[WeightedSurvivors.lean](../lean/WeightedSurvivors.lean). The infinite-sum
arguments below are written proofs. The accompanying exact Python checks
certify finitely many mass estimates, not an all-time bound. No novelty is
asserted.

The research lead was the public [aggregate Mellin transport note](https://github.com/GettysburgResearch/collatz/blob/main/research/astra-three-routes/ROUTE1_MELLIN.md),
read on 2026-10-09. Its definitions, proposed 69/200 bound, and finite
counterexample to a one-third bound are reconstructed here independently;
no foreign code or theorem is imported. The distinction between exponential
decay and merely vanishing mass, and the recurrent-contraction criterion
below, determine which missing estimate to pursue.

## 1 Exact transport above a fixed floor

Use the shortcut map
\[
 U(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd}.\end{cases}
\]
Fix an integer \(H\ge1\) and define
\[
 \tau_H(n)=\inf\{j\ge0:U^j(n)\le H\},\qquad
 \chi_k(n)=\mathbf1_{\{\tau_H(n)>k\}},\qquad
 M_k=\sum_{n\ge1}\chi_k(n)n^{-s},\quad s>1.
\]
An infinite hitting time is allowed. Each sum is finite because it is
bounded by \(\zeta(s)\). The survivor sets decrease with \(k\), so
\(M_{k+1}\le M_k\). They have positive mass: \(U(n)\ge n/2\), hence
every \(n>2^kH\) survives to time \(k\).

The even predecessor of \(y>H\) is \(2y\). Its odd predecessor exists
exactly when \(y\equiv2\pmod3\), and is \((2y-1)/3\). This predecessor
is above the floor exactly when \(2y>3H+1\). Consequently
\[
 M_{k+1}=2^{-s}M_k+(3/2)^s\widetilde Q_k,\tag{1}
\]
where
\[
 \widetilde Q_k=
 \sum_{\substack{y>(3H+1)/2\\y\equiv2\pmod3}}
       \chi_k(y)y^{-s}(1-1/(2y))^{-s}.
\]
This is a partition of nonnegative summands into the two actual inverse
branches; it uses neither randomness nor residue independence. The exact
cutoff and affine correction are retained.

Let \(a_H\) be the smallest eligible endpoint and remove the correction
to define
\[
 Q_k=\sum_{\substack{y\ge a_H\\y\equiv2\pmod3}}\chi_k(y)y^{-s}.
\]
Then
\[
 Q_k\le\widetilde Q_k\le c_H Q_k,\qquad
 c_H=(1-1/(2a_H))^{-s}.\tag{2}
\]

## 2 Vanishing mass is equivalent to reaching the floor

For any \(s>1\),
\[
 M_k\longrightarrow0
 \quad\Longleftrightarrow\quad
 \tau_H(n)<\infty\text{ for every positive }n.\tag{3}
\]
If an eternal survivor \(n\) exists, its fixed weight \(n^{-s}\) occurs
in every \(M_k\), excluding the limit zero. Conversely, for any
\(\varepsilon>0\), choose \(R\) with
\(\sum_{n>R}n^{-s}<\varepsilon\). If every start hits the floor, finitely
many hitting times for \(n\le R\) have a finite maximum. Beyond it,
\(M_k<\varepsilon\). This proves (3) without a uniform stopping bound.

For \(H=64\), every positive start at or below the floor reaches one.
The kernel certificate allows at most 71 shortcut steps; an independent
Python replay checks the first hitting times. Thus (3), for this fixed
floor, is equivalent to the full positive-integer conjecture. The weighted
formulation does not remove its pointwise difficulty.

## 3 The unconditional bias bound reaches a critical value

Put
\[
 \kappa_s=\frac{2^s-1}{3^s},\qquad
 d_k=\kappa_s-\frac{\widetilde Q_k}{M_k},\qquad
 \epsilon_k=1-\frac{M_{k+1}}{M_k}.
\]
Equation (1) and nested survival give the exact identities and bounds
\[
 \epsilon_k=(3/2)^s d_k,\qquad
 0<\epsilon_k\le1-2^{-s}<1,\qquad
 \frac{\widetilde Q_k}{M_k}<\kappa_s.\tag{4}
\]
For strict positivity, \(n=2^{k+1}H\) survives through time \(k\) and
first reaches the floor at time \(k+1\). Its weight is lost, so
\(M_{k+1}<M_k\). The weak upper bound in (4) follows from the even
predecessor contribution alone. In particular,
\[
 \epsilon_k\ge\frac{(2^{k+1}H)^{-s}}{M_0}.\tag{5}
\]
The right side is summable in \(k\); this lower bound cannot force the
needed cumulative loss to diverge.

More exactly, multiplying the successive mass ratios gives
\[
 \frac{M_k}{M_0}=\prod_{j<k}(1-\epsilon_j),\qquad
 e^{-2^s\sum_{j<k}\epsilon_j}
 \le\frac{M_k}{M_0}\le e^{-\sum_{j<k}\epsilon_j}.\tag{6}
\]
The exponential inequalities follow by integrating \(1/(1-t)\) between
zero and \(\epsilon_j\), where it lies between 1 and \(2^s\).
Thus vanishing mass is equivalent to
\[
 \sum_{k\ge0}d_k=\infty.\tag{7}
\]
Strict loss at each finite time is insufficient. If eternal survivors
have positive limiting mass, (1) instead forces
\(\widetilde Q_k/M_k\to\kappa_s\), with a finite total deficit.
The unconditional inequality in (4) therefore stops precisely at the
critical value; it supplies no positive uniform gap.

## 4 Contraction at recurrent horizons is sufficient

Suppose that for some \(\eta>0\) there are infinitely many indices with
\[
 \widetilde Q_k/M_k\le\kappa_s-\eta.\tag{8}
\]
At each such index (1) contracts the mass by at least
\(1-(3/2)^s\eta<1\). At all other indices the mass is nonincreasing.
Hence (8) implies (7), and every start reaches the floor. No positive
frequency of the selected indices is required. This is weaker than
requiring the same gap at every sufficiently large index.

A concrete sufficient instance, retaining the affine correction, is
\[
 H=64,\quad s=3/2,\quad a_H=98,\qquad
 Q_k\le\frac{69}{200}M_k
 \text{ for infinitely many }k.\tag{9}
\]
At any index satisfying (9), (1) and (2) imply
\[
 \frac{M_{k+1}}{M_k}
 \le\frac1{\sqrt8}+\frac{69}{200}(98/65)^{3/2}
 <\frac{177}{500}+\frac{69}{200}\frac{463}{250}
 =\frac{49647}{50000}<\frac{993}{1000}.\tag{10}
\]
The strict root comparisons and final rational comparison are kernel
checked as integer inequalities. For \(G(k)\) good indices below \(k\),
\(M_k\le M_0(993/1000)^{G(k)}\). Unbounded \(G(k)\) suffices.
Neither (8) nor (9) is proved for infinitely many horizons here.

Ignoring the affine correction only to identify the arithmetic window,
a one-third share would give
\[
 2^{-s}+(3/2)^s/3<1\qquad(1<s<2).
\]
Indeed \(\log(1+3^{s-1})-s\log2\) is strictly convex and zero at both
endpoints. This calculation does not supply the survivor-conditioned
one-third bound. The finite replay below disproves that bound.

## 5 Exponential mass decay has a stronger stopping-time meaning

For fixed \(H\) and \(s>1\), the following two existence statements are
equivalent:

1. There are \(C\ge1,\delta>0\) such that
   \(M_k\le Ce^{-\delta k}\) for all \(k\).
2. There are \(A>0,B\ge0\) such that
   \(\tau_H(n)\le A\log n+B\) for every positive \(n\).

For the first implication, (3) first gives finite hitting times. For
\(\tau_H(n)\ge1\), take \(k=\tau_H(n)-1\). Survival then gives
\[
 n^{-s}\le M_k\le Ce^{-\delta k},\qquad
 \tau_H(n)\le1+\frac{s\log n+\log C}{\delta}.\tag{11}
\]
The zero hitting times also satisfy this bound.

Conversely, a survivor at time \(k\ge B\) must satisfy
\(n>R=\exp((k-B)/A)\). For \(R\ge1\), monotonicity and an integral
bound give
\[
 M_k\le\sum_{n>R}n^{-s}
 \le R^{-s}+\frac{R^{1-s}}{s-1}
 \le\frac{s}{s-1}e^{-(s-1)(k-B)/A}.\tag{12}
\]
Enlarging the constant covers \(k<B\).

An eventual uniform ratio bound \(M_{k+1}\le\rho M_k\), \(\rho<1\),
therefore requires a worst-case logarithmic hitting bound. The converse
above yields an exponential envelope, not a bound on every successive
ratio. Recurrent contraction at arbitrarily sparse horizons has no such
logarithmic-time implication. Pursuing (9) only infinitely often avoids
assuming the stronger timing conclusion.

## 6 Pointwise power weights cannot prove this contraction

Define killed inverse transfer by
\[
 (L_Hw)(y)=\sum_{\substack{n>H\\U(n)=y}}w(n),\qquad y>H.
\]
There is no positive weight comparable to a fixed decreasing power,
\[
 c n^{-s}\le w(n)\le C n^{-s}\quad(n>H),\qquad c,C>0,\ s>0,
\]
that satisfies \(L_Hw\le\rho w\) everywhere for \(0<\rho\le1\).
The comparison factors may vary arbitrarily with \(n\) within these
bounds; periodicity is not assumed.

To prove this, choose \(K\) large and an integer \(q\ge H+1\). The
all-odd path starting at \(x_0=2^Kq-1\) stays above \(H\), with
\(x_K=3^Kq-1\); the universal growth formula is already kernel checked
in [CollatzGrowth.lean](../CollatzGrowth.lean). Each inverse inequality
implies \(w(x_i)\le\rho w(x_{i+1})\), hence
\[
 c x_0^{-s}\le\rho^K C x_K^{-s},\qquad
 (x_K/x_0)^s\le(C/c)\rho^K.
\]
But \(x_K/x_0\ge(3/2)^K\), contradicting this for large \(K\).
This written obstruction concerns a pointwise transfer inequality.
It does not obstruct contraction averaged over the actual survivor set.

## 7 Finite exact replay and its scope

Let \(A_{H,k}=\{n\ge1:\tau_H(n)\le k\}\). The kernel proves this is
the finite inverse cone generated from \(1,\ldots,H\), and that
\(A_{H,k}\subseteq[1,2^kH]\). The Python implementation removes
duplicates and explores only the new frontier. Thus
\[
 M_k=\zeta(3/2)-\sum_{n\in A_{64,k}}n^{-3/2},
\]
and \(Q_k\) is the full eligible progression sum minus its absorbed
members. No source cutoff is mistaken for the full survivor population.

All numerical endpoints use denominator \(B=2^{96}\). For every term,
the integer \(a=\lfloor\sqrt{B^2/n^3}\rfloor\) is checked by squaring
and gives \(a/B\le n^{-3/2}<(a+1)/B\). Infinite tails use only the
monotone-integral bounds
\[
 \frac2{\sqrt{N+1}}\le\sum_{n>N}n^{-3/2}\le\frac2{\sqrt N},
\]
\[
 \frac2{3\sqrt m}\le\sum_{j\ge0}(m+3j)^{-3/2}
 \le m^{-3/2}+\frac2{3\sqrt m}.
\]
Here \(N=65536\), and \(m\) is the first eligible endpoint above it.
Square-root bounds are directed outward using integer arithmetic. These
analytic integral inequalities are written inputs, not Lean theorems.

The [replay](../verify_weighted_survivors.py) reconstructs all 37 cones
for \(0\le k\le36\). At \(k=19\), exact intervals establish
\(3Q_{19}>M_{19}\), while the reverse strict inequality holds at each
earlier tested depth. All 37 depths satisfy \(200Q_k<69M_k\).
There are 18,847 absorbed starts at depth 19 and 2,510,783 at depth 36.
These are finite tests of a conditional premise, not evidence of an
eternal Collatz survivor and not proof of its infinite recurrence.

Separate forward simulation checks all starts through \(2^{18}\), plus
samples across every inverse frontier, against their exact absorption
depths. The [verification record](../results/weighted-survivors/verification.json)
distinguishes kernel results, Python arithmetic, written analysis, and
the still-unproved global estimate. Reproduce with
`python3 verify_weighted_survivors.py`.

The next substantive step is an arithmetic reason that the positive
deficits in (7) cannot have a finite sum. One possible sufficient target
is recurrent bias separation (9). Finite-depth positivity, unconditioned
residue equidistribution, and the density estimates in
[DENSITY-TO-POINTWISE.md](DENSITY-TO-POINTWISE.md) do not establish it.
