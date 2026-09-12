# Quantitative escape required of a divergent orbit

This note strengthens the running-maximum and summability restrictions in
[`APERIODIC-ATTEMPT.md`](APERIODIC-ATTEMPT.md). It does not exclude every
divergent trajectory or establish cycle uniqueness. The general counting,
real-analysis, and asymptotic arguments below are written proofs. The finite
fixed-weight ingredient is checked in [`CollatzPacking.lean`](CollatzPacking.lean);
the two optional integer comparisons in Section 5 are checked separately in
[`CollatzEscapeBounds.lean`](CollatzEscapeBounds.lean). No novelty is claimed.

Use the shortcut map U(n)=(3n+1)/2 on odd n and U(n)=n/2 on even n.
Let O be the set of values of a nonrepeating positive integer U-orbit.
Every fixed iterate U^ell is injective on O: a collision would be a later
repeat in the original orbit.

## 1. An optimized elementary packing exponent

For 0<p<1 define the binary entropy in natural logarithms by

\[
 h(p)=-p\log p-(1-p)\log(1-p).
\]

There is a unique tau in (1/2,1) with h(tau)=tau log 3. Indeed h decreases
strictly on this interval, tau log 3 increases strictly, and their endpoint
order reverses. Set

\[
 \theta=\frac{h(\tau)}{\log2}=\tau\log_2 3<1.
 \tag{1}
\]

For orientation, tau is approximately 0.60909, theta approximately 0.96538,
and 1/theta approximately 1.03586. The proof uses definition (1), not these
rounded numerical values or an external assertion of an optimal exponent.

Fix ell and an aligned block [q2^ell,(q+1)2^ell). There are exactly
binomial(ell,j) residues of parity weight j. On that class the affine identity
and sharp residue-image bound give

\[
 U^\ell(q2^\ell+s)=3^j q+U^\ell(s),\qquad 0\le U^\ell(s)<3^j.
\]

Injectivity therefore bounds the contribution of weight j by
min{binomial(ell,j),3^j}. Both the affine identity and the sharp image bound
are locally checked finite theorems. Parity-word counting is derived in
Section 2 of the earlier note; it has not been formalized here.

Take J=ceil(tau ell) and z=tau/(1-tau)>1. The low weights contribute at most

\[
 \sum_{j<J}3^j=\frac{3^J-1}{2}
 \le\frac32\,3^{\tau\ell}=\frac32\,2^{\theta\ell}.
\]

The high weights contribute at most

\[
 \sum_{j\ge J}\binom\ell j
 \le z^{-J}(1+z)^\ell
 \le\left(z^{-\tau}(1+z)\right)^\ell
 =\exp(h(\tau)\ell)=2^{\theta\ell}.
\]

Thus each aligned block contains at most (5/2)2^(theta ell) orbit values.
For any real X>=1, choose ell=ceil(log_2 X). An interval of length X meets
at most two aligned blocks of length 2^ell, and 2^ell<=2X. Consequently

\[
 \boxed{\#(O\cap[a,a+X))\le10X^\theta
 \qquad(a\ge0,\ X\ge1).}
 \tag{2}
\]

This optimizes the threshold in the specific two-part estimate. It does not
assert that theta is the smallest possible exponent for actual Collatz orbits.

## 2. Inverse-power sums, including the cumulative multiplier

For any real s>theta, dyadic shells and (2) give the uniform estimate

\[
 \sum_{x\in O}x^{-s}
 \le10\sum_{r\ge0}2^{(\theta-s)r}
 =\frac{10}{1-2^{\theta-s}}<\infty.
 \tag{3}
\]

Each shell [2^r,2^(r+1)) has length 2^r, so (2) applies directly.
The sum counts distinct orbit values, which are exactly the time-indexed
values under the nonrepetition assumption.

For the accelerated odd subsequence write

\[
 2^{h_k}n_{k+1}=3n_k+1,\quad H_k=\sum_{i<k}h_i,\quad
 A_k=\frac{3^k}{2^{H_k}},\quad
 P_k=\prod_{i<k}\left(1+\frac1{3n_i}\right).
\]

The exact identity n_k=n_0 A_k P_k and (3) at s=1 imply

\[
 1\le P_k\le P_\infty<\infty,
 \qquad\boxed{\sum_{k\ge0}A_k^{-s}<\infty\quad(s>\theta).}
 \tag{4}
\]

Indeed P_k is increasing, log P_k<=sum_i 1/(3n_i), and
A_k^(-s)=(n_0P_k)^s n_k^(-s). The finite constant can depend on n_0.
For s=1 the product has the additional exact telescoping identity

\[
 P_{k+1}-P_k=\frac{1}{3n_0A_k},\qquad
 \sum_{k\ge0}A_k^{-1}=3n_0(P_\infty-1).
 \tag{5}
\]

In particular, merely prescribing A_k to tend to infinity is insufficient.
For example A_k=O(k log(k+2)) is impossible for a nonrepeating integer orbit:
it would make the sum in (5) diverge. Equation (4) is stronger still.

## 3. A lower bound on the running maximum

Let M_N=max_{0<=k<=N} A_k and B=n_0 P_infty M_N. All N+1 odd states
n_0,...,n_N are distinct positive integers and are <=B. Applying (2) to
[0,B+1), and using B>=1, yields

\[
 N+1\le10(B+1)^\theta\le20B^\theta.
\]

Therefore

\[
 \boxed{M_N\ge\frac1{n_0P_\infty}
       \left(\frac{N+1}{20}\right)^{1/\theta}.}
 \tag{6}
\]

This is a running-maximum statement, not a lower bound on every individual
n_k or A_k. A nonrepeating orbit can have large downward excursions without
violating this estimate. In terms of halving discrepancy it says

\[
 \max_{0\le k\le N}(k\log_2 3-H_k)
 \ge\theta^{-1}\log_2(N+1)-C(n_0).
 \tag{7}
\]

Consequently any positive integer orbit satisfying A_k=O(k^beta) for a
fixed beta<1/theta eventually repeats. This replaces the earlier beta<8/9
criterion by an exponent exceeding one. If additionally H_k/k tends to
log_2 3, repetition is also impossible: a positive cycle has mean halving
exponent strictly greater than log_2 3. Thus critical-mean schedules with
this polynomial upper growth have no positive integer realization at all.

For any increasing positive envelope F with sum_k F(k)^(-s)=infinity for
some s>theta, equation (4) also rules out an eventual bound A_k<=F(k).
This includes nonpolynomial envelopes without needing a separate drift model.

## 4. Why this still does not yield a contradiction

Neither packing nor parity integrality currently provides an upper bound
A_k=O(k^beta) for every positive orbit, at any fixed beta. The elementary
upper bound is exponential. Exponential growth satisfies (4), (6), and (7).
The complexity restrictions in [`COMPLEXITY-GROWTH.md`](COMPLEXITY-GROWTH.md)
also allow sufficiently complicated words with positive exponential drift.

Conversely, an abstract real sequence that satisfies these inequalities is
not an integer Collatz trajectory. Proving that every remaining parity word's
two-adic candidate fails to be a positive integer is still the missing step.
No change of metric or exchange of finite-prefix and infinite quantifiers
is justified by the estimates above.

## 5. An exact rational-exponent alternative

The use of logarithms in defining theta is optional. Set ell=18r and split
at j=11r. The same two sums are bounded by

\[
 \frac12(3^{11})^r
 +\left(\frac{18^{18}}{11^{11}7^7}\right)^r.
\]

The exact positive-integer inequalities

\[
 3^{352}<2^{558},\qquad
 18^{576}<2^{558}11^{352}7^{224}
\]

show that both bases are smaller than 2^(18*31/32). Scaling intervals through
powers of 2^18 gives a uniform bound C X^(31/32), with a fixed finite C.
Hence a completely rational exponent suffices for all conclusions above
with theta replaced by 31/32: summability for s>31/32 and repetition whenever
A_k=O(k^beta) with beta<32/31. `CollatzEscapeBounds.lean` checks these two
integer inequalities in Lean's kernel; it does not certify the surrounding
entropy argument, interval counting, real powers, infinite sums, or limits.

The packing method builds on the finite collision mechanism associated with
[Garcia–Tal, *A note on the generalized 3n+1 problem* (1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf).
All specialized estimates needed for the conclusions here are given above.
