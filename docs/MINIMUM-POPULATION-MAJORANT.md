# A kernel bound for actual population minima

**Status: 36 new kernel theorem roots prove an unconditional upper bound
for actual finite-prefix and global-minimum tail means. The population
majorant previously supplied as an explicit premise to the Green-kernel
theorems is now proved. The bound grows with the cutoff and does not
establish the uniform subunit budget or the Collatz conjecture.**

For the ordinary Collatz map, let
\[
 m_T(n)=\min_{0\le t\le T}C^t(n),\quad
 F_{H,T}(N)=\frac1N\sum_{n=1}^Nm_T(n)\mathbf1_{\{m_T(n)>H\}},
\]
and let \(G_H(N)\) be the same mean using the attained global minimum
\(m(n)=\min_{t\ge0}C^t(n)\). Put
\[
                         r=\frac{29}{15},\qquad k=\lfloor\log_2N\rfloor.
\]
For every positive cutoff \(N\), every floor \(H\ge0\), and every
ordinary clock \(T\ge2k\), the kernel proves
\[
 \boxed{G_H(N)\le F_{H,T}(N)\le2r^k+\frac{k}{2}.}                 \tag{1}
\]
At a dyadic cutoff there is a sharper bound:
\[
 \boxed{G_H(2^k)\le F_{H,T}(2^k)\le r^k+\frac{k}{4}
                       \quad(T\ge2k).}                         \tag{2}
\]
No minimum is assumed to be one. The proof of the global bound uses
\(m(n)\le m_T(n)\), without a density theorem, convergence assumption,
or interchange of infinite limits and population sums.

The [earlier Green-kernel note](MINIMUM-GREEN-KERNEL.md) had a written
population estimate with a worst-case affine correction \((3/2)^k\).
Here exact complete-period averaging replaces that correction by
\(k/4\) at a dyadic cutoff and at most \(k/2\) on its dyadic cell.
The finite population assembly, including incomplete-period estimates,
is fully formalized.

## 1. Integer word weights and exact complete-period mass

For \(k\) shortcut steps, let \(a_k(n)\) count the odd steps, and write
\[
 2^k U^k(n)=3^{a_k(n)}n+B_k(n),\qquad B_k(n)\ge0.                 \tag{3}
\]
The integer numerator \(B_k\) and the exact affine identity are
existing kernel definitions and theorems. Define
\[
 W_k(n)=85^{\,k-a_k(n)}147^{\,a_k(n)},\qquad Q_k=120^k.
\]
The two scalar comparisons
\[
               120^2\le2\cdot85^2,\qquad
            3\cdot120^2\le2\cdot147^2
\]
give, by induction along the actual parity word,
\[
                    3^{a_k(n)}Q_k^2\le2^k W_k(n)^2.            \tag{4}
\]
Thus \(W_k/Q_k\) dominates the smaller of one and the affine slope
\(3^{a_k}/2^k\).

Both \(W_k\) and \(B_k\) are periodic in the source modulo \(2^k\).
The two sources \(n\) and \(n+2^k\) have the same first \(k\)
parities, and their endpoints at time \(k\) have opposite parity.
Consequently the last-bit weight identity is
\[
       W_{k+1}(n)+W_{k+1}(n+2^k)=232W_k(n).
\]
Summing the two halves of the complete period and inducting gives
\[
                  \sum_{n=0}^{2^k-1}W_k(n)=232^k.              \tag{5}
\]
This is an all-depth kernel identity. The proof uses the existing
endpoint parity-flip theorem rather than assuming a probabilistic
parity model or extrapolating a finite count.

The existing [binary-image energy](BINARY-IMAGE-ENERGY.md) theorem gives
\[
                  4\sum_{n=0}^{2^k-1}B_k(n)=k\,4^k.            \tag{6}
\]
Therefore the complete-period average of the rational affine correction
\(B_k(n)/2^k\) is exactly \(k/4\). Its mass, not a worst-case value,
is what enters the new bound.

## 2. A pointwise bound with the actual correction

The existing ordinary/shortcut simulation proves that \(U^k(n)\) is
an ordinary iterate at a time no greater than \(2k\). Hence, for
\(T\ge2k\),
\[
                    m_T(n)\le n,\qquad m_T(n)\le U^k(n).
\]
If \(W_k\ge Q_k\), the source bound suffices. Otherwise (4) and
\(W_k<Q_k\) imply
\[
                         3^{a_k(n)}Q_k\le2^kW_k(n).
\]
Use (3) and the endpoint bound in that case. Both cases yield the
denominator-free kernel inequality
\[
 2^k Q_k m_T(n)
       \le 2^k n W_k(n)+Q_k B_k(n).                            \tag{7}
\]
Equivalently,
\[
                    m_T(n)\le n\,W_k(n)/Q_k+B_k(n)/2^k.
\]
Replacing the minimum by its nonnegative tail value can only decrease
the left side. No upper estimate on the individual correction \(B_k(n)\)
has been substituted.

## 3. Positive source ranges and incomplete periods

Write \(M=2^k\), \(Q=120^k\), \(P=232^k\), and
\(S=\sum_{n=1}^N m_T(n)\mathbf1_{\{m_T(n)>H\}}\).
Periodicity proves that a sum over \(1,\ldots,M\) equals a sum over
\(0,\ldots,M-1\). The endpoint at \(M\) is retained correctly.

For \(N\le2M\), nonnegativity and two complete periods give
\[
              \sum_{n=1}^NW_k(n)\le2P,\qquad
              2\sum_{n=1}^NB_k(n)\le kM^2.
\]
Summing (7), bounding each source \(n\) in its weighted term by \(N\),
and cancelling the positive factor \(M\) proves
\[
                         2QS\le4NP+QkM.                       \tag{8}
\]
All these steps are kernel checked over arbitrary natural parameters.
For \(M\le N\le2M\), division gives the slightly sharper intermediate
bound
\[
                    F_{H,T}(N)\le2r^k+\frac{kM}{2N}
                                    \le2r^k+\frac{k}{2}.
\]
The exact cross-multiplied intermediate bound is (8); the last rational
bound is also an explicit Lean theorem.

At \(N=M\), there is only one complete period. Equations (5)–(7) give
\[
                         4QS\le4MP+QkM,
\]
which proves (2). This improvement is not based on a numerical observation.

## 4. Discharging the Green-kernel majorant

Recall the exact gauge from the earlier note:
\[
 q=\frac{29}{30},\quad
 V(N)=q^k\frac{2^k+14N}{15}\quad(N>0),\quad V(0)=0.
\]
Since \(N\ge2^k\), the kernel proves \(V(N)\ge r^k\).
A separate integer induction gives
\[
                         (k+2)120^k\le2\cdot232^k,
\]
or \(k/2+1\le r^k\). Thus (1) proves, at every cutoff, including zero,
\[
 \boxed{0\le G_H(N)\le3V(N),\qquad
        F_{H,T}(N)\le3V(N)\quad(T\ge2\lfloor\log_2N\rfloor).}    \tag{9}
\]
The nonnegativity of prefix means was already formalized.

In particular, (9) applies uniformly in \(L\ge0\) to the adaptive
prefix mean \(A_{H,L}(N)=F_{H,L+2\lfloor\log_2N\rfloor}(N)\).
The earlier finite adaptive occupation lower bound no longer needs
an explicit majorant premise.

For \(H\ge1\), let \(P\) be the fair cutoff average with children
\[
              a(N)=\lfloor N/2\rfloor,\qquad
              b(N)=3\lfloor(N-1)/2\rfloor+2,
\]
and set \(R_H=G_H-PG_H\). Let \(\tau\) be the first time this cutoff
chain reaches a value at most \(H\). With
\(\rho=1704/1711\), the existing finite Green bounds now apply to the
actual global mean with its population premise discharged in Lean:
\[
 0\le G_H(N)-\mathbb E_N\sum_{j<J,\ j<\tau}R_H(N_j)
        \le3\rho^J V(N),                                      \tag{10}
\]
\[
 \mathbb E_N\sum_{J\le j<J+K,\ j<\tau}|R_H(N_j)|
        \le\frac{5133}{7}\rho^J V(N).
\]
The binary-average versions of these finite formulas are kernel
theorems. They concern an auxiliary chain of source cutoffs, not random
choices along an individual Collatz orbit.

The infinite Green representation still uses the prior written
monotone-convergence and \(L^1\) argument. What has changed is that its
actual-minimum majorant is now a kernel theorem. No fully formal
measure-theoretic limit is claimed.

For a hypothetical least counterexample \(A\), the prior diagnostic
\[
             1\le[3\rho^J+\eta(1-\rho^J)/(1-\rho)]V(A)
\]
also no longer needs the population-majorant premise. For \(\eta\ge0\),
it **still** requires the separate hypothesis \(R_{A-1}(N)\le\eta V(N)\) on active
cutoffs. No sufficiently small value of \(\eta\) has been proved.

## 5. What is and is not gained

Equations (1)–(2) are stronger finite estimates and make the analytic
input to the residual construction fully kernel checked. In the
written real-variable consequence, the power exponent is
\(\log_2(29/15)<1\), so \(G_H(N)=o(N)\).
The normalized mean itself may still grow under this upper bound.
Neither sublinearity nor the exact residual expansion forces the strict
budget \(G_H(N)<1\) uniformly over all cutoffs.

The [critical-clock obstruction](MINIMUM-CRITICAL-CLOCK-LIFT.md)
remains valid and is compatible with (9), since \(V\) grows.
The new upper bound is not a claim that finite-prefix approximants
converge uniformly to the global minimum.

For context, [Tao's theorem and Remark 1.4](https://arxiv.org/html/1909.03562v5#S1.SS1)
give almost-everywhere control in logarithmic density, with a floor
depending on the allowed exceptional density. That statement does
not supply this project's uniform linear-tail budget. It is not an
input to the new proof.

## 6. Verification

The [Lean module](../lean/MinimumPopulationMajorant.lean) audits 36
theorem roots. They use only the standard logical axioms as applicable.
No new axiom, admitted result, native computation, or external
mathematical premise is introduced.

The [verifier](../verify_minimum_population_majorant.py) authenticates
the latest clock-lift and binary-image manifests and freshly builds
the 21 dependency modules sequentially. Its independent exact checks
cover complete residue periods through \(2^{16}\), the weight and
affine-correction masses, the pointwise bound, and actual ordinary
prefix minima for every source through 65,536 at every even clock
through 32. It checks the population bounds at every cutoff through
65,536 for four floors.

Separate finite Green checks use computable adaptive prefix profiles,
with forward distributions compared against backward recursion.
They do not numerically evaluate the unknown global-minimum residual.
The universal global-minimum statements come from the kernel proof.
The [manifest](../results/minimum-population-majorant/verification.json)
and [replay record](../results/minimum-population-majorant/replay.json)
record exact counts, hashes, and build logs.

Verification passed on 14 October 2026 at 20:49:42 UTC. The 21 fresh
Lean builds took 9.643 seconds. The verifier authenticated 28 and 26
hashes from its two preceding manifests; the new manifest records 47
files. The complete period tests cover 131,071 residue/depth pairs
and 1,966,082 shortcut steps. Separate pointwise checks cover 196,590
source/depth pairs and 2,883,468 shortcut steps. Each of the two
ordinary traversals performs 2,097,152 steps, with 1,114,112 matching
prefix minima. There are 262,144 population inequalities, the same
number of gauge comparisons, 68 sharper dyadic bounds, 216 finite
Green depth comparisons and 576 absolute-tail windows. The 261
large-index constant checks, through index 4096, are arithmetic only.

The missing uniform subunit estimate and the full Collatz conjecture
remain unresolved. No claim of mathematical novelty is made for the
elementary parity-weight argument.
