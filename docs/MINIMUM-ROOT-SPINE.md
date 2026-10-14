# Actual minimum roots, cap budgets, and eventual repetition

The attained minima of successive actual orbit tails form a nondecreasing
sequence. Its cap increments telescope exactly, and bounded accumulated
caps along one orbit are equivalent to eventual repetition of that orbit.
This does **not** identify the eventual cycle as the cycle through one.

A second consequence of the
[population-majorant proof](MINIMUM-POPULATION-MAJORANT.md) is a uniform
bound on dyadic counts of all integers that never descend. Their reciprocal
sum converges. This still permits an infinite sparse sequence of such
integers and does not rule out divergence.

The new [Lean module](../lean/MinimumRootSpine.lean) has 52 audited theorem
roots. Statements below marked **kernel** are proved there using the prior
local modules. The infinite reciprocal-sum passage is **written**, not a
formal real-series proof. No external mathematical input or novelty claim
is used. **Collatz remains unresolved.**

## 1. Global minimum transport

Write
\[
 C(n)=\begin{cases}3n+1,&n\text{ odd},\\ n/2,&n\text{ even},\end{cases}
 \qquad m(n)=\min_{t\ge0}C^t(n).
\]
The minimum is attained, without assuming convergence, by well-ordering.
Call a positive integer \(a\) a **minimum root** if \(m(a)=a\), equivalently
if its orbit never falls below its starting value. This definition does
not assert that \(a\) is periodic.

**Kernel:**
\[
 m(n)\le m(C^t n),\qquad
 m(n)=\min\{n,m(Cn)\},
 \tag{1}
\]
\[
 m(2n)=m(n),\qquad
 m(2n+1)=\min\{2n+1,m(3n+2)\}.
 \tag{2}
\]
The earlier finite-prefix odd cap identity therefore has an exact global
counterpart. For
\[
 v_H(y)=y\,\mathbf1_{y>H},\qquad
 d_H(s,y)=v_H(y)-v_H(\min\{s,y\}),
\]
the module proves
\[
 v_H(m(2n+1))+d_H(2n+1,m(3n+2))
 =v_H(m(3n+2)).
 \tag{3}
\]
This is actual global transport; finite replay does not assign unknown
values to either side.

A positive root is odd. If it is greater than one, the existing explicit
forward paths additionally give
\[
 a\bmod16\in\{7,11,15\}.
 \tag{4}
\]
These are forward restrictions. The extra backward restrictions on a
**least counterexample** cannot be applied to every minimum root.

## 2. The successor is an attained tail minimum

For a root \(a\), set
\[
 \sigma(a)=m(Ca).
\]
Then, **kernel**,
\[
 m(\sigma(a))=\sigma(a),\qquad
 a\le\sigma(a),\qquad
 2\sigma(a)\le3a+1.
 \tag{5}
\]
The last estimate uses the first odd step and its following halving.
The successor is not divisible by three: \(Ca=3a+1\) is not divisible
by three, this property persists along the ordinary orbit, and its
minimum is attained.

The equality case has an exact meaning:
\[
 \boxed{\quad \sigma(a)=a
 \quad\Longleftrightarrow\quad
 \exists p>0:\ C^p(a)=a.\quad}
 \tag{6}
\]
Indeed, if \(m(Ca)=a\), attainment supplies a positive-time return from
\(a\). A return gives the reverse implication using \(a\le m(Ca)\).
The return could be on a nontrivial cycle; (6) does not prove \(a=1\).

For a positive source \(n\), define
\[
 a_0=m(n),\qquad a_{k+1}=\sigma(a_k).
\]
There are explicitly defined ordinary clocks \(s_k\), using the chosen
minimum-attainment clocks, with
\[
 C^{s_k}(n)=a_k,\qquad s_{k+1}>s_k.
 \tag{7}
\]
Thus these roots lie on the actual orbit. No independent trajectory or
comparison map is substituted for it.

If the original orbit never repeats, every inequality
\(a_k<a_{k+1}\) is strict. Each \(a_k>1\), and (4) implies gaps of at
least four. The module proves
\[
 m(n)+4k\le a_k,\qquad
 2^k(a_k+1)\le3^k(m(n)+1).
 \tag{8}
\]
For \(k\ge1\), the forward and modulo-three restrictions combine to give
\[
 a_k\bmod48\in\{7,11,23,31,43,47\}.
 \tag{9}
\]
The different list for a least counterexample is intentional: the roots
later on its orbit need not themselves be least counterexamples.

The bounds in (8) concern the **root index** \(k\).
The ordinary clocks \(s_k\) have no upper bound here. Consequently (8)
does not provide a linear growth rate in ordinary time.
Its lower and upper estimates are compatible, and do not exclude an
infinite root sequence.

## 3. What a cap budget would establish

Define the ordinary-step global cap increment and its accumulated sum by
\[
 \Delta(n)=m(Cn)-m(n)\ge0,\qquad
 A_T(n)=\sum_{0\le t<T}\Delta(C^t n).
\]
The increments vanish at even sources. Their exact support is, **kernel**,
\[
 \Delta(n)>0
 \quad\Longleftrightarrow\quad
 m(n)=n\ \text{and}\ n\ \text{has no positive-time return}.
 \tag{10}
\]
A transient root leading to a hypothetical cycle with a larger minimum
also fits (10), so a positive increment alone would not certify divergence.

The orbit identity is
\[
 \boxed{\quad m(n)+A_T(n)=m(C^T n).\quad}
 \tag{11}
\]
It involves global minima on both sides, not the last value of a finite
trajectory.

The module proves the equivalences
\[
\begin{aligned}
 \exists B\ \forall T:\ A_T(n)\le B
 &\quad\Longleftrightarrow\quad
 \exists B\ \forall T:\ m(C^T n)\le B\\
 &\quad\Longleftrightarrow\quad
 \exists s,\ p>0:\ C^{s+p}n=C^s n.
\end{aligned}
 \tag{12}
\]
All of (12) is **kernel checked**, including the eventual-repetition
direction. If repetition failed, the attained root sequence would
increase by at least one per index, contradicting the proposed bound.
Conversely, after a return, arbitrarily late multiples of its period
bound every tail minimum by the minimum at the return time.

Hence a proof of bounded actual caps for every orbit would eliminate
nonrepeating orbits. It would leave the problem of excluding every
nontrivial cycle. No such universal cap bound is proved here.

If \(n\) reaches one, every positive suffix also reaches one, so
\(m(C^Tn)=m(n)=1\) and \(A_T(n)=0\) for every \(T\), again **kernel**.

## 4. Finite-horizon caps have a moving endpoint

For a fixed terminal clock \(T\), let
\[
 u_j=\min_{j\le i\le T}C^i n,\qquad 0\le j\le T.
\]
The computable suffix minima increase as \(j\) increases. Their finite
caps satisfy
\[
 \sum_{0\le j<T}(u_{j+1}-u_j)=C^T n-m_T(n),
 \qquad m_T(n)=\min_{0\le i\le T}C^i n.
 \tag{13}
\]
The recursive finite sum and (13) are **kernel**. The right side is the
terminal orbit value minus the prefix minimum; it differs from (11).

Even the cycle through one shows why the moving horizon matters.
For every \(q\ge0\), the kernel proves that the finite cap totals from
source one at clocks \(3q,3q+1,3q+2\) are respectively
\[
 0,\quad3,\quad1,
 \tag{14}
\]
while every global cap total from one is zero.
For each fixed edge, increasing the terminal clock eventually makes its
finite cap zero. Summing over all edges up to the moving terminal clock
does not commute with that pointwise settling; (14) keeps oscillating.
This example already lies in the verified trivial cycle.

## 5. Population control for all minimum roots

Let
\[
 R_k=\#\{a:\ 2^k<a\le2^{k+1},\ m(a)=a\},
 \qquad r=\frac{29}{15}.
\]
Every counted source contributes at least \(2^k\) to the untruncated
minimum sum through \(2^{k+1}\). Applying the previous sharp dyadic
population bound gives, **kernel**,
\[
 \boxed{\quad R_k\le2r^{k+1}+\frac{k+1}{2}.\quad}
 \tag{15}
\]

The same inequality holds for the computable overestimate
\[
 R_{k,T}=\#\{a:\ 2^k<a\le2^{k+1},\ m_T(a)=a\}
\]
whenever \(T\ge2(k+1)\). The proof includes
\[
 R_k\le R_{k,T},\qquad
 2\cdot120^{k+1}R_{k,T}
 \le4\cdot232^{k+1}+120^{k+1}(k+1).
 \tag{16}
\]
This allows independent finite checks without pretending to know which
unfinished sources are genuine global roots.

There is also a **kernel finite weighted budget**. Put
\[
 S_K=\sum_{0\le k<K}\frac{R_k}{2^k},
 \qquad
 E_K=116\left(\frac{29}{30}\right)^K+\frac{K+2}{2^K}.
\]
The exact envelope telescope proves
\[
 S_K+E_K\le118,\qquad E_K\ge0,\qquad S_K\le118.
 \tag{17}
\]
The constants come from
\[
 \frac{2r^{k+1}+(k+1)/2}{2^k}+E_{k+1}=E_k,
 \qquad E_0=118.
\]
Lean uses rational powers \(2^{-k}=(1/2)^k\).

**Written corollaries.** Every root \(a>1\) belongs to one of the
disjoint shells in (15), and \(1/a\le2^{-k}\) there. By comparison and
monotone passage to the limit,
\[
 \boxed{\quad
 \sum_{\substack{a\ge1\\m(a)=a}}\frac1a\le119,
 \quad}
 \tag{18}
\]
including the contribution one from \(a=1\).
The infinite real-series argument and the comparison to individual
reciprocals are written; the finite shell budget (17) is kernel.
Similarly, summing (15) gives a root-count bound of order
\(N^{\log_2(29/15)}\), whose exponent is less than one.
Writing \(\alpha=\log_2(29/15)\), the first \(k+1\) distinct roots of a
nonrepeating orbit all lie below \(a_k\). Hence the same written counting
argument gives \(k+1\le C a_k^\alpha\), and therefore
\(a_k\ge c(k+1)^{1/\alpha}\) for an absolute positive constant \(c\).
This improves the linear lower bound in the root index, but still has
no ordinary-clock estimate and is compatible with the exponential upper
bound in (8). This power-law corollary is not separately formalized.

This is a restriction on the set of **all** minimum roots, not on all
members of their predecessor basins and not on the whole orbit. The
older [orbit-packing analysis](../APERIODIC-ATTEMPT.md) concerns a
different set, the values of one nonrepeating orbit.
A sparse infinite root sequence can obey (5), (8), (9), and (18).
These bounds do not give a uniform subunit minimum-tail mean.

## 6. Verification and remaining target

Run the [verifier](../verify_minimum_root_spine.py) with
python3 verify_minimum_root_spine.py.

It authenticates the prior population-majorant manifest and builds all
22 Lean modules sequentially in a fresh temporary import directory.
It audits all 52 new theorem roots, allowing only the standard
propext, Classical.choice, and Quot.sound axioms, with no native finite
computation axiom, added axiom, or unfinished proof.

The independent Python checks cover:

- Every source from 2 through 65,536 at its shell clock \(2(k+1)\),
  comparing ordinary iteration with a separate exact-clock shortcut
  traversal, and checking the finite cap telescope and shell bounds.
- Additional finite prefixes, including starts \(2^{31}-1\) and
  \(2^{63}-1\), and the cycle oscillation in (14).
- Explicit arrivals at one for every source from 1 through 4,096,
  replayed independently. Only those witnessed paths are used to assign
  numerical global minimum one and zero global caps.
- Exact envelope arithmetic through index 256 and at indices 512,
  1,024, and 4,096. These larger-index tests are arithmetic identities,
  not enormous source censuses.

The [verification manifest](../results/minimum-root-spine/verification.json)
and [replay record](../results/minimum-root-spine/replay.json) give exact
counts, file hashes, compiler information, and proof scopes.

The full run completed at 2026-10-14T21:10:53.643080Z. The 22 fresh
builds took 10.470 seconds; all 52 roots passed, with 48 file hashes and
47 prior hashes authenticated. Python checked 65,535 complete shell
sources over 1,966,082 ordinary steps, with 65,535 independent exact-clock
comparisons. Across the shell census and additional examples it checked
65,626 finite cap telescopes and 1,970,655 cap edges. The separate
4,096-source convergence replay used 307,751 ordinary steps and
independently reconstructed every path; its global-cap assignments cover
320,039 witnessed edges, including the appended cycle. These finite
convergence witnesses are Python evidence, not new kernel interval
certificates.

The next substantive requirement remains an independently useful bound
on actual global residuals or caps, or stronger arithmetic that excludes
both the growing root sequence and nontrivial periodic roots. No such
bound or exclusion follows from the new equivalences and sparse counts.
The full Collatz goal remains active.
