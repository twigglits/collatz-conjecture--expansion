# Refinements of the actual escape weight

**Status: twenty-one finite arithmetic and all-depth moment roots are
kernel checked. The energy bounds and measure arguments are written.
No uniform energy bound, exclusion of escape, or full Collatz proof is
established.**

This note returns to the actual correction weight \(W\), rather than
the auxiliary grade weight \(V\). It gives an explicit finite-energy
bound at each fixed time offset, but that bound grows with the offset.
It also removes the written natural-passage premise from the previous
energy criterion: the replayed predecessor-density theorem and the exact
odd Collatz rule suffice for that implication. The required uniform
energy estimate remains open.

## 1. Matching the time and binary refinements

For the shortcut map \(U\), put
\[
 W_t(n)=\frac{n3^{a_t(n)}}{2^tU^t(n)},\qquad
 f_t(n)=W_t(n)/n\quad(n>0).
\]
This is the product retaining \(3x/(3x+1)\) at each odd input. Fix an
integer time offset \(s\ge0\). For \(x\in[1,2)\), let
\[
 n_k=\lfloor2^kx\rfloor,\qquad
 H_{s,k}(x)=2^kf_{s+k}(n_k)
          =\frac{3^{a_{s+k}(n_k)}}{2^sU^{s+k}(n_k)}.
                                                               \tag{1}
\]
Each function lies in \([0,1]\). The exact rules
\(U(2n)=n\) and \(U(2n+1)=3n+2\) give, on the two children of
the cell indexed by \(n\) at level \(k\),
\[
 H_{s,k+1}^{\rm even}=H_{s,k},\qquad
 H_{s,k+1}^{\rm odd}=3\,2^kf_{s+k}(3n+2).                  \tag{2}
\]
Define
\[
 e_{s,k}=\int_1^2|H_{s,k+1}-H_{s,k}|^2\,dx,
 \qquad E_s=\sum_{k\ge0}e_{s,k}.                          \tag{3}
\]
If the parent and odd-child values are \(a,b\), respectively, their
contribution to the conditional drift is \((b-a)/2\), and to the
conditional squared increment is \((b-a)^2/2\). In particular,
\[
 \frac{(b-a)^2}{2}=\frac{b^2-a^2}{2}-a(b-a).              \tag{4}
\]
The drift can have either sign. These functions are not a martingale.

## 2. An unconditional tail bound at each fixed offset

Write \(2^tU^t(n)=3^{a_t}n+b_t(n)\) and
\(c_t(n)=b_t(n)/3^{a_t}\). Then
\[
 W_t(n)=\frac{n}{n+c_t(n)},\qquad
 0\le1-W_t(n)\le c_t(n)/n.                               \tag{5}
\]
The quantity \(c_t\) has period \(2^t\). To avoid rational sums in
the kernel, use \(D_t=3^{t-a_t}\) and \(Q_t=b_tD_t\).
The two next-bit children sum to \((4D_t,6Q_t+2^tD_t)\).
[EscapeWeightRefinements.lean](../lean/EscapeWeightRefinements.lean)
proves the integer identities and, at every depth,
\[
 \sum_{0\le n<2^t}D_t(n)=4^t,\qquad
 2\sum_{0\le n<2^t}Q_t(n)+6^t=8^t.
\]
Dividing by \(3^t\) therefore gives the written identity
\[
 \sum_{0\le n<2^t}c_t(n)
                  =\frac{(8/3)^t-2^t}{2}.               \tag{6}
\]

Let \(L_{s,k}\) be the mean of \(1-W_{s+k}(n)\) on
\([2^k,2^{k+1})\). For \(s\ge1\), that interval is contained in one
period of length \(2^{s+k}\); for \(s=0\), it is exactly a translated
period. Nonnegativity and (5)--(6), using \(n\ge2^k\), yield
\[
 0\le L_{s,k}\le\frac12(8/3)^s(2/3)^k.                   \tag{7}
\]
For each fixed \(s\), this bound is summable in \(k\). Hence
\(W_{s+k}(n_k)\to1\) almost everywhere and
\(H_{s,k}\to1/x\) almost everywhere and in \(L^2([1,2))\).
This is a statement with \(s\) fixed, not a statement about \(W_\infty\).

For completeness, a quantitative energy tail follows from the same
estimate. The comparison function \(g_k=2^k/n_k\) also copies its even
child; its odd-child change has magnitude at most \(2^{-k-1}\).
The nonnegative deficit \(g_k-H_{s,k}\) is at most
\(1-W_{s+k}(n_k)\). Apply \((u+v+w)^2\le3(u^2+v^2+w^2)\)
on each odd half-cell. The parent deficit contributes at most
\(3L_{s,k}/2\), and the odd-child deficit at most \(3L_{s,k+1}\).
Consequently
\[
 e_{s,k}\le\frac38\,4^{-k}
             +\frac74(8/3)^s(2/3)^k,
\]
and
\[
 \boxed{\sum_{k\ge K}e_{s,k}
 \le\frac12\,4^{-K}+\frac{21}{4}(8/3)^s(2/3)^K.}         \tag{8}
\]
Also \(e_{s,k}\le1/2\), because changes occur only on odd half-cells.
Take \(K=3s\) in (8) to obtain
\[
                       E_s\le\frac32s+\frac{23}{4}.      \tag{9}
\]
Thus every fixed-offset energy is finite. This bound grows with \(s\)
and does not justify taking \(s\to\infty\) in the energy sum.

## 3. Nonvanishing jumps at arbitrarily fine levels

The lack of a simple pointwise contraction is an actual-map phenomenon.
For each integer \(j\ge1\), set
\[
 n_j=\frac{8(64^j-1)}9,\quad q_j=3n_j+2,\quad
 k_j=6j-1,\quad t_j=k_j+6=6j+5,\quad A_j=3^{3j-1}.
\]
These are positive integers, with
\(2^{k_j}\le n_j<2^{k_j+1}\). Direct symbolic paths give
\[
 U^{t_j-2}(n_j)=A_j+1,\quad a_{t_j-2}(n_j)=3j+1,
 \qquad U^{t_j-2}(q_j)=1,\quad a_{t_j-2}(q_j)=1.          \tag{10}
\]
Indeed, writing \(u=(64^j-1)/9\), the first five steps from \(8u\)
lead to \(2^{6j-2}+1\), using two odd inputs. The next \(6j-2\)
steps are the affine lift of the shortcut cycle at one. The target
\(24u+2\) first reaches a power of two in two steps and then halves to
one. The kernel proves these formulas and constructs the divisible seed
for every \(j\); it does not assume a conjectured long-term path.

At offset \(s=6\), the odd child of the cell \(n_j\) has value
\(27/64\), by (2) and the two extra cycle steps at \(q_j\). The parent
value is
\[
 H_{6,k_j}=
 \begin{cases}
 9A_j/(16(A_j+1)),&j\text{ even},\\
 27A_j/(16(3A_j+5)),&j\text{ odd}.
 \end{cases}
\]
It follows that
\[
 \boxed{H_{6,k_j}-H_{6,k_j+1}^{\rm odd}\ge27/512,
 \qquad H_{6,k_j}-H_{6,k_j+1}^{\rm odd}\longrightarrow9/64.} \tag{11}
\]
The uniform lower inequality follows from a kernel-checked two-step
integer bound for every odd \(A\ge9\); division and the displayed
limit are written. Thus the maximum individual jump does not tend to
zero even at this fixed offset. The exhibited half-cells have summable
lengths, so (11) is consistent with (8). It supplies no divergent orbit.

Nor is \(E_s\) nonincreasing in \(s\). Exact finite rational enclosures
through level 12, with (8) for the remaining tail at \(s=0\), give
\[
                         E_0<1/7,\qquad E_{16}>1/4.      \tag{12}
\]
Only the first inequality needs an infinite tail estimate; the second
already holds for the finite sum through level 12. This refutes energy
contraction under increasing the time offset. It does not refute a
larger bound independent of \(s\).

## 4. Finite limiting energy would exclude escape without passage mixing

Let \(a(n)\) be any \(\{0,1\}\)-valued function invariant under \(U\).
In particular
\(a(2n)=a(n)\) and \(a(2n+1)=a(3n+2)\). Suppose
\(a(\lfloor2^kx\rfloor)\) converges for almost every \(x\in[1,2)\).
We claim its limit is a constant, zero or one, almost everywhere.

Write this limit as \(A(x)\), and extend it to all \(x>0\) by
\(A(2x)=A(x)\). The step functions
\(a_k(x)=a(\lfloor2^kx\rfloor)\) converge to this extension in
\(L^1\) on every compact subinterval of \((0,\infty)\).
Let \(b_k(x)=a(2\lfloor2^kx\rfloor+1)\). On each parent cell,
the even child equals the parent and the odd child equals \(b_k\), so
\[
 \|b_k-a_k\|_{L^1([1,2))}
                  =2\|a_{k+1}-a_k\|_{L^1([1,2))}\to0.
\]
Thus \(b_k\to A\) in \(L^1\). Exact Collatz invariance also gives
\(b_k(x)=a(3\lfloor2^kx\rfloor+2)\).

To pass this latter expression to the limit, map a cell with index \(n\)
linearly, with slope one, to
\([(3n+2)2^{-k},(3n+3)2^{-k})\). Call the resulting map \(S_k\).
Its image cells are disjoint and \(|S_k(x)-3x|\le2^{1-k}\).
Consequently composition by \(S_k\) does not increase the \(L^1\) error
over a compact interval containing all its images. Approximate \(A\)
there by continuous functions to get \(A\circ S_k\to A(3x)\) in
\(L^1\). Since \(a_k\circ S_k=b_k\), this proves
\(A(x)=A(3x)\) almost everywhere.

In logarithmic coordinates, \(G(y)=A(2^y)\) is a bounded measurable
one-periodic function invariant under translation by the irrational
number \(\log_2 3\). All its nonconstant Fourier coefficients vanish:
each equals itself times \(e^{2\pi i m\log_2 3}\ne1\) for \(m\ne0\).
Uniqueness in \(L^2\) makes \(G\), and hence \(A\), constant almost
everywhere. As \(A\) takes values zero or one, its constant is zero or one.
Convergence of the dyadic-annulus means then gives that same ordinary
natural density for \(a(n)=1\), by summing the annuli and their partial
intervals. For a partial interval, use the same \(L^1\) convergence on
\([1,2)\); complete-annulus convergence alone would not suffice.

Apply this rigidity to the indicator of divergence. The earlier
[packing and loss argument](WEIGHTED-DISSIPATION.md) gives
\(W_\infty=0\) off divergence and
\(W_\infty\ge c_0=e^{-8192/3}\) on divergence. Thus a switch of this
indicator between adjacent binary levels causes a change of at least
\(c_0/2\) in
\(h_k(x)=2^kW_\infty(n_k)/n_k\). If
\(\sum_k|h_{k+1}-h_k|^2<\infty\) almost everywhere, each indicator
switches only finitely often. The preceding argument forces divergence
to have natural density zero or one, without assuming a density law.

The replayed [predecessor theorem](PREDECESSOR-DENSITY-REVIEW.md) excludes
both alternatives if any divergent orbit exists: a fixed unit target
on that orbit has predecessors of positive lower density, and the basin
of one also has positive lower density. Therefore finite limiting energy
almost everywhere would exclude divergence. This implication uses the
external PLD theorem, but **does not use the written natural-passage
mixing premise**. The same rigidity applied to the indicator of failure
to reach one would exclude all counterexamples if its own dyadic changes
were summable. No such estimate is proved either.

## 5. The remaining uniform bound

For every fixed \(k\), \(H_{s,k}\to h_k\) as \(s\to\infty\).
Consequently the estimate
\[
                         \liminf_{s\to\infty}E_s<\infty  \tag{13}
\]
would imply finite integrated limiting energy by Fatou, and Section 4
would exclude escape. **Equation (13) is unproved.** The linear bound
(9), the finite inequalities (12), and fixed-offset convergence to
\(1/x\) do not establish it. Other positive cycles would still require
exclusion even if (13) were established.
A bound uniform in all offsets would suffice, but is stronger than
needed: a bounded sequence of energies at arbitrarily late offsets is
enough. No such sequence with a proved bound has been obtained.

The operator literature does not fill this gap. Neklyudov's
[Hardy-space fixed-point argument](https://arxiv.org/html/2106.11859v9)
concerns the unweighted coefficient map \(a(n)\mapsto a(U(n))\).
Here \(f_t\) evolves under coefficients \(1/2\) at even inputs and
\(3/2\) at odd inputs. Although \(f_\infty(n)\le1/n\) is square
summable, it is a fixed point of this different, weighted operator.
The nonzero sequence \(W_\infty\) itself could not be square summable
because it is constant along each doubling ray. Béhani's
[operator dynamics results](https://arxiv.org/html/2303.03203v1) likewise
do not assert convergence of individual Collatz orbits. No new external
theorem is adopted in this note.

## 6. Reproduction and scope

```sh
python3 verify_escape_weight_refinements.py
```

[The record](../results/escape-weight-refinements/verification.json)
separates fresh local kernel builds, exact finite rational energy
enclosures, and the written real/measure arguments. The finite replay
checks complete reciprocal moments through depth 18, energy levels
0 through 12 at seven stated offsets, and the explicit jump family
for \(1\le j\le128\). The kernels prove the family formulas and moments
for all parameters; those are not inferred from finite samples.
Exploratory floating-point sampling at larger scales was used to choose
which estimate to investigate and is not a certificate for (13).
