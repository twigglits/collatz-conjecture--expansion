# Exact norm growth for the killed Collatz operator

**Collatz remains unresolved.** On the space of functions with finite norm
\(\sum_{n>H}|f(n)|n^{-s}\), for any fixed integer \(H\ge1\) and \(s>1\),
the killed composition operator has spectral radius and essential spectral
radius exactly \((3/2)^s>1\). Thus it has no gap between those two radii.
At the project's floor \(H=64\) and exponent \(s=3/2\), its powers satisfy
\[
 (3/2)^{3k/2}\le\|K_{64}^{k}\|\le5(3/2)^{3k/2}.       \tag{1}
\]
This concerns the whole function space. The actual survivor mass is the
norm of the particular vector \(K_{64}^{k}\mathbf1\), and remains
nonincreasing. Equation (1) neither refutes its possible decay nor proves
convergence of every orbit.

The integer source comparisons and all-index orbit witnesses are kernel
checked in [KilledOperatorBounds.lean](../lean/KilledOperatorBounds.lean).
The norm, infinite-sum, real-power, compactness, and spectral arguments
below are **written analysis**, not Lean theorems. The proof uses the
earlier kernel [fibre bound](EQUAL-WEIGHT-FIBRES.md); it does not need an
unproved mixing law or a hypothesis about exceptional orbits. No claim
of novelty is made.

## 1 The operator and the actual survivor mass

Let \(U\) be the shortcut Collatz map and let
\[
 X_{H,s}=\left\{f:\{H+1,H+2,\ldots\}\to\mathbb C:
        \|f\|_{H,s}=\sum_{n>H}|f(n)|n^{-s}<\infty\right\}.
\]
Define
\[
 (K_Hf)(n)=\begin{cases}f(U(n)),&U(n)>H,\\0,&U(n)\le H,\end{cases}
 \qquad n>H.
\]
This is composition on functions, not forward transport of probability
masses. Its powers retain every killing condition:
\[
 K_H^k f(n)=\mathbf1_{\{\tau_H(n)>k\}}f(U^k(n)).          \tag{2}
\]
Since \(s>1\), the constant function belongs to \(X_{H,s}\), and
\[
                 \|K_H^k\mathbf1\|_{H,s}=M_k(s).        \tag{3}
\]
The [existing mass equivalence](WEIGHTED-SURVIVORS.md) concerns (3),
not uniform decay over the unit ball of \(X_{H,s}\).

Write
\[
 R_k(y)=y^s\sum_{\substack{U^k(n)=y\\\tau_H(n)>k}}n^{-s},
 \qquad y>H.
\]
Regrouping nonnegative absolute values gives the exact column formula
\[
                       \|K_H^k\|=\sup_{y>H}R_k(y).       \tag{4}
\]
For the upper bound, sum \(|f(y)|y^{-s}R_k(y)\); for the reverse bound,
use the norm-one function \(e_y=y^s\mathbf1_{\{y\}}\).
The estimate below proves boundedness, including at \(k=1\).

## 2 Converting coefficients into actual source weights

For \(y=U^k(n)\) and \(j=w_k(n)\), the kernel shifted envelope gives
\[
 2^k(y+1)\le3^j(n+2^{k-j}).
\]
Since \(3^j2^{k-j}\le3^k\), this implies
\[
                  2^ky\le3^jn+3^k.                     \tag{5}
\]
In particular, if \(y\ge2(3/2)^k\), then
\[
 2^ky\le2\,3^jn,\qquad
 (y/n)^s\le2^s(3^j/2^k)^s.                              \tag{6}
\]
These natural-number inequalities are kernel checked without a first-entry
or distinctness assumption. They therefore also hold for paths that might
repeat above the floor.

The complete same-time, same-weight fibre has at most \(2^{k-j}\)
sources. Consequently, for \(s>1\),
\[
 Z_{k,s}(y):=\sum_{\substack{U^k(n)=y\\n>0}}
          (3^{w_k(n)}/2^k)^s
 \le \frac{(3/2)^{sk}}{1-2/3^s}.                        \tag{7}
\]
Indeed, group by \(e=k-j\) and sum the geometric majorant
\((3/2)^{sk}\sum_{e\ge0}(2/3^s)^e\).
Deleting paths that touch the floor only decreases this sum.

For high targets, (6) and (7) bound \(R_k(y)\). For low targets use
the total source weight instead:
\[
 y<2(3/2)^k
 \quad\Longrightarrow\quad
 R_k(y)\le y^s\sum_{n>H}n^{-s}
 \le2^s\frac{H^{1-s}}{s-1}(3/2)^{sk}.                    \tag{8}
\]
Thus, with a constant independent of \(k\),
\[
 \|K_H^k\|\le C_{H,s}(3/2)^{sk},\qquad
 C_{H,s}=2^s\max\left\{\frac{H^{1-s}}{s-1},
                              \frac1{1-2/3^s}\right\}. \tag{9}
\]
For \(H=64,s=3/2\), the first entry in the maximum is \(1/4\).
The exact integer comparisons \(8<9\) and \(25<27\) give
\(2^{3/2}<3\) and \(3^{3/2}>5\), so the second contribution
in (9) is less than \(3/(1-2/5)=5\). This proves the upper bound
in (1). No floating-point estimate decides that constant.

## 3 The lower rate persists beyond every finite cutoff

For every \(k\), choose any sufficiently large positive integer \(q\)
and put
\[
 x=2^kq-1,\qquad y=3^kq-1.
\]
The first \(k\) steps are odd, with states
\(2^{k-i}3^iq-1\). They stay at least \(x\), so choosing \(x>H\)
makes this a killed inverse-fibre witness. Also
\[
 3^kx\le2^ky,\qquad
 R_k(y)\ge(y/x)^s\ge(3/2)^{sk}.                          \tag{10}
\]
Increasing \(q\) sends both source and target beyond any prescribed
finite bound. The all-parameter witness, its survival, and (10)'s integer
comparison are kernel checked. Together with (9), the spectral radius
formula gives
\[
                         r(K_H)=(3/2)^s.                \tag{11}
\]
No claim that arbitrary witnesses with fixed \(q\) converge is needed.

## 4 Exact essential norm and essential spectral radius

There is a precise coefficient interpretation after removing finite
target columns. For \(0\le a<2^k\), put
\(j_a=w_k(a)\), \(b_a=U^k(a)\), and \(c_a=3^{j_a}/2^k\).
The exact affine identity and canonical image bound are
\[
 U^k(2^kq+a)=3^{j_a}q+b_a,\qquad 0\le b_a<3^{j_a}.
\]
For each target residue \(r\bmod3^k\), define the finite sum
\[
 Z_k(r)=\sum_{\substack{0\le a<2^k\\r\equiv b_a\ ({\rm mod}\ 3^{j_a})}}
                  c_a^s.                               \tag{12}
\]
For \(y\to\infty\) in this residue class, every summand in (12)
has exactly one positive source
\[
 n=2^k\frac{y-b_a}{3^{j_a}}+a.
\]
Every intermediate state eventually exceeds \(H\), since each fixed
prefix is affine with positive slope in \(q\). Also \(y/n\to c_a\).
There are only \(2^k\) source classes, hence
\[
 \lim_{\substack{y\to\infty\\y\equiv r\ ({\rm mod}\ 3^k)}}R_k(y)=Z_k(r).
                                                               \tag{13}
\]
This is an actual-source-weight limit; it does not substitute coefficients
for the finite-target weights in (4).

Let \(\|A\|_{\rm ess}\) mean the distance of an operator from the
compact operators. Then
\[
                    \boxed{\|K_H^k\|_{\rm ess}=\max_r Z_k(r).}   \tag{14}
\]
For the upper bound, retaining only columns \(y\le Y\) gives a finite-rank
operator; the norm of the remaining columns is \(\sup_{y>Y}R_k(y)\).
Let \(Y\to\infty\) and use (13).

For the lower bound, select distinct targets tending to infinity in a
maximizing residue class. Their normalized vectors \(e_y\) have pairwise
distance two. Images under \(K_H^k\) have disjoint supports, because a
source has only one endpoint. For any compact operator \(A\), a subsequence
of \(Ae_y\) is Cauchy. On two far-out elements of this subsequence,
\[
 2\|K_H^k-A\|\ge R_k(y_i)+R_k(y_j)-\|Ae_{y_i}-Ae_{y_j}\|.
\]
Taking the limit proves the reverse inequality. This argument does not
incorrectly assume that the normalized coordinate vectors are weakly null
in \(\ell^1\).

The all-odd residue \(a=2^k-1\), \(b_a=3^k-1\), contributes
\((3/2)^{sk}\) to (12). Equation (7) bounds every residue sum above by
\((3/2)^{sk}/(1-2/3^s)\). Taking \(k\)-th roots in (14), or applying
the spectral radius formula in the Calkin algebra, yields
\[
                r_{\rm ess}(K_H)=r(K_H)=(3/2)^s>1.       \tag{15}
\]
In particular no finite-rank or compact correction makes its essential
radius less than one. An equivalent norm on this same function space
does not alter these radii. A different function space requires a separate
proof of invariance and of the estimates needed for the vector \(\mathbf1\).

## 5 Norm growth supported entirely on convergent paths

The phenomenon is not caused by assuming a counterexample exists. For
every \(K\ge7\), set
\[
 a_K=3^{K-1},\quad b_K=2^{a_K},\quad
 q_K=(b_K+1)/3^K,\quad x_K=2^Kq_K-1.
\]
The earlier [power-target construction](WEIGHTED-BASIN-BARRIER.md) proves
that \(q_K\) is a positive integer. The new kernel theorem gives, for
every such \(K\),
\[
 \tau_{64}(x_K)>K,\quad U^K(x_K)=b_K,\quad
 U^{K+a_K}(x_K)=1,\quad 3^Kx_K\le2^Kb_K.                 \tag{16}
\]
The floor condition follows already from \(x_K\ge2^K-1>64\).

At \(s=3/2\), define an unbounded nonnegative function by
\[
 f(b_K)=(3/4)^K b_K^{3/2}\quad(K\ge7),\qquad
 f(n)=0\text{ at every other }n>64.
\]
The targets are distinct. Its norm is finite and explicit:
\[
                     \|f\|_{64,3/2}=\sum_{K\ge7}(3/4)^K
                                      =2187/4096.       \tag{17}
\]
Yet the single source \(x_K\) supplies
\[
 \|K_{64}^Kf\|_{64,3/2}
 \ge(3/4)^K(b_K/x_K)^{3/2}
 \ge(243/128)^{K/2}\longrightarrow\infty.               \tag{18}
\]
The cubic integer comparison supporting (18) is kernel checked.

For **every fixed source** \(n\), on the other hand,
\(K_{64}^k f(n)\) is eventually zero, unconditionally. If its orbit never
hits a target \(b_K\), every value is zero. If it does hit one, the
subsequent power-of-two path reaches the floor and is killed permanently.
Every source that ever contributes is therefore a provably convergent
source. Pointwise disappearance alone does not imply norm disappearance
for these unbounded observables.

This does not apply the example to \(\mathbf1\): the latter is bounded,
and \(0\le K_H^k\mathbf1\le1\) supplies a summable dominating function.
Its norm always tends to the mass of the eternal-survivor set. Proving
that this limit is zero is still the missing Collatz assertion.

## 6 Verification and the remaining estimate

Run `python3 verify_killed_operator_bounds.py` for sequential Lean builds
and independent exact replay. The replay reconstructs complete killed
fibres by both inverse branching and canonical affine lifting, tests the
high-target comparison and norm bounds with directed square-root
enclosures, and checks the coefficient limits and convergent witnesses.
Finite numerical checks do not certify the Banach-space arguments.
The [verification record](../results/killed-operator-bounds/verification.json)
keeps these scopes separate.

This calculation supplies the previously missing conversion from
coefficient bounds to an actual weighted operator bound. Its rate is
expansion, so a contraction of this whole space cannot establish decay
of the actual survivor mass. The next estimate must use the specific
functions \(K_H^k\mathbf1\), or justified additional regularity that
excludes the norm-growth witnesses. No such estimate, new successful
survivor horizon, nontrivial integer cycle, or divergent orbit is proved
here. The 128 existing finite mass contractions retain their original scope.
