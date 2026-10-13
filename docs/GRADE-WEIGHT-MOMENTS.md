# A power bound for the auxiliary grade weight

**Status: thirteen finite arithmetic and all-depth moment identities are
kernel checked. The real inequalities, limits, and measure arguments below
are written. The power bound needs no passage or predecessor-density
assumption. Collatz remains unresolved.**

The auxiliary weight from the
[dyadic-defect audit](DYADIC-COALESCENCE-DEFECTS.md) has an unconditional,
uniform power bound on actual initial intervals. This weight vanishes on
every orbit that fails to reach one. The separate weight that detects
escape is not controlled by this bound.

## 1. A decreasing finite-time extension

Let \(U\) be the shortcut map, \(x_t=U^t(n)\), and let \(a_t\)
count odd inputs before time \(t\). For positive \(n\), put
\[
 V_t(n)=\frac{2^t x_t}{4^{a_t}n}.
\]
An even step preserves this quantity. At an odd input \(x\), its
multiplier is \((3x+1)/(4x)\le1\). Hence
\[
 0<V_{t+1}(n)\le V_t(n)\le1.                              \tag{1}
\]
The multiplier equals one at \(x=1\); at every other positive odd
input it is at most \(5/6\). Every infinite positive orbit has infinitely
many odd inputs: a tail containing only halvings would eventually cease
to be a positive integer. It follows that
\[
 V(n):=\lim_tV_t(n)=
 \begin{cases}
 2^{t-2a_t}/n,&U^t(n)=1\text{ for some }t,\\
 0,&\text{the orbit never reaches one}.
 \end{cases}                                             \tag{2}
\]
After reaching one, the shortcut cycle \(1,2\) preserves \(V_t\).
Thus (2) agrees with the arrival-grade definition in the preceding audit.
This argument allows both other cycles and divergence.

## 2. Exact moments of the affine correction

Write
\[
 2^tU^t(n)=3^{a_t}n+b_t(n),\qquad b_t(n)\ge0,
\]
and use a common denominator \(4^t\):
\[
 E_t=4^{t-a_t},\quad P_t=3^{a_t}E_t,\quad Q_t=b_tE_t.
\]
Then
\[
 V_t(n)=\frac{P_t(n)}{4^t}+\frac{Q_t(n)}{4^t n}.           \tag{3}
\]
All three integer data are periodic in \(n\) with period \(2^t\).
The two lifts \(n\) and \(n+2^t\) have the same first \(t\) data
and opposite endpoint parity. At the next step, the even child transforms
\((P,E,Q)\) into \((4P,4E,4Q)\), and the odd child transforms it
into \((3P,E,3Q+2^tE)\). Summing the two children gives
\((7P,5E,7Q+2^tE)\).

Consequently, over one complete period,
\[
 \boxed{\sum_{n=1}^{2^t}P_t(n)=7^t,\quad
        \sum_{n=1}^{2^t}E_t(n)=5^t,\quad
        3\sum_{n=1}^{2^t}Q_t(n)+7^t=10^t.}                \tag{4}
\]
These are identities for every depth, not extrapolations from a finite
enumeration. [GradeWeightMoments.lean](../lean/GradeWeightMoments.lean)
proves the integer affine identities, monotonicity, periodicity, child
recursions, and moments. Its sums use representatives \(0\le n<2^t\);
periodicity replaces zero by \(2^t\) in (4). Division and the remaining
estimates are written steps.

## 3. Uniform control on initial intervals

Set \(c_t(n)=Q_t(n)/4^t\). Equations (1) and (3) give
\(0\le c_t(n)/n\le1\), while (4) gives
\[
 S_t:=\sum_{n=1}^{2^t}c_t(n)
     =\frac{(5/2)^t-(7/4)^t}{3}.
\]
For any real \(Y\ge1\), separate the sources at \(Y\). There are
at most \(Y\) positive integers at most \(Y\), and each remaining
denominator exceeds \(Y\). Therefore
\[
 \sum_{n=1}^{2^t}\frac{c_t(n)}n\le Y+\frac{S_t}Y.
\]
Take \(Y=(8/5)^t\). Applying (3)--(4) yields the explicit bound
\[
 \boxed{\frac1{2^t}\sum_{n=1}^{2^t}V_t(n)
 \le (7/8)^t+(4/5)^t+\frac13(25/32)^t
 \le\frac73(7/8)^t.}                                    \tag{5}
\]
The affine correction is controlled separately; it has not been discarded
as a small error uniformly in the source.

Let \(\eta=\log_2(8/7)>0\), approximately \(0.192645\). For an integer
\(X\ge1\), choose \(t=\lceil\log_2X\rceil\). Nonnegativity extends
the source sum to \(2^t\), and monotonicity handles every later time.
Since \(X\le2^t<2X\), (5) implies
\[
 \boxed{\frac1X\sum_{n=1}^X V_T(n)
       \le\frac{14}{3}X^{-\eta}\quad
       (T\ge\lceil\log_2X\rceil),\qquad
       \frac1X\sum_{n=1}^XV(n)\le\frac{14}{3}X^{-\eta}.} \tag{6}
\]
The second inequality follows pointwise from \(V\le V_t\); no exchange
of an uncontrolled source limit and time limit is needed. In particular
the natural mean of \(V\) is zero, with a power rate. The earlier audit
only needed a qualitative zero mean obtained by counting paths with a
fixed number of odd steps.

Here the chosen population really is one parity period at time \(t\).
This argument gives no bound on the escape weight at a longer logarithmic
clock, the source-scale issue in the
[coalescence audit](PREFIX-COALESCENCE-AUDIT.md).

## 4. A summable auxiliary amplitude

For \(1\le x<2\), write \(n_k=\lfloor2^kx\rfloor\). Equation (6)
and nonnegativity imply
\[
 \int_1^2 V(n_k)\,dx
 =2^{-k}\sum_{2^k\le n<2^{k+1}}V(n)
 \ll (7/8)^k.
\]
Tonelli's theorem gives \(\sum_k V(n_k)<\infty\) for almost every
\(x\). It also gives finite total amplitude variation for
\(z_k(x)=2^kV(n_k)/n_k\), since \(0\le z_k\le V(n_k)\) and
\(|z_{k+1}-z_k|\le z_{k+1}+z_k\).

This does not say that the sets where successive values differ are
summable. The preceding audit proves that unweighted grade defects occur
infinitely often on a set of positive measure, using the external
positive-density theorem. Small amplitudes and infinitely many changes
are compatible on the actual map.

## 5. The escape weight has a different critical factor

For the same shortcut path, let
\[
 W_t(n)=\frac{n3^{a_t}}{2^tx_t}.
\]
This is the product that retains \(3x/(3x+1)\) at each odd input,
as in [WEIGHTED-DISSIPATION.md](WEIGHTED-DISSIPATION.md). The exact
duality is
\[
                       V_t(n)W_t(n)=(3/4)^{a_t}.          \tag{7}
\]
Thus (5)--(6) do not bound \(W_t\) from above. In particular, \(V\)
is positive on every start reaching one even though its mean is zero.
That zero mean is compatible with a basin of natural density one.
The earlier packing argument makes \(W_\infty\) positive, with a
uniform positive lower bound, precisely on divergent starts.

One weaker version of the previous sufficient refinement condition is
worth isolating. Define the actual escape-weight refinements
\[
 h_k(x)=2^kW_\infty(n_k)/n_k.
\]
Assume the earlier written natural-density/component law and the replayed
external predecessor theorem. If a divergent orbit exists, its set of
divergent starts has a natural density \(\lambda\in(0,1)\): positivity
comes from that orbit's predecessors, and the known basin has positive
lower density as well. For any set of integers of natural density
\(\lambda\), the functions \(\mathbf1_E(n_k)\) converge weakly against
every integrable test function on \([1,2)\) to the constant \(\lambda\).
This follows first for interval indicators from the defining density
limit and then for integrable functions by approximation.

Apply this to the measurable set of binary paths making only finitely
many visits to \(E\). Dominated convergence makes the integral on that
set tend to zero, while weak convergence makes it tend to \(\lambda\)
times the set's measure. The set is null. Apply the same argument to
the complement of \(E\). Almost every binary path therefore changes
between divergence and nondivergence infinitely often.

At each such change, \(h_k\) changes between zero and a value at least
\(e^{-8192/3}/2\). Hence, under the stated inputs, existence of any
divergent orbit would force
\[
 \sum_k|h_{k+1}(x)-h_k(x)|^2=\infty
                         \quad\text{for almost every }x. \tag{8}
\]
In particular, a finite integral of this squared variation would exclude
divergence. **No such bound for \(W_\infty\) is proved here.** The
summable amplitude in Section 4 concerns \(V\). Neither (6) nor this
conditional criterion excludes other positive cycles.

## 6. Verification scope

```sh
python3 verify_grade_weight_moments.py
```

[The verification record](../results/grade-weight-moments/verification.json)
separates the thirteen audited kernel roots, independent exact finite
checks, and written bounds. It builds the three local modules afresh and
revalidates the relevant prior manifests. The finite replay checks whole
period moments through depth 20, actual source-interval rational
enclosures, direct trajectory samples, lifted residue data, and the exact
duality with the correction product. All sampled terminal paths reach
one; they do not decide an unresolved infinite orbit.

The unconditional power bound does not use external PLD, passage mixing,
or a claimed density-one convergence theorem. Those inputs occur only
in the explicitly conditional interpretation of (8), through the prior
notes. No additional external theorem is adopted.
