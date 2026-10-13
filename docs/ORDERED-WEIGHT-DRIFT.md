# Controlling drift before reversal of the odd-count order

**Status: thirty-one arithmetic roots are kernel checked. The real estimates,
integrals, and infinite sums below are written deductions. The contribution
after a count reversal remains uncontrolled. Neither escape nor additional
cycles are excluded.**

The [previous energy estimate](COALESCENCE-ENERGY-CAPS.md) leaves a lower
bound on the signed refinement drift open. This note bounds the negative
drift on cells where the adjacent odd-step counts have never reversed their
initial order. Its sum over all time offsets is at most fourteen.
It also proves that the pointwise time-loss estimate used here cannot
extend to all cells with any fixed constant.

No new external theorem is used for these bounds. The eventual implication
from bounded energy to absence of escape retains the earlier written
packing argument and the replayed external predecessor theorem.

## 1. A shifted reciprocal weight

Use the shortcut map \(U\), and put
\[
 x_t=U^t(n),\quad a_t=\#\{j<t:x_j\text{ odd}\},\quad
 f_t(n)=\frac{3^{a_t}}{2^t x_t},\quad
 z_t(n)=\frac{3^{a_t}}{2^t(x_t+1)}.
\]
All uses of these fractions have \(n>0\). The exact identity
\[
 U(x)+1=3^{x\bmod2}(\lfloor x/2\rfloor+1)                 \tag{1}
\]
gives, according to the current endpoint \(x=x_t\),
\[
 \begin{array}{c|cc}
 &f_t-f_{t+1}&z_t-z_{t+1}\\\hline
 x\text{ odd}&f_t/(3x+1)&0\\
 x\text{ even}&0&f_t x/((x+1)(x+2)).
 \end{array}                                               \tag{2}
\]
Thus both weights decrease with time. The shifted weight charges even
steps; the original weight charges odd steps. This use of \(z_t\) does
not replace the escape weight by the earlier auxiliary grade weight.

Keep \(n_k=\lfloor2^k x\rfloor\), \(x\in[1,2)\), and define
\[
 A_{s,k}=2^k f_{s+k}(n_k)=H_{s,k},\quad
 Z_{s,k}=2^k z_{s+k}(n_k),\quad g_k=2^k/n_k.
\]
Here \(0<Z_{s,k}\le A_{s,k}\le g_k\le1\). Both refinements copy
their even child exactly. Write \(B\) for the odd-child value of \(A\)
and \(\widetilde B\) for that of \(Z\), on a given parent cell.

## 2. Order before a count reversal

For the pair \(2n,2n+1\), let \(X_i,Y_i\) be its endpoints and
\(a_i,b_i\) its odd counts. At time one,
\[
 X_1=n,\quad Y_1=3n+2,\quad a_1=0,\quad b_1=1,
 \qquad Y_1+1=3(X_1+1).
\]
Say the pair is **ordered through time \(T\)** if
\(a_i\le b_i\) for every \(1\le i\le T\). This is a condition
on the whole finite history, not just the terminal counts.
Then
\[
             Y_T+1\le3^{b_T-a_T}(X_T+1).                 \tag{3}
\]
Indeed \(y+1\le P(x+1)\), with integral \(P\ge0\), implies
\(\lfloor y/2\rfloor+1\le P(\lfloor x/2\rfloor+1)\).
Apply (1), and use the nonnegative new count difference, to propagate
(3) one step. The base case is the equality at time one.

In particular, at the first positive return of equal odd counts the
endpoints satisfy \(Y_T\le X_T\). Before that return, the initially
positive difference \(b_i-a_i\) cannot become negative without passing
through zero, since it changes by at most one each step. This proves the
endpoint order suggested by the previous exploratory calculation. It
does not imply equality of the endpoints or balanced coalescence.

[OrderedWeightDrift.lean](../lean/OrderedWeightDrift.lean) proves (1),
the all-time propagation, the first-return consequence, and the exact
refinement cross-product inequality. On an ordered cell at pair clock
\(T=s+k+1\), division by the positive endpoints gives
\[
                       Z_{s,k}\le\widetilde B\le B.
\]
If \(X=U^{s+k}(n)\) is the parent endpoint, this yields
\[
              A(A-B)_+\le \frac{A^2}{X+1}.               \tag{4}
\]
The kernel also checks an integer cross-multiplied version of the
reciprocal bound underlying (4).

## 3. Charge the ordered part to actual time losses

The bounds \(A\le1\), \(3X+1\le3(X+1)\), and
\(X+2\le2X\) for positive even \(X\), together with (2), give
\[
 \frac{A_{s,k}^2}{X+1}
 \le3(A_{s,k}-A_{s+1,k})+2(Z_{s,k}-Z_{s+1,k}).           \tag{5}
\]
Only one of the two differences is nonzero at each step. Equation (5)
holds on every cell; using it to bound the downward refinement also
requires the order hypothesis of (4).

Let \(N_s^{\rm ord}\) be the sum over all levels of the negative drift
on ordered cells:
\[
 N_s^{\rm ord}=\sum_{k\ge0}\frac1{2^{k+1}}
   \sum_{2^k\le n<2^{k+1}}
    \mathbf1_{\text{ordered through }s+k+1}
        A_{s,k}(n)\bigl(A_{s,k}(n)-B_{s,k}(n)\bigr)_+.
                                                               \tag{6}
\]
The factor \(1/2\) accounts for the odd half of each parent cell.
Define two total deficits
\[
 M_s=\sum_{k\ge0}\int_1^2(g_k-A_{s,k}),\qquad
 \widetilde M_s=\sum_{k\ge0}\int_1^2(g_k-Z_{s,k}).        \tag{7}
\]
Their finiteness is proved next; both are nondecreasing in \(s\).
Summing (4)--(5), with that half-cell factor, gives
\[
 \boxed{N_s^{\rm ord}\le
  \tfrac32(M_{s+1}-M_s)+(\widetilde M_{s+1}-\widetilde M_s).} \tag{8}
\]
All terms being summed on the right before telescoping are nonnegative.

## 4. Finite deficits and a uniform Cesaro bound

As in the [reciprocal moment calculation](ESCAPE-WEIGHT-REFINEMENTS.md),
write \(2^t x_t=3^{a_t}n+b_t\), \(D_t=3^{t-a_t}\), and
\(Q_t=b_tD_t\). The shifted affine correction is
\[
 R_t=Q_t+2^tD_t,\qquad
 z_t(n)=\frac1{n+R_t/3^t}.
\]
The new kernel proofs give its periodicity, its exact affine identity,
and the all-depth moment
\[
          2\sum_{0\le n<2^t}R_t(n)+6^t=3\,8^t.        \tag{9}
\]
Thus the total shifted real correction over a period is
\(\tfrac32(8/3)^t-2^{t-1}\). Bounding each deficit by its
nonnegative correction divided by \(2^k\), and placing the actual
source annulus in one period, gives
\[
 \int(g_k-A_{s,k})\le\tfrac12(8/3)^s(2/3)^k,\qquad
 \int(g_k-Z_{s,k})\le\tfrac32(8/3)^s(2/3)^k.             \tag{10}
\]
For \(s=0\) the annulus is a translated whole period; for \(s\ge1\)
it is contained in one period. This argument does not replace a short
initial interval by an average over a longer period.

Let \(J(s)=\lceil121s/50\rceil\). The earlier kernel cutoff gives
\((8/3)^s(2/3)^{J(s)}\le1\). Use the bound one on levels below
\(J(s)\), and sum (10) on the remaining levels:
\[
 M_s\le J(s)+\tfrac32,\qquad
 \widetilde M_s\le J(s)+\tfrac92.                       \tag{11}
\]
In particular the series in (7) are finite. Sum (8) over
\(0\le s<S\), discard the nonnegative initial deficits, and apply
(11). For every positive integer \(S\),
\[
 \boxed{\sum_{s<S}N_s^{\rm ord}
    \le\tfrac52J(S)+\tfrac{27}4
    <\tfrac{121}{20}S+\tfrac{37}4.}                    \tag{12}
\]
Consequently \(\limsup_{S\to\infty}S^{-1}\sum_{s<S}N_s^{\rm ord}
\le121/20\). This is an unconditional bound on an infinite sum of
actual weighted downward changes. It is not a bound on the whole drift.
No passage-mixing or predecessor-density premise is used in (1)--(12).

### A stronger bound from the actual positive-offset transitions

The special initial relation \(Y=3X+2\) gives more than (3). While the
unshifted reciprocal difference is negative, write
\(Y=3^dX+c\), so \(d=b-a\ge1\) and \(c>0\). Starting from
\((d,c)=(1,2)\), its only positive-offset states are:

- \((1,2)\) while the parent inputs are odd;
- \((d,1)\), \(d\ge1\), and \((d,2)\), \(d\ge2\), after
  the first even parent input.

In the initial state an odd parent input preserves \((1,2)\), and an
even parent input produces \((1,1)\). Subsequently, an even parent
input takes \((d,1)\) to \((d+1,2)\), and \((d,2)\) to
\((d,1)\). The first odd parent input after that even run makes
\(Y'\le3^{d'}X'\): for offset one this is
\((3^dX+1)/2\le3^{d-1}(3X+1)/2\); for offset two with \(d\ge2\)
it follows from \(7\le3^d\). Once this unshifted order holds, it
persists as long as the count order remains nonnegative.

All four transition statements and persistence are kernel checked.
Their induction gives the following **written** classification: an
ordered downward change at parent time \(t\) requires its entire parent
parity prefix to have the form \(1^L0^{t-L}\). In particular its first
\(k\) bits have at most one change, from odd to even.

The kernel proves that exactly \(k+1\) residues modulo \(2^k\) have
this property, and proves the same count on \([2^k,2^{k+1})\). For
the count, appending a zero preserves every admissible prefix, while
appending a one preserves just the all-odd prefix. The two high-bit
children have opposite new endpoint parities. This gives the exact
recurrence \(c_{k+1}=c_k+1\), with \(c_0=1\), without a finite
enumeration assumption. Hence, uniformly in \(s\),
\[
 N^{\rm ord}_{s,k}\le\frac{k+1}{2^{k+1}},\qquad
                         N_s^{\rm ord}\le2.             \tag{12a}
\]

There is also a source-height cutoff. For a positive source
\(2^k\le n<2^{k+1}\) with parity word \(1^L0^{t-L}\), the exact
run formula is
\[
       2^tU^t(n)+2^L=3^L(n+1),\qquad 2^L\mid n+1.
\]
The divisibility follows from the odd-run formula and coprimality of
powers of two and three. Thus \(L\le k+1\), and positivity gives
\(2^t<3^L(n+1)\le2^{3(k+1)}\). Therefore \(t\le3k+2\), and a
downward ordered change at \(t=s+k\) must have \(s\le2k+2\).
This height deduction and the real sums are written, not additional
kernel claims. Combining it with (12a), and using nonnegative summation,
\[
 \boxed{\sum_{s\ge0}N_s^{\rm ord}
   \le\sum_{k\ge0}\frac{(2k+3)(k+1)}{2^{k+1}}=14.}     \tag{12b}
\]
In particular this part of the negative drift tends to zero. More
explicitly, if \(K=\max(0,\lceil s/2\rceil-1)\), then
\(N_s^{\rm ord}\le(K+2)2^{-K}\). The earlier loss-budget argument
remains useful as a different estimate, but its Cesaro constant is
superseded by this summable all-offset bound.

## 5. The remaining contribution is real

Let \(N_s^{\rm rev}\) be (6) with the complementary indicator: the
odd member's accumulated count has at some time fallen below the even
member's. For each fixed \(s\), both drift parts are finite. In fact
the earlier geometric estimate on \(e_{s,k}\) makes
\(\sum_k\sqrt{e_{s,k}}\) finite, and
\(\int|H_{s,k}(H_{s,k+1}-H_{s,k})|\le\sqrt{e_{s,k}}\).
This also establishes **absolute** convergence of the fixed-offset
drift series, a stronger statement than was needed in the previous note.

The exact energy identity gives
\[
 E_s\le\tfrac12+2N_s^{\rm ord}+2N_s^{\rm rev}.
\]
Therefore a sufficient remaining estimate is
\[
                \liminf_{S\to\infty}\frac1S
                       \sum_{s<S}N_s^{\rm rev}<\infty.  \tag{13}
\]
Indeed (12b) would give a bounded subsequence of Cesaro energy means,
and hence a bounded subsequence of individual energies at unbounded
offsets. The prior Fatou, rigidity, packing, and PLD argument would then
exclude escape. **Equation (13) is unproved.** Additional positive
cycles would still require exclusion.

The reversal part cannot simply be dropped. For \(n=37,k=5,s=6\),
the pair \(74,75\) at clock twelve has endpoints \(5,2\) and counts
\(5,4\). Its parent and odd-child values are
\(243/320\) and \(81/128\), a strictly downward change. Both sources
reach the known cycle; these finite certificates are kernel checked.

## 6. No fixed pointwise loss charge covers the reversal part

There is a stronger obstruction than a single example. Restrict the
earlier jump family to positive even \(j\), and write
\[
 n=\frac{8(64^j-1)}9,\quad k=6j-1,\quad s=6,
 \quad A_*=3^{3j-1}.
\]
The new kernel specialization gives, at the parent clock \(t=k+6\),
\[
 U^t(n)=(A_*+1)/4\text{ odd},\quad a_t(n)=3j+1,
 \qquad U^t(3n+2)=1,\quad a_t(3n+2)=2.
\]
At pair clock \(t+1\) the counts are \(3j+1\) and three, so all
these cells belong to the reversal part. The exact refinement values are
\[
 P=\frac{9A_*}{16(A_*+1)},\qquad B=\frac{27}{64}.
\]
Since the parent endpoint is odd, its shifted time loss is zero. If
\(\delta=P-A_{7,k}\) is the original time loss, then
\[
 \frac{P(P-B)}{\delta}
 =\frac{9(A_*-3)(3A_*+7)}{256(A_*+1)}
 \ge\frac{27(A_*-3)}{256}\longrightarrow\infty.          \tag{14}
\]
Thus **no fixed constant multiplying the two immediate parent time
losses can bound every downward refinement**. The downward product
itself tends to \(81/1024>0\), whereas both immediate losses tend to
zero. This uses exact finite trajectories for every family member; it
assumes no long-term convergence or divergence for the whole family.
Their individual cell lengths are summable, so (14) does not refute an
integrated bound for (13).

The next estimate must therefore average the reversal contribution over
the actual source intervals, exploit cancellation with positive drift,
or use losses over more than one parent step. Extending (5) by changing
its constants cannot suffice.

## 7. Verification

```sh
python3 verify_ordered_weight_drift.py
```

The [verification record](../results/ordered-weight-drift/verification.json)
separates fresh kernel compilation, independent exact finite replay, and
the written real/measure deductions. All thirty-one new audited roots use
standard axioms only. The replay checks complete shifted moments, ordered
and first-return inequalities, the parity classification and source-height
cutoff in finite cases, exact one-turn counts, rational time-loss charging, finite sums
with exact rational enclosures, and the all-parameter family's stated
finite instances. Finite data do not certify (13). Prior manifests are
hash-validated; no external proof bundle is rebuilt or newly adopted.
