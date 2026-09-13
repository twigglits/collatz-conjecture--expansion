# Folded order constrains cycles of spread below eight

Let a primitive positive odd Collatz cycle have \(k\) distinct odd members,
minimum \(m\), maximum \(M\), and total halving exponent \(H\).

**Written theorem.**
\[
 \boxed{M<8m\quad\Longrightarrow\quad\gcd(k,H)=1.}            \tag{1}
\]
Thus every primitive integer cycle with noncoprime counts would have
\(M>8m\); equality is impossible because the extrema are odd.
The theorem also gives a mechanical normal form with three possible scale
layers. It does not exclude all coprime-count cycles.

The proof uses integer spacing, exact accelerated successors, and sorted
rank order. Its finite arithmetic and the coprimality implication from a
rotation covering all ranks are kernel checked in
[FoldedCycleBounds.lean](../lean/FoldedCycleBounds.lean).
The normalization, sorting argument, and complete assembly of (1) remain
written proofs. No novelty claim or complete Collatz proof is made.

The [forward-closure extension](FOLDED-CYCLE-INVERSIONS.md) now improves
the coprimality condition to \(M<9m+2\). Below spread sixteen it also
classifies every order inversion and bounds their number in terms of
\(\gcd(k,H)\). The new local and closure lemmas are kernel checked; the
sorting and permutation assembly remains written.

## 1. Normalize the odd states into one factor-of-two interval

Write the cycle in orbit order as \(x_0=m,x_1,\ldots,x_{k-1}\), with
\[
 2^{h_i}x_{i+1}=3x_i+1,\qquad H=\sum_{i=0}^{k-1}h_i,
\]
using cyclic indices. Define
\[
 a_i=\left\lfloor\log_2(x_i/m)\right\rfloor\in\{0,1,2\},
 \qquad c_i=2^{2-a_i},\qquad u_i=c_ix_i.
\]
Then \(4m\le u_i<8m\). Since \(x_i\) is odd, the power of two dividing
\(u_i\) exactly is \(c_i\in\{1,2,4\}\). Thus the folded states are
distinct: equality of two would imply equality of their odd parts.
Their minimum is \(u_0=4m\).

Put \(G(u_i)=3u_i+c_i=c_i(3x_i+1)\).
For two folded integers \(u<v\),
\[
 G(v)-G(u)=3(v-u)+c(v)-c(u)\ge3-3=0.                       \tag{2}
\]
Equality would require \(v=u+1,c(u)=4,c(v)=1\).
The corresponding odd sources would be \(x\) and \(4x+1\). They have
the same accelerated successor, because
\[
 3(4x+1)+1=4(3x+1).
\]
The accelerated map is injective on the members of a primitive cycle,
so equality is impossible. Hence \(G\) strictly preserves the order of
the folded cycle states.

Lean checks that multiplication by 1, 2 or 4 does not change an odd part,
and that distinct accelerated successors turn (2) into a strict inequality.
It keeps the distinct-successor hypothesis explicit.

The endpoints satisfy
\[
 G_{\min}=12m+4,\qquad G_{\max}\le24m-2<2G_{\min}.            \tag{3}
\]
For the upper bound, \(u\) is a multiple of \(c(u)\) below \(8m\);
thus \(u\le8m-c(u)\) and \(G(u)\le24m-2c(u)\le24m-2\).
The range comparison is also kernel checked.

## 2. The successor ranks form a rotation

The original edge equation becomes
\[
 G(u_i)=2^{b_i}u_{i+1},\qquad b_i=h_i+a_{i+1}-a_i.           \tag{4}
\]
Initially this is an equation in positive rational numbers with integer
\(b_i\). From \(u_{i+1}\in[4m,8m)\) and \(12m<G(u_i)<24m\), its
ratio lies strictly between \(3/2\) and 6. The only powers of two in that
interval are 2 and 4, so \(b_i\in\{1,2\}\).

Sort the folded values increasingly. The \(b=1\) sources, characterized
by \(G(u)<16m\), form an initial segment; the \(b=2\) sources form the
final segment. The boundary \(G(u)=16m\) belongs to the second branch.
Within either branch the successors increase. Moreover, every second-branch
image precedes every first-branch image because (3) gives
\[
 G_{\max}/4<G_{\min}/2.
\]
If \(r\) sources use \(b=2\), the successor permutation on ranks is therefore
\[
 j\longmapsto j+r\pmod k.                                  \tag{5}
\]
This is one \(k\)-cycle, so it visits every rank and \(\gcd(k,r)=1\).
The latter implication is kernel checked: when \(k>1\), reaching rank 1
forces every common divisor of \(k,r\) to divide 1; \(k=1\) is immediate.

Telescoping the layers in (4) yields
\[
 H=\sum_i b_i=k+r,\qquad \gcd(k,H)=\gcd(k,r)=1,
\]
proving (1). For \(k>1\), both branches occur; otherwise an increasing
permutation of a finite ordered set would be the identity.
Thus \(0<r<k\). The only positive integer one-member cycle is \(x=1,h=2\).

## 3. The layer constraints and exact remaining divisibility test

For a nontrivial cycle, the folded minimum has rank zero. Following (5)
therefore gives
\[
 \boxed{
 b_i=\left\lfloor\frac{(i+1)H}{k}\right\rfloor
     -\left\lfloor\frac{iH}{k}\right\rfloor,\qquad
 h_i=b_i+a_i-a_{i+1}.}                                    \tag{6}
\]
The first word is mechanical, but the actual halving word need not be.
The layers satisfy
\[
 a_0=a_k=0,\quad a_i\in\{0,1,2\},\quad
 a_{i+1}\le a_i+b_i-1.
\]
The last inequality is exactly positivity of \(h_i\).
In particular \(a_1=0\), and every actual exponent lies between 1 and 4.
Prefix sums differ from the mechanical prefix sums by \(a_0-a_i\).

These constraints leave exponentially many choices. At disjoint mechanical
\(21\) pairs whose midpoints are not index 0, setting the midpoint layer to 1
and all other layers to 0 independently changes \(21\) into \(12\).
Excluding at most one pair preserves the exponentially large subfamily of
the existing masks. It respects the fixed condition \(a_0=a_k=0\).
Layer positivity alone does not imply a small factor catalog.

There is a precise remaining integer condition. Put
\[
 D=2^H-3^k>0,\qquad B_{i,j}=\sum_{t<j}b_{i+t},\qquad
 V_i=\sum_{j=0}^{k-1}3^{k-1-j}2^{B_{i,j}}c_{i+j}.
\]
Iterating (4) gives
\[
 u_i=V_i/D,\qquad x_i=V_i/(c_iD).
\]
If \(W_i\) is the usual cyclic numerator of the actual halving word,
the telescoping layer relation gives \(V_i=c_iW_i\).
Each \(W_i\) is odd, so \(V_i\) has exactly the power of two \(c_i\).
Since \(D\) is odd, divisibility \(D\mid V_0\) is equivalent to
\(D\mid W_0\). The existing
[complete cycle criterion](../CollatzCycleCriterion.lean) then propagates
integrality and exact valuations to every rotation.

For fixed \(1<k\), \(k<H<2k\), coprime \((k,H)\), and positive \(D\),
the following is a complete finite reduction for spread below eight:

1. Choose layers satisfying the stated bounds and positivity conditions.
2. Check \(D\mid V_0\).
3. Check \(V_0\le V_i<2V_0\), with strict increasing order prescribed by
   the ranks \(ir\bmod k\).

These conditions reconstruct a primitive integer cycle with minimum
\(V_0/(4D)\) and maximum less than eight times that minimum.
Indeed \(x_i/m=2^{a_i}V_i/V_0\in[2^{a_i},2^{a_i+1})\), which also
verifies the chosen layers.
Conversely every such cycle supplies these data.
The third step is essential; arbitrary layer assignments need not preserve
the required order. The reduction does not show that every candidate fails.

## 4. Why the elementary ordering threshold cannot exceed eight

Let \(m=4q+3\), \(q\ge0\), and consider the two odd sources \(m\) and
\(8m+1\). With the next normalization scale, their folded integers are
\(u=8m<v=8m+1\), but their folded numerators satisfy
\[
 G(u)=24m+8>24m+4=G(v).
\]
Their exact accelerated successors are \((3m+1)/2=6q+5\) and \(6m+1\),
both within \([m,8m+1]\). These formulas, range bounds, and the strict
order reversal are kernel checked for every \(q\).

Thus local inversions occur at spread \(8+1/m\), arbitrarily close above
eight. These are two valid steps, not a cycle. They show that a larger
spread theorem would require additional global information, rather than
the same pointwise monotonicity argument.
The later extension uses precisely such information: the next successor
of \(6m+1\) is \(9m+2\), so a forward-invariant cycle cannot keep that
pair inside the smaller interval.
