# Narrow integer cycles must be critical mechanical masks

Let a primitive positive odd Collatz cycle have \(k\) distinct odd states,
minimum \(m\), maximum \(M\), and total halving count \(N\). Thus its
shortcut period is \(N\), and its odd edges satisfy
\[
 2^{h_i}x_{i+1}=3x_i+1,\qquad h_i\ge1.
\]

**Written reduction theorem.** If the cycle is nontrivial and
\[
 \boxed{3M+1<8m,}                                        \tag{1}
\]
then its halving word is an independent \(21\to12\) mask of a critical
mechanical word:
\[
 N=\lceil k\log_2 3\rceil,\qquad \gcd(k,N)=1.
\]
This applies to an arbitrary integer cycle satisfying (1); membership
in the mask family is a conclusion.

The new arithmetic is kernel checked in
[NarrowCycleMasks.lean](../lean/NarrowCycleMasks.lean).
Sorting the cycle, assembling the rank rotation, and identifying the
complete cyclic word remain written arguments, given below.

Two consequences follow from the existing mask results:

- For \(2^{21}\le N\le10^{1000}\), every nontrivial primitive positive
  cycle must satisfy \(3M+1\ge8m\).
- With the published small-period input already recorded in
  [MASK-RESONANCE.md](MASK-RESONANCE.md#5-closing-the-smaller-range-with-an-external-published-result),
  the same conclusion holds for every \(N\le10^{1000}\).

Equivalently, throughout that range the odd maximum is at least
\((8m-1)/3\). This extends the finite mask exclusion to a geometric class
of arbitrary cycles. It does not exclude larger periods or all cycles.

The later [explicit logarithm bound](EXPLICIT-LOG-GAP.md) extends this
finite range through \(10^{4000}\) and proves \(4M\ge9m+5\) at every
period. It removes the nonnumerical dependency in Section 5 using a new
integral estimate and extended finite certificate, with the identified
external prime and small-period inputs.

The subsequent [edit-position argument](MASK-SPAN-BOUND.md) strengthens
the all-period span restriction to \(20M>49m\), using this classification
and a catalog that also accounts for the assumed odd maximum.

## 1. Odd spacing makes the halving count critical

First, any primitive odd cycle with \(M<3m\) has \(k\le m\).
Sort its odd members as \(y_0=m<\cdots<y_{k-1}=M\).
Consecutive distinct odd integers differ by at least two, so
\[
 m+2(k-1)\le M<3m,
\]
which gives \(k\le m\). Both the spacing induction and this implication
are kernel proved.

Here is an entirely integer proof of the resulting critical power bracket.
For an edge with \(x_i\ge m\),
\[
 m\,2^{h_i}x_{i+1}
 =m(3x_i+1)\le(3m+1)x_i.
\]
Multiplication around the cycle and cancellation of the positive states
give
\[
 m^k2^N\le(3m+1)^k.                                    \tag{2}
\]
For integers \(0\le j\le a\), induction proves
\[
 (a-j)(a+1)^j\le a^{j+1}.                              \tag{3}
\]
Indeed, the induction step uses
\((a-j-1)(a+1)\le a(a-j)\).
Apply (3) with \(a=3m,j=k\). Since \(k\le m\) and \(m>0\),
\(2(a-k)>a\), and therefore
\[
 (3m+1)^k<2(3m)^k.
\]
Together with (2), this gives \(2^N<2\cdot3^k\).
Every edge also has \(2^{h_i}x_{i+1}>3x_i\), giving the other strict
inequality:
\[
 \boxed{3^k<2^N<2\cdot3^k.}                            \tag{4}
\]
The generic theorem `cycle_critical` checks (4) for arbitrary finite
positive affine cycles with \(k\le m\). Its proof uses neither logarithms
nor native evaluation. Taking logarithms in the written argument converts
(4) into \(N=\lceil k\log_2 3\rceil\).

Condition (1) implies \(M<3m\), so this applies to every cycle considered here.

## 2. Only halving exponents one and two are possible

If any \(h_i\ge3\), then
\[
 8m\le8x_{i+1}\le2^{h_i}x_{i+1}=3x_i+1
 \le3M+1<8m,
\]
a contradiction. Thus all \(h_i\) belong to \(\{1,2\}\).

Call a state high when \(x_i\ge2m\), and set
\[
 a_i=\begin{cases}1&x_i\ge2m,\\0&x_i<2m,\end{cases}
 \qquad c_i=2^{1-a_i},\qquad u_i=c_ix_i.
\]
Then \(2m\le u_i<4m\). The folded values are distinct: a scale-one value
is odd and a scale-two value is even; equality within the same scale
would give the same original state. Their minimum is \(u_0=2m\) when
the cycle is cut at \(x_0=m\).

A high state cannot use halving one: its successor would exceed \(3m\),
whereas \(M<3m\). A halving-two edge always ends below \(2m\), because
\[
 4x_{i+1}=3x_i+1\le3M+1<8m.
\]
Consequently every high state is isolated. It is entered by halving one
and left by halving two.

The folded edge has the exact form
\[
 2^{b_i}u_{i+1}=3u_i+c_i,\qquad
 b_i=h_i+a_{i+1}-a_i\in\{1,2\}.                         \tag{5}
\]
The Lean module checks the folded range, distinctness, equation (5),
both possible values of \(b_i\), and the entry/exit rules for a high state.

## 3. Folded ranks give a mechanical base word

For folded values \(u<v\) and \(c,d\in\{1,2\}\),
\[
 3u+c<3v+d.
\]
Also, if \(2m\le u,v<4m\), then
\[
 3v+d<2(3u+c).
\]
These comparisons are kernel proved. They are the two-scale version of
the ordering inputs in [FOLDED-CYCLES.md](FOLDED-CYCLES.md).

Sort the \(k\) folded values. Equation (5) shows that the \(b=1\) sources
form the initial segment \(3u+c<8m\), and the \(b=2\) sources form its
complement. The equality boundary belongs to \(b=2\).
Successors increase within each segment. The second displayed inequality
places every \(b=2\) image before every \(b=1\) image.

Thus, if \(r\) sources use \(b=2\), the successor permutation on ranks is
\(j\mapsto j+r\pmod k\). The primitive cycle visits every rank, so
\(\gcd(k,r)=1\); this last implication is also checked in
[FoldedCycleBounds.lean](../lean/FoldedCycleBounds.lean).
Since \(k>1\), both branches occur, so \(0<r<k\).

The layers telescope in (5), giving
\[
 N=\sum_i h_i=\sum_i b_i=k+r,\qquad \gcd(k,N)=1.
\]
Starting at rank zero therefore gives precisely
\[
 b_i=\left\lfloor\frac{(i+1)N}{k}\right\rfloor
     -\left\lfloor\frac{iN}{k}\right\rfloor.              \tag{6}
\]

## 4. Every high state selects one disjoint edit

If \(a_i=1\), Section 2 gives
\[
 a_{i-1}=a_{i+1}=0,\quad
 (h_{i-1},h_i)=(1,2),\quad (b_{i-1},b_i)=(2,1).
\]
Thus the high state selects exactly the edit \(21\to12\) at midpoint \(i\).
High states are never adjacent, so these selected pairs are disjoint.
At every other edge, the relation
\[
 h_i=b_i+a_i-a_{i+1}
\]
leaves the base exponent unchanged. This reconstructs the entire actual
word, including the cyclic seam. At the minimum cut \(a_0=0\); a selected
pair cannot straddle that midpoint.

For the period range of the resonance certificate, \(k>89\) follows from
\(N\le2k\). The critical base word then has the full eligible-pair structure
used in [MECHANICAL-MASKS.md](MECHANICAL-MASKS.md). Equation (6) and the
selected high-state midpoints put the cycle inside that complete family.
Its word is primitive because a repetition count would divide both \(k\)
and \(N\), which are coprime.

The resonance certificate rejects every member for
\(2^{21}\le N\le10^{1000}\). This proves the local period-range corollary.
For smaller \(N\), the external input is exactly the one already recorded:
Eliahou's Theorem 1.1, combined with its cited convergence computation
through \(2^{40}\), puts any nontrivial shortcut cycle above this smaller
range. See [Eliahou (1993)](https://doi.org/10.1016/0012-365X(93)90052-U).
That computation has not been rerun here.

## 5. An eventual span bound for arbitrary cycles

The classification also transfers the unbounded
[mask-transition theorem](MASK-TRANSITIONS.md).
Let \(H_0\) be its effective, currently nonnumerical logarithm threshold.
For every nontrivial primitive cycle,
\[
 \boxed{N\ge\max(H_0,2^{2048})
 \quad\Longrightarrow\quad 4M\ge9m+5.}                 \tag{7}
\]

To see this, first suppose (1) holds. The mask-transition theorem gives at
least one pair of consecutive halving-one edges. Starting from its odd
state \(x\ge m\), those two edges end at
\[
 z=(9x+5)/4\le M,
\]
which proves (7).
If (1) fails, \(3M+1\ge8m\) already implies (7) for \(m\ge5\).
A nontrivial cycle has \(m\ge5\), since starts 1 and 3 reach the known cycle.

More precisely, if a cycle satisfying (1) has \(q>0\) halving-\(11\)
occurrences, their starting states are distinct odd integers. Sorting them
and applying the same two-step identity gives
\[
 \boxed{9m+18q\le4M+13.}                               \tag{8}
\]
The two-step identity and the spacing implication (8) are kernel proved.
For sufficiently long narrow cycles, the existing transition and density
theorems supply further lower bounds on \(q\).

This original proof leaves a nonnumerical threshold in (7), so its two
ranges alone cannot be joined. The subsequent [explicit logarithm
argument](EXPLICIT-LOG-GAP.md) closes that gap and proves (7)'s span
conclusion at every period. It does not establish an all-period \(8/3\)
span bound.

## 6. Verification and scope

The new Lean module uses only kernel proofs with standard logical axioms.
It checks the power bounds for arbitrary parameters, the count/minimum
inequality for a sorted odd list, the local normalization and edge rules,
and the two-rise span bounds.
There are no admitted proofs or native computations in that module.

The finite-cycle sorting, cyclic mask identification, and assembly with
the existing analytic results remain written proofs. The earlier
resonance cover still uses native evaluation for its finite arithmetic;
the corresponding real logarithm and factor-catalog arguments remain written.

The [verification record](../results/narrow-cycle-masks/verification.json)
also supplies a fresh check of the preceding
[automatic folded-order theorem](MASK-FOLDED-ORDER.md), whose earlier note
lacked a saved record. Commands and source hashes distinguish new checks
from reused evidence.

These results do not show that every integral ordered numerator is trivial.
Narrow cycles of unbounded period, wider cycles, and aperiodic divergence
remain to be excluded to prove the full conjecture.
