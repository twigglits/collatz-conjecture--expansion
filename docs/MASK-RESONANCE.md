# Exact resonance restrictions for every mechanical mask

Consider the full family of independent cyclic \(21\to12\) edits from
[MECHANICAL-MASKS.md](MECHANICAL-MASKS.md). Let \(k>89\) be the odd-step
count and \(N=\lceil k\log_2 3\rceil\) the shortcut count. No bound on the
number of selected edits is imposed. Assume that the edited word is
primitive and realizes a positive integer cycle.

**Written theorem with a finite arithmetic certificate.** Such a cycle
cannot have
\[
 \boxed{2^{21}\le N\le10^{1000}.}                         \tag{1}
\]
The lower endpoint is \(2,097,152\). This excludes every mask at every
count pair in the interval, rather than testing particular subsets.
It uses neither an irrationality-measure theorem nor an unknown \(H_0\).

The all-period argument also gives the necessary condition
\[
 \boxed{N\ge2^{64}\quad\Longrightarrow\quad
  0<\frac{\log2}{\log3}-\frac{k}{N}<\frac4{N^3}.}        \tag{2}
\]
The unbounded range beyond \(10^{1000}\) remains unresolved.

[MaskResonance.lean](../lean/MaskResonance.lean) proves the Farey denominator
lemma, extraction of a checked bracket for every denominator in the
interval, and the integer induction supporting (2). Its finite logarithm
arithmetic and complete bracket cover use native evaluation. The
combinatorial catalog, real logarithm enclosure, and application to cycles
are written proofs below. No full Collatz proof or novelty claim is made.

## 1. A catalog for the unrestricted family

Put \(\rho=k/N\) and \(\eta=2\rho-1\). The base binary shortcut word is
mechanical, with neither \(00\) nor \(111\), since
\(3/2<N/k<8/5\). A \(21\to12\) edit moves the first 1 of a base \(11\)
edge one place to the left. All such moved pairs are disjoint.

Take a base window of length \(L\), with \(O\) ones and \(e\in\{0,1,2\}\)
zero endpoints. Its number of internal \(11\) edges is
\[
 B=2O-L-1+e.
\]
Let \(E\) count eligible moved-one centers in the window, allowing an
edge to exit at its right endpoint. If that exit occurs, the last bit is
1, so \(e\le1\), and \(E\le B+1\le2O-L+1\). Otherwise
\(E\le B\le2O-L+1\). Mechanical balance gives \(O<\rho L+1\), hence
\[
 E<\eta L+3.                                             \tag{3}
\]

An edited factor on \([t,t+m)\) can be affected only by centers in
\([t,t+m+1)\), a window of length \(m+1\). The base factor on
\([t-1,t+m+2)\), of length \(m+3\), identifies all these centers and has
at most \(m+4\) possibilities. Equation (3) bounds their independent choices.
This includes cyclic seams and windows longer than one period; allowing
independent choices at repeated copies only enlarges the catalog.

The exact comparison \(3^{101}>2^{160}\) gives
\(\rho<101/160\), so \(\eta<21/80\). Since the number of centers is an
integer, a safe integer catalog bound is
\[
 \boxed{P_w(m)\le B_m:=(m+4)\,
  2^{\lfloor21(m+1)/80\rfloor+3}.}                       \tag{4}
\]
This counts the full family. It imposes no no-\(11\), alternating-selection,
transition-density, or low-entropy restriction.

## 2. Integrality turns the catalog into a resonance requirement

Write
\[
 \alpha=\frac{\log2}{\log3},\quad
 D=2^N-3^k>0,\quad
 \lambda=N\log2-k\log3,\quad
 \delta=D/2^N=1-e^{-\lambda}.
\]
Critical counts give \(0<\lambda<\log2<1\).

The prefix one-count of each rotated edited word satisfies
\(J_w(i)>\rho i-2\): the mechanical error is less than one and the
disjoint moves change any cyclic prefix count by at most one. Therefore
every term in its shortcut affine numerator
\[
 \Phi(w)=\sum_{i:w_i=1}2^i3^{k-J_w(i)-1}
\]
is less than \(3\cdot2^N\). Every shortcut state is consequently less
than \(3k/\delta\), as in the preceding mask notes.

If \(B_m<N\), two of the \(N\) distinct integer cycle states have the same
first \(m\) parity bits. Their difference is a nonzero multiple of \(2^m\).
Thus their diameter is at least \(2^m\), giving
\[
 \delta<\frac{3k}{2^m}.
\]
The parity congruence and diameter implication are already kernel proved
in [CollatzRepetition.lean](../CollatzRepetition.lean).

Since \(e^\lambda>1+\lambda\) and \(\lambda<1\), we have
\(\delta>\lambda/(1+\lambda)>\lambda/2\).
Also \(\log3>1\) and \(\rho<2/3\). We obtain the general necessary test
\[
 \boxed{B_m<N\quad\Longrightarrow\quad
   0<\alpha-\frac{k}{N}<\frac4{2^m}.}                    \tag{5}
\]
In particular, none of this reasoning uses the effective threshold from
the earlier logarithm-theorem argument.

For (2), let \(t=\lfloor\log_2N\rfloor\ge64\) and \(m=3(t+1)\).
Then \(2^m>N^3\), while (4) gives
\[
 B_m<32(3t+7)\,2^{63t/80}<2^t\le N.                     \tag{6}
\]
The second strict inequality follows from the kernel theorem
\[
 [32(3t+7)]^{80}<2^{17t}\qquad(t\ge64).
\]
Its proof checks the base case \(t=64\) exactly and uses
\[
 16(3t+10)\le17(3t+7),\qquad17^{80}<2^{337}
\]
for the induction step. Substituting this window into (5) proves (2).
For the finite interval (1), the checker chooses larger admissible windows
when useful, using the exact integer bound (4) rather than the coarse (6).

There is also an asymptotic restriction on an unbounded sequence of such
cycles. Put \(\eta_*=2\alpha-1\). The unrounded estimate (3) gives
\(P_w(m)<8(m+4)2^{\eta_*(m+1)}\). For any fixed
\(0<\varepsilon<1/\eta_*\), choosing
\[
 m=\left\lfloor(1/\eta_*-\varepsilon)\log_2N\right\rfloor
\]
makes that catalog \(O((\log N)N^{1-\eta_*\varepsilon})<N\)
for sufficiently large \(N\). Equation (5) then yields
\[
 0<\alpha-k/N<8N^{-1/\eta_*+\varepsilon}.
\]
In particular, infinitely many such cycles with unbounded periods would
force the irrationality exponent
\[
 \mu(\alpha)\ge\frac1{2\alpha-1}\approx3.82.
\]
This is a written necessary condition, not a contradiction: the published
estimate used in the earlier notes does not give a sufficiently small
upper bound for \(\mu(\alpha)\).

## 3. An explicit rational enclosure of the logarithm ratio

For \(0<z<1\), integrate the finite geometric identity to obtain
\[
 \log\frac{1+z}{1-z}
 =2\sum_{j=0}^{n-1}\frac{z^{2j+1}}{2j+1}
   +2\int_0^z\frac{v^{2n}}{1-v^2}\,dv.
\]
The remainder is positive and less than
\(2z^{2n+1}/((2n+1)(1-z^2))\).

Set \(P=8192\), \(n=4096\), and, for \(q=2,3\), compute the integers
\[
 A_q=\sum_{j=0}^{n-1}
 \left\lfloor\frac{2^{P+1}}{(2j+1)q^{2j+1}}\right\rfloor.
\]
Each rounded term loses less than one unit at scale \(2^P\), and the
finite certificate checks
\[
 2^{P+1}<(2n+1)(q^2-1)q^{2n-1}.
\]
Thus the scaled analytic remainder is less than one, and
\[
 \frac{A_q}{2^P}
 <\log\frac{q+1}{q-1}
 <\frac{A_q+n+1}{2^P}.
\]
All denominators are positive. Since \(q=3\) gives \(\log2\) and \(q=2\)
gives \(\log3\), the explicitly computed fractions
\[
 L=\frac{A_3}{A_2+n+1},\qquad
 U=\frac{A_3+n+1}{A_2}
\]
satisfy \(L<\alpha<U\). The compiler checks the integer sums, positivity,
ordering, and scaled-remainder comparisons. The displayed real-series
argument is written, not a Lean theorem about logarithms.

## 4. Checked Farey brackets cover every period in the interval

For each accepted row, the checker has a starting denominator \(s\),
a window \(m\), and two fractions \(a/b<c/d\). It checks
\[
 \begin{gathered}
 b,d>0,\quad bc=ad+1,\quad U<c/d,\quad a/b<L,\\
 B_m<s,\qquad L-a/b>4/2^m.                              \tag{7}
 \end{gathered}
\]
The last comparison is performed by exact multiplication:
\[
 4L_{\rm den}b<
   (L_{\rm num}b-aL_{\rm den})\,2^m.
\]
The sign is checked before natural-number subtraction is used.

This row excludes a mask cycle for every
\(s\le N<\min(10^{1000}+1,b+d)\). Indeed \(k/N<\alpha<U<c/d\).
If also \(a/b<k/N\), the positive integers
\[
 u=kb-aN,\qquad v=cN-kd
\]
would satisfy \(du+bv=N\), implying \(N\ge b+d\), a contradiction.
This elementary Farey denominator lemma is kernel proved and does not
require \(k/N\) to be reduced.

Hence \(k/N\le a/b\), and (7) gives
\(\alpha-k/N>4/2^m\). But \(B_m<s\le N\), so (5) gives the opposite
strict inequality. This excludes every mask in that denominator interval.

An integer continued-fraction calculation proposes the brackets. A bounded
binary search proposes each window length. Neither generator is trusted:
every property in (7) is checked independently. Brackets that do not extend
coverage are skipped. An accepted row advances the starting point exactly
to the endpoint it covers; exhaustion succeeds only after the final endpoint
has been reached. The theorem for this recursive checker extracts a
validated row for every integer \(2^{21}\le N\le10^{1000}\).

An independent exact Python replay finds 1,927 accepted intervals. This
count describes the compressed certificate, not the number of periods or
masks excluded. The Lean theorem quantifies all periods in the interval.
No value \(2^N\) or \(3^k\) with astronomically large \(N,k\) is constructed.

## 5. Closing the smaller range with an external published result

The local certificate by itself starts at \(2^{21}\). There is also a
corollary using a published general cycle bound.
[Eliahou, Theorem 1.1, Discrete Mathematics 118 (1993)](https://doi.org/10.1016/0012-365X(93)90052-U)
shows that a nontrivial shortcut cycle with minimum exceeding \(2^{40}\)
has at least 17,087,915 states. The paper's introduction cites the completed
convergence check through \(2^{40}\), which supplies that minimum condition.
These are external mathematical and computational inputs; they were not
replayed by this local Lean certificate.

Accepting that published result, the interval (1) covers every remaining
nontrivial period at most \(10^{1000}\). Therefore a nontrivial primitive
integer cycle in this full critical mask family would have
\[
 \boxed{N>10^{1000}.}                                   \tag{8}
\]
This corollary does not use a purported complete Collatz proof or an
unverified modern improvement to the published lower bound.

## 6. Remaining scope and reproduction

The [narrow-cycle classification](NARROW-CYCLE-MASKS.md) now transfers this
result to arbitrary primitive integer cycles with \(3M+1<8m\): every such
cycle has the required critical mask form. Consequently every nontrivial
cycle with \(N\le10^{1000}\) satisfies \(3M+1\ge8m\), with the same external
small-period input as Section 5.
The [automatic-order theorem](MASK-FOLDED-ORDER.md) shows why folded rank
tests do not remove the remaining unbounded mask periods.

The family still has infinitely many possible periods beyond the finite
endpoint. The resonance condition (2) alone does not eliminate them, and
the available irrationality bound used in the earlier notes is too weak to
contradict it. Arbitrary halving words need not belong to this mask family.
Aperiodic divergent trajectories are not addressed.

The proof boundaries are:

| Component | Verification |
|---|---|
| Farey denominator lemma and complete interval-cover extraction | Lean kernel |
| Integer induction and constants for the cubic resonance condition | Lean kernel |
| Dyadic integer sums and all accepted rational-bracket rows | Lean native evaluation, with kernel checker soundness |
| Mechanical catalog, height, real-series bounds, and cycle assembly | Written proofs |
| General lower period bound used only in (8) | Eliahou's published result and its cited external convergence computation |

Reproduce with the pinned compiler from the repository root:

    lean lean/MaskResonance.lean
    python3 verify_mask_resonance.py

The [verification record](../results/mask-resonance/verification.json) saves
commands, compiler output, source hashes, and the independent replay.
The mathematical goal remains a proof or disproof for every positive
integer; neither (1), (2), nor (8) completes it.
