# Close counts make folded order automatic

The folded-rank restriction does not eliminate the long critical masks
left open by [MASK-RESONANCE.md](MASK-RESONANCE.md). In that range, the
positive affine equations already force the rank comparisons for every
selection of edits.

The main algebraic theorem is kernel proved in
[MaskFoldedOrder.lean](../lean/MaskFoldedOrder.lean), without native
evaluation. Its application to the mask construction and real logarithms
is written below.

For coprime \(k,N\), \(k>1\), choose
\[
 1\le q<k,\qquad qN=kt+1.
\]
If
\[
 \boxed{2^t\le3^q,}                                      \tag{1}
\]
then every positive rational cycle in the full independent \(21\to12\)
mask family has strictly ordered folded coordinates and odd-state spread
less than four. This improves the earlier spread-eight bound in this
count regime, but supplies no integer divisibility obstruction.

## 1. An ordering theorem for arbitrary positive forcing

Label coordinates \(u_0,\ldots,u_{k-1}\) by residues \(j=0,\ldots,k-1\).
No ordering of their values is assumed. Suppose the coordinates satisfy
\[
 2^{\lfloor(j+N)/k\rfloor}u_{(j+N)\bmod k}
 =3u_j+c_j,\qquad c_j>0.                                \tag{2}
\]
The \(c_j\)'s may vary arbitrarily. The theorem says
\[
 \boxed{u_0<u_1<\cdots<u_{k-1}<2u_0.}                    \tag{3}
\]

To prove it, follow \(q\) edges beginning at label \(j\). The labels are
\((j+iN)\bmod k\). The accumulated exponent telescopes to
\(\lfloor(j+qN)/k\rfloor\), since \(j<k\). Every forcing term is positive,
so
\[
 3^q u_j<
 2^{\lfloor(j+qN)/k\rfloor}u_{(j+qN)\bmod k}.           \tag{4}
\]
If \(j<k-1\), the relation \(qN=kt+1\) turns (4) into
\[
 3^q u_j<2^t u_{j+1}.
\]
Condition (1) gives \(u_j<u_{j+1}\). At \(j=k-1\), the same calculation
gives
\[
 3^q u_{k-1}<2^{t+1}u_0,
\]
so \(u_{k-1}<2u_0\). This proves all of (3), including its final endpoint.

The Lean proof uses natural-number numerators. For rational coordinates,
multiply (2) by a common positive denominator to obtain the exact
integer hypotheses. The core theorem takes the strict edge inequalities;
a separate kernel lemma derives them from the positive forcing equations.
The scaled iterate used in the proof is
\[
 V_{j,i}=2^{\lfloor(j+iN)/k\rfloor}v_{(j+iN)\bmod k}.
\]
Lean proves \(V_{j,i+1}>3V_{j,i}\), its iterated version, the carry
identities, the adjacent comparisons, and the full pairwise bound
\(v_j<2v_i\) for all labels.

## 2. Which counts satisfy the power comparison

Let \(\lambda=N\log2-k\log3>0\). The determinant relation gives
\[
 k(q\log3-t\log2)=\log2-q\lambda.
\]
Thus a sufficient strict condition for (1) is
\[
 \boxed{q\lambda<\log2.}                                \tag{5}
\]
For an entirely integer form, it suffices that
\[
 (2^N)^q<2(3^k)^q.
\]
The implication from this power inequality and \(qN=kt+1\) to
\(2^t<3^q\) is also kernel proved.

Two exact examples are:

| \(k\) | \(N\) | \(q\) | \(t\) | Independent mask choices |
|---:|---:|---:|---:|---:|
| 306 | 485 | 53 | 84 | 127 |
| 2966 | 4701 | 665 | 1054 | 1231 |

Lean checks both determinant identities and both strict power comparisons.
The second row is the same count pair whose entire mask family was already
rejected by the [exact subset decoder](MASK-CYCLE-OBSTRUCTIONS.md#5-a-finite-target-reduction-and-the-remaining-work).
All its \(2^{1231}\) masks satisfy the new ordering criterion; their
nonintegrality is a separate arithmetic fact.

## 3. Apply the theorem to every independent mask

Use the lower mechanical base word
\[
 b_i=\lfloor(i+1)N/k\rfloor-\lfloor iN/k\rfloor.
\]
Set \(a_i=1\) at each selected \(21\) midpoint and \(a_i=0\) elsewhere.
Use cyclic indices, including \(a_k=a_0\). The edited exponents are
\[
 h_i=b_i+a_i-a_{i+1}\in\{1,2\}.
\]
Let \(x_i>0\) be the associated rational cycle, with
\(2^{h_i}x_{i+1}=3x_i+1\). Define
\[
 d_i=2^{2-a_i}\in\{2,4\},\qquad u_i=d_i x_i.
\]
The layer identity gives
\[
 2^{b_i}u_{i+1}=3u_i+d_i.                                \tag{6}
\]
There is no integrality assumption on \(x_i\).

Reindex by \(j=iN\bmod k\), a bijection because \(\gcd(k,N)=1\).
The base exponent at this label is \(\lfloor(j+N)/k\rfloor\), and
the next label is \((j+N)\bmod k\). Equation (6) is therefore exactly
the positive-forcing system (2). The theorem proves the claimed folded
order whenever (1) holds.

For any two labels, (3) gives \(u_j<2u_i\). Since the only scale
values are 2 and 4,
\[
 2x_j\le u_j<2u_i\le8x_i.
\]
Consequently
\[
 \boxed{x_j<4x_i\ \text{for every }i,j,\qquad
        M_{\rm odd}<4m_{\rm odd}.}                      \tag{7}
\]
This last finite scale argument is kernel checked for the natural
numerators, so it also applies after division by their common denominator.
The result does not depend on a chosen cut having an unselected midpoint.

## 4. The surviving integer-mask range already satisfies the condition

First, every mask in this family has rational spread below eight by the
earlier construction. For a primitive integer realization, the existing
[folded-cycle theorem](FOLDED-CYCLES.md) consequently gives
\(\gcd(k,N)=1\). This supplies the inverse \(1\le q<k\); coprimality
is not inferred from primitivity alone.

For \(N\ge2^{64}\), the proof in [MASK-RESONANCE.md](MASK-RESONANCE.md)
uses a catalog window \(m=3(\lfloor\log_2N\rfloor+1)\), with \(2^m>N^3\).
Before division by \(N\log3\), its height argument gives
\[
 \lambda<2\delta<\frac{6k}{2^m}<\frac4{N^2},
\]
because \(k/N<2/3\). Since \(q<k<N\),
\[
 q\lambda<4/N<\log2.
\]
The last comparison uses only \(N\ge2^{64}\) and \(\log2>2/3\).
Thus all such hypothetical integer masks satisfy (1), and (7) applies.

In particular, the range \(N>10^{1000}\) left by the preceding result
cannot be removed by adding the folded-order tests. Under the count
conditions forced on an integer realization, the tests accept every mask
choice even before divisibility is checked.

## 5. Infinitely many rational families pass all these tests

This is not limited to the two finite examples. Put \(\beta=\log_2 3\)
and take upper continued-fraction convergents \(N/k\) of \(\beta\).
Infinitely many satisfy
\[
 0<N/k-\beta<1/k^2,\qquad\gcd(k,N)=1,\qquad k\longrightarrow\infty.
\]
For completeness, the usual convergent identity is
\[
 \beta=\frac{p_n\tau+p_{n-1}}{q_n\tau+q_{n-1}},\qquad \tau>1.
\]
The determinant \(p_nq_{n-1}-p_{n-1}q_n=(-1)^{n-1}\) makes the
error alternate in sign and have magnitude
\(1/[q_n(q_n\tau+q_{n-1})]<1/q_n^2\). The denominators increase
without bound because \(\beta\) is irrational.

For all sufficiently large such pairs, \(N=\lceil k\beta\rceil\) and
\(3/2<N/k<8/5\). Moreover
\[
 \lambda=k\log2\,(N/k-\beta)<\log2/k,
\]
so every \(q<k\) satisfies (5). Every one of the
\(2^{\,2k-N}\) independent masks has the folded order (3) and spread
bound (7). All their cycle words are primitive: a repetition count
would divide both \(k\) and \(N\). Primality of \(k\) is not needed.

Their rational minimum still exceeds \(k/12\), by the original mask
height argument. The counting arguments in
[MECHANICAL-MASKS.md, Sections 3–4](MECHANICAL-MASKS.md#3-many-masks-are-far-from-every-mechanical-comparator)
also apply to these coprime counts. Thus some masks simultaneously have
half-Hamming distance greater than \(N/100\) from every matching mechanical
word and more than \(2^{m/8}\) length-\(m\) factors at
\(m=\lfloor\log_2N\rfloor\). Folded order and spread below four do not
force a uniformly small catalog.

These are positive rational cycle constructions, not positive integer
counterexamples. Their possible integer realizations still require the
exact ordered numerator divisibility test.

## 6. Verification and the remaining mathematical gap

The whole finite algebraic theorem in Section 1, its integer power
criterion, and the two-layer scale bound are kernel proved for arbitrary
parameters. No enumeration of masks, admitted proofs, custom axioms, or
native evaluation is used in the new module. The printed dependencies
are the standard logical axioms only.

The reindexing from mask words, logarithmic consequences, and infinite
continued-fraction family are written arguments. They are not asserted
to be a complete Lean formalization.

Reproduce the new kernel checks from the repository root:

    lean lean/MaskFoldedOrder.lean

The [verification record](../results/mask-folded-order/verification.json)
identifies the compiler, source hashes, and exact scope.

The remaining task is to exclude integral ordered numerators in the
unbounded mask range, or find another route that also addresses arbitrary
cycles and divergent trajectories. This theorem makes the limitation of
rank order explicit; it does not establish the Collatz conjecture.
