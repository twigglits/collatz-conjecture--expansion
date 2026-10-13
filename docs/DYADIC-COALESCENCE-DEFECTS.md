# Unweighted dyadic defects persist even inside the known basin

**Status: eighteen kernel theorems verify the finite arithmetic. Counting
and measure conclusions are written. The nonsummability conclusion uses
the already replayed external positive-lower-density theorem at target
one, but does not use the written natural-passage premise. Full Collatz
remains unresolved.**

The preceding [coalescence-tail note](COALESCENCE-TAIL.md) proposed a
sufficient criterion for zero weighted escape mass: summability of the
dyadic cells where normalized infinite weights change. It bounded those
cells by a larger set of even adjacent pairs that never balance. This
follow-up proves that the larger set has a nonsummable sequence of
fractions on the **actual dyadic source intervals**. The obstruction
already comes from the known basin of one.

Thus the unweighted sufficient condition has a false premise under the
existing external input. The condition involving the actual infinite
weights is still open. In particular, this result does not prove their
changes are nonsummable or that any Collatz orbit diverges.

## 1. A grade and an auxiliary weight in the known basin

Use the shortcut map \(U\). If \(n\) reaches one at time \(t\), with
\(a=w_t(n)\) odd inputs, define its integer arrival grade
\[
 g(n)=t-2a.
\]
The earlier [grade theorem](COALESCENCE-GRADES.md) proves that the grade
does not depend on the chosen arrival time. Two convergent starts
eventually have equal endpoints at the same clock and with equal odd
counts if and only if their grades agree. Also
\[
 g(2n)=g(n)+1.                                           \tag{1}
\]

For this note define the **auxiliary** grade weight
\[
 V(n)=\frac{2^{g(n)}}n
\]
on the known basin, and zero outside it. This is not the infinite
remaining weight \(W_\infty\). Every known-basin start has
\(W_\infty=0\), whereas \(V(n)>0\).

For an even step, \(V(n)=V(U(n))\). For an odd step before the first
arrival at one, \(n\ge3\) and
\[
 V(n)=\frac{3n+1}{4n}V(U(n))\le\frac56 V(U(n)).
\]
At one, \(V(1)=1\). Therefore, if the **first** arrival has \(a\)
odd inputs,
\[
 \boxed{0<V(n)\le(5/6)^a\le1.}                         \tag{2}
\]
The kernel checks the integer inequality
\[
 3^{w_t(n)}2^tU^t(n)\le10^{w_t(n)}n                    \tag{3}
\]
for any positive prefix avoiding one before time \(t\). At arrival,
division of (3) by \(3^a4^a n\) gives (2). The avoidance condition is
essential: the odd input one has factor one in the grade weight and
does not satisfy the strict \(5/6\) bound.

## 2. Few sources can reach one with a bounded number of odd inputs

The earlier dyadic envelope gives, at any arrival,
\(2^t\le4^a n\). In particular the kernel proves
\[
 n\le2^L,\quad a\le A
 \quad\Longrightarrow\quad t\le L+2A.                  \tag{4}
\]
An endpoint and the complete parity word determine the source uniquely:
reverse an even step by doubling, and reverse an odd step by
\((2y-1)/3\) when integral. This injectivity, the parity-word length,
and its odd count are kernel checked.

Set \(M=L+2A\). Encode an arrival word of length at most \(M\)
and with at most \(A\) ones by its length and the increasing list of
one-positions, padded with zeros to length \(A\). Positions are
one-based so zero is an unambiguous padding symbol. Each of the
\(A+1\) entries lies in \(\{0,\ldots,M\}\). Distinct sources
cannot share this code. Hence the written counting consequence is
\[
 \boxed{\#\{n\le2^L:n\text{ reaches 1 with at most }A
      \text{ odd inputs before its first arrival}\}
      \le(L+2A+1)^{A+1}.}                               \tag{5}
\]
The polynomial is deliberately loose. It is valid for each fixed \(A\)
and does not require knowing which other starts converge. For example,
it implies the natural mean of \(V\) is zero: outside the set in (5),
\(V\le(5/6)^{A+1}\); first let the source cutoff tend to infinity,
then let \(A\) tend to infinity.

## 3. Uninterrupted balanced descendants have zero limiting fraction

Call a binary refinement from \(n\) to a child *balanced* in this
paragraph if either the child is \(2n\), or it is \(2n+1\) and the
pair \((2n,2n+1)\) eventually coalesces with equal odd counts at the
same time. If \(n\) converges, so does any such child, and its grade
is \(g(n)+1\). The new module proves this transport and its iteration.

Fix any convergent positive root \(m\), and follow \(k\) such
refinements to a descendant \(n\). Then
\[
 2^km\le n<2^k(m+1),\qquad g(n)=g(m)+k.
\]
Consequently
\[
 V(n)>c_m:=\frac{2^{g(m)}}{m+1}>0.
\]
By (2), its first-arrival odd count is bounded by a constant \(A_m\)
depending only on \(m\): choose any integer \(A_m\ge0\) for which
\((5/6)^{A_m+1}\le c_m\). With \(m+1\le2^{L_m}\), (5) gives
\[
 \#\{\text{balanced descendants at depth }k\}
 \le(k+L_m+2A_m+1)^{A_m+1}.                              \tag{6}
\]
There are \(2^k\) possible binary descendants in total. Thus the
probability that independent fair child choices remain balanced for
all \(k\) steps tends to zero, and the probability of remaining
balanced forever is zero. This theorem uses only the given root's
convergence, not universal convergence or a density theorem.

There is a concrete uniform bound at root one. Here \(c_1=1/2\),
and \((5/6)^4<1/2\). Every uninterrupted balanced descendant of one
therefore reaches one with at most **three odd inputs**. The kernel
proves the stronger finite statement
\[
 \boxed{n<2^{k+1},\quad g(n)=k
       \quad\Longrightarrow\quad a(n)\le3,}             \tag{7}
\]
where the arrival defining \(a(n)\) is the first one. Algebraically,
(3) and \(t=k+2a\) imply \(6^a<2\cdot5^a\), which fails when
\(a\ge4\). The resulting written bound is
\[
 \Pr(\text{the first }k\text{ refinements from 1 are balanced})
 \le\min\{1,(k+8)^4/2^k\}\longrightarrow0.              \tag{8}
\]
It does not assert that an unbalanced child fails to converge. In fact
all the finite examples checked below reach one.

## 4. The actual unweighted dyadic errors are not summable

For \(x\) uniformly distributed on \([1,2)\), write
\(n_k(x)=\lfloor2^kx\rfloor\). Its next value is either
\(2n_k\) or \(2n_k+1\), with a fair next bit. Put
\[
 B_k=2^{-k}\#\{2^k\le n<2^{k+1}: (2n,2n+1)
            \text{ never coalesces in the balanced sense}\}.
\]
Let \(D_k\) be the event that the next bit chooses the odd child
**and** this pair never balances. Its Lebesgue measure is exactly
\(B_k/2\). These are actual eventual events on the stated source
intervals, not complete-period failures at a finite time.

Let \(S\) be the set where only finitely many \(D_k\) occur.
After its last defect, the path uses only balanced refinements. If it
then visits a convergent prefix \(n_K=m\), every later refinement
is balanced from this convergent root. Section 3 says this has measure
zero in its binary cylinder. A countable union over \(K,m\) is still
null. Therefore, for almost every \(x\in S\), the prefixes eventually
all lie **outside** the known basin.

Let \(q_k\) be the known-basin fraction in
\([2^k,2^{k+1})\). Dominated convergence on \(S\) now implies
\[
 \limsup_k q_k\le |S^c|=\Pr(D_k\text{ occurs infinitely often}). \tag{9}
\]
If the known basin has lower natural density \(\delta>0\), then
\(\limsup q_k\ge\delta\). Otherwise all sufficiently late dyadic
blocks would have fractions strictly below \(\delta\); summing them
with their geometric sizes would contradict that lower density.

The previously replayed
[external predecessor theorem](PREDECESSOR-DENSITY-REVIEW.md) supplies
such a positive \(\delta\) at target one. Combining it with (9) and
the first Borel--Cantelli lemma proves
\[
 \boxed{\Pr(D_k\text{ infinitely often})\ge\delta>0,
        \qquad\sum_k B_k=\infty.}                       \tag{10}
\]
No existence of a natural density, no numerical value of \(\delta\),
and no natural-passage mixing premise is needed. The external theorem
is used only for positivity of the known basin's lower density.

If full Collatz holds, then \(q_k=1\) for every \(k\), so (9)
gives infinitely many unweighted defects for **almost every** \(x\).
At the same time \(W_\infty(n)=0\) for every integer, and all the
weighted dyadic changes in the previous note vanish identically. These
two conclusions are compatible. Unbalanced arrival grades within the
known basin are not evidence of escaping mass.

## 5. Verification scope and what this changes

[`DyadicCoalescenceDefects.lean`](../lean/DyadicCoalescenceDefects.lean)
has eighteen audited roots. They prove grade transport, the strict
prefix envelope, bounded arrival length, parity-word injectivity, and
the three-odd-step cap (7). The polynomial counting, limiting fractions,
and measure arguments (5)--(6), (8)--(10) are written proofs.

[`verify_dyadic_coalescence_defects.py`](../verify_dyadic_coalescence_defects.py)
freshly builds the new module and its six local dependencies. It
revalidates the completed external replay's 389 project source, object,
and log hashes; it does not rebuild that package or all its third-party
dependencies. The finite census certifies first arrivals through
\(2^{19}\), independently replays selected paths and inverse words,
checks the grade contractions, and counts balanced refinements from
several explicitly convergent roots. Finite mean grade weights have
exact rational enclosures, not asymptotic error bounds.

The [verification record](../results/dyadic-coalescence-defects/verification.json)
keeps these scopes separate. Reproduce with:

```sh
python3 verify_dyadic_coalescence_defects.py
```

The previous implication from \(\sum B_k<\infty\) to zero escape
mass remains logically correct, but its premise is now ruled out for
the actual map under the replayed density theorem. Further work must
estimate the actual infinite-weight changes, which discard these
known-basin grade defects, or control their finite-clock replacements.
No vanishing escape mass or exclusion of other positive cycles has
been obtained here.
