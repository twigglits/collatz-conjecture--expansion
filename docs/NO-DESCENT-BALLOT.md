# A sharper count for starts that never descend

Let \(U\) be the shortcut Collatz map and put
\[
 E=\{n\ge1:\ U^t(n)\ge n\text{ for every }t\ge0\},\qquad
 \alpha=\log_3 2,\qquad \sigma=H_2(\alpha).
\]
Here \(H_2\) is binary entropy and \(\sigma\approx0.94995553\).
Every least counterexample belongs to \(E\).

**Written theorem.** An absolute constant \(C\) exists such that, for all
integers \(a\ge0,L\ge1\),
\[
 \boxed{\#(E\cap[a,a+L))\le
 C\,\frac{L^\sigma}{(1+\log L)^{3/2}}.}                        \tag{1}
\]
In fact, the same bound holds for positive starts in that interval that avoid descent
only through \(\lceil\log_2L\rceil\) steps.

The proof uses a published ballot theorem and the kernel-checked finite
parity-collision lemma. It is not a complete Lean formalization. The constant
is not numerically specified. This sharpens the counting estimate for this
particular set of starts; it does not prove \(E=\{1\}\) or the conjecture.

## 1. Survival gives a prefix barrier

Fix an integer \(\ell\ge1\), and suppose \(n\ge\ell\) and
\(n_t=U^t(n)\ge n\) for \(0\le t\le\ell\). Let \(J_t\) count odd
steps before time \(t\). Exact multiplication of the step equations gives
\[
 n_t=n\,3^{J_t}2^{-t}P_t,\qquad
 P_t=\prod_{\substack{0\le i<t\\n_i\ {\rm odd}}}
       \left(1+\frac1{3n_i}\right).
\]
Using \(\log(1+u)\le u\) and \(n_i\ge n\),
\[
 \log P_t\le\frac{t}{3n}.
\]
Thus \(n_t\ge n\) implies
\[
 J_t-\alpha t
 \ge-\frac{t}{3n\log3}
 \ge-\frac1{3\log3}>-\frac13
 \qquad(0\le t\le\ell).                                     \tag{2}
\]
This retains every prefix constraint, whereas a final-count tail estimate
would retain only the condition at \(t=\ell\).

## 2. Count the barrier-respecting words

For counting only, sample independent bits \(B_i\) with
\(\Pr(B_i=1)=\alpha\), and write \(S_t=\sum_{i=1}^t(B_i-\alpha)\).
These increments have mean zero, variance \(\alpha(1-\alpha)>0\), and
lattice span one.

The upper half of Addario-Berry and Reed's Theorem 1 states that, for this
walk, a constant \(K\) bounds the probability of staying strictly positive
at intermediate times and ending in \([u,u+1)\) by
\(K\max(u,1)r^{-3/2}\), for every \(r\ge1,u>0\).
The upper bound has no \(u\le\sqrt r\) restriction.
See [the primary paper, Section 2, Theorem 1](https://problab.ca/louigi/papers/ballot.pdf).

Prepend a bit 1 to every word satisfying (2).
Since \(1/2<\alpha<2/3\), its new first partial sum is
\(1-\alpha>1/3\), and all the extended partial sums are strictly positive.
Partition the original endpoint \(d=J_\ell-\alpha\ell\) into bins
\[
 d\in[s-1/3,s+2/3),\qquad s=0,1,2,\ldots .
\]
The extended endpoint then lies in the length-one interval beginning at
\(u=s+2/3-\alpha>0\). Its probability is at most
\[
 K(s+1)(\ell+1)^{-3/2}.                                    \tag{3}
\]
Here the event consisting of prepended words is a subset of the positive
walk event; no independence of the actual Collatz parity sequence is assumed.

Put \(z=\alpha/(1-\alpha)>1\).
An individual original word of endpoint \(d\) has probability
\[
 \alpha^{J_\ell}(1-\alpha)^{\ell-J_\ell}
 =2^{-\sigma\ell}z^d.
\]
Prepending 1 multiplies this probability by \(\alpha\). In bin \(s\), each
extended word therefore has probability at least
\(\alpha\,2^{-\sigma\ell}z^{s-1/3}\).
Dividing (3) by that lower bound and summing proves
\[
 \#\{\text{words satisfying (2)}\}
 \le K_0\frac{2^{\sigma\ell}}{(\ell+1)^{3/2}},                 \tag{4}
\]
where one may take
\[
 K_0=\frac{Kz^{1/3}}{\alpha}
       \sum_{s\ge0}(s+1)z^{-s}
     =\frac{Kz^{1/3}}{\alpha(1-z^{-1})^2}.
\]

## 3. Transfer the count to every interval

For \(L>1\), set \(\ell=\lceil\log_2L\rceil\), so \(L\le2^\ell<2L\).
Distinct integers in \([a,a+L)\) cannot share the same \(\ell\)-bit parity
word: their difference would be divisible by \(2^\ell\) while having
absolute value less than \(L\).
This finite implication is checked by
`parity_gap_divisible` and `collision_of_small_gap` in
[CollatzRepetition.lean](../CollatzRepetition.lean).

All surviving starts \(n\ge\ell\) are consequently counted by (4).
There are at most \(\ell-1\) positive starts with \(n<\ell\). Hence
\[
 \#(E\cap[a,a+L))
 \le\ell+K_0\frac{2^{\sigma\ell}}{(\ell+1)^{3/2}}.
\]
The inequalities \(\ell\le1+\log_2L\), \(2^\ell<2L\), and the boundedness
of \((\ell+1)^{5/2}2^{-\sigma\ell}\) absorb the first term and convert the
second into (1). Enlarge \(C\) once to cover \(L=1\).
No forward-invariance or injectivity hypothesis on \(E\) is used.

## 4. Summability and future minima

Apply (1) to dyadic shells. The shell \([2^r,2^{r+1})\) contributes at
most \(C'(1+r)^{-3/2}\) to the weighted sum, so
\[
 \boxed{\sum_{n\in E}n^{-\sigma}<\infty.}                     \tag{5}
\]
If \(m_1<m_2<\cdots\) is any infinite subset of \(E\), then (1) on
\([0,m_r+1)\), together with \(m_r\ge r\), gives
\[
 m_r\ge c\,r^{1/\sigma}(1+\log r)^{3/(2\sigma)}
 \quad\text{for all sufficiently large }r.                   \tag{6}
\]

A nonrepeating positive-integer trajectory has distinct values and therefore
tends to infinity. Its successive strict future-tail minima form an infinite
increasing sequence in \(E\); (5) and (6) apply to this sequence, indexed by
the number of minima. If a minimum is \(m_r=n_t\), the next one is the
minimum of the tail beginning at \(t+1\), so
\[
 m_{r+1}\le U(m_r)\le(3m_r+1)/2.                             \tag{7}
\]
These two bounds are compatible: geometric growth satisfies both and allows
the series in (5) to converge.

## 5. Why this still leaves the contradiction open

The set \(E\) is not forward invariant: \(1\in E\), but \(U(1)=2\notin E\).
Images of the future-minimum set need not be future minima.
Thus (1) cannot be substituted for the ambient orbit-set count in
[ORBIT-PACKING-LOG.md](ORBIT-PACKING-LOG.md).

No lower bound on the frequency of future minima in orbit time has been
proved. Equation (6) concerns minimum count, not every time index. The
argument supplies neither a contradiction for all divergent orbits nor an
exclusion of all nontrivial cycles. The least-counterexample descent step
remains unresolved.

## 6. A forward-invariant boundary version

The same argument applies near the lower boundary of a larger set:
\[
 S_m=\{x\ge m:\ U^t(x)\ge m\text{ for every }t\ge0\}.
\]
This set is forward invariant, even though the map need not be injective
on it. Uniformly in positive integers \(m\),
\[
 \boxed{\#(S_m\cap[m,2m))
 \le C_1\,\frac{m^\sigma}{(1+\log m)^{3/2}}.}                 \tag{8}
\]

For \(m>1\), take \(\ell=\lceil\log_2m\rceil\le m\).
If \(x\in S_m\cap[m,2m)\), the exact product identity now gives
\[
 J_t-\alpha t
 \ge\log_3(m/x)-\frac{t}{3m\log3}
 >-\alpha-\frac13>-1\qquad(t\le\ell).
\]
Prepending three ones shifts these partial sums by \(3(1-\alpha)>1\).
The argument of Section 2, with this fixed prefix and barrier, gives
\(O(2^{\sigma\ell}/(\ell+1)^{3/2})\) admissible words. Parity-word
injectivity in \([m,2m)\) proves (8). Enlarge the constant for \(m=1\).
Only survival above \(m\) through the first \(\ell\) steps was needed.

A nonrepeating orbit starting at a future minimum \(m\) must therefore
first reach a value at least \(2m\) within
\(O(m^\sigma/(1+\log m)^{3/2})\) shortcut steps: all states before that
first escape are distinct and lie in the set counted by (8).
The estimate also bounds the total number of later visits to that interval.

This cannot be iterated by automatically replacing \(m\) with \(2m\).
After first reaching a value at least \(2m\), the orbit may return below \(2m\); membership
in \(S_m\) does not imply membership in \(S_{2m}\).
Nor does a fixed floor imply a global sublinear count: \(S_1\) is the
entire set of positive integers.

The existing bounds on successive minima are compatible with a concrete
integer sequence. For \(r\ge0\), let
\[
 \mu_r=48\left\lfloor100(4/3)^r\right\rfloor+7.
\]
It is strictly increasing, is always 7 modulo 48, and satisfies
\(\mu_{r+1}\le(3\mu_r+1)/2\). Indeed, with \(A=100(4/3)^r\ge100\),
the left side is at most \(64A+7\), while the right side is at least
\(72A-61\). Its inverse-\(\sigma\) sum converges geometrically, and it
eventually exceeds the minimum-count lower bound (6).

This sequence is not asserted to be a Collatz orbit. Its compatibility
shows why those inequalities and residue conditions alone cannot supply
the missing contradiction: the exact connections between successive
minima still matter. The boundary estimate and this example are written
deductions, not new Lean formalizations.
