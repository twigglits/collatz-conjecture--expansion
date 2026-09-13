# A logarithmic refinement of the uniform orbit bound

Retaining the square-root factor in the binomial estimate strengthens the
previous counting theorem to
\[
 \boxed{\#(S\cap[a,a+L))
 \le \frac{32768L^\sigma}{\sqrt{1+\log L}},
 \qquad \sigma=H_2(\log_3 2),}                           \tag{1}
\]
for integer \(a\ge0,L\ge1\), whenever \(S\) is forward invariant under the
Collatz shortcut map and that map is injective on \(S\).
It applies to every nonrepeating positive orbit and every cycle.
Logarithms without a subscript are natural.

This excludes the previously surviving endpoint growth condition
\[
 A_k=O(k^{1/\sigma}),\qquad A_k=3^k/2^{H_k},
\]
for a nonrepeating positive integer orbit. It does not exclude faster growth.
The conclusion concerns a running maximum, not each individual iterate.

The proof below is written mathematics, using the kernel-checked finite
transfer lemmas in [CollatzPacking.lean](../CollatzPacking.lean).
The binomial estimate, real functions, induction assembly, and limit
consequences are not formalized in Lean. No novelty claim is made.

The earlier bound \(128L^\sigma\) remains independently valid. One can use the
smaller of the two bounds; the explicit constant in (1) is deliberately loose,
so its improvement is asymptotic.

## 1. Ingredients and a uniform finite-sum estimate

Write
\[
 \alpha=\log_3 2,\qquad b=\log3,\qquad A=3^\sigma,\qquad
 g(L)=\frac{L^\sigma}{\sqrt{1+\log L}}.
\]
The elementary inequalities established in the
[previous proof](ORBIT-PACKING-BOOTSTRAP.md) give
\[
 \tfrac12<\alpha<\tfrac23,\quad
 \alpha<\sigma<1,\quad A>2,\quad 1<b<2.
\]
We also use \(\alpha>5/8\), which follows directly from \(3^5=243<256=2^8\).

For every positive integer \(J\),
\[
 \sum_{0\le j<J}g(3^j)
 <\frac{3A^J}{\sqrt{1+Jb}}.                             \tag{2}
\]
To verify this uniformly, put \(r=J-j\). Then
\[
 \sqrt{\frac{1+Jb}{1+(J-r)b}}
 =\sqrt{1+\frac{rb}{1+(J-r)b}}
 \le r+1.
\]
After dividing the sum by \(A^J/\sqrt{1+Jb}\), it is bounded by
\[
 \sum_{r=1}^J(r+1)A^{-r}
 <\sum_{r=1}^{\infty}(r+1)2^{-r}=3.
\]
Thus (2) needs no asymptotic estimate or interchange of nonuniform limits.

For a block of length \(2^\ell\), states with \(j\) odd steps map injectively
under \(U^\ell\) into a same-set interval of length \(3^j\). The number of
available weight-\(j\) residues is \(\binom{\ell}{j}\).
These are exactly the two inputs used in the previous induction.

## 2. The high-weight tail includes a square-root saving

Suppose \(\ell\ge128\), and set
\[
 J=\lfloor\alpha\ell\rfloor-6,\qquad p=J/\ell.
\]
Then
\[
 \frac9{16}<\frac58-\frac7{128}<p<\alpha<\frac23.         \tag{3}
\]
For \(j\ge J\), consecutive binomial coefficients satisfy
\[
 \frac{\binom{\ell}{j+1}}{\binom{\ell}{j}}
 =\frac{\ell-j}{j+1}<\frac79.
\]
Hence
\[
 \sum_{j\ge J}\binom{\ell}{j}<\frac92\binom{\ell}{J}.     \tag{4}
\]

Robbins's factorial inequalities give, for \(0<J<\ell\),
\[
 \binom{\ell}{J}
 <\frac{e^{1/(12\ell)}}{\sqrt{2\pi\ell p(1-p)}}\,
   e^{\ell h(p)},\qquad
 h(p)=-p\log p-(1-p)\log(1-p).
\]
See [Robbins, *A remark on Stirling's formula*, American Mathematical
Monthly 62 (1955), pp. 26–29](https://dornsife.usc.edu/sergey-lototsky/wp-content/uploads/sites/211/2024/02/Stirling-Robbins.pdf).
Only this factorial inequality is used from that paper.

On the interval in (3), \(p(1-p)\ge2/9\). Using \(\pi>3\) and
\(e^{1/12}<2\), the preceding display is less than
\(2e^{\ell h(p)}/\sqrt\ell\).
Also \(|h'(u)|<\log2\) for \(p\le u\le\alpha<2/3\), and
\(0<\alpha\ell-J<7\). Therefore
\[
 \ell h(p)<\ell h(\alpha)+7\log2,
 \qquad
 \binom{\ell}{J}<256\,\frac{2^{\sigma\ell}}{\sqrt\ell}.  \tag{5}
\]
Combining (4)–(5), the high-weight contribution from at most two aligned
blocks is less than
\[
 2304\,\frac{2^{\sigma\ell}}{\sqrt\ell}.                 \tag{6}
\]

## 3. Strong induction with explicit constants

Let \(C=32768\). Prove the desired bound \(Cg(L)\) by strong induction on
the positive integer \(L\), uniformly in the integer anchor \(a\).
Choose the least \(\ell\ge0\) with \(L\le2^\ell\), so \(2^\ell\le2L\).
The source interval meets at most two aligned blocks of length \(2^\ell\).

If \(\ell<128\), the already proved \(128L^\sigma\) estimate gives
\[
 \#(S\cap[a,a+L))
 \le128\sqrt{1+\log L}\,g(L)<2048g(L)<Cg(L).
\]
This is an independent base bound, not an assumption of (1).

For \(\ell\ge128\), use \(J\) from Section 2. Each low weight \(j<J\) has
\[
 3^j<3^J\le3^{-6}2^\ell<L.
\]
Thus the inductive hypothesis applies to every corresponding image interval.
By (2), the combined low-weight contribution is less than
\[
 6C\,\frac{3^{\sigma J}}{\sqrt{1+J\log3}}.
\]
Now \(J>\ell/2-7\), while \(\log3>1\) and \(\log L<\ell\). Consequently
\[
 \frac{1+\log L}{1+J\log3}
 <\frac{\ell+1}{\ell/2-6}<4.
\]
Together with \(3^{\sigma J}\le3^{-6\sigma}2^{\sigma\ell}\),
\(3^\sigma>2\), and \(2^\sigma<2\), this gives
\[
 \#\{\text{low-weight states}\}
 <6\cdot2^{-6}\cdot2\cdot2\,Cg(L)
 =\frac38 Cg(L).                                      \tag{7}
\]

For the high weights, (6) and
\[
 2^{\sigma\ell}<2L^\sigma,\qquad
 \sqrt{\frac{1+\log L}{\ell}}<2
\]
give
\[
 \#\{\text{high-weight states}\}<9216g(L)<\tfrac12Cg(L). \tag{8}
\]
Adding (7) and (8) closes the induction. Every recursive use was at a
strictly smaller integer interval length, and all estimates are uniform.

## 4. Endpoint growth and summability consequences

Let \(n_k\) be the accelerated odd states of a nonrepeating positive orbit.
As before,
\[
 n_k=n_0A_kP_k,\qquad
 A_k=3^k/2^{H_k},\qquad
 P_k=\prod_{i<k}\left(1+\frac1{3n_i}\right)\le P_\infty<\infty.
\]
Finiteness of \(P_\infty\) follows from the previously proved reciprocal
summability; no new hypothesis is introduced.

Let \(B_N=\max_{k\le N}n_k\) and \(M_N=\max_{k\le N}A_k\).
The \(N+1\) distinct positive odd states imply \(B_N\ge N+1\).
Applying (1) to \([1,B_N+1)\) yields
\[
 N+1\le\frac{CB_N^\sigma}{\sqrt{1+\log B_N}}.
\]
Since \(B_N\le n_0P_\infty M_N\), we obtain
\[
 \boxed{
 M_N\ge
 \frac{(N+1)^{1/\sigma}(1+\log(N+1))^{1/(2\sigma)}}
      {n_0P_\infty\,32768^{1/\sigma}}.}                 \tag{9}
\]
Therefore
\[
 A_k=o\!\left(k^{1/\sigma}(\log k)^{1/(2\sigma)}\right)
 \quad\Longrightarrow\quad\text{eventual repetition}.  \tag{10}
\]
In particular \(A_k=O(k^{1/\sigma})\) forces repetition, as does
\(A_k=O(k^{1/\sigma}(\log k)^q)\) for every \(q<1/(2\sigma)\).
An upper bound at the exact scale in (9), with a sufficiently large constant,
is not excluded by this argument.

There is also a weighted endpoint summability statement. Dyadic shells give
\[
 \sum_{x\in\mathcal O}\frac{x^{-\sigma}}{(1+\log x)^q}<\infty
 \qquad(q>1/2),                                       \tag{11}
\]
because their contributions are bounded by
\(C(1+r\log2)^{-q-1/2}\).
This does not establish unweighted summability at exponent \(\sigma\).

For a primitive cycle with \(N\) distinct shortcut states and integer span
\(L=\max S-\min S+1\), we similarly have \(L\ge N\), giving
\[
 \boxed{L\ge32768^{-1/\sigma}
 N^{1/\sigma}(1+\log N)^{1/(2\sigma)}.}                 \tag{12}
\]
This is a lower bound on the spread, not an upper bound excluding all cycles.

## 5. What the argument still cannot exclude

Exponential cumulative growth remains compatible with (9). Cycles can
have sufficiently large spread to satisfy (12). The counting argument
therefore still supplies necessary restrictions, not a complete contradiction.

Nor does the present induction automatically yield further logarithmic
savings. To see the limitation, try a denominator \((\log L)^\beta\) with
\(\beta>1/2\). Write \(z=\alpha/(1-\alpha)>1\). Near
\[
 j=\alpha\ell+d\log\ell+O(1),\qquad
 d=\frac{\beta-1/2}{\sigma\log3+\log z}>0,
\]
the candidate image bound and binomial bound have the same logarithmic
exponent
\[
 \beta'=
 \frac{\beta\log z+\frac12\sigma\log3}{\log z+\sigma\log3}
 <\beta.
\]
Thus even granting the trial image bound at this scale, the resulting
upper estimate is too large to close that stronger induction.
This diagnoses a limitation of these estimates; it does not prove that a
stronger theorem about actual Collatz orbits is false.

The finite image-transfer sources remain those already checked in
[the earlier verification record](../results/packing-bootstrap/verification.json).
The current [verification record](../results/mask-decoder/verification.json)
also records the reviewed written argument and its precise formal scope.
