# A recursive packing bound for arbitrary orbit patterns

The interval-counting argument can be applied again to the images of the
states being counted. Strong induction then gives the explicit bound
\[
 \boxed{\#(S\cap[a,a+L))\le128L^\sigma,\qquad
 \sigma=H_2(\log_3 2),} \tag{1}
\]
for integer \(a\ge0,L\ge1\), whenever \(S\) is forward invariant under the
Collatz shortcut map and that map is injective on \(S\).
This includes the value set of any nonrepeating orbit and every cycle.
No restriction on parity-word complexity is assumed.

Here \(H_2\) is binary entropy with logarithms to base two. For orientation,
\(\sigma\approx0.9499555272\) and \(1/\sigma\approx1.0526808586\).
The proof uses the exact entropy expression. It strengthens the exponent
\(\theta\approx0.96538\) in [ORBIT-ESCAPE.md](../ORBIT-ESCAPE.md), with a
larger explicit constant.

A [subsequent refinement](ORBIT-PACKING-LOG.md) retains the square-root
binomial factor and proves the additional bound
\(32768L^\sigma/\sqrt{1+\log L}\). Its stronger running-maximum consequence
excludes the endpoint \(A_k=O(k^{1/\sigma})\). That analytic proof remains written.

For a divergent orbit, (1) strengthens inverse-power summability and the
necessary growth of its running maximum. These are necessary restrictions;
they do not exclude exponential growth or prove convergence.

The finite image and packing-transfer lemmas are kernel checked in
[CollatzPacking.lean](../CollatzPacking.lean). The entropy estimate,
strong-induction assembly, and real-analysis consequences remain written
proofs. The exact supporting integer inequalities are kernel checked in
[PackingExponent.lean](../lean/PackingExponent.lean).
No mathematical novelty claim is made. The underlying collision method is
related to [García–Tal, *A note on the generalized 3n+1 problem*
(1999)](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf); the complete
specialized argument needed here is given below.

## 1. Fixed-weight images stay in a shorter interval of the same set

Write \(U(n)=n/2\) for even \(n\), and \(U(n)=(3n+1)/2\) for odd \(n\).
Suppose
\[
 U(S)\subseteq S,\qquad U|_S\text{ is injective}.
\]
Both properties extend to every fixed iterate.

For a residue \(0\le r<2^\ell\), let \(j\) be the number of odd steps
in its first \(\ell\) shortcut steps. The exact affine identity and sharp
residue bound are
\[
 U^\ell(2^\ell q+r)=3^j q+U^\ell(r),\qquad
 0\le U^\ell(r)<3^j. \tag{2}
\]
Consequently, the weight-\(j\) part of \(S\) in the aligned source block
\([2^\ell q,2^\ell(q+1))\) maps injectively into
\[
 S\cap[3^j q,3^j(q+1)). \tag{3}
\]
Any established interval bound at length \(3^j\) therefore bounds that
source group. The earlier estimate used only the number \(3^j\) of
available integers. We can instead use the sparsity of \(S\) itself.

In particular, an inductive bound \(C X^\sigma\) at image length \(X=3^j\)
gives
\[
 \#S_j\le C3^{\sigma j}. \tag{4}
\]
The theorem fixed_weight_local_packing checks this finite transfer with a
bound assumed only at that image length. It supports the induction below
without assuming (1) at the source length.

There is also the combinatorial bound
\[
 \#S_j\le\binom{\ell}{j}. \tag{5}
\]
To see this, parity words correspond bijectively to residues modulo
\(2^\ell\): after a prefix is fixed, the two lifts differing by \(2^\ell\)
have next iterates differing by the odd number \(3^j\), hence opposite next
parities. Induction establishes the bijection. Counting words of weight
\(j\) gives (5). This counting argument remains written here.

## 2. The entropy exponent and elementary constants

Set
\[
 \alpha=\frac{\log2}{\log3},\qquad
 h(t)=-t\log t-(1-t)\log(1-t),\qquad
 \sigma=\frac{h(\alpha)}{\log2},\qquad z=\frac{\alpha}{1-\alpha}.
\]
The inequalities \(3<4\) and \(8<9\) imply \(1/2<\alpha<2/3\).
Since entropy decreases strictly above \(1/2\),
\[
 1>\sigma>H_2(2/3)=\log_2 3-\frac23>\frac23>\alpha.
\]
The penultimate comparison follows from \(27>16\). Thus
\[
 1<z<2,\qquad 2<3^\sigma,\qquad \sigma<1. \tag{6}
\]
These loose bounds suffice for the constant 128.

The identity
\[
 z^{-\alpha}(1+z)=e^{h(\alpha)}=2^\sigma \tag{7}
\]
will control the high-weight binomial tail.

## 3. Strong induction proves the exact exponent

We prove (1) by strong induction on the positive integer interval length
\(L\), uniformly over every integer starting point \(a\). The case \(L=1\)
contains at most one integer.

Choose the least \(\ell\ge0\) with \(L\le2^\ell\); then \(2^\ell\le2L\).
The interval \([a,a+L)\) meets at most two aligned blocks of length
\(2^\ell\). In each block, split the parity weights at
\[
 J=\max\{0,\lfloor\alpha\ell\rfloor-3\}.
\]
If \(J>0\), each weight \(j<J\) has
\[
 3^j<3^J\le3^{-3}2^\ell\le\frac{2L}{27}<L.
\]
The image intervals in (3) therefore have strictly smaller integer length,
so the inductive hypothesis applies at every starting point \(3^j q\).

Let \(C=128\). Summing (4) over low weights and over the two source blocks
gives, when \(J>0\),
\[
\begin{aligned}
 \#\{\text{low-weight states}\}
 &\le2C\sum_{j<J}3^{\sigma j}\\
 &<\frac{2C3^{\sigma J}}{3^\sigma-1}\\
 &\le\frac{2^{\sigma+1}3^{-3\sigma}}{3^\sigma-1}\,C L^\sigma\\
 &<\frac12 C L^\sigma=64L^\sigma.
\end{aligned} \tag{8}
\]
The last step uses \(2^{\sigma+1}<4\), \(3^{-3\sigma}<1/8\), and
\(3^\sigma-1>1\), all from (6). If \(J=0\), the low group is empty and
the same final bound holds.

For high weights, the binomial theorem with \(z>1\) gives
\[
 \sum_{j\ge J}\binom{\ell}{j}
 \le z^{-J}(1+z)^\ell.
\]
Since \(J\ge\alpha\ell-4\), equations (6)–(7) imply
\[
\begin{aligned}
 \#\{\text{high-weight states}\}
 &\le2z^4\,2^{\sigma\ell}\\
 &\le2^{\sigma+1}z^4L^\sigma\\
 &<64L^\sigma.
\end{aligned} \tag{9}
\]
This estimate also holds when \(J=0\).

Adding (8) and (9) proves (1). All applications of the inductive
hypothesis use strictly shorter image intervals. There is no infinite
iteration of constants and no loss in the exponent.

For a real starting point and real length \(X\ge1\), covering the integer
points by an integer interval of length \(\lceil X\rceil\le2X\) gives the
convenient extension \(256X^\sigma\).

## 4. Consequences for a divergent orbit

Let \(\mathcal O\) be the value set of a nonrepeating positive shortcut
orbit. Its time parametrization is injective, so it satisfies the hypotheses
of (1).

For every \(s>\sigma\), dyadic shells give
\[
 \boxed{\sum_{x\in\mathcal O}x^{-s}
 \le\frac{128}{1-2^{\sigma-s}}<\infty.} \tag{10}
\]
Each shell \([2^r,2^{r+1})\) has integer length \(2^r\), and every term
there is at most \(2^{-rs}\).

For the accelerated odd subsequence, use
\[
 2^{h_i}n_{i+1}=3n_i+1,\quad
 H_k=\sum_{i<k}h_i,\quad
 A_k=\frac{3^k}{2^{H_k}},\quad
 P_k=\prod_{i<k}\left(1+\frac1{3n_i}\right).
\]
The exact identity is \(n_k=n_0A_kP_k\). Equation (10) at \(s=1\)
bounds the increasing product by a finite \(P_\infty\), so
\[
 \boxed{\sum_{k\ge0}A_k^{-s}<\infty\quad(s>\sigma).} \tag{11}
\]
Every divergent positive orbit is nonrepeating and eventually leaves every
finite set; hence \(n_k\to\infty\), and \(A_k\to\infty\) still follows.

Let \(M_N=\max_{0\le k\le N}A_k\), and let \(B_N\) be the largest of the
first \(N+1\) odd states. These are distinct and lie in the integer interval
\([1,B_N+1)\), of length \(B_N\). Thus
\[
 N+1\le128B_N^\sigma
 \le128(n_0P_\infty M_N)^\sigma,
\]
giving
\[
 \boxed{M_N\ge\frac1{n_0P_\infty}
       \left(\frac{N+1}{128}\right)^{1/\sigma}.} \tag{12}
\]
This concerns a running maximum. It gives no lower bound on each individual
iterate.

Consequently an orbit satisfying \(A_k=o(k^{1/\sigma})\) must eventually
repeat. In particular, an upper bound \(A_k=O(k^\beta)\) with
\(\beta<1/\sigma\) forces repetition. If the limiting mean halving exponent
is also \(\log_2 3\), repetition is impossible, since every positive cycle
has a strictly larger mean. Such a critical-mean schedule has no positive
integer realization.

For an entirely rational threshold, the exact comparisons
\[
 3^{147}<2^{233},\qquad
 233^{4660}<2^{4427}147^{2940}86^{1720}
\]
give \(1/2<147/233<\alpha\) and \(H_2(147/233)<19/20\).
Entropy monotonicity yields \(\sigma<19/20\), so
\(1/\sigma>20/19\). In particular,
\[
 A_k=O(k^{20/19})\quad\Longrightarrow\quad\text{eventual repetition}.
\]
[PackingExponent.lean](../lean/PackingExponent.lean) checks both integer
comparisons in the kernel, without native evaluation. It does not formalize
the logarithm interpretation or the surrounding analytic argument.

## 5. Consequences for cycles of arbitrary complexity

On a finite cycle \(S\), \(U\) is a permutation, so (1) applies without
any assumption on its parity pattern. If the cycle has \(N\) distinct
shortcut states, minimum \(a\), and maximum \(b\), then
\[
 \boxed{N\le128(b-a+1)^\sigma.} \tag{13}
\]
This strengthens the exponent in the general diameter lower bound.
It does not give an upper bound on the diameter.

If the odd minimum is \(m\), the same shell argument starting at \(m\)
gives
\[
 \Lambda:=N\log2-p\log3
 =\sum_{\text{odd }x}\log\left(1+\frac1{3x}\right)
 <\frac{128}{3(1-2^{\sigma-1})}\,m^{\sigma-1}. \tag{14}
\]
Here \(p\) counts odd states, and the shells
\([2^r m,2^{r+1}m)\) have integer lengths \(2^r m\).
This improves the exponent of the earlier period-independent minimum
bound in [CYCLE-ATTEMPT.md](../CYCLE-ATTEMPT.md).
Unbounded counts can still approach the critical logarithmic slope closely
enough to satisfy this condition.

## 6. A separate restriction on the ratio of odd states

The mechanical-word exclusion also gives an elementary structural corollary:
\[
 \boxed{\text{every nontrivial positive integer cycle has }
        M_{\mathrm{odd}}>2m_{\mathrm{odd}}.} \tag{15}
\]
Here is the additional written argument.

Suppose the odd states lie in \([m,2m)\), and sort them as
\(m=x_0<\cdots<x_{k-1}<2m\). Their accelerated successors are the same
finite set. The numbers
\[
 y_i=\log_2\left(\frac{3x_i+1}{m}\right)
\]
increase strictly and span an interval of length less than one.
If \(h_i\) is the exact halving exponent at \(x_i\), then
\[
 y_i-h_i=\log_2\left(\frac{\operatorname{Syr}(x_i)}m\right)\in[0,1).
\]
Thus \(h_i=\lfloor y_i\rfloor\), and the fractional parts of the \(y_i\)
preserve cyclic order.

The successor permutation of the sorted ranks consequently has the form
\(i\mapsto i+r\bmod k\). The floor of \(y_i\) is a constant integer \(a\)
before the single possible wrap and is \(a+1\) afterward. With no wrap,
\(r=0\) and the exponent word is constant. Along the orbit starting
at rank \(i_0\), the halving exponents are therefore
\[
 h_t=a+
 \left\lfloor\frac{i_0+(t+1)r}{k}\right\rfloor
 -\left\lfloor\frac{i_0+tr}{k}\right\rfloor.
\]
This is a cyclic mechanical halving word. Its binary shortcut encoding
is a cyclic mechanical parity word of the matching slope, as shown in
[the mechanical-word setup](MECHANICAL-SWAP-EXCLUSION.md#1-words-and-rational-return-values).
The [mechanical distance exclusion](MECHANICAL-DISTANCE-EXCLUSION.md)
includes distance zero and excludes every nontrivial integer realization.
Hence \(M_{\mathrm{odd}}<2m_{\mathrm{odd}}\) is impossible. Equality is
impossible because both extrema are odd, proving (15).

This corollary is a written consequence of the mechanical exclusion; the
rank-order argument has not been formalized locally. It supplies a lower
spread bound, while excluding every cycle would require additional control.

The later [folded-order theorem](FOLDED-CYCLES.md) extends the rank analysis:
every primitive integer cycle with odd spread below eight has
\(\gcd(k,H)=1\). It derives a three-layer mechanical normal form, while
leaving the coprime-count divisibility problem open.

## 7. The remaining gap and verification scope

Exponential cumulative growth satisfies (11) and (12). Cycles with large
spread can satisfy (13) and (14). No inequality above supplies the universal
upper growth bound or the ordered divisibility obstruction needed to settle
the conjecture.

The [mechanical-mask construction](MECHANICAL-MASKS.md) also shows that
bounded prefix discrepancy and bounded rational spread alone permit large
factor catalogs and linear distance from all mechanical comparators.
Its explicit checked witness fails integer divisibility; the general
family isolates that arithmetic requirement as a modular subset sum.

The new Lean statements certify exact image intervals, transfer of finite
packing bounds, and preservation of injectivity and membership under
iteration. They cover arbitrary forward-invariant sets with the stated
injectivity hypothesis. The local transfer lemma assumes a packing bound
only at the image length. All use standard logical axioms; no native_decide
or admitted proof is used in these files.

The entropy count, strong-induction assembly, infinite sums, real powers,
limits, and odd-state rank argument remain written proofs.
[Verification logs and source hashes](../results/packing-bootstrap/verification.json)
identify the exact checked sources.
