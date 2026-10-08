# Almost bounded Collatz orbits in natural density

**Status: written proof, not kernel checked, not a proof of Collatz.**
It upgrades Tao's theorem from logarithmic to natural density by the
route his Remark 1.16 anticipates. Tao's published propositions are used
as external inputs, together with a finite irrationality exponent for
\(\log_23\). Unrefereed 2026 claims of a similar upgrade exist, so no
novelty is claimed. The numerical checks in
[verify_natural_density.py](../verify_natural_density.py) are sanity
checks, not proofs.

**Theorem ND.** There is an absolute constant \(c>0\) such that
\[
 \#\{N\le X:\ \operatorname{Col}_{\min}(N)>N_0\}\ \ll\ X(\log N_0)^{-c}
 \qquad(N_0\ge2,\ X\ge2).
\]

**Corollary.** If \(f(N)\to\infty\), then \(\operatorname{Col}_{\min}(N)<f(N)\)
for all \(N\) outside a set of natural density zero. Also, for each
\(\delta>0\) there is \(C_\delta\) such that \(\operatorname{Col}_{\min}(N)\le
C_\delta\) on a set of lower natural density at least \(1-\delta\).

Tao proved both statements with logarithmic density
([arXiv:1909.03562](https://arxiv.org/abs/1909.03562); Forum Math. Pi 10
(2022) e12). Section and statement numbers below refer to the July 2026
arXiv source: Proposition 1.9 (valuations), 1.11 (stabilisation),
1.14 (fine-scale mixing), 1.17 and 7.1 (Fourier decay), 7.3 (white points),
Lemma 2.2 (Chernoff), Proposition 5.2 (approximate formula), Lemma 5.3, and
Theorem 3.1.

## 0. Notation

We follow Tao. \(\operatorname{Syr}(N)\) is the odd part of \(3N+1\) and
\(\vec a^{(n)}(N)\) is the \(n\)-Syracuse valuation. Also
\(\operatorname{Aff}_{\vec a}(x)=3^n2^{-|\vec a|}x+F_n(\vec a)\), and
\(\vec{\mathbf a}\equiv\mathbf{Geom}(2)^n\), so that
\(\mathbf P(\vec{\mathbf a}=\vec a)=2^{-|\vec a|}\).
\(T_x\) and \(\operatorname{Pass}_x\) are the first passage time and
location below \(x\). Also \(\alpha=1.001\) and \(\beta=\log_23\).
Write \(e(t)=e^{2\pi it}\) and \(\chi_\xi(Y)=e(-\xi Y/3^n)\). Let \(S_k\) be
a sum of \(k\) independent \(\mathbf{Geom}(2)\) variables. Finally
\[
 X_n=\sum_{i=1}^n3^{i-1}2^{-\mathbf a_{[1,i]}}\bmod 3^n,
\]
which is \(F_n\) with its arguments reversed. Reversal preserves
\(|\vec{\mathbf a}|\). Instead of Tao's log-uniform
\(\mathbf N_y\) we use
\[
 \mathbf U_y\equiv\mathbf{Unif}\bigl(2\mathbb N+1\cap[y,2y)\bigr),\qquad
 K_y=\#(2\mathbb N+1\cap[y,2y))=y/2+O(1).
\]

## 1. Where logarithmic density entered

Tao's Section 3 deduces the theorem from Proposition 1.11 for the family
\(\mathbf N_y\), and that deduction uses nothing else about the family.
Proposition 1.11 is proved in Section 5. There, logarithmic density
enters at exactly one point: \(\mathbf P(\mathbf N_y=N')\propto1/N'\). With
\(N'=2^{|\vec a|}(M-F)/3^{n'}\), this turns preimage counts into the weights
\(2^{-|\vec a|}\) and removes the multiplier \(3^{n'}2^{-|\vec a|}\).

With \(\mathbf U_y\) every preimage has the same weight \(1/K_y\), so the
multiplier must be tracked. Two inputs are needed:

1. fine-scale mixing of \(F_n\) jointly with \(|\vec{\mathbf a}|\), which is
   the "entire random affine map" of Tao's Remark 1.16 (Section 2); and
2. equidistribution of the multiplier's dyadic phase, from a renewal
   lemma for \(S_k-k\beta\) (Section 3).

## 2. Joint fine-scale mixing

**Lemma 2.1 (tilted decay).** For \(n\ge1\), \(3\nmid\xi\) and every real \(\theta\),
\[
 \bigl|\mathbf E\,\chi_\xi(X_n)\,e(\theta|\vec{\mathbf a}|)\bigr|
 \ \le\ \mathbf E\prod_{j\le n/2}\bigl|f(3^{2j-2}2^{-\mathbf b_{[1,j]}},\mathbf b_j)\bigr|
 \ \ll_A\ n^{-A}.
\]
Here \(\mathbf b_j=\mathbf a_{2j-1}+\mathbf a_{2j}\) and \(f\) is Tao's (7.4).
The product bound is his (7.5).

*Proof.* Tao's pairing in Section 7.1 writes \(X_n\) as a sum of the terms
\(3^{2j-2}2^{-\mathbf b_{[1,j]}}(2^{\mathbf a_{2j}}+3)\), plus
\(3^{n-1}2^{-\mathbf b_{[1,\lfloor n/2\rfloor]}-\mathbf a_n}\) when \(n\) is odd.
Condition on all \(\mathbf b_j\). The phase splits as
\(e(\theta|\vec{\mathbf a}|)=e(\theta\sum_j\mathbf b_j)\,e(\theta\mathbf a_n)\),
with the last factor present only for odd \(n\). The first factor is fixed
by the conditioning. The second replaces Tao's \(g\) by
\(g_\theta(x)=\mathbf E\chi(x2^{-\mathbf a_n})e(\theta\mathbf a_n)\), and
\(|g_\theta|\le1\). The pairs \((\mathbf a_{2j-1},\mathbf a_{2j})\) stay
conditionally independent, and each still contributes the factor
\(f(\cdot,\mathbf b_j)\). Taking absolute values inside the expectation over
the \(\mathbf b_j\), exactly as in Tao's absolute-value bound before Lemma 7.2,
removes every \(\theta\)-dependent phase. Lemma 7.2 and Proposition 7.3 then
give the decay. \(\square\)

Since \(\mathbf E[\chi_\xi(X_n)1_{|\vec{\mathbf a}|=s}]=\int_0^1\mathbf E[\chi_\xi(X_n)
e(\theta(|\vec{\mathbf a}|-s))]\,d\theta\), Lemma 2.1 gives

**Corollary 2.2.** \(|\mathbf E[\chi_\xi(X_n)1_{|\vec{\mathbf a}|=s}]|\ll_An^{-A}\),
uniformly in the integer \(s\).

**Proposition 2.3 (joint fine-scale mixing).** For \(1\le m\le n\), and
uniformly in \(s\in\mathbb Z\),
\[
 \operatorname{Osc}_{m,n}\Bigl(\mathbf P\bigl(X_n=Y\wedge|\vec{\mathbf a}|=s\bigr)\Bigr)_{Y\in\mathbb Z/3^n\mathbb Z}\ \ll_A\ m^{-A}.
\]

*Proof.* Follow Tao's Section 6 with the sub-probability measure
\(\nu_s(Y)=\mathbf P(X_n=Y\wedge|\vec{\mathbf a}|=s)\) in place of the law
of \(X_n\).

*Range \(0.9n\le m\le n\).* Tao's exceptional events \(\overline E\),
\(E_k\setminus E\) contribute \(O(n^{-A-1})\) to Osc. Here \(\overline E\)
is the failure of his (6.1). These bounds use \(\mathbf P(\overline E)\),
with no conditioning. On \(E_k\wedge B_k\wedge C_{k,l}\wedge\{|\vec{\mathbf a}|=s\}\)
the second block must satisfy \(\mathbf a_{[k+2,n]}=s-l\), and the blocks
are independent. Write \(F^{\leftarrow}_r\) for \(F_r\) applied to the
coordinates of its block in reverse order, as in Tao's Section 6. Hence
\[
 \widehat{g_s}(\xi)=\mathbf E\bigl[\chi_\xi(F^{\leftarrow}_{k+1})1_{E_k\wedge B_k\wedge C_{k,l}}\bigr]\cdot
 \mathbf E\bigl[\chi_\xi(3^{k+1}2^{-l}F^{\leftarrow}_{n-k-1})\,1_{\mathbf a_{[k+2,n]}=s-l}\bigr].
\]
The first factor is Tao's, and his collision bound, which comes from the
3-adic separation corollary to Lemma 6.2, is unchanged. Write
\(\xi=3^j2^l\xi'\) as Tao does. The second factor then depends on a sub-block
of length \(n-k-j-1\gg n\). The remaining coordinates are independent, so
summing over the sub-block sum \(t\) bounds it by
\(\sup_t|\mathbf E[\chi_{\xi'}(X_{n-k-j-1})1_{\text{sum}=t}]|\). Corollary 2.2
makes this \(O_{A'}(n^{-A'})\). Plancherel finishes exactly as in Tao.

*General \(m\).* Reducing mod \(3^{n_1}\), the measure \(\nu_s\) at level
\(n\ge n_1\) becomes a mixture of level-\(n_1\) measures
\(\nu_t^{(n_1)}(Y)=\mathbf P(X_{n_1}=Y\wedge\mathbf a_{[1,n_1]}=t)\). The mixture
weights are \(\mathbf P(\mathbf a_{[n_1+1,n]}=s-t)\), which sum to at most 1.
Osc is convex, so uniform-in-\(t\) bounds pass to mixtures. Tao's
telescoping over scales with ratio at least \(0.9\) then applies verbatim. \(\square\)

## 3. A renewal lemma for the dyadic phase

**Lemma 3.1.** Let \(\psi:[0,1)\to[0,2]\) have bounded variation \(V\).
For \(\tau\ge2\) write \(t_k=k\beta+\tau\). Then
\[
 R(\tau):=\sum_{k\ge0}\mathbf P\bigl(S_k=\lceil t_k\rceil\bigr)\,\psi(\lceil t_k\rceil-t_k)
 \ =\ \frac1{2-\beta}\int_0^1\psi+O_V\bigl(\tau^{-c_1}\bigr).
\]
Here \(c_1>0\) depends only on an irrationality exponent for \(\beta\).

*Proof.* Put \(k_*=\tau/(2-\beta)\) and \(W=\{k:|k-k_*|\le k_*^{0.6}\}\).

1. *Tails.* Since \(\lceil t_k\rceil-2k=(2-\beta)(k_*-k)+O(1)\), Lemma 2.2(i)
   bounds the terms with \(k\notin W\) by \(\exp(-ck_*^{0.2})\).
2. *Local limit.* \(S_k\) is a lattice walk with mean \(2k\), variance \(2k\)
   and finite third moment. The local limit theorem with rate (Petrov,
   *Sums of Independent Random Variables*, VII §3) gives
   \(\mathbf P(S_k=s)=g_k(s)+O(k^{-1})\), with \(g_k\) the Gaussian density.
   Since \(g_k'=O(k^{-1})\), we get
   \(R=\sum_{k\in W}w_k\psi(\{-t_k\})+O(k_*^{-0.4})\), where
   \(w_k=g_k(t_k)\) and \(\lceil t\rceil-t=\{-t\}\).
3. *Mass.* Set \(\delta=2-\beta\). The continuous weight
   \(w(t)=(4\pi t)^{-1/2}\exp(-(\delta t-\tau)^2/(4t))\) is unimodal,
   has maximum \(O(\tau^{-1/2})\), and satisfies
   \[
    \int_0^\infty w(t)\,dt=\frac1\delta.
   \]
   To see the identity, expand the exponent as
   \(-\delta^2t/4+\delta\tau/2-\tau^2/(4t)\) and use the Gaussian
   integral \(\int_0^\infty t^{-1/2}e^{-at-b/t}\,dt
   =\sqrt{\pi/a}\,e^{-2\sqrt{ab}}\), for \(a,b>0\).
   The integral-test error for a unimodal function is at most twice
   its maximum. Removing the exponentially small tails outside \(W\)
   gives \(\sum_{k\in W}w_k=1/\delta+O(k_*^{-1/2})\).
4. *Equidistribution.* Koksma's inequality with the weighted Erdős–Turán
   bound gives, for every \(H\ge1\),
   \[
   \Bigl|\sum_Ww_k\psi(\{-t_k\})-\textstyle\sum_Ww_k\int_0^1\psi\Bigr|
   \ll V\Bigl(\frac1H+\sum_{h\le H}\frac1h\Bigl|\sum_Ww_ke(hk\beta)\Bigr|\Bigr).
   \]
   By Abel summation, \(|\sum_Ww_ke(hk\beta)|\ll k_*^{-1/2}\|h\beta\|^{-1}\).
   An irrationality exponent \(\mu\) for \(\beta\) gives
   \(\|h\beta\|\gg h^{-\kappa}\) with \(\kappa=\mu-1+\varepsilon\), for all
   \(h\ge1\). For instance Rhin (1987) gives \(\mu\le8.616\). The repository's
   [explicit bound](EXPLICIT-LOG-GAP.md) gives \(\mu\le5.2\) for
   \(h\ge10^{4000}\); the finitely many smaller \(h\) do not affect the
   exponent. Taking \(H=k_*^{1/(2\kappa+2)}\) leaves an error
   \(O(k_*^{-1/(2\kappa+2)})\). \(\square\)

For \(\psi(z)=2^z\) the main term is
\(1/((2-\beta)\ln2)=1/\ln(4/3)\), because \((2-\beta)\ln2=\ln(4/3)\).
This is the constant in Tao's logarithmic-density formula. Floating-point
evaluation at the four tested values
\(\tau=300.9,1000.37,3000.11,10000.5\) is within
\(4\cdot10^{-4}\) of \(1/\ln(4/3)=3.476059\ldots\). This finite check
does not supply a uniform error estimate.

We also need \(R(\tau)\ll1\) uniformly for **all real** \(\tau\), with
the same definition and \(0\le\psi\le2\). The \(k=0\) term is at most
2. For \(k\ge1\), Tao's local Chernoff bound gives
\[
 \mathbf P(S_k=\lceil k\beta+\tau\rceil)
 \ll k^{-1/2}\exp\!\left[-c\min\left\{
 \frac{(\tau-\delta k+O(1))^2}{k},\,
 |\tau-\delta k+O(1)|\right\}\right].
\]
If \(\tau\le2\), the terms for sufficiently large \(k\) have a
uniform exponentially decaying bound. If \(\tau>2\), split at
\(k_*/2\) and \(2k_*\): the middle range has a Gaussian sum of width
\(O(\sqrt{k_*})\) and height \(O(k_*^{-1/2})\), and the two outer
ranges have exponentially small sums. This proves the uniform bound;
nonnegative partial sums, including \(R_y\) below, obey it too.

## 4. Stabilisation for uniform starts

**Proposition 4.1.** Let \(x\) be large and
\(y\in[x^\alpha,x^{\alpha^2}]\). Uniformly in this interval,
\(\mathbf P(T_x(\mathbf U_y)=\infty)\ll x^{-c}\), and
\[
 \sup_{y,z\in[x^\alpha,x^{\alpha^2}]}
 d_{\rm TV}\bigl(\operatorname{Pass}_x(\mathbf U_y),
 \operatorname{Pass}_x(\mathbf U_z)\bigr)\ll\log^{-c}x .
\]

*Proof.* Use Tao's
\(n_0=\lfloor\log x/(10\log2)\rfloor\),
\(m_0=\lfloor(\alpha-1)\log x/100\rfloor\),
\(E',\mathcal A^{(n')}\), and
\[
 I_y=\Bigl[\frac{\log(y/x)}{\log\frac43}-\log^{0.8}x,\ \frac{\log(y/x)}{\log\frac43}+\log^{0.8}x\Bigr].
\]
We have \(d_{\rm TV}(\mathbf U_y\bmod2^{3n_0},\mathbf{Unif})\ll2^{3n_0}/y\ll2^{-3n_0}\),
so Proposition 1.9 gives Tao's valuation estimates. His proof of the first
claim then applies verbatim.

*Approximate formula.* The proof of Proposition 5.2 uses three things:
the valuation estimates; the deterministic consequences of
\(\vec a^{(n_0)}\in\mathcal A^{(n_0)}\); and
\(\mathbf P(T_x\in I_y)=1-O(\log^{-c}x)\). The last holds because
\(\log(\mathbf U_y/x)/\log\frac43\) lies within \(3\) of the centre of
\(I_y\), and Tao's estimate of \(T_x\) has error \(O(\log^{0.6}x)\). Hence,
for \(E\subset2\mathbb N+1\cap[1,x]\) and \(n'=n-m_0\),
\[
 \mathbf P(\operatorname{Pass}_x(\mathbf U_y)\in E)=\sum_{n\in I_y}\sum_{\vec a\in\mathcal A^{(n')}}
 \sum_{M\in E'}\mathbf P(\operatorname{Aff}_{\vec a}(\mathbf U_y)=M)+O(\log^{-c}x).
\]

*Uniform weights.* If \(M\equiv F_{n'}(\vec a)\pmod{3^{n'}}\), then
\(N'=2^{|\vec a|}(M-F_{n'}(\vec a))/3^{n'}\) is odd, and
\(\mathbf P(\operatorname{Aff}_{\vec a}(\mathbf U_y)=M)=K_y^{-1}1_{N'\in[y,2y)}\).
Replace \(1_{N'\in[y,2y)}\) by \(1_{2^{|\vec a|}M/3^{n'}\in[y,2y)}\). Distinct
pairs \((\vec a,M)\) give distinct \(N'\) for each fixed \(n\), and
\(F_{n'}/M\le x^{-0.8}\). So the symmetric difference consists of odd
integers in two layers of relative width \(O(x^{-0.8})\), and it costs
\(O(x^{-0.7})\) in total.

Group by \(s=|\vec a|\). Then \(M\) runs over
\(J_{n',s}=[3^{n'}y2^{-s},2\cdot3^{n'}y2^{-s})\), and the \(n\)-term equals
\[
 \sum_s\mathbf E\bigl[1_{|\vec{\mathbf a}|=s}1_{\mathcal A}\,c_{n,s}(F_{n'}(\vec{\mathbf a})\bmod3^{n'})\bigr],
 \quad c_{n,s}(Z)=\frac{2^s}{K_y}\#\{M\in E'\cap J_{n',s}:M\equiv Z\ (3^{n'})\}.
\]
Counting residues in \(J_{n',s}\) gives
\(c_{n,s}\le(y/K_y)(1+2^s/y)\). This is uniformly at most 3 for large
\(x\): if the counted set is empty there is nothing to prove; otherwise,
any counted \(M\) gives
\(2^s/y<2\cdot3^{n'}/M\ll x^{-0.8}\), since
\(n'\le n_0\) and \(M\ge x\exp(-\log^{0.7}x)\).
This replaces Lemma 5.3. Dropping \(1_{\mathcal A}\) costs
\(\exp(-c\log^{0.2}x)\) per \(n\).

*Mixing.* Proposition 2.3 with \(m=m_0\le n'\) replaces the joint law of
\(F_{n'}\bmod3^{n'}\) and \(|\vec{\mathbf a}|=s\) by its
\(3^{m_0}\)-smoothing. Each pair \((n,s)\) costs \(O(m_0^{-A})\). There are
\(O(\log^{1.5}x)\) pairs, because \(E'\) spans \(O(\log^{0.7}x)\) dyadic
scales. Since \(2^s/(K_y3^{n'})=(2u/M)(1+O(1/y))\) with
\(u=2^sM/(3^{n'}y)\in[1,2)\), the main term becomes
\[
 \sum_{n\in I_y}\sum_{M\in E'}\frac{2\cdot3^{m_0}u}{M}\,
 \mathbf P\bigl(F_{n'}\equiv M\ (3^{m_0})\wedge|\vec{\mathbf a}|=s_{n'}(M)\bigr),\qquad
 s_{n'}(M)=\Bigl\lceil n'\beta+\log_2\frac yM\Bigr\rceil .
\]

*Reassembly.* \(F_{n'}\bmod3^{m_0}=F_{m_0}(\vec b)\), where \(\vec b\) is the
last \(m_0\) coordinates. It is independent of the first block, which has
length \(k=n-2m_0\). Put \(\sigma=|\vec b|\) and
\(\tau'=m_0\beta+\log_2(y/M)-\sigma\). Then \(s_{n'}(M)-\sigma=\lceil k\beta+\tau'\rceil\),
and \(u=2^{\lceil k\beta+\tau'\rceil-(k\beta+\tau')}\). The main term is
\[
 \sum_{M\in E'}\frac{2\cdot3^{m_0}}M\sum_\sigma\mathbf P\bigl(F_{m_0}(\vec b)\equiv M\ (3^{m_0})\wedge|\vec b|=\sigma\bigr)\,
 R_y(M,\sigma),
\]
where \(R_y\) is the sum in Lemma 3.1, with \(\psi(z)=2^z\), restricted to
\(k\in I_y-2m_0\).

Take \(M\in E'\) and \(|\sigma-2m_0|\le\log^{0.6}x\). The \(k\)-window of
Lemma 3.1 corresponds to \(n=\log(y/x)/\log\frac43+O(\log^{0.7}x)\), which
lies inside \(I_y\). Also \(\tau'\asymp\log x\). So
\(R_y=1/\ln(4/3)+O(\log^{-c_1}x)\).
All constants here are uniform for \(y\) in the indicated interval:
\[
 \tau'=\log_2(y/x)-2m_0(2-\beta)+O(\log^{0.7}x),
\]
whose leading coefficient of \(\log x\) is bounded away from zero
already at \(y=x^\alpha\). Throughout the interval,
\(I_y\subset[2m_0,n_0]\) for sufficiently large \(x\). None of the
previous estimates requires \(y\) to be an endpoint.

The uniform bound
\[
 c'(Z):=3^{m_0}\sum_{M\in E',\,M\equiv Z\,(3^{m_0})}M^{-1}\ll1
\]
needs care because \(m_0\) grows with \(x\). Here is the summation detail
in the adaptation of Tao's Lemma 5.3. Put \(m=m_0\), fix the actual
length-\(m\) valuation word \(\vec a\) of \(M\), and set
\(A=|\vec a|\), \(a=a_m\). The first-passage constraints imply
\[
 c_0\,3^{-m}2^{A-a}x\le M\le3^{-m}2^Ax
\]
for an absolute \(c_0>0\); the additive offsets are \(O(3^m)=o(x)\).
The valuation word and \(M\equiv Z\pmod{3^m}\) constrain \(M\) to one
class modulo \(q=2^{A+1}3^m\).

For \(A\le H=\tfrac12\log_2x\), we have
\(q/(c_0 3^{-m}2^{A-a}x)\ll3^{2m}x^{-1/2}=o(1)\).
The harmonic sum in this class, multiplied by \(3^m\), is therefore
\(O(2^{-A}(a+1))\). For \(A>H\), there is also the lower bound
\(M\gg3^{-m}2^A\). Indeed, all the states \(M_0=M,\ldots,M_{m-1}\)
before passage exceed \(x\), whereas \(M_m\ge1\), so
\[
 2^A=\frac{3^mM}{M_m}\prod_{i=0}^{m-1}
 \left(1+\frac1{3M_i}\right)\le2\cdot3^mM
\]
for large \(x\). The integral test with the larger lower endpoint bounds
this word's contribution by
\(O(3^{2m}2^{-A}+2^{-A}(a+1))\).

Sum the latter terms using
\(\sum_{\vec a}2^{-A}(a+1)=\mathbf E(\mathbf a_m+1)=3\).
For the former terms, \(\mathbf E(4/3)^{S_m}=2^m\) gives
\[
 3^{2m}\mathbf P(S_m>H)
 \le18^m(3/4)^H
 \le x^{10^{-5}\log18-\frac12\log_2(4/3)}=o(1).
\]
This proves \(\sup_Zc'(Z)\ll1\) with an absolute constant. Keeping
these weights is essential: the coarser sum
\(\sum_{\vec a}2^{-A/2}=(\sqrt2+1)^m\) is not uniformly bounded.

Since \(R_y\ll1\) for all \(\tau'\) by the bound after Lemma 3.1,
the atypical \(\sigma\) contribute
\(O(\sup c'\cdot\mathbf P(||\vec b|-2m_0|>\log^{0.6}x))=O(\exp(-c\log^{0.2}x))\).
The same bound gives
\(Z=\sum_{M\in E'}3^{m_0}\mathbf P(M=\mathbf{Syrac}(\mathbb Z/3^{m_0}\mathbb Z))/M=\mathbf Ec'(\mathbf{Syrac})\ll1\),
so the \(O(\log^{-c_1}x)\) error in \(R_y\) stays \(O(\log^{-c_1}x)\) after
summation. We obtain
\[
 \mathbf P\bigl(\operatorname{Pass}_x(\mathbf U_y)\in E\bigr)=\frac2{\ln\frac43}\,Z+O(\log^{-c}x).
\]
The right side does not depend on \(y\), which proves the total-variation
bound. It has the same main term as Tao's log-uniform formula; the two
passage laws are within \(O(\log^{-c}x)\), not exactly equal. \(\square\)

## 5. Proof of Theorem ND and the corollary

Run Tao's proof of Theorem 3.1 with \(\mathbf U_y\) in place of
\(\mathbf N_y\). Its only inputs are the two estimates of Proposition 4.1,
and the inequality chain is unchanged. To make the bounds uniform in
both \(x\) and \(N_0\), first take \(N_0\) larger than a fixed absolute
constant; bounded \(N_0\) are covered by enlarging the implied constant.
If \(2x\le N_0\), every start in \(\mathbf U_x\) is already below
\(N_0\). Otherwise \(x>N_0/2\ge N_0^{1/\alpha}\) for large \(N_0\).
The first \(J\ge1\) for which \(y=x^{\alpha^{-J}}<N_0^{1/\alpha}\)
then satisfies \(y\ge N_0^{1/\alpha^2}\). In the base case,
\(\operatorname{Pass}_{y^{1/\alpha}}\le y^{1/\alpha}\le N_0\) lies in
\(E_{N_0}\) automatically, so that case needs only
\(\mathbf P(T<\infty)\). The telescoping errors have sum
\(O(\sum_{j\ge0}(\alpha^j\log y)^{-c})
=O((\log N_0)^{-c})\). The result is
\(\mathbf P(\operatorname{Syr}_{\min}(\mathbf U_x)>N_0)\ll\log^{-c}N_0\) for
every \(x\ge2\).

Cover \([1,X]\) by dyadic blocks \([2^j,2^{j+1})\), including the block
containing \(X\). Their total length is \(O(X)\), so the uniform estimate
gives the odd case, also when \(X\) is not a power of two.
Since \(\operatorname{Col}_{\min}(N)=\operatorname{Syr}_{\min}(N/2^{\nu_2(N)})\),
summing over \(\nu_2(N)=a\) with weights \(2^{-a}\) gives Theorem ND.

For the strict inequality in the corollary, let
\(\tilde f(t)=\inf_{N\ge t}f(N)\) and use the threshold
\(\tilde f(\sqrt X)/2\), which tends to infinity. Then, for large \(X\),
\[
 \#\{N\le X:\operatorname{Col}_{\min}(N)\ge f(N)\}
 \ll\sqrt X+X\log^{-c}\!\left(\frac{\tilde f(\sqrt X)}2\right)=o(X).
\]
The \(C_\delta\) statement is Theorem ND with \(N_0=\exp(\delta^{-1/c}C)\).

**Remark.** The constants are not explicit. An explicit version with
\(C_\delta\le2^{71}\) for some \(\delta<1\) would combine with Barina's
verification to give Collatz on a set of positive natural density. That
is not claimed here.

## 6. Existence of a distribution of orbit minima

The uniform interval of scales in Proposition 4.1 gives a further written
consequence. For each fixed integer \(B\ge1\), the set
\(\{N:\operatorname{Col}_{\min}(N)\le B\}\) has a natural density
\(d_B\). Moreover \(d_B\to1\) as \(B\to\infty\). This asserts
existence of the densities, rather than only the lower-density bound.

*Proof.* Set
\(h_B(y)=\mathbf P(\operatorname{Syr}_{\min}(\mathbf U_y)\le B)\)
and \(E_B=\{M\text{ odd}:\operatorname{Syr}_{\min}(M)\le B\}\).
For \(x\ge B\) and \(y\ge x^\alpha\), hitting \(E_B\) is equivalent
to finite first passage below \(x\) with passage location in \(E_B\).
Indeed, no state before that passage can be at most \(B\). Apply
Proposition 4.1 with \(x=Y^{1/\alpha}\). It gives
\[
 \sup_{Y\le Z\le Y^\alpha}|h_B(Z)-h_B(Y)|
 \ll(\log Y)^{-c},\qquad Y\ge B^\alpha,
\]
once \(Y\) exceeds an absolute threshold. The two possible infinite
passage events have total probability \(O(x^{-c})\) and are included
in this error.

For arbitrary \(Z\ge Y\), choose \(J\) with
\(Y^{\alpha^J}\le Z\le Y^{\alpha^{J+1}}\) and telescope through
\(Y,Y^\alpha,\ldots,Y^{\alpha^J},Z\). Then
\[
 |h_B(Z)-h_B(Y)|
 \ll\sum_{j=0}^J(\alpha^j\log Y)^{-c}
 \ll(\log Y)^{-c}.
\]
Consequently \(h_B(y)\) has a limit \(d_B\). Summing the odd counts
over blocks \([X/2^{j+1},X/2^j)\) shows that
\(\#\{N\le X:N\text{ odd},\operatorname{Syr}_{\min}(N)\le B\}
=d_BX/2+o(X)\): discard the blocks below a fixed large threshold,
then use uniform closeness of \(h_B\) to \(d_B\) above it.
Decomposing all integers by \(\nu_2(N)\) gives density
\(\sum_{a\ge0}d_B/2^{a+1}=d_B\); the tail after \(a=A\) is bounded
by \(2^{-A}\). Theorem ND gives \(1-d_B\ll(\log B)^{-c}\) for
\(B\ge2\), hence \(d_B\to1\). \(\square\)

Set \(d_0=0\). Thus \(p_m=d_m-d_{m-1}\) is a probability distribution
on the positive integers, and is the limiting frequency of
\(\operatorname{Col}_{\min}(N)=m\). Neither this argument nor Theorem ND
shows \(d_1>0\), \(d_1=1\), or that every orbit reaches 1. Even
\(d_1=1\) would leave open a zero-density set of counterexamples.
The proof is written and depends on Proposition 4.1; it has no separate
numerical or Lean certification, and no novelty is asserted.

## 7. Verification scope

| Component | Evidence |
|---|---|
| Lemma 2.1, Corollary 2.2, Proposition 2.3 | Written modifications of Tao §§6–7; Tao's Proposition 7.3 is an external input |
| Lemma 3.1 | Written proof; external local limit theorem, Erdős–Turán–Koksma, and an irrationality exponent for \(\log_23\) |
| Proposition 4.1, Theorem ND | Written adaptation of Tao §§3–5 |
| Existence of \(d_B\) and the distribution \((p_m)\) | Written consequence of Proposition 4.1, uniform over its entire interval of scales |
| Lemma 2.1 inequality, \(n=2,3,4,5\), 6 tilts | Floating-point evaluation, truncation \(a_i,b_j\le70\); no certified roundoff bound |
| Renewal main term | Floating-point evaluation of truncated negative binomial sums at four specified \(\tau\); no uniform numerical error bound |
| Comparison of passage laws | Monte Carlo at \(x=2^{40}\), using 108 coarsened bins; this does not estimate total variation of the full integer-valued laws |

The logarithmic sampler selects odd integers directly and uses integer
rejection sampling, giving probabilities proportional to \(1/N\) under
the ideal uniform-random model. Each trajectory has a finite fuel limit;
exhaustion is reported as unresolved and fails the check. The manifest
records the fuel, exhausted count, sampling seeds, and numerical scope.

[Verification record](../results/natural-density/verification.json).
No Lean module is added. The full Collatz conjecture remains unresolved:
a density statement says nothing about the exceptional set's members.
