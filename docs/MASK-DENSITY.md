# Empirical diversity and transition density in mechanical masks

This strengthens [MASK-TRANSITIONS.md](MASK-TRANSITIONS.md). Its full family
allows independent \(21\to12\) edits of the critical mechanical halving word.
Throughout assume \(k>89\), so the block decomposition below applies.
Write
\[
 N=\lceil k\log_2 3\rceil,\quad \rho=k/N,\quad
 a=7N-11k,\quad b=8k-5N,\quad S=a+b=2N-3k.
\]
The base consists cyclically of \(a\) short blocks \(A=2(21)^2\) and \(b\)
long blocks \(B=2(21)^3\). A block is called bad when its selection bits
contain \(0\to1\), equivalently one occurrence of \(11\) in the edited
halving word. Let \(q\) be the number of bad blocks. Each block has at most
one such occurrence.

**Written theorem.** Every primitive positive integer mask cycle satisfies
\[
 \boxed{\frac N{8192}<q<S-\frac N{8192}}
 \qquad\text{if }N\ge\max(H_0,2^{16384}).                    \tag{1}
\]
Thus both good and bad blocks must occur at positive linear density. Here
\(H_0\) is the prior effective Wu–Wang threshold, still not numerical.
This is a necessary condition; many masks satisfy it.

The proof also gives a finite empirical-entropy restriction, with limiting
lower bound \(5/26\), without assuming independence or randomness of an
actual itinerary. The full arguments below are written proofs.
[MaskDensityBounds.lean](../lean/MaskDensityBounds.lean) checks the small
block counts, the power comparison used in the generating-function estimate,
and supporting integer
arithmetic. It does not formalize entropy or the all-period conclusion.

## 1. How varied the block selections must be

Let \(\pi_A\) be the empirical distribution of the four selection strings on
the short blocks, and \(\pi_B\) that of the eight strings on the long blocks.
Set \(H(\pi)=-\sum p\log_2p\), with \(0\log_20=0\), and define
\[
 h_{\rm emp}=\frac aN H(\pi_A)+\frac bN H(\pi_B).             \tag{2}
\]
A missing block type contributes zero. In the present range both counts
are positive.

For \(N\ge H_0\), the preceding height bound gives all rational states
less than \(6N^{26/5}\). Put
\[
 m=\left\lceil\log_2(6N^{26/5})\right\rceil .
\]
For a primitive integer realization all \(N\) cyclic parity factors of
length \(m\) are distinct, by the congruence-and-height collision lemma.

Choose a cyclic start \(T\) uniformly from the \(N\) positions.
Let \(W_T\) be the edited length-\(m\) factor and \(E_T\) the base factor
on \([T-10,T+m+25)\), of length \(m+35\).
For each offset \(j=-10,\ldots,m+10\), let \(Y_j\) be the selection label
at the block start \(T+j\), or a fixed empty label if this is not a start.
The base factor determines whether that position is an \(A\)-start,
a \(B\)-start, or neither: markers have spacing at most 11, and checking
the next marker requires at most 14 following bits.
This explains the larger padding than in the counting-only argument.

The edited factor is determined by \(E_T\) and these labels.
There are at most \(m+36\) base factors.
For each offset, conditioning on \(E_T\) reveals its block type, so
\[
 H(Y_j\mid E_T)\le H(Y_j\mid\text{type at }T+j)=h_{\rm emp}.
\]
The equality follows from uniform cyclic translation: the empirical
distribution at every fixed offset is the same.
The entropy chain rule and the fact that conditioning cannot increase
entropy now imply
\[
 \log_2N=H(W_T)
 \le H(E_T)+\sum_{j=-10}^{m+10}H(Y_j\mid E_T)
 \le\log_2(m+36)+(m+21)h_{\rm emp}.
\]
All probability here is a way of counting positions in one fixed word.
There is no assertion that its labels are independent. We obtain
\[
 \boxed{h_{\rm emp}\ge
 \frac{\log_2N-\log_2(m+36)}{m+21}.}                         \tag{3}
\]
Consequently any sequence of these hypothetical integer cycles with
periods tending to infinity has \(\liminf h_{\rm emp}\ge5/26\).

For context, put \(\eta=(7-11\rho)\log_23+2(8\rho-5)\).
Grouping each block's choices into good and bad types gives
\[
 h_{\rm emp}\le\eta+\frac SN H_2(q/S).                      \tag{4}
\]
For short blocks this follows from
\(H(\pi_A)\le\log_23+H_2(p_A)-p_A\log_23\); for long blocks,
\(H(\pi_B)\le2+H_2(p_B)\). Weighted concavity of binary entropy,
and dropping the negative term, prove (4).
As \(\rho\to\log_32\), \(\eta<5/26\); hence (3)–(4) already explain
why neither \(q/S\to0\) nor \(q/S\to1\) is possible.
The next argument supplies explicit constants without numerical entropy
evaluation.

## 2. Many windows would contain few marked blocks

Write \(L_0=m+21\) and work on the doubly infinite periodic lift.
Let \(R_t\) count bad block starts in \([t-10,t+m+11)\), with multiplicity.
Double counting positions and offsets gives the exact identity
\[
 \sum_{t=0}^{N-1}R_t=qL_0.                                 \tag{5}
\]
It remains valid when the interval spans several periods.
If \(q\le N/8192\), the mean is at most \(L_0/8192\).
With \(R=L_0/6144\), at least \(N/4\) starts therefore have \(R_t\le R\).
Indeed, more than \(3N/4\) starts with \(R_t>R\) would contradict (5).
The full-block cover affecting the edited \(m\)-factor is a subset of
this expanded interval, so its bad count is also at most \(R\).

## 3. Count those factors by a weighted generating function

A short block has three good and one bad selection; a long block has four
of each. If a complete cover has \(a'\) short and \(b'\) long blocks, its
selection-count polynomial by number of bad blocks is
\[
 (3+z)^{a'}(4+4z)^{b'}.
\]
For \(z=1/512<1\), the number with at most \(R\) bad blocks is at most
\[
 z^{-R}(3+z)^{a'}(4+4z)^{b'}
 \le 2^{9R}3^{a'}4^{b'}(1+1/512)^{a'+b'}.                  \tag{6}
\]
This remains valid for noninteger \(R\).

From the preceding note, the cover length \(L\le L_0\), its block count
is at most \(L_0/8\), and, for \(k\ge3014\),
\[
 3^{a'}4^{b'}<2^{(19/100)L_0+2}.
\]
The kernel-checked comparison \(513^{256}<2^{2305}\) gives
\(\log_2(513/512)<1/256\). Thus the extra exponent in (6) is less than
\[
 \frac{9L_0}{6144}+\frac{L_0}{2048}=\frac{L_0}{512}.
\]
Put
\[
 \eta_*=\frac{19}{100}+\frac1{512}=\frac{2457}{12800}<\frac5{26}.
\]
At most \(m+26\) base factors identify the complete covers. Since
\(21\eta_*+2<7\), the catalog of all such low-bad-count factors has size
less than
\[
 128(m+26)2^{\eta_*m}.                                     \tag{7}
\]
Although this is only a catalog for some starting positions, those positions
number at least \(N/4\). Integrality and primitivity require their factors
to be distinct.

## 4. Explicit cutoff and the symmetric bound

Write \(t=\log_2N\). For \(t\ge8\), the previous inequalities
\(m<(26/5)t+4\), \(m+26<9t\), and \(4\eta_*<1\) bound (7) by
\[
 2304tN^{31941/32000}.                                    \tag{8}
\]
At \(t=16384\),
\[
 2^{59t/32000}>2^{30}>9216t.
\]
The ratio \(2^{59t/32000}/t\) increases thereafter, since its logarithmic
derivative is positive using \(\log2>1/2\) and \(59t>64000\).
Hence (8) is less than \(N/4\), contradicting the required distinct
factors. The lower bound in (1) follows.

To prove the upper bound, mark good blocks instead.
Their number is \(S-q\); (5) and the window argument are unchanged.
The generating polynomial becomes
\[
 (1+3z)^{a'}(4+4z)^{b'}
 \le3^{a'}4^{b'}(1+z)^{a'+b'},
\]
because \(1+3z\le3(1+z)\). Thus exactly the same catalog and cutoff
exclude \(S-q\le N/8192\). This proves (1).

The finite local distributions and integer comparisons are kernel checked.
The uniform catalog, entropy and double-counting deductions are written.
The new conclusion strengthens the earlier \(N/\log N\) condition; it still
allows a substantial interval of transition densities and does not settle
the unrestricted divisibility problem.
