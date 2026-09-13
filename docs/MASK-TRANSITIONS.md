# Surviving mechanical masks need many adjacent halving ones

This extends the eventual exclusions in
[MASK-CYCLE-OBSTRUCTIONS.md](MASK-CYCLE-OBSTRUCTIONS.md). Consider its full
family of independent \(21\to12\) edits of the critical mechanical halving
word, with \(k\) odd steps and \(N=\lceil k\log_2 3\rceil\) shortcut steps.
Let \(q\) count cyclic occurrences of \(11\) in the **halving word**.

**Written theorem.** If an edited word is primitive and realizes a positive
integer cycle, then
\[
 \boxed{N\ge\max(H_0,2^{2048})
 \quad\Longrightarrow\quad q>\frac{N}{24\log_2N}.}            \tag{1}
\]
The constant \(H_0\) is the same effective, not yet numerical, Wu–Wang
threshold used in the preceding note. In particular, all masks with no
cyclic halving-\(11\) are eventually excluded. More generally a sequence of
such integer cycles with \(q=o(N/\log N)\) is impossible.

The later [explicit logarithm argument](EXPLICIT-LOG-GAP.md) removes this
dependence on \(H_0\): the same transition bound holds for \(N\ge10^{4000}\).
Its extended finite cover and the published small-period input exclude the
no-halving-11 subclass at every period.

The later [empirical-diversity argument](MASK-DENSITY.md) strengthens this:
for \(N\ge\max(H_0,2^{16384})\), both the good and bad block counts exceed
\(N/8192\). It also supplies a finite entropy restriction on every mask.

This does not exclude the unrestricted family or close its finite range.
[MaskTransitionBounds.lean](../lean/MaskTransitionBounds.lean) checks the
elementary integer comparisons and the finite local repairs below. The
decomposition, catalog estimates, logarithm bound, and assembly of (1) remain
written proofs; no all-period Lean theorem is claimed.

## 1. Two types of blocks

Write \(\rho=k/N\), \(\beta=\log_2 3\), and
\[
 P=2k-N,\qquad S=2N-3k.
\]
For \(k>89\), the preceding construction gives \(3/2<N/k<8/5\).
Also \(3^7>2^{11}\) gives \(N/k>11/7\), so
\[
 2<P/S<3.
\]

For a halving word of intercept \(\tau\), its symbols are
\[
 a_i=\lfloor(i+1)N/k+\tau\rfloor-\lfloor iN/k+\tau\rfloor.
\]
The positions of its symbols 1, on a doubly infinite lift, are
\[
 u_j=\left\lfloor(j+\tau)k/P\right\rfloor.
\]
Since \(k=2P+S\), the consecutive gaps \(u_{j+1}-u_j\) are
2 plus a mechanical word of slope \(S/P\). The positions of 1s in this
gap word have spacings \(\lfloor P/S\rfloor\) or \(\lceil P/S\rceil\),
hence 2 or 3. These mark the extra single 2s between the \(21\) pairs.
Consequently the base decomposes cyclically into the blocks
\[
 A=2(21)^2,\qquad B=2(21)^3.                                \tag{2}
\]
Their binary shortcut encodings are \(10101101\) and \(10101101101\),
of lengths 8 and 11, with respectively 5 and 7 ones.
On the periodic binary lift, block starts are exactly the occurrences of
the marker \(1010\); their spacings are therefore 8 or 11.
This description works for every cyclic cut.

Use selection bit 0 for an unchanged pair \(21\), and 1 for \(12\).
Within a run of pairs, a halving-\(11\) occurs precisely at a \(0\to1\)
transition of selection bits. A single 2 separates successive runs, so there
is no additional such occurrence across the block boundaries.
Thus a mask has no halving-\(11\) exactly when each run's selection bits
have the form \(1\cdots10\cdots0\).
Blocks \(A,B\) allow respectively 3 and 4 such variants.

## 2. A uniform factor catalog

For a concatenation of \(a\) short and \(b\) long complete blocks, write its
binary length and one-count as
\[
 L=8a+11b,\qquad O=5a+7b.
\]
Solving gives \(a=7L-11O\), \(b=8O-5L\). Hence the logarithm of its
number of permitted no-\(11\) selections is
\[
 \log_2(3^a4^b)
 =\eta L+(16-11\beta)(O-\rho L),\quad
 \eta=(7-11\rho)\beta+2(8\rho-5).                            \tag{3}
\]
Mechanical balance gives \(|O-\rho L|<1\). Since
\(|16-11\beta|<2\), the count is less than \(2^{\eta L+2}\).

For \(k\ge3014\), exact comparisons
\[
 3^{147}<2^{233},\qquad
 \frac{65}{41}-\frac{233}{147}=\frac2{6027}>\frac1{3014}
\]
give \(N/k<65/41\), hence \(\rho>41/65\).
Also \(\rho<7/11\), so \(7-11\rho>0\). Substituting the upper bound
on \(\beta\) into (3) yields
\[
 0<\eta<
 \frac{161-211\rho}{147}
 <\frac{1814}{9555}<\frac{19}{100}.                          \tag{4}
\]
Positivity also follows directly from \(7-11\rho>0\) and \(8\rho-5>0\).

For a length-\(m\) edited factor in \([t,t+m)\), only moved-one centers
in \([t,t+m+1)\) can affect it. Let \(u\) be the last base block start
at or before \(t\), and \(v\) the first at or after \(t+m+1\).
Then
\[
 u\ge t-10,\qquad v\le t+m+11,\qquad L=v-u\le m+21.
\]
The base factor \([t-10,t+m+15)\), of length \(m+25\), identifies both
endpoints and all intervening blocks through the marker \(1010\).
There are at most \(m+26\) such base factors. For each, the choices on
the complete-block cover are bounded by (3)–(4). Every no-\(11\) mask
\(v_0\) consequently satisfies, for all \(m\ge1\),
\[
 \boxed{P_{v_0}(m)<64(m+26)2^{19m/100}.}                     \tag{5}
\]
Indeed \(21(19/100)+2<6\).
The argument takes place on the periodic lift, so it includes factors
crossing the cyclic seam or spanning multiple periods. Allowing different
choices in repeated copies only enlarges this upper bound.

## 3. Repair an arbitrary mask

Each short or long block has at most one \(0\to1\) transition.
Its possible bad selection strings and one-bit repairs are
\[
 01\to00,\quad
 001\to000,\quad010\to000,\quad011\to111,\quad101\to100.
\]
All other selections already have no such transition.
Repairing each bad block turns any mask \(w\) with \(q\) halving-\(11\)
occurrences into a no-\(11\) mask \(v_0\) by exactly \(q\) pair toggles.
A toggle exchanges the binary blocks \(101\) and \(110\), changing two bits.
The changed pairs are disjoint, so
\[
 d_H(w,v_0)=2q.
\]
The Lean local repair theorems check both lengths of selection run, zero
remaining transitions, the transition bound, and the exact binary Hamming
distance. The global decomposition remains the written argument above.

At most \(2qm\) cyclic factor starting positions have an \(m\)-window
containing a changed bit. All other factors occur in \(v_0\), proving
\[
 P_w(m)\le P_{v_0}(m)+2qm.                                  \tag{6}
\]
The repaired mask need not be primitive or integral.

## 4. Height, collision, and cutoff

The preceding note proves, for \(N\ge H_0\), that every rational state
in this mask family is less than \(6N^{26/5}\).
If \(w\) is primitive and integral, set
\[
 t=\log_2N,\qquad m=\left\lceil\log_2(6N^{26/5})\right\rceil.
\]
Its \(N\) distinct states must have distinct length-\(m\) parity factors,
so \(N\le P_w(m)\).
For \(t\ge8\), we have \(m<(26/5)t+4\), \(m+26<9t\), and \(m<6t\).
Equation (5) gives
\[
 P_{v_0}(m)<1152tN^{247/250}.                               \tag{7}
\]
At \(t=2048\),
\[
 2^{3t/250}>2^{24}>2304t.
\]
The ratio \(2^{3t/250}/t\) increases thereafter: its logarithmic derivative
is \((3/250)\log2-1/t>0\), using \(\log2>1/2\).
Thus (7) is less than \(N/2\) throughout this range.
Also \(N\le2k\) and \(N\ge2^{2048}\) ensure \(k\ge3014\).

Finally, (6) and \(N\le P_w(m)\) imply
\[
 q>\frac{N}{4m}>\frac{N}{24t},
\]
which proves (1). The lower bound concerns halving-\(11\) occurrences, not
binary-\(11\) occurrences or simply the total number of edits.

The small entropy gap is why the original cutoff is large. The subsequent
explicit integral bound supplies the same height estimate for
\(N\ge10^{4000}\), so all remaining steps above apply with that numerical
cutoff. Masks with more transitions still survive this necessary condition.
