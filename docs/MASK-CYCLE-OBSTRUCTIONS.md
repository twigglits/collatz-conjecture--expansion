# Arithmetic and catalog obstructions for mechanical masks

Two families with independently chosen, potentially linearly many edits cannot
produce primitive positive integer cycles of sufficiently large period:

- Independent \(22\to13\) edits of the mechanical halving word.
- Independent \(21\to12\) edits restricted to alternating eligible positions.

The original argument below combines a published effective logarithm bound
with a short parity-factor catalog. Its unspecified threshold \(H_0\) gave
only eventual exclusions. The later [explicit logarithm bound and extended
resonance cover](EXPLICIT-LOG-GAP.md) now close both families at every period,
with the documented external small-period input. The all-index integral and
complete family arguments remain written proofs. The full conjecture is unresolved.

A separate exact normal form for the unrestricted \(21\to12\) family is now
kernel checked in [MechanicalMaskArithmetic.lean](../lean/MechanicalMaskArithmetic.lean).
It reduces divisibility to a bounded list of uniquely decodable subset-sum
targets. The decoder is now kernel checked, and finite certificates reject
every mask at two specified count pairs. The unrestricted all-period
problem remains unresolved.

The later [resonance certificate](MASK-RESONANCE.md) excludes the full
critical \(21\to12\) family at every period \(2^{21}\le N\le10^{1000}\).
It combines an unrestricted factor catalog with exact rational separation,
without an unknown logarithm-theorem cutoff. Eliahou's published general
cycle bound closes the smaller range using external computational input.
The later extension raises this endpoint to \(10^{4000}\). The unrestricted
family beyond the new endpoint remains open.

The later [transition argument](MASK-TRANSITIONS.md) also excludes every
sufficiently long mask without adjacent halving ones. More generally it
forces more than \(N/(24\log_2N)\) such adjacencies in any surviving integer
primitive mask cycle, for \(N\ge\max(H_0,2^{2048})\).

## 1. A logarithm bound and the resulting height limit

Put
\[
 N=\lceil k\log_2 3\rceil,\qquad
 \rho=k/N,\qquad
 \lambda=N\log2-k\log3,\qquad
 \delta=1-3^k/2^N.
\]
Thus \(0<\lambda<\log2\). Throughout, the base halving word is
\[
 a_i=\lfloor(i+1)N/k\rfloor-\lfloor iN/k\rfloor.
\]
For \(k>89\), the estimates in [MECHANICAL-MASKS.md](MECHANICAL-MASKS.md)
give \(3/2<N/k<8/5\). The halving word uses 1 and 2, has no cyclic
\(11\), and has no cyclic \(222\). Its binary shortcut word therefore has
neither \(00\) nor \(111\).

Wu and Wang's Theorem 1 states that, for each \(\varepsilon>0\), an effective
\(H_0(\varepsilon)\) exists such that
\[
 |p+q_1\log2+q_2\log3|
 \ge H^{-4.1163051-\varepsilon},
 \qquad H=\max(|q_1|,|q_2|)\ge H_0(\varepsilon).
\]
Here \(p,q_1,q_2\) are integers. This is the stated linear-independence
theorem, not an inference from an irrationality measure for \(\log3\) alone.
See [Wu–Wang, *On the irrationality measure of log 3*, J. Number Theory
142 (2014), Theorem 1](https://doi.org/10.1016/j.jnt.2014.03.007).

Choose \(\varepsilon=0.0836949\), and write \(H_0\) for its threshold.
Taking \(p=0,q_1=N,q_2=-k\), for \(N\ge H_0\) we get
\[
 \lambda\ge N^{-21/5},\qquad
 \delta=1-e^{-\lambda}>\lambda/2\ge\tfrac12N^{-21/5}.       \tag{1}
\]
The second inequality uses \(e^\lambda>1+\lambda\) and \(\lambda<1\).
No numerical value of \(H_0\) is asserted.

Each edit in either family moves one binary 1 one place left across a 0.
The moved pairs are disjoint. At a cut outside the pairs, the change in a
binary prefix count is 0 or 1; at any cyclic cut it is between \(-1\) and 1.
Consequently every rotated edited word \(w\) has prefix one-count
\[
 J_w(i)>\rho i-2.                                        \tag{2}
\]
This bound is independent of the number of edits.

The shortcut affine numerator is
\[
 \Phi(w)=\sum_{i:w_i=1}2^i3^{k-J_w(i)-1}.
\]
By (2), every term is less than \(3\cdot2^N\). Dividing by
\(D=2^N-3^k\), every state of the rational shortcut cycle satisfies
\[
 x<3k/\delta<6N^{26/5}\qquad(N\ge H_0).                  \tag{3}
\]

Suppose now that the word is primitive and its rational cycle is integral.
There are \(N\) distinct shortcut states. Set
\[
 m=\left\lceil\log_2(6N^{26/5})\right\rceil.
\]
States with the same first \(m\) parity bits are congruent modulo \(2^m\).
All states lie below \(2^m\), so those parity words must be distinct:
\[
 \boxed{N\le P_w(m).}                                    \tag{4}
\]
The finite collision and catalog-cardinality implication is kernel checked
in [CollatzRepetition.lean](../CollatzRepetition.lean).
Primality of \(k\) is a sufficient way to ensure primitivity, since
\(\gcd(k,N)=1\); alternatively primitivity can be assumed directly.

More generally, a uniform bound
\[
 P_w(m)\le A(m+b)^d2^{\eta m},\qquad \eta<5/26,            \tag{5}
\]
with fixed \(A,b,d,\eta\), contradicts (4) for large \(N\):
its right side is \(O((\log N)^dN^{26\eta/5})=o(N)\).
Here a uniform family bound is essential. A single finite periodic word
eventually has constant factor complexity, which by itself proves nothing.

## 2. Every independent 22-to-13 mask is eventually excluded

The absence of \(222\) makes the cyclic \(22\) pairs disjoint. Any subset can
be changed independently to \(13\). In the binary encoding this is
\(1010\to1100\), moving one 1 left.

To count factors, consider a length-\(L\) window of the base binary word.
Let \(O\) be its number of ones, \(B\) its number of internal \(11\) edges,
and \(e\in\{0,1,2\}\) its number of zero endpoints. Since there is no \(00\),
\[
 B=2O-L-1+e.
\]
Since there is no \(111\), the \(11\) edges have disjoint vertices.
An eligible moved 1 has zero neighbors. The number of eligible centers
in the window is therefore at most
\[
 O-2B\le2L-3O+2<(2-3\rho)L+5,                            \tag{6}
\]
using mechanical balance \(O>\rho L-1\).

A resulting factor of length \(m\) depends only on the original factor of
length \(m+3\) and the choices at centers in a window of length \(m+1\).
There are at most \(m+4\) original mechanical factors. Equation (6) gives
\[
 P_w(m)\le(m+4)\,2^{(2-3\rho)(m+1)+5}.                  \tag{7}
\]
This count includes every mask, not a sample of masks.

For \(k\ge313\), we have \(2-3\rho<1/9\). Indeed,
\[
 3^{147}<2^{233},\qquad
 \frac1{313}<\frac8{2499}=\frac{27}{17}-\frac{233}{147}
\]
imply \(N/k<27/17\), hence \(\rho>17/27\).

Write \(t=\log_2N\). The chosen \(m\) satisfies \(m<(26/5)t+4\).
Combining (4) and (7) gives, for \(N\ge2\),
\[
 N^{19/45}<64(m+4)<896t.                                \tag{8}
\]
At \(t=40\), the left side exceeds \(2^{16}=65536\), while
\(896t=35840\). The ratio \(2^{19t/45}/t\) increases for \(t\ge40\),
as follows by differentiating and using \(\log2>1/2\).
Thus (8) is impossible for \(N\ge2^{40}\).

We have proved the written implication
\[
 \boxed{N\ge\max(H_0,2^{40})
 \ \Longrightarrow\
 \text{no primitive integer cycle in the 22-to-13 mask family}.} \tag{9}
\]

This genuinely permits an unbounded number of edits. If \(q\) pairs are
edited, the nearest half-Hamming distance is exactly \(q\): each edit creates
a disjoint \(00\) pair, every matching mechanical comparator has no \(00\),
and equal one-counts require a compensating change for every removed zero.
The original word attains distance \(q\). Thus (9) reaches families beyond
any fixed-distance exclusion, though its finite initial range remains open.

## 3. Alternating 21-to-12 edit positions are also eventually excluded

The broader family in [MECHANICAL-MASKS.md](MECHANICAL-MASKS.md) has
\(s=2k-N>N/4\) disjoint cyclic \(21\) pairs. Enumerate these in cyclic order.
Declare alternating candidates editable; if \(s\) is odd, omit the final
candidate so that no two editable candidates are adjacent in candidate order.
There are \(\lfloor s/2\rfloor\) editable positions, chosen independently.

An eligible center is the first 1 in an \(11\) edge of the base binary word.
The same window identity as above, and \(O<\rho L+1\), bound the number of
such centers in length \(L\) by \((2\rho-1)L+3\), with an endpoint allowance.
If an \(11\) edge exits the window, its last bit is 1, so \(e\le1\) and
the counted centers are at most \(B+1\le2O-L+1\). Otherwise they are at
most \(B\le2O-L+1\). This accounts for that endpoint without an extra factor.
Among consecutive candidate centers, at most half, rounded up, are editable.
For a resulting \(m\)-factor, use an expanded center window of length \(m+2\).
The number of editable centers is at most
\[
 \eta(m+2)+2,\qquad \eta=(2\rho-1)/2<1/6.                \tag{10}
\]

The underlying mechanical \((m+3)\)-factor has at most \(m+4\) possibilities.
There are two alternating phases and at most \(m+4\) positions for the
single possible break in alternation at the cyclic seam. Therefore, for
\(m<N-3\), the safe uniform bound is
\[
 P_w(m)\le2(m+4)^2\,2^{\eta(m+2)+2}.                    \tag{11}
\]
The polynomial seam factor avoids assuming that a cyclic odd-length list
admits perfect alternation.

For \(t=\log_2N\ge10\), \(m+4<6t\). Equations (4), (10), and (11) imply
\[
 N^{2/15}<576t^2.                                      \tag{12}
\]
At \(t=192\), the left side exceeds \(2^{25}\), and
\(576\cdot192^2<2^{25}\). The ratio \(2^{2t/15}/t^2\)
increases thereafter. Also \(m<N-3\) throughout this range. Hence
\[
 \boxed{N\ge\max(H_0,2^{192})
 \ \Longrightarrow\
 \text{no primitive integer cycle in the alternating 21-to-12 family}.} \tag{13}
\]

There are \(2^{\lfloor s/2\rfloor}>2^{N/8-1}\) masks in this subclass.
It still contains words at linearly growing distance from all mechanical
comparators: their ordinary Hamming balls of radius \(N/100\) together
contain fewer than \(N2^{9N/80}=o(2^{N/8-1})\) words.
For the ball estimate, use
\(32^{N/100}(33/32)^N<2^{9N/80}\), since \(33^{16}<2^{81}\).
Consequently some masks have nearest half-distance greater than \(N/200\).

The unrestricted \(21\to12\) family allows a larger catalog exponent,
approaching \(2\log_3 2-1\), which exceeds \(5/26\).
The present catalog bound does not exclude that full family.

## 4. An exact normal form for unrestricted 21-to-12 masks

Choose a common cyclic cut at a 2. Since the base word has no \(11\),
it decomposes into single 2s and disjoint \(21\) pairs.
Write \(W_0\) for its numerator, \(W_{\rm all}\) for the all-edited numerator,
and
\[
 C=\sum_i c_i=W_0-W_{\rm all},\qquad
 X=\sum_i\varepsilon_i c_i,\qquad 0\le X\le C.
\]
Here a pair midpoint \(i\), with original halving prefix sum \(S_i\), has
\[
 c_i=3^{k-1-i}2^{S_i-1}.
\]

Editing every pair moves every halving symbol 1 one position left. Thus the
all-edited word is exactly the left rotation of the base by one symbol.
The first base exponent is 2, so the rotation equation is
\[
 4W_{\rm all}=3W_0+D.
\]
Substituting \(W_{\rm all}=W_0-C\) proves
\[
 \boxed{W_0=D+4C,\qquad W_{\rm mask}=D+(4C-X).}           \tag{14}
\]
Consequently the complete divisibility condition is
\[
 \boxed{D\mid W_{\rm mask}\quad\Longleftrightarrow\quad D\mid4C-X.} \tag{15}
\]

[MechanicalMaskArithmetic.lean](../lean/MechanicalMaskArithmetic.lean)
checks the token construction, rotation identity, explicit recursive
coefficient sums, bounds \(0\le X\le C\), and (14)–(15).
These kernel theorems apply to any such token word, not just a mechanical one.
The nonnegative-denominator hypothesis is explicit wherever natural
subtraction is used as an exact difference.

The interval containing \(X\) is not shorter than one denominator here.
The earlier lower bound \(W_0/D>k/6\) gives
\[
 C/D>(k-6)/24>3\qquad(k>89).
\]
Thus merely comparing the interval width with \(D\) cannot reject all masks.

## 5. A finite target reduction, and the remaining work

If a mask is integral, its starting odd state is \(x=1+t\), where
\[
 \left\lceil\frac{3C}{D}\right\rceil
 \le t\le
 \left\lfloor\frac{4C}{D}\right\rfloor,\qquad X=4C-Dt.    \tag{16}
\]
There are at most \(\lfloor C/D\rfloor+1\) integer targets to test.
Each target has at most one representing mask:

1. Order the coefficients by increasing \(S_i-1\), their distinct two-adic
   valuations, and initialize the residual to \(4C-Dt\).
2. Read the residual's bit in position \(S_i-1\). That bit is the only possible
   value of \(\varepsilon_i\), because all later coefficients are divisible
   by \(2^{S_i}\) and \(c_i/2^{S_i-1}\) is odd.
3. Subtract \(c_i\) when the bit is 1. Reject a negative residual; after the
   last coefficient, accept only a zero residual.

If a representation exists, this procedure recovers it by induction.
Conversely, a zero final residual exhibits that representation. The argument
uses ordinary integer subset sums, not an unsupported assertion of uniqueness
modulo \(D\).

[MaskSubsetDecoder.lean](../lean/MaskSubsetDecoder.lean) now proves completeness
of a token-based implementation. At a single 2 token, the target must be four
times the remaining target. At a pair token, it must be either eight times
the remainder or \(2\cdot3^{\text{tail length}}\) plus eight times it.
The two pair residues are disjoint modulo eight. Positivity and divisibility
checks prevent truncated subtraction from accepting an invalid target.
The theorem decode_iff proves acceptance exactly when a mask with that
skeleton represents the target; excludes_sound turns a complete target scan
into nondivisibility for every such mask.

[MaskSubsetFinite.lean](../lean/MaskSubsetFinite.lean) supplies two certificates:

| Odd count \(k\) | Shortcut count \(N\) | Independent pair choices | Masks covered | Scanned \(t\) interval | Targets checked |
|---:|---:|---:|---:|---:|---:|
| 193 | 306 | 80 | \(2^{80}\) | 737–983 | 247 |
| 2966 | 4701 | 1231 | \(2^{1231}\) | 946661–1262215 | 315555 |

Each scan includes one harmless extra target from rounding the lower endpoint
down. Lean checks the exact mechanical word reconstruction, the counts, both
neighboring powers bracketing \(3^k\), coprimality, the positive denominator,
and rejection of every target. The resulting theorems quantify every token
mask with the specified skeleton. Finite replay uses native_decide; decoder
completeness and the implication to all masks are kernel proved.
These finite exclusions use no logarithm theorem or unknown \(H_0\).
They do not assert convergence of every integer in the scanned numerical
intervals, or exclude masks at other count pairs.

For a mechanical base rotation, \(W_0/D<2k/(3\lambda)\). Hence
\(C/D<k/(6\lambda)\), and after \(H_0\) the number of targets is
\(O(N^{26/5})\). This is polynomial in the period, but can still be enormous.
Neither the reduction nor the bound proves that every target fails.

The logarithm theorem, factor catalog estimates, height bounds, and eventual
exclusions remain written proofs. The subset decoder and the two finite
all-mask exclusions have the formal scope stated above.
[MaskCatalogBounds.lean](../lean/MaskCatalogBounds.lean) checks only their
elementary supporting integer comparisons. The source theorem's general
\(H_0\) is still not numerical here. The later [explicit integral
argument](EXPLICIT-LOG-GAP.md) independently supplies the needed two-logarithm
bound for \(N\ge10^{4000}\), and a checked finite cover completes the two
exclusions. It does not claim a numerical cutoff for every linear form in
the published general theorem.

The [earlier verification record](../results/mask-obstructions/verification.json)
covers the normal form and cutoff arithmetic. The
[decoder verification record](../results/mask-decoder/verification.json)
covers the generic completeness proof, both finite families, and their exact
source and build inputs.

The further no-adjacent-ones catalog, local repairs, and resulting necessary
transition count are detailed in [MASK-TRANSITIONS.md](MASK-TRANSITIONS.md).
