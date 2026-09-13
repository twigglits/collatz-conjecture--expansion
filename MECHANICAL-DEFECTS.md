# Integrality after one defect in a mechanical cycle word

A single adjacent parity swap in a repeated mechanical word cannot produce
an integer cycle. For primitive mechanical words, the full ordered numerator
can be replaced by an exact three-term divisibility test. The test also
restricts where an integral defect could occur. These local tests alone do
not exclude every primitive length. The subsequent
[complexity and logarithm argument](docs/MECHANICAL-SWAP-EXCLUSION.md)
excludes the entire one-swap family, using written proofs and explicitly
identified Lean arithmetic certificates.

The two families considered here are the `22 → 13` halving modification in
[`CYCLE-EXTREMA.md`](CYCLE-EXTREMA.md) and the `121 → 112` modification in
[`GENERAL-CYCLE-DEFECTS.md`](GENERAL-CYCLE-DEFECTS.md). The arithmetic below is
proved in this note; the explicitly identified repeated-block ingredient is
also covered by a local Lean theorem. No novelty claim is made.

## 1. Both modifications move one parity bit

Use the shortcut map

\[
 U_0(x)=x/2,\qquad U_1(x)=(3x+1)/2.
\]

For a binary word \(w=(w_0,\ldots,w_{N-1})\) containing \(p\) ones, write

\[
 \Phi(w)=\sum_{i=0}^{N-1}w_i2^i3^{\sum_{r=i+1}^{N-1}w_r},
 \qquad D=2^N-3^p>0.
 \tag{1}
\]

Its return value is \(\Phi(w)/D\), and its cyclic rotations give all
shortcut states of the rational cycle. Since \(\gcd(D,6)=1\), the cycle
is integral if and only if \(D\mid\Phi(w)\) at one rotation. These
affine numerator and rational-cycle facts agree with Lemmas 1–2 of
[Halbeisen–Hungerbühler, *Optimal bounds for the length of rational Collatz
cycles*, §2](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf).
No numerical verification bound from that paper is used.

A halving exponent \(h\) encodes the shortcut block \(10^{h-1}\).
Changing adjacent exponents \((a,b)\) to \((a-1,b+1)\), with \(a\ge2\),
moves the second block's initial one one place earlier. Thus both target
modifications are exactly one cyclic parity swap \(01\to10\).

If this pair occupies positions \(j,j+1\) without crossing the chosen cut,
and \(r\) ones occur strictly after it, direct cancellation in (1) gives

\[
 \Phi(w')=\Phi(w)-2^j3^r.
 \tag{2}
\]

The exponent-word construction has \(N=H\) and \(p=k\).

## 2. Complete exclusion when the original counts are not coprime

More generally, let an original parity word be \(v^g\), where \(g>1\),
the block \(v\) has length \(q>0\), and it contains \(r>0\) ones.
Set

\[
 F=\sum_{i=0}^{g-1}2^{q(g-1-i)}3^{ri}.
\]

Composition gives

\[
 \Phi(v^g)=F\Phi(v),\qquad
 2^{qg}-3^{rg}=F(2^q-3^r).
 \tag{3}
\]

Here \(F>1\), \(F\) is odd, and \(3\nmid F\): reduce the displayed
sum modulo two and modulo three. Choose a cyclic cut avoiding the swapped
gap. A rotation of \(v^g\) remains a power of a rotated block, so (2)–(3)
apply at that cut. Integrality of the modified word would imply

\[
 F\mid 2^j3^r,
\]

contradicting \(\gcd(F,6)=1\) and \(F>1\).

**Consequently every target defect with \(\gcd(k,H)>1\) is nonintegral.**
The underlying mechanical word repeats \(\gcd(k,H)\) copies of the
reduced mechanical word. This conclusion does not assume that the original
mechanical cycle was integral.

The halving-word version of the shared-factor argument is kernel-checked as
`repeatWord_shared_factor` and `repeated_block_transfer_exclusion` in
[`CollatzCycleSeparation.lean`](CollatzCycleSeparation.lean). Those declarations
use an explicit internal transfer and equality to a repeated word. The
cyclic-cut explanation and the application to mechanical words above remain
written bridges. The [formal separation notes](results/cycle_separation_notes.md)
also describe the stronger single-copy replacement exclusion for three or more repeats.

## 3. Primitive mechanical phases and the corrected endpoint identity

Now assume \(0<p<N\), \(\gcd(p,N)=1\), and \(D>0\). Define the
mechanical phases by

\[
 b_r(i)=\left\lfloor\frac{(i+1)p+r}{N}\right\rfloor
        -\left\lfloor\frac{ip+r}{N}\right\rfloor,
 \qquad 0\le r<N.
 \tag{4}
\]

Let \(s\in\{1,\ldots,N-1\}\) be determined by
\(sp\equiv-1\pmod N\), and put \(a=\lfloor sp/N\rfloor\). Then

\[
 (a+1)N-sp=1,
 \qquad b_{N-1}=\text{the cyclic shift of }b_0\text{ by }s.
 \tag{5}
\]

The extreme phase words are \(b_0=0u1\) and \(b_{N-1}=1u0\), with the
same interior word \(u\). To verify the common interior, at an interior
position the residues for these phases differ by one; a carry can change
only when \((i+1)p\) is divisible by \(N\), which occurs only at the
boundary. If \(L=N-2\), and the affine map of \(u\) is
\((3^{p-1}X+d)/2^L\), their respective numerators are

\[
 \Phi(b_{N-1})=3^{p-1}+2d,
 \qquad \Phi(b_0)=6d+2^{N-1}.
\]

Writing \(x=\Phi(b_{N-1})/D\) and \(y=\Phi(b_0)/D\) therefore gives

\[
 D(3x-y+1)=2^{N-1}=2^{L+1}.
 \tag{6}
\]

Choose an eligible \(01\to10\) swap at positions \(j,j+1\) of \(b_0\).
Here \(0\le j\le N-2\). The special position \(j=s-1\) swaps the last
and first bits when viewed from phase \(N-1\); its modified word is
\(0u1\), hence a rotation of the original mechanical word. It is not one
of the nonmechanical defects under study, so exclude that position below.

Put

\[
 t=(j-s)\bmod N,\qquad
 C_0=2^j3^{p-1-\lfloor jp/N\rfloor},\qquad
 C_1=2^t3^{p-1-\lceil tp/N\rceil}.
 \tag{7}
\]

Both cuts now avoid the swapped gap, and \(0\le t\le N-2\). The ceiling
in \(C_1\) is the prefix count of phase \(N-1\), including prefix zero.
The exponents of three count actual ones after the pair, so are nonnegative.
Equation (2) applies at both cuts. For the two modified rational states
\(x',y'\), in the same order as (6), it gives the exact correction

\[
 \boxed{\quad
 D(3x'-y'+1)=E_j,
 \qquad E_j=2^{N-1}+C_0-3C_1.
 \quad}
 \tag{8}
\]

The pure power of two in (6) has become a sum of three terms. Coprimality
with six alone no longer forces \(D=1\).

## 4. The three-term test is necessary and sufficient

In fact (8) loses no divisibility information:

\[
 \boxed{\quad
 \text{the modified cycle is integral}
 \iff D\mid E_j.
 \quad}
 \tag{9}
\]

First, the determinant identity (5) implies

\[
 \gcd\bigl(D,\,3^{a+1}-2^s\bigr)=1.
 \tag{10}
\]

Indeed, modulo any common positive divisor, \(2^N\equiv3^p\) and
\(2^s\equiv3^{a+1}\). Raising to powers \(a+1\) and \(p\),
respectively, equates powers of two whose exponents differ by one. Since
two is invertible modulo that divisor, the divisor must be one.

The number of ones before the shift cut \(s\) is unchanged by the
modification: the cut contains both changed positions or neither, since
\(j\ne s-1\). The cycle rotation identity consequently gives

\[
 2^s\Phi(b'_{N-1})\equiv3^a\Phi(b'_0)\pmod D.
\]

Multiplying (8) by \(2^s\) and reducing modulo \(D\) yields

\[
 2^sE_j\equiv(3^{a+1}-2^s)\Phi(b'_0)\pmod D.
\]

Both multiplicative coefficients are units by (10) and \(\gcd(D,2)=1\),
proving (9). The same calculation proves the stronger equality

\[
 \gcd(D,E_j)=\gcd(D,\Phi(b'_0)).
 \tag{11}
\]

There is no zero-numerator escape in this test. Because \(0<s<N\),
the indices \(j,t\) differ, and both are less than \(N-1\). Exactly one
of the three terms in \(E_j\) has the least power of two. Therefore

\[
 v_2(E_j)=\min(j,t),\qquad
 T_j:=E_j/2^{\min(j,t)}\text{ is a nonzero odd integer}.
 \tag{12}
\]

For a signed nonzero integer, \(v_2\) means the valuation of its absolute
value. Since \(D\) is odd, (9) is equivalently \(D\mid T_j\).

## 5. An integral defect must be near one of two phase cuts

The three-term test yields a quantitative exclusion of positions without
computing any long numerator. Put

\[
 B=3^{a+1}-2^s,\qquad
 C=2^{N-s}-3^{p-a-1}>0.
\]

The positivity of \(C\) follows from

\[
 \frac{p-a-1}{N-s}=\frac pN-\frac1{N(N-s)}
 <\frac{\log2}{\log3}.
\]

Straight substitution into (7)–(12) gives the two exact forms

\[
 T_j=
 \begin{cases}
 2^{N-1-j}-C\,3^{a-\lfloor jp/N\rfloor},&j<s-1,\\[2mm]
 2^{N-1-(j-s)}-B\,3^{p-1-\lfloor jp/N\rfloor},&j>s-1.
 \end{cases}
 \tag{13}
\]

Write \(d=\min(j,t)\), the distance of the swap from the preceding cut
in \(\{0,s\}\). Then

\[
 0<|T_j|<3\cdot2^{N-1-d}.
 \tag{14}
\]

For the first case in (13), the sharper bound
\(|T_j|<2^{N-1-j}\) holds. To see this, set
\(v=a-\lfloor jp/N\rfloor\). The phase at \(s\) has the largest
residue \(N-1\), so \(v<(s-j)p/N\). Hence
\(3^v<2^{s-j}\) and
\(0<C3^v<2^{N-j}\). Subtracting this positive quantity from
\(2^{N-1-j}\) proves the sharper bound.

In the second case, if \(B>0\), its subtracted term is less than
\(3^{p-\lceil tp/N\rceil}<2^{N-t}\), giving the same sharper bound
with \(j\) replaced by \(t\). If \(B<0\), use
\(|B|<2^s\) and
\(p-1-\lfloor jp/N\rfloor<(N-j)p/N\). The added term is then less
than \(2^{N-t}\), giving the factor three in (14). Equality \(B=0\)
is impossible since both relevant exponents are positive.

Combining (9), (12), and (14), an integral defect must satisfy

\[
 \boxed{\quad
 D<3\cdot2^{N-1-d},\qquad
 d<\log_2\left(\frac{3\cdot2^{N-1}}D\right).
 \quad}
 \tag{15}
\]

For example, on any subfamily with \(D\ge\varepsilon2^N\), where
\(0<\varepsilon<1\) is fixed, only positions with

\[
 d<\log_2\frac3{2\varepsilon}
\]

can survive. Thus at most
\(2\lceil\log_2(3/(2\varepsilon))\rceil\) positions remain for each
count pair, before filtering for the required local pattern. Every other
one-swap position is excluded at all lengths in that subfamily. This is a
necessary condition, not a claim that any surviving position is integral.

## 6. Exact remaining scope

The `22 → 13` construction is completely excluded whenever
\(\gcd(k,\lceil k\log_2 3\rceil)>1\). The `121 → 112` construction
in the earlier note uses prime \(k\) and coprime counts, so does not enter
that exclusion.

For either construction with coprime counts, convert the selected halving
modification into its physical \(01\to10\) gap and rotate to phase zero.
It cannot be the special gap \(s-1\): that gap leaves the word mechanical,
whereas the specified targets respectively introduce an exponent three or a
forbidden adjacent pair of exponent ones. Formula (9), or equivalently
(13), is then an exact sparse test for integrality.

No argument here proves that this divisibility fails for all primitive
\((k,H)\) and all remaining gap positions. The ratio
\((2^H-3^k)/2^H\) can approach zero in the critical count family; no fixed
positive lower bound on it has been assumed. Even when that ratio is bounded
below and (15) leaves only finitely many positions per length, the lengths
and the corresponding exponential divisibility equations remain unbounded.

The local result therefore removes the repeated-count family and most positions
whenever the normalized denominator is bounded below, while giving an exact
three-term description of what remains. It does not establish cycle
uniqueness or solve the Collatz conjecture. The remaining primitive cases
of this particular family are now excluded by
[MECHANICAL-SWAP-EXCLUSION.md](docs/MECHANICAL-SWAP-EXCLUSION.md); arbitrary
cycle words remain outside that family theorem.
