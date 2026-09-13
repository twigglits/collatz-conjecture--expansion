# An explicit logarithm bound and an all-period cycle-span restriction

Write \(\lambda=N\log2-k\log3\). The following bound removes a numerical
cutoff gap in the preceding mask argument.

**Written logarithm theorem.** For positive integers \(k,N\) satisfying
\[
 11k\le7N,\qquad N<2k,\qquad \lambda>0,\qquad N\ge10^{4000},
\]
one has
\[
 \boxed{\lambda>N^{-21/5}.}                               \tag{1}
\]
This is a bound for the displayed two-logarithm form in this cone of
coefficients, not a replacement for the general Wu–Wang theorem.
The integrals and the argument for all indices are written proofs.
The identified finite arithmetic is checked in
[ExplicitLogConstants.lean](../lean/ExplicitLogConstants.lean).

An [extended exact resonance cover](../lean/MaskResonanceExtended.lean)
excludes nontrivial primitive positive integer cycles in the full critical
\(21\to12\) mask family for
\(2^{21}\le N\le10^{4000}\). Combining it with (1) excludes, at every
period, the subclass with no two consecutive halving exponents equal to one.
The small-period part retains the external Eliahou input already
identified in [MASK-RESONANCE.md](MASK-RESONANCE.md#5-closing-the-smaller-range-with-an-external-published-result).
The same argument also closes both earlier independent-edit families:
all \(22\to13\) masks and alternating-position \(21\to12\) masks.
Consequently every nontrivial positive integer cycle has odd extrema
\[
 \boxed{4M\ge9m+5.}                                      \tag{2}
\]
This does not exclude wider cycles or divergent trajectories, and does
not constitute a proof of Collatz. No novelty claim is made.

## 1. Integral and normalization

We use the symmetric integral construction attributed to Salikhov in the
introduction of [Wu–Wang (2014)](https://doi.org/10.1016/j.jnt.2014.03.007).
The estimates and denominator argument below are supplied explicitly;
we do not assume an unspecified asymptotic cutoff from that paper.
Put
\[
 \begin{split}
 R_n(x)&=\frac{[(x-28)(x-30)(x-35)^2(x-40)(x-42)]^n}
                   {x^{2n+1}(70-x)^{2n+1}},\\
 P(u)&=(u-1)^2(2u-3)(3u-2)(3u-4)(4u-3),\\
 F_n(u)&=\frac{P(u)^n}{u^{2n+1}(1+u)^{2n}}.
 \end{split}
\]
The change \(u=x/(70-x)\) gives \(70R_n(x)\,dx=F_n(u)\,du\).
In particular \(x=35,40,42\) correspond to \(u=1,4/3,3/2\).
For even \(n\), let
\[
 f(y)=\frac{y^2(y^2-25)(y^2-49)}{(1225-y^2)^2},\quad
 J_n=\int_0^5\frac{f(y)^n}{1225-y^2}\,dy,\quad
 K_n=\int_5^7\frac{|f(y)|^n}{1225-y^2}\,dy .
\]
Both integrals are positive. The two normalized integrals are
\[
 I_{1,n}=70J_n,\qquad I_{2,n}=70(J_n+K_n).                 \tag{3}
\]

## 2. A common positive logarithm coefficient

The reciprocal polynomial \(P\) has integer coefficients
\[
 [72,-450,1153,-1550,1153,-450,72].
\]
Thus \(F_n(1/u)/u^2=F_n(u)\). The rational differential has residue zero
at \(u=-1\): pullback by \(u\mapsto1/u\) fixes that pole and preserves
its residue, while changing the differential into its negative.
This is the elementary invariance of the coefficient of \(dz/z\)
under an invertible local change of variable.

All partial-fraction coefficients and the polynomial part are integers:
the poles are at 0 and -1, their difference is a unit, and expansion
of \((1\pm u)^{-r}\) has integer coefficients. If \(A_n\) is the residue
at zero, rational numbers \(B_n(z)\), with \(B_n(1)=0\), satisfy
\[
 \int_1^z F_n(u)\,du=A_n\log z+B_n(z).                    \tag{4}
\]
There is no other logarithm term.

In fact
\[
 A_n=[v^{2n}]G(v)^n,\quad
 G(v)=\frac{(1+v)^2(6+13v+6v^2)(12+25v+12v^2)}{(1-v)^2}.
\]
Every coefficient of \(G\) is nonnegative, and \([v^2]G=2269\).
Taking the corresponding term in the coefficient convolution gives
\[
 A_n>0,\qquad A_{n+1}\ge2269A_n.
\]
At \(r=5/19\), coefficient positivity also gives
\[
 A_n\le[G(r)/r^2]^n,\qquad
 G(r)/r^2=\frac{73122192}{9025}<8103.
\]
Therefore
\[
 \boxed{0<A_n<8103^n,\qquad A_{n+2}\ge2269^2A_n.}         \tag{5}
\]
This uses a convergent power series at a specified rational point,
not an asymptotic estimate of its coefficients.

## 3. Denominator clearance for every index

Let \(d_{2n}=\operatorname{lcm}(1,\ldots,2n)\) and
\(Q_n=2^n d_{2n}\). We prove
\[
 \boxed{Q_nB_n(4/3),\ Q_nB_n(3/2)\in\mathbb Z.}           \tag{6}
\]

Here are the full coefficient and denominator details. Write
\[
 a_j=[u^j]\frac{P(u)^n}{(1+u)^{2n}},\quad
 b_j=[w^j]\frac{P(w-1)^n}{(w-1)^{2n+1}}.
\]
Reciprocity identifies the polynomial part with the coefficients at zero.
The zero residue at -1 gives \(b_{2n-1}=0\). An explicit primitive is
\[
 \begin{split}
 B_n(z)={}&\sum_{j=0}^{2n-1}
  \frac{a_j}{2n-j}\left(z^{2n-j}-z^{j-2n}\right)\\
 &+\sum_{j=0}^{2n-2}\frac{b_j}{j-2n+1}
  \left((z+1)^{j-2n+1}-2^{j-2n+1}\right).               \tag{7}
 \end{split}
\]
Every integration denominator in (7) divides \(d_{2n}\).

To control evaluation denominators, use the following elementary
coefficient rule. If all coefficients of \(H(p^e u)\) are divisible
by \(p^V\), then the coefficients \(c_j\) of
\(H(u)^n/(1\pm u)^r\), for any nonnegative integer \(r\), satisfy
\[
 v_p(c_j)\ge nV-ej.                                    \tag{8}
\]
Indeed substitute \(p^e u\) first. The numerator coefficients are all
divisible by \(p^{nV}\), and the reciprocal unit series has integer
coefficients. The coefficient of \(u^j\) is \(p^{ej}c_j\).
Equivalently \(p^{nV}\) divides \(p^{ej}c_j\), including when \(c_j=0\).
This proves (8) for every \(n,j\); a negative lower bound is harmless.
The same argument applies to \((u-1)^{-r}\), up to an overall sign.

The following six seed conditions are checked in Lean:

| Polynomial | \(p\) | \(e\) | \(V\) |
|---|---:|---:|---:|
| \(P(u)\) | 2 | 2 | 3 |
| \(P(u)\) | 2 | 1 | 2 |
| \(P(u)\) | 3 | 1 | 2 |
| \(P(w-1)\) | 2 | 1 | 2 |
| \(P(w-1)\) | 5 | 1 | 2 |
| \(P(w-1)\) | 7 | 1 | 2 |

They can also be read directly from the linear factors. For example,
\((3u-2)^n(3u-4)^n\) supplies the first two conditions, and
\((2u-3)^n(4u-3)^n\) supplies the third. At the other pole,
\[
 P(w-1)=(w-2)^2(2w-5)(3w-5)(3w-7)(4w-7).
\]

For \(s=2n-j\), the terms \(a_jz^s\) have no evaluation denominator:
at \(z=4/3\), (8) gives \(v_3(a_j)\ge s\); at \(z=3/2\)
it gives \(v_2(a_j)\ge s\).
For \(a_jz^{-s}\), the latter endpoint uses \(v_3(a_j)\ge s\).
The former endpoint can leave powers of two, but
\[
 v_2(a_j)-2s\ge(3n-2j)-2(2n-j)=-n.
\]
Multiplication by \(2^n\) clears them.

In the second sum of (7), put \(s=2n-1-j\).
The three evaluated arguments are \(z+1=7/3,5/2\), and the baseline 2.
Their numerator primes are respectively 7, 5, and 2.
For each, (8) gives \(v_p(b_j)\ge2n-j=s+1\), so all three
negative powers have integral coefficients after evaluation.
No other primes enter. Multiplying (7) by \(2^nd_{2n}\) proves (6).

The Python checker also reconstructs the complete partial-fraction
identity and checks (6) for \(1\le n\le16\). These are sanity checks;
the argument (7)–(8), not those sixteen examples, proves the all-index claim.

## 4. Uniform integral estimates

Put
\[
 a=\frac{159}{40000},\quad b=\frac{389}{100000},\quad
 \ell=\frac{397}{100000}.
\]
The finite cubic checks establish
\[
 \begin{array}{ll}
 0\le f(y)<a & (0\le y\le5),\\
 |f(y)|<b & (5\le y\le7),\\
 f(y)>\ell & (13/4\le y\le33/10).
 \end{array}
\]
For clarity, set \(t=y^2\). The three positive polynomials are
\[
 \begin{split}
 &159(1225-t)^2-40000t(t-25)(t-49),\\
 &389(1225-t)^2+100000t(t-25)(t-49),\\
 &100000t(t-25)(t-49)-397(1225-t)^2 .
 \end{split}
\]
Their respective interval endpoints, listed in common denominator units, are

| Denominator | Consecutive endpoints |
|---:|---|
| 64 | 0, 400, 600, 650, 675, 700, 800, 1600 |
| 2 | 50, 74, 77, 80, 86, 98 |
| 400 | 4225, 4356 |

Lean checks every Bernstein coefficient strictly positive on all thirteen
adjacent intervals, and the polynomial identities. The usual Bernstein
basis is nonnegative and sums to one on \([0,1]\), so these are bounds
on entire real intervals. The real-variable application is written.

The interval lengths and denominator bounds give, for positive even \(n\),
\[
 \frac{\ell^n}{24500}<J_n<\frac{a^n}{240},\qquad
 0<K_n<\frac{b^n}{588}.
\]
The checked inequality
\[
 6\cdot24500\cdot389^{300}<588\cdot397^{300}
\]
therefore gives \(K_n<J_n/6\) for every even \(n\ge300\).
Also \(J_{n+2}\le a^2J_n\).

## 5. Two successive even indices prevent a vanishing rational part

For the counts in (1), set \(d=2N-3k>0\) and \(e=2k-N>0\).
The assumption \(11k\le7N\) is exactly \(e\le3d\). Define
\[
 E_n=(N-k)I_{1,n}+(N-2k)I_{2,n}
     =70(dJ_n-eK_n).
\]
For even \(n\ge300\), the preceding estimates imply
\[
 0<35dJ_n<E_n<70dJ_n<Na^n,\qquad
 E_{n+2}<2a^2E_n.                                      \tag{9}
\]
The last upper bound uses \(d<2N\) and \(140/240<1\).

The logarithms in this combination satisfy
\[
 (N-k)\log(4/3)+(N-2k)\log(3/2)=N\log2-k\log3.
\]
Consequently
\[
 A_n\lambda=T_n+E_n,\quad
 T_n=-(N-k)B_n(4/3)-(N-2k)B_n(3/2),\quad Q_nT_n\in\mathbb Z.
                                                               \tag{10}
\]
Equations (5) and (9) imply
\[
 \frac{E_{n+2}}{A_{n+2}}<
 \frac{2a^2}{2269^2}\frac{E_n}{A_n}<\frac{E_n}{A_n}.
\]
Thus \(T_n\) and \(T_{n+2}\) cannot both vanish.
If \(Q_jE_j<1\), positivity of \(\lambda\) in (10) also forbids \(T_j<0\):
that would give \(T_j\le-1/Q_j\) and \(A_j\lambda<0\).
Once both error bounds are small, at least one of these two indices gives
\[
 \boxed{\lambda>\frac1{Q_jA_j}.}                         \tag{11}
\]
No unproved linear independence of a sequence of approximants is assumed.

## 6. A numerical least-common-multiple bound

Use the original [Rosser–Schoenfeld (1962)](https://doi.org/10.1215/ijm/1255631807),
Theorems 9, 13, and 18, on journal pages 71–72.
They bound \(\vartheta(x)\) by \(1.01624x\) for \(x>0\), bound
\(\psi(x)-\vartheta(x)\) by \(1.42620\sqrt{x}\), and give
\(\vartheta(x)<x\) for \(0<x\le10^8\).
These published estimates, including their finite computational inputs,
are external dependencies; they are not re-proved in the local Lean files.

They imply
\[
 \psi(x)<\frac{509}{500}x\qquad(x\ge6400).
\]
For \(6400\le x\le10^8\), use \(\sqrt{x}\ge80\) and
\(1.4262/80<0.018\).
For \(x>10^8\), use
\(1.01624+1.4262/10000<1.018\).
Both rational comparisons are kernel checked.
Since \(\log d_{2n}=\psi(2n)\), for \(n\ge3200\) this gives
\[
 Q_n< B^n,\qquad B=2e^{509/250}.
\]
Define
\[
 \tau=-\log(Ba),\qquad \sigma=\log(8103B).
\]
The exact logarithm enclosure proves
\[
 0<\tau<14/5,\qquad \sigma<12,\qquad \frac{\sigma}{\tau}<\frac{524}{125},
 \qquad \frac12<\log2<1,\qquad \log10>\frac94.             \tag{12}
\]

For reproducibility, the finite checker uses 64 series terms at 128-bit
dyadic scale for
\[
 \log2,\quad \log(8103/4096),\quad \log(625/318),\quad \log(5/4).
\]
It checks the scaled tail below one in each case, just as the earlier
resonance enclosure does. Here
\[
 \sigma=13\log2+\log(8103/4096)+509/250,\quad
 \tau=6\log2+\log(625/318)-509/250,\quad
 \log10=3\log2+\log(5/4).
\]
The sign is checked before any natural-number subtraction in the checker.
Its finite arithmetic uses native evaluation; the real-series remainder
argument is the written elementary geometric-series proof.

## 7. Choosing the index proves the explicit bound

Let \(L=\log N\) and take the least even integer \(n\) strictly greater than
\(\log(2N)/\tau\). Since \(N\ge10^{4000}\), (12) gives
\(L>9000\). Since \(5\cdot9000>14\cdot3200\), \(n>3200\). Also
\[
 n\le\log(2N)/\tau+2,\qquad
 Q_jE_j<N(Ba)^j<1/2\quad(j=n,n+2).
\]
For the index \(j\) supplied by (11), equations (5) and (12) yield
\[
 \lambda>e^{-\sigma j}>
 \exp\left(-\frac{524}{125}L-\frac{6524}{125}\right).
\]
Indeed \(j\le\log(2N)/\tau+4\), \(\log2<1\), and \(4\sigma<48\).
Finally \(L>9000>6524\), and \(21/5-524/125=1/125\), giving
\(\lambda>N^{-21/5}\). This proves (1) with a numerical cutoff.

## 8. Excluding the no-halving-11 mask family

For critical mask counts, \(3^7>2^{11}\) ensures \(11k<7N\);
also \(N<2k\) at the large periods considered here.
The existing height estimate gives every shortcut state less than
\[
 3k/\delta<6N^{26/5},\qquad
 \delta=1-e^{-\lambda}>\lambda/2.
\]
Set \(t=\log_2N\) and \(m=\lceil\log_2(6N^{26/5})\rceil\).
For \(N\ge10^{4000}\), \(t>12000\), and
\[
 m<(26/5)t+4,\qquad m+26<9t,\qquad m<6t.
\]
The no-halving-11 catalog from [MASK-TRANSITIONS.md](MASK-TRANSITIONS.md) is
\[
 P(m)<64(m+26)2^{19m/100}<1152tN^{247/250}<N/2.           \tag{13}
\]
For the final comparison, at \(t=12000\),
\(2304t<2^{121}<2^{3t/250}\).
The ratio \(2^{3t/250}/t\) increases thereafter, since its logarithmic
derivative is \(3\log2/250-1/t>0\).
The required integer comparisons and \(\log2>1/2\) are checked.

All states are below \(2^m\), so the kernel parity-collision theorem
forces the \(N\) distinct states of a primitive integer cycle to have
distinct length-\(m\) factors. This contradicts (13).
The whole no-halving-11 subclass is therefore excluded for
\(N\ge10^{4000}\), with no nonnumerical threshold.

The finite extension uses 32,768-bit logarithm sums with 16,384 terms,
the existing uniform full-mask catalog, and the existing kernel Farey
cover checker. Its endpoint is now \(10^{4000}\). The generator remains
untrusted: every accepted bracket and every interval endpoint is checked.
An independent Python replay corroborates all 7,726 accepted intervals.
It uses exact integer and Fraction arithmetic, and finds a minimum
separation-margin floor of 13 against the required threshold 1.
The original \(10^{1000}\) certificate is retained unchanged.
Combining the extension, the existing published small-period bound, and
the preceding infinite-range argument excludes the no-halving-11 subclass
at every period. The finite cover actually excludes the full mask family
through its endpoint; the infinite-range argument excludes only the subclass.

The quantitative transition bound also becomes explicit. Repairing a
mask with \(q\) halving-11 occurrences changes \(2q\) binary positions,
so its catalog is at most the no-halving-11 catalog plus \(2qm\).
Equation (13) and \(N\le P_w(m)\) give
\[
 q>\frac{N}{4m}>\frac{N}{24\log_2N}\qquad(N\ge10^{4000}). \tag{14}
\]
Since every smaller nontrivial period is already excluded in this
family, every surviving integer mask must obey (14).

The stronger [density proof](MASK-DENSITY.md) uses exactly the same
height exponent \(26/5\), so its remaining steps apply without changing
their constants. Because \(10^{4000}<2^{16384}\), it now yields the
fully numerical implication
\[
 \boxed{N\ge2^{16384}\quad\Longrightarrow\quad
 \frac{N}{8192}<q<(2N-3k)-\frac{N}{8192}.}                \tag{15}
\]
Here the local distribution checks are unchanged and the entropy and
window-counting proof remains written. Periods between \(10^{4000}\)
and \(2^{16384}\) have (14); they are not asserted to have (15).

### Two further all-period exclusions

The [earlier mask note](MASK-CYCLE-OBSTRUCTIONS.md) excluded independent
\(22\to13\) masks for \(N\ge\max(H_0,2^{40})\), and alternating-position
\(21\to12\) masks for \(N\ge\max(H_0,2^{192})\).
In both proofs the only use of \(H_0\) is the height estimate
\(x<6N^{26/5}\). Equation (1) now supplies exactly that estimate for
\(N\ge10^{4000}\). Their unbounded ranges are therefore excluded with
this explicit cutoff.

The alternating-position family is a subset of the full \(21\to12\)
family, so the extended cover already excludes its finite range.
For \(22\to13\), its separate catalog, valid for \(k\ge313\), is
\[
 P_{22}(m)\le(m+4)2^{(2-3\rho)(m+1)+5}
          <(m+4)2^{(m+1)/9+5}.
\]
Every bracket supplied by the extended certificate at a covered
denominator \(N\) has \(m\ge24\). Indeed its inequalities imply
\[
 \frac4{2^m}<L-\frac ab<
 \frac cd-\frac ab=\frac1{bd}.
\]
Since \(b,d\) are positive integers and \(N<b+d\),
\(N\le bd\). Thus \(4N<2^m\), and \(N\ge2^{21}\) forces \(m\ge24\).
The denominator-product and exponent implications are kernel proved.
The real fraction comparison uses the already stated bracket inequalities.

For these windows the kernel integer comparison
\[
 (m+1)+18<9\left\lfloor\frac{21(m+1)}{80}\right\rfloor
\]
gives
\[
 P_{22}(m)<(m+4)2^{\lfloor21(m+1)/80\rfloor+3}=B_m<N.
\]
The prefix-height bound and consequent resonance inequality are identical
for the two types of disjoint binary moves. Therefore the very same
checked brackets reject every independent \(22\to13\) mask throughout
\(2^{21}\le N\le10^{4000}\).
Here \(k\ge313\) follows from \(N\le2k\).

With the same external small-period input, neither independent-edit
family can realize a nontrivial primitive positive integer cycle at
any period. These are full family exclusions, not bounds on the number
of selected edits. The unrestricted \(21\to12\) family remains unresolved.

## 9. Transfer to arbitrary cycles

Consider a nontrivial primitive positive integer cycle. Its odd minimum
is at least 5 because 1 and 3 reach the known cycle.
If \(3M+1\ge8m\), then
\[
 12M\ge32m-4\ge27m+15,
\]
so \(4M\ge9m+5\).
Otherwise the [narrow-cycle reduction](NARROW-CYCLE-MASKS.md) puts it in
the full critical mask family. The all-period exclusion just proved
forces a cyclic halving-11 occurrence. Its two edges have the form
\[
 y=(3x+1)/2,\qquad z=(3y+1)/2=(9x+5)/4.
\]
Since \(x\ge m\) and \(z\le M\), again \(4M\ge9m+5\).
This proves (2). Repeating a primitive cycle changes neither extremum,
so the same bound applies to any nontrivial cycle presentation.

This replaces the nonnumerical threshold on the earlier \(9/4\) span
bound. It does not combine the stronger finite-range \(8/3\) bound into
an all-period \(8/3\) result. Masks with many halving-11 occurrences,
wider arbitrary cycles, and aperiodic divergence remain unresolved.

## 10. Verification boundaries

| Component | Evidence |
|---|---|
| Polynomial identities, six seed divisibilities, thirteen Bernstein intervals, integral-ratio and cutoff integer comparisons | Lean kernel |
| Four dyadic logarithm enclosures and the extended denominator cover | Explicit Lean native certificates, with kernel checker soundness |
| All-index partial fractions, denominator clearance, integral estimates, nonvanishing argument, and real logarithm bound | Written proof above |
| Rosser–Schoenfeld estimates | Published external theorem, with its original computational dependencies |
| No-halving-11 catalog, narrow-cycle sorting, and full cycle-span assembly | Written proofs using the identified Lean lemmas |
| Periods below \(2^{21}\) | Previously documented Eliahou result and its external convergence computation |

The independent script checks finite arithmetic and sixteen small-index
partial fractions; it does not prove the analytic or all-index statements.
The [verification record](../results/explicit-log-gap/verification.json)
identifies the exact files, commands, logs, and hashes.

Reproduce the finite checks with:

    lean lean/ExplicitLogConstants.lean
    mkdir -p /tmp/collatz-explicit-log
    lean -o /tmp/collatz-explicit-log/MaskResonance.olean lean/MaskResonance.lean
    LEAN_PATH=/tmp/collatz-explicit-log lean lean/MaskResonanceExtended.lean
    python3 verify_explicit_log_gap.py --cover

No complete proof or counterexample to the Collatz conjecture is established.
