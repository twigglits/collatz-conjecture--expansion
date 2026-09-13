# Excluding one adjacent swap of a mechanical cycle word

**Restricted-family result:** exchanging one adjacent pair of unequal bits in
any finite rational mechanical parity word cannot produce a nontrivial positive
integer Collatz cycle. This covers both directions, every cyclic position,
all lengths, and all numbers of ones. The only positive integer realization
is the shortcut cycle \(1\to2\to1\), of length two.

This closes the integrality question for the \(22\to13\) family in
[CYCLE-EXTREMA.md](../CYCLE-EXTREMA.md) and the \(121\to112\) family in
[GENERAL-CYCLE-DEFECTS.md](../GENERAL-CYCLE-DEFECTS.md). Their rational cycles
still exist; they are not integer counterexamples.

The proof combines a published logarithm bound, written combinatorial and
analytic arguments, kernel-checked collision lemmas, and finite arithmetic
checked with native_decide. **The complete argument is not formalized in Lean.**
No novelty claim is made. Arbitrary cycles and divergent orbits remain unresolved.

The later [distance exclusion](MECHANICAL-DISTANCE-EXCLUSION.md) covers up to
31 moved ones at arbitrary distances. Every nontrivial primitive cycle must
differ from every same-count mechanical word in at least 64 positions.

## 1. Words and rational return values

Use \(U(x)=x/2\) for even \(x\), and \(U(x)=(3x+1)/2\) for odd \(x\).
For a binary word \(w\) of length \(N\) containing \(p\) ones, put

\[
 J_w(i)=\sum_{r<i}w_r,\quad
 \Phi(w)=\sum_{i:w_i=1}2^i3^{p-J_w(i)-1},\quad
 D=2^N-3^p,\quad \delta=D/2^N.
\]

Composition gives \(2^N U_w(x)=3^p x+\Phi(w)\). Any positive cycle
with this word therefore has \(D>0\) and \(x=\Phi(w)/D\).
Rotations give the other shortcut states. Integrality implies
\(D\mid\Phi(w)\). An unequal-bit swap requires \(0<p<N\).

The mechanical base words are

\[
 b_r(i)=\left\lfloor\frac{(i+1)p+r}{N}\right\rfloor
       -\left\lfloor\frac{ip+r}{N}\right\rfloor,\qquad 0\le r<N.
\]

Every phase is a rotation of phase zero. Indeed, for \(g=\gcd(N,p)\),
the word is constant as \(r\) varies within each group of \(g\) consecutive
integers, and rotations add \(p\) modulo \(N\), visiting every phase
multiple of \(g\). The base word has period \(N/g\).

This includes the halving-word constructions cited above. Exponents
\(h_i=\lfloor(i+1)N/p\rfloor-\lfloor iN/p\rfloor\) encode blocks
\(10^{h_i-1}\), placing their ones at \(\lfloor iN/p\rfloor\).
The binary word is the upper mechanical word
\(\lceil(j+1)p/N\rceil-\lceil jp/N\rceil=b_{N-1}(j)\).
Moving one halving from an exponent to its successor moves the latter
block's one one place earlier, exactly one \(01\to10\) swap.

Let \(w\) result from one cyclic adjacent unequal-bit swap. It is primitive:
if it repeated \(q>1\) times, then \(q\) would divide \(N,p\).
The mechanical base would also have period \(N/q\). Their difference would
repeat \(q\) times, but has exactly one entry \(+1\) and one entry \(-1\).
The number of \(+1\) entries cannot be a multiple of \(q\).
Thus an integer cycle realizing \(w\) has \(N\) distinct shortcut states.

## 2. Few parity patterns force a large diameter

Two integer starts with the same first \(m\) shortcut parity bits are
congruent modulo \(2^m\). This is kernel-checked in
[CollatzRepetition.lean](../CollatzRepetition.lean).
If a primitive cycle has diameter \(R<2^m\), all its length-\(m\) parity
factors must therefore differ. Writing \(P_w(m)\) for their number gives
\(N\le P_w(m)\).

The new theorems catalog_length_of_distinct_range and
range_lower_bound_of_short_catalog check this implication, with distinctness,
range, and catalog coverage as explicit premises.

A mechanical word has at most \(m+1\) factors of length \(m\): the floors
of its prefixes partition the phase interval into at most \(m+1\) pieces.
For \(1\le m<N\), at most \(m+1\) cyclic windows meet the adjacent edited
pair. Unaffected factors belong to the base catalog, and each affected
window adds at most one. Consequently \(P_w(m)\le2m+2\).
This also holds for \(m=0\).

For \(N\ge3\), set \(m=\lfloor(N-3)/2\rfloor\). Then \(2m+2<N\), so

\[
 R\ge2^m. \tag{1}
\]

This factor count applies to the binary shortcut word, not to arbitrary
odd-to-odd halving words.

## 3. Balanced prefixes bound every state from above

For every mechanical rotation, \(J_b(i)>ip/N-1\).
An adjacent swap changes any proper cyclic prefix count by at most one,
including a cut between the edited sites. Thus \(J_w(i)>ip/N-2\).
At a one-bit position the numerator term satisfies

\[
 2^i3^{p-J_w(i)-1}
 <3\cdot3^p\left(\frac{2}{3^{p/N}}\right)^i
 <3\cdot2^N.
\]

The last inequality uses \(D>0\), hence \(2/3^{p/N}>1\), and \(i<N\).
There are \(p\) terms, so every rational shortcut state satisfies
\(0<x<3p/\delta\).
Combining this with (1), any integer realization with \(N\ge3\) requires

\[
 \boxed{\quad
 0<\delta<3p\,2^{-\lfloor(N-3)/2\rfloor}
 <12N\,2^{-N/2}.
 \quad} \tag{2}
\]

This exponential smallness strengthens the earlier position restrictions
in [MECHANICAL-DEFECTS.md](../MECHANICAL-DEFECTS.md).

## 4. A logarithm bound makes the period effective

Apply Matveev's theorem to \(\left|3^p2^{-N}-1\right|=\delta\), with
rational numbers \(3,2\), exponents \(p,-N\), and exponent bound \(N\).
The rational-product form appears as Theorem 2.1 in
[Languasco, Luca, Moree and Togbé, *Sequences of integers generated by two
fixed primes*](https://link.springer.com/article/10.1007/s12188-025-00293-9),
a version of [Matveev's theorem](https://www.mathnet.ru/eng/im314).
Its nonzero hypothesis holds by unique prime factorization. It gives

\[
 \log\delta>
 -1.4\cdot30^5\,2^{4.5}\log2\log3\,(1+\log N)
 >-10^9(1+\log N). \tag{3}
\]

The coefficient estimate uses \(2^{4.5}<23\), \(\log2<0.7\),
\(\log3<1.1\), and
\(1.4\cdot30^5\cdot23\cdot0.7\cdot1.1=602494200<10^9\).

Equations (2)–(3) require

\[
 F(N):=\frac N2\log2-\log(12N)-10^9(1+\log N)<0.
\]

But \(F(10^{12})>10^{12}/3-39-37\cdot10^9>0\), using
\(\log2>2/3\), \(\log10<3\), and \(\log12<3\).
Also \(F'(N)=\log2/2-(10^9+1)/N>0\) for \(N\ge10^{12}\). Therefore

\[
 N<10^{12}. \tag{4}
\]

Matveev is an external mathematical input, not an added local Lean axiom.

## 5. Rational separation reduces the bound to 255

Set \(\alpha=\log2/\log3\) and define the finite rational quantities

\[
 S_q=2\sum_{j=0}^{63}\frac1{(2j+1)q^{2j+1}},\quad
 R_q=\frac2{129(q^2-1)q^{127}},\quad
 L=\frac{S_3}{S_2+R_2},\quad V=\frac{S_3+R_3}{S_2}.
\]

Integrating the finite geometric expansion of \(1/(1-z^2)\) gives, for
\(0<z<1\),

\[
 2\sum_{j=0}^{63}\frac{z^{2j+1}}{2j+1}
 <\log\frac{1+z}{1-z}
 <2\sum_{j=0}^{63}\frac{z^{2j+1}}{2j+1}
   +\frac{2z^{129}}{129(1-z^2)}.
\]

At \(z=1/3,1/2\) this implies \(L<\alpha<V\).
[MechanicalLogBracket.lean](../lean/MechanicalLogBracket.lean) checks
the exact rational comparisons in

\[
 \frac{137528045312}{217976794617}+2^{-98}
 <L<\alpha<V<
 \frac{753110839881}{1193652440098}. \tag{5}
\]

It also checks that the outer fractions \(A/B<C/E\) satisfy
\(BC-AE=1\) and \(B+E=1411629234715>10^{12}\).
The inequalities involving \(\alpha\) follow from the written analytic
remainder proof; the finite Lean file does not define logarithms.

Any fraction \(p/N\) strictly between these neighbors has \(N\ge B+E\),
even if unreduced: the integers \(u=pB-AN\) and \(v=CN-pE\) are at
least one, while \(Bv+Eu=N\).
Since \(D>0\) gives \(p/N<\alpha\), (4) forces \(p/N\le A/B\). Hence

\[
 \lambda=N\log2-p\log3=N\log3(\alpha-p/N)>2^{-98},
 \qquad
 \delta=1-e^{-\lambda}>
 \frac{\lambda}{1+\lambda}>2^{-100}. \tag{6}
\]

Here \(\log3>1\) and \(e^\lambda>1+\lambda\).
For every integer \(N\ge256\), however,

\[
 3N\,2^{-\lfloor(N-3)/2\rfloor}<2^{-100}.
\]

Check \(N=256,257\), then increase \(N\) by two: the power of two doubles
while \(N\) grows by less than a factor of two. This contradicts (2) and
(6), so \(N<256\).

## 6. The finite remainder is independently certified

[MechanicalDefectFinite.lean](../lean/MechanicalDefectFinite.lean) checks
every \(0<p<N\) with \(D>0\):

* For \(32\le N\le255\), the exact inequality
  \(3p2^N\le D\,2^{\lfloor(N-3)/2\rfloor}\) contradicts (2).
* For \(3\le N\le31\), every unequal cyclic adjacent swap of the
  phase-zero word has \(\Phi(w)\bmod D\ne0\). Both directions and the
  last/first boundary are included.

The numerator is defined by
\(\Phi(b::t)=b\,3^{\#1(t)}+2\Phi(t)\); induction gives the formula in
Section 1. The swapped word is constructed explicitly. Phase-zero coverage
suffices by Section 1, since integer cycle states give integral numerators
at every rotation.

The checker soundness is kernel proved, and scalar_or_no_integral_swap
exports the stated arithmetic disjunction with its bounds and eligibility
premises. Only the two finite computations use native_decide.
Thus \(N\ge3\) is impossible. At \(N=2\), an unequal swap requires \(p=1\);
\(D=1\) and the two rotations give \(1,2\). This proves the family result.

There is a second check of the small remainder. The rational certificate
also verifies \(147/233+1/36000<L\), \(V<53/84\), determinant one,
and \(233+84=317>255\). Farey separation gives
\(\lambda>N/36000\), and therefore

\[
 \delta>\frac{N}{N+36000},\qquad
 \max x<\frac{3p}{\delta}<2(N+36000)<72512.
\]

Here \(3p<2N\) follows from \(D>0\) and \(8<9\).
The existing [CollatzCerts.lean](../CollatzCerts.lean) theorem range_a3_c1
checks starts 1 through 100000 with sole target 1. Its alternative is an
ordinary state above \(2^{62}\). A shortcut cycle below 72512 has all
ordinary intermediates below 217537, so cannot take that alternative.
Unfolding checkFrom and orbHits therefore forces a hit of 1.
This is a written soundness application of the existing certificate; the
direct word certificate above does not depend on it.

## 7. A necessary condition for every primitive cycle

For any primitive integer cycle word of length \(N\ge2\), choose a
same-count mechanical comparator. Let \(h\) be half their Hamming distance:
\(h\) ones were removed and \(h\) inserted. This counts changed sites,
not adjacent transpositions.

Any cyclic prefix loses at most \(h\) ones, giving
\(\max x<3^h p/\delta\). At most \(2hm\) windows meet a changed site,
so \(P_w(m)\le(2h+1)m+1\).
For \(m=\lfloor(N-2)/(2h+1)\rfloor\), this catalog is shorter than the
cycle. The same collision and logarithm arguments yield

\[
 \boxed{\quad
 \delta<3^h p\,2^{-m},\qquad
 m\log2<h\log3+\log p+10^9(1+\log N).
 \quad} \tag{7}
\]

These hold for every phase, including a distance-minimizing one; the
comparator need not be primitive. Every fixed \(h\) permits only
effectively bounded cycle lengths. In particular, along any hypothetical
sequence of primitive cycles with \(N\to\infty\),

\[
 \liminf\frac{h}{\sqrt N}\ge
 \sqrt{\frac{\log2}{2\log3}}.
\]

Indeed (7) and the floor bound imply
\(N<2+(2h+1)[1+(h\log3+\log N+10^9(1+\log N))/\log2]\).
On a subsequence where \(h/\sqrt N\) stays bounded, the logarithmic terms
divided by \(N\) tend to zero, giving the result. A ratio tending to infinity
already meets the bound. The large constant limits its finite numerical
usefulness; this is not a competitive finite exclusion record.

This argument supplies no uniform bound on \(h\) for prospective cycle words.
Irregular words can satisfy (7), and none of these cycle arguments excludes aperiodic
divergence. The full conjecture remains unresolved.

## Verification scope

All three Lean files passed Lean 4.33.1 with zero warnings when this result was completed.
[Logs and source hashes](../results/mechanical-one-swap/verification.json)
identify the checked statements. Generic range lemmas use only standard
logical axioms. Finite word and rational checks use native_decide, which
additionally trusts Lean's compiler and native runtime.
The rational-bracket file was subsequently extended; its current source is
covered by the [distance-result verification](../results/mechanical-distance/verification.json).

The complete family proof is the written combination above. Matveev, the
logarithm remainder, Farey separation, word primitivity, factor counts,
and the affine interpretation are not all assembled into a local Lean theorem.
