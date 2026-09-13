# Bounded discrepancy can conceal many independent choices

Small prefix discrepancy does not force closeness to a mechanical word or
a uniformly small factor catalog. The construction below gives exponentially
many primitive **positive rational** cycles with prefix error at most one,
unbounded minimum, and odd-state maximum/minimum ratio below eight.
Some have distance proportional to their length from every matching
mechanical word and much larger factor complexity.

These are not integer counterexamples. Their unresolved arithmetic condition
is an explicit modular subset sum. They demonstrate a limitation of using
discrepancy, rational height, and real-variable budgets alone.

A concrete example is checked in
[MechanicalMaskWitness.lean](../lean/MechanicalMaskWitness.lean):
193 odd steps, 306 shortcut bits, nearest half-Hamming distance 35 from
every mechanical rotation, and 289 distinct length-32 cyclic factors.
Its numerator is **not divisible** by its positive cycle denominator.
The general family arguments below are written proofs; the stated concrete
checks use native_decide.

## 1. Independent edits of a mechanical halving word

Take a prime \(k>89\) and put
\[
 N=\lceil k\log_2 3\rceil,\qquad
 a_i=\left\lfloor\frac{(i+1)N}{k}\right\rfloor
     -\left\lfloor\frac{iN}{k}\right\rfloor,\quad 0\le i<k.
\]
All indices are cyclic. We have \(3/2<N/k<8/5\).
For the upper bound, \(3^{17}<2^{27}\) gives
\(\log_2 3<27/17\), and \(1/k<1/85\) gives
\(N/k<27/17+1/85=8/5\). The lower bound follows from \(8<9\).

The symbols are 1 and 2. There is no cyclic pair \(11\), since every
length-two halving sum is at least \(\lfloor2N/k\rfloor\ge3\).
Each occurrence of 1 therefore has a preceding 2. Consequently there are
\[
 s=2k-N>N/4
\]
cyclic \(21\) pairs. These pairs are disjoint.

For each pair independently, either retain \(21\) or replace it by \(12\).
There are exactly \(2^s\) resulting halving words. All retain length \(k\),
sum \(N\), and the alphabet \(\{1,2\}\). Encoding a halving exponent \(h\)
as the binary block \(10^{h-1}\) gives \(2^s\) distinct words of length
\(N\) containing \(k\) ones.

Since \(k\) is prime and \(k<N<2k\), \(\gcd(k,N)=1\). A nontrivial
repetition count would divide both counts, so every resulting binary word
is primitive.

Choose one cyclic cut outside the interiors of all candidate \(21\) pairs;
such a common cut exists because the pairs are disjoint. Let \(S_i\)
and \(S'_i\) be the original and edited cumulative halving sums.
Only pair midpoints change, each by \(-1\). Thus
\[
 S'_i-S_i\in\{0,-1\}.
\]
For any cyclic prefix, the error is a difference of two such cumulative
errors, so it belongs to \(\{-1,0,1\}\). The bound does not depend on the
number of edited pairs. Another cut can give a translated cumulative band,
as in the certified example.

## 2. The associated rational cycles remain large and narrowly spread

The common denominator is
\[
 D=2^N-3^k>0.
\]
For a halving word \(h\) with cumulative sums \(H_i\), its cycle numerator is
\[
 W(h)=\sum_{i=0}^{k-1}3^{k-1-i}2^{H_i}.
\]
The values \(W(\operatorname{rot}_j h)/D\) obey the prescribed positive
rational affine cycle equations. Their numerators and denominator are odd.
The rotation identity therefore also gives the exact halving valuations
over rationals with odd denominator, as in the
[ordered-cycle construction](../CYCLE-WORDS.md).

For the lower mechanical word, write
\[
 \mathcal M=\sum_{i=0}^{k-1}3^{k-1-i}2^{\lfloor iN/k\rfloor},
 \qquad t=2^{N/k}>3.
\]
Every mechanical rotation has numerator between \(\mathcal M\) and
\(2\mathcal M\), strictly below the upper endpoint. Also
\[
 \frac{\mathcal M}{D}>
 \frac1{2(t-3)}>\frac k6.
\]
For the first inequality, replace each floor by its real argument minus
one and sum the resulting geometric series. For the second, use
\(N<k\log_2 3+1\) and
\(2^{1/k}\le1+1/k\), the chord bound for \(2^x\) on \([0,1]\).

Each edited cyclic prefix differs by at most one, so each rotated numerator
is between one half and twice the corresponding mechanical numerator.
Hence every odd rational state lies between \(\mathcal M/(2D)\) and
\(4\mathcal M/D\), with strict extreme comparisons. Writing \(m_{\rm rat}\)
and \(M_{\rm rat}\) for the minimum and maximum of these odd states,
\[
 \boxed{m_{\rm rat}>k/12,\qquad M_{\rm rat}/m_{\rm rat}<8.}
\]
For the chosen primes all odd states exceed seven, so the real-variable
centered budgets in [GENERAL-CYCLE-DEFECTS.md](../GENERAL-CYCLE-DEFECTS.md)
apply. This does not give the integer-spacing properties used in orbit
packing.

## 3. Many masks are far from every mechanical comparator

There are at most \(N\) cyclic mechanical binary words with these counts.
For any fixed binary comparator, the number of length-\(N\) binary words
within ordinary Hamming distance \(N/50\) is at most
\[
 \sum_{j\le N/50}\binom Nj
 \le16^{N/50}(17/16)^N
 <2^{41N/200}.
\]
The middle bound is the binomial theorem with weight \(1/16\). The last
uses \((17/16)^8<2\), equivalent to \(17^8<2^{33}\).
Thus all comparator balls together contain fewer than
\[
 N\,2^{41N/200}=o(2^{N/4})
\]
words. The mask family has more than \(2^{N/4}\) members.

For all sufficiently large primes, some masks therefore lie more than
\(N/50\) ordinary Hamming positions from every comparator. Since the
counts of ones agree, their nearest half-Hamming distance exceeds \(N/100\).
Bounded cyclic prefix error is compatible with distance growing linearly
in the period.

## 4. A uniform small factor catalog also fails

Let \(P_w(m)\) count distinct cyclic factors of length \(m\). If
\(P_w(m)\le K\), choose its factor catalog from the \(2^m\) possible words.
There are at most \((K+1)2^{mK}\) choices. Specifying the consecutive
nonoverlapping length-\(m\) blocks and the final shorter suffix determines
the original word, so the number of such length-\(N\) words is at most
\[
 (K+1)2^{mK}K^{\lfloor N/m\rfloor}2^m.
\]
Take \(m=\lfloor\log_2 N\rfloor\) and \(K=\lfloor2^{m/8}\rfloor\).
The logarithm to base two of this bound is \(N/8+o(N)\).
It is exponentially smaller than the mask family.

Combining this count with Section 3, some masks simultaneously satisfy
\[
 \min_b\frac{d_{\rm H}(w,b)}2>N/100,\qquad P_w(m)>2^{m/8}.
\]
Thus no uniform \(P_w(m)=O(m)\) bound follows from the discrepancy and
height-ratio conditions alone.
Each individual finite word, repeated periodically, has entropy zero.
The positive exponential counting rate concerns the family as the length
grows.

## 5. The exact integer condition that remains

Use the cut from Section 1. If a selected pair starts at \(j\), its midpoint
is \(i=j+1\). The only affected numerator term has exponent \(S_i\)
reduced by one. Thus
\[
 W_{\rm mask}=W_{\rm base}
 -\sum_i\varepsilon_i c_i,\qquad
 c_i=3^{k-1-i}2^{S_i-1},\qquad \varepsilon_i\in\{0,1\}.
\]
The complete integer-cycle criterion is
\[
 \boxed{\sum_i\varepsilon_i c_i\equiv W_{\rm base}\pmod D.}
\]
The coefficients are units modulo \(D\), because \(D\) is coprime to 6.
Distinct subsets have distinct sums as ordinary integers: in their signed
difference, the term with the smallest two-adic valuation cannot cancel.
This does not prove distinctness modulo \(D\), nor does it exclude the
target residue.

The [mechanical distance exclusion](MECHANICAL-DISTANCE-EXCLUSION.md)
already handles masks whose resulting words have nearest distance at most
31. The family above also contains much more distant words.
Its bounded discrepancy does not resolve the displayed congruence.

The [later arithmetic and catalog analysis](MASK-CYCLE-OBSTRUCTIONS.md)
puts this congruence in the kernel-checked normal form \(D\mid4C-X\),
where \(C\) is the sum of all available edit coefficients and \(X\) the
selected sum. It also gives eventual exclusions for two restricted mask
families, including edits at alternating \(21\) positions. The unrestricted
family remains unresolved, and the eventual exclusions still have an
unverified finite range.

The [resonance analysis](MASK-RESONANCE.md) now excludes the entire critical
family for \(2^{21}\le N\le10^{1000}\), using a finite exact rational cover
and no unknown \(H_0\). With Eliahou's published general cycle bound and
its external convergence computation, a nontrivial primitive integer
realization would have to have \(N>10^{1000}\).

## 6. A concrete checked witness beyond distance 31

[MechanicalMaskWitness.lean](../lean/MechanicalMaskWitness.lean) constructs
the \(k=193,N=306\) base word and makes 43 explicit \(21\to12\) edits.
The list of selected indices is part of the Lean source. A SHAKE256 stream
was used to choose it, but the certificate trusts only the explicit list
and recomputes the resulting word.

Lean checks:

- The selected pairs, word lengths, one count, critical power bracket,
  and \(\gcd(193,306)=1\).
- Every rotation of the mechanical comparator has ordinary Hamming
  distance at least 70; rotation index 104 attains 70.
- The exact number of distinct length-32 Boolean factors is 289.
- All 194 halving-prefix differences lie in \([0,1]\), with both endpoints
  attained and total difference zero.
- \(D>0,\ W>0,\ D\nmid W\).

The nearest half-distance is therefore exactly 35. Coprimality ensures that
the mechanical rotations cover all phases; this phase classification and
the rational-cycle interpretation are written bridges, not claims of the
finite file. The nonzero remainder independently rejects this candidate as
an integer cycle.

[Logs and source hashes](../results/packing-bootstrap/verification.json)
identify the exact checked witness. Its concrete computations use
native_decide, while extraction from the finite checks is kernel proved.
The general family, counting, and modular-reduction arguments remain written.
The two elementary power comparisons used in the general estimates are
also kernel checked in the same Lean file.
