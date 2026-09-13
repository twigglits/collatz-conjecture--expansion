# Sharp extrema for ordered cycle words

For fixed odd-step count and total halving count, the maximum possible cycle
minimum is attained exactly by cyclic rotations of a mechanical exponent
word. The minimum possible cycle minimum is attained exactly by concentrating
all extra halvings in one exponent. Both statements below cover every
positive halving word, including noncoprime count pairs.

These are extrema for positive **rational** Collatz cycles. Integer cycles
must additionally satisfy an ordered divisibility condition. The extrema
give exact finite exclusions for specified counts and height thresholds;
they do not exclude all integer cycles. No novelty is claimed.

## 1. Setup and the two sharp bounds

Let \(k\ge1\), \(H\ge k\), and
\(D=2^H-3^k>0\). Consider all words
\(h=(h_0,\ldots,h_{k-1})\) of positive integers summing to \(H\).
For each cyclic rotation \(a\), put

\[
 S_a(i)=\sum_{j=0}^{i-1}h_{(a+j)\bmod k},\qquad
 W_a=\sum_{i=0}^{k-1}3^{k-1-i}2^{S_a(i)},\qquad
 m(h)=\frac{\min_a W_a}{D}.
\]

Define

\[
 M(k,H)=\sum_{i=0}^{k-1}3^{k-1-i}2^{\lfloor iH/k\rfloor},
 \qquad
 b_i=\lfloor(i+1)H/k\rfloor-\lfloor iH/k\rfloor.             \tag{1}
\]

**Theorem 1.** For every such word,

\[
 \boxed{\quad
 \frac{3^k-2^k}{D}\ \le\ m(h)\ \le\ \frac{M(k,H)}{D}.
 \quad}                                                     \tag{2}
\]

Upper equality holds if and only if \(h\) is a cyclic rotation of \(b\).
Lower equality holds if and only if \(h\) is a cyclic rotation of
\((1,\ldots,1,H-k+1)\). For \(k=1\), both descriptions give the unique
word \((H)\), and both bounds equal \(1/(2^H-3)\).

These formulas correspond to the sharp maximum-of-minima construction in
Halbeisen–Hungerbühler, expressed here using odd-to-odd halving exponents.
Their shortcut-word notation uses length \(H\), weight \(k\), and ones
at the positions \(\lfloor iH/k\rfloor\). See Section 3, Lemma 5 and
Corollary 1 of [*Optimal bounds for the length of rational Collatz cycles*,
Acta Arithmetica 78 (1997), 227–239](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf).
No historical numerical verification bound from that paper is assumed here.

## 2. An independent prefix-sum proof

Extend the original prefix sum \(S\) periodically by
\(S(t+k)=S(t)+H\), and set \(d(t)=S(t)-tH/k\). Then \(d\) is
\(k\)-periodic. Choose \(a\in\{0,\ldots,k-1\}\) maximizing \(d(a)\).
For every \(i\ge0\),

\[
 S(a+i)-S(a)-iH/k=d(a+i)-d(a)\le0.
\]

Since the prefix sums are integers,
\(S_a(i)\le\lfloor iH/k\rfloor\). Every coefficient in \(W_a\) is
positive, so \(\min_rW_r\le W_a\le M(k,H)\).

For the word \(b\), every rotation instead satisfies

\[
 S_a(i)=\lfloor(a+i)H/k\rfloor-\lfloor aH/k\rfloor
       =\lfloor iH/k+\{aH/k\}\rfloor
       \ge\lfloor iH/k\rfloor.
\]

Thus all its numerators are at least \(M\), and its unrotated numerator
equals \(M\). If an arbitrary word attains upper equality, the maximizing
rotation above must have \(W_a=M\). No term can then be smaller, so all
prefix sums through \(k-1\) equal \(\lfloor iH/k\rfloor\).
The fixed total \(H\) determines the last exponent, giving exactly \(b\).

For the lower bound, every rotation has \(S_a(i)\ge i\), whence

\[
 W_a\ge\sum_{i=0}^{k-1}3^{k-1-i}2^i=3^k-2^k.
\]

Equality requires \(S_a(i)=i\) for every \(i<k\), so the first
\(k-1\) exponents are 1 and the last is \(H-k+1\). This also proves
attainment and the equality classification.

No coprimality was used. If \(g=\gcd(k,H)>1\), the mechanical word
repeats a word of length \(k/g\). It remains the extremizer, but the
corresponding rational cycle need not have primitive period \(k\).

The generic rotation step and its integer floor bound are kernel-checked in
[`CollatzCycleExtrema.lean`](CollatzCycleExtrema.lean), declarations
`bounded_rotation` and `floor_bounded_rotation`. They concern periodic
prefix sums, not Collatz directly. The weighted-numerator comparison,
equality classification, and applications here remain written proofs.

## 3. Why these numerators are genuine rational cycles

Every \(W_a\) and \(D\) is odd, and direct expansion gives

\[
 2^{h_a}W_{a+1}=3W_a+D.                                     \tag{3}
\]

Therefore \(n_a=W_a/D\) is positive with odd numerator and odd denominator
in lowest terms, and
\(2^{h_a}n_{a+1}=3n_a+1\). Its two-adic halving valuation is exactly
\(h_a\), because \(n_{a+1}\) is odd. Hence every word in Theorem 1
defines a positive rational accelerated cycle.

The minimum over the full shortcut cycle is also one of these odd states:
a positive even state is followed by its smaller half.

For an **integer** cycle the additional necessary and sufficient condition
is \(D\mid W_a\) for one rotation. It propagates to all rotations by
(3), because \(D\) is odd. This exact ordered test is derived separately
in [`CYCLE-WORDS.md`](CYCLE-WORDS.md), Section 1.

## 4. A quantitative gap below the mechanical extremizer

Suppose \(k\ge2\), and define the positive integer

\[
 G(k,H)=\min_{1\le i<k}
       3^{k-1-i}2^{\lfloor iH/k\rfloor-1}.                  \tag{4}
\]

If \(h\) is not a rotation of \(b\), at least one prefix at the
maximal-discrepancy rotation is smaller than its floor bound by at least 1.
At that index its lost contribution is at least the corresponding term in
(4). Consequently

\[
 \boxed{\quad m(h)\le\frac{M(k,H)-G(k,H)}D.\quad}            \tag{5}
\]

Since \(H/k>\log_2 3\), the terms in (4) are greater than
\(3^{k-1}/4\), giving a simple weaker gap of that size.

A positive integer cycle attaining the mechanical extremum must be the
trivial cycle. For completeness, the arithmetic reason is as follows.
The associated shortcut word is rational mechanical, with reduced slope
\(p/q\). Its phases have carry bits
\(b_r(t)=\mathbf1\{(tp+r)\bmod q+p\ge q\}\).
Since \(\gcd(p,q)=1\), cyclic shifts visit every phase. The phase-0 word
starts with 0 and ends with 1; phase \(q-1\) starts with 1 and ends with 0.
At an interior position \(1\le t\le q-2\), the respective residues are
\(a=tp\bmod q\) and \(a-1\). Their carry bits could differ only if
\(a+p=q\), which would make \((t+1)p\) divisible by \(q\), impossible.
Thus the two words are \(0u1\) and \(1u0\).

These phases are actual orbit states and \(q\) is an actual return period:
two rationals with identical infinite parity words, written over a common
odd denominator, have numerator difference divisible by every power of two,
so are equal.
If both extreme phases are integer return words, write
\(L=|u|\), let \(r\) count its ones, and write its affine map as
\((3^rX+d)/2^L\). For the corresponding return seeds \(x,y\),

\[
 Qx=3^r+2d,\qquad Qy=6d+2^{L+1},\qquad
 Q=2^{L+2}-3^{r+1}>0.
\]

Thus \(Q(3x-y+1)=2^{L+1}\). The odd positive integer \(Q\) must
equal 1. If \(L\ge1\), reduction modulo 8 contradicts
\(2^{L+2}-3^{r+1}=1\), since a power of 3 is 1 or 3 modulo 8.
Hence \(u\) is empty and the two shortcut states are 1 and 2.
The accelerated exponent word is all 2s. This is the endpoint argument
also explained in [`STURMIAN-ATTEMPT.md`](STURMIAN-ATTEMPT.md), Section 5;
it is not a new locally compiled integer-cycle classification theorem.

It follows that every nontrivial positive integer cycle satisfies the strict
extremizer gap (5). This is stronger than simply excluding equality in (2).

## 5. What a verified lower bound on the minimum can exclude

If a candidate cycle has minimum \(m\ge B>0\), then the exact necessary
condition is

\[
 BD\le M(k,H).
\]

For a nontrivial integer cycle, Section 4 improves this to
\(BD\le M(k,H)-G(k,H)\). These are finite integer comparisons when
\(B\) is an integer. In particular, a verified convergence range up to
\(B\) excludes a count pair if its sharp upper minimum is at most \(B\).
The convergence verification is an explicit external hypothesis, not supplied
by this note.

To see the Diophantine scale, put \(R=2^{H/k}>3\). Geometric summation
and \(2^{z-1}<2^{\lfloor z\rfloor}\le2^z\) give

\[
 \frac1{2(R-3)}<\frac{M(k,H)}D\le\frac1{R-3}.               \tag{6}
\]

The upper equality holds exactly when \(k\mid H\). Thus \(m\ge B\)
requires

\[
 0<H\log2-k\log3
 \le k\log\left(1+\frac1{3B}\right)
 \le\frac{k}{3B}.                                           \tag{7}
\]

The ordered sum \(M\) sharpens this scalar approximation restriction, but
it does not make the positive gap between the powers uniformly large enough
to exclude every \((k,H)\).

## 6. Large primitive rational cycles survive the ordering bounds

There is a concrete obstruction to deriving a universal minimum bound after
discarding divisibility. For any \(k\ge3\), take

\[
 H=\lceil k\log_2 3\rceil.
\]

Irrationality of \(\log_2 3\) gives
\(3^k<2^H<2\cdot3^k\), hence \(0<D<3^k\). The mechanical exponents
are 1 or 2. More than half are 2, because \(H>3k/2\), so there is a
cyclically adjacent pair \(22\).

Replace one such pair by \(13\), preserving \((k,H)\). Call the new word
\(h'\). It has exactly one occurrence of 3, and is therefore not a power
of a shorter cyclic word. Its rational cycle is primitive: an earlier return
would repeat the exact halving itinerary and contradict that unique 3.

For **every** cyclic rotation and every prefix length, the modified prefix
sum differs from the old one by one of \(-1,0,1\). A prefix contains
neither changed position, both, only the decremented position, or only the
incremented position. This includes rotations whose cut lies between the
two positions. Thus each new weighted summand is at least half the old one:

\[
 \min_a W_a(h')\ge\tfrac12\min_aW_a(b)=\tfrac12M(k,H).
\]

Also every term of \(M\) is greater than \(3^{k-1}/2\), since
\(H/k>\log_2 3\). Therefore

\[
 \boxed{\quad
 m(h')\ge\frac{M(k,H)}{2D}>\frac{k}{12}.
 \quad}                                                     \tag{8}
\]

These are primitive, nonmechanical positive rational cycles with unbounded
minimum. This construction does **not** decide whether any of these words
passes \(D\mid W\). It proves that rational positivity, primitive order,
and an arbitrarily large lower bound on the cycle minimum do not themselves
contradict the cycle equations.

The subsequent [one-swap exclusion](docs/MECHANICAL-SWAP-EXCLUSION.md)
proves that this entire rational family fails the integer-cycle condition.
It uses parity-factor complexity, Matveev's logarithm bound, and finite
Lean arithmetic certificates. The rational extremal result above is unchanged.

## 7. Remaining task

The extremal optimization is complete for the rational relaxation: (2) is
sharp, its equality cases are classified, and (5) quantifies a loss for every
nonmechanical word. The unresolved integer condition remains the actual
ordered divisibility \(2^H-3^k\mid W(h)\) across unbounded counts and
unbounded word families. Neither a fixed verified minimum cutoff nor the
sharp rotation bound removes that condition or proves cycle uniqueness.
