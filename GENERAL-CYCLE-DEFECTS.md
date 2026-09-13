# Arbitrary halving exponents with a fixed number of growth steps

The number of halving exponents equal to 1 already bounds the entire period
of a nontrivial positive integer cycle. The remaining exponents may be
arbitrarily large initially; the bounds below control them as well.

Let \(q\) count the exponent-1 steps, \(R\) count the other odd-to-odd
steps, and

\[
 k=q+R,\qquad
 E=\sum_{h_i\ge2}(h_i-2),\qquad
 H=\sum_i h_i=q+2R+E.
\]

Every nontrivial positive integer cycle satisfies

\[
 \boxed{\quad
 \left(\frac43\right)^R2^E\le\left(\frac53\right)^q,
 \qquad k<3q,\quad E<q,\quad H<5q.
 \quad}
 \tag{1}
\]

In particular, each individual halving exponent is at most \(q+1\), and
there are only finitely many possible words for each fixed \(q\). An
explicit height bound is given in §3.

The central integer budget (5) and its finite product derivation are kernel
checked in [`CollatzCycleBudget.lean`](CollatzCycleBudget.lean), under explicit
edge, closure, positive-exponent, and state-at-least-seven hypotheses. The
minimum classification, coarse consequences, height bounds, and rational
constructions below are written proofs, **not separately Lean-certified
theorems**. No numerical enumeration is used. The bounds are elementary
consequences of the cycle equations and imply that the earlier
\(R=O(q^2)\) estimate in
[`CYCLE-WORDS.md`](CYCLE-WORDS.md) is quantitatively weaker, even in its
restricted alphabet \(\{1,2\}\). No novelty claim is made.

## 1. Minimum and centered cycle equations

Write the distinct positive odd members of a primitive cycle in cyclic order
as \(n_0,\ldots,n_{k-1}\), with

\[
 2^{h_i}n_{i+1}=3n_i+1,\qquad h_i\ge1,
 \qquad m=\min_i n_i,\quad M=\max_i n_i.
 \tag{2}
\]

For a nontrivial cycle, \(m\ge7\). Indeed, the minimum is odd and exceeds
one. No odd cycle member is divisible by three, by (2) applied to its
predecessor. Also a minimum congruent to 1 modulo four would have its next
odd value at most \((3m+1)/4<m\). Thus the minimum is odd, is not divisible
by three, and is congruent to 3 modulo four; the first possible value is 7.
This argument does not use a computational verification range.

Center at the fixed point of the exponent-2 map:

\[
 y_i=n_i-1\ge m-1\ge6.
\]

Equation (2) becomes

\[
 2^{h_i}y_{i+1}=3y_i+4-2^{h_i}.
 \tag{3}
\]

For \(h_i=1\), it gives

\[
 \frac{y_{i+1}}{y_i}=\frac32+\frac1{y_i}
 \le\frac32+\frac1{m-1}=:B_m\le\frac53.
\]

For \(h_i\ge2\), it gives

\[
 0<\frac{y_{i+1}}{y_i}
 \le\frac{3}{2^{h_i}}
 =\frac34\,2^{-(h_i-2)}.
\]

Multiplying these inequalities around the cycle cancels every \(y_i\).
Therefore

\[
 \boxed{\quad
 \left(\frac43\right)^R2^E\le B_m^q
 \le\left(\frac53\right)^q.
 \quad}
 \tag{4}
\]

The basic inequality can also be expressed using only integers. An
exponent-1 edge satisfies \(3y_{i+1}\le5y_i\); an exponent at least two
satisfies \(4\cdot2^{h_i-2}y_{i+1}\le3y_i\). Multiplication and
cancellation of the positive product of the \(y_i\) gives

\[
 3^q4^R2^E\le5^q3^R.
 \tag{5}
\]

There must be at least one exponent-1 step: otherwise every step strictly
decreases a value greater than one. Hence \(q\ge1\).

For comparison, the uncentered product identity already gives

\[
 2^H=\prod_i\left(3+\frac1{n_i}\right)
 \le\left(3+\frac1m\right)^k,
\]

and \(H\ge2k-q\). Thus even that argument implies

\[
 k\le\frac{q\log2}{\log\bigl(4/(3+1/m)\bigr)}.
\]

Centering improves the constants and separates the contribution of exponents
greater than two through \(E\).

## 2. Period and total halving bounds

From (4) and \(5/3<(4/3)^2\),

\[
 \left(\frac43\right)^R
 \le\left(\frac53\right)^q
 <\left(\frac43\right)^{2q},
\]

so \(R<2q\) and \(k=q+R<3q\). Similarly,
\(2^E\le(5/3)^q<2^q\), so \(E<q\).

The separate bounds on \(R\) and \(E\) alone would give only
\(H<6q\). To obtain the claimed stronger bound, square (4). Since
\(4^E\ge(4/3)^E\),

\[
 \left(\frac43\right)^{2R+E}
 \le\left[\left(\frac43\right)^R2^E\right]^2
 \le\left(\frac{25}{9}\right)^q
 <\left(\frac43\right)^{4q},
\]

where the last comparison is \(225<256\) after using the common
denominator 81. Hence \(2R+E<4q\) and

\[
 H=q+2R+E<5q.
 \tag{6}
\]

Since these parameters are integers,

\[
 k\le3q-1,\qquad H\le5q-1,\qquad E\le q-1.
\]

Every exponent satisfies \(h_i\le E+2\le q+1\) unless it equals 1,
which satisfies the same bound. In the shortcut map, the primitive cycle has
\(H\) steps; in the ordinary map that separates each odd operation from
all its halvings, it has \(H+k\le8q-2\) steps.

The minimum-sensitive real bounds, when useful, are

\[
 R\le q\frac{\log B_m}{\log(4/3)},\qquad
 E\le q\log_2 B_m,\qquad
 H\le q\left(1+2\frac{\log B_m}{\log(4/3)}\right).
 \tag{7}
\]

For the last inequality, use
\((R+E/2)\log(4/3)\le R\log(4/3)+E\log2\le q\log B_m\).

## 3. An explicit height bound and the finite ordered problem

The centered product also sharpens the logarithmic correction estimate.
Write

\[
 \Lambda=H\log2-k\log3>0.
\]

For exponent 1 the extra factor relative to \(3/2^{h_i}\) is
\(1+2/(3y_i)\); for larger exponents the extra factor in (3) is positive
and at most one. Therefore

\[
 0<\Lambda
 \le q\log\left(1+\frac{2}{3(m-1)}\right)
 <\frac{2q}{3(m-1)}.
 \tag{8}
\]

The ordered denominator \(D=2^H-3^k\) is a positive integer, so

\[
 \Lambda=\log\left(1+\frac{D}{3^k}\right)
 \ge\log(1+3^{-k})>\frac1{3^k+1}.
\]

Combining this with (8) gives an elementary effective bound on the minimum:

\[
 m<1+\frac{2q}{3}(3^k+1).
 \tag{9}
\]

To control the maximum, use the coordinate \(z=n+1\). An exponent-1 step
multiplies \(z\) exactly by \(3/2\). Every other step decreases \(n>1\)
and hence also decreases \(z\). Starting at the minimum and following the
cycle until its maximum uses at most \(q\) growth steps. Thus

\[
 M+1\le\left(\frac32\right)^q(m+1)
 <\left(\frac32\right)^q
   \left[2+\frac{2q}{3}(3^k+1)\right].
 \tag{10}
\]

For a deliberately loose bound depending only on \(q\), (9) gives
\(m+1<2(q+1)3^k\). Using \(k<3q\) in (10) therefore yields

\[
 \boxed{\quad M+1<2(q+1)\left(\frac{81}{2}\right)^q.\quad}
 \tag{11}
\]

The largest shortcut-cycle value is at most \((3M+1)/2\); the largest
ordinary-cycle value is \(3M+1\). Consequently (11) bounds those heights
as well. The constants are conservative and are not intended as competitive
cycle-search limits.

For each fixed \(q\), one can instead work entirely with words: list the
positive compositions of \(H\le5q-1\), retain those with exactly \(q\)
entries equal to 1 and satisfying (5), and test

\[
 D=2^H-3^k>0,\qquad
 D\mid W(h),\qquad
 W(h)=\sum_{i=0}^{k-1}3^{k-1-i}2^{h_0+\cdots+h_{i-1}}.
 \tag{12}
\]

As proved in [`CYCLE-WORDS.md`](CYCLE-WORDS.md), this is a complete
integer-cycle test; rotation of the numerator proves that all intermediate
values are odd integers with the prescribed exact valuations. Primitivity
is checked separately. The full test is also kernel-checked as `word_cycle_iff`
in [`CollatzCycleCriterion.lean`](CollatzCycleCriterion.lean).
The bounds make this a finite procedure for every
fixed \(q\), without searching all initial values up to a height bound.
No such enumeration was run for this note.

This is also a limitation: \(q\) is already proportional to the possible
period, so fixing it does not produce a uniform reduction that covers all
periods. Finite-word rational-cycle methods are established; compare
[Halbeisen–Hungerbühler, *Optimal bounds for the length of rational Collatz
cycles*, §2](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf).

## 4. Relation to the sharp cyclic minimum bound

For fixed \((k,H)\), the sharp cyclic minimum theorem studied in
[`CYCLE-EXTREMA.md`](CYCLE-EXTREMA.md) uses the mechanical numerator

\[
 \mathcal M_{k,H}=
 \sum_{i=0}^{k-1}3^{k-1-i}2^{\lfloor iH/k\rfloor}.
\]

Every word has a cyclic rotation whose rational value is at most
\(\mathcal M_{k,H}/D\). The centered estimates above impose additional
count and minimum restrictions, but none of them uniformly bounds
\(\mathcal M_{k,H}/D\) as \(k\) grows.

In particular, take \(H=\lceil k\log_2 3\rceil\). Then the denominator
is positive, while the slope \(H/k\) approaches the critical value.
The mechanical rational cycle has minimum at least

\[
 \frac{1}{2(2^{H/k}-3)} >\frac{k}{6}.
 \tag{13}
\]

Here is a direct verification of the lower estimate. For the lower
mechanical word, every cyclic prefix of length \(i\) has halving sum at
least \(\lfloor iH/k\rfloor\), so every rotated numerator is at least
\(\mathcal M_{k,H}\). Writing \(t=2^{H/k}>3\),

\[
 \mathcal M_{k,H}
 >\frac12\sum_{i=0}^{k-1}3^{k-1-i}t^i
 =\frac{D}{2(t-3)}.
\]

Also \(t<3\cdot2^{1/k}\le3(1+1/k)\), using convexity of \(2^x\)
on \([0,1]\). This proves (13).

The already-established exclusion of the exact mechanical integer cycles
does not remove all nearby words. The following explicit perturbation
demonstrates the remaining distinction.

## 5. Unbounded primitive nonmechanical rational candidates

Choose any sufficiently large prime \(k\), put
\(H=\lceil k\log_2 3\rceil\), and start with the cyclic mechanical word

\[
 h_i=\lfloor(i+1)H/k\rfloor-\lfloor iH/k\rfloor.
\]

For \(k>15\), we have \(3/2<H/k<5/3\). The lower bound follows from
\(3^2>2^3\); for the upper bound use
\(\log_2 3<8/5\), which follows from \(3^5<2^8\), and
\(1/k<1/15\). Thus every symbol is 1 or 2.

There is no cyclic adjacent pair \(11\): every length-two halving sum is
at least \(\lfloor2H/k\rfloor=3\). But there is a cyclic \(121\).
Indeed, the number of 1s is \(q=2k-H\), the number of 2s is \(R=H-k\),
and \(H/k<5/3\) implies \(R<2q\). If every gap between 1s contained
at least two 2s, this inequality would fail. Since no gap is empty, at least
one gap has length one.

Replace the final \(21\) of such a \(121\) by \(12\). The new word
contains \(11\), so it is not a rotation of any mechanical word of this
slope. Its \((k,H,q,R,E=0)\) counts are unchanged.

For every cyclic starting point and every prefix length, this adjacent swap
changes the prefix halving sum by at most one. Hence every term of each
rotated numerator changes by a factor between \(1/2\) and 2. All rotated
numerators of the perturbed word are therefore at least half the corresponding
mechanical numerators. Its positive rational cycle has minimum

\[
 m_{\mathrm{rat}}>\frac{k}{12}.
 \tag{14}
\]

The word is primitive. Since \(k\) is prime and \(k<H<2k\),
\(\gcd(k,H)=1\). A nontrivial repetition of a shorter word would force
its repetition count to divide both \(k\) and \(H\). Equivalently, its
rational orbit cannot repeat early, since exact odd valuations would then
repeat the halving word.

This construction differs from the \(22\mapsto13\) perturbation in
[`CYCLE-EXTREMA.md`](CYCLE-EXTREMA.md): that construction uses an exponent 3
and obtains primitivity from its unique occurrence; the present construction
stays in \(\{1,2\}\) and uses prime lengths to ensure primitivity.

These are actual cyclic solutions of the prescribed rational affine
equations, with positive odd numerators and a common odd denominator. They
are **not asserted to be integer cycles**. For primes \(k\ge89\), (14)
puts every value above seven, so the written real-variable proofs of (4),
(7), and (8) apply to them directly. Their \(q\) and minima grow without bound, they
satisfy all the count restrictions, and they avoid the exact mechanical
family already excluded elsewhere. The remaining integer condition is
precisely the ordered divisibility test (12).

The subsequent [one-swap exclusion](docs/MECHANICAL-SWAP-EXCLUSION.md)
settles that condition for this constructed family: none of these rational
cycles is an integer cycle. The proof combines a written complexity and
logarithm argument with finite Lean arithmetic certificates. It does not
exclude arbitrary ordered words satisfying the budget.

Thus fixing \(q\) does give effective bounds on period, every exponent,
and height. Allowing \(q\) to grow still leaves unbounded ordered families.
Neither the centered budget nor the sharp cyclic minimum estimate supplies
the uniform divisibility obstruction needed to exclude all nontrivial
positive integer cycles. The full Collatz problem remains open here.
