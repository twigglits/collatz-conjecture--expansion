# Aperiodic schedules: what the integer constraint excludes

This attempt rules out every positive integer realization of a critical
balanced halving schedule, and gives a stronger necessary condition on any
divergent orbit. It does **not** rule out all aperiodic schedules or nontrivial
cycles, and therefore does not settle Collatz. The arguments below are written
proofs, not Lean certificates. No claim of novelty is made.

**Follow-up:** [`STURMIAN-ATTEMPT.md`](STURMIAN-ATTEMPT.md) excludes the
mechanical-halving family left open in Section 5 using a separate
growth–complexity argument. [`CollatzPacking.lean`](CollatzPacking.lean) now
checks the sharper finite image bound and fixed-weight packing step; the
summability and real-limit arguments here remain written proofs.

For the accelerated positive odd orbit write

\[
 2^{h_i}n_{i+1}=3n_i+1,\qquad
 H_k=\sum_{i<k}h_i,\quad \alpha=\log_2 3,\quad
 A_k=\frac{3^k}{2^{H_k}}.
\]

The exact multiplicative identity is

\[
 n_k=n_0A_kP_k,\qquad
 P_k=\prod_{i<k}\left(1+\frac1{3n_i}\right).
 \tag{1}
\]

The central distinction is between a positive real solution of the prescribed
affine equations and a positive **integer** orbit. Integer nonrepetition
imposes strong counting restrictions.

## 1. An elementary correction bound and its consequence

Assume first that the orbit never repeats. It consists of distinct positive
odd integers. After discarding its first term if necessary, none is divisible
by three: the equation \(2^{h_i}n_{i+1}=3n_i+1\) proves this immediately.
We reindex this tail starting at zero.

Sort the first \(k\) values increasingly as \(b_0,\ldots,b_{k-1}\).
Positive odd integers not divisible by three begin
\(1,5,7,11,13,17,\ldots\), so \(b_j\ge3j+1\). For \(k\ge1\),

\[
\begin{aligned}
 \log P_k
 &\le\frac13\sum_{j<k}\frac1{b_j}\\
 &\le\frac13+\frac19\sum_{j=1}^{k-1}\frac1j\\
 &\le\frac49+\frac19\log k.
\end{aligned}
\]

Here \(\log\) is the natural logarithm; the empty sum when \(k=1\) is zero.
Thus

\[
 P_k\le e^{4/9}k^{1/9}.
 \tag{2}
\]

If \(A_k\le Ck^\beta\) eventually for a fixed \(0\le\beta<8/9\), equations
(1)–(2) bound every one of the first \(N+1\) orbit values by
\(C' N^{\beta+1/9}\), with a constant absorbing the finite initial prefix.
There are only \(O(N^{\beta+1/9})=o(N)\) positive integers below this bound.
They cannot contain \(N+1\) distinct values. Consequently:

**Theorem 1.** If a positive odd Collatz orbit satisfies
\(A_k=O(k^\beta)\) for some \(0\le\beta<8/9\), it eventually repeats.

An equivalent exclusion condition is

\[
 H_k\ge k\alpha-\beta\log_2 k-C
\quad\text{eventually},\qquad 0\le\beta<8/9.
\]

The same proof also gives a finite restriction. If
\(M_N=\max_{0\le j\le N} A_j\), distinctness of \(N+1\) tail values gives

\[
 3N+1\le e^{4/9}n_0M_NN^{1/9}\qquad(N\ge1).
 \tag{3}
\]

Thus the maximum cumulative multiplier of a divergent orbit grows at least
as a constant times \(N^{8/9}\). This elementary argument requires neither
probabilistic assumptions nor the literature result used for comparison below.

## 2. A stronger orbit-packing argument

We can go further by counting possible images of a short parity word. Define
the shortcut map

\[
 U(x)=\begin{cases}(3x+1)/2,&x\text{ odd},\\x/2,&x\text{ even}.
 \end{cases}
\]

Let \(\mathcal O\) be the set of values of an infinite nonrepeating positive
\(U\)-orbit. For every fixed \(\ell\), the restriction of \(U^\ell\) to
\(\mathcal O\) is injective. Otherwise two different positions in the same
orbit would have equal later values, creating a repeated value and a cycle.

We use three finite facts, with proofs included to expose the dependencies.

**Parity counting.** Among \(0\le s<2^\ell\), exactly
\(\binom\ell j\) residues have \(j\) odd steps in their first \(\ell\)
shortcut steps. Every parity word has one residue: when a length-\(t\) word
is already fixed, the two lifts differing by \(2^t\) have \(t\)-th iterates
differing by the odd number \(3^j\), so their next parities differ. Induction
gives a bijection between residues and binary words.

**Affine translation.** If \(s\) has \(j\) odd steps, then

\[
 U^\ell(q2^\ell+s)=3^jq+U^\ell(s).
 \tag{4}
\]

This follows by induction on the steps: every denominator is two, and each
odd step multiplies the coefficient of the starting value by three. The same
induction shows that adding \(q2^\ell\) preserves the first \(\ell\)
parities. A version of (4) is already formalized as `U_affine` in
[`CollatzFrontier.lean`](CollatzFrontier.lean).

**Small residue images.** For such an \(s\),

\[
 0\le U^\ell(s)<2\cdot3^j.
 \tag{5}
\]

Indeed, the starting-value contribution is \(3^js/2^\ell<3^j\). Each of the
\(j\) added ones contributes at most \(3^{j-1-t}\) to the final value, where
\(t=0,\ldots,j-1\) counts earlier odd steps. Their sum is at most
\((3^j-1)/2\). This proves the looser bound (5), including \(j=0\).

Now choose \(\ell=5r\), so \(2^\ell=32^r\), and consider one aligned block
\([q32^r,(q+1)32^r)\). Partition its orbit points by odd-step count \(j\).
By (4)–(5) and injectivity, each fixed \(j\) contributes at most
\(2\cdot3^j\) points. The groups with \(j<3r\) therefore contribute at most

\[
 \sum_{j<3r}2\cdot3^j=27^r-1.
\]

The remaining groups contain at most all residues of weight \(j\ge3r\).
Using the binomial theorem with weight \(3/2\),

\[
\begin{aligned}
 \sum_{j\ge3r}\binom{5r}{j}
 &\le(3/2)^{-3r}\sum_{j=0}^{5r}\binom{5r}{j}(3/2)^j\\
 &=\left(\frac{3125}{108}\right)^r
 \le30^r.
\end{aligned}
\]

Since \(27^r\le30^r\), the aligned block contains at most \(2\cdot30^r\)
orbit values. Every interval of length \(32^r\) lies in at most two such
aligned blocks. We obtain the explicit packing bound

\[
 \boxed{\quad
 \#(\mathcal O\cap[a,a+32^r))\le4\cdot30^r
 \quad(a\ge0,\ r\ge0).
 \quad}
 \tag{6}
\]

Only finite parity counting, the affine identity, and nonrepetition were used.
The proof does not presume that the conjecture is true.

For comparison, Garcia and Tal's published Fundamental Lemma gives a general
collision criterion for dense subsets of intervals; they apply it to prove
zero Banach density for Collatz orbits. The argument above is a direct
specialization to the standard shortcut map, with explicit convenient
constants rather than an optimized exponent. See [Garcia–Tal, *A note on the
generalized 3n+1 problem*, Acta Arithmetica 90 (1999), Lemma 3 and Corollary 1](https://matwbn.icm.edu.pl/ksiazki/aa/aa90/aa9033.pdf).

## 3. Summability forces escape below the critical line

Divide the positive integers into shells \([32^r,32^{r+1})\). Each shell
fits inside an interval of length \(32^{r+1}\). By (6),

\[
 \sum_{x\in\mathcal O}\frac1x
 \le\sum_{r\ge0}\frac{4\cdot30^{r+1}}{32^r}
 =120\sum_{r\ge0}(15/16)^r
 =1920.
 \tag{7}
\]

The constant is deliberately crude. The accelerated odd orbit is a subset
of this shortcut orbit, so its reciprocal sum is finite as well. Equation
(1) now has a uniformly bounded increasing correction product:

\[
 1\le P_k\le e^{640},\qquad P_k\longrightarrow P_\infty<\infty.
\]

A nonrepeating positive integer sequence visits every finite set only
finitely often, hence \(n_k\to\infty\). Therefore (1) proves:

**Theorem 2.** Every divergent positive odd Collatz orbit satisfies

\[
 A_k\longrightarrow\infty,
 \qquad H_k-k\log_2 3\longrightarrow-\infty.
 \tag{8}
\]

In particular, a bounded subsequence of \(A_k\) already precludes divergence.
This is stronger than merely requiring \(A_k\) to be unbounded, or excluding
a uniformly bounded discrepancy band. These are consequences of the packing
proof supplied above, not assumptions about random parity.

The conclusion permits arbitrarily slow escape of the additive discrepancy;
it does not produce a contradiction for every aperiodic itinerary. The
packing estimate gives additional restrictions on running maxima, but no
argument here excludes all schedules satisfying them.

## 4. Critical balanced and Sturmian words have no integer realization

For \(0\le\rho<1\), prescribe the halving sequence

\[
 h_i=\lfloor(i+1)\alpha+\rho\rfloor-
     \lfloor i\alpha+\rho\rfloor,\qquad\alpha=\log_2 3.
 \tag{9}
\]

Each exponent is one or two. This is the mechanical construction; subtracting
one gives a Sturmian binary word. The connection between mechanical words
and Collatz parity coding is studied in [López–Stoll, *The 3x+1 Conjugacy Map
over a Sturmian Word*, Integers 9 (2009)](https://math.colgate.edu/~integers/j13/j13.pdf).

Here \(H_k=\lfloor k\alpha+\rho\rfloor\), so

\[
 \rho-1<H_k-k\alpha\le\rho,\qquad
 2^{-\rho}\le A_k<2^{1-\rho}\le2.
\]

Either Theorem 1 or Theorem 2 excludes a nonrepeating positive integer orbit
with this schedule. Could the realization be an eventual cycle? No. For a
positive accelerated cycle of length \(p\ge1\), multiplication of its step
equations gives

\[
 2^{h_0+\cdots+h_{p-1}}
 =3^p\prod_{i<p}\left(1+\frac1{3n_i}\right)>3^p.
\]

Its mean halving exponent is strictly greater than \(\alpha\). An eventually
cyclic orbit has the same strictly greater limiting mean, whereas (9) has
limiting mean exactly \(\alpha\). Both possible integer behaviors are
excluded.

**Corollary.** No positive integer orbit can follow (9) forever, even after
an arbitrary finite initial segment.

More generally, suppose a prescribed positive halving word satisfies
\(H_k/k\to\alpha\), and \(H_k-k\alpha\) fails to tend to \(-\infty\).
There are then a constant \(C\) and infinitely many \(k\) with
\(H_k-k\alpha\ge-C\), so \(A_k\le2^C\) on that subsequence. Theorem 2
excludes divergence, and the limiting mean excludes an eventual cycle.
Thus this whole larger class has no positive integer realization either.
All these conditions are preserved by deleting a fixed finite prefix.

## 5. The attempted final step, and why it fails

One might try to extend the exclusion to every aperiodic halving word by
using its unique two-adic candidate

\[
 n_0=-\sum_{i=0}^{\infty}\frac{2^{H_i}}{3^{i+1}}
 \quad\text{in }\mathbb Z_2.
 \tag{10}
\]

This series converges two-adically because \(H_i\ge i\). It does not follow
that its value is a positive ordinary integer. Conversely, when the series
also converges in the real numbers, its negative real sum does not identify
its two-adic value as a negative rational number. Equality of limits in these
two different metrics requires a separate argument.

The exact finite identity exposes the missing term:

\[
 n_0+\sum_{i<k}\frac{2^{H_i}}{3^{i+1}}
 =\frac{2^{H_k}}{3^k}n_k
 =n_0P_k.
 \tag{11}
\]

For a hypothetical divergent integer orbit, the right side tends to the
strictly positive number \(n_0P_\infty\), not zero. Discarding it in real
arithmetic is invalid, even though its two-adic valuation tends to infinity.
Equation (10) therefore cannot supply the hoped-for contradiction by a sign
argument.

For instance, mechanical halving words with slope strictly below
\(\log_2 3\) have exponentially growing \(A_k\). The counting restrictions
above are compatible with that growth. Their positive integer realizability
is not decided by this note. Nor does critical mean alone suffice: a
discrepancy tending to \(-\infty\) sublinearly can still have mean
\(\alpha\) while avoiding the stated exclusion.

The remaining task is to exclude **every** positive integer realization of
the surviving aperiodic schedules, and separately every nontrivial positive
cycle. Neither is accomplished here. The progress is an exact exclusion of
substantial prescribed families, rather than an all-case solution.
