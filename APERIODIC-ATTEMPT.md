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
[`ORBIT-ESCAPE.md`](ORBIT-ESCAPE.md) optimizes the counting threshold and
derives inverse-power summability and stronger running-maximum restrictions.
The later [recursive packing argument](docs/ORBIT-PACKING-BOOTSTRAP.md)
sharpens the exponent further for arbitrary nonrepeating orbits; its finite
image-transfer lemmas are kernel checked in CollatzPacking.lean.

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

The limit statement by itself gives no quantitative escape rate for the
additive discrepancy. The packing estimate supplies restrictions on running
maxima and frequency of small values, developed in
[`ORBIT-ESCAPE.md`](ORBIT-ESCAPE.md). It does not give a matching lower bound
on every individual iterate, and no argument here excludes all schedules
satisfying these restrictions.

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

## 6. An explicit counterexample to identifying real and 2-adic series limits

The metric distinction in Section 5 can be demonstrated **within the Collatz
series itself**, not just with an unrelated rational sequence. The construction
below is a symbolic pseudo-trajectory, not a positive-integer orbit.

Set \(y_0=2\), choose \(v_0=1\), and obtain \(y_1=5/2\). For \(t\ge1\), define
\[
 v_t=\begin{cases}1,&y_t<2,\\0,&y_t\ge2,\end{cases}\qquad
 y_{t+1}=\begin{cases}(3y_t-1)/2,&v_t=1,\\y_t/2,&v_t=0.\end{cases}
 \tag{12}
\]
Thus \(-y_t\) follows the two Collatz affine formulas according to \(v\),
without imposing their integer parity conditions. Its word begins
\(101111011111011111111111111\ldots\).

**Invariant.** For every \(t\ge1\),
\[
 1\le y_t\le5/2,\qquad y_t=a_t/2^t\quad\text{with }a_t\text{ odd}.
 \tag{13}
\]
The interval is preserved because the branch with \(y_t<2\) lands in
\([1,5/2)\), while the other branch lands in \([1,5/4]\).
The numerator starts at \(a_1=5\). At a 1 it changes to
\(3a_t-2^t\), and at a 0 it stays unchanged. Hence it remains odd,
and the displayed denominator is always the reduced denominator.

Let \(J_t=\sum_{i<t}v_i\), \(A_t=3^{J_t}/2^t\), and
\[
 Q_t=-\sum_{\substack{i<t\\v_i=1}}\frac{2^i}{3^{J_i+1}}.
\]
At a 1, the ratio \(y_{t+1}/y_t\) is at most \(13/10\), since
\(y_t\le5/2\); at a 0 it is \(1/2\). Therefore
\[
 1\le y_t\le 2\frac{(13/5)^{J_t}}{2^t},\qquad
 2^t5^{J_t}\le2\cdot13^{J_t}.                            \tag{14}
\]
In particular \(J_t\to\infty\), and
\[
 \liminf_{t\to\infty}\frac{J_t}{t}
 \ge\frac{\log2}{\log(13/5)}>\frac{\log2}{\log3}.
 \tag{15}
\]
Exact iteration of (12), including the forced first step, gives
\[
 Q_t=-2+\frac{y_t}{A_t}=-2+\frac{a_t}{3^{J_t}}.
\]
Combining this with (14) yields the explicit error estimate
\[
 0<Q_t+2\le2(13/15)^{J_t}\longrightarrow0.
\]
Thus the Collatz series has the **rational real sum**
\[
 \boxed{\Phi_{\mathbb R}(v)=-2.}                         \tag{16}
\]
In contrast, its 2-adic sum is odd: the first summand is \(-1/3\),
and all remaining summands are even 2-adic integers. Consequently
\[
 \boxed{\Phi_2(v)\equiv1\pmod2,\qquad\Phi_2(v)\ne-2.}  \tag{17}
\]
The 2-adic series converges because its successive nonzero summands have
strictly increasing powers of two in their numerators. These are two limits
of exactly the same partial sums, and they are not the same rational value.

There is also a second coding of the same real number: the eventually periodic
word \(01^\infty\) gives
\(-\sum_{i\ge0}2^{i+1}/3^{i+1}=-2\) in both metrics by geometric summation.
Thus the real sum alone does not even determine the compatible residue sequence:
these two codings have equal real sums and different 2-adic sums.

**The word is not eventually periodic.** Suppose a positive-length block of
length \(L\) and weight \(j\) repeats forever after time \(t\ge1\).
Its map on \(y\) is \(y\mapsto ay-b\), with
\(a=3^j/2^L\) and \(b=B/2^L\) for a nonnegative integer \(B\).
If \(j=0\), repeated halvings violate the lower bound 1. Otherwise \(B>0\).
If \(a\le1\), each block reduces the positive state by at least \(b\),
again impossible. For \(a>1\), boundedness of its iterates forces
\(y_t=b/(a-1)=B/(3^j-2^L)\). That rational has odd reduced denominator,
contradicting (13). Therefore \(v\) is aperiodic, and (15) shows that its
lower one-density is strictly supercritical.

The finite algebra in (13) and (14), and the incompatibility with any odd
denominator, are kernel checked in
[RealShadowObstruction.lean](lean/RealShadowObstruction.lean).
The real limits, the periodic-block argument, and the 2-adic limit argument
are written deductions. The independent
[exact replay](verify_real_shadow.py) checks 2,000 steps, the finite sum
identity, the error inequality, and integer parity-prefix reconstruction at
four lengths. Its finite tests are not the proof of the infinite claims.
See the [verification record](results/real-shadow/verification.json).

**Consequence for source selection.** López–Stoll's
[2021 preprint](https://arxiv.org/html/2101.12747) claims in Theorem 1 that a
rational noncyclic trajectory has lower parity density exactly \(\log_3 2\).
Section 2, around equations (15)–(16), identifies the compatible residues of
partial sums with an expansion of the real sum; Section 6 uses this to
transfer irrationality and parity claims between the two settings. The
construction above disproves that identification. It also contradicts the
intermediate inference that the real sum of an aperiodic supercritical word
must be irrational. A rational real sum need not follow the prescribed word
under the parity-controlled map: here \(-2\) is even while \(v_0=1\).

This is an obstruction to that proof, **not a disproof of its stated density
theorem**. No rationality or irrationality claim about \(\Phi_2(v)\) is proved
here. The theorem is not used as a dependency, and neither its claimed
exponential-divergence exclusion nor automatic-word consequences are imported.
The independently established lower-density and packing bounds above remain
unchanged. Determining whether every surviving word has nonintegral
\(\Phi_2\), and excluding nontrivial cycles, remain unresolved.

The four least nonnegative representatives at prefix lengths 64, 128, 512,
and 2,000 were subsequently followed by direct exact integer iteration.
All reached 1; the 2,000-bit representative required 14,792 shortcut steps.
The [candidate replay](results/real-shadow/candidate-replay.json) records
the complete starting integers, step counts, and peak bit lengths.
This is a finite Python calculation, not a Lean certificate or a proof
that the infinite compatible residue sequence never stabilizes.

## 7. Büchi automata and exact arithmetic for repeated blocks

The user's automata suggestion gives a useful separation between a finite
language model and integer realizability. Here \(U(n)=(3n+1)/2\) for odd
\(n\), and \(U(n)=n/2\) for even \(n\). Let
\[
 P=\{(U^t(n)\bmod2)_{t\ge0}:n\in\mathbb Z_{>0}\}.
\]
Two integer states with the same infinite parity stream are equal: agreement
through length \(k\) forces their difference to be divisible by \(2^k\).
The finite implication is kernel checked in
[CollatzRepetition.lean](CollatzRepetition.lean). The classical full 2-adic
coding appears in [Bernstein–Lagarias, Section 1, equations (1.3)–(1.5)](https://websites.umich.edu/~lagarias/doc/bernstein.pdf).
The deductions below use ordinary integer states and do not assume Collatz.
No novelty claim is made.

### The full positive-integer parity language is not omega-regular

Suppose a Büchi automaton with \(q\) states recognizes exactly \(P\).
Choose \(k>q\), and take the parity stream of \(2^k-1\). Its first \(k\)
letters are ones, and the state after them is \(m=3^k-1\); these growth
identities are checked in [CollatzGrowth.lean](CollatzGrowth.lean).
Write the stream as \(1^k\tau\). An accepting run repeats an automaton
state during the first \(k\) transitions. Pumping that finite all-one loop
once preserves Büchi acceptance and yields \(1^{k+p}\tau\), for some \(p>0\).

If the pumped stream came from a positive integer \(n'\), uniqueness of
the state coded by its unchanged tail would give
\[
 U^{k+p}(n')=3^k-1,\qquad
 3^{k+p}(n'+1)=2^{k+p}3^k.
\]
Cancellation gives \(3^p(n'+1)=2^{k+p}\), impossible modulo 3.
Thus no such automaton exists. This rules out an exact finite Büchi
recognizer on the parity alphabet; it does not rule out arithmetic
extensions, other encodings, or useful overapproximations.

### A finite divisibility certificate in both time directions

For a nonempty parity block \(w\), let \(\ell=|w|\), let \(j\) be its
number of ones, and write its prescribed affine map as
\[
 F_w(x)=\frac{Ax+B}{D},\qquad A=3^j,\quad D=2^\ell.
\]
Define the integer defect
\[
 \Delta_w(x)=(D-A)x-B.
\]
The exact identity is
\[
 D\Delta_w(F_w(x))=A\Delta_w(x).                       \tag{18}
\]
Consequently, if \(r\) copies of \(w\) lead through integer states from
\(n\) to a fixed endpoint \(m\), then
\[
 A^r\mid\Delta_w(m),\qquad D^r\mid\Delta_w(n).         \tag{19}
\]
These necessary conditions follow by iterating (18) and using
\(\gcd(A,D)=1\). If \(\Delta_w(m)\ne0\) and \(j>0\), the number of
inverse copies is at most \(\lfloor\nu_3(\Delta_w(m))/j\rfloor\).
If \(\Delta_w(n)\ne0\), the number of forward copies is at most
\(\lfloor\nu_2(\Delta_w(n))/\ell\rfloor\).
Valuations here mean those of the absolute value of a nonzero integer.
Zero defect is the separate fixed-point case \(F_w(x)=x\).

For these Collatz blocks the divisibility tests are also sufficient.
For the backward test, put
\[
 N_r=D^r m-B\sum_{i=0}^{r-1}D^{r-1-i}A^i.
\]
The candidate inverse state is \(N_r/A^r\), and
\[
 (D-A)N_r=D^r\Delta_w(m)+A^r B.
\]
Since \(\gcd(A,D-A)=\gcd(A,D)=1\), it is an integer exactly when
\(A^r\mid\Delta_w(m)\). The same test holds at each smaller repetition
count, so all block-boundary states are integers. Integer endpoints of a
prescribed block imply the correct intermediate parities: its numerator
is \(Ax+B\) modulo \(D=2^\ell\), and \(A\) is odd, so there is exactly
one compatible residue modulo \(D\), namely the residue coding \(w\).
Reversing its individual branches preserves positivity whenever the
inverse is integral and the endpoint is positive. Thus this is a criterion
for actual positive block prehistories. Swapping \(A,D\) and replacing
\(B\) with \(-B\) gives the forward integrality criterion; applying the same
parity-residue argument to each block makes it an actual forward criterion.

The necessary divisibilities, their finite cutoff, and the implication
\[
 \bigl(\forall r\ \exists n_r:\ F_w^r(n_r)=m
       \text{ through integer states}\bigr)
 \Longrightarrow F_w(m)=m\qquad(j>0)                 \tag{20}
\]
are kernel checked in [BuchiArithmetic.lean](lean/BuchiArithmetic.lean).
The prehistories in (20) need not be consistent across different \(r\).
The sufficiency proof and the connection to automata are written deductions,
not claimed as Lean formalizations.

### Every sound Büchi sublanguage contains only eventually cyclic orbits

Suppose a finite Büchi automaton accepts a language \(L\subseteq P\),
and let \(s\in L\). A positive orbit has infinitely many odd steps:
an eventually all-even positive orbit would require its tail's initial
integer to be divisible by every power of 2. Along an accepting run on
\(s\), some automaton state therefore repeats with a nonempty block \(w\)
containing a one between the occurrences. Write \(s=u w\tau\).

For every \(r\ge0\), the word \(u w^r\tau\) is accepted: pumping or
removing a finite loop leaves an accepting infinite suffix. Soundness
provides a positive-integer realization for every such word. The fixed tail
\(\tau\) determines the same integer \(m\) in each realization, so (20)
forces \(F_w(m)=m\). In the original orbit, the state \(x\) just before
\(w\) satisfies \(F_w(x)=m=F_w(m)\). Since \(A>0\), \(x=m\), proving
an actual orbit repetition. Thus every stream in \(L\) is eventually cyclic.

This is a limitation on sound *underapproximations* of parity streams.
It does not justify rejecting a loop in an *overapproximation*: such an
automaton may accept pumped words having no positive-integer realization.
Nor does it exclude a nontrivial integer cycle.

### What an arithmetic extension still has to prove

For a fixed block, the forward counter \(\nu_2(\Delta_w(n))\) drops by
\(\ell\) on each repetition. But changing the block changes \(A,B,D\)
and therefore changes the defect being measured. No bound on these counter
resets sufficient for a ranking function for arbitrary block sequences has
been proved. In fact a state-independent reset bound is false. For \(k\ge1\),
\[
 2(2^k-1)\longmapsto 2^k-1
\]
is one even step. The block \(0\) has defect \(\Delta_0(n)=n\), whose
2-adic valuation at the source is exactly 1. The next block \(1\) has
defect \(\Delta_1(x)=-x-1=-2^k\), whose valuation is \(k\).
Thus changing block can reset the counter from 1 to any positive integer
in a single genuine Collatz step. The identities giving this family are
kernel checked by **unbounded_counter_reset**. This does not exclude a
more elaborate ranking function incorporating the state's magnitude.
Equation (19) alone cannot eliminate a divergent aperiodic path.
This is the missing obligation for the proposed automata-plus-arithmetic
approach, rather than a finite-state emptiness computation by itself.

[Yolcu–Aaronson–Heule](https://arxiv.org/abs/2105.14697) provide relevant
prior work: a string-rewriting termination problem equivalent to Collatz
and automated proofs for weakened systems, without a proof of Collatz.
Their results are motivation, not dependencies of (18)–(20).

The [exact replay](verify_buchi_arithmetic.py) checks 510 words of lengths
1–8, endpoints 1–128, and repetition counts 0–5: 783,360 directional
criterion checks, plus 2,048 forbidden extensions of all-one prefixes.
The [verification record](results/buchi-arithmetic/verification.json)
distinguishes these finite checks from the kernel lemmas and written
all-length arguments. Neither a universal descent certificate nor a
positive-integer counterexample has been obtained.

## 8. Why finitely many valuation corrections do not repair a size ranking

The counter resets in Section 7 suggested supplementing them with the
integer's magnitude. The following obstruction rules out a precise class
of such attempts. It does not rule out arbitrary ranking functions.

First consider the feature vector
\[
 \Phi(n)=(\nu_2(n),\nu_2(n+1),\nu_3(n),\nu_3(n+1),n\bmod M)
\]
for any fixed positive modulus \(M\). For every positive integer \(s\),
the shortcut map has the exact path
\[
 192s-5\ \longmapsto\ 288s-7\ \longmapsto\ 432s-10\
 \longmapsto\ 216s-5.                                  \tag{21}
\]
The endpoints are both 3 modulo 8 and 1 modulo 3, so their four
valuations are exactly \((0,2,0,0)\). Their difference is \(24s>0\).
Taking \(s\) to be any positive multiple of \(M\) also makes their
residues modulo \(M\) agree.

It follows that no function \(R(n)=H(n,\Phi(n))\), with \(H(n,z)\)
nondecreasing in \(n\) for each fixed \(z\), can strictly decrease at
every Collatz step outside a finite set. Choose \(s\) large enough that
all four states exceed the exceptional set. Strict decrease along the
three transitions would imply \(R(216s-5)<R(192s-5)\), whereas equality
of the features and size monotonicity imply the opposite inequality.
This includes \(\log n+G(\Phi(n))\) for an arbitrary function \(G\),
not merely a linear combination of the valuations.

The exact path, endpoint residues, arbitrary-modulus specialization, and
the resulting contradiction for integer-valued ranks are kernel checked
in [BuchiArithmetic.lean](lean/BuchiArithmetic.lean). The interpretation
as exact valuations and the real-valued ranking formulation are written
deductions.

### Extension to any fixed finite list of polynomial valuations

Let \(M\ge1\), let \(\mathcal P\) be a finite set of primes, and let
\(f_1,\ldots,f_d\in\mathbb Z[X]\) be nonzero polynomials. Define
\[
 \Phi(n)=\bigl(n\bmod M,\;(\nu_p(f_i(n)))_{p\in\mathcal P,\,1\le i\le d}\bigr).
\]
Values at polynomial zeros may be assigned an extra symbol; none of
the constructed endpoints is a zero. There are arbitrarily large
positive integers \(n\) and positive finite Collatz paths from \(n\)
to a larger integer \(m\) with \(\Phi(n)=\Phi(m)\). All states on the
constructed path are at least \(n\). Therefore the same obstruction
to \(R(n)=H(n,\Phi(n))\) holds for this larger class of features.

Here is a construction and proof. Enlarge \(\mathcal P\) to include 2,
3, and the prime factors of \(M\); equality of the enlarged feature
vector is sufficient. Let \(E\) be a common multiple of \(p-1\) for
the primes \(p>3\) in this set, taking \(E=1\) if there are none.
For multiples \(j\) of \(E\) with \(j\ge2\), use the block \(w_j=1^j0\):
\[
 A=3^j,\quad D=2^{j+1},\quad B=3^j-2^j,\qquad
 F_j(x)=\frac{Ax+B}{D},\qquad
 c_j=\frac{B}{D-A}<0.                                  \tag{22}
\]
These \(c_j\) are distinct: writing \(r=(3/2)^j>2\) gives
\(c_j=(r-1)/(2-r)\), a strictly increasing function of \(r>2\).
Consequently one can choose such a \(j\) avoiding the finitely many
roots of all the \(f_i\).

The denominator \(D-A\) is odd and is not divisible by 3. At a prime
\(p>3\) under consideration, Fermat's theorem gives
\(2^j\equiv3^j\equiv1\pmod p\), hence \(D-A\equiv1\pmod p\).
Thus \(c_j\) has a denominator invertible at every selected prime.
Each \(f_i(c_j)\) is nonzero and has a finite nonnegative \(p\)-adic
valuation. Choose integers
\[
 K_p\ge\max\bigl(1,\nu_p(M),\,1+\max_i\nu_p(f_i(c_j))\bigr).
\]
For an empty polynomial list the last maximum is omitted.
Choose \(n\) in the residue class of the rational \(c_j\) modulo
\[
 N=\prod_{p\in\mathcal P}p^{K_p+\nu_p(D)}.
\]
This residue class exists because the denominator is coprime to \(N\),
and it contains arbitrarily large positive integers. Set \(m=F_j(n)\).
The 2-adic precision makes \(m\) an integer with the prescribed parity
block. Indeed, \(An+B\equiv0\pmod{2^{j+1}}\), which selects precisely
the unique length-\((j+1)\) parity residue for \(w_j\).

For every selected prime,
\[
 m-c_j=\frac{A}{D}(n-c_j),\qquad
 \nu_p(n-c_j)\ge K_p,\quad \nu_p(m-c_j)\ge K_p.
\]
Polynomial evaluation therefore gives the same nonzero residue as
\(f_i(c_j)\) modulo \(p^{K_p}\), and hence the same exact valuation,
at both endpoints. Also \(n\equiv m\pmod M\). Since \(A>D\), \(B>0\),
and \(n>0\), we have \(m>n\). The preceding \(j\) odd steps each
increase the value; the sole final even step ends at \(m>n\).
This proves the claim without assuming any behavior of the later orbit.

The all-polynomial theorem is a written proof, not a Lean formalization.
The [exact replay](verify_buchi_arithmetic.py) constructs explicit rational
fixed points and positive paths for seven polynomials, including
\(n+5\), \(n^2+1\), \(n^2+n+1\), and \((n+1)^2\), with several prime
sets and moduli. It records the complete integer witnesses and feature
vectors in [replay.json](results/buchi-arithmetic/replay.json).
The \(n+5\) feature deliberately defeats the simple fixed point \(-5\);
the construction chooses a different block. Finite replay supports the
implementation but does not replace the all-feature proof.

This result excludes strict stepwise size-monotone rankings with any
fixed finite selection of these local arithmetic features, even if they
are combined nonlinearly and even after any finite exceptional range.
It does not exclude a rank with different dependence on magnitude,
unboundedly many features, orbit history, or a more general return rule.
The rational fixed points in (22) generate finite positive growing
segments, not positive cycles or infinite counterexamples.

## 9. Coalescence induction and its finite-horizon limit

For the shortcut map, define
\[
 W(n)\iff \exists\,0<m<n,\ a,b\ge0:\ U^a(n)=U^b(m).
\]
The Collatz conjecture is equivalent to \(W(n)\) for every \(n>1\).
For the forward implication take \(m=1\). For the reverse implication,
strong induction makes the smaller start converge, and the common point
transfers convergence to the original start. The common point can exceed
both starts. [CoalescenceDescent.lean](lean/CoalescenceDescent.lean) kernel
checks the equivalence, including transfer between shortcut and ordinary
iteration; it does not establish the universal premise.

For a fixed binary modulus \(2^k\), equal-time images of two residues
with the same odd-step count have the same affine slope. If
\(0<s<r<2^k\), \(t\le k\), and
\[
 w_t(r)=w_t(s),\qquad U^t(r)=U^t(s),
\]
then every pair \(2^kq+r,2^kq+s\), \(q\ge0\), coalesces at time \(t\).
The Lean checker combines this test with exact direct descent, including
the additive term and the exceptional starts 0 and 1.

At depth eight the combined test covers 240 of 256 infinite residue
classes; direct descent alone covers 237. The additional classes are
63, 207, and 223 modulo 256. For example,
\[
 U^8(256q+63)=U^8(256q+62)=729q+182.
\]
The kernel checks the complete finite table and proves that a least
counterexample must have residue in
\[
 \{27,31,47,71,91,103,111,127,155,159,167,191,231,239,251,255\}
 \pmod{256}.
\]
It also proves equivalence to establishing \(W(n)\) on those remaining
infinite classes. This is a reduction, not their resolution. Independent
Python enumeration at depths 12, 16, and 18 adds respectively 44, 394,
and 1,391 classes beyond direct descent at the **same** depth. These
larger counts are not kernel checked and do not supersede the existing
depth-26 direct-descent certificate.

### No fixed bound on either meeting time can suffice

There is a stronger obstruction than the previously proved absence of
a uniform direct-descent time. For every \(K\ge1\), choose a positive
integer \(n\) with
\[
 n\equiv-1\pmod{2^K},\qquad n\equiv0\pmod{3^K}.       \tag{23}
\]
The Chinese remainder theorem supplies arbitrarily large such starts.
Then
\[
 U^a(n)\ne U^b(m)
 \quad(0<m<n,\ 0\le a,b\le K).                       \tag{24}
\]
Here is an all-horizon proof. Write \(w_t(x)\) for the odd-step count.
Three elementary orbit inequalities are useful:
\[
\begin{aligned}
 x<2^t Q&\ \Longrightarrow\ U^t(x)<3^{w_t(x)}Q,        &&\tag{25}\\
 3^{w_t(x)}(x+1)&\le2^t(U^t(x)+1),                    &&\tag{26}\\
 2^t(U^t(x)+1)&\le3^{w_t(x)}x+3^t.                   &&\tag{27}
\end{aligned}
\]
For (25), induct on \(t\): an even first step replaces the bound by
\(2^{t-1}Q\), an odd first step by \(2^{t-1}(3Q)\).
For (26), each odd step satisfies \(2(U(x)+1)=3(x+1)\),
and each even step satisfies \(2(U(x)+1)\ge x+1\).
For (27), the additive numerator of any length-\(t\) branch word is
at most \(3^t-2^t\), attained by the all-odd word. Induction proves
this using \(w_t(x)\le t\).

The first \(K\) steps from (23) are odd, so
\[
 2^a(U^a(n)+1)=3^a(n+1).                              \tag{28}
\]
Suppose \(U^b(m)=U^a(n)\). If \(b<a\), (27) implies
\(U^b(m)+1\le(3/2)^b(m+1)<(3/2)^a(n+1)\), a contradiction.
Otherwise write \(b=c+a\), set
\[
 z=U^c(m),\quad i=w_c(m),\quad h=w_a(z),\quad
 n=3^i q,\quad T=3^{a-h}q.
\]
Here \(i\le c\le K\), so the integer \(q\) exists by (23), and
\(h\le a\). Combining (27) on the suffix with (28) yields
\[
 3^h z\ge3^a n,\qquad z\ge3^iT.
\]
The contrapositive of (25) on the prefix gives \(m\ge2^cT\).
Put \(A=3^{i+h}\) and \(B=2^c3^a\). Since \(A2^cT=Bn\),
we have \(Am\ge Bn\). Applying (26) successively to the prefix
and suffix also gives \(A(m+1)\le B(n+1)\). Subtraction yields
\(A\le B\). Therefore
\[
 Am\ge Bn\ge An,
\]
and \(m\ge n\), again a contradiction. This proves (24).

All three inequalities and the complete no-uniform-coalescence-horizon
theorem are kernel checked in the Lean module. Its existence proof avoids
an external CRT dependency: start with \(n_0=3\) and set
\(n_{j+1}=(n_j+1)^3-1=n_j(n_j^2+3n_j+3)\).
Induction gives \(2^{j+1}\mid n_j+1\) and \(3^{j+1}\mid n_j\),
with \(n_j>1\). These witnesses suffice for every horizon; the replay
uses smaller CRT representatives for efficiency. The kernel proofs use
no admitted claims, native evaluation, or new axioms.

The proof addresses arbitrary smaller positive starts and unequal meeting
times, not only the equal-weight residue pairing used by the finite checker.
It does not assert that the chosen starts never merge or converge.
The horizon increases along with the chosen start; exchanging these
quantifiers would be invalid. A universal coalescence proof therefore
requires an unbounded, start-dependent search or a different global argument.

[verify_coalescence.py](verify_coalescence.py) independently enumerates
every inverse branch through depth 24 at every permitted forward image
of one CRT start for each horizon 1 through 24. It checks 716,286 inverse
nodes and finds no smaller meeting start. It also checks 571,137 exact
shifted-start identities. These computations are finite support for the
implementation; the all-horizon conclusion has the universal kernel proof.
The [verification record](results/coalescence/verification.json) records
source hashes, build commands, logs, and the distinct verification scopes.

## 10. Quantitative meeting horizons and the first-drop gap

The obstruction in Section 9 can be made quantitative without introducing
new number-theoretic assumptions. For every integer \(K\ge1\) there is
a positive start \(n_K\) such that
\[
 3^K\le n_K<6^K,\qquad
 U^a(n_K)\ne U^b(m)\quad
 (0<m<n_K,\ a,b\le K).                               \tag{29}
\]
Take the constructive witness from Section 9 and reduce it modulo
\(2^K3^K\). Its residue retains \(3^K\mid n_K\) and
\(2^K\mid n_K+1\). The residue cannot be zero, since that would make
\(2^K\) divide 1. Thus it is at least \(3^K\), and Section 9 applies.
[CoalescenceHeight.lean](lean/CoalescenceHeight.lean) kernel checks this
reduction and the power bounds.

If \(h(n)\) denotes the minimum of \(\max(a,b)\) over all smaller-start
meetings, taking \(h(n)=\infty\) when none exists, then (29) gives
\[
 h(n_K)>K>\frac{\log n_K}{\log6}.
\]
The lower bound \(n_K\ge3^K\) makes these inputs unbounded. Therefore
no bound \(h(n)=o(\log n)\) can hold uniformly. This conclusion does
**not** rule out an upper bound \(C\log n\), and no such upper bound
has been proved here. Establishing one would prove Collatz via the
coalescence induction theorem, but it is stronger than what that theorem
requires.

### An exact obstruction to early coalescence at 27

The set
\[
 S=\{1,2,\ldots,26,29,32,35,38,40,44,53,80\}
\]
is forward invariant under the shortcut map. The first 59 states of
the orbit starting at 27, at times 0 through 58, are disjoint from
\(S\), while \(U^{59}(27)=23\). Hence
\[
 U^a(27)\ne U^b(m)\quad
 (1\le m<27,\ 0\le a<59,\ b\ge0).                   \tag{30}
\]
Unlike a search with a capped inverse depth, (30) allows **every** time
\(b\). The Lean proof checks the finite invariant set and lifts closure
to arbitrary iteration. It also checks that 59 is the first coefficient
stopping time for 27. Thus the first actual descent, first multiplier
drop, and earliest possible forward meeting with any smaller start
all occur at 59 in this example. Coalescence cannot always avoid a long
initial excursion by choosing a more distant inverse branch.

The independent [replay](verify_coalescence_height.py) reconstructs the
invariant set, checks 256 bounded-size CRT witnesses, and computes exact
minimum meeting horizons for starts 2 through 32,768. It traverses all
smaller starts through 192 steps, stopping at the first repeat when
earlier. Every tested start has a meeting within that bound, so all
smaller possible values of \(\max(a,b)\) have been considered. The largest
observed ratio \(h(n)/\lceil\log_2 n\rceil\) is \(59/5\), attained at 27.
This finite observation is not a proof of an upper bound for all inputs.
The [verification record](results/coalescence-height/verification.json)
separates these computations from the universal kernel results.

### The proposed first-multiplier-drop bridge is still missing

A possible route is to prove that the first affine multiplier drop below
1 always supplies a smaller coalescing start, even if direct descent
cannot yet be shown. The direct-descent version is Terras' coefficient
stopping-time conjecture; see [Rozier and Terracol, Section 1](https://arxiv.org/html/2502.00948v3).
The weaker coalescence implication has not been proved here either.
Moreover, either implication would still need an argument ensuring the
relevant first drop exists on every positive orbit. Neither an average
drift calculation nor the finite experiments supply those universal steps.
No result in the new modules assumes them.

## 11. Bidirectional ranking search and a finite-affine obstruction

The coalescence principle allows a global proof to use either direction
of a valid Collatz edge. Call positive integers \(x,y\) adjacent when
\(U(x)=y\) or \(U(y)=x\). A sufficient proof certificate is a
nonnegative integer rank \(R\) such that every \(x>N\) has an adjacent
positive \(y\) with \(R(y)<R(x)\), together with verified convergence
for \(1\le x\le N\). Strong induction on the rank then transfers
convergence across the chosen edge. The theorem
`conjecture_of_graph_rank` in
[CoalescenceEnvelope.lean](lean/CoalescenceEnvelope.lean) kernel checks
this implication. No rank satisfying its hypotheses has been found.

### Exact synthesis attempt

We tested ranks \(R(n)=a_r n+b_r\), \(r=n\bmod M\), with all
\(a_r>0\). For \(n=6Mq+s\), the possible neighbors are
\[
 U(n),\qquad 2n,\qquad (2n-1)/3\quad\text{when }n\equiv2\pmod3.
\]
Each neighbor is an exact affine expression \(Aq+B\), with fixed
residue \(t=B\bmod M\). Its rank difference is
\[
 (a_t A-6Ma_r)q+(a_tB+b_t-a_rs-b_r).
\]
It is negative for all sufficiently large \(q\) exactly when its slope
is negative, or its slope is zero and its constant is negative. Taking
the disjunction over valid neighbors for every \(s\) gives the exact
eventual-progress constraints. The search allows arbitrary finite
exceptional ranges and permits neutral leading slopes. Normalizing
all \(a_r\ge1\) loses no positive-slope solution, since every coefficient
and offset can be scaled by a common positive factor.

[search_graph_ranks.py](search_graph_ranks.py), using Z3 5.1.0, returned
`unsat` for all 22 tested moduli:
\[
 1,2,3,4,6,8,9,12,16,18,24,27,32,36,48,54,64,72,96,108,128,144.
\]
These are exact SMT results for those templates, not Lean proofs.
The solver's constraint hashes and unsatisfiable cores are retained in
the [verification record](results/coalescence-envelope/verification.json).
No timeout is treated as an impossibility result. The following written
argument gives a broader explanation independent of the solver.

### The affine envelope

Let \(2^K\mid n+1\), \(3^K\mid n\), and suppose
\(U^a(n)=U^b(m)\), with \(a,b\le K\). Write \(j=w_b(m)\) and set
\[
 A=2^a3^j,\qquad B=2^b3^a.
\]
The kernel proves the paired inequalities
\[
 Bn\le Am,\qquad A(m+1)\le B(n+1).                  \tag{31}
\]
Consequently \(A\le B\). With \(q=B/A\) and \(c=m-qn\), this is
equivalently
\[
 m=qn+c,\qquad q\ge1,\qquad0\le c\le q-1.           \tag{32}
\]
For \(b\ge a\), split the orbit from \(m\) after \(b-a\) steps and
use the divisibility pullback in Section 9; retaining both inequalities
gives (31). For \(b<a\), the upper affine bound (27) gives its lower
inequality because
\(2^{a-b}3^b\le3^a\); the lower affine bound (26) gives its upper
inequality. These arguments, including both time orderings, are formalized.
An independent exact replay checks (31) and (32) at 716,286 inverse nodes.

### Written theorem: finitely many affine formulas cannot supply the rank

Let \(\mathcal F=\{x\mapsto a_i x+b_i:1\le i\le d\}\), with every
\(a_i>0\). Even allowing an arbitrary assignment of one formula to each
positive integer, there is no function \(R\) selected from this finite
family for which every sufficiently large integer has an adjacent integer
of strictly smaller rank. In particular, residue classes of any fixed
modulus cannot supply such a rank. The selection need not be periodic
or computable for this statement.

**Proof.** Every oriented edge has the real affine form
\(y=\lambda x+\eta\), with
\[
 (\lambda,\eta)\in
 \{(1/2,0),(3/2,1/2),(2,0),(2/3,-1/3)\}.
\]
There are only finitely many choices of \(i,j,\lambda,\eta\). Hence,
beyond a fixed threshold \(H\), strict decrease of \(R\) across an
edge implies \(a_j\lambda\le a_i\): a positive leading difference
would eventually dominate its constant term. Increase \(H\) to include
the proposed exceptional range.

Let \(a_{\min},a_{\max}\) be the smallest and largest slopes. Choose
\(0<\rho<1\) at least as large as every ratio
\(\lambda a_j/a_i<1\) occurring among the finite choices (take any
such \(\rho\) if there are no ratios below 1). Fix \(J\ge1\) with
\(a_{\max}\rho^J<a_{\min}\), and put \(K=2dJ\). Choose \(n>H\)
with \(2^K\mid n+1\) and \(3^K\mid n\). Such starts are arbitrarily
large: adding multiples of \(6^K\) to a witness preserves both conditions.

Suppose the proposed local rank decrease exists. Follow decreasing-rank
edges for \(K\) steps. A strict-rank path never repeats a vertex.
Once it takes a backward edge, taking a forward edge next would return
to the preceding vertex and increase the rank. Thus the path consists
of a forward segment followed by a backward segment, with at most one
change of direction. Every visited vertex is a coalescing start with
both times at most \(K\), so (31) applies. In particular it is at least
\(n>H\), and the proposed next decreasing edge remains available.

Write its vertices \(x_t=q_t n+c_t\), using the affine formulas along
the path. The initial forward segment is all odd, so these slopes are
exactly those in (32): \(q_t\ge1\). If formula \(i_t\) is chosen at
\(x_t\), set \(L_t=a_{i_t}q_t\). Along every edge,
\[
 L_{t+1}/L_t=\lambda a_{i_{t+1}}/a_{i_t}\le1,
 \qquad a_{\min}\le L_t\le a_{\max}.
\]
A strict decrease in \(L_t\) multiplies it by at most \(\rho\), so
there can be at most \(J-1\) such steps.

Consider a run of neutral steps, where \(L_t\) is constant, without a
change of direction. If it had \(d\) edges, two of its \(d+1\) vertices
would use the same formula. Their equal \(L_t\) values would force the
product of the intervening \(\lambda\)'s to be 1. On a forward segment
that product is \(3^u/2^v\); on a backward segment it is
\(2^v/3^u\), with \(v>0\). Neither can equal 1. Therefore each such
run has at most \(d-1\) edges. A neutral run crossing the single
direction change has at most \(2(d-1)\) edges.

There are at most \(J\) neutral runs and at most \(J-1\) strict steps,
so the entire path has at most
\[
 (J-1)+2J(d-1)<2dJ=K
\]
edges, contradicting its construction. This proves the theorem. □

The complete finite-family argument is **written**, not fully formalized
in Lean. The universal envelope, the unequal-power fact used in the
neutral-run argument, and the sufficient rank criterion are kernel proved.
The SMT results are separately identified as solver checks. The argument
does not exclude a nonlinear rank, infinitely many affine formulas, or
an unbounded valuation-dependent construction. It does not prove that
a positive-integer counterexample exists. It closes the particular
finite-affine bidirectional proof search, while leaving the full conjecture
and more general rank constructions unresolved.

## 12. A four-feature valuation rank obstruction

The next attempted rank was
\[
 R(n)=C\log_2 n+a\nu_2(n)+b\nu_2(n+1)
              +c\nu_3(n)+d\nu_3(n+1),\qquad C>0.
\]
Coefficients may be arbitrary real numbers. A decreasing adjacent edge
means a positive integer neighbor under the shortcut map: forward `U(n)`,
the even predecessor `2n`, or the odd predecessor `(2n-1)/3` when
`n ≡ 2 (mod 3)`. Merely being bounded below does not make a real-valued
rank well founded. A proof using such a rank would need an additional
termination argument, for example finite sublevel sets.

**Written theorem.** No rank of the displayed form that is bounded below
on the positive integers supplies a strictly decreasing adjacent edge at
every sufficiently large positive integer. Thus even the necessary local
progress condition fails, regardless of the finite exceptional range.
This excludes this particular template, not general valuation-based ranks.

First, boundedness below forces `C+a ≥ 0`: for `n=3·2^k`, `k≥1`, the
four features are `(k,0,1,0)`, so
`R(n)=(C+a)k+C log₂3+c`. Set `L=C log₂(3/2)`. Exact power inequalities
`2^19<3^12` and `3^5<2^8` imply
\[
 C>0,\qquad 12L-7C>0,\qquad 3C-5L>0,\qquad C+a\ge0. \tag{12.1}
\]

Five infinite arithmetic progressions suffice. The feature vector here is
`(ν₂(n),ν₂(n+1),ν₃(n),ν₃(n+1))`. Each row's source and neighbor features
are constant for every `q≥0`:

| Source | Source features | Forward neighbor | Even predecessor | Odd predecessor |
|---|---|---|---|---|
| `432q+131` | `(0,2,0,1)` | `648q+197` | `864q+262` | `288q+87` |
| `1296q+134` | `(1,0,0,3)` | `648q+67` | `2592q+268` | `864q+89` |
| `216q+137` | `(0,1,0,1)` | `324q+206` | `432q+274` | `144q+91` |
| `864q+142` | `(1,0,0,0)` | `432q+71` | `1728q+284` | none |
| `72q+147` | `(0,2,1,0)` | `108q+221` | `144q+294` | none |

The complete feature data are in
[patterns.json](results/valuation-graph-rank/patterns.json).
[ValuationGraphRank.lean](lean/ValuationGraphRank.lean) proves the exact
features and neighbor identities universally in `q`, using divisibility
by `p^k` and nondivisibility by `p^(k+1)`. The source residue modulo three
also determines whether the odd predecessor exists.

On each progression, at least one of the following conditions is necessary
for decreasing edges at arbitrarily large members:

| Seed | Forward condition | Even-predecessor condition | Odd-predecessor condition |
|---|---|---|---|
| 131 | `-L+b-d>0` | `-C-a+2b+d>0` | `L-b-c+d≥0` |
| 134 | `C+a-2b+3d>0` | `-C-a+3d>0` | `L+a-b+d≥0` |
| 137 | `-L-a+b-d>0` | `-C-a+b+d>0` | `L-b+d≥0` |
| 142 | `C+a-3b-2d>0` | `-C-a-d>0` | none |
| 147 | `-L+b+c-d>0` | `-C-a+2b>0` | none |

These are source rank minus neighbor rank in the limit. The strictness
matters. The odd forward logarithmic increment approaches `L` from above,
so a zero limiting decrease never permits actual decrease. For the odd
predecessor the logarithmic increment approaches `-L` from below, so a
zero limiting decrease does permit actual decrease. Even forward and
doubling ratios are exact. If every condition on a row fails, each of its
finitely many neighbors fails to decrease rank beyond some threshold;
the maximum of those thresholds contradicts the proposed tail property.

There are `3·3·3·2·2=108` ways to select one condition from each row.
For each selection,
[certificates.json](results/valuation-graph-rank/certificates.json) gives
nine nonnegative integer weights for the four inequalities (12.1) and
the five chosen conditions. Their weighted coefficient vectors sum to
zero in every coordinate `(C,L,a,b,c,d)`, and at least one strict
inequality has positive weight. Consequently their weighted left sides
must sum both to zero and to a strictly positive real number. This is a
contradiction for every selection, proving the theorem. No approximate
logarithms or numerical feasibility tolerances enter the deduction.

The Lean module kernel-checks all 108 finite certificate identities,
their exhaustive selection list, the progression lemmas, and the two
power inequalities. The interpretation as inequalities over real numbers,
logarithmic limits, bounded-below implication, and the complete rank
obstruction above are **written bridges**, not a fully formalized Lean
theorem. [verify_valuation_graph_rank.py](verify_valuation_graph_rank.py)
independently reconstructs every row from its neighbors and replays every
certificate using integer arithmetic, without Z3. Discovery used Z3;
verification does not depend on trusting its answer. The
[verification record](results/valuation-graph-rank/verification.json)
records the exact scope. Nonlinear combinations, other features, and
other proof strategies remain open. The Collatz conjecture is unresolved.

## 13. Proper nonlinear ranks and a quadratic obstruction

An arbitrary nonlinear function of the four valuations can evade the
bounded-below obstruction in section 12 for an unhelpful reason. For example,
\[
 R(n)=\log_2 n-\nu_2(n)+2^{-\nu_2(n)}
\]
is positive and strictly decreases along the neighbor `n → 2n` for every
positive integer. On `n=2^k` its values tend to zero. Thus boundedness below
does **not** make this real rank a termination proof. We now require
**properness**: for every real `H`, only finitely many positive integers
satisfy `R(n)≤H`. Equivalently, `R(n)→+∞` as `n→∞` through integers.
This condition would make a strict decreasing-neighbor path terminate.

### A necessary graph condition

Suppose a proper real-valued rank provides a decreasing adjacent edge for
every `n>N`. If `3 | n` and `n>N`, then
\[
 R(2n)>R(n),\qquad R(U(n))<R(n). \tag{13.1}
\]
Indeed, a multiple of three has no odd predecessor under `U`. Each vertex
`2^j n`, `j≥1`, has precisely the neighbors `2^(j-1)n` and `2^(j+1)n`.
If `R(2n)≤R(n)`, properness implies that the rank attains its minimum on
the ray starting at `2n`: the nonempty sublevel set below `R(2n)` is finite.
At a minimizing vertex neither neighbor has smaller rank, including the
boundary neighbor `n`. This contradicts local progress. Hence doubling
increases rank, and the only possible decreasing neighbor of `n` is `U(n)`.

[GraphRankNecessity.lean](lean/GraphRankNecessity.lean) proves (13.1) for
**natural-valued** ranks using strong induction on the rank. The extension
to proper real-valued ranks in the preceding paragraph is a written proof.
The theorem does not assert existence of any such global rank.

### Excluding every quadratic polynomial of the four valuations

**Written theorem.** There is no proper rank
\[
 R(n)=C\log_2 n+P(x,y,z,w),\quad C>0,
 \qquad (x,y,z,w)=(\nu_2(n),\nu_2(n+1),\nu_3(n),\nu_3(n+1)),
\]
where `P` is any real polynomial of total degree at most two, that supplies
a decreasing adjacent edge at every sufficiently large integer.

The constant term cancels in rank differences, and `xy=zw=0` on every
integer. Write the remaining polynomial as
\[
 Ax+By+Zz+Ww+E x^2+F y^2
 +G_{xz}xz+G_{xw}xw+G_{yz}yz+G_{yw}yw+G_{zz}z^2+G_{ww}w^2.
\]
The following necessary restrictions follow from properness and (13.1):
\[
 E=F=0,\quad C+A\ge0,\quad B\le0,\quad
 G_{yw}\ge0,\quad A+G_{xw}\le0. \tag{13.2}
\]
Here are the details, including the unbounded valuation families needed
to justify these restrictions rather than infer them from finite samples.

1. Along `n=2^k` with even `k`, the features are `(k,0,0,0)`.
   Properness forces `E≥0`. For each sufficiently large `k`, choose a
   positive odd `u≤54` such that `2^(k+1)u≡10 (mod 27)` and set
   `n=(2^(k+1)u-1)/3`. Such a choice exists because two is invertible
   modulo 27 and either a residue representative or that representative
   plus 27 is odd. The source features are `(0,1,1,0)` and those of
   `U(n)=2^k u` are `(k,0,0,1)`. These are odd multiples of three tending
   to infinity. Forced forward decrease in (13.1), and the bounded
   logarithmic increment tending to `C log₂(3/2)`, imply `E≤0`.
   Thus `E=0`; the same families give `C+A≥0` and `A+G_xw≤0`.

2. For every `b,c≥1`, the Chinese remainder theorem supplies an integer
   with features `(0,b,c,0)` in
   `0<n<2^(b+1)3^(c+1)`: prescribe
   `n≡2^b-1 (mod 2^(b+1))` and `n≡3^c (mod 3^(c+1))`.
   Its double has features `(1,0,c,0)`. Fix `c=1` and let `b→∞`.
   The inequality `R(2n)>R(n)` forces `F≤0`.
   Conversely, along `n=2^k-1` with odd `k`, the features are `(0,k,0,0)`;
   properness forces `F≥0`. Hence `F=0`.

3. For each fixed `c≥1`, return to the CRT family in step 2.
   The doubling inequality, now with `F=0`, implies `B+G_yz c≤0`.
   Its upper size bound and properness imply `C+B+G_yz c≥0`; a negative
   coefficient would make the rank tend to minus infinity as `b→∞`.
   These two bounds hold for arbitrarily large `c`, so `G_yz=0` and
   `-C≤B≤0`. Only `B≤0` is needed in the final certificates.

4. For fixed `w≥1`, use `n=2^b 3^w-1`, whose features are `(0,b,0,w)`.
   With `F=0`, properness forces `C+B+G_yw w≥0`. Since this holds for
   every positive integer `w`, it forces `G_yw≥0`.

Some equality cases in these weak necessary inequalities also violate
properness; retaining them only enlarges the candidate set and does not
weaken the exclusion.

Set `L=C log₂(3/2)`. After setting `E=F=0`, the exact linear background
conditions used in the certificates are only
\[
 C>0,\quad 12L-7C>0,\quad C+A\ge0,\quad -B\ge0,\quad
 G_{yw}\ge0,\quad -A-G_{xw}\ge0. \tag{13.3}
\]
The logarithm bound again follows from `3^12>2^19`. No restriction on
`G_zz` or `G_ww` is needed for the ensuing finite contradiction.

Six progression patterns, with seeds `151,153,155,170,230,233`, suffice.
Their exact moduli, source/neighbor features, and coefficient rows are
recorded in [certificates.json](results/quadratic-valuation-rank/certificates.json).
The progression with seed 153 consists of multiples of three, so (13.1)
requires its **forward** alternative. Each other row allows every adjacent
edge, with the same strict forward and weak inverse limiting conditions
as section 12. There are `2·1·3·3·3·3=162` selections.

For each selection, twelve nonnegative integer weights combine the six
inequalities (13.3) and six selected edge conditions. The weighted vector
is zero in all twelve coordinates
`(C,L,A,B,Z,W,G_xz,G_xw,G_yz,G_yw,G_zz,G_ww)`, and a strict inequality has
positive weight. Thus the selected inequalities contradict one another
over the real numbers. Every selection fails, proving the written theorem.

[QuadraticValuationRank.lean](lean/QuadraticValuationRank.lean) kernel-checks
the six universal progression feature/edge identities, all 162 finite
certificate identities, and exhaustive selection coverage. The independent
[Python replay](verify_quadratic_valuation_rank.py) reconstructs the
polynomial feature differences and checks every weight identity without
an SMT solver. The graph theorem for natural ranks is separately kernel
proved. Properness over the reals, the coefficient restrictions (13.2),
logarithmic limits, and interpreting the certificates as a contradiction
over the reals remain **written bridges**. See the
[verification record](results/quadratic-valuation-rank/verification.json).

This excludes an entire quadratic template rather than just the tested
starting values. It does not exclude general nonlinear valuation functions,
new arithmetic features, or other proof strategies. It neither proves
convergence for every positive integer nor supplies a counterexample.

## 14. Graph ranks must follow the forward map outside the base closure

The restriction to multiples of three in section 13 can be replaced by
a general functional-graph theorem when the exceptional base is enlarged
to a forward-closed region. This changes which ranking searches are useful.

**Kernel theorem.** Let `f:X→X`, let `S⊆X` satisfy `f(S)⊆S`, and let `≺`
be any well-founded relation on `X`. Suppose every `x∉S` has a neighbor
`y≺x`, where adjacency means `f(x)=y` or `f(y)=x`. Then
\[
                 f(x)\prec x\quad\text{for every }x\notin S. \tag{14.1}
\]
No finiteness, arithmetic, or total-order assumption is needed for this
abstract statement. In particular, well-foundedness is essential;
bounded-below real ranks with infinite descending chains do not qualify.

**Proof.** Use well-founded induction on `x`. A decreasing forward neighbor
already gives the result. Otherwise take a decreasing predecessor `y≺x`
with `f(y)=x`. If `y∈S`, forward closure would put `x∈S`, a contradiction.
Thus `y∉S`, and induction gives `f(y)≺y`, hence `x≺y`. Together with
`y≺x` this is a two-cycle in a well-founded relation, impossible. □

[GraphRankOrientation.lean](lean/GraphRankOrientation.lean) proves this
statement for an arbitrary type and well-founded relation. The theorem
and its auxiliary asymmetry lemma have no axioms. A natural-valued
Collatz-rank specialization and the concrete obstruction below are also
kernel checked, with their printed logical dependencies recorded separately.

### Consequence for a verified finite base

Suppose the proposed Collatz proof checks the finitely many positive starts
`n≤N`, and supplies decreasing graph-rank neighbors for all `n>N`.
Let `S` contain zero and the entire forward orbits of those checked starts.
If each checked start converges, these orbits are finite: after reaching
one the shortcut map alternates between one and two. Thus `S` is finite
and forward closed. Set `B=max S`. For natural ranks, (14.1) now forces
`R(U(n))<R(n)` for every `n∉S`, in particular every `n>B`.

The same conclusion holds for a proper real-valued rank, since finite
sublevel sets make the induced strict rank relation well founded. One
can also see this directly: an infinite descending path stays inside
its initial finite sublevel set and cannot repeat a rank, a contradiction.
This proper-real implication and the construction of `S` from convergence
of a finite base are written bridges; the generic graph theorem itself
is kernel proved.

**The base hypothesis must not be dropped.** We have not proved that the
forward closure of an arbitrary finite base is bounded without verifying
its starts. A formulation that assumes only local progress beyond `N`,
with no well-founded decrease relation or bounded base closure, is not
covered by the full obstruction below. The result applies to the proposed
complete-proof strategy, whose finite base must already be established.

### Arbitrary nonlinear valuation corrections do not rescue this strategy

For any fixed positive modulus `M`, choose a positive multiple `s` of `M`
so large that every state in
\[
 192s-5\ \longmapsto\ 288s-7\ \longmapsto\ 432s-10
          \ \longmapsto\ 216s-5
\]
exceeds `B`. The endpoints have identical features
`(ν₂(n),ν₂(n+1),ν₃(n),ν₃(n+1),n mod M)`, while the last endpoint is larger.
If `R(n)=H(n,Φ(n))` is nondecreasing in its size argument for each fixed
feature vector, then `R(192s-5)≤R(216s-5)`. But (14.1) forces strict
decrease along all three forward edges. This is a contradiction.

`no_feature_monotone_graph_rank` kernel-checks this conclusion for natural
ranks, using explicit modular conditions for the four exact valuations.
Its assumptions include a bounded forward-closed set containing the base.
It does not assert that such a base or a global rank has been found.

Combining (14.1) with the written construction in section 8 gives the
broader **written corollary**: no well-founded rank that is nondecreasing
in size at fixed features, using any fixed finite list of polynomial
valuations at finitely many primes and residues modulo a fixed modulus,
can furnish graph descent outside a verified finite base. In particular,
no proper real rank `C log₂n+G(Φ(n))`, `C>0`, can do so, even when `G` is
an arbitrary nonlinear function. The arbitrarily large growing paths
from section 8 lie wholly outside `S` and have matching endpoint features.
The all-polynomial feature construction remains written, not fully Lean
formalized. This corollary does not silently remove the base hypothesis.

The [independent replay](verify_graph_rank_orientation.py) constructs
closed orbit sets for six finite bases through 32,768 and checks 42 exact
growing paths above their maximum values, for seven moduli. These finite
checks validate the witness construction; the universal graph theorem is
proved independently in Lean. [The verification record](results/graph-rank-orientation/verification.json)
separates these scopes.

Consequently, expanding the degree, adding finitely many polynomial
valuation features, or changing their nonlinear combination cannot repair
this size-monotone graph-rank proof strategy. A rank with different
dependence on magnitude, genuinely different information, or a different
global argument is still possible. No such successful construction has
been established, and the full Collatz conjecture remains unresolved.

## 15. Separated binary blocks and weighted digit-pattern ranks

Binary digit information is not covered by the finite polynomial-valuation
obstruction. The next search therefore tried a different class: a weighted
sum of binary pattern counts and bit length. Exact synthesis at widths
one through nine found contradictions. Their common structure yields a
proof for every fixed width, without relying on those solver answers.

The precise encoding matters. For `n>0`, let `ℓ(n)` be its binary length.
Fix a width `w≥1`, pad its usual binary word with `w-1` zeros on **both**
sides, and let `C_v(n)` count each overlapping length-w word `v`. Consider
\[
 R(n)=\beta+\alpha\ell(n)+\sum_{v\in\{0,1\}^w}\lambda_v C_v(n),
\]
with arbitrary real coefficients. This includes weighted bit length and
population count at width one. No positivity or properness of this score
is assumed in the following forward-descent obstruction.

Put `z=α+λ_(0^w)` and `c=β+(w-1)λ_(0^w)`. Two counting identities hold:
\[
 R(2n)=R(n)+z, \tag{15.1}
\]
and, when `a,b>0` and `k-ℓ(b)≥w-1`,
\[
 R(a2^k+b)=R(a)+R(b)+(k-\ell(b))z-c. \tag{15.2}
\]
Appending a zero adds one all-zero window after boundary padding, giving
(15.1). For (15.2), the binary word consists of the word for a, a gap of
`k-ℓ(b)` zeros, and the word for b. No width-w window can meet nonzero
digits in both blocks. The padded block counts therefore add, with
`k-ℓ(b)-(w-1)` extra all-zero windows. Binary lengths add with the gap,
and the constant term is counted twice before subtracting c. These
observations prove the identities for every permitted width and gap.

In fact, **any score satisfying (15.1) and (15.2) beyond some fixed gap
threshold fails eventual strict forward descent**, whether or not it
was defined using digit counts. To see this, take `q=2^k` with k large.
The following are exact shortcut edges:

| Source | Successor | Rank change from the two block laws |
|---|---|---|
| `2q+2` | `q+1` | `-z` |
| `2q+21` | `3q+32` | `R(3)-R(21)+3z` |
| `6q+9` | `9q+14` | `R(7)-R(3)` |
| `14q+1` | `21q+2` | `R(21)-R(7)-z` |

Here `R(32)=R(1)+5z`, `R(14)=R(7)+z`, and `R(2)=R(1)+z`, by (15.1).
For window scores, `k≥w+5` suffices for every separation in the table.
The first edge would force `z>0`. The other three rank changes sum to
`2z`, so they cannot all be negative. Equivalently, twice the first
change plus the other three is identically zero: the positive integer
weights `(2,1,1,1)` are a universal contradiction certificate.

Since k can be arbitrarily large, all four sources can exceed any
proposed finite exceptional range. This is an obstruction over infinite
families, not an inference from enumerating a finite interval.

[DigitBlockRank.lean](lean/DigitBlockRank.lean) proves the four edge
identities, the cancellation, and the complete impossibility of eventual
forward descent for an **integer-valued** score satisfying the two
structural block laws with any fixed gap threshold. The score laws are
explicit assumptions of that theorem. The all-width digit-count proof
of those laws above, and the real-coefficient formulation, remain written
bridges. No admitted proofs or native evaluation are used.

[verify_digit_block_rank.py](verify_digit_block_rank.py) independently
checks the counting and doubling identities at their minimum permitted
gaps and larger gaps, for widths 1–64. It also checks the full vector
identity with weights `(2,1,1,1)` at three exponents per width, including
4096. Thus cancellation holds separately for bit length and every pattern
count in those finite tests; no choice of numeric score coefficients is
used. The [verification record](results/digit-block-rank/verification.json)
separates the finite replay, kernel theorem, and written interpretation.

Combined with section 14, such a score also cannot provide well-founded
bidirectional progress outside a verified finite base whose forward
closure is bounded. This consequence requires that well-foundedness and
base-closure hypothesis, whereas the forward obstruction does not.

The padding convention and additive laws are part of the result's scope.
It does not classify arbitrary finite-state digit scores, independent
prefix/suffix boundary corrections, nonlinear functions of counts,
interactions between distant binary blocks, or rules that demand a rank
drop only after a varying number of steps. The Collatz conjecture remains
unresolved; these four families are not counterexamples to convergence.

## 16. Inverse-basin counts do not supply an injective orbit-packing contradiction

After the rank obstructions, the next route examined whether inverse-tree
growth could conflict with the project's uniform orbit-packing bound.
There is a structural mismatch in this proposed combination. The packing
theorem bounds a **forward-invariant set on which U is injective**. An
inverse basin counts many different starts whose orbits merge. Those are
different sets, and the missing injectivity cannot be inferred from a
lower bound on the basin's size.

For reference, Krasikov and Lagarias prove a lower bound `x^0.84` for the
number of starts below x whose orbit contains a fixed positive root a,
when `3 ∤ a` and x is sufficiently large depending on a. This is a basin
count, not a count along one trajectory. We use this only to identify the
scope of the proposed comparison, not as a new proof dependency.
[Original paper, abstract and introduction](https://arxiv.org/pdf/math/0205002).

Define `B(a)={n: U^k(n)=a for some k≥0}`. The new
[InverseBasinAudit.lean](lean/InverseBasinAudit.lean) proves the following
distinctions without assuming Collatz:

* If `3 | a`, then `B(a)={2^k a:k≥0}`. A multiple of three has only its
  even predecessor, and induction gives the entire inverse basin.
* If `3 ∤ a`, then B(a) contains distinct positive u,v with `U(u)=U(v)`.
  Both reach a in at most two shortcut steps. For `a=3q+2`, take
  `u=6q+4,v=2q+1`; their common image is a. For `a=3q+1`, take
  `u=12q+4,v=4q+1`; their common image is `2a`, which halves to a.
* If S is forward closed, U is injective on S, and `S⊆B(a)`, then any
  two members of S are comparable by forward iteration. If they reach
  a in i and j steps with `i≤j`, injectivity of `U^i` on S cancels the
  meeting and gives `u=U^(j-i)(v)`. Thus S cannot retain incomparable
  branches of the inverse basin.
  More generally, this chain conclusion holds inside the entire
  **coalescence component** `C(a)={n: U^i(n)=U^j(a) for some i,j}`:
  align two meetings with the root's orbit, then cancel equal iterates.
* In the special case `S⊆B(1)`, such a set S contains only 1 and 2.
  Once S contains any point reaching 1, it contains the shortcut cycle
  `1↔2`. Injectivity prevents any additional predecessor from joining it.
  This is a particularly clear example of why a large basin does not
  yield a large forward-closed injective subset.

For a nonperiodic root, B(a) has a further problem: it contains no nonempty
forward-closed subset at all. If such a subset contained n, it would
contain a and U(a); the latter reaching a again would make a periodic.
This is also kernel proved. Passing instead to the forward-closed C(a)
fixes closure but does not fix the collision or chain restriction.

These are kernel theorems; the statement about B(1) uses no axioms. They do not
give an upper bound for the whole nonconvergent basin. To turn inverse
growth into a contradiction, one would need a new estimate valid for
branching sets, or a lower bound on an actual injective orbit set. The
existing orbit-packing bound and a basin lower bound alone do neither.

### Version-aware check of a tempting density claim

A search result displayed the original `x^0.946` claim from
[Liu, arXiv:2512.13760v1](https://arxiv.org/html/2512.13760v1).
Its Lemma 2.2, as stated, fails at the free tuple `(u1,u2)=(3,1)`.
The floor constraints allow only `v1∈{5,6}`, `v2∈{1,2}`, but none satisfies
`2^(v1+v2)≡2^v2+3 (mod 9)`. Their left-minus-right residues are
`5,4,6,6`. Equivalently, the first admissible inverse step with exponent
six reaches 21, a multiple of three that cannot take another odd inverse
step. This finite counterexample is kernel checked.

The [current v2](https://arxiv.org/abs/2512.13760v2), dated 17 December
2025, instead reports `x^0.3227`; the original improvement must not be
treated as current. V2's Lemma 3.1 still states uniqueness under displayed
conditions that, at level one and `u1=2`, admit both `v1=8` and `v1=10`.
Both have `floor((v1+1)/6)=1`, and `2^v1≡1 (mod 3)` but not modulo nine.
They produce 85 and 341 respectively. This pair is also kernel checked.
[V2, section 3](https://arxiv.org/html/2512.13760v2#S3).
This refutes that uniqueness statement as written; it is **not** a
counterexample to the weaker final counting bound or an audit of every
possible repair. Neither version's counting theorem is adopted here.

The [independent replay](verify_inverse_basin_audit.py) checks explicit
collisions for 21,846 roots through 32,768, six larger roots, 325 dyadic
basin examples, and both
version-specific congruence examples. The [verification record](results/inverse-basin-audit/verification.json)
distinguishes those finite checks from the universal basin theorems.
The full Collatz conjecture, including exclusion of nontrivial cycles
and divergent orbits, remains unresolved.

## 17. The inverse-fibre multiplicity loss is exponentially large

The failure of injectivity from section 16 is quantitative, not just a
single exceptional collision. For a depth k, odd-step count j, and endpoint
y, define
\[
 F_{k,j,y}=\{0\le r<2^k:\operatorname{wt}(k,r)=j,\ U^k(r)=y\},
 \qquad D_k=\max_{j,y}|F_{k,j,y}|.
\]
The index j is part of the fibre definition: these are collisions at the
**same time and the same parity weight**, precisely the partition used
by the orbit-packing argument.

**Written lower bound.** For every `k≥0`,
\[
 D_k\ge\max_{0\le j\le k}\left\lceil\frac{\binom{k}{j}}{3^j}\right\rceil
 \ge \left\lceil\frac{4^k}{(k+1)3^k}\right\rceil. \tag{17.1}
\]
To prove this, the first k parity bits bijectively label the residues
modulo `2^k`. One inductive justification is that r and `r+2^k` have the
same first k parity bits, while their k-th iterates differ by the odd
number `3^wt(k,r)`. Thus their next parity bits are opposite, providing
exactly the two extensions of each word. There are therefore `binom(k,j)`
residues of weight j. The sharp residue-image bound gives `0≤U^k(r)<3^j`.
Pigeonhole counting gives the first inequality in (17.1).

For the second, each weight group satisfies `binom(k,j)≤D_k 3^j`.
Multiply by `3^(k-j)` and sum over j. The binomial theorem gives
\[
 4^k=\sum_{j=0}^k\binom{k}{j}3^{k-j}
      \le (k+1)D_k3^k.
\]
Consequently the required worst-case multiplicity correction cannot be
bounded, polynomial in k, or even subexponential in k: its exponential
growth rate is at least `4/3`. This is a lower bound, not a claim that
`4/3` is the exact maximum-fibre growth rate.

### These collisions persist arbitrarily far from the origin

The exact affine identities are
\[
 \operatorname{wt}(k,2^kq+r)=\operatorname{wt}(k,r),\qquad
 U^k(2^kq+r)=3^jq+U^k(r)\quad\text{when wt}(k,r)=j.
\]
Hence every aligned block `[2^kq,2^k(q+1))` has exactly the same
same-weight fibre partition, translated in its image. Taking q positive
avoids zero and taking q arbitrarily large moves all witnesses beyond
any finite exception range. The weight periodicity and the equivalence
of fibre equalities between aligned blocks are kernel proved in
[InverseFibreGrowth.lean](lean/InverseFibreGrowth.lean).

As a concrete universal certificate, the module checks 48 distinct
positive residues r below `2^16`, all with weight four and `U^16(r)=2`.
For every `q≥0`, their shifts `65536q+r` are distinct positive members
of the q-th block, all with weight four and common endpoint `81q+2`.
The complete residue list is in
[certificate.json](results/inverse-fibre-growth/certificate.json).
This is not merely a collision near the known cycle: the same identity
holds for arbitrarily large q. It says nothing about convergence of
those arbitrary shifted targets.

The [independent replay](verify_inverse_fibre_growth.py) enumerates every
residue at depths 1–20, checking parity-weight histograms, image bounds,
the exact weighted binomial identity, and fibre maxima. At depth 16 the
maximum is 48; at depth 20 it is 140, attained by a weight-five fibre
ending at 47. These **maximality** claims are finite Python results;
the Lean certificate proves the 48-member family and its universal
shifts, not an exhaustive maximum at depth 16 or 20.

The all-depth parity enumeration, pigeonhole assembly, and exponential
interpretation of (17.1) remain written arguments, supported by the
kernel affine and image bounds. [Verification scope](results/inverse-fibre-growth/verification.json).

This closes the proposed repair that would charge only a constant,
polynomial, or subexponential worst-case loss for collisions in arbitrary
components. It does **not** rule out bounds specific to a hypothetical
nonconvergent component, weights that account for branching differently,
or a different proof strategy. The large fibres exhibited here need not
belong to any exceptional component. No new upper bound on such a
component has been proved, and Collatz remains unresolved.

## 18. Methods reviewed from the OpenAI mathematics collection

On 8 October 2026 the user suggested [openai/math](https://github.com/openai/math).
This is a targeted review, not an audit of the whole collection. Its README
distinguishes verification stages. We inspected the catalogue, selected
reasoning summaries, the entropy paper's introduction and strategy, the
permanence paper's strategy, and associated formalization scope statements.
No external theorem from this collection is a dependency of our proofs.

**Account for collisions before counting growth.** The
[self-similar entropy manuscript](https://github.com/openai/math/blob/main/preprints/The-entropy-rate-dimension-formula-for-self-similar-measures-on-the-line-September-24-2026/main.pdf),
sections 1.1–1.2, groups word probabilities by their complete affine maps.
It conditions blocks on symbol counts to fix contractions, and arranges
disjoint scale windows so information gains can be added without reuse.
These are methodological leads. Its hypotheses include contracting real
similarities and an independent coding law; neither is supplied by ordinary
Collatz iteration. Equality of maps is also different from equality of
endpoints at different starting integers. Simply substituting a Collatz
branch count into its dimension formula is unjustified.

For our problem, the elementary identity
`H(X)=H(U^k(X))+H(X | U^k(X))` for a finite random starting value X
identifies the missing quantity exactly: the conditional information lost
under iteration. Section 19 shows this loss can be linear in time inside
the basin of **any** fixed unit root. An entropy approach must control this
loss for its particular distribution and relate the remaining information
to the **same set** used by the orbit-packing bound. Changing measures,
conditioning on nonconvergence, or ignoring merged histories requires proof.

**Seek scale-dependent trapping, with finite entry.** The
[permanence manuscript](https://github.com/openai/math/blob/main/preprints/Uniform-Permanence-in-Weakly-Reversible-Mass-Action-Systems-October-5-2026/permanence.pdf),
section 1.3, uses scale-dependent minima of affine functions, compact
plateaux, strict progress outside a plateau, and passage between scales.
The strictness relies on reaction-network structure and cannot be imported
into Collatz. Its value here is the separation of three obligations:
construct a trapping region, prove finite entry, then identify the possible
limiting dynamics. For Collatz, boundedness alone still permits other cycles.

Our potential analogue would use a height-dependent state description and
variable return times. A useful certificate must exhibit a genuinely
well-founded quantity and prove that every trajectory outside a verified
base makes strict progress at a finite return time. Merely renaming the
existing descent equivalence does not establish any of these estimates.
Sections 8–15 already exclude several fixed local rank templates, while
the coalescence-height result excludes a uniform sublogarithmic horizon.
Those obstructions should be tested against each proposed construction
before a large search.

**Preserve the difficult estimate through every reduction.** The
[two-point correlation summary](https://github.com/openai/math/blob/main/reasoning_traces/ordinary-two-point-correlations.pdf)
repeatedly checks dependence introduced by conditioning, finite-interval
versus independent-residue calculations, and the distinction between
almost-all scales and every scale. These are directly relevant to our
parity models: uniform finite residue statistics do not make one fixed
infinite integer orbit a sequence of independent coin tosses. They also
do not eliminate a sparse exceptional set.

The [Vlasov–Maxwell summary](https://github.com/openai/math/blob/main/reasoning_traces/relativistic-vlasov-maxwell.pdf)
uses proposed impulse and occupation estimates to force divergent total
time for successive momentum doublings. The estimates, not just the
continuation criterion, carry the substantive burden. For Collatz an
analogue preventing infinitely many doublings in finite time would be
insufficient: each finite iterate is already finite. We need to prevent
unbounded growth over infinitely many discrete steps, or prove eventual
entry into the known basin. The separate Navier–Stokes Millennium problem
is still listed as [active by Clay](https://www.claymath.org/millennium/navier-stokes-equation/).

**Verification scope.** The repository's
[entropy scope](https://github.com/openai/math/blob/main/lean/docs/148.md)
states coverage of its dimension theorem. The
[mass-action scope](https://github.com/openai/math/blob/main/lean/docs/149.md)
states an initial-state-dependent boundedness and persistence result;
this is weaker than the common classwise absorbing set in the later
permanence paper. Their comparator challenge files contain placeholder
proofs by design; the accompanying JSON configurations point to separate
solution modules. We inspected the statements and configurations but did
not build those solution modules or independently validate the papers.
Neither a scope label nor an unbuilt comparator configuration is a local
kernel verification. The Kaplansky summary was also sampled for its
assumption audits; no group-ring argument was adopted.

## 19. Uniform inverse branching within every unit-root basin

The collision issue from sections 16–17 persists even when the endpoint
is fixed in advance, including a hypothetical nonconvergent endpoint.
Here a **unit root** means a positive integer a with `3∤a`.

For each such a choose the two exponents e in `{1,...,6}` satisfying
`2^e*a ≡ 1 (mod 3)` and `2^e*a ≠ 1 (mod 9)`, and set
\[
 m_e=2^{6-e}\frac{2^e a-1}{3}=\frac{64a-2^{6-e}}3.
\]
Among the three exponents of the required parity exactly one is excluded
modulo nine, since two has order six modulo nine. The integer
`(2^e*a-1)/3` is positive and odd. Starting with `m_e`, the first `6-e`
steps halve it; the next odd step reaches `2^(e-1)*a`; the remaining
`e-1` steps halve to a. Thus `U^6(m_e)=a` with exactly one odd step.
The two children are distinct, positive, not divisible by three, greater
than a, and satisfy `3*m_e<64*a`.

For `a=9q+r` the explicit children are `192q+d`:

| r | first d | second d |
|---|---|---|
| 1 | 16 | 20 |
| 2 | 32 | 40 |
| 4 | 80 | 85 |
| 5 | 104 | 106 |
| 7 | 148 | 149 |
| 8 | 160 | 170 |

[UniformInverseBranching.lean](lean/UniformInverseBranching.lean) checks
this table and lifts it to every quotient with the affine and weight
identities. It recursively constructs a list L_h(a) with kernel proofs of
\[
 |L_h(a)|=2^h,\qquad L_h(a)\text{ has no duplicates},
\]
\[
 n\in L_h(a)\Longrightarrow
 n>0,\quad3\nmid n,\quad U^{6h}(n)=a,\quad
 \operatorname{wt}(6h,n)=h,\quad3^h n\le64^h a.
\]
Distinct subtrees cannot overlap: applying `U^(6h)` to a shared leaf
would identify their distinct parent roots. This is kernel proved along
with the length, endpoint, weight and size statements. No `native_decide`
or admitted proof is used. Printed dependencies are only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

**Written consequences.** For `a<3^h` all these leaves lie below
`64^h=2^(6h)`, so the same conclusion eventually holds inside the zero
aligned residue block for every fixed unit root. Its same-time,
same-weight inverse-fibre size therefore grows at least as `2^h` along
times `6h`. No bound subexponential in time, even with a root-dependent
constant, can bound all these fibres. This is a lower bound, not an exact
growth rate or a stronger claim than known inverse-basin density bounds.

If a is nonconvergent, every leaf is nonconvergent as well: convergence
of a leaf would imply convergence of its later iterate a. Any hypothetical
positive counterexample eventually has an iterate not divisible by three:
remove its finite initial halving run, and if the resulting odd value is
divisible by three its next shortcut iterate is not. Hence restricting
attention to exceptional components does not restore uniformly small
fibre multiplicities. This supplements, rather than replaces, section 17's
stronger generic worst-case exponential rate.

Uniformly sampling L_h(a) gives `H(X)=h` bits, while `U^(6h)(X)=a` is
constant. Thus `H(X | U^(6h)(X))=h` exactly. This elementary entropy
corollary is written, not formalized. It concerns endpoint collisions,
not the self-similar paper's equality of complete maps. The construction
also works in the known basin of 1, so large inverse trees alone cannot
give a contradiction or supply a lower bound for one forward orbit.

The [independent replay](verify_uniform_inverse_branching.py) derives
children from exponents rather than copying the table, checks 6,679
roots, and checks 36,846 leaves across 18 trees at depths 0–10,
including roots with more than 1,024 bits. Running the script also builds
all three Lean modules from source into a fresh temporary directory.
[Manifest and scope](results/uniform-inverse-branching/verification.json).
Both nontrivial cycles and divergence remain unresolved.

## 20. Every unit-root basin meets every mixed residue cylinder

Before searching for a scale-dependent trapping certificate, we checked
what fixed residue information can distinguish. The following is a
**written theorem**, with its arithmetic transport lemmas kernel checked
separately. No novelty claim is made.

**Theorem.** Fix a positive integer a with `3∤a`. For every A,B≥0,
every residue r modulo `M=2^A*3^B`, and every height H, there is an
integer N>H such that
\[
 N\equiv r\pmod M,\qquad U^t(N)=a\quad\text{for some }t\ge0.
\]
Thus each such inverse basin has infinitely many members in every mixed
residue class. This is topological density in the congruence sense, not
positive natural density or an interval-count estimate.

### Elementary power lifting

For every J≥1 the powers of two run through all units modulo `3^J`.
Here is an explicit proof, so no unverified external input is needed.
Inductively,
\[
 4^{3^s}=1+3^{s+1}c_s,\qquad c_s\equiv1\pmod3.
\]
The base has c_0=1. Cubing gives
\[
 c_{s+1}=c_s+3^{s+1}c_s^2+3^{2s+1}c_s^3,
\]
which preserves the congruence. Put `T_J=2*3^(J-1)`. Then
\[
 2^{T_J}\equiv1+3^J c_{J-1}\pmod{3^{J+1}}.
\]
Suppose `a*2^e≡y (mod 3^J)` with a,y units. The three candidates
`e+d*T_J`, d=0,1,2, give all three lifts of this residue modulo
`3^(J+1)`, since their difference coefficients
`a*2^e*c_(J-1)` are units modulo three. Start with e=0 or 1 modulo
three, and choose the unique lift at each stage. This proves that some
`0≤e<T_J` satisfies `a*2^e≡y (mod 3^J)`.
Also `2^T_J≡1 (mod 3^J)`, so adding arbitrary multiples of T_J to e
preserves the congruence while making `a*2^e` arbitrarily large.

### Constructing the ancestor

Choose any positive representative n of r modulo M, and choose k≥A
with `n<2^k`. Let `j=wt(k,n)` and `y=U^k(n)`.
There must be an odd step among these k steps: otherwise `2^k` would
divide the positive integer n<2^k. Thus j≥1. An odd shortcut step
ends at a unit modulo three, and all subsequent steps preserve that
property, so `3∤y`.

Apply power lifting at J=j+B and choose e sufficiently large that
\[
 Q=\frac{a2^e-y}{3^{j+B}}
\]
is a positive integer. Define
\[
 N=2^k3^B Q+n.
\]
Then N≡r modulo M, and the affine identity gives
\[
 U^k(N)=3^j(3^BQ)+y=a2^e,\qquad U^{k+e}(N)=a.
\]
Taking larger exponents in the same progression makes N arbitrarily
large, proving the theorem. In fact N has exactly the same first k
parity bits as n, since N≡n modulo `2^k`. The construction can preserve
any prescribed finite parity prefix while directing the later orbit to
any prescribed positive unit root.

[BasinResidueShadow.lean](lean/BasinResidueShadow.lean) kernel-proves
unit preservation, the unit endpoint after a positive-weight prefix,
the displayed endpoint and residue identities **given the power
equality**, preservation of the prefix weight, and transport into a
forward-closed set containing the cylinder. It does not formalize the
universal power-lifting existence argument above; no such assertion is
hidden in an axiom or admitted proof. Its printed dependencies are only
`propext` and `Quot.sound`.

### A one-class convergence criterion, and its limitation

Fix any A,B,r and any H. The assertion
\[
 \text{every }N>H\text{ with }N\equiv r\pmod{2^A3^B}
 \text{ eventually reaches 1}
\]
is equivalent to the full positive-integer Collatz conjecture.
The forward implication follows by constructing, for each positive
unit root a, such an N with a later iterate equal to a. A later iterate
of a convergent orbit also converges: if it occurs after the first visit
to 1 it is already in the shortcut cycle `{1,2}`. Every positive start
has a unit iterate, since its finite initial halving run reaches an odd
integer and the next odd step, if needed, reaches a unit. Therefore all
positive starts converge. The converse is immediate.

Equivalently, if even one positive counterexample exists, it has a unit
iterate a. The theorem supplies nonconvergent ancestors of a in every
mixed residue class and above every height. Taking a=1 supplies
convergent starts there as well. Fixed congruence information alone
cannot separate these two possible outcomes, even after finitely many
exceptions are removed. This does not prohibit residue-based **descent**
certificates: those establish progress to a smaller positive integer,
not unconditional convergence of an entire class.

This gives a potential sufficient target—a whole tail of one favorable
residue class—but does not establish it. In particular, topological
density cannot replace the missing quantitative estimate. The lifted
exponent can be comparable to `3^(j+B)`, and the resulting ancestor
can be far larger than the root. It need not contradict a least
counterexample or meet an absorbing region. A useful scale-dependent
certificate must supply size control or strict progress in addition to
residue compatibility; the construction does not rule out such a
certificate.

The [independent replay](verify_basin_residue_shadow.py) constructs
3,276 ancestors across all classes with 0≤A≤5 and 0≤B≤2, for four
unit roots including `2^128+1`. It checks exact parity prefixes, residues,
and the endpoint before the pure-halving tail. It also checks 2,184
power lifts exhaustively through modulus `3^6`. The largest constructed
ancestor has 39,098 bits. No assumption about convergence of the chosen
targets enters these checks. Three fresh Lean builds pass.
[Verification scope and hashes](results/basin-residue-shadow/verification.json).
The universal density and one-class equivalence remain written results.
Collatz itself and a quantitative trapping certificate remain unresolved.
