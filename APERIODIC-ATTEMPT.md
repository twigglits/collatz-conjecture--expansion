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
