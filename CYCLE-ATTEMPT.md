# Cycle minima and reciprocal packing

Every positive primitive Collatz cycle obeys a reciprocal bound depending only
on its minimum, independently of its period. Combining that bound with the
cycle product identity gives the restriction (12) below. This strengthens the
elementary period-dependent estimate in one regime, but it does not exclude
all nontrivial cycles. Section 5 identifies the remaining gap explicitly.

These are written mathematical proofs, **not Lean certificates**. The exact
affine identity used here is formalized in
[`CollatzAffine.lean`](CollatzAffine.lean); the counting and real-analysis
arguments below have not been formalized. No numerical search or benchmark is
used, and no claim of novelty is made.

## 1. The cycle product and the correct injectivity hypothesis

Use the shortcut map

\[
 U(n)=\begin{cases}(3n+1)/2,&n\text{ odd},\\n/2,&n\text{ even}.
 \end{cases}
\]

Let \(C\) be the set of distinct values in one primitive positive cycle, and
let \(O\subset C\) be its odd members. Write these in cyclic order as
\(n_0,\ldots,n_{k-1}\), with \(k\ge1\), and put

\[
 m=\min C=\min O,\qquad
 2^{h_i}n_{i+1}=3n_i+1,\qquad
 H=\sum_{i=0}^{k-1}h_i.
\]

Indices are cyclic and each \(h_i\ge1\) is the exact halving exponent.
The minimum is odd because an even minimum would immediately decrease.
Multiplying the equations and cancelling the product of the \(n_i\) gives

\[
 \Lambda:=H\log2-k\log3
   =\sum_{n\in O}\log\left(1+\frac1{3n}\right)>0.
 \tag{1}
\]

All logarithms without a base are natural. Since \(m\in O\),

\[
 \log\left(1+\frac1{3m}\right)
 \le\Lambda
 <\frac13\sum_{n\in O}\frac1n
 \le\frac{k}{3m}.
 \tag{2}
\]

The orbit-packing argument in
[`APERIODIC-ATTEMPT.md`](APERIODIC-ATTEMPT.md) requires injectivity of every
fixed iterate on the set being counted. It does not require that the set be
infinite: \(U\) permutes \(C\), so every \(U^\ell\) is injective on
\(C\), and therefore on \(O\). We always count distinct members of one
primitive cycle, not repetitions of a period.

Moreover, no member of \(C\) is divisible by three. Every odd-to-odd step
has \(2^{h_i}n_{i+1}=3n_i+1\), so its odd endpoint is not divisible by
three. Every intervening even member is a power of two times that endpoint.
These two facts permit sharper counting constants for cycles.

The use of products, cycle minima, continued fractions, and linear forms in
logarithms is established in the literature; see, for example,
[Simons–de Weger, *Theoretical and computational bounds for m-cycles of the
3n+1 problem*, §§2–5](https://deweger.net/papers/%5B35a%5DSidW-3n%2B1-v1.44%5B2010%5D.pdf).
Their parameter called \(m\) counts local minima and is different from the
minimum value \(m\) used in this note.

## 2. A finite affine packing bound for odd cycle members

Fix \(\ell\ge1\), and write an input in an aligned block as
\(q2^\ell+s\), where \(0\le s<2^\ell\). If its first \(\ell\)
shortcut steps contain \(j\) odd steps, the affine identity is

\[
 U^\ell(q2^\ell+s)=3^j q+U^\ell(s).
 \tag{3}
\]

The first \(\ell\) parities depend only on \(s\). There is exactly one
residue for each parity word: after fixing a word of length \(t\), its two
lifts modulo \(2^{t+1}\) have \(t\)-th iterates differing by the odd
number \(3^{j_t}\), and hence have different next parities. Consequently,
the number of **odd** residues with weight \(j\) is
\(\binom{\ell-1}{j-1}\), for \(1\le j\le\ell\).

We also have the sharper small-image estimate

\[
 0\le U^\ell(s)\le3^j-1.
 \tag{4}
\]

Here is a proof that retains the strict integer endpoint. For
\(0\le i\le\ell\), set

\[
 y_i=U^i(s),\qquad
 E_i=3^{j_i}2^{\ell-i},\qquad d_i=E_i-y_i,
\]

where \(j_i\) counts odd steps before time \(i\). Initially
\(d_0=2^\ell-s\ge1\). For \(i<\ell\), \(E_i\) is even, so
\(d_i\) has the same parity as \(y_i\). If \(y_i\) is even then
\(d_{i+1}=d_i/2\ge1\), since \(d_i\) is a positive even integer.
If \(y_i\) is odd then \(d_{i+1}=(3d_i-1)/2\ge1\), since \(d_i\)
is a positive odd integer. Thus \(d_\ell\ge1\), proving (4).

For a fixed weight \(j\), equations (3)–(4) put all images in

\[
 [3^jq,\,3^j(q+1)).
\]

This integer interval contains exactly \(2\cdot3^{j-1}\) numbers not
divisible by three. The images of the cycle members being counted are
distinct members of \(C\), so there can be at most that many inputs of
weight \(j\). Combining this with the residue count gives the finite bound

\[
 \#\bigl(O\cap[q2^\ell,(q+1)2^\ell)\bigr)
 \le D_\ell:=
 \sum_{j=1}^{\ell}
 \min\left\{\binom{\ell-1}{j-1},\,2\cdot3^{j-1}\right\}.
 \tag{5}
\]

Formula (5) is an exact finite expression for a proved upper bound, not a
claim that the upper bound is attained. It can be used directly when sharper
constants matter. The next section uses a looser expression with a closed
geometric sum.

## 3. Explicit bounds on geometric blocks

Put

\[
 \lambda=\frac{3125}{108},\qquad
 \rho=\frac{27}{32},\qquad
 \sigma=\frac{\lambda}{32}=\frac{3125}{3456}.
\]

Take \(\ell=5r\), \(r\ge1\), and split (5) before weight \(3r\).
The weights \(1\le j<3r\) contribute at most

\[
 \sum_{j=1}^{3r-1}2\cdot3^{j-1}
 =3^{3r-1}-1=\frac{27^r}{3}-1.
\]

For the remaining weights, put \(t=3/2\). Since \(t^j\ge t^{3r}\)
when \(j\ge3r\), the binomial theorem gives

\[
\begin{aligned}
 \sum_{j=3r}^{5r}\binom{5r-1}{j-1}
 &\le t^{-3r}\sum_{j=1}^{5r}\binom{5r-1}{j-1}t^j\\
 &=t^{1-3r}(1+t)^{5r-1}
 =\frac35\left(\frac{3125}{108}\right)^r.
\end{aligned}
\]

Thus every aligned block of length \(32^r\) satisfies

\[
 \boxed{\quad
 \#\bigl(O\cap[q32^r,(q+1)32^r)\bigr)
 \le B_r:=\frac{27^r}{3}-1+\frac35\lambda^r
 \quad(r\ge1).
 \quad}
 \tag{6}
\]

An arbitrary interval of the same length meets at most two aligned blocks,
so \(2B_r\) is also valid there. For the minimum-sensitive reciprocal
bound below, blocks aligned at zero suffice, avoiding this extra factor.

## 4. Finite shells and a period-independent minimum bound

Let

\[
 R=\lfloor\log_{32}m\rfloor,\qquad
 32^R\le m<32^{R+1},\qquad
 N(t)=\#\{n\in O:n\le t\}.
\]

Since \(O\) is finite and all its members are at least \(m\), summing
the elementary identity \(1/n=\int_n^\infty t^{-2}\,dt\) gives

\[
 S:=\sum_{n\in O}\frac1n
   =\int_m^\infty\frac{N(t)}{t^2}\,dt
   =\int_{32^R}^\infty\frac{N(t)}{t^2}\,dt.
 \tag{7}
\]

For \(32^r\le t<32^{r+1}\), (6) gives \(N(t)\le B_{r+1}\).
Also \(N(t)\le k\) everywhere. Hence for every integer \(J\ge R\),

\[
 S\le\frac{31}{32}\sum_{r=R}^{J}\frac{B_{r+1}}{32^r}
      +\frac{k}{32^{J+1}}.
 \tag{8}
\]

This finite-shell inequality needs no bound on the largest cycle member.
The last term bounds the entire remaining tail, including any members beyond
the chosen cutoff. With \(L=J-R+1\), its geometric terms evaluate exactly
to

\[
\begin{aligned}
 S\le{}&\frac{279}{5}\rho^R(1-\rho^L)
       +\frac{58125}{331}\sigma^R(1-\sigma^L)\\
      &-32^{-R}(1-32^{-L})+\frac{k}{32^{J+1}}.
\end{aligned}
 \tag{9}
\]

For clarity, the arithmetic follows by substituting
\(B_{r+1}/32^r=9\rho^r-32^{-r}+(625/36)\sigma^r\)
into (8). Both \(\rho\) and \(\sigma\) lie strictly between zero and
one. Letting \(J\to\infty\), with the finite cycle and its \(k\) fixed,
proves

\[
 \boxed{\quad
 S\le G_R:=\frac{279}{5}\rho^R
           +\frac{58125}{331}\sigma^R-32^{-R}.
 \quad}
 \tag{10}
\]

Combining (1)–(2) with (10), define

\[
 F_R:=\frac{G_R}{3}
 =\frac{93}{5}\rho^R+\frac{19375}{331}\sigma^R
   -\frac13\,32^{-R}.
 \tag{11}
\]

Every positive primitive cycle therefore satisfies

\[
 \boxed{\quad
 \log\left(1+\frac1{3m}\right)
 \le H\log2-k\log3
 <\min\left\{\frac{k}{3m},\ F_R\right\}.
 \quad}
 \tag{12}
\]

In particular, set

\[
 \delta=\log_{32}\!\left(\frac{3456}{3125}\right)>0,
 \qquad
 C_0=\left(\frac{93}{5}+\frac{19375}{331}\right)
      \frac{3456}{3125}.
\]

Since \(\rho<\sigma<1\) and \(32^R>m/32\),

\[
 0< H\log2-k\log3 < F_R < C_0m^{-\delta}.
 \tag{13}
\]

This bound tends to zero with the minimum regardless of the number of odd
members. At a fixed minimum it improves \(k/(3m)\) whenever
\(k>3mF_R\); for other parameter ranges the elementary bound may be much
better. The constants are deliberately conservative, so (13) should not be
interpreted as a competitive numerical cycle-exclusion record.

## 5. Why this does not force the trivial cycle

The obstruction cannot be removed by saying that \(\log_2 3\) is
irrational. Irrationality excludes equality of the two powers but provides
no uniform positive separation between \(H\log2\) and \(k\log3\).
It is also insufficient just to cite convergents with gaps tending to zero:
for a fixed minimum, the positive lower bound in (12) must be respected.

There is a direct test of the scalar-inequality route. Write
\(a_m=\log(1+1/(3m))\). Since \(0<\delta<1\), (11) implies
\(F_R/a_m\to\infty\) as \(m\to\infty\), while \(F_R\to0\).
Indeed, \((93/5)\rho^R-(1/3)32^{-R}>0\), so
\(F_R\ge(19375/331)\sigma^R\ge(19375/331)m^{-\delta}\), whereas
\(a_m<1/(3m)\). Thus for any sufficiently large integer \(m\) we can choose

\[
 a_m<a<b<\min\{F_R,\log2\}.
\]

Put \(\alpha=\log_2 3\). The fractional parts of \(k\alpha\) are dense
in \([0,1]\), and visit every open subinterval infinitely often. Hence
infinitely many positive integers \(k\), with
\(H=\lceil k\alpha\rceil\), satisfy

\[
 a<(H-k\alpha)\log2<b.
\]

Taking these \(k\) sufficiently large also ensures
\(b<k/(3m)\). These integer parameter pairs satisfy all the scalar bounds
in (12), including its lower bound. One may restrict \(m\) to arbitrarily
large allowed congruence classes without changing this argument.

This establishes compatibility of the inequalities, **not existence of a
cycle**. The missing arithmetic involves the order of the halving exponents.
With \(H_i=\sum_{j<i}h_j\), \(H_0=0\), and the cycle starting at its
minimum, the exact affine equation additionally requires

\[
 m(2^H-3^k)
 =\sum_{i=0}^{k-1}3^{k-1-i}2^{H_i}.
 \tag{14}
\]

Every intermediate value must be a positive odd integer, every \(h_i\)
must be its exact valuation, and the completed orbit must be primitive.
None of these ordered divisibility conditions follows from (12).
The schedule-uniqueness results in
[`CollatzPeriodic.lean`](CollatzPeriodic.lean) constrain a fixed schedule;
they do not show that every nontrivial schedule lacks an integer realization.

Linear-form lower bounds are useful when combined with additional cycle
structure, as in the cited Simons–de Weger work. Abstractly, a lower bound
\(\Lambda\ge c k^{-A}\) combined with (13) would imply only
\(m<(C_0/c)^{1/\delta}k^{A/\delta}\). Such a relation is not a
contradiction for unbounded \(k\).

Finally, a minimum of an arbitrary nontrivial cycle is not automatically the
least positive counterexample among all initial integers: smaller values can
feed that cycle. Thus least-counterexample predecessor restrictions from
[`CollatzContradiction.lean`](CollatzContradiction.lean) cannot be imported
for every cycle minimum. Restrictions that do follow directly are that a
nontrivial cycle minimum is odd, is not divisible by three, and is
\(3\pmod4\): if it were \(1\pmod4\), its next odd value would be at
most \((3m+1)/4<m\). Consequently \(m\equiv7\) or \(11\pmod{12}\).
These elementary restrictions still leave the scalar compatibility argument
above intact.

The result of this attempt is the universal necessary condition (12) and its
explicit finite-shell precursor (9). Excluding all ordered integer
realizations in (14), or otherwise obtaining a contradiction for every
nontrivial cycle, remains unresolved.
