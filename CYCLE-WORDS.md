# Ordered cycle words and a fixed divisibility obstruction

For a fixed nonempty halving block \(w\) and fixed connector \(v\), the
integer cycle condition for \(w^r v\) forces its growing denominator to
divide one integer \(K\) independent of \(r\). If \(K\ne0\), only
finitely many repetition counts can work. If \(K=0\), the block \(w\)
already closes, so the longer word cannot be a primitive cycle.

The same obstruction gives a further restriction for words whose halving
exponents are all 1 or 2. If there are \(q\) occurrences of 1 and \(R\)
occurrences of 2, then \(R=O(q^2)\), with explicit bounds below. Direct
applications exclude **all** words in this alphabet with \(q=1,2,3\),
regardless of the number or placement of the 2s. Thus a nontrivial cycle
using this alphabet would need at least four occurrences of 1. This is a
restricted-family result, not a claim about cycles with larger halving
exponents, and no novelty claim is made.

The finite centered algebra, cancellation, denominator bound, and
zero-obstruction conclusion are kernel checked in
[`CollatzCycleBlocks.lean`](CollatzCycleBlocks.lean). Its hypotheses are
explicit affine recurrences and coprimality conditions. The word
specializations, analytic estimates, complexity bound, and family exclusions
in this note are written proofs, **not separately Lean-certified theorems**.
No exhaustive integer-range search or timing claim is used here.

## 1. The ordered divisibility condition is a complete cycle test

For a nonempty positive halving word \(h=(h_0,\ldots,h_{k-1})\), with every
\(h_i\ge1\), put

\[
 H_i=\sum_{j<i}h_j,\qquad H=H_k,\qquad
 W(h)=\sum_{i=0}^{k-1}3^{k-1-i}2^{H_i},\qquad
 D(h)=2^H-3^k.
 \tag{1}
\]

The prescribed accelerated steps are
\(2^{h_i}n_{i+1}=3n_i+1\). Their affine composition has the form

\[
 F_h(x)=\frac{3^k x+W(h)}{2^H}.
\]

Consequently a positive integer cycle following the word requires
\(D(h)>0\) and \(D(h)\mid W(h)\). These conditions are also
**sufficient for a positive integer cycle**, though it need not be primitive.

To verify sufficiency without presuming that intermediate values are
integral, let \(W_i\) denote (1) for the cyclic rotation starting at
\(h_i\). Every \(W_i\) is positive and odd, and direct expansion gives

\[
 2^{h_i}W_{i+1}=3W_i+D,
 \tag{2}
\]

where \(D=D(h)\) is unchanged by rotation. This \(D\) is odd and is
not divisible by three. If \(D\mid W_i\), equation (2) and
\(\gcd(D,2)=1\) imply \(D\mid W_{i+1}\). Thus all
\(n_i=W_i/D\) are positive odd integers and obey the required step
equations. Since \(n_{i+1}\) is odd, each \(h_i\) is the exact
halving exponent. This proves sufficiency and explains why the order in
\(W(h)\), rather than merely \((H,k)\), matters.

Affine coding of rational cycles and its compatibility with parity are
established tools; compare
[Halbeisen–Hungerbühler, *Optimal bounds for the length of rational Collatz
cycles*, §2, Lemmas 1–2](https://people.math.ethz.ch/~halorenz/publications/pdf/collatz.pdf).
Our notation uses accelerated odd-to-odd steps rather than their shortcut
parity symbols. No historical numerical bound from that paper is being used.

## 2. A repeated block leaves a fixed obstruction

Fix a nonempty word \(w\), and a possibly empty word \(v\), with affine
maps

\[
 F_w(x)=\frac{ax+b}{d},\qquad
 F_v(x)=\frac{cx+e}{f}.
\]

If \(w\) has \(p\) symbols and total halving exponent \(s\), then
\(a=3^p\), \(d=2^s\), and \(b=W(w)>0\). Similarly, for \(v\),
\(c=3^t\), \(f=2^u\), and \(e=W(v)\). For an empty connector use
\(c=f=1,e=0\). Set

\[
 L=d-a\ne0,\qquad
 z(x)=Lx-b,\qquad
 K=b(c-f)+eL.
 \tag{3}
\]

The centered recurrence is homogeneous:

\[
 d\,z(F_w(x))=a\,z(x).
\]

Suppose a cycle follows \(w^r v\), \(r\ge1\), and write \(x_j\)
for its value after \(j\) copies of \(w\). Repetition and closure give

\[
 d^r z(x_r)=a^r z(x_0),\qquad
 fz(x_0)=cz(x_r)+K.
\]

Eliminating \(z(x_r)\) yields

\[
 \boxed{\quad
 D_r z(x_0)=K d^r,\qquad
 D_r=f d^r-c a^r.
 \quad}
 \tag{4}
\]

Here \(D_r\) is exactly the denominator \(D(w^r v)\), so it is positive
for a positive cycle, and is coprime to both two and three. Since \(d\)
is a power of two, cancellation in (4) proves

\[
 \boxed{\qquad D_r\mid K.\qquad}
 \tag{5}
\]

In particular, if \(K\ne0\),

\[
 1\le D_r\le |K|.
 \tag{6}
\]

One may remove all factors of two and three from \(|K|\) before using
this bound, because \(D_r\) is coprime to six. Equation (5) is only a
necessary condition in this generality; surviving candidates must still pass
the full \(D_r\mid W(w^r v)\) test.

For comparison with a direct numerator calculation, define

\[
 T_r=\sum_{j=0}^{r-1}d^{r-1-j}a^j
     =\frac{d^r-a^r}{d-a}.
\]

Then \(W(w^r v)=cbT_r+ed^r\), and the elimination identity is

\[
 (d-a)W(w^r v)=bD_r+Kd^r.
\]

This provides a second direct derivation of (5). The centered form has the
advantage of using only finite recurrences and no division, which is the form
formalized in `repeated_block_obstruction` and
`collatz_block_divisibility` in the linked Lean file.

## 3. A finite theorem for every fixed block and connector

If \(K=0\), (4) and \(D_r>0\) give \(z(x_0)=0\), hence
\(dx_0=ax_0+b\). Thus \(F_w(x_0)=x_0\). The shorter block already
returns to the initial integer, with the same valid intermediate steps.
Whenever the whole word is longer than \(w\), it cannot describe a
primitive cycle. If \(d<a\), its putative fixed point \(b/(d-a)\) is
negative, so there is no positive realization at all.

Now suppose \(K\ne0\).

If \(d<a\), positivity of \(D_r\) requires
\((a/d)^r<f/c\), leaving finitely many \(r\) even before applying
divisibility.

If \(d>a\), let \(r_0\ge1\) be the first integer with \(D_{r_0}>0\).
It exists, and later denominators obey

\[
 D_{r+1}=dD_r+c(d-a)a^r>dD_r\qquad(r\ge r_0).
\]

Therefore every candidate satisfies

\[
 d^{r-r_0}D_{r_0}\le |K|.
 \tag{7}
\]

If \(D_{r_0}>|K|\), there are no candidates. Otherwise, a convenient
explicit upper bound is

\[
 r\le r_0+
 \left\lfloor\log_d\left(\frac{|K|}{D_{r_0}}\right)\right\rfloor.
 \tag{8}
\]

The finitely many candidates can be filtered first by (5) and then by the
complete integer-cycle test of §1. All powers can be compared as exact
integers; logarithmic approximation is unnecessary for implementing the
bound. This is an effective finite reduction for each fixed \((w,v)\),
not a uniform bound when the connector is allowed to grow with \(r\).

## 4. Repetition also costs integer spacing

There is a complementary consequence of the parity-collision lemma.
Suppose two odd integers \(x,y\) follow the same halving word of length
\(\ell\) and total exponent \(S\), ending at odd integers \(x',y'\).
Subtracting their affine equations gives

\[
 2^S(x'-y')=3^\ell(x-y).
\]

Since \(x'-y'\) is even and \(3^\ell\) is odd,

\[
 2^{S+1}\mid x-y.
 \tag{9}
\]

Distinct starting values therefore differ by at least \(2^{S+1}\).
The extra factor of two uses the fact that the terminal value, as well as
every starting value, is odd.

For the repeated block in §2, integrality of the centered recurrence gives
\(d^r\mid z(x_0)\). Write \(z(x_0)=d^r t\); then
\(z(x_r)=a^r t\). Since \(L\), \(b\), and \(x_r\) are odd,
\(z(x_r)=Lx_r-b\) is even. Thus \(t\) is even. Unless \(w\) already
closes the cycle, \(t\ne0\), so

\[
 |(d-a)x_0-b|\ge2d^r.
 \tag{10}
\]

The same result follows from (9): consecutive block boundaries share the
prefix \(w^{r-1}\), and their distance is \(|z(x_0)|/d\).

If a contracting block \(d>a\) begins at the minimum \(m\) of a
primitive cycle and is a proper part of its period, its next boundary cannot
be smaller. Consequently \((d-a)m-b<0\); equality would already close
the block. Equation (10) then gives the explicit repetition cap

\[
 2d^r\le b-(d-a)m\le b-(d-a).
 \tag{11}
\]

For a general height-dependent complexity statement, let a primitive cycle
have \(k\) odd members, minimum \(m\), maximum odd member \(M\), and
let \(p_C(\ell)\) count its distinct cyclic halving factors of length
\(\ell\). Each such factor has \(S\ge\ell\). By (9), at most
\(\lfloor(M-m)/2^{\ell+1}\rfloor+1\) positions can carry the same
factor, hence

\[
 p_C(\ell)\ge
 \left\lceil
 \frac{k}{\lfloor(M-m)/2^{\ell+1}\rfloor+1}
 \right\rceil.
 \tag{12}
\]

In particular, if \(2^{\ell+1}>M-m\), all \(k\) cyclic factors of that
length are distinct. This is a genuine spacing restriction, but it permits
long repetitions when the cycle's values are sufficiently large.

## 5. Few occurrences of 1 among halving exponents 1 and 2

Now restrict to a nontrivial positive cycle with every \(h_i\in\{1,2\}\).
Let \(q\) count the 1s and \(R\) count the 2s. All cycle values exceed
one. If \(q=0\), every step is \(F_2(x)=(3x+1)/4\), whose only
periodic real point is 1; this gives only the trivial accelerated cycle.
Thus \(q\ge1\). Positivity of the full denominator also requires
\(R\ge1\).

There are \(q\) cyclic gaps of 2s between the 1s, allowing empty gaps.
Choose a longest gap of length \(r\ge\lceil R/q\rceil\), rotate the
word to begin there, and apply (5) with

\[
 w=(2),\qquad a=3,\quad b=1,\quad d=4,\quad L=1.
\]

The connector contains \(q\) occurrences of 1 and \(R-r\) occurrences
of 2. Its coefficients are

\[
 c=3^{q+R-r},\qquad f=2^q4^{R-r},\qquad K=c-f+e.
\]

The full denominator and its slope are

\[
 D=2^q4^R-3^{q+R}=2^q4^R(1-A),\qquad
 A=\left(\frac32\right)^q\left(\frac34\right)^R<1.
 \tag{13}
\]

Equation (4), now centered at 1, reads
\(D(x_0-1)=K4^r\). Therefore \(K>0\) and \(D\le K\).

There is a bound on \(K\) using only the symbol counts of the connector.
In the centered coordinate \(y=x-1\), a symbol 1 sends
\(y\mapsto(3y+2)/2\), and a symbol 2 sends \(y\mapsto3y/4\).
Starting at \(y=0\), all values remain nonnegative. Removing the
contractions associated with the 2s can only increase the terminal value.
Thus

\[
 \frac{K}{f}=F_v(1)-1
 \le 2\left(\left(\frac32\right)^q-1\right),
\]

or equivalently,

\[
 0<K\le2(3^q-2^q)4^{R-r}.
 \tag{14}
\]

Combining \(D\le K\) with (13)–(14) proves

\[
 4^r(1-A)\le2\left(\left(\frac32\right)^q-1\right).
 \tag{15}
\]

If \(A>1/2\), its definition immediately gives

\[
 R<\frac{q\log(3/2)+\log2}{\log(4/3)}.
\]

If \(A\le1/2\), (15) gives
\(4^r<4(3/2)^q\), hence
\(r<1+q\log_4(3/2)\). Since \(R\le qr\), the two cases yield

\[
 \boxed{\quad
 R<\max\left\{
 \frac{q\log(3/2)+\log2}{\log(4/3)},\quad
 q+q^2\log_4(3/2)
 \right\}.
 \quad}
 \tag{16}
\]

There are therefore only finitely many candidate cyclic words in this
alphabet for every fixed \(q\). Along any hypothetical sequence of such
cycles with unbounded length \(k=q+R\), the number \(q\) must be
\(\Omega(\sqrt{k})\). This consequence comes from integrality and the
ordered repetition obstruction; the scalar requirement \(A<1\) alone
only gives a lower bound on \(R\).

## 6. Complete exclusions for one, two, or three occurrences of 1

The following arguments use (5), (13), and (14), with a few small constants
displayed explicitly. They do not assume a finite upper bound on \(R\).
Once \(D_R=2^q4^R-3^{q+R}\) becomes positive, the recurrence
\(D_{R+1}=4D_R+3^{q+R}\) shows that it increases.

**One occurrence.** The word is cyclically \((2)^R(1)\). Here
\(K=2\) and \(D_R=2\cdot4^R-3^{R+1}\). For \(R=0,1\),
\(D_R<0\); at \(R=2\), \(D_R=5\). Hence every positive denominator
is at least 5 and cannot divide 2. No such cycle exists.

**Two occurrences.** Positivity requires \(R\ge3\): at \(R=2\),
\(D_R=4\cdot16-9\cdot9=-17\), and the ratio
\(4-9(3/4)^R\) is increasing. For \(R\ge4\), a longest gap has
\(r\ge2\), so

\[
 \frac{D_R}{4^R}\ge\frac{295}{256}
   >\frac{10}{16}\ge\frac{K}{4^R},
\]

contradicting \(D_R\le K\). At \(R=3\), \(D_R=13\), and the two
gaps, up to cyclic rotation, are either \((3,0)\) or \((2,1)\).
For \((3,0)\), choose the length-three gap; the connector is \((1,1)\)
and \(K=10<13\). For \((2,1)\), the connector is \((1,2,1)\),
whose coefficients are \(c=27,f=16,e=23\), so \(K=34\).
But \(13\nmid34\). Both possibilities are excluded.

**Three occurrences.** Positivity requires \(R\ge5\): at \(R=4\),
\(D_R=8\cdot256-27\cdot81=-139\). For \(R\ge6\), a longest gap
has \(r\ge2\), and

\[
 \frac{D_R}{4^R}\ge\frac{13085}{4096}
   >\frac{38}{16}\ge\frac{K}{4^R}.
\]

At \(R=5\), \(D_R=1631\). If a gap has length at least three, (14)
gives \(K\le38\cdot4^2=608<1631\). Otherwise the three gaps are
\((2,2,1)\), up to cyclic rotation. Choose a length-two gap with connector

\[
 v=(1,2,2,1,2,1).
\]

It has \(c=729,f=512\), and its numerator is

\[
 e=243+162+216+288+192+256=1357.
\]

Thus \(K=729-512+1357=1574<1631\), another contradiction.
Every case is excluded.

These prove that a nontrivial positive cycle with only exponents 1 and 2,
if one exists, has at least four occurrences of 1. They do not exclude all
words over this alphabet.

## 7. The remaining gap

The fixed-connector theorem is substantially stronger than just comparing
\(2^H\) and \(3^k\), because it uses the actual order of the halving
blocks. Its limitation is equally specific: when both the connector and the
number of defects grow, the obstruction \(K\) grows as well. The argument
does not give a uniform upper bound for every cyclic word.

Likewise, (16) permits infinitely many count pairs. For example, choose
\(R=2q\). Then \(A=(27/32)^q<1\), and for all sufficiently large
\(q\), the quadratic alternative in (16) exceeds \(2q\). Thus these
count pairs satisfy both the positive-slope condition and our necessary
count bound. This does not claim that any corresponding ordered word passes
\(D\mid W\). It shows why this reduced inequality cannot by itself
exclude the remaining families.

The spacing bound (12) also remains compatible with sufficiently large
cycle values. No argument here bounds all cycle heights or controls all
possible growing connectors. The results exclude explicit infinite word
families and impose quantitative repetition restrictions, while uniqueness
of the positive cycle remains unresolved.
