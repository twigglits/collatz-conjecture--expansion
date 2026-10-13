# Endpoint-height coupling on the actual source intervals

**Collatz remains unresolved.** The count-return estimates now yield
a bounded mean logarithmic separation of actual paired endpoints after
the available source bits have been exposed. An exact exponentially
small error connects this separation to the count gap. This is a real
height estimate on the specified integer intervals, not just a statement
about random 2-adic inputs. It does not control arbitrary later clocks.

[AnnulusHeightCoupling.lean](../lean/AnnulusHeightCoupling.lean) proves
twelve supporting integer identities and inequalities. Logarithms and
the consequences of the previous probability proof are written arguments.
The last section identifies the arithmetic progression retained by a
count return; replacing its average with an interval average remains open.

## 1. Normalize the two endpoint heights

For an integer \(t\ge1\), put \(N=2^t\), choose \(r\) uniformly
from \(0\le r<N/2\), and set
\[
 m=N+2r,\quad X=U^t(m),\quad Y=U^t(m+1),\quad
 a=a_t(m),\quad b=a_t(m+1).
\]
These are precisely the even/odd refinement pairs at level \(k=t-1\)
and offset zero. Both sources lie in \([N,2N)\).
Write their positive normalized heights as
\[
                            u=X/3^a,\qquad v=Y/3^b.
\]
The affine lift gives \(u,v\ge1\). Recall the nonnegative integer
correction and its previous exact full-period moment:
\[
 Q_t(n)=3^{t-a_t(n)}(2^tU^t(n)-3^{a_t(n)}n),\qquad
 2\sum_{0\le n<N}Q_t(n)+6^t=8^t.                    \tag{1}
\]
It is periodic modulo \(N\). Hence
\[
 u=\frac mN+\frac{Q_t(m)}{N3^t},\qquad
 v=\frac{m+1}N+\frac{Q_t(m+1)}{N3^t}.
\]
The kernel proves the individual cross-multiplied difference bound,
its transport to the actual annulus, and the even/odd sum. Using (1),
the written division gives the estimate
\[
 \begin{split}
 \mathbb E|u-v|
 &\le\frac1N+\frac{2}{N^2 3^t}\sum_{n<N}Q_t(n)\\
 &=\boxed{(2/3)^t}.                                  \tag{2}
 \end{split}
\]
The factor two is the reciprocal even-source fraction. In integer form,
with \(h_t(n)=3^{t-a_t(n)}U^t(n)\), the checked theorem is
\[
 2^{t+1}\sum_{r<N/2}|h_t(N+2r+1)-h_t(N+2r)|\le8^t.
\]
No stochastic return estimate or external theorem is needed for (2).

## 2. Logarithmic endpoint separation

Since \(u,v\ge1\), integrating \(1/z\le1\) between them gives
\(|\log u-\log v|\le|u-v|\). Consequently, with
\(L_t=\log(Y/X)\) and \(d_t=b-a\),
\[
             \boxed{\mathbb E|L_t-d_t\log3|\le(2/3)^t.}             \tag{3}
\]
This transfers the previous full count-gap moment to actual real heights.
Let \(C_*=2187414\,2^{454272}\), the explicit constant in the
[written count-return proof](COUNT-RETURN-CONTROL.md). Conditioning
that proof on the first input being even gives
\(\mathbb E|d_t|\le2C_*\). Therefore
\[
                   \mathbb E|L_t|\le2C_*\log3+(2/3)^t.              \tag{4}
\]

The signed count mean has a much smaller exact value. The kernel proves
\[
 \sum_{r<N/2}a_t(N+2r+1)
    =\sum_{r<N/2}a_t(N+2r)+N/2,
\]
so \(\mathbb E d_t=1\) for every \(t\). Equation (3) thus also gives
\[
               \boxed{|\mathbb E L_t-\log3|\le(2/3)^t.}             \tag{5}
\]
This signed mean does not tend to zero.

There is a useful equivalent threshold formulation. For \(z\in\mathbb R\),
let \(C_t(z)\) be the event that \(e^z\) lies between \(X\) and \(Y\),
using either convention at the endpoints. Layer-cake integration gives
\[
 \int_{\mathbb R}\Pr(C_t(z))\,dz
       =\mathbb E|\log Y-\log X|
       \le2C_*\log3+(2/3)^t.                          \tag{6}
\]
The signed integral of
\(\Pr(X\le e^z)-\Pr(Y\le e^z)\) equals \(\mathbb E L_t\).
Thus the total disagreement over *all height thresholds* has a uniform
bound. No monotonicity in height is asserted for actual future weights.

## 3. A limitation of the moment bound

Balanced pairs have \(L_t=0\). The previous written coalescence estimate,
conditioned on even input, implies
\[
                  \Pr(L_t\ne0)\le42C_*t^{-1/5}\longrightarrow0.
\]
Nevertheless, (5) implies
\(\liminf_t\mathbb E|L_t|\ge\log3\). Thus this family of actual
logarithmic height differences is **not uniformly integrable**. The
bounded first moment cannot be replaced by convergence in first mean.
This conclusion combines (3), the kernel signed-count identity, and the
previous written probability result; it is not a finite-data inference.

For each \(0<\theta<1\), Hölder's inequality does give
\[
 \mathbb E|L_t|^\theta
 \le(2C_*\log3+1)^\theta(42C_*)^{1-\theta}
              t^{-(1-\theta)/5}\longrightarrow0.       \tag{7}
\]
These statements are compatible: increasingly rare pairs can carry a
nonvanishing first moment. They do not give a lower bound on the actual
refinement energy.

## 4. A finite budget over all count returns

There is also a stronger consequence of the previous return drift that
can pay for separation-dependent errors. Let \(D_j\) be the separation
at return-cycle boundaries, start with \(D_0=1\), and absorb at zero.
Let \(N\) be the number of cycles until fusion and \(V(D)=D^{1/16}\).
The previous proof gives, for \(D>0\),
\[
 \mathbb E[V(D_{j+1})\mid D_j=D]
       \le(509/512)V(D)+6404.
\]
At zero both sides can instead be set to zero. Summing this inequality
through a deterministic truncation and using nonnegativity gives
\[
 \frac3{512}\mathbb E\sum_{j<\min(J,N)}V(D_j)
       \le1+6404\,\mathbb E\min(J,N).
\]
Monotone convergence and \(\mathbb EN\le C_*\) therefore prove
\[
 \boxed{\mathbb E\sum_{j<N}D_j^{1/16}
              \le\frac{512}3(1+6404C_*).}              \tag{8}
\]
Since \(\log(1+D)\le16D^{1/16}\), the total expected
\(\log(1+D_j)\) cost over all these returns is finite as well.
This is a written probability conclusion under the coherent binary law.
It is not asserted for a uniform sample from a finite integer interval
continued indefinitely after its source bits have been exhausted.

## 5. The exact arithmetic progression after a return

The distinction in the last sentence is material. Suppose the adjacent
sources \(r,r+1\) first return to equal counts at clock \(\tau\), with
common count \(a\) and endpoints \(x_0,y_0\). The earlier affine lift
gives, for every integer \(q\ge0\),
\[
 X(q)=U^\tau(2^\tau q+r)=3^a q+x_0,\qquad
 Y(q)=U^\tau(2^\tau q+r+1)=3^a q+y_0.                 \tag{9}
\]
For \(f_h(n)=3^{a_h(n)}/(2^hU^h(n))\), weight factorization gives
the exact identity for positive endpoints
\[
 f_{\tau+h}(2^\tau q+r)-f_{\tau+h}(2^\tau q+r+1)
       =\lambda\{f_h(X(q))-f_h(Y(q))\},
 \qquad\lambda=3^a/2^\tau.                            \tag{10}
\]

Take an actual source annulus \([A,2A)\), where \(A=2^K\) and
\(K\ge\tau\). For a fixed even residue \(r<2^\tau\),
\(q\) ranges from \(Q=A/2^\tau\) through \(2Q-1\). Set
\(M=3^aQ=\lambda A\), and
\(G_h(x)=f_h(x)-f_h(x+y_0-x_0)\), at the relevant positive arguments.
The contribution of this residue to the normalized squared difference is
\[
 A\lambda^2\sum_{q=Q}^{2Q-1}G_h(3^a q+x_0)^2
       =\lambda M\sum_{q=Q}^{2Q-1}G_h(3^a q+x_0)^2.     \tag{11}
\]
The endpoint sample is one arithmetic progression of spacing \(3^a\)
inside \([M+x_0,2M+x_0)\). Its spacing is not removed by the fact that
the unexposed *binary* input was Haar-uniform in the return proof.

If a bound of the form
\[
 3^a\sum_{q=Q}^{2Q-1}G_h(3^a q+x_0)^2
       \le C\sum_{x=M+x_0}^{2M+x_0-1}G_h(x)^2          \tag{12}
\]
were available for the actual weights, then (11) would carry the binary
branch factor \(C\lambda/3^a=C2^{-\tau}\). Without such averaging,
the trivial inclusion only gives the factor \(\lambda\), which is
larger by \(3^a\). Equation (12) is **not established here**. Nor is
it asserted sufficient by itself for bounded energy: control of the
shifted endpoint intervals, separations, and unreturned branches would
also be needed.

There is already a concrete bias in the actual weights. The even residue
\(r=200\) first returns at \(\tau=10\), with \(a=4\) and
\((x_0,y_0)=(17,16)\). With \(Q=1\), the progression samples just
\(X=98,Y=97\), while its containing interval is \(98\le x<179\).
At continuation clock \(h=128\), the independent exact replay gives
\[
 \frac{81\,[f_{128}(98)-f_{128}(97)]^2}
 {\sum_{x=98}^{178}[f_{128}(x)-f_{128}(x-1)]^2}
       =\frac{10453976883}{926254009}>11.              \tag{13}
\]
Every source from 97 through 178 is checked to have reached the known
cycle by this clock. Thus even a factor of eleven fails in this example
of (12). This does not disprove (12) with an arbitrary larger uniform
constant, and it concerns a different comparison from the earlier
whole-annulus parent-loss charge.

This is the exact location at which a proposed transfer of the return
budget (8) to actual weighted energy must account for a new sampling law.
The independent rational replay checks (9)--(11) on actual lifted orbits;
it does not silently replace a progression by an interval.

## 6. Reproduction and scope

Run `python3 verify_annulus_height_coupling.py`. The
[record](../results/annulus-height-coupling/verification.json) separates
the twelve new kernel roots, exact finite endpoint/count/transport checks,
and the written logarithmic and probability conclusions. The previous
count-return record is authenticated without rewriting it.

The new result supplies a uniform logarithmic height-coupling budget and
a separation-dependent return budget. It establishes neither the missing
progression estimate nor a uniform reversal-energy bound. Escape and
additional positive cycles remain unexcluded.
