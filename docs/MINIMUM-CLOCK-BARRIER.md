# An unbounded tail at the elementary logarithmic prefix clock

**Status: an all-index finite-prefix obstruction, with kernel proofs.
For every fixed floor and additive clock shift, the population minimum
tail mean at clock \(2\lfloor\log_2N\rfloor+L\) is unbounded in the cutoff.
This does not show that any orbit fails to converge. The actual
global-minimum budget and full Collatz remain unresolved.**

The [Green-kernel result](MINIMUM-GREEN-KERNEL.md) bounds the actual
global-minimum mean using a finite prefix at clock \(2\lfloor\log_2N\rfloor\).
That suggests increasing this clock by \(L\), then trying to make its
residual uniformly small as \(L\) grows. The present result rules out
that uniform approximation route, while retaining pointwise settling.

The obstruction is a whole residue class of the actual Collatz map,
not a comparison map. At
\[
 N=2^{5j+2L},\qquad T=L+2\log_2N=10j+5L,
\]
the kernel proves
\[
 \boxed{\frac1N\sum_{n\le N}m_T(n)\mathbf1_{\{m_T(n)>H\}}
          \ge 2^{j-1}}
 \quad\text{if }j\ge1,\ H<2^{4j+2L}-1.                    \tag{1}
\]
For each fixed \(H,L\), the right side tends to infinity. An additive
clock correction cannot make these prefix means uniformly less than one.
The old elementary upper bound, which also grows with \(N\), remains valid.

## 1. Exact ordinary growth and a halving buffer

Let \(C\) be the ordinary Collatz map and
\(m_t(n)=\min_{0\le s\le t}C^s(n)\). For \(K,q\ge1\), the source
\[
                         n=2^Kq-1
\]
has \(K\) initial odd shortcut steps. Their exact ordinary-clock formula is
\[
 C^{2i}(n)=2^{K-i}3^iq-1\quad(0\le i\le K),\qquad
 C^{2i+1}(n)=3C^{2i}(n)+1\quad(0\le i<K).                \tag{2}
\]
Every value in these first \(2K\) ordinary steps is at least \(n\).
The endpoint is \(3^Kq-1\).

At every positive integer, \(C(x)\ge x/2\). Thus an orbit starting at
least \(2^s n\) cannot fall below \(n\) within its next \(s\) ordinary
steps. In the kernel, this is a lower bound on the finite prefix minimum,
combined with the exact prefix-concatenation identity
\[
 m_{u+v}(n)=\min\{m_u(n),m_v(C^u(n))\}.                  \tag{3}
\]

Suppose \(T\ge2K\) and \(2^T\le6^K\). With \(s=T-2K\), this implies
\(2^{K+s}\le3^K\), so
\[
 3^Kq-1\ge 2^s(2^Kq-1).
\]
Equations (2)–(3) and the halving bound therefore prove
\[
 \boxed{m_T(2^Kq-1)=2^Kq-1\quad
       \text{whenever }q\ge1,\ 2^T\le6^K.}              \tag{4}
\]
If \(T<2K\), the same conclusion follows directly from the growing
prefix. The universal statement (4), including all intermediate
ordinary times and the additive minus-one terms, is kernel checked.
It is a finite-time statement only.

A useful integer specialization is
\[
                   m_{5b}(2^{2b}q-1)=2^{2b}q-1,         \tag{5}
\]
because \(2^{5b}=32^b\le36^b=6^{2b}\). This specialization needs
neither logarithms nor numerical approximations.

## 2. A whole residue class supplies the population lower bound

Suppose a period \(M\ge2\), a count \(Q\ge1\), and a clock \(T\) satisfy
\[
 m_T(Mq-1)=Mq-1\quad(1\le q\le Q),\qquad H<M-1.
\]
All \(Q\) sources lie in \([1,MQ]\) and are distinct. Nonnegativity of
the remaining summands gives
\[
 \sum_{n\le MQ}m_T(n)\mathbf1_{\{m_T(n)>H\}}
 \ge\sum_{q=1}^Q(Mq-1)=\frac{MQ(Q+1)}2-Q.
\]
Consequently
\[
 F_{H,T}(MQ):=\frac1{MQ}\sum_{n\le MQ}
       m_T(n)\mathbf1_{\{m_T(n)>H\}}
 \ge \frac{Q+1}2-\frac1M\ge\frac Q2.                    \tag{6}
\]
The residue embedding, arithmetic sum, and cross-multiplied bound
are kernel theorems. This is an infinite-family consequence, rather
than a finite sample extrapolation.

Now choose
\[
 b=2j+L,\quad M=2^{4j+2L}=2^{2b},\quad Q=2^j,\quad
 N=MQ=2^{5j+2L}.
\]
The adaptive clock is
\[
 T_L(N):=L+2\lfloor\log_2N\rfloor
        =10j+5L=5b.
\]
Apply (5)–(6) to obtain (1). In particular, the kernel proves both
\[
 \forall H,L,B\in\mathbb N,\quad
 \exists N>0:\quad F_{H,T_L(N)}(N)\ge B,                 \tag{7}
\]
and failure, for every \(H,L\), of the proposed strict budget
\[
 \sum_{n\le N}m_{T_L(N)}(n)\mathbf1_{\{m_{T_L(N)}(n)>H\}}<N
 \quad\text{for every }N>0.                             \tag{8}
\]
Allowing the finite floor to depend on \(L\) does not avoid (7).
Both quantifiers over the floor and the shift are universal.

## 3. The wider logarithmic-clock obstruction

There is a sharper written consequence of the kernel ingredients.
Put \(\gamma=\log_2 6=1+\log_2 3\). For a dyadic cutoff \(N=2^d\),
choose
\[
 K=\lceil T/\gamma\rceil,\qquad M=2^K,\qquad Q=2^{d-K}.
\]
Whenever \(1\le K\le d\) and \(H<2^K-1\), condition \(2^T\le6^K\)
holds, and (4)–(6) give
\[
 F_{H,T}(2^d)\ge 2^{d-K-1}
                    \ge\frac14\,2^{d-T/\gamma}.         \tag{9}
\]
Thus for any fixed \(0<c<\gamma\), integer \(L\ge0\), and floor \(H\),
the clocks \(T=\lfloor c\log_2N\rfloor+L\) satisfy, at all sufficiently
large dyadic cutoffs,
\[
 F_{H,T}(N)\ge
             \frac14\,2^{-L/\gamma}N^{\,1-c/\gamma}
             \longrightarrow\infty.                   \tag{10}
\]
The ceiling and real-exponent assembly is written; the integer
no-descent and population ingredients are kernel checked. For \(c=2\)
this improves the exponent \(1/5\) implicit in (1), although (1) is the
convenient fully rational, formalized instance.

More concretely, any clock satisfying the strict budget at every large
dyadic cutoff must obey
\[
                T(2^d)>\gamma(d-1).
\]
Apply (4)–(6) with period \(2^{d-1}\) and count two; the two sources
already contribute at least \(2^d\). The exact integer implication
from a strict budget to \(6^{d-1}<2^{T(2^d)}\) is kernel checked.
For an additional clock \(L(N)\) on top of \(2\lfloor\log_2N\rfloor\),
this requires
\[
                L(2^d)>(\gamma-2)d-\gamma
\]
at every sufficiently large dyadic cutoff. This is a necessary
condition only.

The calculation does not rule out coefficients at or above
\(\log_2 6\), faster clocks, or other estimates for global minima.
It is a necessary restriction on this finite-prefix budget, not a
general lower bound on every source's stopping time. No novelty is
claimed for the elementary growing-block mechanism.

## 4. Pointwise settling survives, but uniform smallness fails

Write
\[
 A_{H,L}(N)=F_{H,T_L(N)}(N),\qquad
 G_H(N)=\frac1N\sum_{n\le N}m(n)\mathbf1_{\{m(n)>H\}}.
\]
At each fixed \(N\), increasing \(L\) decreases \(A_{H,L}(N)\). Moreover
it eventually equals \(G_H(N)\), without assuming that any source
reaches one. Every global minimum is attained at a finite time; for
the finitely many sources through \(N\), take a common upper bound
on those attaining times. The kernel proof uses their sum as such
a bound. It does not supply an effectively known stopping clock.

Thus
\[
 \forall N,\quad A_{H,L}(N)=G_H(N)
 \text{ for all sufficiently large }L,                 \tag{11}
\]
while (7) says that \(\sup_N A_{H,L}(N)=\infty\) at every finite \(L\).
If full Collatz is true and \(H\ge1\), then \(G_H=0\), so (11)
is a direct example of convergence at each fixed cutoff that is
maximally nonuniform over cutoffs. Unconditionally, (7) already
excludes a uniform subunit bound on these adaptive prefix means.
It does not identify \(A_{H,L}-G_H\) without additional information
about \(G_H\).

A small closed witness shows that this obstruction can be supplied
by convergent sources. At \(H=64,L=0,N=1024,T=20\), the four sources
\[
                         255,\ 511,\ 767,\ 1023
\]
retain their initial values as their prefix minima. Their contribution
alone is \(2556>1024\), so \(A_{64,0}(1024)\ge639/256\).
All four sources reach one at ordinary clocks \(47,61,59,62\),
respectively. The tail-sum lower bound and these hitting statements
are kernel checked; the latter use kernel reduction with no axioms.
This certifies the four contributing sources, not a new kernel
certificate for the entire population through 1024.

## 5. What this says about the residual route

For the fixed function \(N\mapsto A_{H,L}(N)\), define the clockless
residual
\[
 R_{H,L}(N)=A_{H,L}(N)
       -\frac{A_{H,L}(a(N))+A_{H,L}(b(N))}{2}.
\]
Each child uses its own cutoff-dependent clock \(T_L\). This differs
from the earlier finite-clock residual, whose children use the
parent's remaining clock minus one or two.

The written elementary parity bound from the preceding note applies
uniformly in \(L\), because \(T_L(N)\ge2\lfloor\log_2N\rfloor\). It gives
\[
 0\le A_{H,L}(N)\le3V(N),\qquad A_{H,L}(N)=0\ (N\le H).
\]
For \(H\ge1\), the Green-kernel argument gives an absolutely integrable expansion
\[
 A_{H,L}(N)=\mathbb E_N\sum_{i<\tau}R_{H,L}(N_i).
\]
Combining it with (1) shows that, for every fixed \(H,L\), both the
expected signed occupation and the expected positive-part occupation
are unbounded in the initial cutoff. In particular,
\[
 \sup_N\mathbb E_N\sum_{i<\tau}\max(R_{H,L}(N_i),0)=\infty. \tag{12}
\]
The corresponding finite-depth lower bound
\[
 \mathbb E_N\sum_{i<J,\ i<\tau}R_{H,L}(N_i)
 \ge2^{j-1}-3\rho^J V(N),\qquad N=2^{5j+2L},             \tag{13}
\]
is kernel checked under the explicit majorant premise. Its application
and the infinite limits retain the written scope of the previous note.

There is still valid convergence at each fixed initial cutoff.
Pointwise settling (11), applied also to the two children, gives
\(R_{H,L}(n)\to R_H(n)\). The common majorant
\(\lvert R_{H,L}-R_H\rvert\le6V\) and the integrable Green occupation
of \(V\) justify dominated convergence:
\[
 \mathbb E_N\sum_{i<\tau}
       |R_{H,L}(N_i)-R_H(N_i)|\longrightarrow0
 \quad\text{for each fixed }N.                           \tag{14}
\]
This written conclusion supplies no uniform rate in \(N\).
Equation (12) rules out the hoped-for uniform positive-residual estimate
on these finite approximants. It does not rule out a bound for the
actual global residual, or cancellation estimates at other clock scales.

## 6. Verification and remaining work

Run:

    python3 verify_minimum_clock_barrier.py

The verifier authenticates the preceding Green-kernel record and
freshly builds eleven Lean modules sequentially. It audits all 30 new
roots, including the four closed hitting certificates. Independent
integer checks replay selected ordinary prefixes, exact residue-class
population arithmetic, and complete finite populations with a second
source-major traversal. It also records a small fixed-cutoff population
settling to minimum one. See the
[manifest](../results/minimum-clock-barrier/verification.json) and
[exact replay](../results/minimum-clock-barrier/replay.json).

The final run passed on 2026-10-14 at 20:10:10 UTC. Eleven fresh
Lean 4.33.1 builds took 5.426 seconds; all 30 roots passed, and the
four-source hitting root is axiom-free. The manifest hashes 26 files
and authenticates 24 files from the preceding record. Independent
checks include 1,596 selected sources with 501,492 ordinary steps,
418 large-family arithmetic cases, and 256 dyadic clock thresholds.
The complete census covers 131,072 sources through clock 35, with
4,587,520 ordinary steps in each traversal order and 786,432 matching
minimum snapshots. Twenty-two population lower bounds pass.
The separate settling check verifies all 1,024 small sources reach
one, with maximum first-arrival clock 178; that larger interval claim
is Python evidence, not a new kernel interval certificate.

Huge family cutoffs in the arithmetic replay are not interval
enumerations. Finite surviving prefixes never certify divergence.
Python population and settling checks are separate from kernel proofs.
No external result or floating-point proof decision is used.

The next argument must control the actual global residual directly,
or use a cutoff-dependent additional clock whose growth escapes this
barrier. Absolute integrability alone does not provide that control.
The uniform minimum-tail budget, unknown nonconvergent mass, and
positive-integer Collatz conjecture remain unresolved.
