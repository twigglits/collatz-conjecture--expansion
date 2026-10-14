# An absolutely integrable clockless residual expansion

**Status: a rational contraction and finite truncation bounds are kernel
checked. Elementary parity counting and the infinite expectation argument
remain written. They justify an absolutely integrable residual expansion
for actual global-minimum tail means. They do not prove the uniform subunit
budget or resolve Collatz. No external density or analytic mixing theorem
is used.**

The [linear-boundary note](MINIMUM-LINEAR-BOUNDARY.md) proved, in its written
clockless argument, that the terminal mean vanishes. It explicitly left
expectation of an infinite residual sum unjustified. The stronger elementary
power bound available in that same note closes this integrability gap.

The new ingredient is a rational dyadic weight \(V\) for which the fair cutoff
operator satisfies \(PV\le\rho V\), with \(\rho=1704/1711<1\). At floor
\(H\ge1\), write \(G_H(N)=N^{-1}\sum_{n\le N}m(n)\mathbf1_{m(n)>H}\), where
\(m(n)=\min_{t\ge0}C^t(n)\) is the attained global minimum, whether or not the
orbit reaches one. With \(R_H=G_H-PG_H\), the resulting written identity is

\[
 G_H(N)=\mathbb E_N\sum_{j<\tau}R_H(N_j),\qquad
 \mathbb E_N\sum_{j\ge J,\ j<\tau}|R_H(N_j)|
 \le\frac{5133}{7}\left(\frac{1704}{1711}\right)^J V(N).       \tag{1}
\]

This concerns a chain of **source cutoffs**, not a random model of an
individual Collatz orbit. Its finite bounds are formalized for arbitrary
nonnegative functions bounded by \(3V\), with the bound stated as a premise.
The verification does not hide the written population estimate in an axiom.

## 1. A weight compatible with elementary parity counting

Put \(q=29/30\), \(r=2q=29/15\), and set \(V(0)=0\). For \(n\ge1\), let
\(k=\lfloor\log_2n\rfloor\), \(p=2^k\), and define

\[
                 V(n)=q^k\frac{p+14n}{15}.                 \tag{2}
\]

Thus \(V(p)=r^k\); its real extension is the continuous, increasing,
concave piecewise linear interpolation between consecutive dyadic values.
Its successive slopes are \(14q^k/15\). Direct inequalities give

\[
 1\le q^kp\le V(n)\le q^kn,
 \qquad q^k(n+2p)\le3V(n).                                \tag{3}
\]

The last inequality is equivalent to \(p\le n\). The displayed lower bound,
sublinear envelope, and conversion to \(3V\) have kernel proofs. In
particular, \(V(n)/n\to0\), although \(V(n)\to\infty\).

Here is the population argument, restated to expose its scope. For \(k\)
shortcut steps and \(j\) odd steps, the final value has affine slope
\(A=3^j/2^k\) and correction at most \((3/2)^k-1\). Choose rational weights
\(e=17/24\), \(o=49/40\); they satisfy \(e^2\ge1/2\), \(o^2\ge3/2\), and
\((e+o)/2=q\). For a word weight \(w=e^{k-j}o^j\), therefore
\(\min(1,A)\le w\). As \(k\) shortcut steps consume at most \(2k\) ordinary
steps, for \(T\ge2k\) the prefix minimum obeys

\[
                   m_T(n)\le nw+(3/2)^k.
\]

Every length-\(k\) parity word occurs once among residues modulo \(2^k\).
Each such residue occurs at most \(N/2^k+1\) times through \(N\), and the
sum of all word weights is \((2q)^k\). Bounding each source by \(N\) in its
weighted term gives, uniformly in \(H\ge0\),

\[
 \frac1N\sum_{n\le N}m_T(n)\mathbf1_{m_T(n)>H}
 \le Nq^k+(2q)^k+(3/2)^k.                                 \tag{4}
\]

Apply this at \(k=\lfloor\log_2N\rfloor\), \(T=2k\), and use
\(m\le m_{2k}\). Since \(3/2\le2q\), (3)–(4) imply the all-population bound

\[
                         0\le G_H(N)\le3V(N).             \tag{5}
\]

This uses no convergence assumption on the sources. The finite affine
identity is an existing kernel result; the parity population assembly
(4), its application to all global minima, and the limiting arguments
remain written. Python separately checks finite instances using actual
prefix minima, never substituting those values for unknown global minima.

## 2. Exact contraction, including integer rounding

For \(n\ge1\), define

\[
 a(n)=\lfloor n/2\rfloor,\quad
 b(n)=3\lfloor(n-1)/2\rfloor+2,\quad
 Pf(n)=\frac{f(a(n))+f(b(n))}{2}.
\]

For every integer \(n\ge2\), the kernel theorem is

\[
                      PV(n)\le\rho V(n),\qquad
 \rho=\frac{1704}{1711},\quad1-\rho=\frac7{1711}.          \tag{6}
\]

One way to understand the constant is to interpolate the dyadic values
\(r^k\) for a general \(1<r<2\). On a dyadic cell, write \(x=n/2^k\in[1,2]\)
and \(L(x)=2-r+(r-1)x\). At the ideal, unrounded children, the lower ratio
is \(1/r\). The upper ratio is \(L(3x/2)/L(x)\) up to \(x=4/3\), and
\(rL(3x/4)/L(x)\) afterwards. The first increases and the second decreases;
their common maximum is \(3r/(r+2)\). Thus

\[
 \rho_r=\frac1{2r}+\frac{3r}{2(r+2)}
 =1-\frac{(r-1)(2-r)}{2r(r+2)}<1.                         \tag{7}
\]

For even \(n\), rounding lowers the upper child by one. For odd \(n\),
rounding moves the lower child down by \(1/2\) and the upper child up by
\(1/2\); concavity lowers their sum. This gives a written explanation of
(6). The Lean proof avoids real interpolation and differentiability:
it verifies the following two integer inequalities directly.

For \(2p\le n<4p\), where \(p=2^k\), the lower child lies in \([p,2p)\)
and the upper in \([2p,8p)\). If \(b\le4p\),

\[
 295(88p+420a+406b)\le17040(2p+14n).                      \tag{8}
\]

If \(b\ge4p\),

\[
 295(2132p+6300a+5887b)\le255600(2p+14n).                 \tag{9}
\]

Substitute (2) on the appropriate child cells, multiply these inequalities
by \(q^k\ge0\), and cancel their fixed denominators to obtain (6).
The odd/even arithmetic, dyadic cell locations, and all-cutoff conclusion
are kernel checked. At \(r=2\), (7) instead gives \(\rho_r=1\); this
contraction does not extend to a linear weight with a finite geometric
constant. It does not invalidate the preceding finite-clock linear
boundary obstruction.

## 3. Finite killed averages and occupation bounds

Let \(N_0=N\), choose either cutoff child with probability \(1/2\), and let
\(\tau=\inf\{j\ge0:N_j\le H\}\). On active states \(N_j>H\ge1\), both
children are positive. Iterating (6), with zero value after absorption,
gives

\[
 \mathbb E_N[V(N_J)\mathbf1_{\{\tau>J\}}]\le\rho^JV(N).   \tag{10}
\]

Since \(V\ge1\) on positive states, \(\Pr_N(\tau>J)\le\rho^JV(N)\to0\).
Thus the floor is reached almost surely, also for \(H=1,2\). This new
bound does not require the earlier logarithmic potential's floor \(H\ge3\).
It is generally weaker as a bound on the mean hitting time.

More generally, if \(f\le cV\) on active states and \(c\ge0\), then

\[
 \mathbb E_N[f(N_J)\mathbf1_{\{\tau>J\}}]\le c\rho^JV(N),
\]
\[
 \mathbb E_N\sum_{j<K,\ j<\tau}f(N_j)
 \le c\frac{1-\rho^K}{1-\rho}V(N).                       \tag{11}
\]

The function in the second inequality may be signed. The rational finite
recurrences, (10)–(11), their geometric identities, and splitting an
occupation at depth \(J\) are kernel checked. The probabilistic notation
here is the interpretation of those finite binary averages.

## 4. Absolute integrability and the signed truncation error

For any \(f\ge0\) bounded by \(3V\), at an active state,

\[
       0\le Pf\le3PV\le3\rho V\le3V,\qquad
                         |f-Pf|\le3V.                  \tag{12}
\]

The second inequality uses nonnegativity of both terms, improving the
looser triangle bound \(3(1+\rho)V\). Applying (11) to (12), then (10)
to the remaining occupation after depth \(J\), gives, for every finite
\(J,K\ge0\),

\[
 0\le\mathbb E_N\sum_{J\le j<J+K,\ j<\tau}|f(N_j)-Pf(N_j)|
 \le\frac3{1-\rho}\rho^JV(N)
 =\frac{5133}{7}\rho^JV(N).                              \tag{13}
\]

If \(f=0\) on \([0,H]\), finite telescoping gives

\[
 f(N)=\mathbb E_N[f(N_J)\mathbf1_{\{\tau>J\}}]
      +\mathbb E_N\sum_{j<J,\ j<\tau}(f-Pf)(N_j).         \tag{14}
\]

These finite statements are kernel theorems. By (5), they apply to the
actual global-minimum mean \(G_H\). The global mean's nonnegativity and
vanishing below the floor are also separately kernel checked.

Now let \(K\to\infty\) in the nonnegative sum (13). Monotone convergence
proves integrability of its infinite total absolute value and the same
tail bound. Thus its signed partial sums converge in \(L^1\), justifying
expectation of the infinite sum. The first term of (14) tends to zero by
(10), proving (1). This is a written measure-theoretic argument; no
measure-theory formalization or new external theorem is claimed.

The signed approximation has the sharper error bound

\[
 0\le G_H(N)-\mathbb E_N\sum_{j<J,\ j<\tau}R_H(N_j)
 \le3\rho^JV(N).                                        \tag{15}
\]

Its partial expectations need not be monotone: local residuals can have
either sign. Equation (15) follows from the nonnegative terminal term,
not from termwise positivity. The limit and tail bounds hold at each
fixed initial cutoff. They are not uniform subunit bounds over all \(N\).

## 5. What a least counterexample would require

Suppose \(A\) is the least positive counterexample to Collatz. Then \(A>1\),
every smaller positive source reaches one, and every iterate of \(A\) is
at least \(A\). Consequently

\[
 m(A)=A,\qquad m(n)=1\ (1\le n<A),\qquad
                    G_{A-1}(A)=1.                       \tag{16}
\]

All three implications, including the exact diagonal tail sum \(A\), are
kernel checked. Let

\[
 \eta_{A-1}=\sup_{n\ge A}\frac{\max(R_{A-1}(n),0)}{V(n)}.
\]

It is finite, at most three, by (12). If a nonnegative \(\eta\) majorizes
these positive ratios, (11), (15), and (16) give, for every finite \(K\),

\[
       1\le[3\rho^K+\eta(1-\rho^K)/(1-\rho)]V(A).        \tag{17}
\]

This finite diagnostic is kernel checked under the explicit \(G\le3V\)
premise. Letting \(K\to\infty\) in the written argument gives

\[
             \boxed{\eta_{A-1}\ge\frac7{1711V(A)}.}       \tag{18}
\]

This is a supremum bound; attainment of a maximum is not asserted.
The required lower bound decreases as \(A\) grows. No independent bound
on the actual positive residual contradicting (18) is known here.
Defining \(R_H=G_H-PG_H\) does not itself estimate the unknown function.
The expansion therefore resolves a summability issue, not the conjecture.

## 6. Verification and remaining work

Run `python3 verify_minimum_green_kernel.py`. It freshly builds the ten
listed Lean modules sequentially, audits all 34 new roots, authenticates
the previous verification's files, and records source/log hashes in
[the manifest](../results/minimum-green-kernel/verification.json).
No native finite reduction axiom is used by the new proofs.

The full run passed on 2026-10-14 at 19:46:20 UTC. Ten fresh Lean 4.33.1
builds took 4.666 seconds; all 34 roots use only the standard logical
axioms. The manifest authenticates 24 files and validates all 26 hashes
from the preceding record. The replay includes 66,696 exact gauge checks
(1,161 at large dyadic/cell boundaries), 36 profile trees, 468 independent
tree-depth comparisons, and 3,276 absolute-tail windows. The actual
prefix census covers 16,589 sources through clock 28, with 464,492
ordinary steps in each traversal order and 248,835 matching minimum
snapshots; 49,767 population majorant comparisons pass.

The independent exact-rational replay covers all cutoffs 2 through 65536,
dyadic and cell-transition arithmetic through exponent 1024, and finite
cutoff trees with both forward probability propagation and backward
recursion. Two synthetic bounded profiles are explicitly distinguished
from a third profile using actual Collatz prefix means at
\(T(N)=2\lfloor\log_2N\rfloor\). A separate source-major traversal checks
every saved prefix minimum against the time-major census. Large cutoffs
in the arithmetic checks are not Collatz orbit censuses. Large rational
output values may be stored as tagged outward enclosures with exact
binary hashes; all comparisons use exact fractions.

The remaining research target is an independent bound on the signed or
positive residual that yields the uniform subunit tail budget. The bound
(1) grows with \(V(N)\) and does not do that. The uniform integrability of
actual minima, the unknown nonconvergent mass, and full Collatz remain
unresolved.
