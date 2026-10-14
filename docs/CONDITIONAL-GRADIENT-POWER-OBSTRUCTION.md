# Universal convergence would force large accumulated-gradient powers

**Collatz remains unresolved. The infinite conclusion below assumes
universal convergence to one.** Under that assumption, a uniform power
bound for the complete accumulated adjacent gradients on all dyadic
source intervals is impossible, for every power strictly greater than
one. This is a conditional obstruction to a proposed proof ingredient,
not a counterexample to Collatz.

In the actual refinement notation, let \(M=2^k\), \(M\le n<2M\), and
\[
 G_k(n)=\sum_{s\ge0}
   [M f_{k+s}(n)-3M f_{k+s}(3n+2)]^2,
 \qquad f_t(n)=\frac{3^{a_t(n)}}{2^tU^t(n)}.
                                                               \tag{1}
\]
Write \(\langle\cdot\rangle_k\) for the uniform mean on this parent
interval. Assuming every positive integer reaches one, the written
theorem is: for every real \(p>1\), there are constants \(c_p>0,K_0\)
such that
\[
 \boxed{\sum_{k<K}\langle G_k^p\rangle_k
           \ge c_p K^{(p+1)/2}\quad(K\ge K_0).}                \tag{2}
\]
In particular \(\sup_k\langle G_k^p\rangle_k=\infty\). For \(p=1\)
the argument gives only a positive lower bound for the average over
levels, compatible with uniformly bounded first moments.

The proof uses local written simple-path packing and the local written
fusion-clock tail. It uses **no external density theorem**. Twelve
kernel roots check the finite arrival-clock, parity-average and
telescoping inputs. Real weight profiles, Holder and (2) remain written.

## 1. Remaining arrival clocks grow on average

For a source known to converge, let \(\tau(n)\) be its first shortcut
arrival at one. Set
\[
 T_k(n)=\tau(n)-k,\qquad
 F_k=\langle T_k\rangle_k.
\]
These are defined on an entire source interval only when its sources
are known to converge. Under the hypothesis of (2), they are defined
at every level. The subtraction is nonnegative: \(n\le2^{\tau(n)}\)
and \(n\ge2^k\) give \(\tau(n)\ge k\).

The affine lower bound gives
\[
 U^k(n)\ge3^{a_k(n)}\ge2^{a_k(n)}.
\]
At least \(a_k(n)\) further steps are needed to reach one, since each
step decreases a positive value by at most a factor two. Therefore
\[
 \tau(n)\ge k+a_k(n).
\]
The parity words on the complete band \([2^k,2^{k+1})\) have exact
mean odd count \(k/2\). The new kernel identities prove these facts,
including \(k=0\). Consequently
\[
                         \boxed{F_k\ge k/2.}                 \tag{3}
\]
This is an elementary lower bound, not an asymptotic stopping-time law.

For the two children of a parent \(n\), initial even halving gives
\[
 T_{k+1}(2n)=T_k(n),\qquad
 \Delta_k(n):=T_{k+1}(2n+1)-T_k(n)
                  =\tau(2n+1)-\tau(n)-1.
\]
Averaging the two children and telescoping yields the exact finite
identity
\[
 2F_K=\sum_{k<K}\langle\Delta_k\rangle_k,
 \qquad F_0=\tau(1)=0.                                     \tag{4}
\]
No positivity of individual \(\Delta_k\) is assumed.

## 2. Only a small fraction of edges can change this clock

Let \(E_k\) be the parents for which the actual pair
\((2n,2n+1)\) has not balanced-fused by clock \(k+1\), and write
\(\eta_k=\langle\mathbf1_{E_k}\rangle_k\).

If fusion has occurred, the two endpoints agree at this clock and
afterwards. Neither first arrival can precede \(k+1\), because both
sources are at least \(2^{k+1}\). Their first arrival times are
therefore equal, so \(\Delta_k=0\). Equality of their accumulated odd
counts also makes the two normalized profiles in (1) identical for
every \(s\ge0\). Thus
\[
                \Delta_k=0,\quad G_k=0\quad\text{off }E_k.   \tag{5}
\]

Here the source interval covers exactly the even residues modulo
\(2^{k+1}\). The earlier [fusion-clock bound](COUNT-RETURN-CLOCK.md)
for the full binary period, followed by conditioning on even sources,
gives
\[
 \eta_k\le\min\{1,28C_*/\sqrt{k+1}\},
 \qquad C_*=540\,2^{5180}.
\]
Hence
\[
 Q_K:=\sum_{k<K}\eta_k\le A\sqrt K,\qquad A=56C_*.
                                                               \tag{6}
\]
This is a legitimate complete-period calculation at the finite prefix
clock \(k+1\). The displayed \(C_*\) uses the later
[improved mean cycle budget](RETURN-CORRECTION-MOMENTS.md). The argument
does not sample independent bits on a fixed integer source beyond the
prefix clock.

Already (3)--(6) give a lower bound for the clock increments themselves.
Holder on their support, whose total measure is \(Q_K\), gives
\[
 \boxed{\sum_{k<K}\langle|\Delta_k|^p\rangle_k
   \ge\frac{(2F_K)^p}{Q_K^{p-1}}
   \ge A^{1-p}K^{(p+1)/2}\quad(p>1).}                       \tag{6a}
\]
Thus their uniform power bounds would fail under universal convergence
even without the packing argument in the next section. The first
inequality in (6a) is also an exact finite-family consequence whenever
all the required arrivals are supplied.

## 3. A clock difference costs accumulated gradient energy

The local [packing bound](FINITE-PATH-PACKING.md) makes the first-hit
weight satisfy
\[
 w_1(n)=n f_{\tau(n)}(n)\ge c:=e^{-8192/3}>0
                                                               \tag{7}
\]
for every source that reaches one. Before that arrival the remaining
weight is at least \(c\). After it, two steps on the known cycle
multiply the weight by \(3/4\).

The even- and odd-refinement identities rewrite the two profiles in
(1) as the normalized weights of the children \(2n,2n+1\), at the
same physical clocks \(k+1+s\). Their initial normalization factors
are both in \([1/2,1]\). Thus each profile is at least \(c/2\)
through its remaining first-arrival clock, and is at most
\((3/4)^{\lfloor h/2\rfloor}\) at age \(h\ge0\) after that clock.

Choose a fixed integer \(J\) with \((3/4)^J\le c/4\), and put
\(R=2J\), \(C=16c^{-2}\). Between the earlier arrival plus \(R\)
and the later arrival, one profile is at most \(c/4\) and the other
is at least \(c/2\). There are at least
\((|\Delta_k|-R)_+\) integer clocks in this window. Summing the
squared gap gives
\[
 G_k(n)\ge\frac{c^2}{16}(|\Delta_k(n)|-R)_+.
\]
Together with (5), this proves the pointwise estimate
\[
 \boxed{|\Delta_k(n)|
       \le R\mathbf1_{E_k}(n)+C G_k(n).}                    \tag{8}
\]
The fixed width \(R\) uses the known cycle only after first arrival.
It is not asserted for unknown periodic or escaping trajectories.

There is an exact finite variant. If the relevant finite source family
has certified first-hit weights at least \(3/4\), then
\((3/4)^6\le3/16\) gives
\[
 G_k(n)\ge\frac9{256}(|\Delta_k(n)|-12)_+,
 \qquad |\Delta_k(n)|\le12\mathbf1_{E_k}(n)+\frac{256}{9}G_k(n).
                                                               \tag{9}
\]
The verifier certifies this larger floor on its finite family. It is
not used as a universal floor in the infinite theorem.

## 4. Rare edges cannot carry linear clock growth with bounded powers

Equations (3), (4), and (8) give
\[
 K\le2F_K\le RQ_K+C\sum_{k<K}\langle G_k\rangle_k.          \tag{10}
\]
For \(K\ge4R^2A^2\), (6) makes \(RQ_K\le K/2\), so
\[
                  \sum_{k<K}\langle G_k\rangle_k\ge K/(2C).
                                                               \tag{11}
\]
Apply Holder on the disjoint union of the parent intervals, each
with its normalized counting measure. By (5), the support of the
integrand has total measure at most \(Q_K\). Therefore
\[
 \sum_{k<K}\langle G_k\rangle_k
 \le Q_K^{1-1/p}
       \left(\sum_{k<K}\langle G_k^p\rangle_k\right)^{1/p}.
\]
Combining with (6) and (11) proves (2), explicitly with
\[
                    c_p=(2C)^{-p}A^{1-p}.                  \tag{12}
\]
All quantities in each finite sum are finite under universal convergence,
because every sampled pair eventually enters the known cycle and its
remaining squared costs form geometric series. The conclusion is
\[
 \max_{k<K}\|G_k\|_p
       \ge c_p^{1/p}K^{(p-1)/(2p)}\quad(K\ge K_0).
\]
This is a bound on the maximum over levels, not a lower bound at every
individual level or a claim about the optimal growth rate.

Before invoking the universal hypothesis, the finite statements
(3)--(5), (8), and (10) hold whenever the displayed finite sources
and children have certified arrivals, with their applicable weight floor.

## 5. Scope for the density-pairing approach

Define the broader adjacent-gradient field on a full dyadic interval by
\[
 \mathcal G_j(m)=\sum_{t\ge j}
    [2^j(f_t(m)-f_t(m+1))]^2,
       \qquad2^j\le m<2^{j+1}.
\]
The child identities give exactly
\(\mathcal G_{k+1}(2n)=G_k(n)\). Its full-interval \(p\)th mean
is consequently at least half \(\langle G_k^p\rangle_k\).
Thus universal convergence would also rule out uniform \(p\)th means
of this broader field for every \(p>1\), including powers above four.

This prevents treating a uniform complete-interval accumulated-gradient
power bound as an ingredient compatible with a proof of full Collatz.
It is stronger than the earlier unconditional obstruction to certain
exponential norms in one respect: it addresses every power above one.
It is weaker in another: its infinite conclusion is conditional on
universal convergence and concerns a different, broader source family.

No contradiction to Collatz has been proved: the uniform power bound
has not been established. Nor does this argument disprove a bound on a
particular returned progression, on the gradients weighted by their
actual return density, or on reversed negative drift alone. The new
lower-image Haar \(L^p\) theorem is unchanged. A useful pairing must
retain enough of those restrictions or correlations; the broad uniform
power estimate above cannot supply a full-convergence proof.

The first-moment budgets \(\mathcal T_k=\langle G_k\rangle_k/2\)
can still be uniformly bounded. The fixed-offset energies \(E_s\),
criterion Q, escape exclusion, and additional-cycle exclusion also remain
open. Large moments of a time-summed field do not imply that any of
these other estimates fails.

## Verification

Run `python3 verify_gradient_clock_obstruction.py`. The
[record](../results/gradient-clock-obstruction/verification.json)
separates twelve kernel roots, exact finite first-arrival and profile
checks, reused authenticated all-future energy enclosures, and the
written conditional infinite theorem. No external theorem is used.
Finite convergence certificates are never promoted to universal
convergence. The large universal constants in (7) and (12) are analytic
bounds, not constants inferred from the finite census.
