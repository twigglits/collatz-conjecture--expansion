# Direct exit-mass certificates for actual survivor horizons

**Collatz remains unresolved.** Exact forward first-entry data and a
rigorous infinite-tail bound certify
\[
                  M_{k+1}\le\frac{993}{1000}M_k
\]
for every \(0\le k\le126\), and also for \(k=128\), at the existing
floor \(H=64\) and exponent \(s=3/2\). These are **128 finite-horizon
certificates** for the full infinite survivor mass, not an all-time
estimate. The earlier complete inverse-cone replay certified the
sufficient eligible-share bound through \(k=36\).

The computation covers starts through \(R=2{,}000{,}000\). It does not
assume that larger starts converge. All numerical decisions use exact
integers. The finite computation is an independent Python check; the
infinite-sum and integral inequalities below are written arguments,
not new Lean theorems. The previously checked integer definitions,
inverse branches, and convergent base are reused without modification.

## 1. Keep the actual exit set

Use the definitions from [WEIGHTED-SURVIVORS.md](WEIGHTED-SURVIVORS.md):
\[
 \tau(n)=\inf\{t\ge0:U^t(n)\le64\},\quad
 S_k=\{n:\tau(n)>k\},\quad M_k=\sum_{n\in S_k}n^{-3/2}.
\]
Infinite hitting times remain allowed. The exact exit mass is
\[
 D_k=M_k-M_{k+1}=\sum_{\tau(n)=k+1}n^{-3/2}.               \tag{1}
\]
This follows from nested survivor sets and absolute convergence. Also
\(M_k>0\): every \(n>64\,2^k\) survives through time \(k\).

Given exact hitting times for starts through \(R\), set
\[
 P_k(R)=\sum_{n\le R,\ \tau(n)>k}n^{-3/2},\qquad
 E_k(R)=\sum_{n\le R,\ \tau(n)=k+1}n^{-3/2}.
\]
The decreasing-integrand bound gives
\[
 M_k\le P_k(R)+2/\sqrt R=:V_k(R),\qquad D_k\ge E_k(R).
\]
Consequently
\[
 \boxed{\frac{M_{k+1}}{M_k}
       \le1-\frac{E_k(R)}{V_k(R)}.}                      \tag{2}
\]
The proof uses \(E_k(R)/M_k\ge E_k(R)/V_k(R)\). It does not divide
two independently truncated survivor masses or presume cancellation
of unobserved exits. Every omitted exit only improves (2).

The sufficient test
\[
                       1000E_k(R)\ge7V_k(R)              \tag{3}
\]
therefore certifies the displayed contraction for the **actual**
survivor sequence. This calculation uses its first-entry times, not a
replacement population satisfying only predecessor closure.

## 2. Exact integer enclosures

Let \(S=2^{96}\) and compute
\[
 a_n=\left\lfloor S n^{-3/2}\right\rfloor
     =\operatorname{isqrt}\!\left(\left\lfloor S^2/n^3\right\rfloor\right).
\]
For each value the verifier checks
\(a_n^2n^3\le S^2<(a_n+1)^2n^3\). Thus
\(a_n/S\le n^{-3/2}<(a_n+1)/S\).
With
\[
 A_k=\sum_{n\le R,\ \tau(n)>k}a_n,\quad
 C_k=\#\{n\le R:\tau(n)>k\},\quad
 L_k=\sum_{n\le R,\ \tau(n)=k+1}a_n,
\]
define
\[
 B_R=2\left(\operatorname{isqrt}(\lfloor S^2/R\rfloor)+1\right),
 \qquad U_k=A_k+C_k+B_R.
\]
Then \(M_k\le U_k/S\), \(D_k\ge L_k/S\), and the implemented test
is the integer comparison \(1000L_k\ge7U_k\).

For reported lower mass bounds, all integers exceeding
\(B=\max(R,64\,2^k)\) are guaranteed survivors. The integral from
\(B+1\) supplies the additional lower tail \(2/\sqrt{B+1}\).
This lower bound is not needed in (3). At very late horizons its rounded
integer enclosure may be zero, even though the true mass is positive.

## 3. What passed, and what a failed test means

The independently computed table establishes first entry into 1..64
for every source through 2,000,000. Its maximum first-entry time is
335. Separate direct trajectories replay an initial interval and
samples from every attained hitting-time layer, including large
sources. An additional independent check covers **every** nonbase table
row: follow its actual trajectory to the first return into 1..R and
check that the source's time equals the excursion length plus the
returned state's time. All intervening states exceed R, and the stored
time strictly decreases on return. Induction on these nonnegative
integer times proves the table's first-entry claims. This complete
finite certificate is checked in Python, not Lean.

The forward table and the older inverse-cone mass intervals agree at
every shared horizon.

The integer test passes at \(k=0,\ldots,126,128\). At \(k=128\),
the certified relative loss is greater than 0.00711966. The sufficient
test first fails at \(k=127\). This does **not** show that the actual
mass ratio exceeds 0.993 there: the denominator still includes the
whole unclassified tail above \(R\), while the numerator omits its
exits. No failed numerical certificate is labeled a failure of the
actual inequality.

Run `python3 verify_survivor_exit_mass.py`. The
[verification record](../results/survivor-exit-mass/verification.json)
contains the integer bounds, first-entry table digest, direct replay
scope, dependency hashes, and exact list of certified horizons. The
scale \(S\) controls rational enclosure precision; displayed decimal
values are explanatory only.

## 4. The missing infinite step

Infinitely many horizons with this fixed contraction would force
\(M_k\to0\), hence convergence of every positive start by the existing
kernel-certified base and the written mass equivalence. A finite set
of horizons does not do so. This computation provides no bound ensuring
that (3) passes at arbitrarily large horizons, for this or any growing
cutoff schedule.

The new [fibre-prefix bound](FIBRE-PREFIX-BOUND.md) controls coefficient
moments but does not provide that missing exit-mass lower bound. Nor
does first-passage stabilisation for uniformly sampled starts assert
the same law after arbitrary survivor conditioning. Neither statement
is used as such an input here. Nontrivial positive cycles and divergent
positive trajectories both remain unresolved.
