# Coalescence caps for the actual refinement energy

**Status: seventeen arithmetic roots are kernel checked. The real energy
estimates are written deductions, with independently checked finite counts.
The bounded-energy subsequence, absence of escape, and full Collatz remain
unproved.** No additional external theorem is assumed.

The [actual-weight refinement argument](ESCAPE-WEIGHT-REFINEMENTS.md)
would exclude escape if its energies have a bounded subsequence at
arbitrarily late offsets. This note improves its linear upper bound and
identifies a limitation of using coalescence counts alone to improve it
further. A growing *upper-bound certificate* is not a lower bound on the
actual energy.

## 1. A cap uniform in the time offset

Keep the notation
\[
 H_{s,k}(x)=2^k\frac{W_{s+k}(n)}n,
 \quad n=\lfloor2^kx\rfloor,
 \quad e_{s,k}=\int_1^2|H_{s,k+1}-H_{s,k}|^2,
 \quad E_s=\sum_{k\ge0}e_{s,k}.
\]
Write \(p_H^{(0)}\) for the fraction of even residues modulo \(2^H\)
whose adjacent trajectories have both equal endpoints and equal odd counts
after \(H\) shortcut steps, and put
\[
                         q_H=\tfrac12(1-p_H^{(0)}).
\]
Balanced coalescence persists. If \(2n,2n+1\) are balanced at depth
\(H\le s+k+1\), their endpoints and odd counts at time \(s+k+1\)
coincide. The even-child identity then makes the parent and odd-child
values of \(H\) equal exactly. Otherwise their squared difference is at
most one. The even child contributes zero in either case.

For \(1\le H\le k+1\), the even inputs \(2n\) with
\(2^k\le n<2^{k+1}\) cover an integer number of complete even-residue
periods. Consequently, for **every** offset \(s\ge0\),
\[
                         \boxed{e_{s,k}\le q_H.}             \tag{1}
\]
In particular \(e_{s,k}\le q_{k+1}\). This retains the actual source
annulus; no proper subinterval of a longer residue period is averaged
as though it were a whole period.

[CoalescenceEnergyCaps.lean](../lean/CoalescenceEnergyCaps.lean) proves
persistence to arbitrary later clocks, equality of the refinement data
and cross products, and the exact repeated-period count on every such
annulus. Division, integration, and the squared bound are written.

## 2. A sharper all-offset estimate

The independent finite replay through depth twenty gives
\[
 p_{20}^{(0)}=\frac{289565}{524288},\qquad
 q_{20}=\frac{234723}{1048576},\qquad
 B:=\sum_{H=1}^{19}q_H=\frac{699653}{131072}.              \tag{2}
\]
These counts are finite Python checks, not kernel evaluations of all
the residues. The all-depth periodic transport in Section 1 is a kernel
proof; the distinction matters.

Set \(J(s)=\lceil121s/50\rceil\). A kernel proof, using the exact
block inequality \(2^{271}\le3^{171}\) and fifty remainder cases, gives
\[
 121s\le50J(s)<121s+50,\qquad
                  2^{3s+J(s)}\le3^{s+J(s)}.              \tag{3}
\]
Thus \((8/3)^s(2/3)^{J(s)}\le1\). Split the energy at
\(K=19+J(s)\). Apply (1) separately to the first nineteen levels,
use \(q_{20}\) on the next \(J(s)\) levels, and use the previously
proved written geometric tail thereafter. This yields
\[
 \begin{split}
 E_s&\le B+q_{20}J(s)+T_{19},\\
 T_{19}&=\tfrac12\,4^{-19}+\tfrac{21}4(2/3)^{19}.
 \end{split}                                             \tag{4}
\]
All constants here are rational. In particular
\(B+q_{20}+T_{19}<6\), and hence
\[
 \boxed{E_s\le\frac{28401483}{52428800}s+6
                  \le0.542s+6.}                         \tag{5}
\]
The previous bound \(3s/2+23/4\) remains valid; either can be used.
Neither proves a bounded subsequence as \(s\to\infty\).

For an arbitrary fixed depth \(H\), the same argument with
\(K=H-1+J(s)\) gives
\[
 E_s\le\sum_{j=1}^{H-1}q_j+q_HJ(s)
          +\tfrac12\,4^{-(H-1)}+\tfrac{21}4(2/3)^{H-1}.
                                                               \tag{6}
\]
If one additionally establishes \(p_H^{(0)}\to1\), (6) would give
\(E_s=o(s)\). That extra coalescence limit is not proved or adopted
here. Even sublinear growth would not imply the bounded subsequence
needed by the escape criterion.

## 3. Why these caps and this tail cannot prove bounded energy

Persistence makes \(q_H\) nonincreasing. The strongest levelwise estimate
obtained by combining (1) with the existing pointwise tail is
\[
 E_s\le\mathcal B_s:=\sum_{k\ge0}\min\{q_{k+1},t_{s,k}\},
 \qquad
 t_{s,k}=\tfrac38\,4^{-k}+\tfrac74(8/3)^s(2/3)^k.        \tag{7}
\]
Here the exact, all-depth \(q_H\) are allowed; this is not a claim
about the limitations of a particular finite enumeration.

For \(0\le k\le2s\), the second term in \(t_{s,k}\) is at least
\((7/4)(32/27)^s\ge7/4\), while \(q_{k+1}\le1/2\).
Thus the minimum in (7) is exactly \(q_{k+1}\) on those levels.
The earlier [kernel harmonic bound](COALESCENCE-TAIL.md) implies
\[
                    \mathcal B_s\ge
                       \tfrac12\sum_{j=1}^{2s+1}\frac1j
                       \longrightarrow\infty.           \tag{8}
\]
The stronger written fair-walk comparison in that note gives
\(q_{k+1}\ge\tfrac12\binom{k}{\lfloor k/2\rfloor}2^{-k}\),
and therefore
\[
 \boxed{\mathcal B_s\ge
       (2s+1)\frac{\binom{2s}{s}}{4^s}-\frac12
       \sim2\sqrt{s/\pi}.}                              \tag{9}
\]
For the finite-sum identity, put \(c_j=\binom{2j}{j}/4^j\).
The even term at \(k=2j\) is \(c_j\), and the odd term at
\(k=2j+1\) is \(c_{j+1}\). The recurrence for \(c_j\) proves
\(\sum_{j=0}^s c_j=(2s+1)c_s\), giving (9). The binomial
asymptotic and measure arguments are written, not additional kernel
theorems. Exact checks of finite instances accompany the replay.

The upper-bound certificate \(\mathcal B_s\), and its time averages,
are therefore unbounded. **No lower bound on \(E_s\) follows from
(8) or (9).** The actual energy may be much smaller because unmerged
pairs can have small or zero limiting weights. A successful upper bound
must estimate that weighted contribution, or use information beyond the
two levelwise estimates in (7).

## 4. The stopped odd-count gap is not a fusion time

For the even pair \(6,7\), the first positive time at which the odd
counts agree is eleven.
At that time the endpoints are respectively \(2,1\), and each odd
count is five. They subsequently alternate around the known cycle in
opposite phases and never have equal endpoints at the same clock.
The kernel proves that this pair is not balanced at **any** time.
Both starts converge to one; this is not a Collatz counterexample.

The affine lift gives an entire residue class. For every \(q\ge0\),
the first positive time of equal odd counts for
\(2048q+6,2048q+7\) is eleven, and
\[
 \begin{array}{c|cc}
   &2048q+6&2048q+7\\\hline
 U^{11}&243q+2&243q+1\\
 a_{11}&5&5
 \end{array}
\]
Hence the stopped gap is zero although the balanced-coalescence defect
is one. This occupies exactly \(1/1024\) of the even residues at that
depth. No assertion of eternal noncoalescence is made for all positive
\(q\). The base pair alone is proved never balanced.

Thus the earlier stopped-gap martingale supplies lower bounds on
noncoalescence. Its absorption probability cannot be substituted for
the balanced-coalescence probability in (1).

## 5. The drift estimate that remains open

There is an exact way to state the missing cancellation. Define the
ordinary limit of partial sums
\[
 D_s=\lim_{m\to\infty}\sum_{k=0}^{m-1}
                  \int_1^2 H_{s,k}(H_{s,k+1}-H_{s,k})\,dx.
\]
The finite telescoping identity, finite \(E_s\), and fixed-offset
\(H_{s,k}\to1/x\) in \(L^2\) prove that this limit exists and that
\[
                    E_s=\frac12-W_s(1)^2-2D_s.            \tag{10}
\]
Absolute convergence of the drift series is not claimed. A lower bound
on \(D_s\) along arbitrarily late offsets would give the required
bounded-energy subsequence. A bounded sequence of Cesaro energy means
would also suffice. Neither bound has been proved. The coalescence-only
estimate (7) cannot supply either, by Section 3.

## 6. Reproduction and scope

```sh
python3 verify_coalescence_energy_caps.py
```

The [verification record](../results/coalescence-energy-caps/verification.json)
separates seventeen fresh kernel roots, finite direct-trajectory counts,
and written infinite-sum deductions. The preceding coalescence and
refinement manifests are hash-validated. The depth-twenty census is
recomputed by direct iteration of the entire source interval, without
the earlier high-bit affine recursion. No new external result, passage
premise, or predecessor-density replay is needed for (1)--(10).
The earlier implication from bounded energy to no escape still uses its
stated packing argument and external positive predecessor density.
