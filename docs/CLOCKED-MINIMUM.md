# A logarithmic clock for attaining the global orbit minimum

**Status: written deductions conditional on the project's unformalized
natural-density first-passage Proposition 4.1. The exact clock-transfer
lemmas and finite integer comparisons are kernel checked. This is not a
proof of Collatz, and no novelty claim is made.**

Let \(M(n)=\min_{t\ge0}C^t(n)\) and let \(\tau_M(n)\) be its first
attainment time, in ordinary Collatz steps. Both are defined for every
positive integer, including a hypothetical divergent start: a nonempty
subset of the positive integers has a least element, attained at a finite
time. This does not imply \(M(n)=1\). All logarithms below are natural.

Retaining both passage clocks gives the sharper written conclusion
\[
 \boxed{\frac1X\#\left\{2\le n\le X:
 \left|\frac{\tau_M(n)}{\log n}-\frac3{\log(4/3)}\right|>\varepsilon
 \right\}\longrightarrow0\quad(\varepsilon>0).}          \tag{0}
\]
The coefficient is approximately \(10.42818\), so \(11\log n\) suffices
outside a set of natural density zero. Section 6 proves this
using the exact difference between the two passage clocks. Sections 1–5
first give a coarser one-sided argument with separately checked integer
comparisons. Both conclusions retain the same unformalized analytic
dependency; they do not show that almost all starts reach one.

The written passage estimates imply
\[
 \boxed{\#\{n\le X:\tau_M(n)>\lfloor435\log n\rfloor\}=o(X).} \tag{1}
\]
Moreover, for every fixed finite set of targets, the set of starts whose
eventual visitation profile is not fully captured by this clock has
natural density zero. Thus all of a fixed target's predecessor density
is recovered by a logarithmic clock. The error in this statement is
pointwise in the target, not uniform over all targets at once.

The [preceding clock audit](DENSITY-TIME-TRUNCATION.md) identified the
uniform truncation defect \(\Delta_X(T)\). The present argument also gives
\[
 \boxed{\Delta_X(\lfloor435\log X\rfloor)
             \longrightarrow\lambda_{\rm div},}         \tag{2}
\]
where \(\lambda_{\rm div}\) is the largest divergent-component density,
or zero if there are none. Neither its value nor \(M(n)=1\) is determined
by the argument.

## 1. A clock for one passage

Write \(\alpha=1001/1000\), and let \(\mathbf U_y\) be uniform on
odd integers in \([y,2y)\). For an odd start let \(F_x\) be its first
odd landing at most \(x\), with a separate nonentry mark. We use the
written proposition in
[NATURAL-DENSITY-ALMOST-BOUNDED.md](NATURAL-DENSITY-ALMOST-BOUNDED.md#4-stabilisation-for-uniform-starts):
\[
 \sup_{y,z\in[x^\alpha,x^{\alpha^2}]}
 d_{\rm TV}(F_x(\mathbf U_y),F_x(\mathbf U_z))
                                      \ll(\log x)^{-c}.   \tag{3}
\]
This natural-density input is the local written argument, not a theorem
asserted by the kernel module or by Tao's original paper.

The early valuation estimate used there supplies a time bound as well.
Put \(n_0=\lfloor\log x/(10\log2)\rfloor\). Uniformity of odd residues
modulo \(2^{3n_0}\), together with
[Tao's Proposition 1.9](https://arxiv.org/html/1909.03562v7),
approximates the first \(n_0\) Syracuse valuations by independent
\(\operatorname{Geom}(2)\) variables with exponentially small error.
The earlier lower-tail argument gives passage by \(n_0\) Syracuse
steps except with probability \(O(x^{-c})\).

For the upper tail, if \(G\) has probability \(\Pr(G=j)=2^{-j}\),
then \(\mathbf E r^G=r/(2-r)\), \(1<r<2\). Take \(r=202/201\).
For a sum \(S\) of \(n_0\) such variables, Markov's inequality gives
\[
 \Pr\left(S>\frac{201}{100}n_0\right)
 \le q^{n_0/100},\qquad
 q=\frac{101^{100}201^{201}}{100^{100}202^{201}}<1.        \tag{4}
\]
The strict integer inequality in (4) is kernel checked. Its decay is
\(O(x^{-c'})\) for some fixed \(c'>0\); no numerical error constant
is asserted. The total ordinary time through passage is the number of
Syracuse steps plus their total valuation. Therefore, outside an event
of probability \(O(x^{-c})\),
\[
       \text{ordinary passage time}\le
       L(x):=\frac{301}{1000\log2}\log x.                \tag{5}
\]
We reduce the positive exponent \(c\) if necessary. The estimate is
uniform for \(y\in[x^\alpha,x^{\alpha^2}]\).

## 2. Transferring the minimum clock

First odd passage is a strict record low in the ordinary trajectory.
Previous odd states exceed the floor; each intervening even state exceeds
its following odd endpoint. Thus every state before the landing is larger
than that landing. In particular, although an intermediate **even** state
can already be below the floor, it cannot be the global minimum before
this first odd landing.

If the first landing of \(n\) is \(b\) at ordinary time \(i\), then
\[
                  M(n)=M(b),\qquad
                  \tau_M(n)=i+\tau_M(b).                 \tag{6}
\]
The Lean module proves the record property and the precise clock-transfer
implication for two sources with a common landing. It also proves that
every finite population has some finite common minimum-attainment clock.
That clock is not a certificate that these minima equal one.

Let \(E(y,T)=\Pr(\tau_M(\mathbf U_y)>T)\), for real \(T\ge0\).
Apply (3) to the indicator
\(g_T(b)=\mathbf1_{\{\tau_M(b)>T\}}\) on finite landing marks,
and set \(g_T(\infty)=0\). On the good event in (5), failure to attain
the minimum by \(L(x)+T\) forces \(g_T(F_x)=1\). For the reference
source, (6) implies \(g_T(F_x)\le\mathbf1_{\{\tau_M>T\}}\).
Consequently
\[
 E(y,L(x)+T)\le E(z,T)+C(\log x)^{-c},
       \qquad y,z\in[x^\alpha,x^{\alpha^2}].             \tag{7}
\]
Setting the nonentry test value to zero is deliberate. The source's
nonentry is already in the exceptional event of (5). We do not infer
that nonentry forces a late global minimum. No independence between
passage, subsequent behavior, and the minimum is assumed.

## 3. Sum the clocks before taking the density limit

Fix a sufficiently large \(B\). For \(Y\ge B\), descend through scales
\(Y_i=Y^{\alpha^{-i}}\) until \(Y_J\in[B,B^\alpha)\), using shared
floors \(x_i=Y^{\alpha^{-(i+2)}}\) at adjacent scales. Indeed,
\(Y_i=x_i^{\alpha^2}\) and \(Y_{i+1}=x_i^\alpha\), so (7) applies.
All sources at the final reference scale lie below \(2B^\alpha\).
There is a finite integer \(T_B\) by which every positive integer below
that bound has attained its own global minimum. No convergence assumption
or computable bound for \(T_B\) is used.

The sum of the passage clocks is at most
\[
 \sum_{i<J}L(x_i)\le K\log Y,\qquad
 K=\frac{301}{1000\log2\,\alpha(\alpha-1)}
   =\frac{301000}{1001\log2}<435.                        \tag{8}
\]
For an exact check of the final inequality, the positive logarithm series
gives
\[
 \log2>2\sum_{j=0}^{3}\frac1{(2j+1)3^{2j+1}}
        =\frac{53056}{76545}>\frac{693}{1000},
 \qquad301000000<435\cdot693\cdot1001.
\]
The two rational comparisons are kernel checked; the logarithm series
and real clock summation are written analysis. For orientation only,
\(K\approx433.817389918\).

The errors in (7) sum to \(O((\log B)^{-c})\), since the logarithms
of the floors grow geometrically when read backward from the last scale.
The resulting estimate is
\[
 \boxed{E(Y,K\log Y+T_B)\ll(\log B)^{-c}
                                      \quad(Y\ge B).}    \tag{9}
\]
The implicit constant is independent of \(Y,B\), above an absolute
threshold. The additive clock \(T_B\) depends on the actual small orbits.

For each fixed \(B\), the positive margin \(435-K\) absorbs \(T_B\)
and integer rounding as \(Y\to\infty\). Taking that limit first, and
then \(B\to\infty\), proves (1) for odd dyadic intervals. Dyadic
decomposition gives the odd natural-density statement.

For a general start \(n=2^a m\) with \(m\) odd,
\(\tau_M(n)=a+\tau_M(m)\). If \(\tau_M(m)\le435\log m\), then
\(a+\tau_M(m)\le435\log n\), because \(435\log2>1\).
For each fixed valuation \(a\), the exceptional odd parts have density
zero; the union with \(a>A\) has density at most \(2^{-A-1}\).
Letting \(A\to\infty\) proves (1) for positive starts.
The same proof works with every coefficient strictly greater than \(K\).

There is no effective error rate in (1) here: replacing \(T_B\) by a
usable bound would require further information about those small orbits.
In particular, one cannot replace the minimum in (1) by one.

## 4. Fixed targets and convergent starts are captured in logarithmic time

Fix a finite target set \(A\), and choose \(K<C_1<435\). For any fixed
\(B\), there is a finite bound \(V_{B,A}\) on the first hitting times
from all \(m\le B\) to the members of \(A\) that they actually reach.
Only finitely many pairs are involved; unreachable pairs are omitted.

If \(M(n)\le B\), and its minimum has been attained by \(C_1\log n\),
then an eventual hit of any \(a\in A\) either has already occurred or
occurs within another \(V_{B,A}\) steps. For sufficiently large \(n\)
these hits occur by \(435\log n\). The density of the remaining sources
is at most the minimum-law tail \(\sum_{m>B}p_m\), which tends to zero.
Thus the eventual and clocked visitation profiles agree outside a set
of natural density zero. For every fixed positive \(a\),
\[
 \frac1X\#\{n\le X:\exists t\le\lfloor435\log n\rfloor,
                         C^t(n)=a\}\longrightarrow r_a. \tag{10}
\]
The same limit holds with the population clock \(\lfloor435\log X\rfloor\).
Existence of \(r_a\) and tightness of the minimum law are the earlier
written density deductions. The external positive predecessor theorem
then makes (10) positive for each fixed target not divisible by three.
This is a **written time consequence using additional local analytic
premises**; it is not a newly replayed time theorem from that external source.

For a start already known to reach one, its global minimum is one.
The kernel checks this equivalence at a finite clock. Equation (1)
therefore implies that convergent starts taking more than \(435\log n\)
steps have natural density zero. The density of fast convergence is
\(p_1\), whose equality to one remains unproved.

## 5. The remaining uniform defect is exactly the divergent mass

Use the notation of [DENSITY-TIME-TRUNCATION.md](DENSITY-TIME-TRUNCATION.md).
For a sample through \(X\), let \(d_X\) be the largest sampled fraction
in one divergent component. For every finite \(T\),
\(\Delta_X(T)\ge d_X\), by choosing a late common target beyond all
sampled prefixes. The component law gives \(d_X\to\lambda_{\rm div}\).

For the upper bound at \(T=\lfloor435\log X\rfloor\), fix \(B\) and
again take \(K<C_1<435\). The finitely many cyclic starts \(m\le B\)
have finite orbit sets, with a common finite cover time. Thus, apart from
the density-zero late-minimum set and sources with minimum greater than
\(B\), every sampled source in a cyclic component has had its entire
orbit set covered by \(T\), once \(X\) is sufficiently large.

A missed target in a divergent component receives at most \(d_X\) of
the sample. A missed target in a cyclic component receives at most
\(\sum_{m>B}p_m+o(1)\). Hence
\[
 \Delta_X(\lfloor435\log X\rfloor)
       \le\max\left(d_X,\sum_{m>B}p_m+o(1)\right).
\]
First let \(X\to\infty\), then \(B\to\infty\), proving (2).
This supplies a fixed logarithmic clock reaching the optimal limiting
uniform defect. It does **not** prove that the defect is zero.

With external PLD positivity, zero defect is equivalent to absence of
divergent positive orbits. Additional cycles would still have to be
excluded. A divergent source can reach its global minimum quickly and
then escape; (1) is compatible with precisely that unresolved behavior.

## 6. Retaining both passage clocks gives the typical coefficient

Put \(d=\log(4/3)\) and \(\kappa=3/d\). For every fixed
\(\eta>0\), the early valuation law gives, uniformly over the same
source scales,
\[
 \Pr\bigl(I_x(\mathbf U_y)=\infty\ \text{or}\quad
 |I_x(\mathbf U_y)-\kappa\log(y/x)|>\eta\log x\bigr)
                                      =O_\eta(x^{-c_\eta}),       \tag{11}
\]
where \(I_x\) denotes the **ordinary** first odd passage time, and
\(c_\eta>0\) is allowed to depend on \(\eta\).

Here are the details needed to retain the clock. By
[Tao's Proposition 1.9 and Lemma 2.2](https://arxiv.org/html/1909.03562v7),
for any fixed sufficiently small \(h>0\), outside an event of probability
\(O_h(x^{-c_h})\), the actual valuation partial sums satisfy
\[
             |S_j-2j|\le h\log x\qquad(0\le j\le n_0).
\]
Indeed, apply the Chernoff tail estimate to each of the at most
\(n_0=O(\log x)\) partial sums and use the valuation-law total-variation
error. The power-saving bound absorbs this logarithmic union factor.
The earlier passage estimate also gives a first Syracuse entry
\(1\le k\le n_0\), outside a power-small exceptional event.

For an actual source \(n\in[y,2y)\), write its odd states as \(N_j\).
Before first entry they exceed \(x\), so for \(j\le k\) the exact
logarithmic identity is
\[
 \log N_j=\log n-dj-(S_j-2j)\log2+e_j,\qquad
 0\le e_j=\sum_{\ell<j}\log\left(1+\frac1{3N_\ell}\right)
                                                  \le\frac{j}{3x}.
\]
Apply this at \(k\) and \(k-1\), using \(N_k\le x<N_{k-1}\).
It follows that
\[
 \left|k-\frac{\log(y/x)}d\right|
       \le\frac{h\log2}d\log x+O(1),
 \qquad
 |I_x(n)-\kappa\log(y/x)|
       \le\left(1+\frac{3\log2}d\right)h\log x+O(1).
\]
We used \(I_x(n)=k+S_k\) and
\(0\le\log n-\log y<\log2\). Choose \(h\) small enough in terms
of \(\eta\), then increase the threshold for \(x\), to obtain (11).
No estimates after first passage enter this argument.

Couple the two landing laws from \(\mathbf U_y,\mathbf U_z\) so their
marks disagree with probability at most their total variation. Lift this
to a coupling of the original sources by their conditional distributions
given a mark. This preserves both source marginals. On matching finite
marks with both clocks good, (6) gives the exact identity
\[
 \tau_M(n)-\tau_M(m)=I_x(n)-I_x(m).
\]
The kernel module separately proves the corresponding integer equality
\(\tau_M(n)+I_x(m)=\tau_M(m)+I_x(n)\) under its explicit
first-minimum and common-record assumptions. Consequently this coupling
satisfies
\[
 |(\tau_M(n)-\kappa\log y)-(\tau_M(m)-\kappa\log z)|
                                               \le2\eta\log x       \tag{12}
\]
outside an event of probability
\(O_\eta((\log x)^{-c})\). This combines two marginal clock estimates
and the landing-law estimate; it does not assert independence or require
a separate mixing theorem for the joint clock and landing.

Let \(D_y(w)=\Pr(|\tau_M(\mathbf U_y)-\kappa\log y|>w)\).
For \(w\ge0\), (12) gives
\[
 D_y(w+2\eta\log x)\le D_z(w)+C_\eta(\log x)^{-c}.       \tag{13}
\]
Use the same descending scales \(Y_i,x_i\) as in Section 3. At the
final scale all centered minimum times have absolute value at most
\(W_B=T_B+\kappa\alpha\log B\). Iterating (13), and summing the
geometric series of logarithms and errors, gives
\[
 D_Y\left(W_B+\frac{2\eta}{\alpha(\alpha-1)}\log Y\right)
                         \ll_\eta(\log B)^{-c}.           \tag{14}
\]
For a requested \(\varepsilon>0\), fix
\(\eta<\varepsilon\alpha(\alpha-1)/4\). First let \(Y\to\infty\)
so the fixed \(W_B\) is absorbed; then let \(B\to\infty\). Replacing
\(\log Y\) by \(\log n\) changes the center by only a bounded amount
on \([Y,2Y)\). This proves (0) for odd sources. For fixed \(a\),
\[
 \tau_M(2^a m)-\kappa\log(2^a m)
       =\tau_M(m)-\kappa\log m+a(1-\kappa\log2),
\]
so discarding the density-small tail of large initial valuations and
then using odd dyadic decomposition proves (0) for all positive sources.
Neither a rate nor an effective bound on \(W_B\) is supplied.

For a fixed target \(a\), let \(\tau_a(n)\) be its first hitting time
on starts that eventually hit it. There are finite constants \(q_a,V_a\)
such that, for all such starts,
\[
          \tau_M(n)-q_a\le\tau_a(n)\le\tau_M(n)+V_a.     \tag{15}
\]
Take \(q_a=\tau_M(a)\): the global minimum of the source is attained
either before hitting \(a\), or by another \(q_a\) steps afterward.
For the upper bound, \(M(n)\le a\); take \(V_a\) to be the maximum
first hitting time of \(a\) from the finitely many \(m\le a\) that
reach it. A first hit after minimum attainment is bounded by this
constant, and a hit before it needs no additional time.

Thus for every fixed positive \(a\) and \(c\ge0\),
\[
 \frac1X\#\{n\le X:\tau_a(n)\le\lfloor c\log n\rfloor\}
 \longrightarrow
 \begin{cases}0,&c<\kappa,\\ r_a,&c>\kappa.\end{cases}     \tag{16}
\]
Unreachable starts contribute zero. The same conclusion holds for the
population clock \(\lfloor c\log X\rfloor\): for the lower-clock
case discard \(n\le X^\rho\), where \(c/\kappa<\rho<1\).
Finite target sets follow by taking finite unions. The case
\(c=\kappa\) is not decided here.

Finally let \(\lambda_*\) be the largest component density, including
cyclic components. The sharper uniform-defect conclusion is
\[
 \boxed{\Delta_X(\lfloor c\log X\rfloor)\longrightarrow
 \begin{cases}
 \lambda_*,&0\le c<\kappa,\\
 \lambda_{\rm div},&c>\kappa.
 \end{cases}}                                           \tag{17}
\]
Above \(\kappa\), repeat Section 5 with
\(\kappa<C_1<c\). Below \(\kappa\), (16) makes the clocked proportion
at each fixed target tend to zero. Taking fixed targets whose densities
approach \(\lambda_*\) proves the lower bound. The upper bound follows
from \(\Delta_X(T)\le\sup_aR_X(a)\to\sup_ar_a=\lambda_*\),
using the earlier target-uniform convergence. Equation (17) does not
determine either component mass. In particular a typical clock to a
minimum is fully compatible with an escaping tail after that minimum.

In particular one can use the fixed coefficient 11:
\(\log(4/3)>2/7\) from its positive logarithm series implies
\(\kappa<21/2<11\). Then
\[
 \lim_{X\to\infty}\frac1X
 \#\{n\le X:\exists t\le\lfloor11\log X\rfloor,\ C^t(n)=1\}=p_1.
                                                               \tag{18}
\]
With external PLD, the full conjecture is therefore equivalent to this
specific finite-clock proportion tending to one. The argument identifies
the limit with \(p_1\); it does not establish its missing value.

## 7. Verification and dependencies

[`ClockedMinimum.lean`](../lean/ClockedMinimum.lean) imports only the local
ordinary Collatz definitions. It proves minimum attainment, finite
population clocks, the first-odd-passage record property, suffix and
coupling clock transport (including the exact signed clock difference),
and the finite-time equivalence with hitting one for an already convergent
start. It also checks the integer comparisons in Sections 1 and 3.
None of the density conclusions or logarithmic estimates is
claimed as kernel formalized.

The [independent replay](../verify_clocked_minimum.py) checks complete
known-cycle trajectories, first passage and minimum-time identities,
coupled and centered clocks, fixed-target time transfer, and exact
rational comparisons.
It does not infer a natural-density theorem from a finite sample.
The [manifest](../results/clocked-minimum/verification.json) records the
kernel, finite Python, written analytic, and external scopes separately.

```sh
python3 verify_clocked_minimum.py --reuse-build-dir /tmp/collatz-killed-operator-build
```
