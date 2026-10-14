# A finite clock test that includes every positive source

**Status: written deductions from the local written minimum-clock and
weight-limit arguments. Finite rational accounting is kernel checked
separately. The final pointwise equivalence additionally uses the external
positive predecessor-density theorem. The required zero limit is unproved;
Collatz remains unresolved.**

The preceding deficit notes concern the known basin of one and leave an
unbounded first moment open. The statistic here includes **every** source,
uses a finite clock, and stops accumulating when one is first reached.
Its normalization makes it bounded. Its limit detects the lost weight
outside the basin of one, including both escape and other cycles.
Neither a finite mean lifetime deficit nor uniform integrability of that
deficit is needed to identify this limit.

## 1. A fully finite statistic

Use the **ordinary** map `C(n)=n/2` for even `n`, and `3n+1` for odd
`n`. All clocks in this note are ordinary, unlike the shortcut clocks
in the most recent deficit notes. Use the ordinary weight `W_t(n)` from
[Weighted dissipation](WEIGHTED-DISSIPATION.md), with `W_0=1` and the
factor `3v/(3v+1)` at an odd input `v`.

Let `tau_1(n)` be first arrival at one, with value infinity if there is
no arrival. Set

\[
 z_t(n)=\mathbf1_{\{\tau_1(n)>t\}}(1-W_t(n)),\qquad
 A_T(n)=\sum_{0\le t<T}z_t(n).
                                                               \tag{1}
\]

Computing these quantities requires only the first `T` steps and an
arrival flag. A source still alive at the cutoff is not classified as
nonconvergent. In particular `z_t(1)=A_T(1)=0`, and

\[
 A_T(n)=\sum_{t<\min(T,\tau_1(n))}(1-W_t(n)),\qquad
                         0\le A_T(n)\le T.                    \tag{2}
\]

Here the minimum with infinity means `T`. For a source reaching one,
the statistic eventually stabilizes at its ordinary lifetime deficit.
It omits all losses on the known cycle after arrival.

For the finite hit flag `h_t=1_(tau_1<=t)`, the exact identity is

\[
                    z_t=1-h_t-W_t+h_tW_t.                     \tag{3}
\]

The final term cannot be dropped at finite clocks.

## 2. Which mass the statistic detects

Let `B` be the basin of one, `r_B` its natural density, and `mu` the
existing total-variation limit of the loss measures. Write

\[
 d=\mu(\{\infty\})=\lim_X\frac1X\sum_{n\le X}W_\infty(n),
 \qquad
 b=\mu(\{v>0:v\text{ odd},\ v\notin B\}).                    \tag{4}
\]

The letter `b` denotes a mass, not an orbit endpoint. A source in `B`
loses all its weight at odd states in `B`; a source outside `B` never
visits any such state. Therefore, exactly for each source,

\[
 \mu_n(B\cap\{\text{odd states}\})=\mathbf1_B(n),\qquad
 \mu_n(B^c\cap\{\text{odd states}\})
                 =\mathbf1_{B^c}(n)(1-W_\infty(n)).          \tag{5}
\]

Total variation permits evaluating these fixed sets, even though their
membership is not assumed decidable. It follows that

\[
 \boxed{b=1-r_B-d
      =\lim_X\frac1X\sum_{n\le X}
                     \mathbf1_{B^c}(n)(1-W_\infty(n)).}       \tag{6}
\]

Thus `0<=b<=1-r_B`. The quantity `d` measures unlost escape weight;
`b` instead measures lost weight on all nonconvergent components.
Its definition does not discard hypothetical additional cycles.

## 3. The bounded instantaneous limit

Put `kappa=3/log(4/3)`, using natural logarithms. The previously written
[minimum-clock theorem](CLOCKED-MINIMUM.md) and weight phase law give,
for fixed `c>=0`, `c!=kappa`, and `T_X=floor(c log X)`,

\[
 \frac1X\sum_{n\le X}\mathbf1_{\{\tau_1(n)\le T_X\}}
 \longrightarrow
 \begin{cases}0,&c<\kappa,\\r_B,&c>\kappa,\end{cases}
 \quad
 \frac1X\sum_{n\le X}W_{T_X}(n)
 \longrightarrow
 \begin{cases}1,&c<\kappa,\\d,&c>\kappa.\end{cases}            \tag{7}
\]

For `c<kappa`, the mean of `h_T W_T` is at most the hit proportion
and tends to zero. For `c>kappa`, choose `kappa<c'<c` and put
`S_X=floor(c' log X)`. On sources arriving by `S_X`, the ordinary
cycle `1,4,2` gives

\[
 W_{T_X}(n)\le(3/4)^{\lfloor(T_X-S_X)/3\rfloor}.
\]

The remaining arrived sources have proportion
`Pr(S_X<tau_1<=T_X)`, tending to `r_B-r_B=0`. Hence the mean
of `h_T W_T` also tends to zero in this case. Using (3),

\[
 \boxed{\frac1X\sum_{n\le X}z_{\lfloor c\log X\rfloor}(n)
       \longrightarrow b\,\mathbf1_{\{c>\kappa\}}.}          \tag{8}
\]

No value of the instantaneous limit at `c=kappa` is inferred.
All functions averaged here lie in `[0,1]`; no unbounded-moment
exchange has occurred.

## 4. Integrating the clock resolves the critical coefficient too

For `X>=2` integer and real `c>=0`, define

\[
 \Phi_X(c)=\frac1{X\log X}\sum_{n\le X}A_{\lfloor c\log X\rfloor}(n).
                                                               \tag{9}
\]

Set `f_X(u)=mean_(n<=X) z_floor(u log X)(n)`. Integrating the step
function over `[0,c]` gives

\[
 \left|\Phi_X(c)-\int_0^c f_X(u)\,du\right|\le1/\log X.
\]

Equation (8) holds at every `u` except the single possible critical
point, and `0<=f_X<=1`. Bounded dominated convergence therefore proves

\[
 \boxed{\Phi_X(c)\longrightarrow b(c-\kappa)_+
                          \quad\text{for every }c\ge0.}       \tag{10}
\]

This includes `c=kappa`, where the limit is zero regardless of the
unknown value of `b`. Moreover
`|Phi_X(c)-Phi_X(c')|<=|c-c'|+1/log X`. A finite mesh and the
Lipschitz continuity of the limiting function make (10) uniform on
every compact coefficient interval. A diagnostic run at or below the
critical coefficient cannot decide whether `b` is zero.

For comparison, if losses continue accumulating after arrival at one,
the same argument using only the weight limit in (7) gives

\[
 \frac1{X\log X}\sum_{n\le X}\sum_{t<\lfloor c\log X\rfloor}(1-W_t(n))
                  \longrightarrow(1-d)(c-\kappa)_+.           \tag{11}
\]

In particular, universal convergence would make the uncensored limit
positive above `kappa`. Omitting the arrival flag would test the wrong
condition. Conversely, restricting (9) to sources already known to
converge gives limit zero for every `c`, even if `b>0`. Below the
critical clock its integrand is bounded by the all-source integrand
in (8); above it, it is bounded by `Pr(n in B, tau_1(n)>T_X)`,
which tends to zero by (7). Bounded integration applies again.
Neither modified statistic can replace (9).

## 5. Relation to the full conjecture

The minimum distribution is tight under the same written inputs. Its
minimum is odd. For a nonconvergent source with minimum `m>1`, the
weight loses at least the fraction `1/(3m+1)` by its first odd step
from that minimum: if the weight there is `p<=1`, its later weight is
at most `p*3m/(3m+1)<=3m/(3m+1)`. Thus, writing `pi_m` for the
natural minimum density,

\[
 b\ge\sum_{1<m\le H}\frac{\pi_m}{3m+1}\quad(H\ge2).
\]

Since the minimum law has total mass one, this proves

\[
                         b=0\ \Longleftrightarrow\ r_B=1.     \tag{12}
\]

To pass from density one to **every** positive start, use the separately
external [positive predecessor-density theorem](PREDECESSOR-DENSITY-REVIEW.md).
Every nonconvergent orbit reaches a positive target `v` coprime to
three, and every predecessor of that target is also nonconvergent.
External positivity gives `r_v>0`, contradicting `r_B=1`. More
quantitatively, those predecessors have minimum at most `v`, so

\[
                         b\ge r_v/(3v+1)>0.                   \tag{13}
\]

Consequently, with the stated written and external inputs, for any
fixed `c>kappa` the following are equivalent:

* every positive integer reaches one;
* `b=0`;
* `Phi_X(c)->0`.

The last limit is **not proved**. This is a criterion for the full
conjecture, including cycle exclusion, not a proof of that criterion.
It is weaker than asking for a uniformly bounded unnormalized mean
deficit and does not assume a finite mean in the limiting deficit law.

There is an entirely integer-clock version. At `X=2^k`, set `T=8k`.
Then `c=8/log 2>kappa`: the elementary comparison
`(4/3)^8>2^3` is equivalent to `8 log(4/3)>3 log 2`.
Equation (10) becomes

\[
 \boxed{\frac1{k2^k}\sum_{n\le2^k}A_{8k}(n)
        \longrightarrow\left(8-\frac{3\log2}{\log(4/3)}\right)b.}
                                                               \tag{14}
\]

Every finite term in (14) is computable using exact rational arithmetic.
There is no effective convergence rate here, so a small finite value
does not certify the missing zero limit.

## Verification and next estimate

Run `python3 verify_censored_deficit_clock.py`. The
[record](../results/censored-deficit-clock/verification.json) separates
finite kernel algebra, independent ordinary-clock replay, and the written
bounded-integration argument. Existing analytic and external inputs keep
their original provenance; there is no fresh external source replay.

The next useful estimate is `sum_(n<=2^k) A_(8k)(n)=o(k2^k)` for
**all** sources. It includes unresolved trajectories through their finite
prefixes. The known-basin lifetime-deficit UI problem is a sufficient
route to some earlier drift bounds, but proving it alone would not
establish this all-source estimate. The direct pre-arrival bound and the
new zero-limit criterion both remain open.
