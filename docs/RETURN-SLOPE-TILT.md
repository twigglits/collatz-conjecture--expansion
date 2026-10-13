# Exact return slopes and the critical first moment

**Collatz remains unresolved.** Under the coherent binary residue law,
the first positive count return has an exact mean slope and a sharp
first-moment obstruction. For a fresh positive separation `D`,

\[
 \boxed{\mathbb E\lambda_\tau=
       \begin{cases}1&D\text{ even},\\1/2&D\text{ odd}.
       \end{cases}}                                         \tag{1}
\]

For odd `D`, the value `1/2` also holds conditional on either first input
parity. Label the initially odd endpoint `F` and the initially even one
`S`. Throughout the excursion, `F` has the larger cumulative odd count.
Writing their returned corrections as `b_F,b_S`, we prove

\[
 \boxed{\mathbb E b_F\le5/4,\qquad
        \mathbb E b_S=\infty,\qquad
        \mathbb E D_{\rm next}=\infty.}                     \tag{2}
\]

All powers strictly below one remain integrable. The new quantitative
bound, for either endpoint and every fresh separation, is

\[
 \boxed{\mathbb E b_\tau^\eta\le\frac{72}{1-\eta}
                    \quad(1/2\le\eta<1).}                   \tag{3}
\]

This improves the previous quadratic blow-up in `1/(1-eta)`. It sharpens
the occupation tails to `O((log u)^2/u)` and proves that the separation
weight range `beta<1` is necessary for Haar integrability of `K*_beta`.
It does not prove the optimal `Lp` exponent in that range.

These are **written probability and real-analysis arguments**. Nine
kernel arithmetic roots and exact finite tests support them. No external
theorem is used. The probability law is the coherent full binary residue
law, not a fixed finite integer interval continued forever. An infinite
expectation here does not assert divergence of any positive orbit.

## 1. Tilting by one endpoint's affine slope

Condition on a finite pair prefix. Each endpoint's next parity is fair,
and its two high-bit children have opposite parities. The XOR of the
two endpoint parities is already fixed before the fresh bit: both
parities flip together. Thus whether the next step changes the count gap
is predictable; its direction uses the fresh bit.

For one chosen endpoint, its continuation slope `lambda_t` is a positive
martingale, since its multiplier is `1/2` or `3/2` with probabilities
`1/2,1/2`. Weighting each finite prefix by `lambda_t` defines a consistent
probability law. Under that law the chosen endpoint's next parity is
odd with probability `3/4` and even with probability `1/4`, conditionally
on the entire past. This uses neither independent endpoint parities nor
independent holding times.

At a nonzero absolute count gap `k`, the endpoint difference has the
form `(3^k-1)X+c`. Holding for `h` steps is equivalent to its divisibility
by `2^h`. If `v(k)=v_2(3^k-1)`, there are at most `2^v(k)` such source
residues modulo `2^h`. The same count applies to either endpoint, since
their affine relation has odd slope. Under the tilted law, any specified
length-`h` parity word has probability at most `(3/4)^h`. Hence

\[
 \Pr_{\rm tilt}(\text{at least }h\text{ holds}\mid\text{prefix})
             \le\min\{1,2^{v(k)}(3/4)^h\}\longrightarrow0.   \tag{4}
\]

Every active step therefore occurs in finite physical time under the
tilt as well. This check is essential: an unbounded stopping equality
cannot be inferred from the original slope martingale alone.

Until the counts agree, let `k>=1` be the count lead of `F` over `S`.
Under the `F` slope tilt, the active walk goes outward with probability
`3/4`; under the `S` tilt, it goes inward with probability `3/4`.
For the respective probabilities of ever reaching zero,

\[
                  h_F(k)=3^{-k},\qquad h_S(k)=1.             \tag{5}
\]

To see this without a recurrence boundary assumption at infinity, stop
at `0` or `K>k`. The two zero-hit probabilities are

\[
 \frac{3^{K-k}-1}{3^K-1},\qquad
 \frac{3^K-3^k}{3^K-1}.                                    \tag{6}
\]

The kernel checks the finite boundaries and biased harmonic equations.
Finite-interval exit is almost sure, and the finite maximum principle
identifies (6). Letting `K` increase gives (5). Equation (4) makes the
active and physical hitting events agree.

For a future count-return time `sigma`, summing its disjoint finite
stopping cylinders gives the exact change-of-measure identity

\[
 \mathbb E[\lambda_\sigma\mathbf1_{\{\sigma<\infty\}}
                    \mid\text{prefix}]
       =\Pr_{\rm tilt}(\sigma<\infty\mid\text{prefix}).      \tag{7}
\]

Under the original law `sigma` is almost surely finite, by the existing
fair-gap and holding-time argument. Thus its expected continuation slope
is exactly (5). Equation (7) is a sum of nonnegative terms; it does not
assume uniform integrability at an unbounded stop.

## 2. The fresh-cycle slope

If `D` is even, the first step has equal endpoint parities and already
returns the counts, so `tau=1` and the unconditioned mean slope is one.
For odd `D`, the first step creates gap one. Conditional on that first
bit, the two slope calculations are

\[
 \mathbb E\lambda_\tau^{(S)}=(1/2)h_S(1)=1/2,\qquad
 \mathbb E\lambda_\tau^{(F)}=(3/2)h_F(1)=1/2.                \tag{8}
\]

The returned slopes are the same pathwise, because the final counts
agree. This proves (1), including the conditional odd-separation version.
Concavity also gives the stronger fractional slope bound

\[
       \mathbb E\lambda_\tau^\eta\le2^{-\eta}
           \quad(0<\eta<1,\ D\text{ odd}).                   \tag{9}
\]

For even separations the one-step fractional mean remains
`r_eta=(2^-eta+(3/2)^eta)/2`. Thus (9) alone does not replace the uniform
all-separation drift factor by a constant bounded away from one.

## 3. Correction contributions and the first-moment obstruction

An odd step adds `1/2` before multiplication by the remaining slope.
For either endpoint, pathwise at the finite return time,

\[
 b_\tau=\frac12\sum_{0\le j<\tau}
       \mathbf1_{\{j\text{th input odd}\}}
       \lambda_{j+1,\tau}.                                 \tag{10}
\]

Tonelli and (5)--(7) evaluate each contribution by the count gap just
after that step. No subtraction of infinite expectations is used.

Under the original law, the active gap is a fair walk from one killed
at zero. The expected number of visits to each `k>=1` is two: the finite
Green value `2(K-k)/K` increases to two. The next active direction is
fair after every such visit. Consequently the expected number of inward
active steps from each `k` is one.

Each inward active step is odd for `S`, and its remaining expected slope
is `h_S(k-1)=1`, including the terminal step. Its correction contribution
has expectation `1/2`. Summing over the infinitely many levels gives

\[
                  \mathbb E b_S\ge\frac12\sum_{k\ge1}1
                              =\infty.                      \tag{11}
\]

For `F`, the initial odd step contributes `(1/2)h_F(1)=1/6` in expectation.
At a visit to gap `k`, let `W` include the next active step. The previous
local holding estimate gives `E W<=v(k)+2`. Holding is predictable and
each fresh parity is fair, so the expected number of odd holding steps
is half the expected number of holds. Each such odd correction is
multiplied in expectation by `3^-k`. An outward active step is odd for
`F`, with probability `1/2`, and has remaining mean `3^(-k-1)`.
Thus the expected correction cost per visit is at most

\[
                  \frac14\,3^{-k}(v(k)+4/3).
\]

Using the Green value two and `v(k)<2k`,

\[
 \mathbb E b_F\le\frac16+\frac12\sum_{k\ge1}3^{-k}(2k+4/3)
                =\frac54.                                 \tag{12}
\]

The kernel checks the denominator-cleared partial geometric identity
and its nonnegative-remainder cap. Its infinite limit is written.

Let `D_next` be the absolute endpoint separation at return. The two
affine representations, whose slopes agree, imply pathwise

\[
                     b_S\le D_{\rm next}+b_F+\lambda_\tau D.
\]

Since `E b_F<=5/4` and `E lambda_tau=1/2`, (11) forces
`E D_next=infinity`, proving (2). This holds for every odd positive `D`
and conditional on either first parity.

## 4. A fractional root controls the remaining slope

Fix `0<eta<1`, and write

\[
 a=\tfrac12(3/2)^\eta,\quad b=\tfrac12(1/2)^\eta,
 \quad r_\eta=a+b<1,
\]
\[
 z=\frac{1-\sqrt{1-4ab}}{2b}
   =2^\eta\{1-\sqrt{1-(3/4)^\eta}\},\qquad
 z_F=\frac ba z=3^{-\eta}z.                                \tag{13}
\]

The smaller root satisfies `0<z<1`, `0<z_F<1`, and

\[
                   a/z+bz=1,\qquad b/z_F+az_F=1.             \tag{14}
\]

For the endpoint `S`, the process `lambda_t^eta z^(k_t)`, stopped when
`k_t=0`, is a nonnegative supermartingale. At a holding step the expected
multiplier is `r_eta<1`; at an active step (14) gives equality. For `F`
use `z_F` and the second identity. Bounded physical stopping and Fatou
give, from any prefix at gap `k`,

\[
 \mathbb E\lambda_{\rm return}^{\eta,(S)}\le z^k,
 \qquad
 \mathbb E\lambda_{\rm return}^{\eta,(F)}\le z_F^k.           \tag{15}
\]

Again, active direction and holding time need not be independent.

## 5. Improving the correction moment to a simple pole

Raise the finite sum (10) to power `eta`, using subadditivity, and
apply (15) term by term. For `S`, at gap `k` the odd holds cost at most
`2^(-eta-1)(v(k)+1)z^k` per visit; an inward active step costs
`2^(-eta-1)z^(k-1)`. Summing the Green value two gives

\[
 \mathbb E b_S^\eta
 \le2^{-\eta}\sum_{k\ge1}
                 \{(v(k)+1)z^k+z^{k-1}\}.                   \tag{16}
\]

The previous valuation-mass bound is
`sum_(k=1)^N (v(k)+2)<=9N/2`. Nonnegative summation by parts yields

\[
 \sum_{k\ge1}(v(k)+2)z^k\le\frac{9z}{2(1-z)},
\]

and therefore

\[
 \mathbb E b_S^\eta
       \le2^{-\eta}\frac{1+(7/2)z}{1-z}
       \le\frac{9}{2(1-z)}.                                \tag{17}
\]

The root equation gives the factorization

\[
             1-r_\eta=(1-z)\{1-b(1+z)\}\le1-z.             \tag{18}
\]

For `eta>=1/2`, the previously established chord estimate is
`1-r_eta>=(1-eta)/16`. Thus (17) is at most `72/(1-eta)`.
For `F`, Jensen applied to (12) gives `E b_F^eta<=(5/4)^eta<=5/4`.
Even separations return in one step and have correction at most `1/2`.
This proves the uniform fresh-cycle bound (3).

The divergent first moment in (11) is consistent with this simple pole;
the proof does not substitute `eta=1` into (16) or (17).

## 6. Occupation tails and the separation endpoint

Keep the earlier occupation measure `nu`, cumulative formal coefficient
`C=lambda+B`, separation `D`, and `C_star=540*2^5180>=E N`.
Use (3) in the existing killed-return drift argument. For `1/2<=eta<1`,

\[
 \int C^\eta\,d\nu,\quad\int D^\eta\,d\nu
       \le\frac{B_*}{(1-\eta)^2},
       \qquad B_*=16(1+144C_*).                             \tag{19}
\]

This uses the old all-separation slope factor `r_eta`; the improvement
comes from the correction cost. Taking `eta=1-1/log_2 u`, for `u>=4`,
gives

\[
 \Pr(b_\tau>u)\le\frac{144\log_2u}{u},\qquad
 \nu(C>u),\ \nu(D>u)\le\frac{2B_*(\log_2u)^2}{u}.           \tag{20}
\]

Holder against the existing `O(H^-1/2 log H)` occupation-clock tail,
with `eta=1-1/log H>beta` for sufficiently large `H`, improves the
weighted truncation estimate to

\[
 \|K^*_\beta-K^*_{\beta,H}\|_1
  =O_\beta\!\left(H^{-(1-\beta)/2}(1+\log H)^{1+\beta}\right),
                \qquad0\le\beta<1.                         \tag{21}
\]

The previously proved range `K*_beta in Lp` for
`1<=p<5/(4+beta)` is unchanged.

There is now a genuine endpoint exclusion. Start the original adjacent
pair with its first member even, so it is the endpoint `S` and `D=1`.
At its first positive count return, (2) gives an infinite mean separation.
Fusion contributes separation zero, so removing fused paths preserves
that infinite mean. On fusion, `b_S=lambda_tau+b_F`, whose mean is finite;
removing those paths also leaves an infinite mean of `C=lambda_tau+b_S`.
Consequently, for the same even-source occupation used by our columns,

\[
                    \int D\,d\nu=\int C\,d\nu=\infty.       \tag{22}
\]

Every nonfused return has integer `D>=1`. Tonelli and the unit Haar mass
of each column therefore imply

\[
                \boxed{K^*_\beta\notin L^1(\mu_3)
                                   \quad(\beta\ge1).}        \tag{23}
\]

The permitted separation range `beta<1` is thus sharp for Haar
integrability. No optimality of the separate density exponent `p` is
claimed, and no ordinary-integer divergence follows from (22)--(23).

## Verification and remaining problem

Run `python3 verify_return_slope_tilt.py`. The
[record](../results/return-slope-tilt/verification.json) distinguishes
nine kernel roots, exact finite biased-walk systems, direct finite
Collatz stopping trees, rational power enclosures, and the written
infinite arguments. It retains unresolved paths at every finite clock;
growing finite partial means are not used to prove an infinite mean.
That conclusion comes from the change of measure and Green argument.

These results identify the critical moment and improve the existing
tail bounds. They do not pay for the actual forward-gradient costs
after a return. The temporal criterion `Q`, escape exclusion, additional
cycle exclusion, and full positive-integer Collatz remain open.
