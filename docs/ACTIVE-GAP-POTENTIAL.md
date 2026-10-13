# A bounded potential at active count-gap steps

**Collatz remains unresolved.** A written stopping argument extends the
returned affine-correction moments to every power below one. It yields

\[
 \boxed{K^*_\beta\in L^p(\mu_3),\qquad
       0\le\beta<1,\qquad 1\le p<\frac5{4+\beta}.}             \tag{1}
\]

In particular, the unweighted range improves from `p<6/5` to `p<5/4`.
This uses the project's coherent binary residue law and no new external
stationary-density, mixing, or predecessor theorem. The actual-gradient
pairing and infinite-cutoff sampling on ordinary integer intervals remain
open. Neither escape nor other positive cycles are excluded.

[ActiveGapPotential.lean](../lean/ActiveGapPotential.lean) proves nine
arithmetic roots for the finite Green potential, geometric sums, and
explicit slope constants. Probability, stopping, fractional powers,
Haar integration, and the infinite-density consequence remain **written**.

## 1. One active block has integrable correction

Work conditionally at any binary prefix with nonzero absolute odd-count
gap `d>=1`. Orient the lower-count endpoint as `X`; the other endpoint
has the form `Y=3^d X+c`. The fresh binary parameter makes `X` Haar-uniform
on the binary integers. The two endpoints' parities are each fair, but
they are not independent.

Let `W>=1` be the number of physical steps up to and including the next
active step, namely the next step whose two endpoint parities differ.
The [count-return clock argument](COUNT-RETURN-CLOCK.md) proves

\[
 \mathbb E[W\mid\text{prefix}]\le v(d)+2,
 \qquad v(d)=v_2(3^d-1),                                    \tag{2}
\]

uniformly in the offset `c`. The next gap is `d-1` or `d+1` with equal
conditional probabilities. Equation (2) is an expectation bound, not a
deterministic upper bound on the wait.

For either endpoint, write the continuation's affine coefficients as
`lambda_s,b_s`, with `lambda_0=1,b_0=0`. For `0<eta<1`, put

\[
 r_\eta=\tfrac12(2^{-\eta}+(3/2)^\eta)<1.
\]

The slope power is a nonnegative supermartingale. Since `W>=1`, apply
bounded stopping after time one to `W wedge m`, for `m>=1`, and then
Fatou. The bounded correction identity already proved in
[RETURN-CORRECTION-MOMENTS.md](RETURN-CORRECTION-MOMENTS.md) gives
`E b_(W wedge m)=E(W wedge m)/4`. Fatou and monotone convergence yield

\[
 \mathbb E\lambda_W^\eta\le r_\eta,\qquad
 \mathbb E b_W\le\tfrac14\mathbb E W\le\tfrac14(v(d)+2).
 \tag{3}
\]

Only an inequality is asserted at the unbounded stop. Concavity gives

\[
 \mathbb E b_W^\eta\le((v(d)+2)/4)^\eta\le d+3.              \tag{4}
\]

For the last, even the elementary `v(d)<2d` suffices: use
`2^v(d)<=3^d-1<4^d`, and `x^eta<=max(1,x)` for `x>=0`.
All statements (2)--(4) are conditional on the current prefix. Neither
the wait, the active sign, nor the two continuation coefficients need be
independent.

## 2. The Green potential pays for the active-block cost

Choose `r_eta<q<1` and define, for natural `d`,

\[
 h_q(d)=2\sum_{j\ge1}\min(d,j)q^{j-1}(j+3).                 \tag{5}
\]

The summands are nonnegative. Geometric summation gives

\[
 h_q(0)=0,\quad 0\le h_q(d)\le\frac{8-4q}{(1-q)^3},\qquad
 h_q(1)=\frac{8-6q}{(1-q)^2}.                               \tag{6}
\]

The exact closed form is

\[
 h_q(d)=\frac{8-4q-2q^d((d+4)-(d+2)q)}{(1-q)^3}.            \tag{7}
\]

For `d>=1`, the elementary curvature of `min(d,j)` gives

\[
 \frac{h_q(d-1)+h_q(d+1)}2
       =h_q(d)-q^{d-1}(d+3).                               \tag{8}
\]

The new kernel lemmas prove the finite-sum curvature, its boundary and
cap, and denominator-cleared geometric identities with nonnegative
remainders. The geometric limits and their real-valued interpretation
are written steps. The factor two in (5) is needed for (8).

Let `B>=0` be the cumulative correction so far for one fixed endpoint.
Across the next active block,

\[
                  B'=\lambda_W B+b_W,\qquad d'=d\pm1.
\]

Define `F(B,d)=q^d B^eta+h_q(d)`. Because `q^(d')<=q^(d-1)`,
subadditivity of the power and (3)--(4) imply

\[
 \begin{aligned}
 \mathbb E[q^{d'}(B')^\eta\mid\text{prefix}]
 &\le q^{d-1}(r_\eta B^\eta+d+3)\\
 &\le q^d B^\eta+q^{d-1}(d+3).
 \end{aligned}                                             \tag{9}
\]

Conditional fairness of the active sign gives (8) for the expected
`h_q(d')`. Adding it to (9) cancels the waiting cost:

\[
            \mathbb E[F(B',d')\mid\text{prefix}]\le F(B,d).
 \tag{10}
\]

This estimate does not factor an expectation of correlated quantities.
The crude bound on `q^(d')` is what permits their dependence.

## 3. Stop at the first count return

Freeze the process when its gap first reaches zero, and sample `F` at
successive active epochs. It is a nonnegative supermartingale. For every
fixed number of active blocks it is integrable: the gap is bounded by
its initial value plus that number, and (3)--(4) bound the next
conditional moment. Iterating (10) at a finite active-step cutoff is
therefore justified.

The fair embedded gap walk hits zero almost surely from every finite `d`.
Indeed, stopping it at zero or `K>d` gives upper-exit probability `d/K`;
it exits this finite interval almost surely. Never hitting zero would
require the upper exit for every `K`, an event of probability at most
`d/K` for every `K`, hence zero. Each active wait is finite almost surely
by (2). Thus the physical return time is also finite almost surely,
consistent with the previous clock-tail bound for fresh cycles.
At the return, `q^0=1` and `h_q(0)=0`.
Fatou at increasing **active-step cutoffs** gives

\[
       \mathbb E B_{\rm return}^\eta\le q^d B^\eta+h_q(d).
 \tag{11}
\]

This uses no unverified equality at an unbounded stopping time, no fixed
maximum wait, and no integrability of the full physical return clock.

For a fresh cycle from equal counts and positive integer separation `D`,
an even `D` returns in one step, with `E b_1^eta=2^(-eta-1)`. An odd `D`
departs to absolute gap one in one step. Applying (11) conditionally
after that step gives, for either endpoint,

\[
 \mathbb E b_\tau^\eta\le q2^{-\eta-1}+h_q(1)
                         \le b_\eta:=1+h_q(1).               \tag{12}
\]

The same `b_eta` also bounds the even case. The old nonnegative-slope
argument still gives `E lambda_tau^eta<=r_eta`. Both bounds are uniform
in `D` and valid conditionally at every fresh return prefix, for all
`0<eta<1`.

For concrete constants, the kernel inequalities give

| `eta` | strict slope cap | choice of `q` | `b_eta=1+h_q(1)` |
| --- | --- | --- | --- |
| `1/2` | `31/32` | `63/64` | `8577` |
| `3/4` | `63/64` | `127/128` | `33537` |
| `7/8` | `127/128` | `255/256` | `132609` |

These constants prioritize a transparent bound. For powers below one
half the previous correction estimate can be smaller.

## 4. Moments over all nonfused returns

Keep `S_j,D_j,N` from the occupation note, with `S_0=0,D_0=1` and
balanced fusion at return index `N`. Keep the existing bound

\[
                  \mathbb EN\le C_*:=540\,2^{5180}.
\]

The cumulative formal coefficient `C_t=lambda_t+B_t` starts at one
and composes as `C_next=lambda C_current+b`. Equations (12) and
subadditivity give, before fusion,

\[
 \mathbb E[C_{S_{j+1}}^\eta\mid\mathcal F_{S_j}]
          \le r_\eta C_{S_j}^\eta+b_\eta.                    \tag{13}
\]

At a count return the endpoint slopes agree and
`D_next<=lambda D_current+b^(1)+b^(2)`, giving

\[
 \mathbb E[D_{j+1}^\eta\mid\mathcal F_{S_j}]
          \le r_\eta D_j^\eta+2b_\eta.                      \tag{14}
\]

Kill each moment at fusion. Finite telescoping, dropping nonnegative
terminal terms, and monotone convergence prove

\[
 \boxed{\mathbb E\sum_{j<N}C_{S_j}^\eta
       \le\frac{1+b_\eta C_*}{1-r_\eta},\qquad
 \mathbb E\sum_{j<N}D_j^\eta
       \le\frac{1+2b_\eta C_*}{1-r_\eta}<\infty,
                      \quad0<\eta<1.}                       \tag{15}
\]

The earlier kernel drift-budget lemma supplies the finite arithmetic.
The occupation measure `nu` counts only `1<=j<N`; restricting further
to even initial inputs reduces every nonnegative integral. No conditional
fairness of the first bit is asserted after imposing that restriction.

For later use, these constants can be bounded as `eta` approaches one.
The function `1-r_eta` is concave, vanishes
at one, and its value at one half exceeds `1/32`. Thus

\[
 1-r_\eta\ge(1-\eta)/16\quad(1/2\le\eta<1).
\]

Choose `q=1-(1-eta)/32`, which is strictly between `r_eta` and one.
Since `1-q=(1-eta)/32` and `8-6q<=8`,
`b_eta<=8193/(1-eta)^2`. Both bounds in (15) are at most

\[
 \frac{\mathcal B}{(1-\eta)^3},\qquad
                  \mathcal B=16(1+16386C_*).                 \tag{16}
\]

For `u>=4`, choose `eta=1-1/log_2(u)` and apply Markov:

\[
 \nu(C>u),\ \nu(D>u)\le\frac{2\mathcal B(\log_2 u)^3}{u},
 \qquad
 \Pr(b_\tau>u)\le\frac{16386(\log_2 u)^2}{u}.               \tag{17}
\]

No first moment at the endpoint `eta=1` is asserted.

## 5. Density range and weighted clock truncation

Reuse the fractional fixed-count fibre bound and parity-count concentration
from [RETURN-AFFINE-BUDGET.md](RETURN-AFFINE-BUDGET.md). Put `alpha=p-1`.
Its typical dyadic block estimate now applies for `alpha<eta<1`:

\[
 \|\Delta_H\|_p^p\ll_{p,\eta}
 H^{3\alpha/2-1/2+\alpha/(2\eta)}
 (1+\log(H+1))^{\alpha/2+1-\alpha/\eta}.                     \tag{18}
\]

One can choose `alpha/(1-3alpha)<eta<1` exactly when `alpha<1/4`.
Then the power of `H` is negative, making the dyadic norms summable.
The atypical clock components satisfy the same prior bound
`||psi_t||_p^p << (t+2)^(17alpha-8)`; its norms remain summable because
`(17alpha-8)/p<-1` throughout `0<alpha<1/4`. Finite Minkowski and
monotone convergence yield `K*_0 in Lp` for `1<p<5/4`. Finite occupation
mass covers `p=1`.

For `0<=beta<gamma<1`, positivity of the columns and Holder give
`K*_beta <= (K*_0)^(1-beta/gamma)(K*_gamma)^(beta/gamma)`.
Equation (15) makes `K*_gamma` integrable. Taking the unweighted power
arbitrarily close to `5/4` and `gamma` arbitrarily close to one gives
(1). Each application uses strictly subcritical exponents; no endpoint
norm is assumed.

This component-counting argument has limiting dyadic power
`2alpha-1/2` as `eta` increases to one. Improving its range past `5/4`
would require an additional estimate on overlap or on joint clock and
coefficient tails. The present range is not asserted to be optimal.

The same moments also control weighted clock truncation. For
`0<=beta<eta<1`,

\[
 \|K^*_\beta-K^*_{\beta,H}\|_1
 =\int_{S>H}D^\beta\,d\nu
 \le M_\eta^{\beta/\eta}\nu(S>H)^{1-\beta/\eta},              \tag{19}
\]

where `M_eta=(1+2b_eta C_*)/(1-r_eta)`. The existing unweighted clock
tail is `O(H^(-1/2)(1+log H))`. Choosing
`eta=1-1/log_2 H>beta` for sufficiently large `H`, and using (16), gives

\[
 \boxed{\|K^*_\beta-K^*_{\beta,H}\|_1
       =O_\beta\!\left(H^{-(1-\beta)/2}
                     (1+\log H)^{1+2\beta}\right),
                    \quad0\le\beta<1.}                     \tag{20}
\]

Indeed the unsimplified powers are `H^(-(1-beta/eta)/2)` and
`(log H)^(1+2beta/eta)`. Their ratios to the displayed powers stay
bounded: `(1-eta)log H=log 2`, and
`(1-eta)log log H` is bounded. Constants may depend on fixed `beta`.

For the unweighted gradient pairing, a complementary power strictly
above five could now suffice, instead of strictly above six. No such
uniform bound for the actual accumulated gradients is established.
The ternary Haar norms still give only the existing truncated integer
transfer with its `1+3^H/M` factor. They do not yield an infinite-cutoff
trace estimate on a fixed ordinary integer interval.

## 6. Verification scope

Run `python3 verify_active_gap_potential.py`. The
[record](../results/active-gap-potential/verification.json) separates the
nine kernel arithmetic roots from exact finite checks and the written
analytic argument. The finite checks retain unfinished active blocks and
return cycles as unfinished; they do not identify a clock cutoff with a
completed return. They verify bounded-stop correction and slope identities,
active-sign balance, Green curvature and geometric tails, partial terminal
potential inequalities, and cumulative finite return moments. Fractional
powers use outward integer-root enclosures, with no floating decisions.

The kernel file does not formalize stochastic processes or the infinite
moment theorem. Finite experiments, including exponents at the boundary
when explicitly tested, are not extrapolated to infinite integrability.
The all-depth real-valued deductions are the written proofs above.
