# Affine corrections stopped at count-gap boundaries

**Collatz remains unresolved.** Under the coherent binary residue law,
the first-return affine correction and returned separation have
square-root tails. Their moments therefore exist for every power below
`1/2`, improving the preceding range below `1/3`. This also gives an
explicit endpoint rate for truncating the separation-weighted return-image
density. The arguments involving probability, infinite stopping, and real
moments are **written**, with the integer inputs separately kernel checked.

## 1. Probability law and the bounded stopping identities

Use the setup of [count-return control](COUNT-RETURN-CONTROL.md).
The initial endpoints differ by an integer `D>0` and depend on a common
Haar binary input. Equivalently, all finite statements use coherent full
residue periods. Each endpoint's next parity is conditionally fair after
every finite prefix. The endpoints' parities are dependent. This is not
uniform sampling from a fixed finite interval for arbitrarily long times.

For each endpoint write its formal affine iterate as

\[
 U^t(X)=\lambda_tX+B_t,\qquad
 \lambda_t=3^{a_t}/2^t,\qquad B_0=0.
\]

These nonnegative real coefficients are determined by the finite parity
word, even when the source input is interpreted 2-adically. If the next
parity is `epsilon` and `m=3^epsilon/2`, then

\[
 \lambda_{t+1}=m\lambda_t,\qquad
 B_{t+1}=mB_t+\epsilon/2.
\]

Conditional fairness gives the exact identities

\[
 \mathbb E(\lambda_{t+1}\mid\mathcal F_t)=\lambda_t,
 \qquad
 \mathbb E(B_{t+1}\mid\mathcal F_t)=B_t+\tfrac14.       \tag{1}
\]

For any bounded stopping time `S`, summing (1) with the predictable
indicators `1_{S>t}` proves

\[
 \mathbb E\lambda_S=1,\qquad \mathbb EB_S=\tfrac14\mathbb ES.
                                                               \tag{2}
\]

No optional-stopping theorem with an unverified integrability hypothesis
is needed for this finite identity.

The [Lean module](../lean/ReturnCorrectionMoments.lean) identifies the
actual numerator `N_t=2^t U^t(n)-3^{a_t}n`, proves its one-step and lift
identities, and checks the two-child sum

\[
             N_{t+1}(r)+N_{t+1}(r+2^t)=4N_t(r)+2^t.
\]

It also proves (2) with denominators cleared for every finite binary
stopping tree. With fuel `h`, initial correction `N/d`, and clock numerator
`Q=2^h E S`, its correction numerator `P=d4^h E B_S` satisfies
`4P=4^(h+1)N+d2^h Q`. The corresponding stopped slope numerator equals
`4^h A`, starting from slope `A/d`. These are kernel arithmetic results;
the probabilistic interpretation and passage to an infinite tree are written.

## 2. Stop at zero or a count-gap boundary

Let `tau` be the first positive return of the odd-count difference to
zero. For odd `D`, the first step puts its absolute value at one. For an
integer `K>=1`, stop at physical time `sigma_K` when the embedded active
gap walk first reaches zero or `K`, including that initial step. For
`K=1`, `sigma_1=1`. The preceding
[square-root clock argument](COUNT-RETURN-CLOCK.md) proves

\[
 \Pr(\text{exit at }K)=1/K,\qquad
 \mathbb E\sigma_K\le9K-8.                                    \tag{3}
\]

On exit at zero, `sigma_K=tau`. The holding times are included in (3),
which is uniform in the initial separation and subsequent affine offsets.
In particular `sigma_K` is finite almost surely. If `D` is even,
`tau=1`; take `sigma_K=1` and declare no upper-boundary exit.

Apply (2) to `sigma_K` truncated at a deterministic integer `n`.
Fatou's lemma for nonnegative coefficients and monotone convergence for
the clock give

\[
 \mathbb EB_{\sigma_K}\le\tfrac14(9K-8),\qquad
 \mathbb E\lambda_{\sigma_K}\le1.                              \tag{4}
\]

Only inequalities are asserted at this unbounded stop. Uniform
integrability, or equality in (4), is not assumed.

For every real `L>=1`, the exceptional upper exit and Markov's inequality
now give, for either endpoint,

\[
 \Pr(B_\tau>L)\le\frac1K+\frac{9K-8}{4L}.
\]

Choose `K=floor(sqrt(L))+1`. Then `1/K<=L^(-1/2)` and
`9K-8<=9sqrt(L)+1`, so

\[
 \boxed{\Pr(B_\tau>L)\le\frac7{2\sqrt L}\quad(L\ge1).}          \tag{5}
\]

Integrating the tail, using probability at most one below `L=1`, yields

\[
 \boxed{\mathbb EB_\tau^\beta\le
       m_\beta:=1+\frac{7\beta}{1-2\beta}<\infty
                 \quad(0<\beta<1/2).}                         \tag{6}
\]

In particular `E B_tau^(1/4)<=9/2`. These estimates hold conditionally
at every count-return boundary. They require no independence of the
clock, the correction, or the two endpoints.

## 3. A direct tail for the returned separation

At `tau` both endpoints have the same slope `lambda_tau`. Their returned
integer separation `D'` satisfies

\[
             D'\le D\lambda_\tau+B^{(1)}_\tau+B^{(2)}_\tau.
                                                               \tag{7}
\]

Put `Z_t=D lambda_t^(1)+B_t^(1)+B_t^(2)`. This is nonnegative and
has conditional drift `1/2`. The same bounded-stop calculation and
Fatou argument prove

\[
                 \mathbb EZ_{\sigma_K}\le D+(9K-8)/2.
\]

On the lower exit, (7) bounds `D'` by `Z_sigma_K`. Consequently

\[
 \Pr(D'>L)\le\frac1K+\frac{D+(9K-8)/2}{L}
       \le\frac{D+6}{\sqrt L}\quad(L\ge1),                     \tag{8}
\]

using the same choice of `K`. For the adjacent initial pair, `D=1`,
this gives `Pr(D'>L)<=7/sqrt(L)`. This is an unconditioned full binary
law. Restricting its nonnegative sums to even, nonfused return prefixes
only decreases them.

## 4. A smaller explicit cycle budget

For `0<beta<1`, the slope power has conditional contraction

\[
 r_\beta=\tfrac12(2^{-\beta}+(3/2)^\beta)<1.
\]

Since `tau>=1`, bounded stopping of this nonnegative supermartingale
after time one, followed by Fatou, gives `E lambda_tau^beta<=r_beta`.
Subadditivity of the power in (7) and (6) therefore show

\[
 \mathbb E[(D')^\beta\mid D]\le r_\beta D^\beta+2m_\beta
                                      \quad(0<\beta<1/2).       \tag{9}
\]

The kernel-checked comparisons
`120^4<2*101^4` and `3*120^4<2*133^4` give `r_(1/4)<39/40`.
Thus, writing `V(D)=D^(1/4)`,

\[
                 \mathbb E[V(D')\mid D]\le\tfrac{39}{40}V(D)+9.
                                                               \tag{10}
\]

Take `R=400^4=25,600,000,000<2^35`. Outside `D<=R`, (10) gives
drift at most minus one. Stopping its finite partial sums shows that the
expected number of return cycles needed to reach this set is at most
`V(D)`, just as in the earlier count-return argument.

Reuse its kernel-checked prescribed descent paths. For even separation,
choose both endpoints even to obtain `D/2`. For odd separation, choose
the lower endpoint even, then keep its parity even while the offset
`c=(3D+1)/2` is even, and choose it odd once `c` is odd. The next return
has separation at most `(3D-1)/4`. Each prescribed bit has conditional
probability one half. Since `(3/4)^4<1/2`, from `D<2^35` these paths
fuse within `M=140` return cycles. Each cycle uses at most 37 bits,
because its positive initial offset is below `2^36`. Thus an attempt
succeeds with conditional probability at least

\[
                              p=2^{-5180}.                     \tag{11}
\]

Starting with `V<=400`, (10) keeps the expected `V` at every later cycle
at most 400: `(39/40)*400+9=399<=400`. Treat zero as absorbing. An
attempt of up to 140 cycles, followed on failure by return to `D<=R`,
therefore has conditional expected length at most `140+400=540`.
Every reached attempt succeeds with probability at least `p`, without
any assumption of independence. The probability of reaching attempt
`j` is at most `(1-p)^(j-1)`. Summing expected costs gives, from `D_0=1`,

\[
 \boxed{\mathbb EN\le C_{1/4}:=540\,2^{5180}<\infty.}            \tag{12}
\]

This replaces the much larger previous explicit constant. The physical
fusion clock still has infinite mean. Its existing upper tail can now
use `14 C_(1/4)/sqrt(H)`, and the energy estimate can use
`E_s<=28 C_(1/4) sqrt(ceil(121s/50))+23/4`. The growth exponent of that
estimate is unchanged; it does not prove a bounded energy subsequence.

Summing (9) through the absorbing cycle `N` gives the further written
budget

\[
 \mathbb E\sum_{j<N}D_j^\beta
      \le\frac{1+2m_\beta C_{1/4}}{1-r_\beta}<\infty
                          \quad(0<\beta<1/2),                  \tag{13}
\]

and, at `beta=1/4`, the bound `40(1+9 C_(1/4))`.

## 5. Consequences for returned-endpoint densities

Retain the notation `p_i,D_i,tau_i,F_i,K_beta,K_(beta,H)` from
[return-image bounds](RETURN-IMAGE-BOUNDS.md). The new separation
moments and the existing clock moments imply

\[
 \sum_i p_iD_i^\beta(1+\tau_i)^\alpha<\infty
     \quad\text{if }\beta\ge0,\ \alpha>0,\ \beta+\alpha<1/2.    \tag{14}
\]

For `beta>0`, choose `beta/(1-2alpha)<beta'<1/2` and use Hölder
exactly as before. For `beta=0`, use the clock moment alone. The previous
Jensen proof then gives `K_beta in L(log L)^alpha` under ternary Haar
measure throughout this larger region. Its absolute-continuity and
finite-integer-interval estimates keep their original forms. This
does not assert an `L^p` density bound for any `p>1`.

There is also an endpoint improvement to the clock-truncation rate.
For `0<beta<1/2` and real `H>=1`, tail integration and the two bounds
`Pr(tau>H)<=7/sqrt(H)` and `Pr(D'>u)<=7/sqrt(u)` give

\[
\begin{split}
 \mathbb E[(D')^\beta\mathbf1_{\{\tau>H\}}]
 &=\int_0^\infty\beta u^{\beta-1}
                  \Pr(D'>u,\tau>H)\,du\\
 &\le7H^{\beta-1/2}
           +7\beta\int_H^\infty u^{\beta-3/2}\,du\\
 &=\frac7{1-2\beta}H^{\beta-1/2}.
\end{split}
\]

For `beta=0`, use the clock tail directly on nonfused prefixes. Therefore

\[
 \boxed{\|K_\beta-K_{\beta,H}\|_{L^1(\mu_3)}
       \le\frac7{1-2\beta}H^{\beta-1/2}
             \quad(0\le\beta<1/2,\ H\ge1).}                   \tag{15}
\]

No independence is used in this integration. The ternary conditional
expectation at depth `L>=1` consequently satisfies
`||K_beta-E[K_beta|depth L]||_1<=14 L^(beta-1/2)/(1-2beta)`, since
each returned cylinder has depth `a_i<=tau_i` and conditional expectation
contracts `L^1`.

The earlier unweighted logarithmic quarter-moment constants 80 and 82
remain valid. Passing to an infinite return depth on a fixed integer
interval, or pairing the transported density with the actual future
weighted gradients, remains unproved. These estimates do not exclude
escaping trajectories or additional positive cycles.

## 6. Verification boundary

Run `python3 verify_return_correction_moments.py`. The
[verification record](../results/return-correction-moments/verification.json)
separates twelve new kernel arithmetic roots, fresh sequential builds,
independent exact finite stopping-law checks, and the written arguments
above. It authenticates earlier clock, control, and image records without
rewriting their hashed sources.

The finite replay checks both endpoints and the slope on actual stopped
residue trees, directly recomputes selected affine trajectories, checks
the drift constants, and replays the prescribed fusion paths. No finite
check proves the all-depth probability or real-analysis conclusions.
No native evaluation, floating arithmetic, or new external theorem is
used in this verification.
