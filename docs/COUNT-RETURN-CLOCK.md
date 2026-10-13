# A square-root bound for the count-return clock

**Collatz remains unresolved.** The first positive count-return time has
tail at most `7/sqrt(H)`, uniformly in the starting separation. Together
with the previous finite expected number of return cycles, this gives
balanced noncoalescence of order `H^(-1/2)` and actual refinement energy
`E_s = O(sqrt(s))`. The earlier lower bound has the same square-root order
for the coalescence-only energy certificate. Bounded actual energy and
the exclusion of other positive cycles remain unproved.

[CountReturnClock.lean](../lean/CountReturnClock.lean) proves fifteen
arithmetic roots: exact odd cofactors, their nondivisibility by the next
power of two, a valuation-sum bound, and finite Green-function equations.
The probability, real-analysis, and endpoint-sampling arguments below are
**written proofs**, not complete Lean formalizations. No new external
theorem is adopted.

## 1. The delay at an active count gap

Use the coherent uniform binary input law and the notation of
[count-return control](COUNT-RETURN-CONTROL.md). This law is Haar measure
on binary inputs, equivalently uniform complete residue periods. It is
not a law for a finite integer interval continued indefinitely.

Start with equal counts and integer endpoint separation `D>0`, and let
`tau` be their first positive count return. If `D` is even, `tau=1`.
If `D` is odd, one step produces absolute count gap one. At a nonzero
gap `d`, orient the lower-count endpoint as `X`, and write

\[
                         Y=3^dX+c.
\]

Conditioned on any finite prefix, `X` is Haar-uniform. The previous
holding congruence gives, for the number `R` of holding steps before the
next active step,

\[
 \Pr(R\ge h\mid\text{prefix})
 \le\min\{1,2^{v(d)-h}\},\qquad v(d)=\nu_2(3^d-1).
\]

Consequently the physical wait `W=R+1` obeys

\[
                    \mathbb E[W\mid\text{prefix}]\le v(d)+2.       \tag{1}
\]

The bound is uniform in `c`. Each next active step has a fresh fair
sign, so the embedded gap is a simple symmetric walk from one until
absorption at zero. Independence between waits and past states is not
required.

The sharper arithmetic input is

\[
 v(d)=
 \begin{cases}
 1,&d\text{ odd},\\
 2+\nu_2(d),&d\text{ even}.
 \end{cases}                                                     \tag{2}
\]

Here is a proof using the kernel cofactors. For odd `u`,
`3^u = 3 (mod 8)`, so `3^u-1` has exactly one factor of two and
`3^(2u)-1` has exactly three. If `n=1+2^e q`, with `e>=2` and `q`
odd, then

\[
 n^2=1+2^{e+1}\bigl(q+2^{e-1}q^2\bigr),
\]

and the new cofactor is odd. Iterating proves that `3^(2^(j+1)u)-1`
has exactly `j+3` factors of two. The kernel proves these identities and
the failure of divisibility by the next power. Decomposing positive `d`
into a power of two times an odd number gives (2).

For `n>=0`, counting multiples of each power of two gives

\[
 \sum_{d=1}^{n}\nu_2(d)
   =\sum_{r\ge1}\left\lfloor\frac n{2^r}\right\rfloor
   =:B(n)\le n.                                                  \tag{3}
\]

The count is a finite double sum. Its identification with valuations is
written; the kernel defines the right side by repeated halving and
proves `B(n)<n` for `n>0`. By (2), the total wait bound is

\[
 C(n):=\sum_{d=1}^{n}(v(d)+2)
      =3n+\lfloor n/2\rfloor+B(n),\qquad
                         2C(n)\le9n.                             \tag{4}
\]

Thus large delays at individual gaps do not make their sum over a gap
interval superlinear. Equation (4), rather than a worst-state bound,
is the improvement over the earlier clock estimate.

## 2. Stop the walk at a height boundary

Fix an integer `K>=1`. After the initial departure, stop at the first
active visit to either `0` or `K`. Include the initial step in its
physical clock `sigma_K`. If `K=1`, stop immediately at that step.
For the embedded walk,

\[
 \Pr(\text{exit at }K)=\frac1K,
 \qquad
 G_K(1,d):=\mathbb E[\text{visits to }d\text{ before exit}]
          =\frac{2(K-d)}K\quad(1\le d<K).                          \tag{5}
\]

These formulas can be checked without an infinite-walk estimate. The
exit function `d/K` is harmonic with boundary values zero and one.
For the Green function, set `g_0=g_K=0` and `g_d=2(K-d)/K` in the
interior. Then

\[
               2g_d=g_{d-1}+g_{d+1}+2\mathbf1_{d=1}.
\]

The finite killed walk exits almost surely: from every interior state,
`K` consecutive downward choices have probability `2^(-K)` and force
exit. Its finite system has a unique solution, by the maximum principle
for its homogeneous equation. This proves (5). The kernel checks the
cross-multiplied Green equations, boundaries, and `g_d<=2`.

Condition on the prefix at each visit before taking its wait. Its
presence before exit is already decided, and (1) is uniform over that
prefix. Tonelli and (4)--(5) therefore give

\[
 \begin{split}
 \mathbb E\sigma_K
 &\le1+\sum_{d=1}^{K-1}G_K(1,d)(v(d)+2)\\
 &\le1+2C(K-1)\le\boxed{9K-8}.                                  \tag{6}
 \end{split}
\]

This argument does not replace a holding time by its unconditional mean
or assume independence from subsequent exit events. It sums predictable
visits and conditions before each wait.

If `tau>H`, either this stopped walk exited at `K`, or its physical
clock exceeds `H`. Markov's inequality yields, for every `K>=1,H>=1`,

\[
                 \Pr(\tau>H)\le\frac1K+\frac{9K-8}H.              \tag{7}
\]

Choose `K=floor(sqrt(H)/3)+1`. Then `K>sqrt(H)/3` and
`9K-8<=3sqrt(H)+1`, proving

\[
              \boxed{\Pr(\tau>H)\le7H^{-1/2}.}                   \tag{8}
\]

The trivial cap of one is understood. Even separations have zero tail
for these horizons, so (8) is uniform over **every** positive starting
separation and every finite prefix at which the counts agree.

## 3. Balanced fusion and actual refinement energy

Retain the previous written bound for the number `N` of count-return
cycles needed for balanced fusion from adjacent inputs:

\[
               \mathbb EN\le C_*,\qquad
               C_*=2187414\,2^{454272}.
\]

There is no need to change or optimize its constants. Summing (8) gives

\[
                    \mathbb E\min(\tau,H)\le14\sqrt H.            \tag{9}
\]

For example, use `E min(tau,H)=1+sum_(h=1)^(H-1) Pr(tau>h)` and
`sum_(h=1)^(H-1) h^(-1/2)<=2sqrt(H)-1`. If `T` is the whole
balanced-fusion clock, the event that cycle `j` is needed is known
before that cycle starts. Therefore the same predictable-cycle argument
as in the previous note gives

\[
 \mathbb E\sum_{j=1}^{N}\min(\tau_j,H)\le14C_*\sqrt H.
\]

On `T>H` this sum is at least `H`. Consequently

\[
              \boxed{\Pr(T>H)\le14C_*H^{-1/2}.}                   \tag{10}
\]

Conditioning on either first input parity doubles this upper bound.
The prior central-binomial lower bound is of order `H^(-1/2)` too.
Thus balanced noncoalescence has exactly this order up to constant
multipliers in the full-period laws, including the even-source law.
The infinite mean of `T` remains consistent with (10).

For actual source annuli, the previous kernel transport and written
squared cap give `e_(s,k)<=q_(k+1)`, where `q_H` is half the
even-source noncoalescence fraction. Thus (10) yields

\[
                             q_H\le14C_*H^{-1/2}.
\]

Split the refinement energy at `J(s)=ceil(121s/50)`. The existing
geometric tail contributes at most `23/4`; the first `J(s)` levels
contribute at most `28C_*sqrt(J(s))`. Hence

\[
 \boxed{E_s\le28C_*\sqrt{\lceil121s/50\rceil}+23/4
                 =O(\sqrt s).}                                  \tag{11}
\]

The much smaller constant in the earlier `0.542s+6` estimate still makes
that estimate useful at practical offsets. Neither estimate proves
`liminf E_s<infinity`.

The earlier coalescence-cap-plus-tail certificate is bounded below by
`(2s+1) binom(2s,s)/4^s-1/2`, of order `sqrt(s)`. Equation (11)
gives an upper bound of the same order for that certificate. Thus this
method's growth order is now determined. This is **not a square-root
lower bound on the actual energy**. A bounded actual energy remains
possible, but requires using the weights or cancellation beyond this cap.

## 4. A stronger range of return-separation moments

The new tail also enlarges the available separation budget, without
changing the already verified constant `C_*`. For any `0<alpha<1`,
the prior affine correction recursion gives

\[
 \sup_t\mathbb EB_t^\alpha
 \le M_\alpha:=\frac{2^{-\alpha-1}}{1-r_\alpha}<\infty,
 \qquad r_\alpha=\tfrac12(2^{-\alpha}+(3/2)^\alpha)<1.
\]

On `2^(j-1)<tau<=2^j`, Hölder and (8) bound the stopped
`beta` moment, for `beta<alpha`, by a constant times

\[
 2^{j\beta/\alpha}\,2^{-j(1-\beta/\alpha)/2}
          =2^{-j(1-3\beta/\alpha)/2}.
\]

This is summable when `beta<alpha/3`. Given any `0<beta<1/3`,
choose `3beta<alpha<1` to obtain a finite bound `B_beta` on
`E B_tau^beta`, uniform over the initial separation. Nonnegative
optional stopping still gives `E lambda_tau^beta<=r_beta<1`.
The same return comparison therefore proves

\[
 \mathbb E[(D')^\beta\mid D]
      \le r_\beta D^\beta+2B_\beta.
\]

Absorb at zero, telescope deterministic truncations, and use the
already established `EN<=C_*`. Starting with `D_0=1`, this gives

\[
 \boxed{\mathbb E\sum_{j<N}D_j^\beta
             \le\frac{1+2B_\beta C_*}{1-r_\beta}<\infty
                 \quad(0<\beta<1/3).}                            \tag{12}
\]

No assertion is made at or above the endpoint exponent `1/3`.
These are written stopped-moment deductions, not new kernel probability
theorems and not an estimate for indefinite finite-integer sampling.

## 5. Why raw endpoint aggregation still needs care

The return-image experiment suggested an exact family with arbitrarily
large transport multiplier and fixed returned distance four. For `m>=0`,
choose the unique odd `v_m` in `1..127` satisfying

\[
                   3^m v_m\equiv125\pmod{128},
 \quad r_m=2^{m+1}v_m-2,\quad \tau_m=m+8,\quad a_m=m+5.
\]

Here `0<r_m<2^(tau_m)` and `r_m` is even. After the first step and
`m` common odd steps, the lower-count endpoint is
`X=3^m v_m-1=128z+124`, and the other is `3X+2=384z+374`.
Their next seven parity words are respectively `0011111` and `0110110`.
Their count gap remains positive before the last step, when the
endpoints are `243z+242` and `243z+238`. Thus this is their first
positive count return, with common count `a_m` and separation four.
Its multiplier in the exact progression transport is

\[
              \lambda_m=\frac{3^{a_m}}{2^{\tau_m}}
                  =\frac{243}{256}(3/2)^m\longrightarrow\infty.   \tag{13}
\]

The base larger endpoint is `(3^(m+5)v_m+601)/128`. The parity and
affine calculations in this paragraph are written algebra, with exact
finite replay; they are not among the fifteen new kernel roots.

For a finite collection of nonfused even-source first-return prefixes,
form its raw ternary image density

\[
 K_H(z)=\sum_{\tau\le H}\frac{3^a}{2^\tau}
                 \mathbf1_{z\equiv x_0\pmod{3^a}}.
\]

Each term has ternary Haar integral `2^(-tau)`. Prefix freeness makes
their total at most `1/2`. Monotone convergence hence gives an
integrable limiting density under that Haar law. But (13) makes its
essential supremum unbounded: each indicated cylinder has positive
measure. The raw positive-integer columns are unbounded as well; take
the lifted endpoint `x_0+3^a` of this family in its actual source annulus.

This disproves a **constant bound on these raw aggregate coefficients**.
It does not disprove a comparison for the particular actual weighted
gradients, whose values can compensate for a large coefficient. An
integrable ternary density alone supplies no uniform bound on those
integer progression samples. The weighted sampling problem identified
in [annulus-height coupling](ANNULUS-HEIGHT-COUPLING.md) remains open.

## 6. Reproduction and scope

Run `python3 verify_count_return_clock.py`. The
[verification record](../results/count-return-clock/verification.json)
authenticates the prior count-return, energy-cap, and height-coupling
records, freshly builds the standalone fifteen-root Lean module, and
keeps finite rational checks separate from the written stopping proofs.

The new bounds improve the clock and energy orders and enlarge the
return-separation moment range. They do not prove bounded actual energy,
control of the actual weighted progression averages, absence of escape,
exclusion of additional cycles, or the full Collatz conjecture.
