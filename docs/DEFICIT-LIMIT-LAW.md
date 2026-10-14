# A limiting law for the deficit before the global minimum

**Status: written analysis, conditional on the repository's written natural
first-passage stabilization and finite-path packing arguments.** The finite
algebra below has separate kernel proofs and exact Python checks. Neither
the limiting law nor its tightness conclusion is kernel proved. No universal
convergence, uniform mean deficit, or pointwise deficit bound is assumed or
established.

The new conclusion is that the deficit up to the global minimum has a
limiting probability distribution under uniform integer sampling. In
particular it is uniformly tight. On the basin of one this is the lifetime
deficit from [the pre-arrival transfer](PREARRIVAL-DEFICIT-TRANSFER.md).
Consequently the pre-arrival cost with a known convergent child is tight
over actual source bands. This is weaker than the average bound still
needed by that route.

## 1. A functional that is finite without assuming Collatz

Use the shortcut map `U`, and put

\[
 m(n)=\min_{t\ge0}U^t(n),\qquad
 T(n)=\min\{t:U^t(n)=m(n)\},
\]
\[
 W_h(n)=\frac{n3^{a_h(n)}}{2^hU^h(n)},\qquad
 D_m(n)=\sum_{0\le h<T(n)}(1-W_h(n)),\qquad
 P(n)=W_{T(n)}(n).
\]

Well-ordering makes `T(n)` finite for every positive start, including a
hypothetical escaping or nontrivially periodic start. It does not make
`m(n)` equal to one. A repeat before `T(n)` would contradict first
attainment, so this prefix is simple. The ordinary and shortcut orbit
minima agree. The omitted ordinary odd-step outputs are larger than
their odd inputs.

Thus `0 <= D_m(n) <= T(n)` and `0 < P(n) <= 1`. The existing
[packing argument](FINITE-PATH-PACKING.md) gives the uniform floor
`P(n) >= exp(-8192/3)`. For `n` in the basin `B` of one, `T(n)=tau(n)`
and `D_m(n)=D(n)` from the preceding note.

Initial halvings have weight one. Hence, for every `a >= 0`,

\[
 (m(2^a n),D_m(2^a n),P(2^a n))=(m(n),D_m(n),P(n)).       \tag{1}
\]

## 2. The exact comparison through a common landing

Suppose a source first reaches an odd value at most `x` at shortcut
clock `i`, with landing `b`. Every earlier odd input is greater than
`x`. Every earlier state is greater than `b`, even though an even
state in the final halving segment may already be below `x`. Therefore

\[
 m(n)=m(b),\qquad T(n)=i+T(b).
\]

The record and clock facts were established in
[Clocked minimum](CLOCKED-MINIMUM.md). The same facts hold in shortcut
time. Before this landing there are no repeated states.

Let `p=W_i(n)` and `A=sum_(h<i)(1-W_h(n))`. Weight multiplication gives

\[
 \boxed{D_m(n)=A+pD_m(b)+(1-p)T(b)
               =D_m(b)+A+(1-p)(T(b)-D_m(b)).}             \tag{2}
\]

If every prefix weight is at least `1-e`, with `0 <= e <= 1`, then

\[
 0\le D_m(n)-D_m(b)\le e\,[i+T(b)]=eT(n).                \tag{3}
\]

For two sources `n,n'` with the same landing and the same bound `e`,

\[
 |D_m(n)-D_m(n')|\le e\max\{T(n),T(n')\},\qquad
 |P(n)-P(n')|\le e.                                      \tag{4}
\]

The first estimate uses the common *nonnegative* interval in (3),
not a sum of two error bounds. The second uses
`P(n)=pP(b)`, `P(n')=p'P(b)` and `p,p' in [1-e,1]`.

Packing the distinct odd inputs before first odd passage gives

\[
 \sum_{u\text{ odd before passage}}\frac1u\le8192x^{-1/20}.
\]

Since `1-prod(1-z_j) <= sum z_j` for `z_j in [0,1]`, all prefix
weights, including `p`, are at least `1-e(x)`, where

\[
 e(x)=\min\{1,(8192/3)x^{-1/20}\}.                        \tag{5}
\]

Only odd inputs need to exceed the floor in this argument. It would be
incorrect to assert that every previous even state does so.

## 3. The probabilistic input and finite coupling chains

Fix `alpha=1001/1000`. For odd uniform starts `U_y` on `[y,2y)`,
[Proposition 4.1](NATURAL-DENSITY-ALMOST-BOUNDED.md) and the early-clock
estimate in [Clocked minimum](CLOCKED-MINIMUM.md) supply constants
`C,c,L>0` such that, for large `x` and
`y,z in [x^alpha,x^(alpha^2)]`, there is a coupling of the two
sources satisfying, outside probability `C(log x)^(-c)`:

* their first odd passage locations below `x` exist and agree;
* both passage clocks are at most `L log x`.

The clock estimate may use the ordinary upper bound
`L=301/(1000 log 2)`; shortcut clocks are smaller. Couple landing laws
maximally, then lift the coupling to the source distributions conditional
on each landing. The two marginal bad-clock probabilities are included
by a union bound. No independence between a clock and its landing is
required.

This input is a **local written adaptation** of
[Tao's first-passage method](https://arxiv.org/html/1909.03562v7).
Tao's published theorem itself uses logarithmic density. The present
note does not turn the adaptation into an externally established or
kernel-checked natural-density theorem. The renewed check found no new
gap in its paired-sum tilt, renewal reassembly or summation; the factor
`2*m0*(2-log_2 3)` there includes the scale of `E'` and stays unchanged.

Let `Y >= Z >= B`, with `B` larger than a fixed threshold. Descend from
`Y` to `Z` by powers `u -> u^(1/alpha)`, with at most one final partial
step; then do the same from `Z` to `B`. In any link with larger scale
`u` and smaller scale `v`, we have `v <= u <= v^alpha`; choose the
floor `x=v^(1/alpha)`. Both sources lie in the required scale interval.
Glue the finitely many source couplings by their common marginals.

There are at most two partial links. On all other links the logarithms
of the scales form geometric sequences with ratio `alpha`. Consequently
the total bad probability is at most

\[
                    C_1(\log B)^{-c}.                   \tag{6}
\]

On the complementary event, all sampled sources have the same global
minimum. Define the finite, not effectively bounded constant

\[
 T_B=\max\{T(n):n\text{ positive odd},\ B\le n<2B\}.
\]

Clock comparison through each common record yields, for every node at
scale `u` in the chain,

\[
                    T(n_u)\le T_B+C_2\log u.             \tag{7}
\]

Indeed `T(n_u)-T(n_v)=i_u-i_v <= L log x`; sum the logarithms
down to `B`. The constants in (6)--(7) do not depend on `Y,Z,B`.
The existence of `T_B` uses only a finite population and well-ordering.
No termination algorithm for arbitrary orbits is being asserted.

## 4. Tightness and convergence of the law

Put `s=1/20`. Equations (4)--(7) bound a link's deficit difference by

\[
 C_3 x^{-s}(T_B+\log u),
\]

and its terminal-weight difference by `C_3 x^(-s)`. For a full link
`x=u^(1/alpha^2)`. A partial link has the same lower bound in terms
of its larger scale. For any sequence of full links above `Z`,

\[
 \sum (T_B+\log u)u^{-s/\alpha^2}
       \le C_4(T_B+1)Z^{-\gamma},\qquad
             \gamma=\frac1{40\alpha^2}>0.               \tag{8}
\]

For completeness, absorb `1+log u` into a fixed multiple of
`u^(s/(2alpha^2))`. In increasing order the remaining terms are at most
`exp(-gamma (log Z) alpha^r)`. Use
`alpha^r >= 1+r(alpha-1)` and sum a geometric series. For large fixed
lower threshold on `Z` its denominator is bounded away from zero.
The at most two partial links change only the constant.

Therefore the coupled sources at `Y` and `Z` satisfy

\[
 \Pr\left(
 \begin{array}{c}
 m(n_Y)\ne m(n_Z)\quad\text{or}\\
 |D_m(n_Y)-D_m(n_Z)|+|P(n_Y)-P(n_Z)|
       >C_5(T_B+1)Z^{-\gamma}
 \end{array}\right)
       \le C_1(\log B)^{-c}.                              \tag{9}
\]

The order of choices matters: first fix `B` to make the right side
small, then let `Z` grow so that its fixed `T_B` is absorbed. There is
no claim that `(T_B+1)B^(-gamma)` tends to zero.

Taking `Z=B` in the same chain argument gives, outside (6),

\[
 m(n_Y)\le2B,\qquad
 D_m(n_Y)\le T_B+C_5(T_B+1)B^{-\gamma}.                   \tag{10}
\]

This proves uniform tightness for the odd-source laws. Equation (9)
also makes these laws Cauchy in the Prokhorov metric on the Polish space
`N_(>0) x [0,infinity) x [0,1]`, with a discrete first coordinate.
Completeness gives a limiting probability law `mu` for

\[
                         (m(U_Y),D_m(U_Y),P(U_Y)).        \tag{11}
\]

One can equivalently choose successive error tolerances tending to zero
in (9), use tightness to extract a subsequence, and then use the same
couplings to show that every subsequential limit agrees.

Dyadically decompose the odd integers up to `X`; finitely many small
blocks have vanishing mass. Then decompose all integers according to
their initial power of two. Identity (1) and the geometric tail of those
powers give the same law `mu` for uniform positive integers up to `X`.
The argument also applies to any fixed multiplicative interval.

In particular, for every bounded continuous `f`,

\[
 \frac1X\sum_{n\le X} f(m(n),D_m(n),P(n))
                \longrightarrow \int f\,d\mu.          \tag{12}
\]

The minimum marginal agrees with the previously established limiting
minimum distribution. The finite submeasure obtained by restricting
`m=1` is the limiting law of the known-basin deficit, with mass equal
to the natural density of that basin. No assertion that this mass is
one is included. Bounded truncated moments, for example
`min(D_m,R)` for fixed `R`, converge. Untruncated moments need not follow.

## 5. Consequence for the pre-arrival problem

The pre-arrival transfer gives, whenever `q=3n+2` reaches one,

\[
                     H(n)\le(23/3)D(q)+1.
\]

The set of these `q` in a parent band `[M,2M)` lies in `[1,6M+2]`.
Uniform tightness of `D_m` for actual positive integers therefore gives

\[
 \boxed{\lim_{R\to\infty}\sup_{k\ge0}
 2^{-k}\#\{2^k\le n<2^{k+1}:3n+2\in B,\ H(n)>R\}=0.}   \tag{13}
\]

First obtain the statement with `limsup_(k->infinity)` from (10),
absorbing the fixed interval-length factor. Then absorb finitely many
early bands: each contains only finitely many eligible sources, each
with finite `H`. The parent is not required to be known convergent.

Tightness alone does **not** bound `sup_k mean H`, and it does not bound
`sup_k mean D_m`. For a nonnegative functional the mean is the integral
of its tail probabilities; (13) supplies no integrable tail estimate.
Uniform integrability would be a stronger sufficient condition, but is
not necessary merely for bounded first moments. The negative arrival
advance and post-arrival reversed drift remain separate unresolved terms.

## Verification and exploration

Run `python3 verify_deficit_limit_law.py`. Its
[record](../results/deficit-limit-law/verification.json) separates finite
kernel identities, exact rational checks, and the written analytic inputs.
The finite tests cannot certify stabilization, packing, tightness, the
limiting law, or convergence of all positive integers.

A separate terminal floating C++ exploration scanned starts below
`2^26`. Its displayed mean deficits in the last three binary bands were
about `1.874137`, `1.873696`, and `1.873234`; the displayed band maxima
were about `5.083346`. These are exploratory floating outputs, not
certified maxima, limiting values, or bounds. They are not used by the
argument or by verification decisions.
