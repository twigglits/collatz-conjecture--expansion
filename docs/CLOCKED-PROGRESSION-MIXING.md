# Progression mixing with the passage clock retained

**Status: a local written extension of the joint fine-scale mixing and
uniform-preimage argument. It uses Tao's published analytic inputs.
Finite residue arithmetic and coupling inequalities are kernel checked;
the asymptotic mixing assertion is not. No effective constants or full
Collatz proof are obtained, and no novelty claim is made.**

The preceding [finite transport](CENSORED-PROGRESSION-TRANSPORT.md) isolates
the progression error

\[
 \delta_t(X)=\frac1X\sum_{n=1}^X A_t(3n+2)
          -\frac1{3X+2}\sum_{n=1}^{3X+2}A_t(n),              \tag{1}
\]

where `A_t` is the deficit stopped at first arrival at one, in **ordinary**
time. The exact finite counterexamples there reject certain `t/X` bounds.
The argument here gives a weaker rate in `X`, but an actual asymptotic
estimate, uniformly over the finite time cutoff:

\[
 \boxed{\text{For every }R>0,\quad
       |\delta_t(X)|\le C_R\,t(\log X)^{-R}
       \quad(X\ge X_R,\ t\ge0).}                           \tag{2}
\]

The constants and thresholds are not made effective. In particular,
at `X=2^k`, `t=8k`, the **unnormalized** discrepancy in (1) is
`O_R(k^(-R))` for every fixed `R`, after changing the exponent used in
(2). This does not establish that either mean in (1), divided by `k`,
tends to zero. Section 6 explains the remaining issue.

There are analogous bounds `C_R(log X)^(-R)`, uniformly in `t`, for
the progression discrepancies of

\[
 s_t(n)=\mathbf1_{\{\tau_1(n)>t\}},\qquad
 z_t(n)=s_t(n)(1-W_t(n)).                                    \tag{3}
\]

Here `tau_1=infinity` is allowed. The argument couples both the first
passage location **and its ordinary clock**. Coupling locations alone
would not justify these uniform cutoff comparisons.

## 1. Encoding a source congruence by one extra ternary digit

For a Syracuse valuation word `a=(a_1,...,a_n)`, put `S=sum a_i` and
write its affine map as

\[
 \operatorname{Aff}_a(N)=3^n2^{-S}N+F_n(a),\qquad
 B=2^SF_n(a)\in\mathbb Z.
\]

An odd landing `M` has an integer preimage under this word exactly when
`M=F_n(a) mod 3^n`. If that preimage must also satisfy `N=r mod 3`,
the condition becomes

\[
 M\equiv V_{n,r}(a):=F_n(a)+3^n2^{-S}r\pmod{3^{n+1}}.         \tag{4}
\]

Indeed `2^S M=3^n N+B`; clearing the invertible power of two gives
`2^S M=B+3^n r mod 3^(n+1)`. The finite kernel lemma proves this
equivalence in the corresponding integer-witness form.

For the two unit classes take `c_1=2`, `c_2=1`, so that
`2^(-c_r)=r mod 3`. Prepending this single valuation gives

\[
 F_{n+1}(c_r,a)=F_n(a)+3^n2^{-S-c_r}
                      \equiv V_{n,r}(a)\pmod{3^{n+1}}.       \tag{5}
\]

Thus the extra-digit law in (4) is a Syracuse-offset law with one
endpoint valuation fixed. Its reduction modulo `3^m`, for `m<=n`,
is exactly that of `F_n`, jointly with the remaining valuation sum `S`.
There is no independence assumption between the offset and the sum.

## 2. Fine-scale mixing survives the fixed endpoint

The analytic starting point is the paired Fourier estimate, the
collision argument, and the valuation bounds in
[Tao, Sections 5–7](https://arxiv.org/html/1909.03562v7).
The unconditioned sum-tilted version is the project's written
[joint-mixing argument, Section 2](NATURAL-DENSITY-ALMOST-BOUNDED.md#2-joint-fine-scale-mixing).
The following modification is a local deduction, not a new assertion
attributed to the published paper.

Reverse the word and write

\[
 X_N=\sum_{j=1}^N3^{j-1}2^{-S_j}\pmod{3^N}.
\]

Let the first `N-1` valuations be independent `Geom(2)` variables and
fix the last valuation to `c`, where `c=1` or `2`. Call this law `X_N^c`
and its total valuation `S_N^c`. For `3` not dividing `xi`, the needed
bound is

\[
 \sup_{\theta\in\mathbb R}
 \left|\mathbb E\,e\!\left(-\frac{\xi X_N^c}{3^N}
                             +\theta S_N^c\right)\right|
                         \ll_{A,c} N^{-A}.                  \tag{6}
\]

There are two parity cases, which should not be conflated:

* If `N` is odd, pair the first `N-1` coordinates. Conditional on the
  pair totals, the sum tilt and the final fixed-coordinate term are
  phases of modulus one. Each pair contributes exactly the same
  conditional factor as in the original paired estimate. Taking
  absolute values leaves its product bound at ambient modulus `3^N`.
* If `N` is even, first condition on the first coordinate `a`. The
  identity `X_N^c=2^(-a)(1+3 X_(N-1)^c)` reduces the character to a
  primitive character modulo `3^(N-1)`. The remaining length is odd,
  so the preceding case applies uniformly in `a`; averaging over `a`
  proves (6). This avoids deleting an uncontrolled paired factor.

Integrating the sum tilt over `[0,1]` gives (6) with the indicator
`S_N^c=s`, uniformly in `s`. This is an unnormalized subprobability
bound; we do not divide by the possibly small probability of that sum.

For a measure `nu` on `Z/3^N Z`, use the L1 oscillation

\[
 \operatorname{Osc}_{m,N}(\nu)=
 \sum_{y\bmod3^N}\left|\nu(y)
      -3^{m-N}\nu(y\bmod3^m)\right|.
\]

The resulting conditioned joint estimate is

\[
 \operatorname{Osc}_{m,N}
     \bigl(\Pr(X_N^c=y,\ S_N^c=s)\bigr)
                          \ll_{A,c}m^{-A}.                  \tag{7}
\]

Here are the details needed to reuse the collision/Plancherel step.
In the range `0.9N<=m<=N`, the exceptional-event probabilities grow
by at most `2^c`, since the conditioning event has probability `2^(-c)`.
The first block used for the collision bound ends a positive fraction
of `N` before the fixed final coordinate, so its distribution and
collision bound are unchanged. The second block is independent of it
and has the same fixed final coordinate. At a primitive frequency use
(6) with a fixed sum. When a frequency is divisible by a positive power
of three, projection removes the final coordinate before that Fourier
bound is applied. The visible block then has the ordinary unconditioned
law; the invisible coordinates give an independent mixture of fixed-sum
laws with total mixing weight at most one. In either case the tail
Fourier factor has arbitrary inverse-power decay. The same Plancherel
estimate follows.

For smaller `m`, first smooth down to a level `j` with
`0.9N<=j<N`. The projected joint law at that level is a mixture of
ordinary length-`j` fixed-sum laws: the fixed last coordinate is outside
the projection. Apply the existing joint estimate to that mixture,
and add the error of the first smoothing. Small lengths are covered
by enlarging the constant. This proves (7) without a claimed uniform
bound after conditioning on a rare total valuation.

Apply (7) to `N=n+1`, `c=c_r` in (5), with total valuation `s+c_r`.
Its coarse joint marginal is the ordinary `F_n mod 3^m, S=s` law.
That exact equality is the reason the same main term will occur below.

## 3. Retaining the ordinary passage clock at the same source scale

Let `alpha=1001/1000`, `y=x^alpha`, and let `U_y` be uniform on the
odd integers in `[y,2y)`. Let `U_(y,r)` be the corresponding uniform
sample restricted to `N=r mod 3`, for `r=1,2`.

Use first **odd** passage below `x`, and mark a source by `(b,I)`,
where `b` is the landing and `I` is its ordinary clock. Add a distinct
nonentry mark. The assertion is

\[
 d_{\rm TV}\bigl(\mathcal L(b,I)(U_{y,r}),
                 \mathcal L(b,I)(U_y)\bigr)
                         \ll_R(\log y)^{-R}                 \tag{8}
\]

for every fixed `R>0`; nonentry has probability `O(x^(-c))`.

Use the parameters and good valuation events of the earlier uniform
preimage argument:
`n_0=floor(log x/(10 log 2))`,
`m_0=floor((alpha-1)log x/100)`, and the **expanded** window

\[
 I_y^* =\left[\frac{\log(y/x)}{\log(4/3)}-\log^{0.8}x,
              \frac{\log(y/x)}{\log(4/3)}+\log^{0.8}x\right].
\]

The change in `log N` across `[y,2y)` is bounded. Thus the entire source
interval lies within this window on the good valuation event. Its
complement has a stretched-exponential bound in `log x`, and hence
costs `O_R((log x)^(-R))` for every fixed `R`. There is no loss from
trimming a logarithmically broad source interval. Restricting the source
to either class modulo three preserves the early dyadic valuation
estimate: each allowed odd dyadic residue occupies one class modulo
three times the dyadic modulus, with an `O(1)` counting error.

Write `n'=n-m_0`. The pre-passage intermediate state `M` has exactly
`m_0` remaining Syracuse steps to its first odd passage. On the good
event the actual passage time is `n`. If its initial word sum is `s`,
then its ordinary passage clock is exactly

\[
                     I=n+s+S_{m_0}(M).                      \tag{9}
\]

Consequently an arbitrary bounded test of `(b,I)` is a bounded test
of `(n,s,M)` in the approximate preimage formula. No clock need be
averaged away. The good-event equivalence identifying the true first
passage remains valid with this test inserted.

Let `K_y=y/2+O(1)` and `K_(y,r)=y/6+O(1)` be the two source counts.
After replacing the shifted preimage interval by the unshifted one,
the intermediate range for fixed `(n,s)` is

\[
             J_{n',s}=[3^{n'}y2^{-s},\ 2\cdot3^{n'}y2^{-s}).
\]

The interval replacement costs `O(x^(-c'))`, including the sum over
`n`; conditional source classes change only the constant. Its validity
uses the same small relative affine offset and uniqueness of a valuation
word for each source.

For unrestricted sources the residue modulus in the count is `3^n'`;
for the restricted source it is `3^(n'+1)`, with the law (4).
The count coefficients, including any test bounded by one, are bounded
uniformly: respectively they are at most

\[
 \frac{2^s}{K_y}\left(3^{n'}y2^{-s}/3^{n'}+1\right),\quad
 \frac{2^s}{K_{y,r}}\left(3^{n'}y2^{-s}/3^{n'+1}+1\right).
\]

Both are at most three for large `x` whenever the counted set is
nonempty, by the support bound `2^s/y=O(x^(-c'))`. Dropping the initial
good-word indicator therefore costs only its stretched-exponential
probability, including when the clock test is inserted.

Smooth the two fixed-sum laws to the common modulus `3^m_0`, using
the ordinary joint estimate and (7). There are
`O((log x)^(3/2))` relevant `(n,s)` pairs, so choosing the mixing
exponent larger than `R+2` absorbs their number. The coarse joint laws
are exactly equal, and their prefactors have ratio

\[
 \frac{2^s/(K_{y,r}3^{n'+1-m_0})}
      {2^s/(K_y3^{n'-m_0})}
                 =\frac{K_y}{3K_{y,r}}=1+O(1/y).            \tag{10}
\]

This identifies the marked main terms without summing over `n` or `s`.
Any harmless polynomial factor from their normalization is absorbed
by `1/y`. The error bound is uniform over all marked tests, proving
(8). Unlike the comparison of **different** source scales, this step
uses no renewal-phase averaging, local limit theorem, or irrationality
exponent. The arbitrary power in (8) must not be imported into the
earlier different-scale stabilization theorem.

## 4. A matched clock controls every later cutoff

Couple the marked laws maximally and lift the coupling to sources.
Include nonentry in the bad event. Outside probability
`eta<=C_R(log y)^(-R)`, the sources reach the same odd `b` at the same
ordinary clock `I`. Before the landing both odd trajectories stay
above `x` and have no repeated states. The earlier
[finite-path packing bound](FINITE-PATH-PACKING.md) gives

\[
 1-\varepsilon_x\le W_h(n),W_h(n')\le1\quad(0\le h\le I),
 \qquad \varepsilon_x=\min\{1,(8192/3)x^{-1/20}\}.            \tag{11}
\]

Only the odd inputs must exceed the floor; intermediate even states
need not do so. This does not assume the common tail reaches one.

For an arbitrary cutoff `t`, let `a` be the deficit accumulated before
`min(t,I)`, let `p=W_I(n)`, and put
`d=A_(t-I)_+(b)`, `l=L_(t-I)_+(b)`. Then

\[
 A_t(n)=a+pd+(1-p)l,\qquad
 0\le A_t(n)-d=a+(1-p)(l-d)\le\varepsilon_x t.               \tag{12}
\]

This includes `t<I`, when `d=l=0`. It follows from
`a<=epsilon_x min(t,I)`, `0<=d<=l<=(t-I)_+`, and
`min(t,I)+(t-I)_+=t`. The second source lies in the same interval
`[d,d+epsilon_x t]`, giving

\[
 |A_t(n)-A_t(n')|\le\varepsilon_x t\quad\text{for every }t.   \tag{13}
\]

The equality of both passage clocks also makes the entire first-arrival
clock at one equal, including the value infinity. Before passage neither
source has reached one; after passage they have the same tail and the
same elapsed clock. Thus their `s_t` values agree for every `t`. For
`z_t`, before passage both values lie in `[0,epsilon_x]`; afterwards
the tail weight is multiplied by `p` or `p'`, so their difference is
at most `epsilon_x`, until both cells are censored to zero.

On the bad event use `0<=A_t<=t` and `0<=s_t,z_t<=1`.
These bounds and (13) prove the odd-block versions of (2)–(3), uniformly
in `t`. The finite kernel inequalities cover the window, cell, and
coupling-mean algebra. The analytic coupling and packing inputs remain
written mathematics.

## 5. From odd blocks to the actual progression in (1)

For a positive-integer block `[y,2y)`, split by the initial valuation
`a=v_2(n)`. The odd parts lie in `[y/2^a,2y/2^a)`. Conditioning on
`n=2 mod 3` makes their classes `2*2^(-a) mod 3`, always either one
or two. In each class compare with the corresponding unrestricted odd
block as above, and append the same initial `a` halving steps.
Those steps have zero deficit and add the same clock to both sources.

Truncate at `a<=floor((log_2 y)/2)`. The omitted mass is `O(y^(-1/2))`
for both source laws, and every retained odd scale is at least `sqrt y`.
The conditional and unconditional mixture weights differ by
`O(1/y)` per retained valuation, hence by `O(log y/y)` in total.
The logarithms of all retained odd scales are comparable to `log y`,
so the block bounds retain every fixed inverse logarithmic power.

Next decompose `1..Y` into positive-integer dyadic blocks down to
scale `sqrt Y`, discarding the remaining `O(sqrt Y)` sources. The
conditional block weights have total mismatch `O(log Y/Y)`; the
comparison errors are averaged with block probabilities, not summed
without those probabilities. This proves the analogous bounds for a
uniform source in `1..Y` and one conditioned to be two modulo three.

For `Y=3X+2`, the latter sample includes `2` and has `X+1` members.
The progression in (1) omits `2` and has `X` members. Removing that
source and renormalizing costs at most `t/X` for deficits and `1/X`
for (3), which are absorbed by the asserted bounds. This proves (2)
and the stated cell/survivor comparisons with their exact endpoints.

## 6. What this estimate does not decide

At logarithmic clocks the new discrepancy is `o(1)`, while the explicit
affine term in the population recurrence has mean size
`O(t log X/X)=o(1)`. This closes a quantitative sampling question;
it does not identify the remaining basin mass.

To see the limitation of a bulk coefficient comparison, put
`kappa=3/log(4/3)` and, in a region above the critical clock, consider
the candidate profile `H_t(N)=b(t-kappa log N)`. For **any** coefficient
`b`, it obeys the idealized balance

\[
 2H_{t+2}(2X)=H_{t+1}(X)+H_t(3X),                            \tag{14}
\]

because its residual is
`b[3-kappa(2 log 2-log 3)]=0`. The finite integer endpoint changes
and the explicit correction in the actual recurrence vanish at this
scale. The kernel module checks the algebra of (14).

This is only a bulk profile calculation, not a constructed orbit law or
a proof that (2) can never help. It shows that comparing the bulk
coefficients alone cannot force `b=0`. One still needs control of the
iteration and its small-scale boundary data, or another argument that
proves the all-source mean tends to zero. The earlier written phase
law identifies `b=1-r_B-d`; it leaves that coefficient undetermined.

The finite inequalities `delta>9t/X` and `X delta>8E` remain valid.
A bound with arbitrary inverse logarithmic powers and unspecified
constants is much weaker than `C t/X`; there is no conflict. No
effective numerical estimate for (2) is inferred from those censuses.

## 7. Verification and dependencies

Run `python3 verify_clocked_progression_mixing.py`. The
[record](../results/clocked-progression-mixing/verification.json) separates:

* ten new finite kernel roots for integer source/seed arithmetic,
  affine composition, common-clock bounds, finite coupling sums, and
  the neutral bulk identity, with standard axioms only;
* independent exact modular and affine enumeration of finite valuation
  words, with omitted geometric mass reported rather than discarded;
* exact conditional pair convolutions and the even-length reduction,
  supporting the algebra behind (6), without numerically claiming
  Fourier decay;
* actual finite first-odd-passage laws and distinct matched-clock source
  pairs, checked at every cutoff across and after the landing;
* the **written** conditioned-mixing, marked-preimage, and large-scale
  consequences, using the published analytic inputs and local written
  joint-mixing argument. These are not kernel-certified or independently
  peer-reviewed asymptotic theorems.

The small finite passage populations test identities, not the asymptotic
regime or the unknown constants. No floating-point verification decision
is used. No external predecessor-density theorem is needed for this
progression estimate; the earlier equivalence between a zero all-source
limit and full Collatz keeps its own separate written and external
dependencies. Full Collatz remains unresolved.
