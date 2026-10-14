# Logarithmic moments of the global orbit minimum

**Status: a written consequence of the preceding local progression-mixing
argument. Sixteen finite kernel roots check the actual floor-survivor
relations, cutoff arithmetic, and finite stopping inequalities. The
analytic mixing input, real logarithmic potentials, infinite iteration,
and moment conclusions are not kernel formalized. Collatz remains open.**

Let `C` be the ordinary positive-integer Collatz map and let

\[
 m(n)=\min_{t\ge0} C^t(n),\qquad
 f_H(n)=\mathbf1_{\{m(n)>H\}},\qquad
 F_H(N)=\frac1N\sum_{n=1}^N f_H(n).                         \tag{1}
\]

Every orbit has an attained global minimum by well-ordering, regardless
of convergence to one. The minimum is not assumed computable. We show,
under the stated written mixing input, that for each fixed `r>0`,

\[
 \boxed{\sup_{N\ge1}F_H(N)\le C_r(\log H)^{-r}
               \quad(H\ge2).}                             \tag{2}
\]

Here and below `H,N` are integers and logarithms are natural. Constants
may depend on the displayed exponent and are not made effective. This
improves the earlier written minimum-tightness bound with one fixed
logarithmic exponent. It also gives uniform integrability of every
fixed power of `log m(n)`, as detailed below.

## 1. The progression error is uniform over minimum thresholds

The [clocked progression-mixing note](CLOCKED-PROGRESSION-MIXING.md)
constructs, outside probability `O_R((log y)^(-R))`, a coupling of an
odd source in `[y,2y)` and a source in either unit class modulo three
with the same first odd landing `b` below a smaller floor `x`.
That landing is a strict record: every preceding ordinary state is
larger than `b`. This elementary record fact is already treated in
[Clocked Minimum](CLOCKED-MINIMUM.md).

Consequently both sources have the same **global minimum**, namely
`m(b)`, on the good event. This identity holds for every threshold `H`
at once. It does not require `x>=H` and it does not require deciding
what happens after `b`. The matched ordinary clock, useful for the
earlier censored-deficit comparison, can be forgotten here. No weight
retention estimate is needed for this minimum label.

Initial halvings preserve the minimum. Apply the same valuation
decomposition, dyadic source blocks, and endpoint correction from
Section 5 of that note. The source `2`, present in the full class
`2 mod 3` but absent from `3n+2`, costs at most `1/X`. We obtain

\[
 \delta_H(X):=\frac1X\sum_{n=1}^X f_H(3n+2)-F_H(3X+2),
 \qquad
 |\delta_H(X)|\le A_R(\log X)^{-R}\quad(X\ge X_R),           \tag{3}
\]

**uniformly in `H`**, for every fixed `R>0`. More generally the same
coupling compares the entire global-minimum laws in total variation.
The constants in (3) do not depend on a minimum value or threshold.

The analytic premise here is the local WRITTEN same-scale mixing
extension, using the published Fourier and collision inputs discussed
in the preceding note. This is not a theorem attributed directly to
Tao, nor does finite replay certify it. The present deduction uses
neither the different-scale renewal estimate nor external positive
predecessor density. Convergence of moments to an existing limiting
law, stated in Section 5, has an additional dependency on that law.

## 2. The killed relation and the exact cutoff endpoints

For `H>=1` the actual map gives

\[
 f_H(2n)=f_H(n),\qquad
 f_H(2n+1)=\mathbf1_{\{2n+1>H\}}f_H(3n+2)
                        \le f_H(3n+2),\qquad
 f_H(n)=0\ (n\le H).                                      \tag{4}
\]

The indicator in the odd identity must be retained. A source below
the floor is already killed even when its later tail might avoid that
floor. We use the upper bound in (4), not an unrestricted equality.

For `N>=3` put

\[
 a(N)=\lfloor N/2\rfloor,\qquad
 l(N)=\lfloor(N-1)/2\rfloor,\qquad b(N)=3l(N)+2.
\]

There are `a(N)` positive even sources and `l(N)` odd sources other
than one. Since `f_H(1)=0`, parity splitting and (3) give

\[
 F_H(N)\le\frac{a(N)}N F_H(a(N))+
          \frac{l(N)}N F_H(b(N))+
          \frac{l(N)}N\delta_H(l(N))
 \le \frac{F_H(a(N))+F_H(b(N))}{2}
                     +\frac{|\delta_H(l(N))|}{2}.          \tag{5}
\]

Both coefficient replacements are valid because the means are
nonnegative and both coefficients are at most `1/2`. For `N>=9`,
`l(N)>=N/3>=sqrt(N)`. Thus (3) with `R=r+1` gives, for all `N>H`
once `H>=max(9,3X_(r+1))`,

\[
 F_H(N)\le P F_H(N)+K_{r+1}(\log N)^{-r-1},\qquad
 Pg(N):=\tfrac12[g(a(N))+g(b(N))],                          \tag{6}
\]

where one may take `K_(r+1)=2^r A_(r+1)`. The boundary value is
exactly zero on `1..H`.

## 3. A descending auxiliary chain on source cutoffs

Start at an integer `N>H>=3`. At each active step choose either
`a(N)` or `b(N)` with probability `1/2`, independently, and stop on
first reaching `1..H`. Write the cutoff chain as `N_j`, with stopping
time `tau`. It is an averaging device for (6), **not a stochastic
description of a Collatz orbit**.

The integer endpoints have a uniform negative logarithmic drift.
Indeed, if `N=2m`, then `a=m,b=3m-1`, whereas if `N=2m+1`, then
`a=m,b=3m+2`. Direct multiplication gives

\[
 4ab=\begin{cases}3N^2-2N,&N\text{ even},\\
                  3N^2-2N-1,&N\text{ odd},\end{cases}
 \qquad
 \tfrac12(\log a+\log b)\le\log N-d,
 \quad d=\tfrac12\log(4/3)>0.                              \tag{7}
\]

For an active state `N>H>=3`, both children are at least `H/2`, and
`b(N)>N`. Thus every stopped or active state reached by the chain
is at least `H/2`. At a fixed finite depth `J`, all random variables
are bounded; summing the conditional drift gives

\[
 d\,\mathbb E(\tau\wedge J)
       \le\log N-\mathbb E\log N_{\tau\wedge J}
       \le\log(2N/H).                                     \tag{8}
\]

Monotone convergence proves `E tau<=log(2N/H)/d<infinity`, hence
almost-sure absorption of this auxiliary chain. In particular
`Pr(tau>J)<=log(2N/H)/(d J)` for `J>=1`. This argument makes no
termination assertion about individual Collatz orbits.

## 4. A potential sums all the errors before the boundary

For a fixed `r>0`, the function `phi(s)=s^(-r)` is decreasing and
convex on positive reals. Its tangent inequality, applied at `s=log N`
to the two child logarithms, and (7) yield

\[
 \frac{(\log a)^{-r}+(\log b)^{-r}}2-(\log N)^{-r}
             \ge r d(\log N)^{-r-1}.                      \tag{9}
\]

For a globally bounded potential take
`V_H(n)=[log(max(n,H/2))]^(-r)` on positive integers. At every active
state and both its children this equals the expression in (9).
Also `0<=V_H<=[log(H/2)]^(-r)`. Finite telescoping gives

\[
 rd\,\mathbb E\sum_{j<\tau\wedge J}(\log N_j)^{-r-1}
 \le\mathbb E V_H(N_{\tau\wedge J})-V_H(N)
 \le[\log(H/2)]^{-r}-(\log N)^{-r}.                         \tag{10}
\]

Unroll (6) to the same finite depth. The boundary contribution is
zero, and `0<=F_H<=1`, so

\[
 F_H(N)\le\Pr(\tau>J)+
       K_{r+1}\,\mathbb E\sum_{j<\tau\wedge J}
                         (\log N_j)^{-r-1}.               \tag{11}
\]

For each fixed starting cutoff `N`, let `J` tend to infinity using
(8) and (10). The resulting upper bound no longer depends on `N`:

\[
 F_H(N)\le\frac{K_{r+1}}{rd}[\log(H/2)]^{-r}.                \tag{12}
\]

There is no exchange of a nonuniform limit with a supremum in this
step: first prove (12) separately for every `N`, then take the
supremum. If `N<=H`, its left side is zero already. For `H>=4`,
`log(H/2)>=log(H)/2`. Enlarging the constant for the finitely many
remaining floors proves (2).

For a rational check on the finite potential mechanism, exact integer
arithmetic also gives `8ab<=3N(a+b)` for `N>=3`, equivalently

\[
 P(1/n)(N)-1/N\ge1/(3N).                                  \tag{13}
\]

The clipped reciprocal potential `min(1/n,2/H)` equals `1/n` on
all reached states and their children. It therefore yields the exact
finite occupation bound
`E sum_(j<tau wedge J) 1/N_j <= 6/H`. The verifier checks this with
rational arithmetic; (13) is not a substitute for the real logarithmic
convexity step in (9).

## 5. Logarithmic moments and their limits

Let `Z_N=log m(U_N)` for a uniform source `U_N` in `1..N`. By taking
`H=floor(exp u)` in (2) and adjusting constants, for every fixed `R>0`

\[
 \sup_N\Pr(Z_N>u)\le B_R u^{-R}\qquad(u\ge u_R).             \tag{14}
\]

For `p>0` choose `R>p`. The layer-cake formula gives, for `L>=u_R`,

\[
 \mathbb E[Z_N^p\mathbf1_{\{Z_N>L\}}]
 =L^p\Pr(Z_N>L)+\int_L^\infty p u^{p-1}\Pr(Z_N>u)\,du
 \le B_R\frac{R}{R-p}L^{p-R}.                              \tag{15}
\]

Thus every fixed logarithmic power of the global minimum has uniformly
bounded source means and is uniformly integrable. If one also uses
the preceding written existence of the minimum law `pi`, truncation
and (15) give

\[
 \lim_{N\to\infty}\frac1N\sum_{n\le N}(\log m(n))^p
                =\sum_{a\ge1}\pi_a(\log a)^p<\infty.       \tag{16}
\]

Existence of `pi` is a separate written dependency of (16), not a
premise needed for (2), (14), or (15). These are moments of the
**minimum value**. They supply no bound for the time to attain that
minimum, the lifetime deficit `D`, the censored deficit `A_t`, or
positive powers of `m` itself.

## 6. Remaining gap and reproducibility

At a fixed floor the right side of (12) is a generally positive,
unspecified number. The exponent cannot be sent to infinity with
fixed constants or a fixed threshold: both depend on it. Additional
cycles or escaping orbits with a fixed finite initial minimum are
compatible with this tail estimate. Nothing here proves `pi_1=1`,
the all-source censored-deficit zero limit, or the full conjecture.

Run `python3 verify_cutoff_descent.py`. Its
[record](../results/cutoff-descent/verification.json) separates:

* 16 new kernel roots for the actual infinite-survival **predicate**,
  exact parity bounds and cutoff products, finite stopping and
  potential inequalities, and rational tangent-drift algebra;
* independent bounded ordinary-prefix survival checks, including the
  killed odd boundary and the correct one- and two-step clock shifts;
* finite first-odd-record checks with arbitrary minimum thresholds;
* exact rational auxiliary-chain distributions, compared with a
  separately evaluated recursive operator, and finite reciprocal
  occupation budgets;
* authenticated reuse of the two preceding verification manifests,
  without rerunning their large finite censuses.

The infinite-survival predicate in Lean is noncomputable; no positive
survival instance is asserted or tested. Finite live prefixes are not
counterexamples to Collatz. The verifier has no floating-point proof
decisions, and it does not establish (3), (9), or the infinite analytic
conclusions. The Lean file imports only the earlier finite transport
module and the standard library, not an axiom stating the mixing bound.
