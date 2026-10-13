# An obstruction to uniform complementary moments of accumulated gradients

**Collatz remains unresolved.** The actual returned gradients do not
have a uniform exponential moment of the form `exp((G/C)^p)` for any
`p>1`, where `G` is their accumulated squared difference over time and
`C` is fixed. The obstruction occurs inside the single return cylinder
`(tau,a,D)=(6,2,1)`, on its actual endpoint intervals and progressions.

This rules out one proposed use of the new
[all-return density estimate](RETURN-OCCUPATION-DENSITY.md): summing
the time contributions first and then using a uniform complementary
Orlicz bound against `L(log L)^alpha`, with `alpha<1`. It does not
disprove a direct averaged energy estimate or one that uses the
dependence between the density and the gradients.

Eight arithmetic roots are kernel checked in
[GradientOrliczObstruction.lean](../lean/GradientOrliczObstruction.lean).
The real exponential, convex-conjugate, and norm conclusions below are
written deductions from those inputs and the preceding family proofs.

## 1. Use the actual returned interval

For an integer `m>=0`, put

\[
 Q_m=2^{12m+6},\qquad M_m=9Q_m,\qquad
 I_m=[9Q_m+8,\ 18Q_m+8)\cap\mathbb Z.
\]

This interval contains exactly `M_m` integers. The fixed even source
prefix `r=48 mod 64` has first count return six, common count two,
and returned endpoints

\[
                         (9q+8,\ 9q+7).
\]

For source annulus `[64Q_m,128Q_m)`, its source quotient runs through
`Q_m<=q<2Q_m`. Thus the exact image progression is

\[
          P_m=\{9q+8:Q_m\le q<2Q_m\}\subset I_m,
\]

with `Q_m` elements. No progression is replaced by an interval in
these definitions.

The kernel proves `Q_m=1 mod 9`. Consequently

\[
 q_m=16\lfloor Q_m/9\rfloor+1,\qquad
 x_m=9q_m+8=16Q_m+1=2^{12m+10}+1
\]

satisfies `Q_m<=q_m<2Q_m`. In particular the exceptional endpoint
`x_m` belongs to both `P_m` and `I_m`, and `x_m-1=2^(12m+10)`.
These are the returned endpoints of the previously proved persistent
family, with its parameter `j=2m+2`.

## 2. The accumulated squared gradient grows at one point

For positive `x`, retain

\[
 f_t(x)=\frac{3^{a_t(x)}}{2^tU^t(x)}.
\]

Define the finite accumulated gradient on `I_m` by

\[
 G_m(x)=\sum_{h=0}^{6m+1}
 \left[M_m\{f_{12m+12+h}(x)-f_{12m+12+h}(x-1)\}\right]^2.
                                                               \tag{1}
\]

Every input is positive, and every sum is finite. No eventual
convergence assertion is used to define or estimate it.

The exact scale identity is
`M_m/2^(12m+12+h)=9/2^(h+6)`. The retained-parent and child-ceiling
proofs therefore give, for every `0<=h<=6m+1`,

\[
 M_m f_{12m+12+h}(x_m)\ge\tfrac12,\qquad
 M_m f_{12m+12+h}(x_m-1)\le\tfrac{27}{64}.                      \tag{2}
\]

The kernel proves these two statements with denominators cleared,
as well as the general cross-product subtraction and squared-gap
inequalities. Dividing by positive denominators and summing gives

\[
 \boxed{G_m(x_m)\ge L_m:=\frac{25(6m+2)}{4096}.}                \tag{3}
\]

The window in (1) is entirely inside the second count excursion of
the pair, by the preceding no-return theorem. The equal-count data
before it are fixed; its image height is what increases with `m`.

## 3. Failure of every fixed superlinear exponential bound

Fix real `p>1` and `C>0`. A single point of `I_m` gives

\[
 \frac1{M_m}\sum_{x\in I_m}
             \exp((G_m(x)/C)^p)
       \ge\frac{\exp((L_m/C)^p)}{M_m}.                         \tag{4}
\]

Here `L_m` grows linearly in `m`, while
`log M_m=(12m+6)log 2+log 9` does also. Since `p>1`, the logarithm
of the right side in (4), `(L_m/C)^p-log M_m`, tends to infinity.
Hence

\[
 \boxed{\sup_m\frac1{M_m}\sum_{x\in I_m}
              \exp((G_m(x)/C)^p)=\infty
                \quad\text{for every }p>1,\ C>0.}             \tag{5}
\]

Exactly the same proof applies to the actual progression average,
with denominator `Q_m` in place of `M_m`. Thus this failure is not
caused by including unsampled residues in the reference interval.

There is a quantitative norm statement. Use the Luxemburg convention

\[
 \|G\|_{\operatorname{Exp}L^p(I)}
  =\inf\left\{C>0:\frac1{|I|}\sum_{x\in I}
                       (e^{(G(x)/C)^p}-1)\le1\right\}.
\]

The contribution of `x_m` alone proves

\[
 \boxed{\|G_m\|_{\operatorname{Exp}L^p(I_m)}
       \ge\frac{L_m}{[\log(M_m+1)]^{1/p}}.}                    \tag{6}
\]

On `P_m`, replace `M_m+1` by `Q_m+1`. Thus these norms grow at
least as a positive constant times `m^(1-1/p)`. The full accumulated
gradient over a longer clock range, including all future clocks,
has the same lower bounds whenever that sum is defined, by
nonnegativity; no finiteness of the infinite sum is claimed.

For an explicit large finite certificate, take `m=16384`, `p=2`,
and `C=1`. The kernel verifies

\[
 [25(6m+2)]^2>4096^2(12m+9+100000).
\]

The elementary bounds `log 2<1` and `log 9<3` then make (4) larger
than `exp(100000)`. The latter bounds follow from `e>2` and
`e^3>1+3+9/2+27/6>9`. This certificate uses the all-parameter
family theorem; it is not a direct orbit enumeration at that large
source size. All logarithm and exponential steps are written.

## 4. The complementary norm required by the density bound

For `0<alpha<1`, let

\[
 \Phi_\alpha(u)=u[\log(1+u)]^\alpha,\qquad
 \Psi_\alpha(v)=\sup_{u\ge0}\{uv-\Phi_\alpha(u)\}.
\]

The current return-density estimates control the integral of
`Phi_alpha(K/Mbar)` for `alpha<1/2` in the unweighted case, and for
`alpha+beta<1/2` with separation weight `beta`. A direct application
of Young's inequality to the pairing with `G_m` would require a
bound for `Psi_alpha(G_m/C)` at some fixed `C>0`.

Its growth can be bounded without citing an Orlicz duality theorem.
For `v>=2`, choose `u=exp((v/2)^(1/alpha))-1`. Then
`Phi_alpha(u)=uv/2`, and `exp(t)-1>=exp(t)/2` for `t>=1` gives

\[
 \Psi_\alpha(v)\ge\frac v4\exp((v/2)^{1/\alpha})
             \ge\tfrac12\exp((v/2)^{1/\alpha}).                \tag{7}
\]

Since `L_m/C` eventually exceeds two, (3) and (7) prove

\[
 \boxed{\sup_m\frac1{M_m}\sum_{x\in I_m}
                  \Psi_\alpha(G_m(x)/C)=\infty
                         \quad(0<\alpha<1,\ C>0).}            \tag{8}
\]

The progression version fails too. In particular the complementary
exponential power `p=1/alpha>2` demanded by the currently available
`alpha<1/2` estimates cannot have a uniform norm for these accumulated
actual gradients. The lower bound (6) grows like `m^(1-alpha)`.

This is specifically an obstruction to **one uniform complementary
norm after summing the time contributions**. It does not rule out
pairing contributions at individual clocks, keeping more information
about their supports, or an estimate adapted to the actual density.

## 5. The averaged energy question remains open

The exceptional point contributes only `L_m/M_m` to the lower bound
for the ordinary interval mean of `G_m`; that quantity tends to zero
and is summable over `m`. The exponential obstruction in (5) does
not prove that those ordinary means are unbounded.

The fixed return column itself is `9/64` on `x=8 mod 9` and zero
elsewhere. It is bounded. Larger return densities have additional
columns, but no lower bound for their correlation with `G_m` is
deduced here. In particular this note does not disprove a bounded
energy subsequence, the whole-annulus loss comparison, or Collatz.

A route through a uniform complementary norm would need materially
different integrability bounds or a different aggregation of the
gradients. For example, this family alone does not rule out an ordinary
exponential norm (`p=1`) at a sufficiently large scale. Such a bound,
and the corresponding stronger density estimate, remain unproved.

## 6. Verification boundary

Run `python3 verify_gradient_orlicz_obstruction.py`. The
[verification record](../results/gradient-orlicz-obstruction/verification.json)
separates eight new kernel roots, independent exact finite returned-
gradient checks, and the written norm and conjugate deductions.
It authenticates the earlier occupation and persistence records.
No floating arithmetic, native evaluation, or new external theorem
is used in the verification.
