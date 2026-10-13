# Quadratic image energy and power moments of all-return densities

**Collatz remains unresolved.** The ternary density accumulated over
every nonfused count return satisfies the following written theorem:

\[
 \boxed{K^*_\beta\in L^p(\mu_3)
   \quad\text{for }0\le\beta<\tfrac12,
          \quad 1\le p<\frac{10}{9+2\beta}.}                    \tag{1}
\]

Here the source law is coherent uniform binary residues and `mu_3` is
additive ternary Haar probability. In particular, `K*_0` has every
power moment strictly below `10/9`. This improves the previous
logarithmic moment range. It supplies neither a bound for its pairing
with the actual future weighted gradients nor a bounded subsequence
of the actual energy.

[BinaryImageEnergy.lean](../lean/BinaryImageEnergy.lean) proves eleven
arithmetic roots. The real-valued energy estimates, finite-fibre
ordering, interpolation, and the infinite-density theorem (1) are
written arguments. They reuse the written occupation-clock tail and
separation moments in [RETURN-OCCUPATION-DENSITY.md](RETURN-OCCUPATION-DENSITY.md).
No new external theorem is a dependency.

The quotient-counting idea was suggested by Lucas Valbuena's
[Quadratic cylinder energy and integrability of the Syracuse law](https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/quadratic-cylinder-energy.tex)
(8 October 2026). We give the complete adaptation to a finite binary
source period below. Its mass identities and interpolation use the
project's return law; no stationary-law result or Tao mixing theorem
is used in this argument.

## 1. The full finite image law

For `t>=0` and `0<=r<2^t`, set

\[
 a_r=\operatorname{wt}_t(r),\qquad x_r=U^t(r),\qquad
 N_r=2^t x_r-3^{a_r}r\ge0.
\]

The affine source lift is
`U^t(2^t q+r)=3^(a_r)q+x_r`. Its normalized image column on ternary
integers is

\[
 F_r(z)=3^{a_r}\mathbf1_{\{z\equiv x_r\pmod{3^{a_r}}\}}.
\]

Define the full image density

\[
 \rho_t(z)=2^{-t}\sum_{0\le r<2^t}F_r(z),\qquad
                         \int\rho_t\,d\mu_3=1.                \tag{2}
\]

The input `r=0` is allowed in this finite residue law. This is not a
claim about the infinite orbit of a uniformly sampled positive integer.
At `t=0` the single column is the constant function one.

## 2. An injective quotient in each image fibre

Fix a count `a` and an image residue `v mod 3^a`. The fibre consists of
the sources with `a_r=a` and `x_r=v mod 3^a`. On it,

\[
                       N_r\equiv2^t v\pmod{3^a}.              \tag{3}
\]

If two sources in the full binary period have the same count and
numerator, subtracting their affine equations shows that
`2^t` divides `3^a(r-s)`. Coprimality forces `r=s mod 2^t`, hence
`r=s` in this period. Combined with (3), this makes

\[
                  q_r=\lfloor N_r/3^a\rfloor
\]

injective within the fibre. The three kernel roots
`source_eq_of_numerator_eq`, `numerator_image_residue`, and
`quotient_injective_on_fibre` include `t=0` and `a=0`.

Let the fibre have cardinality `m`. Sort its distinct nonnegative
quotients increasingly, with indices `j=0,...,m-1`. Then `q_j>=j`,
so

\[
 3^a m^2\le3^a m(m+1)
       \le2\sum_{r\text{ in fibre}}(3^a+N_r).                 \tag{4}
\]

The finite sorting step is written. The kernel root
`ranked_numerator_cost` checks the last bound for any enumeration
satisfying these rank inequalities, with all denominators cleared.

## 3. Two exact full-period mass identities

The previous cubic identity and the new numerator identity are

\[
 \sum_{r<2^t}3^{a_r}=4^t,\qquad
                   4\sum_{r<2^t}N_r=t4^t.                    \tag{5}
\]

Both hold at every depth by kernel induction. For the second, the
children of each depth-`t` source satisfy

\[
 N_{t+1}(r)+N_{t+1}(2^t+r)=4N_t(r)+2^t.
\]

Summing gives `S_(t+1)=4S_t+4^t`, starting from `S_0=0`, hence (5).
Equivalently, the mean additive correction `N_r/2^t` is `t/4`.
The combined cost identity is

\[
              4\sum_{r<2^t}(3^{a_r}+N_r)=(t+4)4^t.            \tag{6}
\]

## 4. Quadratic finite image energy

Let `rho_(t,a)` be the part of (2) with count `a`, and let `m_(a,v)`
be the fibre sizes. Since all columns in this component have the
same ternary depth,

\[
 \|\rho_{t,a}\|_2^2
       =\frac{3^a}{4^t}\sum_{v\bmod3^a}m_{a,v}^2
       \le\frac2{4^t}\sum_{r:a_r=a}(3^a+N_r).                 \tag{7}
\]

There are at most `t+1` counts. Pointwise Cauchy--Schwarz, followed
by (6), gives

\[
 \boxed{\|\rho_t\|_2^2
       \le(t+1)\sum_{a=0}^t\|\rho_{t,a}\|_2^2
       \le\frac{(t+1)(t+4)}2.}                                \tag{8}
\]

In particular `||rho_t||_2<=t+2`; its squared integer comparison is
kernel checked. This estimate uses collisions in each image fibre.
Replacing the columns by their individual norms before counting those
collisions would lose this polynomial bound.

## 5. Summing return layers and interpolating

Retain the all-return notation from the occupation note: a prefix
`i` has total clock `t_i`, even source `r_i`, common count `a_i`,
first endpoint `x_i=U^(t_i)(r_i)`, separation `D_i>0`, binary mass
`p_i=2^(-t_i)`, and column `F_i`. It is stopped only at balanced
fusion. The density includes every nonfused return, so prefixes from
different clocks need not be disjoint.

At any one clock `t`, these sources are a subset of the full period
with each source appearing at most once. Thus

\[
 \kappa_t=\sum_{i:t_i=t}p_iF_i\le\rho_t,
 \qquad K^*_{0,H}=\sum_{t=1}^H\kappa_t.
\]

Minkowski and (8) prove

\[
 \boxed{\|K^*_{0,H}\|_2
       \le\sum_{t=1}^H(t+2)=\frac{H(H+5)}2\le3H^2
                                                  \quad(H\ge1).} \tag{9}
\]

The written occupation-clock bound already proves, with explicit
finite constants `A=A_T`, `B=B_T` defined in that note,

\[
 \|K^*_0-K^*_{0,H}\|_1
                    \le(A+B\log H)H^{-1/2}.                   \tag{10}
\]

This is an all-return bound, including later nested prefixes. Set
`Delta_j=K*_(0,2^(j+1))-K*_(0,2^j)` for `j>=0`. By positivity,
(9), and (10),

\[
 \|\Delta_j\|_1\le(A+Bj\log2)2^{-j/2},\qquad
 \|\Delta_j\|_2\le12\,2^{2j}.                                \tag{11}
\]

For `1<p<2`, put
`theta=(2-p)/p`, `eta=2(p-1)/p`, so `theta+eta=1`.
Hölder interpolation now gives

\[
 \|\Delta_j\|_p
 \le12^\eta(A+Bj\log2)^\theta
                 2^{-j(5/p-9/2)}.                            \tag{12}
\]

This is summable precisely in the range used here, `1<p<10/9`.
The nonnegative partial densities converge monotonically to `K*_0`;
finite Minkowski and monotone convergence therefore prove its `L^p`
membership. No convergence of a stationary law is required.

For example, a finite explicit norm bound is

\[
 C_p=3+
 \frac{12^\eta(A+B\log2)^\theta}
       {(1-2^{-(5/p-9/2)})^2},\qquad \|K^*_0\|_p\le C_p.       \tag{13}
\]

Indeed `(A+Bj log2)^theta<=(A+B log2)^theta(1+j)` and
`sum_(j>=0)(1+j)q^j=(1-q)^(-2)`. These constants are very large,
as they inherit the explicit return-cycle budget. No assertion is
made at or above the endpoint `p=10/9`.

## 6. Separation weights and finite interval transfer

For `0<beta<gamma<1/2`, apply Hölder pointwise to finite column
sums and then pass monotonically to get

\[
 K^*_\beta\le(K^*_\gamma)^{\beta/\gamma}
                    (K^*_0)^{1-\beta/\gamma}.                 \tag{14}
\]

The occupation separation budget gives `M*_gamma=||K*_gamma||_1<infinity`.
Combining it with (13), if

\[
 \frac1p=\frac\beta\gamma+
                \frac{1-\beta/\gamma}{p_0},\qquad1<p_0<10/9,
\]

then

\[
 \|K^*_\beta\|_p\le(M^*_\gamma)^{\beta/\gamma}
                                  C_{p_0}^{1-\beta/\gamma}.
\]

Letting the permissible parameters approach `gamma=1/2` and
`p_0=10/9` from below, and using the inclusion of larger `L^p`
spaces into smaller ones on a probability space, proves (1).
The case `beta=0` was proved directly and `p=1` is the prior mass
bound. It follows that, for each fixed `beta<1/2`, **every finite
logarithmic moment order** is now allowed for `K*_beta`. This
supersedes the restriction `beta+alpha<1/2` for mere membership;
the earlier explicit logarithmic constants and cutoff errors remain
valid in their stated ranges.

There is a separate statement on ordinary integer intervals. Since
`a_i<=t_i<=H`, the truncated `K*_(beta,H)` is periodic modulo `3^H`.
For any nonnegative function `g` with period `P` and any interval `I`
of `M>=1` integers, each residue occurs at most `M/P+1` times. Hence

\[
 \frac1M\sum_{x\in I}g(x)
 \le\left(1+\frac PM\right)\frac1P\sum_{v=0}^{P-1}g(v).
\]

With `g=(K*_(beta,H))^p`, `P=3^H`, and the Haar bound above,

\[
 \boxed{\frac1M\sum_{x\in I}K^*_{\beta,H}(x)^p
       \le\left(1+\frac{3^H}{M}\right)\|K^*_\beta\|_p^p.}       \tag{15}
\]

This is uniform over the interval location whenever `3^H<=M`.
It does not justify an infinite cutoff at a fixed integer interval.
For Haar-measurable sets `E`, the same `L^p` theorem gives the power
modulus `integral_E K*_beta <= ||K*_beta||_p mu_3(E)^(1-1/p)`.

## 7. Verification and the remaining comparison

Run `python3 verify_binary_image_energy.py`. The
[record](../results/binary-image-energy/verification.json) separates
eleven fresh kernel roots, independent exact finite image and return
checks, and the written probability and analysis in (1)--(15).
Finite checks do not replace the infinite interpolation argument.
No native evaluation or floating-point verification decision is used.

The [gradient exponential obstruction](GRADIENT-ORLICZ-OBSTRUCTION.md)
still holds. Stronger density integrability changes what complementary
estimate could suffice: in the unweighted case, Hölder would require
a power norm of order greater than ten for the relevant accumulated
gradients. The exceptional-point family does not disprove such a
bound, since its contribution to each fixed power moment tends to
zero. No uniform bound of this kind is proved here. Prefix-dependent
clocks, image scales, and gradient correlations must also be retained
in the actual transport. The actual-energy bound remains `O(sqrt(s))`;
escape and additional cycles remain unexcluded.
