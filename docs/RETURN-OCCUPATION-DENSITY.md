# Sampling densities accumulated over all count returns

**Collatz remains unresolved.** The previous return drift gives an
exponential moment for the number of cycles to balanced fusion under
the coherent binary law. This controls the sampling density accumulated
over **all nonfused returns**, including nested return prefixes. It also
gives a quantitative truncation estimate with a logarithmic factor.
These probability and integration arguments are written; fifteen new
kernel arithmetic roots and independent exact finite checks support them.

The [Lean module](../lean/ReturnOccupationDensity.lean) also identifies
a pointwise obstruction: the persistent-reversal family has a fixed
first-return prefix and separation one, followed by an arbitrarily long
second excursion. A cost depending only on that return's separation,
clock, and common count cannot pay for the excursion pointwise.

## 1. Why a scalar return cost is insufficient

The even residue `r=48 mod 64` has parity words `000011` and `101000`
for its adjacent pair. Its first positive count return is exactly six,
with common count two, and for every integer `q>=0`,

\[
 U^6(64q+48)=9q+8,\qquad U^6(64q+49)=9q+7.             \tag{1}
\]

These identities and the absence of an earlier return are kernel checked.
For even `j>=2`, take the previous persistent family
`n_j=8(64^j-1)/9`. The pair `2n_j,2n_j+1` belongs to this cylinder and
returns to

\[
                  (X,Y)=(2^{6j-2}+1,\ 2^{6j-2}).                \tag{2}
\]

Write `a=3j-1`, so these are `2^(2a)+1,2^(2a)`. The kernel proves

\[
 a_t(2^{2a}+1)>a_t(2^{2a})
                    \quad(0<t\le3a-2,\ a\ge2).                \tag{3}
\]

For `t<=2a`, the lower endpoint only halves while the upper endpoint's
first step is odd. At time `2a`, the upper odd count is `a`, by the
lifted known-cycle formula, and the lower endpoint is one with count
zero. During the remaining at most `a-2` steps, the lower count is
still less than `a`. This proves (3) without knowing the upper orbit's
eventual behavior.

The entire persistence window from [the earlier proof](REVERSAL-PERSISTENCE.md)
lies inside this second excursion. It contributes an unaveraged
negative drift at least `5(3j-4)/128`. Yet its initial return data are
always `(tau,a,D)=(6,2,1)`. Thus no finite function of those three data
alone bounds this excursion's accumulated pointwise negative drift.
The source cells remain rare; this does not refute an averaged estimate.

## 2. An exponential moment for the cycle count

Let `D_j` be the separation after `j` positive count returns, with
`D_0=1`, and absorb at zero. Let `N` be the number of return cycles
until fusion. Work under the coherent binary residue law, with the
fresh-prefix conditional estimates proved in the preceding written
arguments. Neither independent endpoint parities nor independent
attempts are assumed.

Put `V(D)=D^(1/4)` and `R=400^4`. The
[stopped-correction estimate](RETURN-CORRECTION-MOMENTS.md) gives

\[
 \mathbb E[V(D_{j+1})\mid\mathcal F_j]
       \le\frac{39}{40}V(D_j)+9
       \le qV(D_j)\quad(D_j>R),\qquad q=\frac{399}{400}.
                                                               \tag{4}
\]

Let `sigma` count cycles to first reach `D<=R`, starting from arbitrary
`D`. Killing the process at this event and iterating (4) gives

\[
 \Pr(\sigma>n)\le\frac{V(D)}{400}q^n\quad(n\ge0).
\]

For a start already in the set, `sigma=0` and the same upper bound is
harmless. For `1<s<1/q`, the nonnegative tail-sum identity yields

\[
 \mathbb E s^\sigma
  \le1+\frac{(s-1)V(D)}{400(1-sq)}.                            \tag{5}
\]

Use the previously established prescribed attempts with

\[
 M=140,\quad p=2^{-5180},\quad
 \delta=p/4096=2^{-5192},\quad s=1+\delta.
\]

Starting from a positive state in `D<=R`, run at most `M` cycles,
absorbing at zero. If needed, then wait to reach `D<=R` again. This
return can itself fuse the pair. Define the upper-bound attempt length
`L=M+sigma`, taking `sigma=0` if the state after `M` cycles is already
inside. On a successful attempt, the actual remaining cycle count is
at most `L`. A failed attempt means the pair remains positive after
this whole procedure.

The prescribed path gives probability at least `p` of fusion during
the first `M` cycles. Also `E V(D_M)<=400`, because the drift maps a
mean at most 400 to a mean at most 399. Applying (5) conditionally
at cycle `M`, the generating function of a failed attempt is bounded by

\[
 \mathbb E[s^L\mathbf1_{\rm failed}\mid\text{attempt start}]
 \le s^M\left(1-p+\frac{\delta}{1-sq}\right).                  \tag{6}
\]

Here failure is a subset of failure during the first `M` cycles;
fusion during reentry is included among successes.

The elementary inequalities

\[
 1-sq\ge1/800,\qquad s^{140}\le1+280\delta,
 \qquad(1+280\delta)(1-p+800\delta)\le1-p/2                    \tag{7}
\]

show that (6) is at most `rho=1-p/2<1`. For the middle inequality,
`(1+x)^m<=1/(1-mx)<=1+2mx` when `2mx<=1`; the kernel checks
the general integer identities with denominators cleared. The last
inequality is also kernel checked for every rational `0<=p<=1`.
The interpretation for real variables is the same polynomial argument.

Crucially, success during reentry need not have length at most `M`.
Instead (5) bounds the **whole** attempt:

\[
 \mathbb E s^L
 \le(1+280\delta)(1+800\delta)\le2.                            \tag{8}
\]

The weighted probability of reaching attempt `k` is therefore at most
`rho^(k-1)`. Sum the successful terminal contributions, using (8), to
obtain the written exponential moment

\[
 \boxed{\mathbb E(1+2^{-5192})^N\le A:=4/p=2^{5182}.}           \tag{9}
\]

The previous proof already established `N<infinity` almost surely;
alternatively the conditional success probability gives that fact.
No exponential moment of the **physical** fusion clock is asserted.
Its mean remains infinite.

## 3. The occupation measure of nonfused returns

Let `S_j` be the physical clock of the `j`th return and `T=S_N` the
physical fusion clock. Define a finite measure on paths and return
indices by

\[
 \int g\,d\nu
     :=\mathbb E\sum_{1\le j<N}g(D_j,S_j).
\]

This measure counts every nonfused return separately. Its total mass
is at most

\[
 C:=540\,2^{5180},
\]

the earlier upper bound for `E N`. Ancestor and descendant prefixes
can both contribute, so this is not a probability measure on a
prefix-free collection.

The existing physical tail `Pr(T>H)<=14 C/sqrt(H)` and (9) imply
a quantitative occupation-clock tail. For each integer `ell>=1`,

\[
 \nu(S>H)\le\mathbb E[N\mathbf1_{\{T>H\}}]
 \le\frac{14C\ell}{\sqrt H}+\frac{A s^{1-\ell}}{\delta}.
\]

Choose `ell=max(1,ceil(log(H)/(2 log(s))))` and set

\[
 A_T=14C+As/\delta,\qquad B_T=7C/\log s.
\]

Then

\[
 \boxed{\nu(S>H)\le\frac{A_T+B_T\log H}{\sqrt H}
                                    \quad(H\ge1).}             \tag{10}
\]

For separation, the earlier summed power budget gives, for `0<gamma<1/2`,

\[
 \int D^\gamma\,d\nu
 \le\frac{1+2m_\gamma C}{1-r_\gamma},\quad
 m_\gamma=1+\frac{7\gamma}{1-2\gamma},\quad
 r_\gamma=\tfrac12(2^{-\gamma}+(3/2)^\gamma).
\]

On `1/4<=gamma<1/2`, convexity of `r_gamma` and the two endpoint
root comparisons give `r_gamma<=39/40`. Also
`2m_gamma<=(7)/(1-2gamma)`. Thus, with `B=40(1+7C)`,

\[
                  \int D^\gamma\,d\nu\le\frac B{1-2\gamma}.
\]

For `u>=16`, take `gamma=1/2-1/log_2(u)` in Markov's inequality.
For `1<=u<16`, use `nu(total)<=C`. The resulting all-scale bound is

\[
 \boxed{\nu(D>u)\le\frac{B(1+\log_2 u)}{\sqrt u}
                                    \quad(u\ge1).}             \tag{11}
\]

Equations (10)--(11) imply that `D+1+S` has every `nu` moment of
power below `1/2`. In particular,

\[
 \boxed{\mathbb E\sum_{1\le j<N}D_j^\beta(1+S_j)^\alpha<\infty
 \quad(\beta\ge0,\ \alpha>0,\ \beta+\alpha<1/2).}              \tag{12}
\]

Indeed the integrand is at most `(D+1+S)^(beta+alpha)`, and the tail
of a sum is bounded by the sum of its two marginal tails. This argument
uses the finite measure `nu`; it makes no independence assumption.

## 4. The density accumulated over all returned endpoints

Restrict now to even adjacent initial inputs, as in the prior image
note. Index by `i` every nonfused count-return prefix. Write its total
clock `t_i`, even source residue `r_i`, common cumulative count `a_i`,
endpoint `x_i=U^(t_i)(r_i)`, separation `D_i>0`, and binary mass
`p_i=2^(-t_i)`. Define the ternary Haar columns and occupation density

\[
 F_i(z)=3^{a_i}\mathbf1_{\{z\equiv x_i\pmod{3^{a_i}}\}},\qquad
 K^*_\beta=\sum_i p_iD_i^\beta F_i.
\]

Each column has Haar integral one. The full density has finite mass
`M^*_beta=sum_i p_iD_i^beta` for `0<=beta<1/2`, by (12) or the
previous separation budget. Put `Mbar=max(1,M^*_beta)`.
Convexity and Jensen, applied to the weights `p_iD_i^beta/Mbar`, give

\[
 \boxed{\int K^*_\beta
       [\log(1+K^*_\beta/\overline M)]^\alpha\,d\mu_3
 \le\mathcal A^*_{\beta,\alpha}<\infty
       \quad(\beta\ge0,\ \alpha>0,\ \beta+\alpha<1/2),}         \tag{13}
\]

where
`A*_(beta,alpha)=(log 3)^alpha sum_i p_i D_i^beta(1+t_i)^alpha`.
Disjointness of the return prefixes is unnecessary for this mixture
inequality. Their total occupation mass supplies its normalization.

## 5. Truncation with an explicit logarithmic factor

Let `K*_(beta,H)` keep only returns with `t_i<=H`. Its Haar `L^1`
error is bounded by `integral D^beta 1_(S>H) dnu`. For `0<beta<1/2`,
split the layer-cake integral at `u=H`, use (10) below that threshold
and (11) above it, and put `c=1/2-beta`. This gives

\[
\boxed{\begin{split}
 \|K^*_\beta-K^*_{\beta,H}\|_1
 \le H^{\beta-1/2}\bigg[
 A_T+B_T\log H
 +\beta B\bigg(\frac{1+\log H/\log2}{c}
                  +\frac1{c^2\log2}\bigg)\bigg].
\end{split}}                                                   \tag{14}
\]

For `beta=0`, (10) gives (14) with the last term zero. Thus the error
is `O_beta((1+log H) H^(beta-1/2))`. Unlike the first-return estimate,
this bound includes every nonfused return; the extra logarithm has
not been removed. Ternary conditional projection at depth `L>=1`
has at most twice the right side of (14) with `H=L`, because all
columns with `t_i<=L` have depth `a_i<=L`.

## 6. Finite integer intervals retain controlled errors

At each total clock `t`, the selected return residues are a subset of
the full binary period. The existing cubic mass identity yields

\[
 \sum_{i:t_i=t}\lambda_i\le2^t,
 \qquad\lambda_i=3^{a_i}/2^{t_i}.
\]

The new kernel recurrence for cumulative column mass therefore proves
the integer form of

\[
                 \sum_{i:t_i\le H}\lambda_i\le2^{H+1}-2.
\]

The endpoint cap `D_i<2*3^(a_i)` now gives, for every `beta>=0`,

\[
 \sum_{t_i\le H}\lambda_iD_i^\beta
                 \le2^{\beta+1}(2\,3^\beta)^H.                 \tag{15}
\]

No infinite moment is claimed for `beta>=1/2`; (15) is a finite-depth
counting bound. For any interval `I` of `M>=1` nonnegative integers,
the prior kernel residue discrepancy gives

\[
 \left|\frac1M\sum_{x\in I}K^*_{\beta,H}(x)
                  -\sum_{t_i\le H}p_iD_i^\beta\right|
             \le\frac{2^{\beta+1}(2\,3^\beta)^H}{M}.            \tag{16}
\]

In the range of (13), its logarithmic moment on this interval is at most

\[
 \mathcal A^*_{\beta,\alpha}
 +\frac{2^{\beta+1}[(H+1)\log3]^\alpha(2\,3^\beta)^H}{M}.       \tag{17}
\]

The pointwise Jensen bound is applied before the residue count. This
proves uniform integrability for suitable growing cutoffs, for example
`H=floor(c log M)` with `0<c<1/log(2*3^beta)`. It does not justify
an infinite cutoff at a fixed integer interval. The previous constants
80 and 82 were for the first-return density; they are not asserted for
this larger occupation density.

## 7. Verification and remaining gap

Run `python3 verify_return_occupation_density.py`. The
[record](../results/return-occupation-density/verification.json) separates
the fifteen new kernel roots from exact finite cycle/occupation checks
and the written probability and real-analysis arguments (4)--(17).
It authenticates the correction, image, and persistence records.
No native evaluation, floating verification decision, or new external
theorem is used.

The accumulated density can now be controlled without discarding
later returns. The remaining transfer still pairs its columns with
actual future weighted gradients on intervals and at clocks depending
on the prefix. Logarithmic integrability alone does not bound that
pairing. No uniform weighted-energy bound, escape exclusion, exclusion
of further cycles, or full Collatz result is established.
