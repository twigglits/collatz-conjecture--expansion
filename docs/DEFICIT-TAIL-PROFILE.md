# The whole remaining-clock tail and the limiting mean

**Status: written analysis under the same local written first-passage and
packing inputs as the deficit limiting law.** New finite algebra is
kernel checked separately. This note identifies two previously separate
extended moments and strengthens tightness to the whole tail profile.
It proves neither finiteness of that moment nor uniform integrability,
and it does not prove Collatz.

## 1. Removing the final clocks

For every positive start let `m(n)` be its global minimum, `T(n)` its
first attainment, and use the shortcut weights `W_h(n)`. Define, for
integers `L>=0`,

\[
 Q_L(n)=\sum_{0\le h<(T(n)-L)_+}(1-W_h(n)).               \tag{1}
\]

Thus `Q_0=D_m`, and `Q_L=0` for `L>=T(n)`. Each sequence
`Q(n)=(Q_L(n))_(L>=0)` belongs to the Banach space `c_0` of real
sequences tending to zero, with the supremum norm. It is nonnegative
and nonincreasing. Initial halvings preserve the entire sequence:
`Q(2^a n)=Q(n)`. If the truncation ends during those halvings, its
deficit is zero; otherwise they contribute only zero terms.

On the basin `B` of one, `T=tau`, and the exact summation-by-parts
identity gives

\[
 Q_L(n)=\sum_{j<T}(T-1-j-L)_+\ell_j(n)
       =\int(G-L)_+\,d\mu_n,                              \tag{2}
\]

where `G` and the weight-loss measure `mu_n` are those of
[Deficit clock moment](DEFICIT-CLOCK-MOMENT.md). Let
`Q^B(n)=1_(m(n)=1) Q(n)` and `D_B=Q^B_0`. Equation (2), with
`Q^B` on its left, then holds for every positive source. Off `B`
both sides are zero; no finite arrival time is assigned there.

Also,

\[
 0\le Q^B_L\le D_B,\qquad
 0\le D_B-Q^B_L=\int\min(G,L)\,d\mu_n\le L.             \tag{3}
\]

These profiles retain the times of the losses, rather than just their
total contribution. Their values for `L=0,1,...` determine the full
remaining-clock distribution away from clock zero by finite differences.

## 2. A bound simultaneous in every cutoff

Suppose first odd passage below a floor lands at `b` after `i`
shortcut steps. Put `t=T(b)`, `p=W_i(n)`, and
`A=sum_(h<i)(1-W_h(n))`. Assume the prefix weights are at least
`1-e`, where `0<=e<=1`.

If `L<=t`, split (1) at the landing:

\[
 Q_L(n)=A+pQ_L(b)+(1-p)(t-L).
\]

Because `0<=Q_L(b)<=t-L`, the earlier splice estimate yields

\[
                 0\le Q_L(n)-Q_L(b)\le e(i+t).          \tag{4}
\]

If `L>t`, then `Q_L(b)=0` and `(i+t-L)_+<=i`, so only a
part of the source prefix contributes. It is between zero and `ei`.
Therefore (4) holds **for every cutoff at once**. For two sources
with the same first odd landing,

\[
 \boxed{\|Q(n)-Q(n')\|_\infty
       \le e\max\{T(n),T(n')\}.}                        \tag{5}
\]

The same bound holds for `Q^B`, since common record landings preserve
the global minimum and hence basin membership.

As in [Deficit limiting law](DEFICIT-LIMIT-LAW.md), packing the
distinct odd inputs before passage supplies
`e(x)=min(1,(8192/3)x^(-1/20))`. Earlier even states need not all
exceed the passage floor; the weight estimate uses only odd inputs.

## 3. Convergence in the sequence space

Apply the finite coupling chains of the limiting-law note. For
`Y>=Z>=B_0` there is a coupling of odd uniform source laws at `Y`
and `Z` such that, outside probability `C(log B_0)^(-c)`, their
global minima agree and

\[
 \|Q(n_Y)-Q(n_Z)\|_\infty+|P(n_Y)-P(n_Z)|
      \le C'(T_{B_0}+1)Z^{-\gamma},\qquad
                  \gamma=\frac1{40\alpha^2}.             \tag{6}
\]

Here `alpha=1001/1000`, `P` is the terminal weight, and `T_(B_0)`
is the finite maximum minimum-attainment clock of odd sources in
`[B_0,2B_0)`. The proof is unchanged after substituting (5) for
the single-coordinate deficit comparison: along each good link the
clock is at most `T_(B_0)+C log u`, and the weighted errors sum
geometrically. No union bound over `L` is taken or needed.

First choose the fixed base `B_0` to make the failure small, then
send `Z` to infinity to absorb its finite clock. There is no effective
bound on `T_(B_0)` and no assertion that
`T_(B_0)B_0^(-gamma)` tends to zero.

The space `N_(>0) x c_0 x [0,1]` is complete and separable, using
a discrete metric on the first coordinate. Equation (6) makes the
source laws Cauchy in the Prokhorov metric, so they have a probability
limit there. This is stronger than coordinatewise convergence of
the profiles. A bound on their norms alone would not imply compactness
in `c_0`.

Dyadic summation and the exact initial-halving invariance give the same
law under uniform positive sources up to `X`. The continuous map
`(m,q,p) -> 1_(m=1)q` gives a probability law `Lambda` on `c_0` for
the restricted profiles `Q^B`. Its zero-coordinate marginal is exactly
the earlier law of `D_B`: retain the deficit on minimum label one and
put it at zero for the other labels.

Weak convergence gives uniform tightness of these probability laws.
Every compact subset of `c_0` has uniformly vanishing coordinate
tails: cover it by finitely many small norm balls around sequences
which individually vanish. Consequently, for each `epsilon>0`,

\[
 \boxed{\lim_{L\to\infty}\sup_{X\ge1}
   \frac1X\#\{n\le X:Q^B_L(n)>\epsilon\}=0.}             \tag{7}
\]

Finitely many early populations cause no difficulty because their
profiles have finite support. The statement also holds for the
unrestricted minimum profiles `Q` and for binary source bands.
This is uniform tail control **in probability**, not in mean.

## 4. Identification of the two extended means

The closed conditions
`q_L>=q_(L+1)>=0` and `0<=q_0-q_L<=L` pass to the limiting
profile. Write `Z=q_0` for a profile sampled from `Lambda`. Then
`Z` is finite almost surely, but its expectation can be infinite.

For fixed `L`, the function `q -> q_0-q_L` is continuous and
bounded by `L` on these laws. It can be clamped to `[0,L]` to give
a bounded continuous function on all of `c_0`. Weak convergence,
(2)--(3), and the previously proved total-variation limit
`nu_X=(1/X)sum mu_n -> mu` give

\[
 \mathbb E_\Lambda(q_0-q_L)
      =\lim_X\frac1X\sum_{n\le X}(D_B(n)-Q^B_L(n))
      =\int\min(G,L)\,d\mu.                             \tag{8}
\]

Because each limiting profile lies in `c_0`, `q_L` decreases to zero.
Monotone convergence on both sides of (8) now proves

\[
 \boxed{\mathbb E_\Lambda Z
       =\int G\,d\mu
       =\sum_{\substack{v>1\text{ odd}\\v\in B}}
                    \frac{\tau(Uv)d_v}{3v+1}.}           \tag{9}
\]

Equality is in `[0,infinity]`. This closes the identification left
open in the clock-moment note. It does **not** exchange the unbounded
source mean with its limit. Both sides of (9) may be infinite, and a
finite value would still not by itself give uniform integrability of
the source deficits.

## 5. Uniform integrability is the remaining issue

On every source, (3) implies the useful scalar inequality

\[
                         (D_B-K)_+\le Q^B_K.             \tag{10}
\]

Thus uniform vanishing of the mean clock tails implies uniform
integrability of the source deficits. Conversely, for every `K>0`
and `epsilon>0`, `0<=Q^B_L<=D_B` gives

\[
 \mathbb E_X Q^B_L
 \le\epsilon+K\Pr_X(Q^B_L>\epsilon)
                    +\mathbb E_X(D_B-K)_+.              \tag{11}
\]

If the deficits are uniformly integrable, choose `K` for the last
term, then use (7), then send `epsilon` to zero. With the previous
clock-moment criterion, this proves the equivalence of:

* uniform integrability of `D_B` under all uniform prefix populations;
* `lim_L sup_X mean Q^B_L=0`;
* convergence of the source means to the **finite** common value in (9).

None of these equivalent conditions is established here. A uniform
bound on first moments alone remains weaker than uniform integrability.

There is a sharper conditional consequence for the original pre-arrival
cost. Let `eta_k` be the fraction of parents in `[2^k,2^(k+1))`
whose binary sibling pair has not balanced-fused by physical clock
`k+1`. The existing [coalescence estimates](SIGNED-ARRIVAL-WINDOWS.md)
give `eta_k -> 0`. The pre-arrival cost `H(n)` is zero outside this
set. With the full parent-band denominator, (3) and the transfer
`H<=(23/3)D(3n+2)+1` give, for every integer `L>=0`,

\[
 \frac1{2^k}\sum_{\substack{2^k\le n<2^{k+1}\\3n+2\in B}}H(n)
 \le\bigl((23/3)L+1\bigr)\eta_k
                     +46\sup_X\mathbb E_X Q^B_L.        \tag{12}
\]

The factor six again comes from the distinct child targets below
`6*2^k`. Under any of the three equivalent conditions above, first
send `k` to infinity at fixed `L`, then send `L` to infinity. The
known-child pre-arrival mean would therefore tend to **zero**, not
merely remain bounded. Negative arrival advances, post-arrival drift,
and pairs with an unknown child remain separate unresolved quantities.

## Verification

Run `python3 verify_deficit_tail_profile.py`; the
[record](../results/deficit-tail-profile/verification.json) separates
finite kernel algebra, exact finite tail profiles, and the written
infinite-dimensional probability argument. No external reciprocal
density floor is needed for this note. The analytic first-passage,
packing and coalescence inputs retain their earlier written status.
