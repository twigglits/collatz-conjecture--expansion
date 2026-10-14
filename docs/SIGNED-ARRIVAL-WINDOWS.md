# Which arrival delays force reversed drift?

**Collatz remains unresolved.** The conditional power obstruction can be
localized to the **upward** part of the accumulated gradient. It does not
force large reversed negative budgets. In the opposite direction, a long
advance of the odd child's arrival forces reversed negative drift, but
arrival advances alone miss a cost incurred before either arrival.

The finite arithmetic inputs have kernel proofs in
[SignedArrivalWindows.lean](../lean/SignedArrivalWindows.lean). Real weight
profiles, infinite geometric sums, packing and Holder remain written.
Every use of an arrival clock presupposes an actual arrival at one; the
infinite power conclusion explicitly assumes universal convergence.
No external analytic theorem is used.

## 1. Oriented costs and clocks

Set `M=2^k`, `M<=n<2M`, `q=3n+2`, and retain

\[
 A_s=Mf_{k+s}(n),\qquad B_s=3Mf_{k+s}(q),\qquad
 f_t(v)=\frac{3^{a_t(v)}}{2^tU^t(v)}.
\]

Both profiles are between zero and one. Write `R_s` for the flag that
`a_t(n)>1+a_t(q)` at some `t<=k+s`. Define the cell costs

\[
 G_k^+(n)=\sum_{s\ge0}(B_s-A_s)_+^2,\quad
 G_k^-(n)=\sum_{s\ge0}(A_s-B_s)_+^2,\quad
 J_k(n)=\sum_{s\ge0}R_s A_s(A_s-B_s)_+ .                 \tag{1}
\]

Thus the earlier `G_k` is `G_k^++G_k^-`, and the annulus reversed
negative budget is `mathcal R_k=<J_k>_k/2`.

For a pair reaching one, put

\[
 \alpha=\tau(n)-k,\quad \beta=\tau(q)-k,\quad
 \Delta=\beta-\alpha=\tau(2n+1)-\tau(n)-1,\quad
 D_+=(\Delta)_+,\quad D_-=(-\Delta)_+.                     \tag{2}
\]

These clocks are nonnegative by the source-height bound. Let `E_k`
be nonfusion of `(2n,2n+1)` at physical clock `k+1`. Off `E_k` the
profiles agree for all future offsets and both delays vanish, by the
[previous prefix and arrival argument](CONDITIONAL-GRADIENT-POWER-OBSTRUCTION.md).

The local [simple-path packing result](FINITE-PATH-PACKING.md) gives
the first-hit floor `c=exp(-8192/3)>0` on every orbit reaching one.
Both normalized profiles are at least `c/2` until their respective
first arrivals. After arrival, either profile at age `h` is at most
`(3/4)^floor(h/2)`. Choose an integer `J` with `(3/4)^J<=c/4`, and
set `R=2J`.

## 2. The two windows have different meanings

If `beta>alpha`, every integer offset
`alpha+R<=s<beta` has `A_s<=c/4` and `B_s>=c/2`. Consequently

\[
 G_k^+\ge\frac{c^2}{16}(D_+-R)_+,
 \qquad D_+\le R\mathbf1_{E_k}+16c^{-2}G_k^+.             \tag{3}
\]

If `alpha>beta`, the window `beta+R<=s<alpha` has
`A_s>=c/2` and `B_s<=c/4`. This is a reversed cell, not just a
downward gap: the parent endpoint `X` is at least two before its first
arrival, whereas the child endpoint `Y` is in `{1,2}`. If its current
counts satisfied `a<=b+1`, then

\[
 \frac{A_s}{B_s}=3^{a-b-1}\frac YX\le1,
\]

contradicting `A_s>B_s`. Therefore the current count order has already
reversed, so the historical flag `R_s` equals one. Each term in this
window is at least `(c/2)(c/4)=c^2/8`. Hence

\[
 \boxed{J_k\ge\frac{c^2}{8}(D_--R)_+,\qquad
 D_-\le R\mathbf1_{E_k}+8c^{-2}J_k.}                       \tag{4}
\]

This is a **lower bound** on drift from a clock advance. Reversing the
inequality in (4) would be an error. The corresponding downward squared
cost also satisfies `G_k^- >= (c^2/16)(D_--R)_+`.

For a certified finite family with first-hit weights at least `3/4`,
take `R=12`, because `(3/4)^6<=3/16`. The exact finite constants are

\[
 G_k^+\ge\frac9{256}(D_+-12)_+,\qquad
 G_k^-\ge\frac9{256}(D_--12)_+,\qquad
 J_k\ge\frac9{128}(D_--12)_+.                              \tag{5}
\]

The finite floor `3/4` is not asserted for every positive integer.

## 3. Under universal convergence, upward powers must grow

**Assume every positive integer reaches one in this section.** Let
`F_k=<tau(n)-k>_k`, `eta_k=<1_Ek>_k`, and `Q_K=sum_(k<K)eta_k`.
The previous exact clock identity and mean parity bound give

\[
 \sum_{k<K}\langle D_+\rangle_k
 =2F_K+\sum_{k<K}\langle D_-\rangle_k\ge K.                \tag{6}
\]

The local fusion-clock estimate gives `Q_K<=A sqrt K`, where
`A=56 C_*` and `C_*=540*2^5180`. It samples complete binary residue
periods only at the actual prefix depth; no fresh-bit law is assumed
after that depth on a fixed integer interval.

Set `C=16/c^2`. From (3) and (6), for `K>=4R^2 A^2`,

\[
 \sum_{k<K}\langle G_k^+\rangle_k\ge K/(2C).
\]

Each `G_k^+` is supported on `E_k`. Holder on the disjoint union of
the normalized source intervals therefore proves, for every `p>1`,

\[
 \boxed{\sum_{k<K}\langle(G_k^+)^p\rangle_k
 \ge (2C)^{-p}A^{1-p}K^{(p+1)/2}.}                         \tag{7}
\]

In particular uniform powers of the upward accumulated gradient cannot
hold under universal convergence. This strengthens the previous
conditional result by identifying a direction that already carries
the required growth. Equation (6) supplies no lower growth for
`sum <D_->`; consequently neither (4) nor this argument forces
unbounded moments of `J_k` or `G_k^-`. Their boundedness is not proved
either. The first moments and fixed-offset energies remain undecided.

## 4. The additional cost before either arrival

For a convergent pair define

\[
 H_k(n)=\sum_{0\le s<\min(\alpha,\beta)}
                   R_s A_s(A_s-B_s)_+.                    \tag{8}
\]

The interval before the parent's arrival consists of (8) followed by
at most `D_-` offsets. Each latter term is at most one. Starting at
the parent's first arrival, let `a=A_alpha`. The exact cycle phases are
`A_(alpha+2j)=a(3/4)^j` and
`A_(alpha+2j+1)=a(3/4)^(j+1)`. Thus

\[
 \sum_{s\ge\alpha} A_s^2
 =a^2\frac{1+9/16}{1-9/16}=\frac{25}{7}a^2\le\frac{25}{7}.
\]

Off `E_k` the reversed integrand is zero even if this parent-square
majorant is positive. We obtain the two-sided comparison

\[
 \boxed{
 J_k\le H_k+D_-+\tfrac{25}{7}\mathbf1_{E_k},\qquad
 H_k+D_-\le(1+8c^{-2})J_k+R\mathbf1_{E_k}.}                 \tag{9}
\]

The second inequality uses `H_k<=J_k` and (4). Thus on convergent
bands, a uniform reversed first-moment bound is equivalent, up to
these fixed constants, to a uniform first-moment bound on the sum of
the pre-arrival cost and the negative clock advance. Neither bound
has been established for all bands. This is a decomposition of the
remaining difficulty, not an independent escape criterion for an
unknown nonconvergent pair.

The pre-arrival term really occurs. For `n=823`, `k=9`, `q=2471`,
the two first arrivals both have clock `86`, but exact replay gives

\[
 D_-=D_+=0,\qquad
 J_9(823)=H_9(823)=\frac{6289513358589}{491370708992000}>0.   \tag{10}
\]

In particular `J_k<=C D_-` cannot hold for any fixed multiplier on
all convergent pairs. This example does not disprove an estimate
with an additive constant, or an averaged estimate.

## Verification and remaining scope

Run `python3 verify_signed_arrival_windows.py`. Its
[verification record](../results/signed-arrival-windows/verification.json)
separates kernel roots, exact finite arrival and sign checks, full
future rational enclosures using known-cycle tails, and the written
conditional infinite result. Previous all-time energy records are
authenticated and compared with the newly computed signed totals.

No unrestricted gradient bound, reversed-drift bound, integer image
sampling theorem, criterion Q, escape exclusion or additional-cycle
exclusion follows. The next estimate must control the actual
pre-arrival cost together with negative arrival advances, or avoid
arrival clocks and bound the reversed integrand directly.
