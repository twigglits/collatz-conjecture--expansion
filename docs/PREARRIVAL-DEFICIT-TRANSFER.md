# Pre-arrival drift and a single trajectory's lifetime weight deficit

**Collatz remains unresolved.** The pre-arrival cost has a useful
one-trajectory characterization. A uniform pointwise bound for it is
equivalent, up to explicit constants, to bounding a lifetime weight
deficit on the known convergent basin. Such a bound would in particular
give a uniform linear arrival-clock bound on the convergent starts
coprime to three. None of these bounds is proved here.

An explicit infinite family also rules out charging the pre-arrival
cost to the parent's losses during that same interval. A separate exact
404-bit convergent example exceeds even the parent's complete future
loss budget with multiplier one. These are obstructions to pointwise
charges; they do not rule out an averaged estimate or an arbitrary
multiplier for complete future losses.

Thirteen arithmetic roots in
[PrearrivalDeficitTransfer.lean](../lean/PrearrivalDeficitTransfer.lean)
support the affine construction, count reversal and retention bounds.
The real sums, limits, boundedness equivalence and clock consequence
are **written** arguments. No external theorem, packing estimate or
universal-convergence hypothesis is used in this note.

## 1. A lifetime deficit, defined only for a convergent start

Let `B` be the basin of one under the shortcut map `U`. For `v in B`,
let `tau(v)` be its first arrival at one and define

\[
 W_h(v)=\frac{v3^{a_h(v)}}{2^hU^h(v)},\qquad
 D(v)=\sum_{0\le h<\tau(v)}(1-W_h(v)).                    \tag{1}
\]

Each `D(v)` is finite and nonnegative. The question concerns their
supremum, not the already finite sum for a fixed known start. Exact
one-step factorization gives

\[
 D(1)=0,\quad D(2v)=D(v),\quad
 (3v+1)D(v)=3vD(Uv)+\tau(Uv)\quad(v>1\text{ odd}).        \tag{2}
\]

For the odd identity, after the first step the weight is
`r W_h(Uv)` with `r=3v/(3v+1)`. Summing `1-rW_h` for the remaining
`tau(Uv)` clocks proves (2). In particular

\[
 \tau(v)\le(3v+1)D(v)+1\quad(v>1\text{ odd}).             \tag{3}
\]

Write any convergent `v` as `2^h o`, with `o` odd. Doubling preserves
`D` and adds one arrival clock. If `o>=3`, (3) and `h+1<=2^h` give

\[
 \frac{\tau(v)}v
 \le\frac{h+1}{2^ho}+\frac{3+1/o}{2^h}D(o)
 \le\frac13+\frac{10}{3}D(v).
\]

If `o=1`, use `h/2^h<=1/2` (also valid at `h=0`). Thus

\[
 \boxed{\frac{\tau(v)}v\le\frac{10}{3}D(v)+\frac12
                       \quad(v\in B).}                    \tag{4}
\]

## 2. A finite pre-arrival cost without assuming both starts converge

Let `n>=1`, `q=3n+2 in B`, `k=floor(log_2 n)` and `M=2^k`.
Set `A_t=M f_t(n)`, `B_t=3M f_t(q)`, using the physical parent
clock `t`. Let `T` be the first clock at which **either** endpoint
reaches one. It exists because `q in B`, even if the parent's future
is unknown. Define

\[
 H(n)=\sum_{k\le t<T} R_t A_t(A_t-B_t)_+,                 \tag{5}
\]

where `R_t` flags a historical count reversal
`a_i(n)>1+a_i(q)` for some `i<=t`. When both starts converge, (5)
is exactly the previous [pre-arrival cost](SIGNED-ARRIVAL-WINDOWS.md).

Write `A_0=M/n`, `B_0=3M/q`. Monotonicity gives

\[
 (A_t-B_t)_+\le A_0-B_0+B_0(1-W_t(q)),\qquad
                         A_0-B_0=\frac{2M}{nq}.
\]

Both initial profiles are at most one. Dropping the reversal flag
and extending the finite sum through `tau(q)-1` proves

\[
 H(n)\le\frac{2\tau(q)}q+D(q)
       \le\boxed{\frac{23}{3}D(q)+1}.                      \tag{6}
\]

This is a one-sided upper bound for a particular pre-arrival cost.
It does not control the drift after the child has reached one.

## 3. Affine clones give the converse bound

Fix a convergent `v>1` with `v=1 mod 9`. For integers `j>=1`, put

\[
 n_j=\frac{8(64^jv-1)}9,\quad q_j=3n_j+2,\quad
 a=3j-1,\quad T_j=6j+3,\quad X_j=3^av+1.
\]

The generalized affine-family identity, proved in the kernel, is

\[
 U^{T_j}(n_j)=X_j,\quad a_{T_j}(n_j)=a+2,\qquad
 U^{T_j}(q_j)=v,\quad a_{T_j}(q_j)=1.                    \tag{7}
\]

The child's first two steps lead to `2^(6j+1)v`, followed by
halvings to `v`; it has not visited one before this clock.

Choose `ell>=3` by `2^ell<=8v/9<2^(ell+1)`. The source band is
exactly `k_j=6j+ell`: from `9n_j+8=8*64^j v`, the integer lower
bound loses less than one and therefore still gives `2^k_j<=n_j`.
Put

\[
 h_0=\ell-3,\qquad b_v=\frac{9\,2^\ell}{8v}\in(1/2,1].
\]

Take `j` large enough that `a>=tau(v)`. Then `X_j>2^tau(v)`.
Since an orbit decreases by at most a factor two per step, the parent
cannot reach one before the child. Nor could it have reached one
earlier than `T_j`, since its endpoint there exceeds two. The first
arrival of either endpoint is consequently `T_j+tau(v)`.

For `0<=h<tau(v)`, the original even/odd child counts are at least
`a+2` and at most `2+h`, respectively. The current count order is
therefore reversed. The profiles at `T_j+h` are exactly

\[
 A=b_v\frac{X_j-1}{X_j}W_h(X_j),\qquad B=b_vW_h(v).        \tag{8}
\]

The elementary [retention bound](REVERSAL-PERSISTENCE.md),
`W_h(X)>=3X/(3X+2^h-1)`, makes `A` tend to `b_v` for each of
these finitely many clocks. Hence

\[
 \boxed{\lim_{j\to\infty}H(n_j)
   =b_v^2\sum_{h_0\le h<\tau(v)}(1-W_h(v)).}               \tag{9}
\]

This limit does not assume that the parent eventually converges.
It uses only the displayed finite prefixes and the certified arrival
of `v`. There is also an explicit finite error bound, when `a>=tau(v)`:

\[
 0\le b_v^2\sum_{h_0\le h<\tau(v)}(1-W_h(v))-H(n_j)
 \le\frac{2b_v^2}{3X_j}\bigl(2^{\tau(v)}+2\tau(v)\bigr).  \tag{10}
\]

Indeed `0<=b_v-A<=(b_v/(3X_j))(2^h+2)`, and the function
`A(A-B)_+` on `0<=A<=b_v` has Lipschitz constant at most `2b_v`.
Summation of the geometric bound gives (10).

The part omitted from (9) is uniformly small. Retention also gives
`1-W_h(v)<=(2^h-1)/(3v)`, so

\[
 \sum_{h<h_0}(1-W_h(v))
 \le\frac{2^{h_0}-1}{3v}<\frac1{27}.                       \tag{11}
\]

Here `2^ell<=8v/9` and `h_0=ell-3`; at `h_0=0` the empty sum
is zero. Every positive integer coprime to three can be multiplied
by some `2^e`, `0<=e<=5`, to become one modulo nine. This finite
unit-class fact is kernel checked. Doubling changes neither `D`
nor convergence, so (9)--(11) apply to every such convergent start;
the exceptional `v=1` has zero deficit.

## 4. Quantitative equivalence and its clock consequence

Use extended nonnegative suprema

\[
 D_*:=\sup_{v\in B,\,3\nmid v}D(v),\qquad
 H_*:=\sup_{n\ge1,\,3n+2\in B}H(n).
\]

Equations (6) and (9)--(11) prove

\[
 \boxed{\tfrac14(D_*-1/27)_+\le H_*\le\tfrac{23}{3}D_*+1.} \tag{12}
\]

The statement includes the case of an infinite supremum. In particular,
`H_*<infinity` if and only if `D_*<infinity`. If `H_*<=B`, then
`D(v)<=4B+1/27` on the convergent unit basin, and (4) implies

\[
 \tau(v)\le\left(\frac{40}{3}B+\frac{101}{162}\right)v
            \quad(v\in B,\ 3\nmid v).                    \tag{13}
\]

Thus a universal pointwise pre-arrival bound entails substantial
single-trajectory clock control. Neither (12) nor (13) supplies that
bound or proves that a start outside the known basin enters it.
An averaged pre-arrival bound can be weaker and is not excluded.

The same transfer applies to **all finite prefixes before one**, without
assuming that the sampled start eventually converges. Define
`D_L(v)=sum_(h<L)(1-W_h(v))` whenever `U^h(v)!=1` for `h<L`, and
take `D_hat` to be their supremum over positive units and such finite
clocks. Define `H_hat` similarly from (5), stopping at any finite
clock before or at the first arrival of either endpoint, without the
restriction `q in B`. Empty windows have cost zero.

The finite-prefix version of (4) is
`L/v <= (10/3) D_L(v)+1/2`. To see this, remove the initial `h`
halvings. If the prefix has passed the first odd input `o>=3`, its
weight deficit is at least `1/(3o+1)` for its remaining `L-h-1`
terms. If it has not, use the halving-clock bound. Thus the proof of
(6) works at a finite stopping clock. In the converse construction,
replace `tau(v)` by the chosen finite clock in (8)--(11), choose
`a` at least that clock, and double the prefix as needed to reach the
unit class one modulo nine. If the clock is below `h_0`, the entire
deficit is already below `1/27`. Consequently

\[
 \tfrac14(\widehat D-1/27)_+\le\widehat H
                    \le\tfrac{23}{3}\widehat D+1.         \tag{13a}
\]

A positive nonconvergent start eventually has an odd input greater
than one. The weight then loses a fixed positive amount and never
recovers it, so its finite-prefix deficits grow without bound. Every
positive orbit also reaches a unit modulo three, after the initial
halvings and at most one odd step; this finite fact is kernel proved.
It follows that

\[
 \widehat H<\infty
 \quad\Longleftrightarrow\quad
 [\text{every positive integer reaches one and }D_*<\infty].
                                                               \tag{13b}
\]

This supplies a sufficient condition for full Collatz, including cycle
exclusion, but **does not prove the condition**. It is not asserted to
be equivalent to Collatz alone: the additional uniform deficit bound
has not been deduced from universal convergence. The restricted
known-basin supremum in (12) and the unrestricted finite-prefix
supremum in (13b) must not be confused.

## 5. No charge to losses during the pre-arrival interval

There is a short explicit suffix: take `v=10`, so `ell=3`,
`k_j=T_j`, `b_v=9/10` and `tau(10)=5`. Its path is
`10,5,8,4,2,1`; its lifetime deficit is exactly `3/16`. Thus

\[
                 H(n_j)\longrightarrow\frac{243}{1600}>0.\tag{14}
\]

A direct all-parameter bound is available already for `j>=2`.
Writing `R=3^(3j-1)`, `X=10R+1`, the kernel retention comparison
gives `A_(k_j+h)>=7/8` for `h<=4`. At `h=2,3,4` the child's
profile is `27/32`, and the count order has reversed. Therefore

\[
                         H(n_j)\ge\frac{21}{256}.          \tag{15}
\]

Let `Z_t=M f_t(n_j) U^t(n_j)/(U^t(n_j)+1)` be the shifted
parent profile. Its losses through the child's first arrival satisfy

\[
 L_j=3(A_{k_j}-A_{k_j+5})+2(Z_{k_j}-Z_{k_j+5})
       \le\frac{93}{X}\longrightarrow0.                  \tag{16}
\]

This is the earlier elementary fixed-window retention estimate applied
at the large endpoint `X`. Equations (15)--(16) rule out
`H(n)<=C L(n)` for every universal multiplier `C`, even though the
whole interval being charged ends at the **first** arrival of either
endpoint. No post-arrival cycle loss is involved in this obstruction.

## 6. A complete future-loss charge with multiplier one also fails

Take `v=597484`, `j=64`. Then `k=403`, and the source is

\[
 n=\frac{8(597484\cdot64^{64}-1)}9.
\]

Exact replay certifies first arrivals `tau(n)=1863` and
`tau(3n+2)=538`. The source has 404 bits. With normalization `M=2^403`,
the rational decisions certify

\[
 H(n)>3A_{403}+2Z_{403}+\frac1{200}.                       \tag{17}
\]

For orientation only, the values are approximately `H=4.940951`
and `3A+2Z=4.935898`. Since this parent converges, the latter is
exactly its complete future weighted-loss budget. Thus multiplier one
fails even when all future parent losses are available. This does not
rule out a larger universal multiplier for this pre-arrival cost.

## Verification and remaining gap

Run `python3 verify_prearrival_deficit_transfer.py`. The
[record](../results/prearrival-deficit-transfer/verification.json)
distinguishes the thirteen kernel roots, finite exact deficit recurrences,
affine clone windows and first arrivals, and the written infinite
transfer. Large rational window sums are certified exactly and stored
as rational enclosures; floating displays decide no comparisons.

Uniform `D_*`, uniform `H_*`, useful averaged pre-arrival estimates,
negative arrival advances and drift after a convergent child has
arrived all remain uncontrolled. Criterion Q, escape exclusion,
additional-cycle exclusion and the full conjecture remain open.
