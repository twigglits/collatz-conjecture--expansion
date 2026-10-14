# The square-root window around the critical ordinary clock

**Status: written deductions from the local uniform-in-time progression
mixing estimate and the earlier written minimum-clock, tightness, and
lost-weight limits. Finite transport and stopping identities are checked
separately. The analytic Gaussian limit is not kernel formalized.
Collatz remains unresolved; its required zero amplitude is not proved.**

Use the ordinary censored cells and deficits

\[
 z_t(n)=\mathbf1_{\{\tau_1(n)>t\}}(1-W_t(n)),\quad
 A_T(n)=\sum_{t<T}z_t(n),\quad
 Z_t(N)=\frac1N\sum_{n\le N}z_t(n),\quad
 F_T(N)=\frac1N\sum_{n\le N}A_T(n).
\]

Thus `z_0=A_0=A_1=0`, `0<=z_t<=1`, and `0<=A_T<=T`.
Let

\[
 L=\log(4/3),\quad d=L/2,\quad \kappa=3/L,\quad
 \sigma^2=\frac{2(\log6)^2}{L^3},\quad
 T_N(u)=\left\lfloor\kappa\log N+u\sqrt{\log N}\right\rfloor.
                                                               \tag{1}
\]

For each fixed real `u`, this clock is nonnegative for large `N`.
Let `Phi` and `phi` denote the standard normal distribution function
and density. Write `b` for the nonconvergent lost-weight mass from
[Censored Deficit Clock](CENSORED-DEFICIT-CLOCK.md), rather than a landing
state. The new written conclusions are

\[
 \boxed{Z_{T_N(u)}(N)\longrightarrow b\,\Phi(u/\sigma),}
                                                               \tag{2}
\]

\[
 \boxed{\frac{F_{T_N(u)}(N)}{\sqrt{\log N}}
       \longrightarrow b\,[u\Phi(u/\sigma)+\sigma\phi(u/\sigma)].}
                                                               \tag{3}
\]

In particular the critical instantaneous limit, left undecided by the
earlier fixed-coefficient argument, is `b/2`. The critical cumulative
limit is

\[
 \frac{F_{\lfloor\kappa\log N\rfloor}(N)}{\sqrt{\log N}}
       \longrightarrow
       \frac{b\log6}{\sqrt\pi\,[\log(4/3)]^{3/2}}.             \tag{4}
\]

The boundary analysis is essential. A Gaussian statement about an
auxiliary random walk alone would not justify (2) or (3).

## 1. Two-sided recurrences retain the clock shifts

For `N>=3`, put `a=floor(N/2)`, `ell=floor((N-1)/2)`, and
`c=3ell+2`. The letter `c` here is a cutoff, not a clock coefficient.
The exact deficit transport from the preceding note gives, for `T>=2`,

\[
 F_T(N)=\frac aN F_{T-1}(a)+\frac\ell N F_{T-2}(c)
       +\frac\ell N\delta^A_{T-2}(\ell)
       +\frac{E^A_{T-2}(\ell)}N.                            \tag{5}
\]

This holds for both parities of `N`; the source one contributes zero.
Here `delta^A` is the progression discrepancy and
`0<=E^A_t(ell)<=(t+1)H_ell/6`.

The corresponding individual cell identities are

\[
 z_{t+1}(2n)=z_t(n),\qquad
 z_{t+2}(2n+1)=z_t(3n+2)+e^z_t(n),\qquad
 0\le e^z_t(n)\le\frac1{2(3n+2)}.                           \tag{6}
\]

To see the correction, let `q=3n+2`,
`r=3(2n+1)/(3(2n+1)+1)`, and `s_t(q)=1_(tau_1(q)>t)`.
The odd cell is `r z_t(q)+(1-r)s_t(q)`, so its excess is
`(1-r)(s_t(q)-z_t(q))`. This proves (6) without assuming future arrival.
Parity splitting yields the cell version of (5), with correction
at most `H_ell/6`.

Both exact coefficients in (5) are at most `1/2`; their total deficit
from the fair coefficients is
`1-a/N-ell/N=1/N`. Consequently replacing them by `1/2` incurs
absolute error at most `T/N` for deficits and `1/N` for cells. These
losses must be retained for a two-sided comparison.

Use the preceding WRITTEN progression bounds, uniformly in time,
with exponent `R`. Since `ell>=sqrt N` for `N>=9`, there are constants
`K_R,N_R`, independent of time, for which

\[
 \left|Z_T(N)-\frac{Z_{(T-1)_+}(a)+Z_{(T-2)_+}(c)}2\right|
        \le g_R(N),\qquad
 \left|F_T(N)-\frac{F_{(T-1)_+}(a)+F_{(T-2)_+}(c)}2\right|
        \le T g_R(N),                                      \tag{7}
\]

for `N>=N_R`, `T>=0`, where

\[
                 g_R(N)=K_R(\log N)^{-R}
                              +\frac{\log N+7}{6N}.         \tag{8}
\]

The case `T=1` for cells needs a separate check: its even terms vanish
and its odd terms, other than the censored source one, are
`1/[2(3n+2)]`. Their mean is at most `(1+log N)/(6N)`.
For deficits, `F_0=F_1=0` already. Thus the clipping in (7) is valid.

## 2. The auxiliary cutoff chain and its consumed clock

Use the fair cutoff chain from [Minimum Log Moments](MINIMUM-LOG-MOMENTS.md).
At cutoff `n>H>=3`, choose `a(n)` or `c(n)` with probability `1/2`.
Let `tau` be its first entrance into `1..H`, and keep the state fixed
afterward. The lower branch consumes one unit of ordinary clock and
the upper branch consumes two. Write `J_tau` for the total consumed
clock. This is an averaging device for (7), not a random model of
an individual Collatz orbit.

The exact product inequality and overshoot bounds are

\[
 4a(n)c(n)<3n^2,\qquad
 H/2\le N_\tau\le H,\qquad
 \mathbb E\tau\le\frac{\log(2N/H)}d,\qquad
 \mathbb E\sum_{j<\tau}\frac1{N_j}\le\frac6H.               \tag{9}
\]

The last two statements follow by finite stopping and passage to the
limit, as in the preceding note. All subsequent expectations concern
this auxiliary chain unless explicitly stated otherwise.

Let the independent branch signs be `xi_j=-1` for lower and `+1`
for upper, and put `S_k=sum_(j<=k) xi_j`. The exact logarithmic increment is

\[
 \log N_{j+1}-\log N_j=-d+v\xi_{j+1}+\rho_j,
                 \qquad v=\tfrac12\log3,                  \tag{10}
\]

before stopping. The rounding errors are

\[
 \rho_- =\begin{cases}0,&n\text{ even},\\
                \log(1-1/n),&n\text{ odd},\end{cases}
 \quad
 \rho_+ =\begin{cases}\log(1-2/(3n)),&n\text{ even},\\
                \log(1+1/(3n)),&n\text{ odd}.
                \end{cases}                               \tag{11}
\]

For `n>=3`, each absolute value is at most `2/n`. Therefore
`R_tau=sum_(j<tau) rho_j` satisfies

\[
                         \mathbb E|R_\tau|\le12/H.          \tag{12}
\]

Each branch clock is `(3+xi)/2`. Put `mu=1/kappa=L/3` and
`w=log6/3`. The identities `-d+3mu/2=0`, `v+mu/2=w` turn (10) into

\[
 \log N_\tau-\log N+\mu J_\tau=wS_\tau+R_\tau,
 \quad
 J_\tau=\kappa(\log N-\log N_\tau)
                              +\kappa wS_\tau+\kappa R_\tau.\tag{13}
\]

Finite stopped-sign identities give `E S_(tau wedge k)=0` and
`E S_(tau wedge k)^2=E(tau wedge k)`. Since `E tau<infinity`, the
stopped sums converge in `L2`, so `E S_tau^2=E tau`. In particular,

\[
 \mathbb E|J_\tau-\kappa\log(N/H)|
 \le\kappa\left[\log2+w\sqrt{\frac{\log(2N/H)}d}+\frac{12}H\right].
                                                               \tag{14}
\]

## 3. A Gaussian clock limit without an exit-law assumption

For the rest of the argument take

\[
                  H=H_N=\left\lfloor
                         \exp((\log N)^{1/4})\right\rfloor.\tag{15}
\]

For large `N` this exceeds every fixed analytic threshold, tends to
infinity, and has `log H=o(sqrt(log N))`. Equation (10), (9), and (12)
give

\[
 \mathbb E\left|\tau-\frac{\log N}d\right|
    \le\frac{\log H+v\sqrt{\mathbb E\tau}+12/H}{d}
                         =O(\sqrt{\log N}).                \tag{16}
\]

Let `m_N=floor(log N/d)`. Orthogonality of independent mean-zero
increments, with predictable indicators for stopping, gives

\[
       \mathbb E(S_\tau-S_{m_N})^2
                              =\mathbb E|\tau-m_N|.        \tag{17}
\]

For completeness, the coefficient of `xi_(j+1)` in the difference
is `1_(j<tau)-1_(j<m_N)`, known before that sign is sampled. Distinct
terms are orthogonal, and the sum of their squared coefficients is
`|tau-m_N|`. Finite truncation followed by `L2` convergence proves
(17). Thus `(S_tau-S_m_N)/sqrt(log N)` tends to zero in `L2`.

The ordinary independent-sign central limit theorem now gives
`S_tau/sqrt(log N) -> Normal(0,1/d)`. One may obtain the fixed-time
theorem directly from
`[cos(t/sqrt(log N))]^m_N -> exp(-t^2/(2d))`.
Using (13), the bounded exit interval and (12) yields

\[
       \frac{J_\tau-\kappa\log N}{\sqrt{\log N}}
                          \Longrightarrow \sigma G,
                    \qquad G\sim\operatorname{Normal}(0,1).
                                                               \tag{18}
\]

Here `sigma^2=kappa^2 w^2/d`, which is exactly (1).
The sign term divided by `sqrt(log N)` has a uniformly bounded second
moment; the other errors tend to zero in `L1`. Hence (18) also gives
convergence of expected positive parts:

\[
 \frac{\mathbb E(T_N(u)-J_\tau)_+}{\sqrt{\log N}}
       \longrightarrow \mathbb E(u-\sigma G)_+
       =u\Phi(u/\sigma)+\sigma\phi(u/\sigma).              \tag{19}
\]

No stationary distribution for `N_tau`, nor independence of the exit
state and clock, is assumed or needed.

## 4. Summing the recurrence errors

Apply (7) until the cutoff reaches `1..H`. Repeated clock subtraction
is the same as subtracting the total consumed clock and clipping at zero.
At finite depth this is an ordinary binary-tree identity with residuals.
The bounded terminal terms and almost-sure absorption justify its limit.

For `R=r+1>1`, the preceding logarithmic potential bounds the first
term of (8). For the other term use the convex decreasing potential
`psi(s)=(s+8)exp(-s)` on `s>0`. Its tangent slope in magnitude is
`(s+7)exp(-s)`. The negative log drift gives

\[
 P\!\left(\frac{\log n+8}{n}\right)(n)
             -\frac{\log n+8}{n}
                     \ge d\,\frac{\log n+7}{n}.             \tag{20}
\]

Clip the potential below `H/2`, where it is never needed at an active
state or child. Finite telescoping gives

\[
 \mathbb E\sum_{j<\tau}g_{r+1}(N_j)\le\eta_{H,r},\qquad
 \eta_{H,r}:=
 \frac{K_{r+1}}{rd}[\log(H/2)]^{-r}
                  +\frac{\log(H/2)+8}{3dH}.               \tag{21}
\]

Consequently the two-sided boundary representations are

\[
 \left|Z_T(N)-\mathbb E Z_{(T-J_\tau)_+}(N_\tau)\right|
                          \le\eta_{H,r},\qquad
 \left|F_T(N)-\mathbb E F_{(T-J_\tau)_+}(N_\tau)\right|
                          \le T\eta_{H,r}.                 \tag{22}
\]

The arguments on the right are **population means at the terminal
cutoff**, not cells evaluated at the single integer `N_tau`.
For (15), choosing `r=3` gives `eta=O((log N)^(-3/4))`.
At the clocks (1), the error for cells tends to zero and the error for
deficits is `o(sqrt(log N))`. This step needs only the progression
estimate at `R=4`; it does not send an error exponent to infinity.

Already (14), (21), (22), and the bound `F_s(M)<=s` imply
`F_floor(kappa log N)(N)=O(sqrt(log N))`. This upper bound uses only
the same-scale progression estimate and elementary cutoff arguments.
Identifying its coefficient needs the boundary limit below.

## 5. The boundary population settles at super-logarithmic clocks

Define the bounded pointwise limit

\[
 q(n)=\mathbf1_{\{n\notin B\}}(1-W_\infty(n)),
                \qquad B=\{n:\tau_1(n)<\infty\}.
\]

The earlier written lost-weight law gives `mean_(n<=M)q(n)->b`.
Let `m(n)` be the attained global minimum and `tau_m(n)` its first
attainment time. The earlier written results give tightness of `m`
and `tau_m(n)/log M -> kappa` in probability under uniform sources
`1..M`. They imply the following uniform sequential statement:

\[
 M\to\infty,\quad s/\log M\to\infty
 \quad\Longrightarrow\quad Z_s(M)\to b,
                                  \quad F_s(M)/s\to b.     \tag{23}
\]

Here is the required justification, without a lifetime-deficit moment
assumption. Fix a minimum cutoff `K`. Except on
`{tau_m>s/2} union {m>K}`, a source has reached one of finitely many
minimum states at least `s/2` steps before the observation. If it is
in `B`, its minimum is one, so its cell is already zero. Otherwise,
the difference between its cell and `q(n)` is at most

\[
       \max_{1\le a\le K}
          [W_{\lfloor s/2\rfloor}(a)-W_\infty(a)].          \tag{24}
\]

Use the ordinary, uncensored weights in (24). Each decreases to its
limit, so this maximum tends to zero for fixed `K`. The first exceptional
probability tends to zero when `s/log M` tends to infinity; the second
is made uniformly small by choosing `K` large. Fix `K` before passing
to the source/clock limit, then let `K` grow. This proves the cell
statement in (23). Averaging cells over `epsilon s<=t<s` and bounding
the omitted initial fraction by `epsilon` proves the deficit statement.

Because (23) holds for every such sequence, it is uniform for
`H_N/2<=M<=H_N` and `epsilon sqrt(log N)<=s<=T_N(u)`, for any fixed
`epsilon>0`. This is why an arbitrary, possibly correlated terminal
cutoff may be used in (22).

For cells, (18) shows that the probability of remaining time between
zero and `epsilon sqrt(log N)` tends to a Gaussian interval probability,
which vanishes as `epsilon` tends to zero. On the other positive
remaining times, (23) replaces the boundary mean by `b`. At remaining
time zero the cell is exactly zero. This proves (2).

For deficits, (23) replaces `F_s(M)` by `b s` on the same long
remaining times. The error is `o(1)` times their mean remaining time;
(19) keeps that mean bounded after division by `sqrt(log N)`. The
short remaining times cost at most `epsilon` after that normalization.
Equations (19) and (22) prove (3). No unbounded source-deficit moment
or exit-state/clock independence has been used.

## 6. The resulting critical-clock tests still have an unknown answer

The earlier written tightness argument identifies `b=0` with natural
density one of the basin of one. With the separately EXTERNAL positive
predecessor-density theorem, this is equivalent to full Collatz.
Under exactly those dependencies, (2)–(4) give two further equivalent
finite-prefix zero-limit criteria:

\[
 \frac1N\sum_{n\le N}z_{\lfloor\kappa\log N\rfloor}(n)\to0,
 \qquad
 \sum_{n\le N}A_{\lfloor\kappa\log N\rfloor}(n)
                                  =o(N\sqrt{\log N}).     \tag{25}
\]

Along `N=2^k`, the latter becomes
`sum_(n<=2^k) A_floor((kappa log 2)k)(n)=o(2^k sqrt k)`.
The limiting coefficient after division by `2^k sqrt k` is
`b sigma sqrt(log 2)/sqrt(2pi)`.

Neither limit in (25) has been proved zero. A zero limit after the
coarser normalization `N log N` at the same critical clock remains
automatic for any `b`, and cannot replace (25). The Gaussian profile
identifies the missing mass more sharply; it does not determine it.

## 7. Finite verification and its limits

Run `python3 verify_critical_clock_window.py` for the finite identities
and exact replay in [the verification record](../results/critical-clock-window/verification.json).
Fifteen new kernel roots prove the actual cell bounds, their relation
to deficit increments, even/odd transport, the even population split,
the fair-coefficient error bound, finite clocked unrolling, the cost
majorant, clock algebra, and stopped-sign mean and second moments.
The three fresh sequential builds use only the standard Lean axioms,
with no admitted proofs or native finite evaluation.

Independent exact-rational replay uses all 1,024 sources through clock
26, without a future-arrival decision. It checks 6,400 instances of
each cell transport, 644 exact population splits, 700 two-sided
residual bounds, and 360 clocked unroll/cost comparisons. Separate
stopped-sign trees check the first two moments, and 16 bounded
stopping-versus-fixed-time isometries are exhaustively replayed over
16,384 sign words. At clock 26, 771 source prefixes are still alive;
this is not a nonconvergence classification.

A separate exact dynamic program illustrates the **ideal multiplicative**
auxiliary chain at source/floor ratios `2^8` through `2^128`, using
rational logarithm brackets to select critical clocks. It groups all
contributing sign words and reports the unabsorbed probability too.
It is neither a census of Collatz trajectories nor a numerical proof
of the Gaussian limit, and is kept separate from the rounded cutoff
chain used in the deduction.

The kernel and finite computational scope is distinct from the real
logarithms, stopped-walk central limit theorem, boundary settling,
and analytic progression premise used above. Those remain written
mathematics, without effective asymptotic constants.
