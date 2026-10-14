# The missing clock moment of the weight-loss measure

**Status: exact finite identities, with a written density deduction.** The
density statements use the written first-passage and packing inputs of
[Weighted dissipation](WEIGHTED-DISSIPATION.md). The optional subquadratic
clock consequence below additionally assumes the external reciprocal
weighted-density floor. Neither a uniform mean deficit nor full Collatz
convergence is proved.

The [limiting-law result](DEFICIT-LIMIT-LAW.md) gives tightness, but does
not control means. The exact identity here places the missing mean in
an already constructed probability measure. It identifies one unbounded
observable for which a uniform tail estimate would suffice.

## 1. Deficit is loss multiplied by remaining time

Use shortcut time. For a convergent start `n`, let `T=tau(n)` be its
first arrival at one, and put `x_j=U^j(n)`. As before,

\[
 W_j=\frac{n3^{a_j(n)}}{2^jx_j},\qquad
 \ell_j=W_j-W_{j+1}
       =\mathbf1_{x_j\text{ odd}}\frac{W_j}{3x_j+1}.
\]

Finite summation in the opposite order gives

\[
 \boxed{D(n)=\sum_{h<T}(1-W_h)
       =\sum_{j<T}(T-1-j)\ell_j.}                         \tag{1}
\]

The factor is `T-1-j`, not `T-j`: a loss at step `j` first affects
the weight at clock `j+1`, and the weight at clock `T` is omitted from
the deficit. The prefix is simple, so for each odd visited target
`v>1`, `T-1-j=tau(Uv)` and `W_j=w_v(n)`, its first-hit weight. Hence

\[
 D(n)=\sum_{\substack{v>1\text{ odd}\\v\text{ visited before }1}}
            \frac{\tau(Uv)}{3v+1}w_v(n).                  \tag{2}
\]

All terms are nonnegative. In particular `D(n)>=D(v)` if `n` reaches
a convergent `v`; this also follows from the earlier splice identity.

## 2. A single fixed observable on the existing probability space

Let `B` be the basin of one and define `D_B(n)=D(n)` for `n in B`,
and zero otherwise. This convention is only for the restricted source
average. It does not assign a finite arrival time to a nonconvergent
source.

Recall the weight-loss probability measure `mu_n` on positive odd
targets and an extra symbol `infinity` from
[Weighted dissipation](WEIGHTED-DISSIPATION.md). It places each lost
weight at the odd state where the loss occurred, and places the
unlost infinite weight at `infinity`. Ordinary and shortcut clocks give
the same measure, because deleting the extra even steps changes no loss.

Define the nonnegative finite-valued function

\[
 G(v)=\begin{cases}
       \tau(Uv),&v>1\text{ odd and }v\in B,\\
       0,&\text{otherwise},
      \end{cases}
 \qquad G(\infty)=0.                                    \tag{3}
\]

This function need not be bounded or effectively computable on all
targets. Its definition uses a convergent target's actual finite clock.
Every `v>1` in `B` is nonperiodic. If a source outside `B` visited such
a target, it would itself belong to `B`. Equation (2) therefore proves,
for **every** positive source,

\[
                         \boxed{D_B(n)=\int G\,d\mu_n.}  \tag{4}
\]

The loss at one has coefficient zero in (3). Its infinitely many cycle
visits must not be charged a remaining lifetime. The separate atom at
infinity also has coefficient zero; (4) concerns the known basin only.

Put `nu_X=(1/X)sum_(n<=X) mu_n` for integer `X>=1`. The earlier written
result gives a probability measure `mu` and

\[
 d_{\rm TV}(\nu_X,\mu)\le C(\log X)^{-c}                 \tag{5}
\]

for large `X`. Let `d_v=lim_X (1/X)sum_(n<=X) w_v(n)` denote the
weighted first-hit density, distinguished from the lifetime deficit
`D`. At our nonperiodic targets, `mu({v})=d_v/(3v+1)`. Thus

\[
 M:=\int G\,d\mu
   =\sum_{\substack{v>1\text{ odd}\\v\in B}}
           \frac{\tau(Uv)d_v}{3v+1}\ \in[0,\infty].       \tag{6}
\]

For each fixed `L>=0`, bounded integration in (5) proves

\[
 \left|\frac1X\sum_{n\le X}\int\min(G,L)\,d\mu_n
                -\int\min(G,L)\,d\mu\right|
          \le CL(\log X)^{-c}.                           \tag{7}
\]

Monotone convergence after this fixed-cutoff limit gives the necessary
inequality

\[
             M\le\liminf_{X\to\infty}
                         \frac1X\sum_{n\le X}D_B(n).     \tag{8}
\]

Neither finiteness of `M` nor equality in (8) follows from (5). The
new limiting law for `D_m` does not justify an unbounded-moment exchange
either. No identification of `M` with the first moment of that separate
limiting law is required or claimed here.

## 3. An exact sufficient tail condition, and its limits

The remaining-clock tails are

\[
 R_L(X)=\int(G-L)_+\,d\nu_X
       =\frac1X\sum_{n\le X}\sum_{\substack{v>1\text{ odd}\\v\in B}}
                   (\tau(Uv)-L)_+\,\mu_n(\{v\}).         \tag{9}
\]

For each fixed `X`, the moment and these tails are finite: there are
only finitely many convergent sources at most `X`, each with a finite
pre-arrival path. The following equivalence uses (5):

\[
 \boxed{\lim_{L\to\infty}\sup_{X\ge1}R_L(X)=0
 \quad\Longleftrightarrow\quad
 \frac1X\sum_{n\le X}D_B(n)\longrightarrow M<\infty.}    \tag{10}
\]

For the forward implication, split `G=min(G,L)+(G-L)_+`, use (7),
then send `L` to infinity. A fixed finite cutoff and the uniformly
small tail first show that the moments are uniformly bounded, so `M`
is finite by (8). For the converse, convergence of the full moments
and (7) gives `lim_X R_L(X)=M-int min(G,L) dmu`. This tends to zero
with `L`. Control all large `X` first, then the finitely many earlier
source populations by their finite moments.

Condition (10) is stronger than a uniform first-moment bound alone.
A bounded mean may still have some moment carried by increasingly rare
large values. Its advantage is a precise nonnegative tail whose finite
approximations can be checked, without mistaking the bounded total
lost weight for a bound on time-weighted loss.

If `A=sup_X (1/X)sum_(n<=X)D_B(n)<infinity`, the preceding pre-arrival
transfer gives the sufficient bound

\[
 \frac1{2^k}\sum_{\substack{2^k\le n<2^{k+1}\\3n+2\in B}}H(n)
                              \le46A+1.                 \tag{11}
\]

Indeed the distinct targets `q=3n+2` are below `6*2^k`, so their
mean deficit is at most `6A`, and `H<=(23/3)D(q)+1`. This concerns
the cost before either arrival. It does not bound negative arrival
advances, post-arrival drift or pairs with an unknown child.

## 4. How strong a bounded mean would be

Let `r_v` be the unweighted predecessor density of a convergent target.
Since `D_B(n)>=D(v)` on its predecessor basin, a bounded mean `A`
necessarily satisfies

\[
                    r_vD(v)\le A.                       \tag{12}
\]

For `r_v>0`, the earlier pointwise clock inequality consequently gives

\[
              \tau(v)\le\frac{10Av}{3r_v}+\frac v2.     \tag{13}
\]

This is root-dependent; positivity alone gives no uniform power bound.
There is a stronger conditional consequence if one additionally uses
the **external reciprocal weighted-density floor** reviewed in
[Local obstruction review, Section 2](LOCAL-OBSTRUCTION-REPO-REVIEW.md):

\[
 d_v\ge c_*/v\quad(v>1\text{ odd},\ 3\nmid v,\ v\in B)
                       \quad\text{for some }c_*>0.       \tag{14}
\]

Here (14) follows from that external unit envelope floor and
`g(v)=delta v d_v`, because these targets are nonperiodic. It is not
reproved or newly kernel replayed in this note. With (14), (6)--(8)
would imply

\[
 \sum_{\substack{v>1\text{ odd}\\3\nmid v,\ v\in B}}
             \frac{\tau(Uv)}{v^2}\le\frac{4A}{c_*},
 \qquad
 \sum_{\substack{v>1\text{ odd}\\3\nmid v,\ v\in B}}
             \frac{\tau(v)}{v^2}<\infty.                 \tag{15}
\]

Use `v(3v+1)<=4v^2` for the first inequality, then
`tau(v)=1+tau(Uv)` and convergence of `sum v^(-2)` for the second.
In particular `tau(v)=o(v^2)` uniformly along these known convergent
targets. This extends to all convergent starts: initial halvings
contribute only their number, and an odd multiple of three takes one
shortcut step to a unit of size at most `2v`.

Thus even the proposed mean bound would have a substantial global
clock consequence under the external floor. None of (13) or (15)
establishes the assumed bound `A`, and none asserts convergence of an
unknown start.

## Verification and literature check

Run `python3 verify_deficit_clock_moment.py`; the
[record](../results/deficit-clock-moment/verification.json) distinguishes
the finite kernel algebra, exact trajectories and moment decompositions,
the written measure arguments, and the optional external floor.

The literature search did not provide the missing upper moment.
[Inselmann's paper](https://arxiv.org/html/2402.03276v3) states a lower
bound for the average total stopping time, and obtains its matching
limit under the stronger assumption `tau(n)=O(log n)`. That result is
context only here; it is not an input to (1)--(15). Numerical averages
and finite target or clock tails do not verify (10).
