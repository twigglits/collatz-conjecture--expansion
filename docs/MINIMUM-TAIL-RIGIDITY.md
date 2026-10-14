# The linear threshold for minimum-tail control

**Status: new finite kernel implications for the actual Collatz minimum,
and written moment deductions for an explicitly different escaping map.
No required Collatz tail bound is proved. The conjecture remains open.**

The preceding [minimum logarithmic-moment bound](MINIMUM-LOG-MOMENTS.md)
controls every fixed power of the logarithm of the global minimum.
Can these estimates, perhaps strengthened to fractional powers, force
the [unknown nonconvergent mass](CRITICAL-CLOCK-WINDOW.md) to vanish?
There is a sharp obstacle: even some weights very close to linear are
uniformly integrable in the existing escaping comparison map.

At the linear weight itself, a diagonal argument gives a much stronger
conclusion. This identifies a sufficient estimate with direct pointwise
force, and distinguishes it from the weaker moments already obtained.
No mathematical novelty is claimed for the elementary diagonal or
dominated-summation arguments.

## 1. A minimum is a fixed point of the minimum map

For ordinary Collatz let

\[
 m(n)=\min_{t\ge0}C^t(n),\qquad
 S_H(N)=\sum_{1\le n\le N}m(n)\mathbf1_{\{m(n)>H\}},\qquad
 U(H)=\sup_{N\ge1}\frac{S_H(N)}N.                         \tag{1}
\]

These minima exist and are attained by well-ordering, without assuming
arrival at one. If `a=m(n)`, its forward orbit is a suffix of the
source orbit, so every iterate is at least `a`. It starts at `a`.
Consequently

\[
                         m(m(n))=m(n).                    \tag{2}
\]

Suppose some minimum `a=m(n)` exceeds `H`. In the source population
`1..a`, the single source `a` contributes exactly `a` to `S_H(a)`.
Therefore

\[
 \boxed{U(H)=0\quad\hbox{or}\quad U(H)\ge1,}
 \qquad
 \boxed{U(H)<1\ \Longleftrightarrow\ m(n)\le H
                                     \text{ for every }n\ge1.} \tag{3}
\]

The argument uses the **supremum over all source cutoffs**. Replacing
it by a limiting minimum distribution would discard the source `a`
chosen on the diagonal. In fact the slightly weaker-looking hypothesis
`S_H(N)<N` separately for every positive integer `N` already forces
the right side of (3), even without a common strict margin below one.

The Lean theorem `tail_budget_rigidity` proves this equivalence for
any positive idempotent integer-valued map. The minimum construction,
its attainment and idempotence are separately proved for actual Collatz.
No mixing theorem or predecessor-density result is needed.

## 2. What first-moment uniform integrability would prove

Uniform integrability of the actual minimum means

\[
                 \lim_{H\to\infty}U(H)=0.                \tag{4}
\]

By (3), this is equivalent to a finite global bound on all orbit minima.
Thus (4) is considerably stronger than a finite moment of a limiting
minimum law. It is also stronger than a uniformly bounded first moment;
the latter distinction is illustrated below.

For any deterministic map of the positive integers, a global minimum
bound is equivalent to all orbits eventually entering a **finite
collection of cycles**. To prove the forward implication, apply the
minimum bound at every successive state of an orbit. The orbit must
visit `1..H` at arbitrarily late times. Some member of that finite set
repeats, forcing eventual periodicity. Every cycle contains a value at
most `H`, and disjoint cycles have distinct such values, so there are
at most `H` cycles. Conversely, finitely many eventual cycles give a
bound by their largest cycle minimum.

This does not by itself select the cycle through one. For actual
Collatz, if all starts through the same floor `H` have been proved to
reach one, (3) immediately yields full Collatz. The kernel theorem
`bounded_minimum_verified_floor` checks that final implication.

There is an integer finite-prefix version. Put

\[
                 m_T(n)=\min_{0\le t\le T}C^t(n).
\]

For any proposed clock function `T(N)`,

\[
 \boxed{\forall N\ge1,\quad
    \sum_{n\le N}m_{T(N)}(n)\mathbf1_{\{m_{T(N)}(n)>H\}}<N}
                                                               \tag{5}
\]

is sufficient for the same global minimum bound, since `m<=m_T` and
`x 1_(x>H)` is nondecreasing. This implication and its combination
with a verified floor are kernel checked. The estimate (5) is
**unproved**. It concerns every source cutoff; finitely many successful
checks do not establish it. Nor is (5), for an arbitrarily prescribed
clock, asserted equivalent to Collatz.

For a dyadic-only sufficient test, it is enough that the corresponding
sum at each `N=2^k` is at most `2^(k-1)`, or equivalently that twice
the sum is at most `2^k`. Given a minimum `a>H`, choose the least
dyadic cutoff `N>=a`. Then `N<2a`, while its sum is at least the
single diagonal contribution `a`, a contradiction. The clock at each
dyadic cutoff may be chosen separately. This is a written consequence
of the same summand bound, not an established estimate for those sums.

## 3. Why bounded first moments alone are insufficient

For a small independent example, define a map `J` by
`J(2^k)=2^(k+1)` for `k>=1`, and `J(n)=1` otherwise, including `J(1)=1`.
This is not Collatz and does not preserve its even branch. Its minimum
is `n` at powers of two greater than one and is one everywhere else.
Since the sum of the powers of two through `N` is less than `2N`,

\[
                \sup_N\frac1N\sum_{n\le N}m_J(n)\le3.
\]

Nevertheless it has escaping orbits and violates (4): at every large
power-of-two source `a`, the diagonal contribution to `U_J(H)` is one
when `a>H`. Its limiting minimum law is the point mass at one, whose
first moment is finite. This example illustrates only the distinction
between bounded moments, limiting-law moments, and uniform integrability;
it does not satisfy the external positive predecessor-density premise.

## 4. An escaping comparison map has nearly linear integrable weights

Now use the more structured map `F` from
[Density Countermodel](DENSITY-COUNTERMODEL.md), which keeps even halving
and the cycle `1 -> 4 -> 2 -> 1`, but changes the odd branch. Exactly
half its starts escape. Its positive predecessor densities, including
the stronger floor `r_a>=1/(2a)`, have elementary written proofs in
that note. These are facts about `F`, not Collatz inputs.

Write an odd part as either `4j-3` or `4j-1`. The former reaches one.
The latter deletes leading binary ones from `j` until reaching its
lowest set bit, then follows the increasing spine. Hence its exact
ordinary minimum is

\[
 m_F(n)=
 \begin{cases}
 1,&\text{odd part of }n\equiv1\pmod4,\\
 v_k:=2^{k+2}-1,&\text{odd part }n=4j-1,\quad k=\nu_2(j).
 \end{cases}                                               \tag{6}
\]

Every intervening even value is at least the next odd value, so no
smaller value is hidden by accelerating the description. The kernel
checks `F^t(v_k)>=v_k` at **every** time, using the previously proved
explicit spine formulas. Thus its global minimum at `v_k` is indeed
`v_k`; a finite cutoff is not being used to declare escape.

The limiting minimum masses, already identified in the earlier note,
are

\[
            \pi_1=1/2,\qquad \pi_{v_k}=2^{-k-2}
                                      =\frac1{v_k+1}.       \tag{7}
\]

We need a uniform finite-population bound too. The sources with label
`v=v_k` are exactly

\[
                    2^a(v+2(v+1)j),\qquad a,j\ge0.         \tag{8}
\]

For each fixed `a`, the `r`th positive member is at least `2^a v r`.
The count through `N` is therefore at most `floor(N/(2^a v))`.
Summing over `a`, the elementary dyadic floor sum is at most `2N/v`.
As `v>=3`, this gives

\[
 \boxed{\frac1N\#\{n\le N:m_F(n)=v_k\}
                \le\frac2{v_k}\le\frac3{v_k+1}=3\pi_{v_k}.} \tag{9}
\]

The finite last-member, dyadic-budget, and cross-multiplied comparison
inequalities are kernel checked. The all-source classification and
counting assembly in (6)–(9) remain written proofs, independently
replayed on the stated finite populations.

## 5. An exact criterion for any nonnegative minimum weight

Let `w` be a nonnegative finite-valued function on positive integers.
Equations (7)–(9) imply

\[
 \boxed{\lim_{H\to\infty}\sup_N\frac1N
    \sum_{n\le N}w(m_F(n))\mathbf1_{\{m_F(n)>H\}}=0
 \quad\Longleftrightarrow\quad
             \sum_{k\ge0}\frac{w(v_k)}{v_k+1}<\infty.}     \tag{10}
\]

For sufficiency, dominate each finite-population atom by three times
its limiting mass and sum the convergent series tail. For necessity,
the left side gives a uniformly bounded full weighted mean: finitely
many labels below a fixed `H` have bounded weights, and the remaining
tail is bounded. Passing to the density limit for any **finite** set
of labels bounds each partial sum on the right. Monotone convergence
of those partial sums proves necessity.

If the series is finite, dominated summation also gives the source
mean limit

\[
        \frac1N\sum_{n\le N}w(m_F(n))
                \longrightarrow \frac{w(1)}2+
                       \sum_{k\ge0}\frac{w(v_k)}{v_k+1}.    \tag{11}
\]

If the series diverges, these means tend to infinity: every fixed
finite partial sum supplies an eventual lower bound, and those lower
bounds grow without limit. No unproved interchange of an infinite sum
and a density limit is needed.

There is also an exact dyadic formula. For `N=2^L`, `L>=1`, (8)
gives exactly `2^(L-k-2)` sources with minimum `v_k` when `0<=k<=L-2`,
and none for larger `k`. Put `d=L-k-2`. For initial valuation `a<d`
the count is `2^(d-a-1)`, and for `a=d` it is one; these sum to
`2^d`, including the case `d=0`. The remaining `2^(L-1)+1`
sources have minimum one. Thus for every such `L`,

\[
 \frac1{2^L}\sum_{n\le2^L}w(m_F(n))
    =\left(\frac12+2^{-L}\right)w(1)
                  +\sum_{k=0}^{L-2}\frac{w(v_k)}{v_k+1}. \tag{11a}
\]

For the linear weight this simplifies to the exact finite value
`L-1+2^(1-L)`, so its unbounded first means are visible directly.
The finite identity still describes only the altered comparison map.

In particular:

* `w(x)=x^p`, `p>=0`: (10) holds exactly for `p<1`.
* Every fixed positive power of `log x` satisfies (10).
* `w_q(x)=x/[log_2(x+1)]^q`: (10) holds exactly for `q>1`.

For the last assertion, `log_2(v_k+1)=k+2` and
`3/4<=v_k/(v_k+1)<1`, reducing the series to the usual `q`-series.
For `q>1`, with `K` the least index for which `v_K>H`, (9) gives the
explicit uniform bound

\[
 \sup_N\frac1N\sum_{n\le N}w_q(m_F(n))1_{m_F(n)>H}
           \le\frac{3}{q-1}(K+1)^{1-q}.                  \tag{12}
\]

At `q=2` this follows even from rational telescoping, since
`1/(k+2)^2 <= 1/[(k+1)(k+2)]`. For `0<=p<1`, similarly,

\[
 \sup_N\frac1N\sum_{n\le N}m_F(n)^p1_{m_F(n)>H}
       \le\frac{3(H+1)^{p-1}}{1-2^{p-1}}.                \tag{13}
\]

Thus nearly linear minimum weights can have uniformly vanishing tails
while a positive-density set escapes and every target has positive
predecessor density. Improving logarithmic moments to these weights
would not, by itself, settle the conjecture.

## 6. Consequence for the current route

The existing Collatz estimate `Pr(m>H)<=C_r/(log H)^r` for every
fixed `r` supplies none of (3)–(5). Its constants depend on `r`; one
cannot choose an exponent depending on `H` without controlling that
dependence. The comparison map even satisfies a uniform `O(1/H)` tail
bound, which is stronger than all those logarithmic estimates, while
retaining escape.

The linear weighted tail has a decisive diagonal effect that its
sublinear substitutes can lack. A proof of a uniform tail budget below
one at a verified Collatz floor would finish the problem. The current
recurrence and analytic error bounds do not provide that budget. This
is a limitation and a precise next estimate, not a proof of convergence.

A source check on 14 October 2026 reconfirmed that the advertised
[natural-density descent theorem](https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/)
uses thresholds tending to infinity, while the
[predecessor-density theorem](https://www.proofatlas.ai/proofs/artifact.collatz.predecessors_positive_lower_density.v001.html)
has target-dependent constants. Neither statement supplies the uniform
linear minimum-tail budget. No new external theorem is used here.

## 7. Verification scope

Run `python3 verify_minimum_tail_rigidity.py`; see its
[record](../results/minimum-tail-rigidity/verification.json).
The kernel implications, exact finite computations, written infinite
moment deductions, and the explicitly altered maps are recorded
separately. The actual global Collatz minimum is a noncomputable
definition, not an algorithm or a claim that every source reaches one.

Nineteen new kernel roots passed four fresh sequential builds, with
only standard Lean axioms. The independent replay exhausts all 256 maps
on four positive states, checks 8,192 actual Collatz prefixes through
ordinary clock 128, and classifies 32,768 comparison-map sources using
the proved infinite-spine continuation. It checks 393,248 finite atom
bounds and the exact dyadic gauge formulas. The 4,000 large dyadic atom
formula checks include cutoff `2^1024`; these are arithmetic evaluations
of (8), **not** a trajectory census through that cutoff. No asymptotic
claim is inferred from a finite sample.
