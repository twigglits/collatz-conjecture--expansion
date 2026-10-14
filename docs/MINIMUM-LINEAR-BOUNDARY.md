# A persistent linear boundary in the finite-clock recurrence

**Status: exact kernel bounds and a kernel-certified finite Collatz example,
plus a written leading-order cancellation law. The finer bound needed for
convergence remains unproved. Collatz is unresolved. No analytic mixing or
external density theorem is a premise of the new arguments.**

The [cap audit](MINIMUM-CAP-TRANSPORT.md) left open whether the whole signed
recurrence error could be summed usefully. Before estimating that sum, its
terminal contribution must be retained. For finite-clock linear minimum
weights, this contribution stays large at every clock, even though the
probability of reaching it tends to zero.

At floor `H=4` and initial cutoff `N=256`, the terminal mean is at least
`103/2` for every clock. All 256 actual sources have also been kernel
checked to reach that floor within clock 128. Consequently their signed
recurrence error, summed with the cutoff-tree probabilities, is at most
`-103/2` at every clock `T>=128`. Cancellation is essential even for
this verified convergent finite population.

The leading cancellation can also be determined. Uniformly in clock,
the boundary is `[3/7+(-3/4)^T/14]*N` up to `H+1+6ell(N)`.
An elementary finite-parity estimate then gives `S_(T(N))(N)/N -> -3/7`
for every clock function tending to infinity, at a fixed floor.
This leading law is written, not a new kernel asymptotic theorem. It
does not bound the unscaled prefix mean below one.

## 1. Stop at the floor or before exhausting the remaining clock

Write

\[
 F_T(N)=\frac1N\sum_{n=1}^N m_T(n)\mathbf1_{\{m_T(n)>H\}},\qquad
 m_T(n)=\min_{0\le j\le T}C^j(n),
\]
\[
 a(n)=\lfloor n/2\rfloor,\qquad b(n)=3\lfloor(n-1)/2\rfloor+2.
\]

For an active pair `(T,N)` with `T>=2` and `N>H`, define the exact residual

\[
 R_T(N)=F_T(N)-\tfrac12\{F_{T-1}(a(N))+F_{T-2}(b(N))\}.       \tag{1}
\]

This includes the progression error, negative cap loss, and coefficient
deficit from the preceding note. Choose either cutoff child with probability
`1/2`; the lower child consumes one ordinary clock and the upper consumes
two. Stop at `N_j<=H` or remaining clock `s_j<=1`. Let the stopping depth
be `sigma_T`, and write

\[
 B_T(N)=\mathbb E F_{s_{\sigma_T}}(N_{\sigma_T}),\qquad
 S_T(N)=\mathbb E\sum_{j<\sigma_T}R_{s_j}(N_j).
\]

The finite tree has depth at most `T`. Exact telescoping gives

\[
                         F_T(N)=B_T(N)+S_T(N).             \tag{2}
\]

This identity is kernel checked for an arbitrary rational-valued function,
with both stopping conditions included. The cutoff chain is an averaging
device on **source populations**, not a stochastic model of an individual
Collatz orbit.

## 2. A rational dyadic potential bounds the occupation time

Let `ell(n)` be the binary length, with `ell(0)=0`, and let
`Pv(n)=[v(a(n))+v(b(n))]/2` denote the unstopped cutoff average.
The following exact three-step drift holds for every `n>=4`:

\[
                    P^3\ell(n)\le\ell(n)-\frac18.          \tag{3}
\]

Here is an elementary proof, separately kernel checked. Both cutoff maps
and binary length are nondecreasing. If `ell(n)=k+3`, compare all eight
three-step descendants to those of `2^(k+3)-1`. With `p=2^k`, those
descendants are

\[
 p-1\quad(1\text{ copy}),\quad 3p-1\quad(3),\quad
 9p-1\quad(3),\quad27p-1\quad(1).
\]

Their lengths are at most `k,k+2,k+4,k+5`, respectively. The sum is at
most `8k+23`, one less than `8ell(n)`. No real logarithm or numerical
drift approximation is used in this proof.

Set

\[
 V(n)=\ell(n)+P\ell(n)+P^2\ell(n).
\]

Then `V-PV=ell-P^3 ell>=1/8` for `n>=4`. Also `V>=0`, and
`V(n)<=3ell(n)` for `n>=2`: the lower child loses one bit and the upper
child gains at most one, so `Pell<=ell` on positive states.
Finite telescoping for any depth and clock stopping gives

\[
 \mathbb E\sigma_T
 \le8\{V(N)-\mathbb EV(N_{\sigma_T})\}
 \le8V(N)\le24\ell(N),\qquad H\ge3,\ N\ge2.                \tag{4}
\]

These rational finite bounds are kernel theorems. Applying the same
bound before any fixed branch depth and letting that depth grow proves
almost-sure floor absorption of the auxiliary chain. Alternatively, on a
clock-exhaustion event at `T>1`, at least `(T-1)/2` branches have been
used; hence

\[
 \Pr(N_{\sigma_T}>H)\le\frac{48\ell(N)}{T-1}\longrightarrow0. \tag{5}
\]

The probabilistic limiting consequences are written, rather than part of
the rational Lean formalization. No individual Collatz termination follows
from this auxiliary absorption.

## 3. Linear size loses very little before stopping

The two integer endpoints satisfy exactly

\[
 a(n)+b(n)=2n-\mathbf1_{\{n\text{ even}\}},\qquad n\ge1.
\]

Thus the source cutoff is a supermartingale whose conditional loss is
`1/2` at an even state and zero at an odd state. Finite stopping gives

\[
 \mathbb E N_{\sigma_T}
 =N-\frac12\mathbb E\#\{j<\sigma_T:N_j\text{ even}\}
 \ge N-\frac12\mathbb E\sigma_T
 \ge N-12\ell(N).                                         \tag{6}
\]

Both the equality and the bounds are kernel checked. They hold at every
finite clock. Combining almost-sure absorption with an unjustified
interchange of limit and mean would contradict (6) for large `N`:
the limiting absorbed cutoff is at most `H`, while the means in (6)
can stay close to `N`. The stopped cutoff family is not uniformly
integrable in that regime.

## 4. The actual clock-zero and clock-one means are linear

At clock one, the minimum is `n` for odd sources and `n/2` for even
sources. Exact summation gives

\[
 2\sum_{j\le2q}m_1(j)=3q^2+q,\qquad
 2\sum_{j\le2q+1}m_1(j)=3q^2+5q+2.
\]

In particular `mean m_1 >=3N/8`. Since `g_H(y)=y1_(y>H)>=y-H`,
and `m_0>=m_1`,

\[
                    F_s(N)\ge\frac{3N}{8}-H\quad(s=0,1).  \tag{7}
\]

The exact sums, cross-multiplied inequality, and rational normalized
bound are kernel checked. At a floor stop, `F_s(N)=0` for any remaining
clock, and the right side of (7) is nonpositive because `N<=H`.
Therefore (6)–(7) imply, at **every** finite clock,

\[
 \boxed{B_T(N)\ge\frac{3N}{8}-\frac92\ell(N)-H,\qquad
                                      N\ge2,\ H\ge3.}      \tag{8}
\]

The full implication for actual Collatz prefix-minimum means is a
kernel theorem. Its positive right side can be linear in the initial
cutoff even while the probability in (5) tends to zero. Rare large
terminal cutoffs cannot be discarded merely because their probability
vanishes.

For `N=256,H=4`, binary length is nine, so (8) gives

\[
                              B_T(256)\ge103/2.            \tag{9}
\]

Literal ordinary-step paths for all sources `1..256` end at or below
four within 125 steps. Lean checks every supplied edge and the fuel
bound by kernel reduction, then applies a generic checker-soundness
proof. This proves `F_128(256)=0`. Prefix monotonicity extends that
equality to every `T>=128`. Consequently (2) and (9) give the kernel
statement

\[
                    \boxed{S_T(256)\le-103/2\quad(T\ge128).} \tag{10}
\]

The certificate has 256 paths and 10,971 edges. It is not a native
finite check, and no timeout is used to classify an orbit. Direct
evaluation of deeply nested minima was replaced by literal edge
certificates so the same finite assertion has an efficient kernel proof.

Equation (10) does not disprove a cancellation method. It quantifies
the cancellation such a method must capture. An argument seeking a
vanishing total error while dropping this terminal term would already
fail on this verified finite population.

## 5. The universal leading boundary coefficient is 3/7

The short-clock means in (7) have leading coefficients `c_0=1/2`
and `c_1=3/8`. The cutoff ratios and clock shifts determine the recurrence

\[
 c_T=\frac14c_{T-1}+\frac34c_{T-2},\qquad
 \boxed{c_T=\frac37+\frac1{14}\left(-\frac34\right)^T.}       \tag{11}
\]

The closed formula follows by substitution and the two initial values.
In particular `3/8<=c_T<=1/2`. For `phi_T(n)=c_T n`, its exact local
residual, at `T>=2`, is

\[
 r_T(n)=\phi_T(n)-\tfrac12\{\phi_{T-1}(a(n))+\phi_{T-2}(b(n))\}
 =\begin{cases}
 c_{T-2}/2,&n\text{ even},\\
 (c_{T-1}-c_{T-2})/4,&n\text{ odd}.
 \end{cases}                                                \tag{12}
\]

Hence `|r_T(n)|<=1/4`. At a clock stop, the exact short-clock formulas
give `|F_s(n)-c_s n|<=H+1`: the raw clock-zero/one means differ from
their linear terms by at most one, and truncating below the floor
changes the mean by at most `H`. At a floor stop the difference is
at most `H/2`, since `F_s=0` and `0<=c_s<=1/2`.

Unroll `phi` by the same finite identity (2). The terminal comparison
and (4) prove the written uniform estimate

\[
 \boxed{|B_T(N)-c_TN|\le H+1+\tfrac14\mathbb E\sigma_T
                              \le H+1+6\ell(N).}           \tag{13}
\]

No cancellation of unknown Collatz terms is assumed in this calculation.
Section 7 proves `F_(T(N))(N)/N -> 0` whenever `T(N)->infinity`.
Consequently, for each fixed `H>=3`, (2), (11) and (13) give

\[
 \boxed{\frac{B_{T(N)}(N)}N\longrightarrow\frac37,\qquad
        \frac{S_{T(N)}(N)}N\longrightarrow-\frac37.}        \tag{14}
\]

This identifies the necessary leading negative cancellation. The
coefficient `3/7` comes from the exhausted-clock boundary; it is not
the unknown nonconvergent mass in the critical-clock analysis. The
unproved target needs control of the remaining unscaled mean, not
just cancellation of its order-`N` terms.

## 6. Weighting by cutoff size reverses the large-scale bias

For the ideal unrounded cutoff chain, the multipliers are `1/2` and
`3/2`, each chosen with probability `1/2`. A path of `j` steps containing
`u` upper branches has cutoff `N 3^u/2^j`. Multiplying its probability
by its cutoff and dividing by `N` changes its branch probabilities to

\[
                     (p_-,p_+)=(1/4,3/4).                \tag{15}
\]

The fair mean logarithmic increment is negative,
`log(3/4)/2`. The size-weighted increment is positive,

\[
 \tfrac14\log(1/2)+\tfrac34\log(3/2)=\tfrac14\log(27/16)>0.
\]

This is a change of measure on auxiliary cutoff paths, not an assumption
about random Collatz parity. At any finite stopping horizon the ideal
mean cutoff is exactly `N`. The fair floor contribution is at most `H`,
so the size-weighted probability of clock exhaustion is at least
`1-H/N`, even while its fair probability tends to zero.

For the actual rounded integer chain, the corresponding weights are

\[
 p_-(n)=\frac{a(n)}{2n},\qquad p_+(n)=\frac{b(n)}{2n},\qquad
 p_-(n)+p_+(n)=1-\frac{\mathbf1_{\{n\text{ even}\}}}{2n}.    \tag{16}
\]

They define a substochastic kernel, with the missing mass sent to a
zero-payoff cemetery state. Along every surviving path the product
telescopes to its fair probability times the terminal cutoff divided by
the starting cutoff. Equation (16) tends to (15) at large states, but
the rounded and ideal chains are kept separate in verification.

These change-of-measure deductions are written elementary algebra;
the finite replay checks the ideal identity with exact rationals.

## 7. Elementary finite parity gives the sublinear prefix mean

This step needs no analytic progression mixing or minimum tightness.
Use the shortcut map `U(n)=n/2` for even `n`, `(3n+1)/2` for odd `n`.
For a `k`-step parity word containing `j` odd steps, write

\[
 U^k(n)=A n+B,\qquad A=3^j/2^k,\qquad
                       0\le B\le(3/2)^k-1.               \tag{17}
\]

The correction bound follows inductively from
`B_(i+1)<=3B_i/2+1/2`, starting at zero. Each length-`k` parity
word occurs in exactly one residue class modulo `2^k`. For completeness,
lift a fixed class from modulus `2^k` to the two classes `r,r+2^k`.
They share the first `k` parities, and their `k`th images differ by
the odd number `3^j`, so their next parities are opposite. Starting
with the empty word proves the assertion by induction. The exact
residue affine identity is already kernel proved in
[CollatzAffine.lean](../CollatzAffine.lean), freshly rebuilt for this audit;
the word-counting and population assembly here remain written.

An entirely rational square-root majorant avoids numerical approximations.
Put

\[
 e=17/24,\quad o=49/40,\quad q=(e+o)/2=29/30<1,
 \qquad w=e^{k-j}o^j.                                     \tag{18}
\]

Since `e^2>=1/2` and `o^2>=3/2`, `w^2>=A`. For any nonnegative
`w,A` with this property, `min(1,A)<=w`: if `w>=1` this is immediate;
otherwise `A<=w^2<=w`. The first `k` shortcut states occur within
`2k` ordinary steps. Thus for `T>=2k`,

\[
 m_T(n)\le\min(n,U^k(n))\le n\min(1,A)+B
                              \le nw+(3/2)^k.
\]

Each residue occurs at most `N/2^k+1` times among `1..N`, and the
sum of the word weights over the complete residue block is
`(e+o)^k=2^k q^k`. Using `n<=N` and dropping the tail indicator gives
the explicit written finite bound, uniform in `H`,

\[
 \boxed{\frac{F_T(N)}N
       \le\left(1+\frac{2^k}{N}\right)\left(\frac{29}{30}\right)^k
                              +\frac{(3/2)^k}{N},\qquad T\ge2k.} \tag{19}
\]

If `N>=2^k`, its right side is at most

\[
                   2(29/30)^k+(3/4)^k.                   \tag{20}
\]

For any integer clock function `T(N)->infinity`, choose
`k=min(floor(T(N)/2),floor(log_2 N))`. Then `k->infinity`, so

\[
                              F_{T(N)}(N)=o(N).            \tag{21}
\]

This says that the unnormalized tail **sum** is `o(N^2)`, not that
it is below `N`. It is therefore far weaker than the sufficient
linear-tail budget. The same elementary bound applies to the global
minimum because it is below every finite-prefix minimum.

At `T>=2floor(log_2 N)`, (19) gives a sublinear power bound, with
exponent `1+log_2(29/30)<1`, plus the smaller affine-correction term.
Increasing `k` much further makes the residue-endpoint term
`(2q)^k` grow in the unnormalized mean bound. Thus simply increasing
the clock in this estimate does not supply the strict budget `F_T(N)<1`.

## 8. Passing to the actual global minimum is a different route

This note does **not** assert a persistent boundary for the true global
minimum. Let

\[
 G_H(N)=\frac1N\sum_{n\le N}m(n)\mathbf1_{\{m(n)>H\}}.
\]

The elementary estimate (19) implies `G_H(N)=o(N)` too. Fix `k`,
use `m<=m_(2k)`, let `N` grow, and then let `k` grow. No previous
analytic tightness premise is needed. This does not prove first-moment
uniform integrability: sublinearity is much weaker than the uniform
linear-tail budget below one.

For this clockless function, stop only at the floor or branch depth
`J`. Given `epsilon>0`, choose `K` so that `G_H(n)<=epsilon*n` above
`K`, and set `M_K=max_(n<=K)G_H(n)`. Its floor value is zero, so

\[
 \mathbb E G_H(N_{\tau\wedge J})
 \le\epsilon\mathbb E N_{\tau\wedge J}+M_K\Pr(\tau>J)
 \le\epsilon N+M_K\Pr(\tau>J).                            \tag{22}
\]

Let `J` tend to infinity and then `epsilon` to zero. The terminal
mean now vanishes, using only sublinearity and the cutoff size bound.
Thus the **clockless** signed residual has a valid representation as
the limit of its finite expected sums. This does not automatically
identify that limit with the expectation of an infinite random sum;
absolute integrability or another interchange argument would be needed.

The order matters: take each fixed population's prefix minimum to its
attained global minimum first, then unroll the clockless recurrence.
Alternatively, a finite-clock proof must retain and cancel (8).
Neither route currently provides the required uniform signed residual
bound or the all-cutoff linear-tail budget. The elementary finite-parity
population estimate, its asymptotic consequences, and this clockless
limit are written arguments, not newly kernel-formalized analytic theorems.

## 9. Verification scope

Run `python3 verify_minimum_linear_boundary.py`; see the
[record](../results/minimum-linear-boundary/verification.json).
The structural cutoff and actual-prefix theorems, finite literal path
certificates, exact Python censuses, and written probabilistic limits are
recorded separately. The verifier authenticates the prior cap, cutoff,
and critical-clock records before fresh sequential builds.

The independent replay checks dyadic drift on a continuous cutoff range
and selected huge powers of two, exact clock-zero/one formulas, actual
Collatz prefix values at all queried cutoff states, and signed unrolling
by both forward distributions and recursive cutoff averaging. Huge
dyadic drift checks and long cutoff-tree leaves are arithmetic evaluations,
not trajectory censuses through those cutoffs. No new external theorem
is used in the kernel results or finite witnesses.

The replay also checks the exact leading-coefficient recurrence and its
rounding residuals, all parity words through length 14, their affine
correction bounds, and the rational word-majorant sums. Very large exact
rational results are stored as explicitly marked outward rational
enclosures with binary digests; all proof decisions use the exact values
before that reporting step.

Thirty new kernel roots passed ten fresh sequential builds. The replay
independently checks 10,971 literal certificate edges and all 256 sources
through clock 128; it also follows 83,981 actual sources through clock 32,
providing 9,451 population values for 78 exact signed cutoff-tree checks.
There are 32,767 complete residue-word checks through shortcut length 14,
66,045 leading-profile rounding checks, and 20,743 ideal tilted-state
checks. None of these finite counts certifies the written limiting claims.
