# Exact minimum transport and the limit of cap-only accounting

**Status: kernel proofs of finite-prefix transport and a small actual-Collatz
obstruction, with a larger independently replayed Python witness. The required
uniform linear-tail estimate is still unproved. Collatz remains unresolved.**

The [linear minimum-tail criterion](MINIMUM-TAIL-RIGIDITY.md) would suffice
for convergence if its budget held at every source cutoff. The odd branch
of its population recurrence has a favorable truncation: an orbit minimum
cannot exceed its source. This note keeps that term exactly and tests whether
it can pay for the separate arithmetic-progression sampling error.

It cannot do so by itself at all finite clocks and cutoffs. There are actual
Collatz prefixes with positive sampling error, and even positive error in
the normalized population recurrence, after the cap loss has become zero
at that and every later clock. This excludes a particular accounting rule,
not eventual estimates or the underlying linear-tail criterion.

## 1. Exact transport before any limit

Use ordinary Collatz steps and include the initial source in the minimum:

\[
 m_t(n)=\min_{0\le j\le t}C^j(n),\qquad
 g_H(y)=y\mathbf1_{\{y>H\}},\qquad f_{H,t}(n)=g_H(m_t(n)).       \tag{1}
\]

For every nonnegative clock `t`,

\[
 m_{t+1}(2n)=m_t(n),\qquad
 m_{t+2}(2n+1)=\min\{2n+1,m_t(3n+2)\}.                     \tag{2}
\]

The first identity uses `m_t(n)<=n`. In the second, the two initial
steps are `2n+1 -> 6n+4 -> 3n+2`; the intermediate even value cannot
lower the minimum. Define the nonnegative cap loss

\[
 d_H(s,y)=g_H(y)-g_H(\min(s,y)),\qquad
 D_{H,t}(X)=\sum_{n=1}^X d_H(2n+1,m_t(3n+2)).                \tag{3}
\]

Its exact scalar form is

\[
 d_H(s,y)=
 \begin{cases}
 g_H(y),&s\le H,\\
 (y-s)_+,&H<s.
 \end{cases}                                                \tag{4}
\]

Thus the tail identities are

\[
 f_{H,t+1}(2n)=f_{H,t}(n),\qquad
 f_{H,t+2}(2n+1)+d_H(2n+1,m_t(3n+2))=f_{H,t}(3n+2).         \tag{5}
\]

All of (2)–(5) are kernel checked, with natural-number addition used
in (5) so that truncated subtraction cannot hide a sign error.

## 2. A cap that is zero remains zero

For fixed `H,s`, (4) is nondecreasing in `y`. The prefix minimum
`m_t(q)` is nonincreasing in `t`. Consequently

\[
 t\le u\quad\Longrightarrow\quad
 0\le D_{H,u}(X)\le D_{H,t}(X).                            \tag{6}
\]

In particular, `D_{H,t}(X)=0` implies `D_{H,u}(X)=0` for **every**
later `u`. This is a kernel theorem for arbitrary clocks and cutoffs.
It requires no convergence assumption or computation of the remaining
orbit. For a finite sum, the same conclusion also holds term by term.

## 3. The full population identity and its normalized error

Let `H>=1`, `N>=3`, and set

\[
 a=\lfloor N/2\rfloor,\quad X=\lfloor(N-1)/2\rfloor,\quad c=3X+2,
 \quad F_t(M)=\frac1M\sum_{n=1}^M f_{H,t}(n),
\]
\[
 P_t(X)=\frac1X\sum_{n=1}^Xf_{H,t}(3n+2),\qquad
 \delta_t(X)=P_t(X)-F_t(c).                                \tag{7}
\]

The source `1` has zero tail contribution. Splitting all other sources
by parity in (5) gives

\[
 \boxed{NF_{t+2}(N)+D_{H,t}(X)=aF_{t+1}(a)+XP_t(X).}        \tag{8}
\]

The unnormalized identities for `N=2X+1` and `N=2(X+1)` are both
kernel checked. There is no omitted even endpoint in the latter case.
Define the fair recurrence residual

\[
 R_{H,t}(N)=F_{t+2}(N)-\tfrac12\{F_{t+1}(a)+F_t(c)\}.
\]

Then exactly

\[
 \boxed{R_{H,t}(N)=\frac XN\delta_t(X)-\frac{D_{H,t}(X)}N-Q,}\qquad
 Q=\left(\frac12-\frac aN\right)F_{t+1}(a)
   +\left(\frac12-\frac XN\right)F_t(c)\ge0.                \tag{9}
\]

The cap has the favorable negative sign. It nevertheless controls
neither the progression sampling error nor the residual by itself.

## 4. A kernel-sized actual-Collatz witness

Take `H=1`, `X=1`, `N=3`, and tail clock `t=4`. Direct finite minima
give

\[
 (f_{1,4}(1),\ldots,f_{1,4}(5))=(0,0,3,0,2),
 \quad f_{1,5}(1)=0,
 \quad\sum_{n\le3}f_{1,6}(n)=2.
\]

Here `m_4(5)=2<=3`, so

\[
 D_{1,4}(1)=0,\quad\delta_4(1)=2-1=1,\quad
 R_{1,4}(3)=\frac23-\frac{0+1}{2}=\frac16>0.              \tag{10}
\]

The closed integer computations are proved by kernel `decide`, without
native computation. The residual sign is also formalized after clearing
denominators: `10*2 > 15*0 + 3*5`.

By (6), every future cap `D_{1,u}(1)` is zero for `u>=4`.
Therefore neither positive quantity in (10) can be bounded, uniformly
over all finite clocks and cutoffs, by any nonnegative multiple of
the current cap or by any nonnegative weighted sum of future caps.
The Lean theorem includes every finite sum with arbitrary natural
weights; the conclusion for real nonnegative weights, including an
infinite sum, follows directly because every term is zero.

This does **not** exclude errors charged to past caps, signed cancellation
between different clocks, an additional boundary term, an eventual
large-scale estimate, or a different estimate for actual infinite minima.

## 5. The effect also occurs at a much larger finite cutoff

A direct integer census through source `98,306` and ordinary clock `256`
checks both population parities at `N=2^k` and `N=2^k+1`, `4<=k<=16`,
with parent clocks `4k,6k,8k,10k,12k,16k` and floors `1,16,64,256,1024`.
Every reported value uses only its specified finite prefix.

For `H=64`, `N=65,537`, `X=32,768`, `c=98,306`, and `t=254`,

\[
 \sum_{n\le65537} f_{64,256}(n)=33999,\qquad D_{64,254}(32768)=0,
\]
\[
 \delta_{254}(32768)=\frac{23790617}{1610645504}>0,\qquad
 R_{64,254}(65537)=\frac{778747256741}{105556874395648}>0.     \tag{11}
\]

The generic theorem (6) makes every later cap zero at this same floor
and progression cutoff. The finite zero-cap value in (11) is checked
in Python, **not** as a kernel-sized closed computation. A second
implementation follows each source separately and compares every
minimum at clocks `254,255,256`, including all integer sums in (11).
The first implementation advances the entire source population one
clock at a time; the second stops a source early only after its
minimum is already `1`.

The adjacent dyadic cutoff `N=65,536` has the same four integer sums:
parent `33,999`, even child `182`, full upper child `100,001`, and
progression `33,817`. Its upper cutoff is `98,303`, its cap is again
zero, and its fair residual is `47,479,783 / 6,442,385,408 > 0`.
Since `33,999 > 32,768`, the previous sufficient **dyadic half budget**
fails for the specific choice `H=64`, `T(2^k)=16k`, at `k=16`.
This does not refute the weaker strict budget `S<N` at this cutoff,
another floor or clock, or the actual infinite-minimum budget.

Neither example addresses arbitrary eventual thresholds: a finite
witness does not disprove a claim whose sufficiently large starting
scale is unspecified.

## 6. Why bounded-label mixing does not supply a linear error bound

For an integer `0<=y<=c` and `H<=c`, the exact layer-cake identity is

\[
 g_H(y)=H\mathbf1_{\{y>H\}}+
                     \sum_{s=H}^{c-1}\mathbf1_{\{y>s\}}.  \tag{12}
\]

Both populations in (7) have minima bounded by `c`. If `delta_s`
denotes their sampling discrepancy for the threshold indicator
`1_(m_t>s)`, then

\[
                  \delta_t(X)=H\delta_H+
                                      \sum_{s=H}^{c-1}\delta_s. \tag{13}
\]

Even granting a bound `|delta_s|<=epsilon_X` simultaneously at every
threshold and the required clock, absolute summation in (13) only
gives `|delta_t(X)|<=c*epsilon_X`. An arbitrary fixed logarithmic
power `epsilon_X=O_R((log X)^(-R))` would therefore give
`O_R(X/(log X)^R)` here. It supplies no uniformly small first-moment
error by this argument. Constants depending on `R` cannot be treated
as if uniform in a growing exponent.

This is a limitation of summing the bounded-observable errors in
absolute value, not a proof that cancellation or a stronger weighted
comparison is impossible. Nor is a new uniform finite-clock threshold
mixing theorem being asserted here. The layer-cake identity itself is
elementary and independently checked on the reported finite prefixes.

## 7. Verification and remaining task

Run `python3 verify_minimum_cap_transport.py`; the
[verification record](../results/minimum-cap-transport/verification.json)
separates kernel implications, exact Python computations, and written
normalization and summation arguments. The previous minimum-tail and
cutoff-descent manifests are authenticated before fresh sequential
builds. No new external theorem is used.

Twenty-two new kernel roots passed five fresh sequential Lean builds;
the roots use only `propext` and `Quot.sound` where needed. The small
replay checks 132,096 instances of each individual transport, 25,800
population identities, 655,360 cap-monotonicity inequalities, and 280
exact weighted layer-cake identities. The large census performs
25,166,336 ordinary steps and checks 780 population rows, including
15 with positive residual and zero cap. The independent replay uses
10,542,123 steps and compares all 294,918 late minima of the 98,306
sources. None of these Python counts is presented as a kernel census.

The useful surviving target is an estimate on the **whole signed
residual** in (9), or another genuinely weighted progression estimate,
strong enough to imply the all-cutoff linear-tail budget. Treating the
cap alone as a reserve for positive error is invalid at finite clocks.
No such stronger estimate is proved by the present checks.
