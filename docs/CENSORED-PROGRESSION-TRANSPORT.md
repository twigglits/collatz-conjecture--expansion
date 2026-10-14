# Censored deficit transport and the progression-average error

**Status: exact finite transport for the ordinary Collatz map, with kernel
proofs of the recursion and sum identities. Native interval censuses and a
smaller independent Python census reject specific proposed error bounds.
No asymptotic bound or complete Collatz proof is obtained.**

The [censored-deficit criterion](CENSORED-DEFICIT-CLOCK.md) leaves open
the all-source estimate `sum_(n<=2^k) A_(8k)(n)=o(k*2^k)`. Splitting a
source interval into even and odd inputs gives an exact recurrence for
this statistic. The odd inputs sample the progression `3n+2`, so the
recurrence requires control of a progression average. Its sampling error
is separate from the explicit correction caused by the `+1` in `3n+1`.

## 1. Finite transport, including sources still alive at the cutoff

Use **ordinary** time throughout. Let `tau_1(n)` be first arrival at one,
with value infinity if there is no arrival. Write

\[
 L_t(n)=\min(t,\tau_1(n)),\qquad
 A_t(n)=\sum_{0\le h<L_t(n)}(1-W_h(n)),
 \qquad 0\le A_t(n)\le L_t(n)\le t.                 \tag{1}
\]

As before, `W_0=1`, even steps preserve weight, and an odd input `v`
multiplies it by `3v/(3v+1)`. Neither computing (1) nor the following
identities requires knowing whether an alive source ever reaches one.

For `n>=1`, an initial even step contributes zero deficit and gives

\[
                         A_{t+1}(2n)=A_t(n).                 \tag{2}
\]

For an odd source `2n+1`, with `n>=1`, put `q=3n+2`. Its first two
ordinary steps are

\[
                   2n+1\longmapsto 2q\longmapsto q.
\]

The first deficit cell is zero; the second is `1-r`, where
`r=(2q-1)/(2q)`. Subsequent alive weights are `r` times the relative
weights from `q`, and the number of those cells is `L_t(q)`. Therefore

\[
\begin{aligned}
 A_{t+2}(2n+1)
   &=(1-r)+rA_t(q)+(1-r)L_t(q)\\
   &=A_t(q)+e_t(q),\\
 e_t(q)&=\frac{1+L_t(q)-A_t(q)}{2q}.
\end{aligned}                                                  \tag{3}
\]

This includes `t=0`, arrivals exactly at the cutoff, and earlier
arrivals. The excluded odd source `1` has deficit zero and is handled
separately when summing. Since
`L_t(q)-A_t(q)=sum_(h<L_t(q)) W_h(q)`,

\[
                  \frac1{2q}\le e_t(q)\le\frac{t+1}{2q}.       \tag{4}
\]

The Lean module defines the actual ordinary map, its weight factor, a
finite alive clock, and deficit with arbitrary initial weight. Its
scaling identity proves (3) for that recursion; this is more than a
formal identity for unrelated abstract variables. The module also proves
(2), the correction identity, and (4) after multiplication by `2q`.
The correspondence between the finite alive clock and the notation
`min(t,tau_1)` in (1) is the elementary recursive interpretation; it
does not assert finite arrival for every source.

## 2. The population identity and the two errors

For positive integers `X,N`, define

\[
\begin{aligned}
 B_t(N)&=\sum_{n=1}^N A_t(n),& F_t(N)&=B_t(N)/N,\\
 P_t(X)&=\frac1X\sum_{n=1}^X A_t(3n+2),&
 E_t(X)&=\sum_{n=1}^X e_t(3n+2),\\
 \delta_t(X)&=P_t(X)-F_t(3X+2).
\end{aligned}                                                  \tag{5}
\]

Thus the progression has exactly `X` terms, from `5` through `3X+2`.
The reference interval is **all** positive sources through `3X+2`.
Splitting `1..2X+1` into its even and odd sources, using `A_t(1)=0`,
gives the exact identity

\[
 B_{t+2}(2X+1)=B_{t+1}(X)+\sum_{n=1}^X A_t(3n+2)+E_t(X).        \tag{6}
\]

Equivalently,

\[
\boxed{(2X+1)F_{t+2}(2X+1)
 =X F_{t+1}(X)+X F_t(3X+2)+X\delta_t(X)+E_t(X).}               \tag{7}
\]

The last two terms have different origins. The correction `E_t` is
positive and has the direct bound, with `H_X=sum_(n<=X)1/n`,

\[
 0<E_t(X)\le(t+1)\sum_{n=1}^X\frac1{6n+4}
       \le\frac{t+1}{6}H_X
       \le\frac{t+1}{6}(1+\log X).                            \tag{8}
\]

The kernel module proves (6) using a finite parity split. The harmonic
comparison (8) and normalized rearrangement (7) are written arguments.
Equation (8) does **not** bound `X delta_t(X)`: that is a sampling
error for the actual deficits on a nontrivial arithmetic progression.

## 3. Exact finite counterbounds

The censuses take `X=2^k`, `Y=3X+2`, and `t=8k`, using all sources in
`1..Y`. They stop each computation at first arrival or the cutoff.
Here are decimal displays of rigorously enclosed quantities; decisions
use the recorded integers, not these rounded displays.

| k | t | Sources through Y | delta (approximately) | X delta / t (approximately) |
|---:|---:|---:|---:|---:|
| 17 | 136 | 393,218 | 0.00250907855 | 2.41816135 |
| 20 | 160 | 3,145,730 | 0.00138426787 | 9.07193790 |

In particular, at `X=1048576`, `t=160`, the exact intervals certify

\[
 \boxed{\delta_t(X)>\frac{9t}{X}>0,\qquad
                         X\delta_t(X)>8E_t(X).}              \tag{9}
\]

Here `E_t(X)` is approximately `172.30790118`, while the ratio
`X delta_t(X)/E_t(X)` is approximately `8.42393212`. Thus none of the
following proposed **uniform finite inequalities** holds:

* `P_t(X)<=F_t(3X+2)`;
* `delta_t(X)<=9t/X`;
* `X delta_t(X)<=8E_t(X)`.

At the smaller cutoff, the independent census also certifies
`delta_t(X)>2t/X`. These are counterexamples to those precise
inequalities. A finite violation does not reject a larger unspecified
constant, an asymptotic bound beyond an unspecified threshold, every
`O(t/X)` or `O(t log X/X)` estimate, or every constant multiple of `E_t`.
It also does not disprove the all-source zero-limit criterion.

For reproducibility, let `S=2^64`, and let `P_-`, `B_+`, `E_+` be the
scaled lower progression sum, upper prefix sum, and upper correction
sum at `k=20`. The recorded values are

```text
P_- = 35531119056706020611884338
B_+ = 106513097985271158323620897
E_+ = 3178519754951037415201
S   = 18446744073709551616
```

The lower bound on the sampling error is

\[
              \delta_t(X)\ge\frac{Y P_- - X B_+}{XY S}.
\]

Two closed integer inequalities establish (9):

\[
 YP_->XB_++9tYS,\qquad YP_->XB_++8YE_+.                       \tag{10}
\]

The generated certificate proves these comparisons in Lean with
`decide`, without native computation or axioms. It does **not** derive
the population sums inside the kernel; those remain native interval
census results with the independent checks described below.

## 4. Verification scope

Run:

```sh
python3 verify_censored_progression_transport.py
```

The [verification record](../results/censored-progression-transport/verification.json)
keeps four kinds of evidence separate:

* **Kernel:** eight roots for finite actual-map scaling, parity transport,
  loss and correction identities, bounds, and the population sum;
  three further roots for closed comparisons of recorded endpoints.
  The finite transport roots use only standard axioms. The three integer
  comparisons use no axioms. Neither file uses `native_decide`.
* **Native finite census:** checked-overflow Rust propagates lower and
  upper weight bounds at scale `2^64`, then sums directed deficit and
  correction bounds. It executes 41,339,617 ordinary steps at `k=17`
  and 396,719,184 at `k=20`. It is not a kernel computation.
* **Independent Python:** for every source through 393,218 at clock 136,
  unbounded integers reconstruct each exact weight as
  `n*3^odd/(2^even*current_state)` before rounding. These intervals lie
  inside the native intervals, and all step, odd-step, and alive counts
  match. This is a full independent replay only of the smaller census.
  A separate Fraction-product implementation checks both transport
  identities for 1,024 parent indices at every cutoff `0..128`, and
  checks finite population identities at 42 source/clock settings.
* **Written:** the harmonic bound, normalized population recurrence,
  and interpretation of the failed proposals. No external density
  theorem, convergence premise, or unproved asymptotic input is needed
  for this finite result. The earlier zero-limit criterion retains its
  own stated written and external premises.

At the larger cutoff 1,169,637 sources are still alive. This is only an
arrival flag at ordinary time 160, not evidence of nonconvergence.

For separate stages, `--census-only` saves native and independent census
evidence; `--reuse-census` authenticates that saved evidence before fresh
kernel builds and Fraction replay. A reused stage is identified in the
manifest. The default command reruns both censuses sequentially.

The remaining task is an actual progression-error estimate strong
enough to control (7), or another direct bound for the all-source
censored mean. Treating the progression as a uniform interval, or
absorbing its error into (8) with any of the rejected constants, cannot
supply that missing argument. Escape, additional cycles, and full
Collatz remain unresolved.
