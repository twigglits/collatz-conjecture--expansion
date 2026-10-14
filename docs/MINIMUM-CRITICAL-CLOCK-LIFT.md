# A second growing block at the critical logarithmic clock

**Status: an infinite-family finite-prefix obstruction, with 21 kernel
theorem roots. The strict population tail budget also fails at the leading
clock coefficient \(\gamma=\log_2 6\), even after any fixed additive shift.
A written consequence requires a further logarithmic correction along an
explicit sequence of cutoffs. No divergent orbit or complete Collatz proof
is obtained.**

The [previous clock barrier](MINIMUM-CLOCK-BARRIER.md) excluded leading
coefficients below \(\gamma\). Here a constructive congruence forces a second
growing block after the first one. For every integer \(j\ge2\), we construct
\[
 2^{j+1}\le K_j<2^{j+2},\qquad N_j=2^{K_j}-1,
\]
and prove, for the actual ordinary Collatz map,
\[
 \boxed{2^T\le6^{K_j+j}\quad\Longrightarrow\quad m_T(N_j)=N_j.}       \tag{1}
\]
The minimum includes every ordinary time from zero through \(T\).
The previous block alone guaranteed only \(2^T\le6^{K_j}\).

Consequently, for every fixed floor \(H<N_j\), the source \(N_j\)
alone gives
\[
 \boxed{\sum_{n\le N_j}m_T(n)\mathbf1_{\{m_T(n)>H\}}\ge N_j.}        \tag{2}
\]
Thus a strict all-cutoff budget must obey
\[
 2^{T(N_j)}>6^{K_j+j}.                                            \tag{3}
\]
These integer statements and their population consequence are kernel
checked. This new lower bound is one for the normalized tail mean;
unboundedness of the mean at the critical coefficient is not established.

## 1. An elementary lift of the exponent

For every \(j\ge0\), the following exact identity has a natural-number
witness \(c_j\):
\[
 9^{2^j}=1+2^{j+3}(2c_j+1).                                      \tag{4}
\]
At \(j=0\), take \(c_0=0\). Squaring the identity proves the next one
with
\[
 c_{j+1}=c_j+2^{j+1}(2c_j+1)^2.
\]
This is a direct kernel induction, with no external valuation theorem.

Start with \(a_0=0\). Suppose
\[
 0\le a_j<2^j,\qquad 9^{a_j}+7=2^{j+3}q_j.
\]
If \(q_j\) is even, let \(a_{j+1}=a_j\). Otherwise set
\(a_{j+1}=a_j+2^j\). Equation (4) gives
\[
 9^{a_j+2^j}+7
 =2^{j+3}\bigl(q_j+9^{a_j}(2c_j+1)\bigr).
\]
When \(q_j\) is odd, the parenthesis is even. Either branch therefore
proves
\[
 a_{j+1}<2^{j+1},\qquad
                  2^{j+4}\mid9^{a_{j+1}}+7.
\]
The Lean definition uses the parity of the exact quotient and is
computable. Its all-index range and divisibility properties are proved
by induction.

Now put
\[
                         K_j=2(a_j+2^j).                         \tag{5}
\]
Multiplication by \(9^{2^j}\), which is one modulo \(2^{j+3}\),
preserves the congruence. Hence there is a positive integer \(q\) with
\[
                 3^{K_j}+7=2^{j+3}q.                            \tag{6}
\]
Equation (5) gives the displayed bounds on \(K_j\), and also
\[
                         \lfloor\log_2 K_j\rfloor=j+1.          \tag{7}
\]
All of (4)–(7), in their natural-number forms, are kernel checked.
No uniqueness assertion about all possible exponent lifts is needed.

## 2. Two growing blocks and three safe halvings

Write \(K=K_j\), \(N=2^K-1\), and let \(q\) satisfy (6). The first
\(K\) odd shortcut steps take \(2K\) ordinary steps and end at
\(3^K-1\). The existing exact growing-block theorem proves that all
these intermediate values are at least \(N\).

Equation (6) rewrites this endpoint as
\[
                   3^K-1=8(2^j q-1).                           \tag{8}
\]
The next three ordinary steps are halvings, reaching
\(x=2^j q-1\). They are safe for the prefix minimum: since \(K\ge8\),
\[
                   3^K-1\ge8(2^K-1),\qquad x\ge N.              \tag{9}
\]
The kernel proves the first inequality already for \(K\ge6\).

The source \(x\) then has \(j\) further odd shortcut steps, taking
\(2j\) ordinary steps and ending at
\[
                             z=3^j q-1.
\]
Every intermediate value in this second block is at least \(x\).
Thus, with
\[
                  O=K+j,\quad D=K+j+3,\quad B=O+D,
\]
the kernel obtains
\[
                 C^B(N)=z,\qquad m_B(N)=N.                      \tag{10}
\]
There are \(O\) odd ordinary steps and \(D\) even ordinary steps in
this prefix.

The exact minus-one terms obey
\[
 3^r(2^r q-1)\le2^r(3^r q-1).
\]
Applying this at the two blocks and using (8) gives
\[
                         3^O N\le2^D z.                        \tag{11}
\]
This inequality is proved with integer multiplication and cancellation,
so no floating-point slope comparison is used.

If \(T\le B\), (10) already proves (1). If \(T=B+s\) and
\(2^T\le6^O\), cancellation of \(2^O\) gives
\[
 2^{D+s}\le3^O.
\]
Multiplying by \(N\), using (11), and cancelling \(2^D\) yields
\(2^sN\le z\). Every ordinary Collatz step satisfies \(C(y)\ge y/2\),
so no value in the next \(s\) steps can be below \(N\). Prefix
concatenation proves (1). The reusable kernel lemma for this argument
takes an arbitrary prefix with (10)–(11) as premises.

## 3. What this forces on a proposed population clock

For \(j\ge2\), \(N_j>1\), and
\[
 \log_2N_j<K_j,\qquad
 \log_2\log_2N_j<\log_2K_j<j+2.
\]
Taking logarithms in (3) therefore gives the written necessary bound
\[
 \boxed{T(N_j)>
   \gamma\log_2N_j+\gamma\log_2\log_2N_j-2\gamma.}                 \tag{12}
\]
The real logarithms and this comparison are written mathematics;
the exact integer implication (3) is the kernel statement.

Since \(N_j\) tends to infinity, (12) rules out clocks
\[
 T(N)=\left\lfloor
       \gamma\log_2N+c\log_2\log_2N
      \right\rfloor+L,\qquad c<\gamma,                           \tag{13}
\]
for every fixed integer \(L\ge0\) and fixed floor \(H\): the deficit
\((\gamma-c)\log_2\log_2N-2\gamma-L\) grows without bound, so (13)
violates the necessary bound at all sufficiently large family cutoffs.
Only sufficiently large \(N\), where the clock is nonnegative, are
relevant when \(c<0\).

There is also a completely integer kernel version of the important
case \(c=0\). Define
\[
 \mathcal T_L(N)=
 \left\lfloor\log_2\!\left(6^{\lfloor\log_2(N+1)\rfloor}\right)
       \right\rfloor+L.
\]
At \(N=N_j\), this is \(\lfloor\log_2(6^{K_j})\rfloor+L\).
For \(j\ge L\),
\[
 2^{\mathcal T_L(N_j)}
 \le6^{K_j}2^L\le6^{K_j+j},
\]
so (1) applies. The kernel proves
\[
 \forall H,L,b\in\mathbb N,\quad
 \exists N>b:\quad
 N\le\sum_{n\le N}
       m_{\mathcal T_L(N)}(n)\mathbf1_{\{m_{\mathcal T_L(N)}(n)>H\}}.
                                                                    \tag{14}
\]
At these same cutoffs, the usual clock
\(\lfloor\gamma\log_2N_j\rfloor+L\) is no larger than
\(\mathcal T_L(N_j)\), so it fails as well.
The definition of \(\mathcal T_L\) is chosen for the exact integer
statement; no comparison with the usual clock at every other cutoff
is asserted.

Neither (12) nor (14) rules out a larger leading coefficient than
\(\gamma\). Nor do they exclude the full coefficient \(\gamma\) on
the logarithmic correction with every additive constant. They are
necessary restrictions on this strict finite-prefix budget.

## 4. Explicit sources and verification scope

The first few choices are:

| \(j\) | \(a_j\) | \(K_j\) | Old guaranteed clock | New guaranteed clock |
|---:|---:|---:|---:|---:|
| 2 | 3 | 14 | 36 | 41 |
| 3 | 7 | 30 | 77 | 85 |
| 4 | 7 | 46 | 118 | 129 |
| 5 | 23 | 110 | 284 | 297 |
| 6 | 23 | 174 | 449 | 465 |
| 10 | 599 | 3246 | 8390 | 8416 |

These guaranteed clocks need not be the first descent times. For
example, \(N_2=16383\) first descends at ordinary time 70 and reaches
one at time 159; \(N_3=1073741823\) first descends at time 197 and
reaches one at time 449. Both hitting-one statements, along with the
two block-length evaluations, have axiom-free kernel proofs by
reduction. Their first-arrival and first-descent minimality are checked
in Python. They illustrate why a large finite minimum is compatible
with eventual convergence.

The [Lean module](../lean/MinimumCriticalClockLift.lean) audits 21
roots. Apart from the two axiom-free closed roots, their axiom reports
contain only the standard logical axioms. There is no native finite
computation axiom, admitted proof, or imported external theorem in the
new argument.

The [verifier](../verify_minimum_critical_clock_lift.py) authenticates
the preceding manifest, freshly builds the twelve Lean modules
sequentially, and then runs independent Python checks:

- Modular lifting and top-bit identities through index 1024, using
  modular exponentiation rather than the full-power quotient in Lean.
  These checks do not construct the enormous sources at large indices.
- Full enumeration of the possible lift exponents for indices 0–12,
  compared with the constructed exponent.
- Ordinary-step prefix replays for the thirteen selected sources
  with indices 2–14, including all prefix minima and exact block
  endpoints. No continuous interval up to these sources is enumerated.
- Separate convergence replays for the nine sources with indices
  2–10, including the two kernel hitting witnesses.

Run the verifier with Python 3 from the repository root. The
[verification manifest](../results/minimum-critical-clock-lift/verification.json)
and [replay record](../results/minimum-critical-clock-lift/replay.json)
contain the exact counts, hashes, and build records.

Verification passed on 14 October 2026 at 20:29:58 UTC. The twelve
fresh builds took 6.055 seconds; 26 previous hashes were authenticated
and the new manifest records 28 files. Independent checks include
1,025 instances of each modular identity and bound, 8,191 enumerated
small exponent residues, 186,810 ordinary prefix steps and 186,823
prefix-time comparisons, 208 exact block endpoints, and 117 shifted
clock inequalities. The largest actually replayed source has 33,966
bits. The separate nine-source convergence replay has 80,543 steps;
608 of these replay the two kernel hitting witnesses.

The argument adds no external premise and makes no claim of novelty.
It does not prove convergence of the infinite constructed family,
unbounded tail means at the critical clock, a uniform bound for actual
global minima or residuals, vanishing nonconvergent mass, or the full
Collatz conjecture.
