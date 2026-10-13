# A nonsummable tail for balanced adjacent coalescence

**Status: an unconditional all-depth bound for the actual shortcut map,
and a conditional test of a proposed route to zero escape mass. Collatz
remains unresolved.** The harmonic bound, including its restriction to
either initial parity, is kernel proved. The random-walk comparison and
the dyadic limit argument below are written proofs, not Lean theorems.
No novelty is claimed and no new external density theorem is assumed.

**Later follow-up:** [DYADIC-COALESCENCE-DEFECTS.md](DYADIC-COALESCENCE-DEFECTS.md)
proves that the actual unweighted fractions \(B_k\) in Section 4 have
divergent sum, using only the previously replayed positive lower density
of the known basin. Thus the sufficient condition \(\sum B_k<\infty\)
has a false premise for the actual map under that input. Summability of
the smaller sets of actual infinite-weight changes remains open; none
of the harmonic-tail identities below needs revision.

The [weighted-loss calculation](WEIGHTED-DISSIPATION.md) leaves the mean
infinite weight \(d\) undetermined. Balanced coalescence of nearby starts
could help because it gives an exact identity between their normalized
infinite weights. The question tested here is whether full-period
coalescence errors could make the corresponding dyadic changes summable.
They cannot: those errors have an unconditional harmonic lower bound.
This does **not** give a lower bound on the actual infinite-weight changes.

## 1. Exposing one more input bit

Let \(U(n)=n/2\) for even \(n\), \(U(n)=(3n+1)/2\) for odd
\(n\), and \(w_H(n)\) count the odd inputs in its first \(H\) steps.
Zero is included only as a convenient residue representative, with
\(U(0)=0\). Define
\[
 \Delta_H(r)=w_H(r)-w_H(r+1).
\]
The affine identity and odd-count periodicity give, for every nonnegative
\(r,q\), without requiring \(r<2^H\),
\[
 U^H(2^Hq+r)=3^{w_H(r)}q+U^H(r),\qquad
 w_H(2^Hq+r)=w_H(r).                                      \tag{1}
\]
In particular adding the next input bit \(2^H\) flips the parity of
**both** time-\(H\) endpoints: each added coefficient is odd. Formula
(1) also applies to \(r+1=2^H\), so the boundary residue is included.

If the endpoint parities agree, both next-bit children have gap
\(\Delta_H\). If they differ, their gaps are \(\Delta_H+1\) and
\(\Delta_H-1\), one of each. Thus the signed gap makes a fair step
whenever it changes. Its activity can depend on the previously exposed
bits; it is not asserted to be an independent step at every time.

Stop at the first equality of the odd counts, starting at time one:
\[
 G_H(r)=
 \begin{cases}
 |\Delta_H(r)|,&\Delta_j(r)\ne0\text{ for every }1\le j\le H,\\
 0,&\text{otherwise}.
 \end{cases}                                             \tag{2}
\]
At depth one, \(\Delta_1=\pm1\), hence \(G_1=1\). An absorbed
parent has two absorbed children. For an active parent, its gap is a
nonzero integer. The two absolute gaps therefore sum to twice its
absolute gap, whether they hold or take opposite unit steps. A child
that reaches zero contributes zero. Consequently, for all \(H\ge1\),
\[
 G_{H+1}(r)+G_{H+1}(2^H+r)=2G_H(r).                        \tag{3}
\]
Stopping matters: the raw difference can return to zero and later leave
zero when the endpoints have not merged. Its unstopped absolute value
does not satisfy (3).

## 2. Exact mass and a lower bound on the tail

Sum (3) over a complete period and use \(G_1(0)=G_1(1)=1\):
\[
 \boxed{\sum_{0\le r<2^H}G_H(r)=2^H\quad(H\ge1).}       \tag{4}
\]
The bit refinement preserves the initial parity. The same induction
separately gives, for \(e=0,1\),
\[
 \boxed{\sum_{0\le s<2^{H-1}}G_H(2s+e)=2^{H-1}.}         \tag{5}
\]

A residue is *balanced-coalescent* at depth \(H\) when both
\(U^H(r)=U^H(r+1)\) and \(w_H(r)=w_H(r+1)\). Write \(p_H\)
for its fraction among all \(2^H\) residues, and \(p_H^{(e)}\)
for its fraction conditioned on parity \(e\). Since each odd count
lies between zero and \(H\),
\[
 0\le G_H(r)\le H\,\mathbf1_{\{r\text{ not balanced-coalescent}\}}.
\]
Combining this with (4) and (5) proves
\[
 \boxed{1-p_H\ge\frac1H,\qquad
        1-p_H^{(0)}\ge\frac1H,\qquad
        1-p_H^{(1)}\ge\frac1H.}                           \tag{6}
\]
These are all-depth kernel results, not extrapolations from finite data.

Balanced coalescence persists with time and is periodic in the initial
input modulo \(2^H\); both statements are also kernel proved. On the
probability space of independent fair binary input bits, let \(T\) be
the first balanced-coalescence depth, allowing \(T=\infty\). Then
\(\Pr(T>H)=1-p_H\), and the tail-sum formula gives
\[
 \mathbb E T=\infty.                                    \tag{7}
\]
The same holds conditioned on either first bit. This is a statement
about the coherent full-period probability laws, not a probability
distribution uniformly sampling all positive integers. It does not
assert that \(T=\infty\) has positive probability, nor that a specific
positive integer fails to reach the known cycle. A limit \(p_H\to1\)
is compatible with (6) and (7); no such limit is proved or adopted here.

## 3. A stronger written random-walk comparison

Condition on either initial parity and orient the first gap to be +1.
Until its first zero, its absolute gap either holds or takes a symmetric
unit step. Whether the next step is active is determined before the
next input bit is revealed.

One can generate the input bits using two independent stacks of fair
coins: use a coin from the first stack at an active step, orienting that
input bit to give the chosen increment; use a coin from the second
stack at a holding step. Every new input bit is conditionally fair, so
this constructs exactly the original input law. The active increments
are the successive increments of one simple symmetric walk. At most
\(H-1\) of them have been used by depth \(H\). If that walk, started
at 1, stays positive for all of its first \(H-1\) steps, the stopped
gap must still be positive at depth \(H\).

For a simple walk started at 1, the reflection bijection shows that the
number of length-\(t\) paths staying positive is
\(\binom{t}{\lfloor t/2\rfloor}\). Explicitly, the count ending at
each positive reachable \(j\) is
\(\binom{t}{(t+j-1)/2}-\binom{t}{(t+j+1)/2}\); summing over \(j\)
telescopes. Therefore the written comparison yields
\[
 1-p_H^{(e)}\ \ge\ \Pr(G_H>0\mid e)
 \ \ge\ \frac{\binom{H-1}{\lfloor(H-1)/2\rfloor}}{2^{H-1}},
 \qquad e=0,1.                                          \tag{8}
\]
It also holds without conditioning. This bound is of order
\(H^{-1/2}\). The coupling, reflection count, and asymptotic comparison
are written arguments; the Lean module proves the weaker but sufficient
harmonic bound directly through integer sums.

## 4. The proposed dyadic route to zero escape mass

Let \(w(n)=W_\infty(n)\) be the infinite remaining weight from the
earlier note, and put \(f(n)=w(n)/n\). These exact identities follow
from its cocycle and the shortcut affine factors:
\[
 w(2n)=w(n),\qquad
 f(n)=\frac{3^{w_H(n)}}{2^H}f(U^H(n)).                    \tag{9}
\]
Here the subscripted \(w_H\) denotes the odd count; the unsubscripted
\(w\) denotes infinite remaining weight. Thus balanced-coalescent
starts have equal \(f\)-values. This consequence of the earlier weight
identity is written, not a new theorem in the Lean tail module.

For \(1\le x<2\), define the dyadic step functions
\[
 h_k(x)=2^k f(\lfloor2^kx\rfloor),\qquad 0\le h_k\le1.
\]
On the even half of each parent cell, \(h_{k+1}=h_k\) exactly by
\(f(2n)=f(n)/2\). On its odd half the same equality holds whenever
\(2n,2n+1\) eventually coalesce in the balanced sense.

Let \(B_k\) be the fraction of \(2^k\le n<2^{k+1}\) for which
that even adjacent pair never becomes balanced-coalescent. The measure
of \(\{h_{k+1}\ne h_k\}\) is at most \(B_k/2\). If
\[
 \sum_k B_k<\infty,                                    \tag{10}
\]
Borel--Cantelli makes \(h_k(x)\) eventually exactly constant for almost
every \(x\). Its limit then has countable range, since every \(h_k\)
has finite range.

Assume, as in the preceding conditional weighted-density argument, that
\(X^{-1}\sum_{n\le X}w(n)\to d\). Partial summation gives, for every
\(1\le a<b\le2\),
\[
 \int_a^b h_k(x)\,dx\longrightarrow d\log(b/a).
\]
The endpoint-cell errors tend to zero. Bounded convergence under (10)
therefore identifies the almost-everywhere limit with \(d/x\).
If \(d>0\), the inverse image under \(d/x\) of any countable set
has measure zero, contradicting the countable range. Hence
\[
 \boxed{\text{existence of the mean and (10) imply }d=0.} \tag{11}
\]
More generally it suffices that the actual measures
\(\lvert\{h_{k+1}\ne h_k\}\rvert\) are summable. No such
summability has been established. Even \(d=0\) would leave exclusion
of additional cycles before full Collatz, as the preceding note explains.

For any depth \(1\le H\le k+1\), the even inputs \(2n\) in this
dyadic source interval run through an exact number of periods modulo
\(2^H\). Thus the immediate finite-depth certificate is only
\[
 B_k\le1-p_H^{(0)}.
\]
Every one of these upper-bound values is at least \(1/H\ge1/(k+1)\)
by (6). Choosing such a depth for each \(k\) cannot make the resulting
upper bounds summable. A depth beyond \(k+1\) requires control of a
proper subinterval of its residue period, the issue identified in the
[earlier source-interval audit](PREFIX-COALESCENCE-AUDIT.md).

This is a limitation of those **upper-bound certificates**. It is not
a proof that \(B_k\ge1/(k+1)\), that (10) is false, or that the actual
weight changes have a nonsummable total measure. Many finite-depth
unmerged pairs can merge later, and unequal components can still have
equal zero infinite weights.

## 5. Verification and the next unresolved estimate

[`CoalescenceTail.lean`](../lean/CoalescenceTail.lean) imports the local
affine module. Twenty-three main roots are audited, including both
all-depth integer mass identities, the harmonic bounds, periodicity,
and persistence. The module uses no native evaluation, admitted proof,
or added axiom. Its printed dependencies are standard logical axioms.

[`verify_coalescence_tail.py`](../verify_coalescence_tail.py) builds both
modules afresh, enumerates the exact residue tree through depth 20, and
compares independent direct integer trajectories and nonzero quotient
lifts. It checks both parity halves separately, verifies the local mass
identities, and compares balanced counts with the preceding independent
enumeration. It also checks the numerical inequality in (8); that finite
check is not the proof of the written all-depth comparison.

The [verification record](../results/coalescence-tail/verification.json)
separates these scopes. Reproduce with:

```sh
python3 verify_coalescence_tail.py
```

The next useful estimate must concern the actual infinite-weight changes
or their finite-clock substitutes on the actual source interval. The
full-period noncoalescence count alone cannot justify the summability
used in (11). The original target remains proving the escape mass zero
and excluding other cycles, or constructing a rigorously verified
positive-integer counterexample.
