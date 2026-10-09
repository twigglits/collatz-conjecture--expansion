# Parity restrictions on survivors and the strength of a credit bound

**Collatz remains unresolved.** The conditional credit bound from the
[previous note](COALESCENCE-GRADES.md) admits a much stronger consequence:
for \(n\le2^b\), full-orbit credit \(A\) implies a shortcut hitting time
of at most
\[
                         \boxed{4A+5b+71.}                \tag{1}
\]
Thus a logarithmic credit bound would already prove a logarithmic total
stopping-time bound. It is not a quantitatively weaker way around that
open problem. No such universal credit estimate is proved here.

The finite inequalities, the time bound, and the implications between
logarithmic bounds are kernel checked in
[ParitySurvival.lean](../lean/ParitySurvival.lean). The proof reuses the
existing kernel convergence table for starts 1 through 64, whose times
are at most 71 shortcut steps. No analytic density or external theorem
is an input.

## 1. Finite growth bounds while a floor is avoided

Write \(x_i=U^i(n)\), \(j=w_k(n)\), and assume \(n>0\).
Avoiding a floor through a prefix means \(x_i>H\) for \(0\le i<k\);
the endpoint \(x_k\) may be the first entry below that floor.

On an odd input greater than one, \(x\ge3\), hence
\(U(x)\le5x/3\). On an odd input above 64, \(x\ge65\), hence
\(U(x)\le98x/65\). Even steps halve exactly. Multiplying the
corresponding integer inequalities gives
\[
 x_i>1\ (i<k)\quad\Longrightarrow\quad
                  3^j2^kx_k\le10^j n,                   \tag{2}
\]
\[
 x_i>64\ (i<k)\quad\Longrightarrow\quad
                  65^j2^kx_k\le196^j n.                 \tag{3}
\]
The general kernel lemma accepts an odd-step bound
\(2P\,U(x)\le Qx\) and proves \(P^j2^kx_k\le Q^j n\).
It retains the actual prefix-avoidance hypothesis.

Assume \(n\le2^b\). Since \(x_k\ge1\), taking fourth powers in (2)
and fifth powers in (3), respectively, and using the exact comparisons
\[
 10^4<3^4 2^7,\qquad 196^5<65^5 2^8
\]
yields the kernel count bounds
\[
 x_i>1\ (i<k)\quad\Longrightarrow\quad
                         4k\le7w_k(n)+4b,                \tag{4}
\]
\[
 x_i>64\ (i<k)\quad\Longrightarrow\quad
                         \boxed{5k\le8w_k(n)+5b.}        \tag{5}
\]
There is no floating-point logarithm in this argument. The generic
power-comparison lemma derives \(ak\le cj+ab\) from
\(P^j2^k\le Q^j n\), \(n\le2^b\), and
\(Q^a\le P^a2^c\).

## 2. One endpoint count can certify convergence

Fix any proposed allowance \(A\ge0\), and set
\[
                       K=4A+5b+1.
\]
If just the single count at that clock satisfies
\[
                       2w_K(n)\le K+A,                  \tag{6}
\]
then the orbit must already have entered \([1,64]\) by time \(K-1\).
Otherwise (5), together with (6), would give
\[
 5K\le8w_K(n)+5b\le4K+4A+5b<K+4K,
\]
a contradiction. The certified base supplies arrival at one at most
71 steps after this entry, proving (1).

Unlike the earlier rank proof, this implication does **not** need the
credit inequality at every earlier index. An earlier violation of the
same proposed allowance does not invalidate this endpoint certificate.
An all-time credit satisfies (6), so (1) also improves the earlier
\(2^{A+1}(n-1)+A\) bound under its original hypothesis.

Failure of (6) is not evidence of nonconvergence. A convergent trajectory
may need a larger allowance at the selected clock, and any finite set of
failed proposals remains only a finite set of failed proposals.

## 3. What a counterexample would have to do

A hypothetical positive counterexample cannot visit any state at most
64, because each such state is kernel certified to reach one. Therefore
(5) holds for **every** clock on that counterexample:
\[
                  5k\le8w_k(n)+5b\qquad(k\ge0).          \tag{7}
\]
For the integer odd-step excess \(D_k=2w_k(n)-k\), this is
\[
                         D_k\ge(k-5b)/4.                 \tag{8}
\]
This is a lower bound at each clock, stronger than merely having
unbounded running maxima. For each proposed allowance \(A\), the
specific clock \(K=4A+5b+1\) would satisfy \(D_K>A\).
These statements cover both eventual nontrivial positive cycles and
divergent trajectories.

As a written consequence of the kernel inequality (7), every such
counterexample would have
\[
                    \liminf_{k\to\infty} w_k(n)/k\ge5/8. \tag{9}
\]
In particular, proving for every positive start that its lower limiting
odd frequency is less than \(5/8\) would suffice for the full conjecture.
Convergent orbits have limiting odd frequency \(1/2\) on the standard
cycle. No universal individual-orbit frequency statement is proved.
Density-one conclusions about starting numbers cannot supply it.

The explicit finite test is simpler than the limit language: if any
clock satisfies \(8w_k(n)+5b<5k\), then \(n\) reaches one. This is
`sparse_prefix_reaches` in Lean.

## 4. Logarithmic credit is equivalent to logarithmic total time

Let \(b=\lceil\log_2 n\rceil\); equivalently, use the least natural
\(b\) with \(n\le2^b\), including \(b=0\) for \(n=1\).
Suppose a proposed uniform estimate supplies full-orbit credit
\(A\le Cb+D\). Then the kernel gives a hitting certificate with
\[
                         T\le(4C+5)b+(4D+71).            \tag{10}
\]
Conversely, a hitting certificate with \(T\le Cb+D\) supplies full-orbit
credit \(A=T+1\le Cb+(D+1)\), using the previous module's core identity.
Consequently the existence of uniform constants in an \(O(\log n)\)
credit bound is equivalent to the existence of uniform constants in an
\(O(\log n)\) total stopping-time bound. The asymptotic terminology is
a written interpretation of the two exact kernel implications.

The same caution applies to fitting credits from a finite census. Such
a fit proposes a strong uniform time estimate; it does not prove one.
The ordinary conjecture asks only for finite convergence of each source
and does not itself supply these quantitative constants.

## 5. Verification and the remaining target

Run `python3 verify_parity_survival.py`. It performs fresh sequential
Lean builds, replays complete finite residue windows, checks both
integer growth envelopes and their parity bounds on surviving prefixes,
and tests the endpoint certificate separately from all-prefix credit.
Large all-odd examples retain unbounded initial excess and are not
misclassified as counterexamples. The exact finite scopes are in the
[verification manifest](../results/parity-survival/verification.json)
and [replay](../results/parity-survival/replay.json).

The useful missing input is now explicit: an individual-orbit parity
estimate that crosses the threshold in (7), or another proof yielding
finite credit without already assuming a hitting-time bound. Neither
the finite checks nor the kernel implications provide that input.
