# Equal-weight merging and a necessary stabilization under divergence

**Collatz remains unresolved.** Two exact affine envelopes now give a
uniform bound on a fixed-time, fixed-odd-count inverse fibre. Combined
with the established written reciprocal-summability argument, they show
that a divergent orbit can acquire only finitely many equal-weight
merging starts. No argument forcing infinitely many such starts is proved.

The finite envelopes, counting bound, nesting, and conditional
stabilization are kernel checked in
[EqualWeightFibres.lean](../lean/EqualWeightFibres.lean). The deduction
from a divergent trajectory uses written real analysis. No novelty is
claimed.

## 1. Shift the affine origin to minus one

Use the shortcut map \(U\), and write
\[
 x_k=U^k(n),\qquad j=w_k(n),\qquad e=k-j,
\]
where \(j\) and \(e\) count odd and even steps. Then
\[
 \boxed{3^j(n+1)\le2^kx_k+2^j,}                             \tag{1}
\]
\[
 \boxed{2^k(x_k+1)\le3^j(n+2^e).}                          \tag{2}
\]
Both hold for every natural start and every finite time, including
prefixes containing repetitions. In particular they give the weaker
lower bound \(3^j(n+1)\le2^k(x_k+1)\).

The shift is useful because an odd step satisfies
\(U(n)+1=3(n+1)/2\) exactly. Reversing an odd step multiplies the
shifted value by \(2/3\); reversing an even step sends it to twice
itself minus one. If \(y=x_k\), the reverse identity is
\[
 n+1=\frac{2^k}{3^j}(y+1)-D,
 \qquad
 (2/3)^j(2^e-1)\le D\le2^e-1.                            \tag{3}
\]
Each of the \(e\) subtractive terms is multiplied by a power of two
from the later reverse-even steps and by between zero and \(j\)
factors \(2/3\). The powers of two sum to \(2^e-1\), proving
the stated bounds. Equations (1)–(2) are the integer versions of (3);
the Lean proof establishes them directly by induction, with no real
arithmetic or division by a variable.

For fixed \(k,j,y\), all possible sources consequently lie in an
interval of width
\[
 (1-(2/3)^j)(2^e-1)<2^e.                                  \tag{4}
\]
They are distinct integers, so their number satisfies
\[
 \boxed{N_{k,j}(y):=\#\{n\ge1:U^k(n)=y,\ w_k(n)=j\}
                    \le2^{k-j}.}                         \tag{5}
\]
The kernel counts any finite list of distinct sources; all sources form
a finite set since each state has at most two predecessors. The same
bound also holds when zero is included.

For \(e=0\) or \(e=1\), the sharper width in (4) is less than one,
so the fibre contains at most one start. This is separately kernel
checked as `one_even_injective`. The bound depends on the number of
even steps; it does not impose a constant bound at arbitrary time.
It is compatible with the earlier
[exponential fibre multiplicity result](../APERIODIC-ATTEMPT.md#17-the-inverse-fibre-multiplicity-loss-is-exponentially-large).

## 2. An optimal exponential rate for the coefficient moment

Here is one written consequence of (5). For \(s>\log_3 2\), define
the coefficient moment, without replacing it by an actual source weight,
\[
 Z_{k,s}(y)=\sum_{\substack{n\ge1\\U^k(n)=y}}
                    (3^{w_k(n)}/2^k)^s.
\]
Putting \(e=k-j\) in (5) gives
\[
 Z_{k,s}(y)\le(3/2)^{sk}
                  \sum_{e=0}^k(2/3^s)^e
 \le\frac{(3/2)^{sk}}{1-2/3^s}.                            \tag{6}
\]
The exponential rate is sharp for a bound uniform in the target: take
\(n=2^kq-1\), \(y=3^kq-1\), with \(q\ge2\). This is an all-odd
path, and its single term is \((3/2)^{sk}\). Hence
\[
 \lim_{k\to\infty}\left(\sup_{y\ge1}Z_{k,s}(y)\right)^{1/k}
       =(3/2)^s.                                         \tag{7}
\]
The target may vary with \(k\); this is not growth at one fixed target.
For integer \(p\ge1\), the finite arithmetic form used in replay is
\[
 (3^p-2)\sum_{U^k(n)=y}3^{p w_k(n)}
       \le3^{p(k+1)}-2^{k+1}.                             \tag{8}
\]
It follows by summing a finite geometric progression. The count (5)
is kernel checked; this moment summation and its limit are written.

Neither moment is the killed weighted survivor mass. The affine
correction and the first-entry conditions still have to be retained
before using a source weight such as \(n^{-s}\). In particular, (6)
is not a contraction estimate.

## 3. Equal-weight fibres along one forward trajectory

For a fixed positive \(n\), define
\[
 F_k(n)=\{m\ge1:U^k(m)=U^k(n),\ w_k(m)=w_k(n)\}.
\]
These sets are nested: once the states and accumulated odd counts agree,
both trajectories have identical future increments. The kernel proves
this for every additional number of steps as `mate_persists`.

Equation (1) gives the explicit complete-search cap
\[
 m\in F_k(n)\quad\Longrightarrow\quad
 m\le\left\lfloor
       \frac{2^kU^k(n)+2^{w_k(n)}}{3^{w_k(n)}}
       \right\rfloor-1.                                  \tag{9}
\]
The subtraction is valid for a nonempty positive fibre. The undivided
integer inequality is `mate_endpoint_cap` in Lean.

More generally, suppose an integer \(M\) satisfies
\[
 2^k(U^k(n)+1)\le3^{w_k(n)}(M+1)\quad\hbox{for every }k.     \tag{10}
\]
Then every member of every \(F_k(n)\) is at most \(M\). A nested
family of subsets of a fixed finite interval eventually stabilizes:
\[
 \exists K\ \forall k\ge K:\quad F_k(n)=F_K(n).             \tag{11}
\]
Both the implication from (10) and this finite-set argument are kernel
checked. The Lean module does not assert (10) for an arbitrary start.

## 4. Why divergence would supply that bound

Suppose the orbit of \(n\) never repeats. Its distinct integer states
tend to infinity. The written
[packing argument](FINITE-PATH-PACKING.md) implies
\(\sum_i1/x_i<\infty\). With
\[
 C_k=3^{w_k(n)}/2^k,\qquad
 P_k=\prod_{\substack{i<k\\x_i\text{ odd}}}
                       (1+1/(3x_i)),
\]
the exact identity is \(x_k=nC_kP_k\). The product increases to a
finite positive \(P_\infty\), and therefore \(C_k\to\infty\).
Consequently
\[
 B_k:=\frac{x_k+1}{C_k}
       =nP_k+\frac1{C_k}\longrightarrow nP_\infty=:L<\infty. \tag{12}
\]
The shifted step identity also shows that \(B_k\) is nondecreasing:
it is unchanged on an odd step, and increases by \(1/C_k\) on an
even step. Thus \(B_k\le L\) for every \(k\). Choosing an integer
\(M\) with \(L\le M+1\) supplies (10).

We have proved the written necessary condition
\[
 \boxed{\text{a divergent trajectory has an eventually constant}
        \text{ equal-weight fibre }F_k(n).}                \tag{13}
\]
The finite cap depends on the trajectory's limiting correction. It is
not a computable universal time bound. Conversely, proving that the
fibres grow without bound for every positive start would exclude
divergence. No such growth theorem is established here. The maximal
fibre lower bound from the earlier work cannot be substituted: its
target and weight are chosen separately at each depth, whereas (13)
concerns the target and weight of this one trajectory.

For the coefficient route, (12) also gives an exact distinction. Since
\(C_k\to\infty\), it has a global minimum at a finite time \(K\).
Starting at \(x_K\), every coefficient prefix is
\(C_{K+t}/C_K\ge1\). Conversely, a positive orbit whose every
coefficient prefix is at least one cannot eventually cycle: a positive
cycle has coefficient product strictly below one, by multiplying its
positive affine correction factors, and repeating it would send the
cumulative coefficient to zero. A bounded integer orbit eventually
cycles. Therefore
\[
 \text{a divergent orbit exists}\quad\Longleftrightarrow\quad
 \exists n\ge1\ \forall k:\ 3^{w_k(n)}\ge2^k.              \tag{14}
\]
This deduction uses reciprocal summability for the forward implication.
It is not a proof of the universal coefficient-stopping statement.
Even that statement, if established, would leave nontrivial positive
cycles to exclude. These distinctions prevent the coefficient route
from being reported as a proof of the full conjecture.

## 5. A complete finite plateau, followed by a new merge

The kernel proves the exact identities
\[
 F_{34}(1)=\{1\},\qquad F_{35}(1)=\{1,159\}.                \tag{15}
\]
Nesting makes \(F_k(1)=\{1\}\) for every \(0\le k\le34\).
At time 35 both 1 and 159 are at 2 with odd count 18. At time 34,
the complete cap (9) is 132; at time 35 it is 176. The kernel checks
every integer in these ranges, then uses (9) to exclude every larger
source. Thus (15) is not a search restricted to an arbitrary cutoff.
The witness 159 reaches one at time 36; it is not a counterexample.

This finite example explains why a long interval with no new members
does not certify the eventual stabilization in (13). It supplies neither
a divergent trajectory nor an infinite growth proof for any fibre.

There is also an all-time obstruction to requiring a **smaller** member:
\[
 \boxed{\forall k\ge0:\quad F_k(27)\cap[1,27)=\varnothing.}  \tag{16}
\]
The kernel checks that 27 reaches one after 70 shortcut steps, and that
every positive start below it lies in \(\{1,2\}\) at time 72 with a
different state/count pair. A merge before time 72 would persist to
time 72. A merge after time 72 could be cancelled back to time 72,
because the map permutes \(\{1,2\}\) and equal future increments
cannot remove a difference in accumulated odd counts. This proves (16)
for every time, using a complete finite base and a general cancellation
lemma. Thus the stronger proposal that every start above one has a
smaller equal-time, equal-weight mate is false even among convergent
starts. The broader smaller-coalescing-start criterion permits different
times or odd counts and is unaffected.

For interpretation, a convergent start has the integer label
\(d(n)=T-2w_T(n)\), where \(U^T(n)=1\). It is independent of the
chosen arrival time: an extra circuit from 1 to 1 adds two steps and
one odd step. Two convergent starts eventually merge at equal time and
weight exactly when their labels agree. Necessity follows by appending
the same path to one; sufficiency follows by taking the later arrival
time, since equal labels force the two arrival times to have the same
parity and then the accumulated odd counts agree. This classification
is written. Here \(d(27)=-12\), while the other 26 checked labels
differ. It does not show whether any one label has infinitely many
starts, or classify hypothetical nonconvergent starts.

The smaller-mate obstruction cannot be removed by enlarging a finite
exceptional range. For each integer \(a\ge0\), the convergent start
\(2^a\) has label \(a\). Let \(m_a\) be the least convergent positive
start with that label; it exists by well-ordering. Any equal-weight mate
of \(m_a\) also converges and has the same label, so it cannot be
smaller. Distinct labels give distinct \(m_a\), hence these witnesses
are unbounded. This is a written corollary of the label classification;
it does not give an explicit formula for all \(m_a\).

[Verification and precise scope](../results/equal-weight-fibres/verification.json)
record fresh sequential Lean builds, independent envelope and complete
residue-fibre checks, exact moment checks, and the finite evolution of
selected fibres. The real limits and the divergence implications remain
written proofs. Reproduce with:

```sh
python3 verify_equal_weight_fibres.py
```
