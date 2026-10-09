# Coalescence grades and a conditional odd/even rank

**Collatz remains unresolved.** This note makes the earlier merging
obstruction explicit and proves that either of two relaxations retains
an exact criterion for the full conjecture. A separate integer rank gives
a finite hitting-time bound whenever the excess of odd over even steps
has a finite bound. The existence of that bound for every start is still
unproved; it is equivalent to the full conjecture, including the exclusion
of nontrivial positive cycles.

All displayed finite and equivalence claims below are kernel checked in
[CoalescenceGrades.lean](../lean/CoalescenceGrades.lean), except where
explicitly identified as an algebraic interpretation or Python replay.
The module imports the existing ordinary/shortcut bridge and
[equal-weight fibre results](EQUAL-WEIGHT-FIBRES.md). No novelty is claimed.

## 1. Arrival grade and arbitrary physical meetings

Write \(x_k=U^k(n)\) for the shortcut orbit and \(w_k(n)\) for its odd-step
count. If \(U^T(n)=1\), define the integer arrival grade
\[
 d(n)=T-2w_T(n).
\]
Another arrival at one adds two steps and one odd step, leaving the grade
unchanged. The kernel uses equations of natural numbers to avoid
truncated subtraction. Its core identity is
\[
 k+U^k(x)=2w_k(x)+x\qquad(x\in\{1,2\}).                 \tag{1}
\]
If convergent starts \(n,m\) physically meet at possibly different clocks,
\(U^a(n)=U^b(m)\), then
\[
 \boxed{d(n)-d(m)=a-b-2\bigl(w_a(n)-w_b(m)\bigr).}       \tag{2}
\]
The proof appends the same sufficiently long continuation to the common
state and applies (1). It does not assume that the meeting is itself at
one. In Lean, `meeting_grade_balance` is the equivalent equation with all
negative terms moved to the other side.

Consequently, two convergent starts have an equal-time, equal-weight
meeting at some time **if and only if** their arrival grades agree. The
converse compares both paths after they have entered \(\{1,2\}\). Equal
grades then force both their states and their odd counts to agree, since
the states can differ by at most one whereas an odd-count difference
contributes an even integer. This upgrades the earlier written
classification to a kernel theorem.

## 2. Explicit minimal representatives

The elementary envelope
\[
 2^k U^k(n)\le 2^{2w_k(n)}n\qquad(n>0)                  \tag{3}
\]
follows from \(U(n)\le2n\) on odd inputs and exact halving on even inputs.
If an arrival has nonnegative grade \(a\), then
\[
 T=2w_T(n)+a\quad\Longrightarrow\quad 2^a\le n.          \tag{4}
\]
The start \(2^a\) reaches one after \(a\) halvings, with grade \(a\).
Thus the minimum convergent representative of every nonnegative grade
is **exactly \(2^a\)**. In particular, for every \(a,k\ge0\),
\[
 U^k(m)=U^k(2^a),\quad w_k(m)=w_k(2^a),\quad m>0
 \quad\Longrightarrow\quad m\ge2^a.                     \tag{5}
\]
For (5), the kernel extends a putative meeting to an arrival at one and
applies (4). No convergence assumption about an unrelated start is needed.
This supplies explicit unbounded witnesses to the failure of induction
through a smaller equal-time, equal-weight mate. Increasing a finite base
does not repair that restricted induction.

## 3. Either freedom restores a full criterion

The following statements are each equivalent to the positive-integer
Collatz conjecture:

1. Every \(n>2\) has some \(0<m<n\) and a common clock \(k\) such that
   \(U^k(n)=U^k(m)\), with no condition on odd counts.
2. Every \(n>1\) has some \(0<m<n\) and clocks \(a,b\) such that
   \(U^a(n)=U^b(m)\) and \(w_a(n)=w_b(m)\).

In the first forward implication, a convergent start can use partner one
or two according to the phase of its arrival clock. The base includes two
because one and two never meet at the same clock. In the second, an
arrival at one with \(j\) odd steps can use partner one at clock \(2j\).
Both reverse implications use strong induction and transfer convergence
through the physical meeting. These are equivalences, not constructions
of the required meetings before convergence is known.

The start 27 quantifies the necessary freedom in a small case. Its grade
is \(-12\), while every positive start below it has nonnegative grade.
Equation (2) therefore gives, for all clocks and every \(0<m<27\),
\[
 U^k(27)=U^k(m)\ \Longrightarrow\ w_k(27)\ge w_k(m)+6,    \tag{6}
\]
\[
 U^a(27)=U^b(m),\ w_a(27)=w_b(m)\ \Longrightarrow\ b\ge a+12.\tag{7}
\]
Both bounds are sharp: 27 and one meet at clock 70 with odd counts 41
and 35; alternatively, clocks 70 and 82 give both odd count 41. The
complete small-grade table and these witnesses use kernel reduction;
the all-time extension uses (2).

## 4. A conditional integer rank

Let \(A\ge0\) be an integer. Say a prefix has credit \(A\) if
\[
 2w_i(n)\le i+A                                         \tag{8}
\]
at every index in that prefix. Since \(i-w_i\) counts even steps, (8)
means that odd steps never outnumber even steps by more than \(A\).
At time \(i\), its remaining credit is the nonnegative integer
\(g_i=A+i-2w_i(n)\). Define
\[
 \boxed{R(x,g)=2^{g+1}(x-1)+g.}                           \tag{9}
\]
Before reaching one, each step that retains nonnegative credit strictly
decreases this natural-number rank. An even step sends \((x,g)\) to
\((x/2,g+1)\), with rank drop
\[
 2^{g+1}-1\ge1.
\]
An odd step has \(x\ge3\) and \(g\ge1\), and sends the pair to
\(((3x+1)/2,g-1)\), with rank drop
\[
 2^{g-1}(x-3)+1\ge1.
\]
These displayed differences are the algebraic interpretation of the two
kernel inequalities `credit_even_decreases` and `credit_odd_decreases`.
Induction on the prefix length proves the termination bound
\[
 \boxed{\bigl[\forall i,\ 2w_i(n)\le i+A\bigr]
 \ \Longrightarrow\ \exists t\le2^{A+1}(n-1)+A:\ U^t(n)=1.} \tag{10}
\]
Only a finite check of (8) through \(R(n,A)+1\) is needed for the same
conclusion. Conversely, a certified arrival at time \(T\) implies (8)
for every index with \(A=T+1\): use \(w_i\le i\) before arrival and
(1) after it. Hence
\[
 \boxed{n\text{ reaches one}\quad\Longleftrightarrow\quad
        \exists A\ge0\ \forall i:\ 2w_i(n)\le i+A.}       \tag{11}
\]
In particular, any hypothetical nonconvergent positive start would,
for **each** proposed \(A\), have a witness
\[
 \exists k\le R(n,A)+1:\quad 2w_k(n)>k+A.                 \tag{12}
\]
This handles both eventual nontrivial cycles and divergent trajectories.
It does not depend on the analytic packing or reciprocal-summability
arguments used in the earlier divergence-only coefficient criterion.

A single credit for all starting numbers is impossible. The source
\(2^Kq-1\), \(q>0\), has \(K\) initial odd steps, so any credit valid
through those steps must be at least \(K\). The kernel checks this entire
family. No universal bound on \(A\) as a function of \(n\) is asserted.
Choosing \(A=T+1\) after obtaining a convergence certificate proves the
reverse implication of (11); it cannot supply the missing forward proof
for arbitrary starts.

## 5. Reproduction and remaining work

Run `python3 verify_coalescence_grades.py`. It builds the six dependency
modules sequentially in a fresh temporary directory and rejects warnings,
admitted proofs, and native-decision axioms. Independent Python checks
replay the rank, labels, finite meeting partitions, sharp witnesses, and
all-odd families. The manifest and replay report exact finite scopes:
[verification](../results/coalescence-grades/verification.json),
[replay](../results/coalescence-grades/replay.json).

The unresolved step is to bound the odd/even excess for every individual
positive orbit, or to construct one orbit whose excess is unbounded.
The new rank verifies the consequence of such a bound; it does not prove
the bound. No nontrivial positive cycle or divergent positive start is
excluded by these equivalences alone.
