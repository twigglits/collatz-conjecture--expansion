# Minimum-root predecessors and their height limitation

Reversing an admissible run of odd shortcut steps from an actual minimum
root gives another actual minimum root. Combining this fact with the
least-counterexample condition imposes exact ternary divisibility
restrictions on the sequence of attained tail minima.

There is also a limitation: once a target is sufficiently large compared
with the original source, none of these all-odd inverse words can produce
a smaller predecessor. This height barrier is proved in the kernel,
so extending this particular inverse family alone cannot exclude an
escaping tail.

The [new Lean module](../lean/MinimumRootPredecessors.lean) contains
21 audited theorem roots. Its finite example has no axioms and uses
kernel computation. The general statements use only standard logical
axioms and the earlier local modules. **Collatz remains unresolved.**
No external theorem is a premise of the new proofs, and no novelty
claim is made.

## 1. Exact inverse transport of a minimum

Use the ordinary map \(C\), the attained global minimum \(m(n)\), and
the finite prefix minimum \(m_T(n)\) from the
[minimum-root note](MINIMUM-ROOT-SPINE.md).

For every \(t,n\), **kernel**,
\[
 m(n)=\min\{m_t(n),m(C^t n)\}.
 \tag{1}
\]
For \(k\ge0,\ q\ge1\), the previously proved odd block has endpoints
\[
 a=2^kq-1,\qquad b=3^kq-1,\qquad C^{2k}(a)=b,
\]
and its prefix minimum is \(a\). Consequently the new module proves
both
\[
 m_{2k+t}(a)=\min\{a,m_t(b)\},
 \qquad
 m(a)=\min\{a,m(b)\}.
 \tag{2}
\]
These are distinct finite and global identities.

Since \(a\le b\), (2) gives
\[
 \boxed{\quad m(3^kq-1)=3^kq-1
 \ \Longrightarrow\
 m(2^kq-1)=2^kq-1.\quad}
 \tag{3}
\]
The target-root hypothesis is essential. In particular, (3) does not
declare a Mersenne start to be a global minimum root merely because
its initial block grows.

## 2. A forced parent and a genuine additional branch

Write \(\sigma(a)=m(Ca)\). If \(b=3q+2\) is a minimum root, its smaller
odd parent is
\[
 p=2q+1,\qquad C^2(p)=b.
\]
The module proves
\[
 m(p)=p,\qquad \sigma(p)=b.
 \tag{4}
\]
It is the smallest possible root parent: every positive root \(a\)
with \(\sigma(a)=b\) satisfies \(p\le a\), by
\(2b\le3a+1\).

Suppose \(a_j,a_{j+1}\) are consecutive roots on a nonrepeating orbit,
and \(a_{j+1}=3q+2\). If \(p<a_j\), the kernel proves that \(p\) is
absent from the **entire original orbit**, not only from its root
sequence. It is an additional minimum root feeding into the same
later root.

The temporal argument matters. If \(p\) occurred before \(a_j\), every
state after its first step would be at least \(a_{j+1}>a_j\). If it
occurred after \(a_j\), self-minimality of \(a_j\) would forbid
\(p<a_j\). Either ordering is impossible.

This produces an additional root when the inequality is strict; it
does not automatically produce an exponentially branching collection.
It also need not produce a positive-density predecessor basin:
\[
 \boxed{\quad 3\mid p\quad\Longleftrightarrow\quad b\equiv5\pmod9.\quad}
 \tag{5}
\]
Equation (5) is kernel checked here. The existing
[inverse-basin proof](../lean/InverseBasinAudit.lean) shows that a target
divisible by three has only its doubling ray as predecessors. That ray
has natural density zero, by the elementary written count
\(O(\log X)\) up to \(X\).
Thus counting these forced roots does not by itself supply the missing
positive branch-density increment.

## 3. Minimality holds throughout the whole component

Let \(A\) be a least positive counterexample. If a positive \(p\) meets
any point on its forward orbit, then
\[
 C^s(p)=C^t(A)\quad\Longrightarrow\quad A\le p.
 \tag{6}
\]
This is **kernel**. If \(p<A\), leastness makes \(p\) converge;
convergence then transfers through the meeting point back to \(A\).

In particular, whenever \(j\ge1,\ q\ge1\) and
\[
 C^t(A)=3^j q-1,
\]
the actual odd-block predecessor \(2^j q-1\) must satisfy
\[
 \boxed{\quad A+1\le2^j q.\quad}
 \tag{7}
\]
This applies to any ordinary orbit value with the indicated form,
not only to the tail-minimum sequence.

For the first successor \(b=\sigma(A)\), (4), (6), and the upper
bound \(2b\le3A+1\) imply the sharper alternative
\[
 \boxed{\quad b\equiv1\pmod3
 \quad\text{or}\quad 2b=3A+1.\quad}
 \tag{8}
\]
Indeed, a successor cannot be divisible by three. If it is two modulo
three, its contracting parent is at most \(A\), while (6) makes it at
least \(A\). It is therefore exactly \(A\).
In particular, strict inequality \(2b<3A+1\) forces \(b\equiv1\pmod3\).

## 4. Ternary restrictions along the root sequence

Let \(a_0=m(A)=A\), \(a_{k+1}=\sigma(a_k)\). The earlier kernel bound is
\[
 2^k(a_k+1)\le3^k(A+1).
 \tag{9}
\]
The new conclusion, for every \(k\ge0\), is
\[
 \boxed{\quad 3^{k+1}\nmid a_k+1.\quad}
 \tag{10}
\]
Equivalently, the ternary valuation of \(a_k+1\) is at most \(k\).
Lean states (10) as nondivisibility; the valuation terminology is its
elementary written interpretation.

If \(a_k+1=3^{k+1}q\), (7) would give
\(A+1\le2^{k+1}q\). Substituting in (9) would yield
\[
 2^k3^{k+1}q\le3^k2^{k+1}q,
\]
which is impossible because \(q>0\). This is the complete kernel
argument; no distribution of ternary digits is assumed.

The borderline case is rigid. For \(k\ge1\), if \(3^k\mid a_k+1\),
the kernel supplies a positive integer \(q\) such that
\[
 A=2^kq-1,\qquad a_k=3^kq-1,\qquad C^{2k}(A)=a_k.
 \tag{11}
\]
Thus \(2^k\mid A+1\), and an actual block of \(k\) odd shortcut steps
reaches this root. The inequalities in (7) and (9) force equality.

Equation (11) gives an explicit attainment clock \(2k\); it does not
evaluate the arbitrary noncomputable clock chosen in the earlier
root-sequence definition. For large \(k\), even (10) becomes automatic
from (9): if \(2^k>A+1\), then \(a_k+1<3^k\).
The restriction therefore must not be mistaken for an exclusion of an
arbitrarily long root sequence.

## 5. A kernel height barrier for this inverse family

For all natural \(d,j\) and positive \(q\), the kernel proves
\[
 3^d\le3^j q\quad\Longrightarrow\quad2^d\le2^j q.
 \tag{12}
\]
If \(j\ge d\), this follows from \(q\ge1\). Otherwise
\(q\ge3^{d-j}\ge2^{d-j}\).

Choose \(d\) with \(A<2^d\). Every target \(b=3^j q-1\) with
\(b+1\ge3^d\) then has
\[
 2^j q-1\ge A.
 \tag{13}
\]
Thus **every all-odd inverse ancestor already passes the leastness
test** above that target height. Increasing the length \(j\) does not
remove this obstruction.

Taking the least such \(d\), the threshold \(3^d\) is within a factor
three of \((A+1)^{\log_2 3}\). This real-power comparison is written;
(12)–(13) are integer kernel statements.
To obtain a contradiction from ancestry at larger targets, this route
would need mixed parity inverse words or some additional constraint.

## 6. A finite example, with convergence proved separately

On the actual orbit from \(27\),
\[
 C^{26}(27)=155,\qquad C^{44}(27)=167.
\]
With the terminal horizon fixed at \(64\), the suffix minima at clocks
26 and 27 are respectively 155 and 167. The contracting parent of 167
is 111:
\[
 111\longrightarrow334\longrightarrow167.
\]
The kernel checks that 111 is absent from the first 65 states of the
orbit from 27. It is smaller than 155, lies outside that finite path,
and is divisible by three, illustrating both branch observations above.

These are **finite suffix minima**, not global roots.
The same axiom-free kernel theorem proves that 155, 167, and 111 reach
one at ordinary clocks 85, 67, and 69. Python separately checks that
these are their first arrivals. No infinite-root hypothesis is inferred
from this finite example.

## 7. Checks on the other proposed routes

The preceding root-count bound does not close the earlier
[branch-density criterion](DENSITY-BRANCH-LEAKAGE.md). That note already
shows that unused predecessor branches can have positive but summable
density along a hypothetical divergent orbit. The extra forced parent
in Section 2 may even have density zero.

The new count over **all** minimum roots is broader than a bound on
one orbit. Its exponent \(\log_2(29/15)\), however, does not improve the
older [per-orbit packing exponent](ORBIT-PACKING-BOOTSTRAP.md)
\(H_2(\log_3 2)\). In particular the root-index power corollary in the
previous note is not the strongest existing per-orbit growth restriction.

The [external masked-energy review](LOCAL-OBSTRUCTION-REPO-REVIEW.md)
was also revisited. A target count bounded by a power of \(N\), even
with exponent below one, gives an exponential bound when the target
cutoff is \(N=3^K\). It does not give the required \(o(K)\) energy bound.
The unresolved energy remains on actual forward orbits of small seeds;
sparsity of the attained minima does not bound its amplitude or arrival
clocks. The external checkout was read only, remained clean, and was
still at commit a7275d5a73814d3d9a400c6fe6577de9542b03a3. No fresh
external Lean replay or new external proof premise is claimed.

A primary-source recheck of the
[2026 Wirsching-program preprint](https://arxiv.org/html/2608.27617)
found that it still explicitly leaves condition star3, and its proposed
Conjecture 2 bridge, open. Its averaged operator estimates do not supply
the required residue-level comparison. The paper was reviewed for this
scope distinction only; none of its new claims is imported into the
kernel proofs here.

## 8. Verification and next requirement

Run python3 verify_minimum_root_predecessors.py using the
[verifier](../verify_minimum_root_predecessors.py).
It authenticates the 48 hashes of the preceding root-spine manifest,
then freshly builds all 23 Lean modules sequentially and audits
all 21 new theorem roots. The finite branch witness is axiom-free.

Independent replay checks exact all-odd transport over a complete stated
parameter rectangle, with additional blocks through depth 1,024; simple
finite paths from every source through 8,192 and two independent suffix-
record selections; the integer saturation and height-barrier inequalities;
and all three kernel convergence witnesses. Larger-index arithmetic
checks are not large source censuses. The least-counterexample
hypotheses are never instantiated numerically.

The [manifest](../results/minimum-root-predecessors/verification.json)
and [replay](../results/minimum-root-predecessors/replay.json) record
the exact counts, hashes, compiler version, and scopes.

The full run completed at 2026-10-14T21:38:59.046171Z: 23 fresh builds
took 10.929 seconds, all 21 new roots passed, and 50 files were hashed.
Python checked 4,243 odd-block source pairs and 33,944 finite transport
identities, including 10,428 conditional finite ancestry cases. The
8,192-source branch census used 636,520 ordinary steps and 49,152
independent suffix-record comparisons. It checked 56,014 contracting
parents; 3,368 were strictly outside the stated finite paths, representing
235 distinct triples. Of those 3,368 instances, 2,118 parents were
divisible by three. These are finite repeated observations, not density
estimates. Separate exact arithmetic checked 49,532 saturation cases,
49,536 next-power exclusions, and 41,538 height-barrier comparisons.
All three kernel convergence witnesses were independently replayed over
221 ordinary steps.

The next ancestry step needs mixed parity words that remain effective
above the barrier (13), or an actual relative branch estimate that
cannot be summable. No such bound, universal cap budget, exclusion of
all cycles, or complete Collatz proof is established here.
