# Finite clocks and the density carried by an escaping component

**Status: finite inverse-fibre bounds are kernel checked; the limiting
density arguments below are written deductions from the earlier written
first-passage results and the independently replayed external predecessor
theorem. Collatz remains unresolved.** No novelty claim is made.

The [uniform predecessor approximation](UNIFORM-PREDECESSOR-APPROXIMATION.md)
controls all targets, including moving targets, but uses **eventual** hits.
It does not supply a finite simulation time. This note gives an arithmetic
lower bound on a useful clock and identifies the exact obstruction to
truncating those infinite trajectories.

Write
\[
 R_X(a)=\frac1X\#\{1\le n\le X:\exists t\ge0, C^t(n)=a\},\qquad
 R_{X,T}(a)=\frac1X\#\{1\le n\le X:\exists t\le T, C^t(n)=a\},
\]
for positive integer \(X\), nonnegative integer \(T\), and positive
target \(a\). These count each source once, even on a cycle. The earlier
written result supplies \(r_a\) and
\[
 \delta_X=\sup_{a\ge1}|R_X(a)-r_a|\longrightarrow0.       \tag{1}
\]
Define the time-truncation defect
\[
             \Delta_X(T)=\sup_{a\ge1}(R_X(a)-R_{X,T}(a)). \tag{2}
\]

## 1. Actual congruences give a twelve-step fibre bound

The ordinary map has the exact two-step inverse description
\[
 \{n\ge0:C^2(n)=a\}=\{4a\}\ \cup
 \begin{cases}
 \{(2a-1)/3\},&a\equiv2\pmod3,\\
 \{2(a-1)/3\},&a\equiv4\pmod6,\\
 \varnothing,&\text{otherwise}.
 \end{cases}                                            \tag{3}
\]
The two optional cases are mutually exclusive. For positive targets all
listed sources are positive. Thus a two-step fibre has at most two elements.

Let \(f_k(a)\) be the length of the recursively enumerated \(2k\)-step
inverse list. Its recursion is obtained by applying (3) at the target.
The kernel proves that the list contains exactly the sources satisfying
\(C^{2k}(n)=a\), and that
\[
 f_k(a+2\cdot3^k q)=f_k(a),\qquad f_k(a)\le2^k.          \tag{4}
\]
The period concerns **inverse-fibre counts**, not forward trajectories.
At a recursive step the primary inverse branch shifts by
\(2\cdot3^{k-1}(12q)\); the optional branch shifts by
\(2\cdot3^{k-1}(2q)\). This proves (4) by induction.

Kernel evaluation of all 1458 residues gives
\[
                  f_6(a)\le38\quad\text{for every }a.   \tag{5}
\]
The target 364 has 38 distinct twelve-step predecessors. Its list length
and lack of duplicates are also kernel checked, so the bound is attained.
These finite computations use `decide`, not `native_decide`.
Composition and the two-step bound give the all-depth kernel theorem
\[
 \#\{n:C^{2k}(n)=a\}
          \le 2^{k\bmod6}38^{\lfloor k/6\rfloor}.        \tag{6}
\]
The formal cardinality statement applies to every finite list of distinct
sources in the fibre, and the inverse list supplies a finite cover.

For odd times, add the at-most-two ordinary predecessors of the target.
Consequently, for \(j=12q+s\), \(0\le s<12\),
\[
 \#\{n:C^j(n)=a\}\le 2^{\lceil s/2\rceil}38^q.
\]
Taking a union over times and using
\(\sum_{s=0}^{11}2^{\lceil s/2\rceil}=189\) yields the written bound
\[
 \begin{aligned}
 \#\{n:\exists j\le T, C^j(n)=a\}
 &\le189\sum_{q=0}^{\lfloor T/12\rfloor}38^q\\
 &<195\,38^{\lfloor T/12\rfloor}
 \le195\,\gamma^T,\qquad \gamma=38^{1/12}.              \tag{7}
 \end{aligned}
\]
Counting repeated sources more than once in the intermediate sum only
enlarges this upper bound. It is uniform in the target and the population.

In particular, \(R_{X,T}(a)\le195\gamma^T/X\). A positive fraction
\(R_{X,T}(a)\ge p>0\), even at a target depending on \(X\), requires
\[
 T\ge\frac{12}{\log38}\log\frac{pX}{195},
 \qquad \frac{12}{\log38}\approx3.29889093.              \tag{8}
\]
This is a **necessary lower bound**, not a sufficient stopping time.
It concerns hitting one target, not entering a growing set of targets.

## 2. Nonzero accumulation values of the target densities

A coalescence component consists of starts whose forward orbits eventually
meet, with different meeting times allowed. By the earlier
[minimum-law argument](DENSITY-TO-POINTWISE.md), its natural density
\(\lambda_C\) exists, these densities sum to one, and convergence holds
uniformly over arbitrary unions of components. The external predecessor
theorem makes every component's density positive. Along a forward orbit
in \(C\), target densities increase to \(\lambda_C\).

A component is *cyclic* if its orbits eventually repeat; otherwise its
orbits are injective and leave every finite set. Call the latter components
divergent. Put
\[
 \lambda_* =\max_C\lambda_C,\qquad
 \lambda_{\rm div}=\sup_{C\text{ divergent}}\lambda_C,
\]
where the second value is zero if there are no divergent components.
For a nonempty family of positive component masses, the supremum is a
maximum: their sum is at most one, so only finitely many can exceed half
of any positive supremum.

For every \(\varepsilon>0\), choose \(X\) with \(\delta_X<\varepsilon\).
If \(r_a\ge\varepsilon\), then \(R_X(a)>0\). Thus
\[
 \{a:r_a\ge\varepsilon\}
       \subseteq\bigcup_{n=1}^{X}\{C^t(n):t\ge0\}.       \tag{9}
\]
Within each represented component, finitely many trajectories merge into
a common forward tail. Outside finitely many prefix values, the union
in (9) is therefore a finite union of divergent tails; its cyclic parts
are finite. On each divergent tail the densities tend to that component's
mass. It follows that
\[
 \boxed{\{\text{positive accumulation values of }r_a\text{ as }a\to\infty\}
       =\{\lambda_C:C\text{ divergent}\}.}              \tag{10}
\]
For the forward inclusion, any sequence tending to a positive limit
eventually lies in the high-level set (9); take a subsequence in one of
the finitely many tails. The reverse inclusion follows by following any
divergent orbit. In particular,
\[
 \boxed{\lim_{A\to\infty}\sup_{a>A}r_a=\lambda_{\rm div}.} \tag{11}
\]
Hence global decay \(r_a\to0\) would exclude divergence. It would still
permit additional cycles. No such global decay is proved here.

## 3. The exact defect when time is truncated

For fixed \(X\), let \(N_C(X)\) count the sampled starts in component
\(C\), and define \(d_X=\max_{C\text{ divergent}}N_C(X)/X\), or zero
if none are represented. Then
\[
                 \boxed{\Delta_X(T)=d_X
                         \quad\text{for all sufficiently large }T.} \tag{12}
\]
Indeed, for every finite \(T\) and every represented divergent component,
choose a common future target beyond all values visited by the sample
through time \(T\). All sampled sources in that component reach it
eventually, none reach it by \(T\), and sources in other components never
reach it. Thus \(\Delta_X(T)\ge d_X\) for **every** \(T\).

The finitely many sampled sources in cyclic components have finite orbit
sets. After a sufficiently large time all those sets have been covered.
A remaining missed target can then receive contributions only from its
own divergent component, at most \(d_X\). This proves (12). There is
no assertion that the threshold is computable without classifying the
sample's orbits.

Uniform convergence of the component distribution gives
\(d_X\to\lambda_{\rm div}\). On the other hand, (7) implies
\(\sup_a R_{X,T}(a)\to0\) for each **fixed** \(T\) as \(X\to\infty\).
Together with (1), this proves
\[
 \boxed{
 \lim_{X\to\infty}\lim_{T\to\infty}\Delta_X(T)=\lambda_{\rm div},
 \qquad
 \lim_{T\to\infty}\lim_{X\to\infty}\Delta_X(T)=\lambda_* .} \tag{13}
\]
Here \(\sup_a r_a=\lambda_*\): targets are contained in their own
components, and a forward orbit approaches the full component mass.
The two limits need not agree. If full Collatz were true, their values
would be zero and one, respectively.

More quantitatively, if for some fixed \(\eta>0\)
\[
 T(X)\le(1-\eta)\frac{12}{\log38}\log X,
\]
then (7) gives \(\sup_aR_{X,T(X)}(a)\le195X^{-\eta}\), and therefore
\(\Delta_X(T(X))\to\lambda_*\). Such a clock leaves a positive
uniform defect, even though (1) has zero limiting error.

Under the stated density inputs and external positivity theorem, a clock
\(T(X)\) with \(\Delta_X(T(X))\to0\) exists **if and only if no positive
orbit diverges**. Necessity follows from the lower bound \(d_X\) for
every time. For sufficiency, when every sampled orbit is eventually
cyclic, choose a time covering their finite orbit sets. This is an
existence equivalence, not a constructed or effective clock.

Grouping more inverse branches does not supply this missing time estimate.
The congruence calculation above bounds how many sources a finite clock
can capture; it does not bound how much eventual mass can remain on a
late, escaping common tail. Nontrivial cycles require a separate exclusion.

## 4. Verification scope

[`DensityTimeTruncation.lean`](../lean/DensityTimeTruncation.lean) checks
the exact two-step branches, inverse-list coverage and length, target
periodicity, the 1458-residue bound and its distinct witness, composition,
and the all-depth finite cardinality bound. It imports only the local
ordinary Collatz definitions. No native evaluator or admitted proof is used.

The independent [Python replay](../verify_density_time_truncation.py)
checks inverse lists against ordinary one-step inversion and complete
bounded forward enumeration, checks lifted residues and longer blocks,
and measures finite-time defects on complete convergent sample orbits.
These finite samples establish no asymptotic density or infinite-orbit
classification. Equations (7)–(13) remain written mathematics; their
analytic dependencies are recorded separately in the
[manifest](../results/density-time-truncation/verification.json).

```sh
python3 verify_density_time_truncation.py --reuse-build-dir /tmp/collatz-killed-operator-build
```
