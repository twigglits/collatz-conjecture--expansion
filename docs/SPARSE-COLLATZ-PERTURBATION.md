# Sparse changes preserve the density inputs while allowing escape

**This is an explicitly different map, not a Collatz counterexample.**
It tests whether the project's density arguments, even halving, and inverse
congruences suffice to exclude escape. They do not. Swapping odd outputs
at only \(O(\log X)\) inputs through \(X\) creates an explicit escaping
path while retaining positive predecessor lower density at every target
coprime to three, zero predecessor density at multiples of three, and
the permitted odd-image classes. The actual odd-parent identity changes
at a sparse set of targets. That identity remains a possible essential
input to a proof for the unmodified Collatz map.

The algebra and basin inclusions below have separate kernel proofs in
[`SparseCollatzPerturbation.lean`](../lean/SparseCollatzPerturbation.lean).
The density inheritance uses the previously
[replayed external PLD theorem](PREDECESSOR-DENSITY-REVIEW.md).
The passage-law stability is a written argument, conditional on the
project's [written passage premise](NATURAL-DENSITY-ALMOST-BOUNDED.md).
No novelty is claimed and no asymptotic statement is certified by the
finite experiment.

## 1. Swap two odd outputs at each scale

Let \(C\) be ordinary Collatz. Define
\[
 A_j=\frac{4^{3j+8}-1}{3},\qquad
 A_{j+1}=64A_j+21,\qquad
 B_j=\frac{2A_{j+1}-1}{3}.
\]
Here \(A_0=21845\), \(A_1=1398101\), and \(B_0=932067\).
The exact identities are
\[
 \begin{gathered}
 A_j\equiv5\pmod{12},\qquad B_j\equiv3\pmod4,
 \qquad A_j<B_j<A_{j+1},\\
 C(A_j)=4^{3j+8},\qquad C(B_j)=2A_{j+1}.
 \end{gathered}
\]
Thus the two increasing sequences are disjoint and all their members
are odd. For a parameter \(t\ge0\), let \(\pi_t\) exchange
\(A_j\) and \(B_j\) for every \(j\ge t\), fixing all other integers.
Set
\[
                         F_t(n)=C(\pi_t(n)).              \tag{1}
\]
This gives the concrete rules
\[
 F_t(A_j)=2A_{j+1},\qquad F_t(B_j)=4^{3j+8}\quad(j\ge t).
\]
Every other input uses the ordinary Collatz rule. In particular all even
inputs are halved, and the cycle \(1\to4\to2\to1\) is unchanged.

The Lean definition uses classical choice to select the unique index.
The map is nevertheless explicitly computable: start at \(A_t\), test
the pair \((A_j,B_j)\), and replace \(A_j\) by \(64A_j+21\) until
\(A_j>n\). At most \(1+\lfloor\log_{64}n\rfloor\) pairs can be
examined. The independent verifier uses that finite algorithm and checks
it against the closed formulas.

Put \(D_t=\{A_j,B_j:j\ge t\}\). Since \(A_j\ge21845\,64^j\),
\[
 \#(D_t\cap[1,X])\le2(1+\lfloor\log_{64}X\rfloor)
 \quad(X\ge1).                                          \tag{2}
\]
Also \(F_t=C\) on every input below \(A_t\). Increasing \(t\)
therefore preserves any prescribed finite collection of actual Collatz
trajectories: take \(A_t\) above every state they visit. This statement
does not assume that untested trajectories terminate. For \(t=0\), the
finite replay checks that all starts through 64 still reach one; the
largest ordinary value on those original paths is 9232, below \(A_0\).

## 2. Escape and exact inverse branches

For every \(k\ge0\), the kernel proves
\[
 F_t^{2k}(A_t)=A_{t+k},\qquad
 F_t^{2k+1}(A_t)=2A_{t+k+1}.                              \tag{3}
\]
These values tend to infinity and never equal one. Any start that reaches
\(A_t\) also never reaches one: a prior visit to one would trap it in
the unchanged finite cycle. By contrast, the actual Collatz orbit of
\(A_t\) reaches a power of four in one step and then reaches one.

The involution \(\pi_t\) fixes even integers and preserves parity.
Consequently the exact ordinary inverse formula is
\[
 F_t(n)=a\quad\Longleftrightarrow\quad
 n=2a\ \text{ or }\
 \left(a\equiv4\pmod6\ \text{ and }\
 n=\pi_t((a-1)/3)\right).                                \tag{4}
\]
There is still one even parent, and exactly one odd parent when the
ordinary congruence permits it. In particular every positive target has
at most two parents. The odd images are still exactly the positive
integers congruent to four modulo six.

For the shortcut map \(V_t(n)=F_t(n)/2\) on odd inputs and
\(V_t(n)=n/2\) on even inputs, the corresponding odd parent is
\(\pi_t((2a-1)/3)\), permitted exactly when \(a\equiv2\pmod3\).
It too has at most two parents. These are exact inverse congruences,
but the odd parent is no longer always \((a-1)/3\) or \((2a-1)/3\).

If \(3\mid a\), (4) allows only the even parent. The kernel proves
\[
                  F_t^k(n)=a\ \Longleftrightarrow\ n=2^ka.
                                                               \tag{5}
\]
For fixed positive \(a\), the union over \(k\) contains only
\(O(\log X)\) starts through \(X\), so its natural density is zero.
The density conclusion is written counting, separate from (5).

## 3. Every unit target retains positive predecessor lower density

This inheritance is unconditional relative to the already replayed
external PLD theorem; it does not need the unformalized natural-density
passage argument.

Under the **original** map \(C\), the set
\[
 \mathcal T=\{2^e:e\ge0\}\cup\{A_j,B_j,2A_j:j\ge0\}
\]
is forward invariant. All modified inputs lie in it. A number
\(c>1\), \(c\equiv1\pmod{12}\), lies outside \(\mathcal T\).
Therefore an original trajectory reaching such a \(c\) cannot have
visited any modified input before that hit. The kernel proves the
exact same-time inclusion
\[
 C^k(n)=c\quad\Longrightarrow\quad F_t^k(n)=c
 \qquad(c>1,\ c\equiv1\pmod{12}).                        \tag{6}
\]

For any positive \(a\) not divisible by three, choose
\(e\in\{6,7,8,9,10,11\}\) with \(2^ea\equiv4\pmod9\), and set
\[
                         c=(2^ea-1)/3.
\]
Such an exponent exists because the six powers of two run through the
units modulo nine. The kernel checks the six residue cases. We have
\(c>1\), \(c\equiv1\pmod{12}\), and \(3c+1=2^ea\).
The path from \(c\) to \(a\) consists of its unchanged odd step followed
by \(e\) halvings. Combining it with (6) gives a kernel-proved inclusion
\[
                         P_c^C\subseteq P_a^{F_t}.        \tag{7}
\]
Since \(3\nmid c\), external PLD gives positive lower natural density
to the left side, and hence to the right side. At \(a=1\) this gives
a positive-density set converging to one. At \(a=A_t\), (3) gives a
positive-density set escaping to infinity. Here and below, this phrase
means positive **lower** density unless existence of a density is
separately invoked. No exact value for either fraction is asserted.

Thus the zero-density rule at multiples of three, positivity at every
other target, the inverse degree bound, and agreement on an arbitrary
finite collection of checked paths coexist with escape in this altered
map. They cannot alone prove Collatz.

## 4. The large-floor first-passage law survives

Let \(Q_x^C\) and \(Q_x^{F_t}\) denote the first odd orbit value at
most \(x\), including a nonentry mark. Sample an odd start uniformly
from \([y,2y)\), with
\(x^\alpha\le y\le x^{\alpha^2}\), \(\alpha=1.001\).
The existing early valuation estimate for \(C\) says that, outside
an event of probability \(O(x^{-c_0})\), its passage occurs within
\[
 T=4n_0\text{ ordinary steps},\qquad
 n_0=\lfloor\log x/(10\log2)\rfloor.
\]
This follows from at most \(n_0\) Syracuse steps and total valuation
at most \(3n_0\). We use this old-map event only.

Until the first visited member of \(D_t\), the two trajectories are
identical. A modified odd input at most \(x\) is already a passage
location, so its outgoing step cannot change that first-passage mark.
A discrepancy on the good old-map event must therefore involve an
old-map hit of \(D_t\) above the floor by time \(T\).

Since \(C(n)\le4n\), all old states by that time lie below
\(B=2y4^T\). By (2), only \(O(\log B)=O(\log x)\) modified inputs
can be encountered. At most \(2^{T+1}-1\) distinct positive starts
hit any one target by time \(T\); this elementary inverse-tree bound
does not require a source cutoff. Also \(2^T\le x^{2/5}\).
Dividing the union bound by the \(y/2+O(1)\) odd sources gives
\[
 \mathbf P(Q_x^{F_t}\ne Q_x^C)
 \ll x^{-c_0}+(\log x)x^{2/5-\alpha}
 \ll x^{-c_0}+x^{-3/5}.                                 \tag{8}
\]
The coupling uses the same sampled start. All constants can be chosen
independently of \(t\). First-passage nonentry for \(F_t\) is covered
by the same bad event; it is not inferred from a numerical timeout.

Equation (8) transfers both assertions of the written Proposition 4.1
to \(F_t\), including the total-variation comparison across the whole
interval of source scales. It also transfers the early first-passage
clock estimates: on the coupled good event the two clocks are equal.
The subsequent minimum-law and component-law deductions apply with
the altered map and retain their written, conditional status. They
therefore cannot by themselves identify the minimum with one or
exclude the explicit escape in (3).

This is a comparison at **growing floors and their nearby source scales**.
It does not say that the two maps have the same eventual basin densities,
the same limiting law at a fixed small floor, or the same convergence
probability. Those stronger claims would conflict with the construction.

## 5. Further counting properties and the remaining distinction

Every finite parity-prefix law has the same limiting natural frequencies
as ordinary Collatz. For any fixed shortcut depth \(k\), the old
trajectory from \(n\le X\) stays below \(2^kX\) up to that depth.
Only \(O_k(\log X)\) starts can encounter a modified input: take a
union of its bounded-time inverse fibres. Apart from those starts,
the entire prefix is unchanged. Thus every length-\(k\) parity word
still has natural density \(2^{-k}\). This fixed-depth fact is not an
assertion of independence along an infinite integer trajectory.

The existing finite orbit-packing exponent also survives, with a changed
absolute constant. Before its first modified input an \(F_t\) orbit is
an original Collatz prefix. After a hit of \(A_j\) it follows the
geometric path (3); after a hit of \(B_j\) it halves a power of four
into the known cycle. Each added geometric path contributes only
\(O(1+\log L)\) distinct values to a length-\(L\) interval. Adding
this to the original \(O(L^\sigma)\) packing bound, \(0<\sigma<1\),
preserves that exponent. This is written counting, not a new kernel
packing theorem for \(F_t\).

What fails is exact ordinary odd-parent arithmetic at the swapped images,
even though its permitted residue classes and parent counts survive.
The upward swaps also violate the original odd-step growth bound:
\(F_t(A_j)=128A_j+42>3A_j+1\). This construction does not test an
argument that uses that upper bound in an essential way.
The perturbation is therefore no evidence that actual Collatz is false.
It narrows the research requirement: an exclusion of escape must use
more than these shared density, passage, packing, and inverse-congruence
properties. In particular, proving an estimate from them and then
applying it to every actual branch would also contradict (3) in this
comparison system.

For example, let \(r'_a\) be the altered-map target densities supplied
by the transferred written passage premise. At the escaping spine,
the ordinary parents of \(2A_{j+1}\) are \(A_j\) and \(4A_{j+1}\).
Nonperiodicity makes their basins disjoint, giving
\[
 r'_{A_{j+1}}=r'_{A_j}+r'_{4A_{j+1}},\qquad
 \sum_{j\ge t}\frac{r'_{4A_{j+1}}}{r'_{A_j}}<\infty.
\]
Since \(\log A_j=O(j+1)\), a uniform positive lower bound on these
ratios of order \(1/\log A_j\) is impossible. Thus the proposed
relative-branch estimate cannot follow from the shared properties alone.
All odd states of this particular escaping tail are modified inputs:
sparsity among integers does not prevent an entire orbit from remaining
in the sparse exceptional set at its odd steps.

## 6. Verification

[`verify_sparse_collatz_perturbation.py`](../verify_sparse_collatz_perturbation.py)
builds the local dependency and the new Lean module afresh, audits the
printed theorem axioms, and runs independent exact checks of the swaps,
forward and inverse steps, explicit paths, safe ancestor construction,
finite classifications, and first-discrepancy counts. The classical
definition in Lean adds no nonstandard axiom; the finite algorithm in
Python is a separate check, not native Lean computation.
It also revalidates the source, object, and log hashes from the completed
external replay; that record's assembled source and build must remain
available. It does not rebuild the external package.

The [verification record](../results/sparse-collatz-perturbation/verification.json)
separates kernel results, finite arithmetic, external PLD inheritance,
and conditional written analysis. Reproduce with:

```sh
python3 verify_sparse_collatz_perturbation.py
```

Full positive-integer Collatz remains unresolved. No density-one estimate
or pointwise convergence proof for the actual map has been obtained.
