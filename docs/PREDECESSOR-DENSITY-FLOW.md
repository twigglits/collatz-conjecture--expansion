# First-passage atoms and density flow in a fixed predecessor basin

**Status: written analytic deductions, with separate kernel-checked finite
counting and graph lemmas. Collatz remains unresolved.** This note uses the
written uniform first-passage Proposition 4.1 in
[NATURAL-DENSITY-ALMOST-BOUNDED.md](NATURAL-DENSITY-ALMOST-BOUNDED.md) and the
early-valuation estimate in
[DENSITY-TO-POINTWISE.md](DENSITY-TO-POINTWISE.md#5-extension-to-every-fixed-positive-target).
It does not independently validate that analytic adaptation. No novelty is
asserted.

Write \(C\) for the ordinary Collatz map, \(U\) for the shortcut map, and
\(P_a=\{n\ge1:C^t(n)=a\text{ for some }t\ge0\}\). The preceding
written argument supplies a natural density \(r_a\) for every fixed
positive target. This note proves the stronger, but basin-specific, limit
\[
 \boxed{\lim_{R\to\infty}\ \sup_{\substack{b>R\\b\in P_a}}r_b=0
          \quad\text{for each fixed }a\ge1.}                 \tag{1}
\]
An empty supremum is zero. The threshold in (1) can depend on the entire
finite orbit information below a chosen floor; it is not uniform in \(a\).

## 1. A target-independent finite fibre bound

Every positive target has at most two shortcut predecessors. Thus the
number of distinct positive starts hitting a fixed \(a>0\) within
\(k\) shortcut steps, including time zero, is at most
\[
                         2^{k+1}-1.                        \tag{2}
\]
The bound concerns the complete bounded-time fibre, without any source
cutoff or factor depending on \(a\). It follows by expanding an inverse
tree and retaining duplicates in an upper-bound list.

The module [BoundedHitFibres.lean](../lean/BoundedHitFibres.lean) proves
exact membership of that list, its length bound, and (2) for every list
of distinct qualifying starts. It also proves first-hit uniqueness and
recursion. These are kernel proofs with standard axioms only; they do not
establish the limiting probability estimates below.

## 2. The limiting first-passage law has small atoms

For a real floor \(x\ge1\), define
\[
 F_x(n)=\operatorname{Pass}_x(\operatorname{oddpart}(n)),
\]
with a separate value \(\infty\) if passage never occurs. For uniform
odd starts \(\mathbf U_Y\) in \([Y,2Y)\), the laws of
\(F_x(\mathbf U_Y)\) have a limiting probability law \(\nu_x\).
The same limit holds for uniform positive starts up to \(X\).
Moreover, for sufficiently large \(x\),
\[
 \boxed{\sup_{z\in(2\mathbb N+1)\cap[1,x]\ \cup\{\infty\}}
                      \nu_x(\{z\})\ll(\log x)^{-c}.}       \tag{3}
\]
The constants in (3) do not depend on a target or basin.

For existence and comparison, if \(u\ge x\) and an odd start exceeds
\(u\), first passage gives the exact identity
\[
                  F_x(n)=F_x(\operatorname{Pass}_u(n)),      \tag{4}
\]
with \(F_x(\infty)=\infty\). Before the first passage below \(u\),
no odd value is at most \(x\); if passage below \(u\) never occurs,
neither can passage below \(x\).

Apply Proposition 4.1 with \(u=Y^{1/\alpha}\), where
\(\alpha=1.001\) and \(Y\ge x^\alpha\). Pushing both passage laws
through \(F_x\) and telescoping the scales \(Y,Y^\alpha,\ldots\)
gives
\[
 d_{\rm TV}\bigl(F_x(\mathbf U_Y),\nu_x\bigr)
                         \ll(\log Y)^{-c}.                \tag{5}
\]
The support is the finite set of odd values below \(x\), together with
\(\infty\), so the limit is a probability law. As in the earlier note,
dyadic decomposition and conditioning on initial powers of two transfer
it to uniform positive starts. Here initial halving changes no mark:
\(F_x\) was defined using the odd part.

To bound individual atoms, take \(Y=x^\alpha\) and
\(n_0=\lfloor\log_2x/10\rfloor\). The earlier valuation argument gives,
outside an event of probability \(O(x^{-c})\),
\[
 T_x\le n_0,\qquad S_{n_0}\le3n_0.
\]
A Syracuse step of valuation \(v\) is exactly \(v\) shortcut steps.
Thus on this event the landing value is reached within \(3n_0\)
shortcut steps. For each fixed finite landing value, (2) bounds the
number of such source integers by \(2^{3n_0+1}-1\). Since there are
\(Y/2+O(1)\) odd sources, its probability is
\[
              O(2^{3n_0}/Y)+O(x^{-c})=O(x^{-c}).
\]
The infinite-passage atom has the same bound. Combining this with (5)
at \(Y=x^\alpha\) proves (3). This is an upper bound on individual
atoms, not a uniform distribution over the landing interval.

## 3. Uniform decay inside one fixed basin

Fix \(a>0\). Take a sufficiently large integer \(x\ge a\); if \(a\)
is periodic, also take \(x\) above every value of its finite cycle.
For each \(z\le x\) that reaches \(a\), retain the finite path from
\(z\) through its **first** hit of \(a\). Let \(Q_x\) be the union
of these paths, and put \(R_x=\max Q_x\).

This is a finite set: only finitely many \(z\) are considered, and a
path is included only when its first hitting time is finite. The
construction does not assume that every \(z\le x\) reaches \(a\).
It also includes the cycle of \(a\), if there is one, by the choice of
\(x\). No effective procedure for deciding all the included \(z\) is
asserted.

Let \(b\in P_a\) satisfy \(b>R_x\). It is outside the cycle of \(a\),
so any orbit that reaches \(b\) must do so before its first hit of
\(a\). Otherwise \(a\to^*b\to^*a\) would put \(b\) in that cycle.
Such an orbit also cannot visit an integer \(z\le x\) before hitting
\(b\): the retained path from that \(z\) to its first hit of \(a\)
would contain \(b\), contradicting \(b\notin Q_x\).

Consequently every ordinary value before the hit of \(b\) exceeds
\(x\). Grouping the halving segments into Syracuse steps gives
\[
       n\in P_b\quad\Longrightarrow\quad F_x(n)=F_x(b).     \tag{6}
\]
This also holds for even \(n\) or \(b\); any initial or intermediate
halving segment is grouped with its eventual odd value. Since \(b\)
reaches \(a\le x\), \(F_x(b)\) is finite. Taking natural densities
in (6), using the limiting law from Section 2, yields
\[
                   r_b\le\nu_x(\{F_x(b)\})
                        \ll(\log x)^{-c}\qquad(b>R_x).     \tag{7}
\]
For any desired error first choose \(x\) large, then the corresponding
finite \(R_x\). This proves (1). It does not permit replacing \(R_x\)
by a uniform function of \(x\) independent of \(a\) and its paths.

In particular, \(r_{2^j a}\to0\) for each \(a\), and densities tend
to zero along every simple infinite inverse chain ending at \(a\).
The statement also applies uniformly to all targets whose first-hit
distance back to \(a\) tends to infinity. Only finitely many integers
lie below a fixed size bound, and each of those in the basin has a fixed
finite first-hitting time.

## 4. The inverse density flow at a nonperiodic root

Say \(a\) is nonperiodic if \(C^k(a)\ne a\) for every \(k>0\).
Its immediate predecessor basins are disjoint. A common source visiting
two distinct immediate predecessors would visit \(a\) at two different
times, giving a positive-time return to \(a\). The kernel checks this
implication, the ordinary inverse branches, and the one-step basin
decomposition in `BoundedHitFibres.lean`.

Singletons have zero density, so for a nonperiodic positive root,
\[
 r_a=r_{2a}+
       1_{a\equiv4\ (6)}\,r_{(a-1)/3}.                    \tag{8}
\]
The second term is used only when its positive odd target is integral.
Every predecessor of a nonperiodic target is itself nonperiodic. For an
odd nonperiodic \(a\), iterating (8) along the doubling chain gives,
for \(K\ge1\),
\[
 r_a=r_{2^K a}+
       \sum_{\substack{1\le k<K\\3\mid 2^k a-1}}
                       r_{(2^k a-1)/3}.                  \tag{9}
\]
Every summand target is a positive odd integer. The finite partition
behind (9) also contains the finitely many pure-halving sources
\(a,2a,\ldots,2^{K-1}a\), which do not affect density.

By (1) the first term on the right tends to zero. Therefore
\[
 \boxed{r_a=\sum_{\substack{k\ge1\\3\mid 2^k a-1}}
                       r_{(2^k a-1)/3}}
       \quad(a\text{ odd and nonperiodic}).               \tag{10}
\]
This infinite branch sum is justified by the explicit remainder in (9),
not by exchanging a density limit with an arbitrary countable union.

Nonperiodicity cannot be dropped. For example, the ordinary root four
has parents eight and one; their basins overlap, as the path
\(8\to4\to2\to1\) already demonstrates. At the Syracuse root one,
one is itself an inverse branch, but cannot be the last odd predecessor
before a **first** hit of one. Counting that cyclic branch as disjoint
would duplicate mass.

## 5. What this does and does not exclude

The [verified external PLD theorem](PREDECESSOR-DENSITY-REVIEW.md) makes
\(r_b>0\) at every target not divisible by three. Thus (10) gives a
nonnegative, countably additive flow of predecessor density through an
acyclic inverse tree. By (1), no infinite inverse chain can retain a
positive limiting fraction of a fixed root's density.

This is compatible with the separate written forward limit
\(r_{a_j}\uparrow\lambda\) in a hypothetical divergent component,
where PLD gives \(\lambda>0\). For each fixed \(J\), the later
forward states \(a_j\), \(j>J\), do **not** belong to \(P_{a_J}\):
a return would make the orbit periodic. Hence the basin-specific limit
(1) does not apply to that forward sequence. Its thresholds cannot be
used while changing the root with \(j\).

A bound uniform enough to force decay along an unbounded forward orbit
is still missing. Upper natural density one of convergence is also
unproved, and nontrivial cycles remain unexcluded. No complete Collatz
proof or positive counterexample follows from this note.

## 6. Verification

[The verification record](../results/predecessor-density-flow/verification.json)
separates the twelve kernel theorems, the complete stated finite Python
checks, and the written limiting arguments. Python independently checks
complete bounded-time fibres by forward simulation, terminal halving
marks, finite branch partitions, the finite-basin first-passage transport,
and the periodic overlap warning.
These finite checks do not establish any asymptotic density limit.

```sh
python3 verify_predecessor_flow.py
```

The optional `--reuse-build-dir` accepts a previous dependency build only
after matching its Lean version and source, object, and log hashes. The
new module is compiled afresh. No third-party library or external PLD
module is recompiled by this verifier.
