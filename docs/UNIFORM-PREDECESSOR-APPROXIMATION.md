# Uniform approximation of all predecessor densities

**Status: written analytic theorem with a kernel-checked passage comparison.
Collatz remains unresolved.** The analysis depends on the written uniform
first-passage Proposition 4.1 in
[NATURAL-DENSITY-ALMOST-BOUNDED.md](NATURAL-DENSITY-ALMOST-BOUNDED.md) and the
limiting passage laws and atom bound in Section 2 of
[PREDECESSOR-DENSITY-FLOW.md](PREDECESSOR-DENSITY-FLOW.md#2-the-limiting-first-passage-law-has-small-atoms).
Those analytic inputs are not kernel checked. No novelty is asserted.

For the ordinary Collatz map \(C\), write \(n\to^*a\) when an iterate
of \(n\) equals \(a\), including time zero. Put
\[
 R_X(a)=\frac1{\lfloor X\rfloor}
           \#\{1\le n\le X:n\to^*a\}.
\]
The following strengthens existence of a density at each fixed target:
there is a function \(r:\mathbb N_{>0}\to[0,1]\) and a constant
\(c>0\) such that
\[
 \boxed{\sup_{a\ge1}|R_X(a)-r_a|\ll(\log X)^{-c}.}          \tag{1}
\]
The constants do not depend on the target. In particular (1) applies to
a target \(a=a_X\) chosen after the cutoff \(X\). It does not say that
\(r_{a_X}\) is small. The proof below constructs the limit directly,
so it does not presuppose the earlier fixed-target density theorem.

## 1. Hits before or after a passage

Fix a positive integer floor \(H\). Let \(F_H(n)\) be the first odd
ordinary orbit value at most \(H\), with an infinity mark if no such
value occurs. This is the Syracuse passage location after removing
initial powers of two. Its finite mark set is
\(B_H=\{b\le H:b\text{ positive and odd}\}\).

If \(n\to^*a\), then either the first visit to \(a\) occurs after
the landing, in which case \(F_H(n)\to^*a\), or it occurs before
the landing, in which case \(F_H(n)=F_H(a)\). If passage never occurs,
a reached target also has the infinity mark. Writing
\[
 L_{H,a}=\{n:\exists b\in B_H,\ F_H(n)=b\text{ and }b\to^*a\},
\]
we have
\[
 L_{H,a}\subseteq P_a
       \subseteq L_{H,a}\cup\{n:F_H(n)=F_H(a)\}.            \tag{2}
\]
The union need not be disjoint. Cyclic targets and infinite passage are
both allowed.

[PassageApproximation.lean](../lean/PassageApproximation.lean) constructs
a noncomputable first-passage mark for **any** target predicate and
proves (2). It checks existence and uniqueness of a first time when entry
occurs, the suffix argument, and the nonentry case. The noncomputable
definition supplies no algorithm for deciding whether an arbitrary orbit
ever enters.

Let \(\mu\) be any probability law on positive starts, and let
\(q=\mathcal L(F_H(\mu))\), including its infinity atom. Define
\[
 T_Hq(a)=\sum_{b\in B_H}q(b)1_{b\to^*a}.
\]
Taking probabilities in (2) gives the target-uniform estimate
\[
 \boxed{0\le\mathbf P_\mu(n\to^*a)-T_Hq(a)
                         \le q(F_H(a))\le\|q\|_\infty.}   \tag{3}
\]
No independence between passage and eventual hitting is assumed. The
quantity \(T_Hq\) retains the actual future orbits of the landing values.

## 2. Uniform convergence for odd source intervals

Let \(\mathbf U_Y\) be uniform on odd integers in \([Y,2Y)\), and put
\(R_Y^{\rm odd}(a)=\mathbf P(\mathbf U_Y\to^*a)\). The earlier
passage-law argument gives a probability law \(\nu_H\) such that,
uniformly for \(Y\ge H^\alpha\), with \(\alpha=1.001\),
\[
 d_{\rm TV}(\mathcal L(F_H(\mathbf U_Y)),\nu_H)
                          \ll(\log Y)^{-c},\qquad
 \delta_H:=\|\nu_H\|_\infty\ll(\log H)^{-c}.              \tag{4}
\]
The infinity atom is included in \(\delta_H\). Existence of these laws
and the uniform constants in (4) use only the first-passage argument in
Section 2 of the flow note, before its fixed-target density deductions.

For clarity, the small-atom input has a finite counting basis: at source
scale \(Y=H^\alpha\), outside an event of probability \(O(H^{-c})\),
entry takes at most \(n_0=\lfloor\log_2H/10\rfloor\) Syracuse steps
and at most \(3n_0\) shortcut steps. At most \(2^{3n_0+1}-1\) starts
can reach any one landing by that time. Dividing by \(Y/2+O(1)\), then
using the passage-law telescope, gives (4). The bounded-time count is
kernel checked; the probabilistic estimates remain written analysis.

Write \(q_Y=\mathcal L(F_H(\mathbf U_Y))\) and
\(\epsilon_Y=d_{\rm TV}(q_Y,\nu_H)\). For every target, (3) implies
\[
 T_H\nu_H(a)-\epsilon_Y
   \le R_Y^{\rm odd}(a)
   \le T_H\nu_H(a)+\delta_H+2\epsilon_Y.                   \tag{5}
\]
Here \(|T_Hq_Y(a)-T_H\nu_H(a)|\le\epsilon_Y\), since the sum is
over a subset of the finite mark space. The same estimate holds for
any larger source scale \(Z\).

Choose \(H=\lfloor Y^{1/\alpha}\rfloor\). For large \(Y\), (4)
applies to both \(Y\) and every \(Z\ge Y\), with error
\(O((\log Y)^{-c})\). Equation (5) gives
\[
 \sup_{a\ge1}|R_Y^{\rm odd}(a)-R_Z^{\rm odd}(a)|
                           \ll(\log Y)^{-c}.              \tag{6}
\]
Each coordinate has a real limit \(r_a\in[0,1]\); passing to that
limit in (6) preserves the bound for **all** targets at once. Hence
\[
 \sup_{a\ge1}|R_Y^{\rm odd}(a)-r_a|\ll(\log Y)^{-c}.        \tag{7}
\]
This is uniform convergence of a function indexed by targets, not total
variation convergence of entire orbit-value sets.

## 3. Uniform positive starts and the initial halving segment

For odd starts up to \(M\), decompose into dyadic intervals and discard
the initial part below \(\sqrt M\). The discarded relative size is
\(O(M^{-1/2})\); every remaining interval satisfies (7) with the same
error uniformly in the target. Their mixture therefore has the same
uniform limit and logarithmic error.

For positive starts up to \(X\), condition on \(v=\nu_2(n)\). The
odd parts in that group are uniform among odd integers up to \(X/2^v\).
The groups with \(2^v>\sqrt X\) have total relative size
\(O(X^{-1/2})\). All other groups use the preceding estimate at
\(M\ge\sqrt X\), uniformly in the target.

An initial halving segment can visit \(a\) before its odd part does.
For a **single arbitrary target**, the discrepant starts are contained in
\(\{2^j a:j\ge0\}\). There are at most \(1+\lfloor\log_2 X\rfloor\)
such starts up to \(X\), independently of \(a\). Its contribution is
therefore \(O((\log X)/X)\) uniformly over targets. This proves (1),
including even targets. Its limits agree with the preceding fixed-target
densities by uniqueness.

## 4. A uniform finite-mixture formula

For each fixed \(H\), let \(q_{H,X}\) be the passage law for uniform
positive starts up to \(X\). It converges to \(\nu_H\). Taking
\(X\to\infty\) in (3), for any target \(a\), gives
\[
 \boxed{0\le r_a-T_H\nu_H(a)\le\nu_H(F_H(a))\le\delta_H.} \tag{8}
\]
The error is uniform in \(a\). Thus the entire predecessor-density
function is uniformly approximated by a finite weighted sum of the
actual forward-orbit indicators of odd starts at most \(H\).

For example, if \(a\) lies on none of those forward orbits, then
\(r_a\le\delta_H\). If all those starts have certified finite orbits,
the mixture has finite support and bounds the density at every target
outside that support. The statements do not certify that all the small
starts converge for arbitrarily large \(H\), nor do the present
implicit analytic constants give a new numerical bound at a tested floor.

## 5. Why uniformity alone does not exclude divergence

Suppose a hypothetical divergent component has natural density
\(\lambda>0\), as supplied by the separate written component law and
the [verified external PLD theorem](PREDECESSOR-DENSITY-REVIEW.md).
Fix one of its forward orbits \(a_0,a_1,\ldots\). For each cutoff
\(X\), finitely many starts at most \(X\) belong to that component;
all eventually join this forward orbit. Choose \(j_X\) beyond all of
their meeting indices, and far enough that \(a_{j_X}>X\). Then
\[
 R_X(a_{j_X})
   =\frac1{\lfloor X\rfloor}
      \#\{n\le X:n\text{ belongs to that component}\}
      \longrightarrow\lambda.                            \tag{9}
\]
No start from another component can hit that target. Equation (1) would
therefore give \(r_{a_{j_X}}\to\lambda\), not zero. A far-away target
need not have few predecessors below the sampling cutoff: those paths
may pass through a small value and then follow the divergent orbit.

The new estimate resolves uniformity in the target. It does not provide
the separate bound making the observed proportions small for such moving
targets, or eliminate the possible divergent seed orbits in (8).
Nontrivial cycles also remain to be excluded. The density-one premise
\(r_1=1\) is still unproved.

## 6. Verification scope

[The verification record](../results/uniform-predecessor-approximation/verification.json)
records eleven new kernel theorems and separate exact finite checks of
(2)–(3), including predicates with nonentry and cyclic targets. The
initial-halving discrepancy bound is also checked over the stated finite
populations. The probabilistic limits, rate, and infinite quantifiers in
(1), (4), and (6)–(9) remain written analysis.

```sh
python3 verify_uniform_predecessor_approximation.py
```

An optional `--reuse-build-dir` validates the existing standalone Lean
dependency by toolchain and source, object, and log hashes. The new module
is compiled afresh. No external PLD module is rebuilt.
