# Positive predecessor density: source audit and the remaining premise

**Status, 2026-10-12: independent Lean source replay passed.** All 389
project modules compiled successfully, and the three public theorem roots
report exactly `propext`, `Classical.choice`, and `Quot.sound`. The source
identities and the mathematical meanings of the public statements have
also been checked. The minimum-law deductions below retain their separate
written analytic dependencies. Collatz remains unresolved.

The external result is Lech Mazur's *Positive Lower Density of Collatz
Predecessors*. The [public claim](https://www.proofatlas.ai/proofs/artifact.collatz.predecessors_positive_lower_density.v001.html)
and [formalization record](https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/)
identify the three roots and the source supplement. The
[local verification record](../results/predecessor-density-review/verification.json)
records our source replay, independently of the publisher's build receipt.

## 1. Exact verified statement

Let \(C(n)=n/2\) for even \(n\), and \(C(n)=3n+1\) for odd \(n\).
Write \(n\to^*a\) when \(C^t(n)=a\) for some integer \(t\ge0\), and
\[
 P_a=\{n\ge1:n\to^*a\},\qquad
 N_A(X)=\#\{n<X:n\in A\}.
\]
The main external statement, abbreviated **PLD** here, is
\[
 a>0,\quad3\nmid a
 \quad\Longrightarrow\quad
 \exists c_a>0\ \exists X_a\ \forall X\ge X_a,
       N_{P_a}(X)\ge c_aX.                              \tag{1}
\]
This counts distinct positive starting integers, includes a zero-step
hit, and concerns the ordinary integer Collatz map. The source defines
the map using `if Even n then n / 2 else 3 * n + 1`; `Reaches` is
existence of an iterate, and `natCount` is `Nat.count` below the cutoff.
The constants depend on the target. No uniform lower bound in \(a\),
general-target hitting-time bound, or density limit is asserted by (1).

The other two advertised roots assert that a positive counterexample
would give the whole nonconvergent set positive lower natural density,
and that the following premise implies convergence of every positive
integer:
\[
 \forall\varepsilon>0\ \forall N\ \exists X\ge N,\quad X>0,
 \qquad N_{P_1}(X)\ge(1-\varepsilon)X.                   \tag{2}
\]
Premise (2) says that the convergent set has upper natural density one.
It is a hypothesis of the third theorem, not a proved conclusion.

## 2. How a counterexample is amplified

This elementary deduction is written here to make the scope transparent;
it is also present in the external source.

Assume (1) and let \(n\ge1\) fail to reach one. Write \(n=2^vm\)
with \(m\) odd. Its orbit reaches \(a=3m+1\), which is positive and
not divisible by three. The integer \(a\) cannot reach one. Every
predecessor of \(a\) also fails to reach one: once an orbit has reached
one, it stays in the ordinary cycle \(1,4,2\), so all its subsequent
states still reach one. Thus, for the nonconvergent set \(E\),
\[
                  P_a\subseteq E,\qquad N_E(X)\ge c_aX
\]
for all sufficiently large \(X\). Taking \(\varepsilon=c_a/2\)
in (2) then contradicts
\(N_E(X)+N_{P_1}(X)\le X\). This covers a hypothetical nontrivial
cycle and a hypothetical divergent orbit alike.

## 3. Consequence for the repository's minimum law

The [written minimum-distribution argument](DENSITY-TO-POINTWISE.md)
has separate analytic dependencies and is not kernel checked. Assuming
that argument as well as (1), it gives a probability law \(p\) with
\[
 \frac1{\lfloor X\rfloor}\#\{n\le X:\operatorname{Col}_{\min}(n)=1\}
        \longrightarrow p_1.
\]
Changing the integer endpoint convention affects only \(O(1/X)\).
Consequently
\[
 \boxed{\text{every positive integer reaches one}\quad\Longleftrightarrow\quad p_1=1.}
                                                               \tag{3}
\]
For the reverse implication, the limit supplies (2), and Section 2
excludes a counterexample. No improved convergence rate for the minimum
law is needed. PLD at target one also gives \(p_1>0\).

More generally, every coalescence component has positive lower natural
density under (1). For a member \(n\), choose \(a=3m+1\) as above;
every predecessor of \(a\) belongs to the same component as \(n\).
Under the written minimum law, component densities exist, so each
component has strictly positive density. Their countable probability
distribution therefore assigns positive mass to every component.
This does not force the distribution to have just one component.

With only the older \(X^{0.84}\) predecessor bound, the previously
identified logarithmic error rate did not exclude a counterexample,
even assuming \(p_1=1\). The verified PLD theorem removes that rate
requirement. It does **not** prove \(p_1=1\). Almost-bounded
minima allow a fixed positive mass at an unknown larger minimum; the
mass tending to one as the allowed minimum bound grows does not select
minimum one.

The same written first-passage argument gives densities for odd-target
predecessor sets. A further
[overshoot estimate extends this to every positive target](DENSITY-TO-POINTWISE.md#5-extension-to-every-fixed-positive-target).
These densities increase along a forward orbit to its component density.
A summed packing bound prevents a uniform positive lower bound over all
eligible targets, but does not exclude a sparse divergent orbit.

## 4. Reproducible verification scope

The two authenticated archives are:

| Archive | Bytes | SHA-256 |
| --- | ---: | --- |
| Positive-density slim baseline v2.1 | 914975 | `23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f` |
| Predecessor-density supplement v1.1 | 55103 | `55ceb4df0cca17ae728dc65b30bf5077000e1b47f2dc322454eea9f637ac75b3` |

The independent [archive check](../verify_predecessor_density_archives.py)
compares every one of the 404 assembled files byte for byte with an
authenticated archive member. They include 389 Lean modules: 388 in the
public interface import closure and one release audit. The
[authentication record](../results/predecessor-density-review/archive-authentication.json)
records each member, hash, and source archive. This is source identity
verification, not theorem verification.

The [source verifier](../verify_predecessor_density_source.py) uses
Lean `4.30.0-rc2`, compiler commit
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, with pinned third-party
compiled dependencies. It independently compiles each project module
sequentially. Third-party libraries are not rebuilt, and no separate
Lean kernel implementation is used.

The previous local run stopped after 121 successful modules. Before
resuming, process inspection found no live audit. The `--resume` mode
validated that exact successful prefix, source/log/object hashes, compiler
commands, toolchain, dependency revisions, and absence of unrecorded
project objects. The remaining 268 modules then compiled successfully.
Progress writes are atomic and an operating-system file lock prevents a
second verifier for the same assembled tree.

After the last successful Lean compilation, the Python verifier initially
rejected the audit output because its axiom-list parser expected a single
line. Lean had wrapped the three standard axioms across lines. The parser
was fixed and checked on the actual multiline report, a single-line
equivalent, and seven invalid reports. The
[parser regression record](../results/predecessor-density-review/axiom-parser-check.json)
preserves the failed validation's provenance. A final resume validated all
389 source/log/object records and passed the corrected axiom check without
recompiling any module. This was a report-formatting failure; no Lean
compilation failed.

The [completed progress record](../results/predecessor-density-review/progress.json)
and [verification record](../results/predecessor-density-review/verification.json)
report success at **2026-10-12 14:44:35 UTC**. The
[release audit log](../results/predecessor-density-review/build/Verification.ReleaseAudit.log)
prints the three statements and their axiom reports, and enumerates 4,717
project declarations in their dependency closure. The audit also checks
expanded public statements and rejects an imported unproved universal
Collatz declaration. Linter and deprecation warnings in other build logs
do not assert additional axioms or admit proofs.

```sh
python3 verify_predecessor_density_archives.py \
  /private/tmp/collatz-density-audit/assembled \
  /private/tmp/collatz-positive-density-baseline.zip \
  /private/tmp/collatz-predecessor-density-source.zip

# For an interrupted replay only, after its previous process has ended:
python3 verify_predecessor_density_source.py \
  /private/tmp/collatz-density-audit/assembled --resume
```

For a completely fresh replay, prepare a new authenticated assembled tree
and omit `--resume`. The project output directory must then contain no
compiled project modules.
