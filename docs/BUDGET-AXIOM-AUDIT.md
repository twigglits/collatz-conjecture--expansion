# A false bounded-budget axiom in a claimed Collatz proof

**Status: the counterexample below is kernel checked. It refutes a
published axiom, not the Collatz conjecture.**

On 8 October 2026, a source search found the public
[CollatzLayerA v8.1 repository](https://github.com/AIDoctrine/CollatzLayerA).
Its README claims a complete formal verification, while its
[Lean source](https://github.com/AIDoctrine/CollatzLayerA/blob/main/CollatzLayerA_v8_1_FINAL.lean)
declares the key budget as an axiom. In the source's ordinary Collatz
clock, let \(P(k,n)\) count the odd states before the first \(k\) steps.
The axiom says that every \(n\ge2^{71}\) with \(n\equiv3\pmod4\)
admits a \(0<k\le200\) with
\[
 P(k,n)\le44,\qquad k-P(k,n)\ge71.
 \tag{1}
\]

Take
\[
 n=2^{111}-1=2596148429267413814265248164610047.
\]
This is above \(2^{109}\), so increasing the axiom's starting threshold
to the source's claimed finite base would not repair this example.
For every \(0\le k\le200\), the ordinary trajectory alternates odd
and even states, giving
\[
 P(k,n)=\lceil k/2\rceil,\qquad k-P(k,n)=\lfloor k/2\rfloor.
\]
The two inequalities in (1) cannot both hold. The algebraic reason is
\(C^{2j}(2^{111}-1)=2^{111-j}3^j-1\) for \(j\le100\), so those
even-time states are odd, and each following \(3n+1\) step is even.
More generally, starts \(2^L-1\) with arbitrarily large \(L\) defeat
any fixed horizon requiring more even than odd ordinary steps.

[BudgetAxiomAudit.lean](../lean/BudgetAxiomAudit.lean) reproduces the
source's map and counting equations, proves all 201 displayed prefix
counts by kernel evaluation, and deduces the negation of its quantified
budget. It also kernel checks that this witness reaches 1 after 1,476
ordinary steps. No external axiom, Mathlib, `sorry`, or native evaluator
is used. The remaining printed dependencies are standard logical axioms.

The foreign file as a whole was not built here. A successful build of
a theorem depending on an added axiom would not prove that axiom.
This explicit contradiction rules out importing its claimed conclusion
as a solution. It does not invalidate every unrelated lemma in the
source, or rule out a valid estimate with a start-dependent horizon.

[Verification record](../results/budget-axiom-audit/verification.json).
The complete Collatz conjecture remains unresolved.
