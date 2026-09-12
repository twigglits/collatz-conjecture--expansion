# Ordinary Collatz: checked contradiction reductions

The new standalone `CollatzContradiction.lean` concerns the ordinary positive-integer **3n+1** conjecture. Its namespaced `C` is definitionally the same formula as `T 3 1` in `CollatzTheory.lean`; `U` is the same shortcut formula as `U` in `CollatzFrontier.lean`. There are no imports of the other files, so these proofs do not depend on their computational certificates.

The file proves:

- **`conjecture_iff_descent`:** Every positive integer reaches 1 if and only if every integer greater than 1 eventually reaches a smaller integer. The reverse implication uses strong induction and positivity of every iterate. There is no bound on the required number of steps.
- **`least_counterexample_exists` / `least_orbit_lower_bound`:** Failure gives a least positive nonconvergent integer n>1, and every forward iterate is at least n.
- **`least_has_no_smaller_predecessor`:** A least counterexample also cannot be reached from a smaller positive start. The proof includes convergence preservation after reaching 1, accounting for the ordinary 1→4→2→1 cycle.
- **`least_mod48`:** A least counterexample must lie in one of six residue classes: **7, 15, 27, 31, 39, 43 modulo 48**. Even starts descend immediately; 4q+1 reaches 3q+1 in three steps (and descends when q>0); 16q+3 reaches 9q+2 in six steps; and 6q+5 is reached in two steps from the smaller positive predecessor 4q+3.
- **`conjecture_iff_restricted_descent`:** Proving eventual descent for all integers greater than 1 in those six classes is equivalent to proving the full conjecture. This is an infinite universal condition, not six finite checks.
- **`shortcut_iteration_simulation`:** k shortcut steps are exactly j ordinary steps for some k≤j≤2k. **`reaches_iff_shortcut`** proves convergence equivalence in both directions, including at 1. **`conjecture_iff_shortcut_descent`** makes the ordinary conjecture equivalent to eventual shortcut descent for every n>1.

These are verified reductions, not a proof or disproof. All six remaining classes contain infinitely many positive integers. We have not proved their universal eventual descent, nor shown the least-counterexample properties inconsistent. A finite search, density estimate, or convergence in related ax+c maps cannot fill that gap. The restrictions apply to a *least* counterexample, not necessarily to every member of a hypothetical nonconvergent orbit.

## Verification log

The default `lean` selector is unconfigured in this environment; the installed explicit selector works. The following is actual output from a complete successful check, including the printed axiom dependencies. No proof uses `sorry`, `native_decide`, or a newly declared axiom. Standard Lean foundations (`propext`, `Classical.choice`, `Quot.sound`) are shown explicitly.

Compiler: `Lean (version 4.31.0, arm64-apple-darwin24.6.0, commit 68218e876d2a38b1985b8590fff244a83c321783, Release)`

Command: `lean +v4.31.0 CollatzContradiction.lean`

Exit code: `0`

```text
'OrdinaryCollatz.conjecture_iff_descent' depends on axioms: [propext, Quot.sound]
'OrdinaryCollatz.least_counterexample_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.least_orbit_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.least_has_no_smaller_predecessor' does not depend on any axioms
'OrdinaryCollatz.least_mod48' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.counterexample_constraints' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.conjecture_iff_restricted_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.shortcut_iteration_simulation' depends on axioms: [propext, Quot.sound]
'OrdinaryCollatz.ordinary_reaches_of_shortcut' depends on axioms: [propext, Quot.sound]
'OrdinaryCollatz.reaches_iff_shortcut' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.conjecture_iff_shortcut_descent' depends on axioms: [propext, Classical.choice, Quot.sound]
'OrdinaryCollatz.least_shortcut_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```
