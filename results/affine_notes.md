# Exact affine descent and the symbolic residue sieve

`CollatzAffine.lean` and the appended template `lean/ResidueSieveBody.lean` are checked with Lean 4.31.0. They concern the ordinary shortcut map U(n)=(3n+1)/2 for odd n and n/2 for even n. They introduce no axioms, admitted proofs, Mathlib dependency, or native computation in their proofs.

For a prefix length k and residue r, put M=2^k, A=3^(wt k r), and b=U^k(r). The universal affine identity is

    U^k(Mq+r) = Aq+b.

For A<M, the sharp first quotient that guarantees descent is

    q0 = 0                         if b<r,
         floor((b-r)/(M-A))+1      otherwise.

The theorem `residue_threshold_iff` proves descent at this step **if and only if q≥q0**. The separately proved inequality Ar≤Mb guarantees that the numerator B=Mb-Ar does not use truncated subtraction. The equivalent start-value threshold (`residue_start_threshold_iff`) is

    U^k(n)<n iff n>floor(B/(M-A)),  for n=Mq+r.

Thus each contracting residue class has an explicitly bounded exceptional set q<q0. `class_descent_iff_finite_exceptions` proves that eventual descent of its members n>1 is equivalent to eventual descent of just those exceptions, because the tail descends at the fixed step k.

## What slope alone does not prove

The statement that the **first** coefficient drop always coincides with first actual descent for n>1 is Terras' Coefficient Stopping Time conjecture. It is not assumed or proved here; `CoefficientStoppingTimeClaim` merely names that proposition. The conjectural status and distinction from later prefixes are explicit in [Rozier–Terracol, Definition 1.2 and following discussion](https://arxiv.org/html/2502.00948v1), with [the revised paper published in 2026](https://arxiv.org/abs/2502.00948).

At an arbitrary later prefix, slope<1 certainly does not suffice. The kernel checks U^8(7)=8 even though 3^5/2^8=243/256<1. It also checks that 7 already descends to 5 at step 7, its first coefficient drop, so this is **not** a counterexample to Terras' conjecture. Here B=347, the sharp q threshold is 1, and all 256q+7 with q≥1 descend at step 8. The single exceptional representative 7 descends at step 7, completing a certificate for the whole infinite class. The excluded start 1 supplies the trivial genuine first-drop exception: U^2(1)=1 with slope 3/4.

## Certificate interfaces

Inside `CollatzAffine`:

- `ClassCertificate` has natural-number fields `k`, `r`, `q0`.
- `checkClass` recomputes r<2^k, A≤M, and the endpoint inequality Aq0+b<Mq0+r. Its soundness theorem proves actual descent for every q≥q0.
- `checkWholeClass` additionally requires q0=0 or q0=1 with r≤1. Its soundness theorem covers every member n>1 immediately.
- `checkCompleteClass c fuel` combines the symbolic tail certificate with explicit bounded descent checks for q<q0. Its soundness theorem certifies eventual descent of every class member n>1.

Append `lean/ResidueSieveBody.lean` after the complete affine file. Inside `CollatzResidue`:

- `certificate k r` uses the computed sharp q0; `closes k r` applies `checkWholeClass`.
- `covered fuel k r q` closes the current class if possible; otherwise it follows the next low bit of q into the even or odd child.
- `covered_sound` proves that accepted n=2^k*q+r>1 descends within k+fuel shortcut steps.
- `good depth n = covered depth 0 0 n`; `good_sound` gives descent within depth for every accepted n>1, without the previous 8^depth threshold.
- `countCovered fuel k r` counts closed branches by their full mass 2^fuel and recursively splits open branches.
- `countCovered_eq_countWhere` proves that this fast counter equals the exact number of accepted q in [0,2^fuel). Its proof partitions even and odd indices; running the counter does not enumerate the whole interval.
- `covered_periodic` proves that adding any multiple of 2^fuel to q preserves acceptance. `count_each_block` therefore certifies the same count in every aligned block.
- `countOpen` is the remaining mass; `mass_partition` proves exact partition of 2^fuel residues.

Counts concern accepted **residue classes**, not necessarily all starts that actually descend. In the initial block, the starts 0 and 1 are outside the n>1 descent statement. For later positive blocks every accepted start descends. Open residue classes remain unresolved; neither the tree nor a finite depth certificate proves convergence for all positive integers.

A generated numeric theorem may use `native_decide` to evaluate `countCovered`; such a theorem additionally trusts Lean's compiler and native runtime. The universal checker, counting, and periodicity proofs are kernel proofs independent of any generated count.

## Actual verification log

The checked file was the exact concatenation of `CollatzAffine.lean` and `lean/ResidueSieveBody.lean`. Command:

    lean +v4.31.0 /tmp/CollatzResidueCheck.lean

Exit code: 0

```text
'CollatzAffine.affine' depends on axioms: [propext, Quot.sound]
'CollatzAffine.descent_requires_slope_drop' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.orbit_equation' depends on axioms: [propext, Quot.sound]
'CollatzAffine.residue_start_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.orbit_threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.affine_descent_mono' depends on axioms: [propext, Quot.sound]
'CollatzAffine.threshold_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.checkClass_sound' depends on axioms: [propext, Quot.sound]
'CollatzAffine.checkWholeClass_sound' depends on axioms: [propext, Quot.sound]
'CollatzAffine.checkCompleteClass_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.class_descent_iff_finite_exceptions' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAffine.example_first_drop' does not depend on any axioms
'CollatzAffine.one_first_drop_exception' does not depend on any axioms
'CollatzAffine.slope_only_counterexample' does not depend on any axioms
'CollatzAffine.example_infinite_class' depends on axioms: [propext, Quot.sound]
'CollatzAffine.example_complete_class' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzResidue.covered_sound' depends on axioms: [propext, Quot.sound]
'CollatzResidue.covered_periodic' depends on axioms: [propext, Quot.sound]
'CollatzResidue.countCovered_eq_countWhere' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzResidue.good_sound' depends on axioms: [propext, Quot.sound]
'CollatzResidue.count_each_block' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzResidue.mass_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
```
