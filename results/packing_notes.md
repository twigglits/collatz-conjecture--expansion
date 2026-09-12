# Finite orbit-packing core

`CollatzPacking.lean` is a standalone Lean 4.31 file. It recreates exactly the
ordinary shortcut definitions `U`, `orbit`, and `wt` from `CollatzAffine.lean`
in a separate namespace, and includes the same proved affine translation.
No existing certificate template is changed.

The principal checked statements are:

- `block_image_bound`: for all natural `k,p,n`, if `n < p*2^k`, then
  `orbit k n < p*3^(wt k n)`.
- `residue_image_bound`: if `r < 2^k`, then `orbit k r < 3^(wt k r)`.
  This strengthens the factor-two bound used in the original written note.
- `orbit_add`: `orbit (k+t) n = orbit k (orbit t n)`.
- `fixed_iterate_injective`: an injective sequence `t ↦ orbit t n` remains
  injective after applying any fixed iterate to its values.
- `fixed_iterate_on_orbit`: the corresponding injectivity statement on the
  set of values of that orbit.
- `fixed_weight_packing`: any duplicate-free finite list of orbit positions
  whose values lie in `[2^k*q, 2^k*q+2^k)` and whose block offsets have weight
  `j` has length at most `3^j`, assuming the full orbit is nonrepeating.

The final statement quantifies over arbitrary starts, block indices, weights,
prefix lengths, and finite lists. The block offset is written as natural
subtraction; the lower block bound explicitly ensures it does not truncate.
The proof injects the selected positions into the integers below `3^j` and
proves the finite cardinality comparison using duplicate-free lists.

Lean exits successfully with no warnings. `results/packing_lean.log` records
the command and axiom reports. There are no admitted proofs, custom axioms,
or uses of `native_decide`; the reports contain only the standard
`propext`, `Quot.sound`, and, for finite list counting, `Classical.choice`.

## Independent audit of APERIODIC-ATTEMPT.md, sections 2–3

The written implications in these sections are sound with their stated
nonrepetition and positivity assumptions:

1. Two equal images at a fixed iterate would give two equal later positions
   of the same orbit. Thus the necessary injectivity applies to that orbit,
   even though `U` is not injective on all positive integers.
2. Affine translation puts the images of a fixed-weight group in a common
   short interval. The checked residue bound strengthens this finite step.
3. The parity-word bijection and binomial tail argument in the note correctly
   bound the remaining groups; an arbitrary interval of one block length
   meets at most two aligned blocks.
4. Reciprocal summability follows from the explicit power-saving interval
   estimate. Zero Banach density alone would not suffice for this step.
5. An accelerated odd orbit embeds into the shortcut orbit: each accelerated
   step is one odd shortcut step followed by its remaining halvings. If the
   shortcut orbit repeated, a subsequent odd value would repeat as well.
6. On a nonrepeating positive integer orbit, the values tend to infinity.
   Combining reciprocal summability, the bounded correction product, and
   the exact multiplicative identity therefore justifies the stated limit
   of the cumulative multiplier to infinity.

The new Lean file does **not** formalize the parity-word binomial count, the
full interval estimate, reciprocal summability, real products and limits,
or Theorem 2 of the note. Those remain written arguments. The checked packing
statement is conditional on orbit injectivity; it neither constructs a
divergent orbit nor excludes every such orbit. Nontrivial cycles also remain
unresolved.
