# Complete ordered integer-cycle test

`CollatzCycleCriterion.lean` now proves the full ordered-word equivalence,
including sufficiency for actual accelerated Collatz cycles.

For every nonempty list `word : List Nat` with each symbol positive,
`word_cycle_iff` states

```lean
(∃ n, RealizesWord word n) ↔
  0 < denominator word ∧ denominator word ∣ weight word
```

The definitions are

```lean
weight [] = 0
weight (h :: tail) = 3 ^ tail.length + 2 ^ h * weight tail
denominator word = 2 ^ word.sum - 3 ^ word.length
```

The recursive numerator unfolds to the ordered sum in `CYCLE-WORDS.md` §1.
Natural subtraction is guarded by `0 < denominator word`, equivalently
`3^word.length < 2^word.sum`; negative or zero signed denominators are
therefore rejected.

`RealizesWord word n` requires a positive odd seed, a return to that seed
after exactly `word.length` applications of `F`, and

```lean
v2 (3 * iterate i n + 1) = word[i]
```

at every indexed position. Here `F n = oddPart (3*n+1)` is the actual
accelerated map. `oddPart` and `v2` are defined by recursively dividing out
all factors of two, with the same conventions as `CollatzFrontier.lean`.
The theorem does not require the word to be primitive.

## What sufficiency proves internally

`word_sufficiency` constructs the seed `weight word / denominator word`.
It establishes all the facts that were explicit assumptions of the initial
cyclic-numerator bridge:

- Rotating the word preserves its total exponent and length, hence its
  denominator; rotating by its length returns the original word.
- The numerators of all rotations are positive and odd.
- The positive denominator is coprime to two.
- The exact rotation identity is
  `2^h_i * W_(i+1) = 3*W_i + D`.
- Starting from `D ∣ W_0`, divisibility propagates to every rotated numerator.
- Every quotient `W_i/D` is a positive odd natural number.
- Cancellation gives `2^h_i*(W_(i+1)/D) = 3*(W_i/D)+1`.
- An odd terminal quotient proves both the actual accelerated transition and
  the exact valuation `v2(3*n_i+1)=h_i`.
- The rotated head at position `i` equals the original indexed symbol
  `word[i]`, so the realized exponent sequence is the supplied ordered word.

Thus intermediate integrality, positivity, and parity are not external
premises of the final sufficiency theorem.

## Necessity and reusable interfaces

`actual_factorization` proves `2^(v2 n)*oddPart n=n` for every positive `n`.
`word_equation` composes arbitrary finite prescribed step equations into the
exact affine identity. For a returning actual orbit, the positive numerator
forces a positive denominator, and the cycle equation gives divisibility.
This is `word_necessity`; combining it with sufficiency gives the equivalence.

`cyclic_numerators_realize` remains available independently. It accepts a
finite cyclic sequence of odd numerators with the rotation equations and
initial divisibility, and produces every actual intermediate iterate and
its exact exponent. This permits other ordered numerator constructions to
reuse the arithmetic bridge.

## Verification and remaining scope

The standalone Lean 4.31 file compiles without warnings. The final command
and axiom reports are recorded in `results/cycle_criterion_lean.log`.
No admitted proofs, custom axioms, or `native_decide` occur; only standard
`propext`, `Classical.choice`, and `Quot.sound` appear in axiom reports.

This is a universally quantified characterization of each finite ordered
halving word. It does not prove that every passing word represents the
trivial cycle, bound all word lengths, or exclude divergent orbits. Those
global questions remain unresolved.
