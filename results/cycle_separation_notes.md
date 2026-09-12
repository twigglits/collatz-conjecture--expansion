# Formal local separation for ordered cycle words

`CollatzCycleSeparation.lean` proves two infinite families of divisibility exclusions, together with reusable local replacement lemmas. All proofs use standalone Lean 4 and were checked with the repository's Lean 4.33.1 toolchain. There are no admitted proofs, new axioms, or native evaluation tactics.

The strongest completed family theorem is `repeated_block_replacement_exclusion`: take any nonempty positive halving block `w` and repeat it `g ≥ 3` times. Replace one occurrence of `w` by a different positive block with the same length and sum. The resulting ordered word fails `D ∣ W`. The original repeated word need not describe an integer cycle.

`repeated_block_transfer_exclusion` also handles `g ≥ 2`: moving exactly one halving between two adjacent positions, in either direction, fails `D ∣ W`. Its premises explicitly identify the original word with a repetition. Arbitrary transfer amounts and edits crossing the chosen linear cut are not asserted by this theorem.

## Definitions and the connection to Collatz

For a halving word `w`, the file defines

\[
W([])=0,\qquad W(h::t)=3^{|t|}+2^hW(t),\qquad
D(w)=2^{\sum w}-3^{|w|}.
\]

These definitions and the append formula are identical to those in `CollatzCycleCriterion.lean`, in a separate namespace. Only this small algebraic core is repeated; the Collatz transition theory is not copied. In Lean, `D` uses natural subtraction. Every application requiring a positive signed denominator states that premise. The common-factor results remain valid even when natural subtraction gives zero.

The existing `CollatzCycleCriterion.word_cycle_iff` identifies the cycle test `0 < D ∧ D ∣ W` with realization of a nonempty positive word by an actual positive odd Collatz cycle, with exact valuations. Consequently the new failures of `D ∣ W` exclude those cycles. This file itself proves arithmetic statements about ordered words; it does not redefine the actual orbit or assert a universal Collatz result.

## Local replacement and injectivity

For blocks `u,v` of equal length and sum, and unchanged surrounding lists `p,s`, `replacement_difference` proves

\[
W(pus)-W(pvs)=2^{\sum p}3^{|s|}\bigl(W(u)-W(v)\bigr).
\]

This identity uses natural subtraction and holds in either order. `replacement_divides_distance` combines both orders: if a number `F` coprime to both 2 and 3 divides both full numerators, it divides the absolute local difference

\[
|W(u)-W(v)|=(W(u)-W(v))+(W(v)-W(u)).
\]

`weight_injective` proves that positive halving words of equal length and sum with equal numerator are identical. Every nonempty tail numerator is odd, so equality of the numerator determines each preceding power of two; the sum determines the final symbol. `replacement_equal_word` therefore proves local uniqueness whenever the absolute local difference is less than `F`.

For the adjacent unit transfer, `transfer_weight` proves the sharper identity

\[
W(p\,[a+1,b],s)=W(p\,[a,b+1],s)+2^{\sum p+a}3^{|s|}.
\]

Neither this identity nor equality of the two denominators needs positivity of `a,b`. `transfer_cycle_test_exclusion` proves the two words cannot both pass divisibility when their common actual denominator is greater than 1, discharging its coprimality conditions internally. The generic `shared_factor_excludes_monomial_perturbation` only needs a nontrivial factor shared by the denominator and original numerator; it does not assume the original cycle test succeeds.

## Repeated blocks

Write `A = 2^S`, `B = 3^ℓ` for a block's sum `S` and length `ℓ`. The formal geometric factor is defined by

\[
F_0=0,\qquad F_{g+1}=B^g+A F_g.
\]

The file proves `W(w^g)=F_g W(w)` and `F_g ∣ D(w^g)`. For positive `S,ℓ` and `g ≥ 2`, it proves `F_g > 1` and coprimality with 2 and 3. These establish the adjacent unit-transfer exclusion without any numerical enumeration or original-cycle premise.

For the complete single-copy replacement theorem, two further bounds are checked:

\[
W(w)<3^S\quad\text{for positive words},\qquad F_g>3^S\quad(g\ge3).
\]

Thus two allowed local numerators differ by less than the shared factor; divisibility and injectivity force the replacement to be identical, contradicting the premise.

These are exclusions for specific families. They do not cover every halving word, supply a decomposition of arbitrary words into excluded edits, prove that only the trivial cycle exists, or rule out divergent trajectories. The sharper fixed-length/sum extremal numerator bound discussed in the root notes is not formalized here.

## Reproduction

From the repository root:

```sh
lean CollatzCycleSeparation.lean
```

`results/cycle_separation_lean.log` records the explicit 4.33.1 command, Lean version, source SHA256, exit status, and printed axiom dependencies. The final file passes with zero warnings. Printed dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.
