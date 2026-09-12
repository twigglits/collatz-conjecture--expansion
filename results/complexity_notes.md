# Weight-sensitive growth and finite collisions

`CollatzComplexity.lean` is a standalone Lean 4.31 file. Its shortcut map and
orbit definitions agree exactly with `CollatzRepetition.lean`. The finite
parity/congruence and list-counting backbone is reused there; the new results
derive height bounds from cumulative odd counts and a lower bound on earlier
states. All proofs use the kernel, with no `native_decide`, admitted proofs,
or custom axioms. The compiler output is in `results/complexity_lean.log`.

## Main checked bound

Write `x_t = orbit t n` and `w_t = wt t n`. If every state `x_i`, `i<t`, is at
least `M`, then `minimum_weight_growth` proves

\[
 2^t M^{w_t}x_t \le n(3M+1)^{w_t}.
\]

For positive `M`, this is the ordinary real inequality

\[
 x_t\le n\,\frac{(3+1/M)^{w_t}}{2^t}.
\]

The Lean statement uses only natural-number products. Each even step retains
its full factor of two. At an odd prestate `x≥M`, the required inequality is
`M(3x+1) ≤ (3M+1)x`. Induction combines the exact number of such factors.
The final state `x_t` need not satisfy the floor assumption.

`minimum_weight_growth_of_le` also accepts any proved upper bound `w_t≤J`,
replacing both exponents by `J`. `weight_le_time` proves the universal count
bound `w_t≤t` separately.

## New finite criteria

Let a catalog contain `P` parity words of length `k`, encoded as natural
numbers. `minimum_weight_catalog_forces_repeat` assumes:

- Every prestate at a position strictly below `P` is at least `M`.
- The parity window at every position `0,…,P` belongs to the catalog.
- For every such position `t`,
  `n*(3*M+1)^(w_t) < 2^k*(2^t*M^(w_t))`.

It concludes that two states at positions `i<j≤P` are equal.
`bounded_weight_catalog_forces_repeat` accepts a function `J(t)` bounding
the actual cumulative odd counts and uses its values in the same products.
These theorems derive the required height bounds; they do not assume them.
They are sufficient criteria: a direct height check can succeed even when
the growth envelope is too loose.

`catalog_forces_descent_or_repeat` sets `M=n`. Under the catalog and product
conditions alone, it proves that either a state before position `P` is smaller
than the seed, or two states repeat by position `P`. Thus the floor assumption
is replaced by an explicit descent alternative.

Finally, `descent_of_weight_deficit` needs no catalog. For positive `n`, if

\[
 (3n+1)^{w_t}<2^t n^{w_t},
\]

then some state at a position at most `t` is smaller than `n`.
This is a necessary cumulative-weight restriction on any prefix without
descent, obtained with the additive `+1` term fully accounted for.

The improvement is a finite bridge from actual weight information to
collision/descent. Its premises are not automatic: no bound on the factor
complexity or cumulative odd count of every Collatz orbit is supplied.
Furthermore, a repeated state establishes a cycle without identifying it as
the trivial cycle. These remaining tasks prevent a universal conclusion.

## Audit of the earlier argument

`CollatzRepetition.lean` handles signed differences through `Int.natAbs`, so
its congruence argument does not truncate a negative difference. Its final
catalog theorem covers `P+1` positions, including position `P`, and concludes
`i<j`. The intermediate periodicity lemmas allow equal starting positions;
a positive period follows when the separate strict inequality `i<j` is
available, as it is in the catalog theorem.

The written proofs in `STURMIAN-ATTEMPT.md` are consistent with these scopes:

- The signed rational extension keeps an odd denominator fixed and requires
  twice the absolute-height bound, whereas the positive-integer version uses
  the interval below `2^k` directly.
- Mechanical words have at most `k+1` factors by partitioning the intercept
  at the finitely many threshold phases. Endpoint conventions do not create
  extra isolated factors.
- The halving-to-parity conversion counts odd positions strictly before an
  integer time; its ceiling formula also handles time zero.
- The two substitution block maps, their shifted growth bound, the finite
  factor bound, and the period-reduction argument are valid.

The cited interpretation of Dubickas is also supported by his Theorem 5 and
its proof in Section 5: the complexity lower bound is conditional on a
divergent positive trajectory. It does not assert existence of such a
trajectory. See [the published paper](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C40C0C07FEC20797475BB2899C436C9A/S0017089508004655a.pdf/on_integer_sequences_generated_by_linear_maps.pdf).

The rational extension, mechanical-word combinatorics, asymptotic exclusions,
and external GitHub development have not been kernel-checked by this file.
The external development retains the partial-audit caveat already recorded
in the earlier note.
