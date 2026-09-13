/-
  Exact elementary comparisons used in MASK-CYCLE-OBSTRUCTIONS.md.
  Standalone Lean 4; kernel evaluation only, no native_decide.
  This file does not formalize logarithms, entropy, the published
  linear-independence theorem, catalog counts, or an all-period exclusion.
  Check: lean lean/MaskCatalogBounds.lean
-/
namespace MaskCatalogBounds

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

theorem mechanical_slope_inputs :
    (3 : Nat) ^ 147 < 2 ^ 233 ∧ 2499 < 8 * 313 ∧
    27 * 147 = 233 * 17 + 8 := by decide

/-- At t=40 the exponential side exceeds 2^16, already above 896t. -/
theorem double_two_cutoff :
    16 * 45 < 19 * 40 ∧ 896 * 40 < (2 : Nat) ^ 16 ∧ 90 < 19 * 40 := by
  decide

/-- At t=192 the exponential side exceeds 2^25, already above 576t^2. -/
theorem alternating_cutoff :
    25 * 15 < 2 * 192 ∧ 576 * 192 ^ 2 < (2 : Nat) ^ 25 ∧ 30 < 192 := by
  decide

theorem hamming_ball_input : (33 : Nat) ^ 16 < 2 ^ 81 := by decide

#print axioms mechanical_slope_inputs
#print axioms double_two_cutoff
#print axioms alternating_cutoff
#print axioms hamming_ball_input
end MaskCatalogBounds
