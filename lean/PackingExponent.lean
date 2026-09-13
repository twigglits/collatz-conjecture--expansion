/-
  Finite integer comparisons supporting the written endpoint packing bound.
  Standalone Lean 4; kernel evaluation only, no Mathlib or native_decide.
  Check: lean lean/PackingExponent.lean

  Logarithms, entropy monotonicity, strong induction on interval lengths,
  and real-analysis consequences are written in ORBIT-PACKING-BOOTSTRAP.md.
-/
namespace PackingExponent

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

/-- These imply 1/2<alpha<2/3 and H_2(alpha)>alpha for alpha=log_3(2). -/
theorem endpoint_elementary_inputs :
    3 < 2 ^ 2 ∧ 2 ^ 3 < 3 ^ 2 ∧ 2 ^ 4 < 3 ^ 3 := by decide

/-- A lower rational bound on alpha, above 1/2. -/
theorem rational_slope_lower : 233 < 2 * 147 ∧ 3 ^ 147 < 2 ^ 233 := by decide

/-- Taking logarithms gives H_2(147/233)<19/20. Since entropy decreases
    between 1/2 and 1, this implies H_2(log_3(2))<19/20 in the written proof. -/
theorem rational_entropy_upper :
    (233 : Nat) ^ 4660 < 2 ^ 4427 * 147 ^ 2940 * 86 ^ 1720 := by decide

#print axioms endpoint_elementary_inputs
#print axioms rational_slope_lower
#print axioms rational_entropy_upper
end PackingExponent
