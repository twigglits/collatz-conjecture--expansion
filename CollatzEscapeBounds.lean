/-
  Exact arithmetic supporting the rational exponent 31/32 in ORBIT-ESCAPE.md.
  These checks do not formalize the real-analysis or orbit-counting argument.
-/
namespace CollatzEscapeBounds

set_option exponentiation.threshold 1024
set_option maxRecDepth 10000

theorem low_weight_base : (3 : Nat) ^ 352 < 2 ^ 558 := by decide

theorem high_weight_base :
    (18 : Nat) ^ 576 < 2 ^ 558 * 11 ^ 352 * 7 ^ 224 := by decide

/-- Exact example used for the substitution family in COMPLEXITY-GROWTH.md. -/
theorem length_eleven_weight_seven :
    (2 : Nat) ^ 44 < 3 ^ 28 ∧ (3 : Nat) ^ 28 < 2 ^ 45 := by decide

#print axioms low_weight_base
#print axioms high_weight_base
#print axioms length_eleven_weight_seven

end CollatzEscapeBounds
