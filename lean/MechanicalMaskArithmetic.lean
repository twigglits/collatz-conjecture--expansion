/-
  Exact numerator arithmetic for independent 21-to-12 edits.
  Standalone Lean 4; no Mathlib or native evaluation.
  Check: lean lean/MechanicalMaskArithmetic.lean

  A token is either a single 2, or a disjoint pair initially equal to 21.
  The Boolean on a pair selects whether to change it to 12. The word need not
  be mechanical. The numerator and denominator agree with the definitions in
  CollatzCycleCriterion.lean; no logarithm or cycle-realization theorem is
  imported or asserted here. A nonnegative denominator hypothesis is explicit
  wherever natural subtraction is converted to an exact identity.
-/

namespace MechanicalMaskArithmetic

abbrev Token := Option Bool

def base : List Token → List Nat
  | [] => []
  | none :: ts => 2 :: base ts
  | some _ :: ts => 2 :: 1 :: base ts

def mask : List Token → List Nat
  | [] => []
  | none :: ts => 2 :: mask ts
  | some false :: ts => 2 :: 1 :: mask ts
  | some true :: ts => 1 :: 2 :: mask ts

def flipped : List Token → List Nat
  | [] => []
  | none :: ts => 2 :: flipped ts
  | some _ :: ts => 1 :: 2 :: flipped ts

def weight : List Nat → Nat
  | [] => 0
  | h :: tail => 3 ^ tail.length + 2 ^ h * weight tail

def denominator (ts : List Token) : Nat :=
  2 ^ (base ts).sum - 3 ^ (base ts).length

/-- Sum of all edit coefficients. Moving past a token multiplies every
    later coefficient by 2 to that token's halving sum. -/
def totalCoefficients : List Token → Nat
  | [] => 0
  | none :: ts => 4 * totalCoefficients ts
  | some _ :: ts => 2 * 3 ^ (base ts).length + 8 * totalCoefficients ts

/-- The same coefficient sum, restricted to selected pair tokens. -/
def selectedCoefficients : List Token → Nat
  | [] => 0
  | none :: ts => 4 * selectedCoefficients ts
  | some false :: ts => 8 * selectedCoefficients ts
  | some true :: ts => 2 * 3 ^ (base ts).length + 8 * selectedCoefficients ts

def C (ts : List Token) : Nat := weight (base ts) - weight (flipped ts)
def X (ts : List Token) : Nat := weight (base ts) - weight (mask ts)

theorem mask_length (ts : List Token) : (mask ts).length = (base ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t with
    | none => simpa [mask, base] using ih
    | some b => cases b <;> simp [mask, base, ih]

theorem flipped_length (ts : List Token) :
    (flipped ts).length = (base ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [flipped, base, ih]

theorem mask_sum (ts : List Token) : (mask ts).sum = (base ts).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t with
    | none => simp [mask, base, ih]
    | some b => cases b <;> simp [mask, base, ih] <;> omega

theorem flipped_sum (ts : List Token) : (flipped ts).sum = (base ts).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [flipped, base, ih] <;> omega

theorem base_append_two (ts : List Token) : base ts ++ [2] = 2 :: flipped ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [base, flipped, ih]

/-- Flipping every pair is exactly the left rotation by one halving symbol.
    This includes the empty word, whose rotation is empty. -/
theorem flipped_is_rotation (ts : List Token) :
    flipped ts = (base ts).drop 1 ++ (base ts).take 1 := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    have hh := base_append_two ts
    cases t <;> simp [base, flipped, hh]

theorem weight_append (u v : List Nat) :
    weight (u ++ v) = 3 ^ v.length * weight u + 2 ^ u.sum * weight v := by
  induction u with
  | nil => simp [weight]
  | cons h u ih =>
    simp only [List.cons_append, weight, List.length_append, List.sum_cons,
      Nat.pow_add, ih]
    grind

theorem base_mask_balance (ts : List Token) :
    weight (base ts) = weight (mask ts) + selectedCoefficients ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | none => simp [base, mask, selectedCoefficients, weight, mask_length, ih]; omega
    | some b =>
      cases b <;>
        simp [base, mask, selectedCoefficients, weight, mask_length, ih,
          Nat.pow_succ] <;> omega

theorem base_flipped_balance (ts : List Token) :
    weight (base ts) = weight (flipped ts) + totalCoefficients ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;>
      simp [base, flipped, totalCoefficients, weight, flipped_length, ih,
        Nat.pow_succ] <;> omega

theorem X_eq_selected (ts : List Token) : X ts = selectedCoefficients ts := by
  unfold X
  rw [base_mask_balance]
  omega

theorem C_eq_total (ts : List Token) : C ts = totalCoefficients ts := by
  unfold C
  rw [base_flipped_balance]
  omega

theorem selected_le_total (ts : List Token) :
    selectedCoefficients ts ≤ totalCoefficients ts := by
  induction ts with
  | nil => exact Nat.le_refl _
  | cons t ts ih =>
    cases t with
    | none => simp [selectedCoefficients, totalCoefficients]; omega
    | some b => cases b <;> simp [selectedCoefficients, totalCoefficients] <;> omega

theorem X_bounds (ts : List Token) : 0 ≤ X ts ∧ X ts ≤ C ts := by
  rw [X_eq_selected, C_eq_total]
  exact ⟨Nat.zero_le _, selected_le_total ts⟩

/-- An addition-only rotation identity, valid even when the natural
    denominator would truncate. -/
theorem rotation_balance (ts : List Token) :
    4 * weight (flipped ts) + 3 ^ (base ts).length =
      3 * weight (base ts) + 2 ^ (base ts).sum := by
  have hh := congrArg weight (base_append_two ts)
  simp [weight_append, weight, flipped_length] at hh
  omega

theorem rotation_denominator (ts : List Token)
    (hD : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum) :
    4 * weight (flipped ts) = 3 * weight (base ts) + denominator ts := by
  have hh := rotation_balance ts
  unfold denominator
  omega

theorem base_normal_form (ts : List Token)
    (hD : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum) :
    weight (base ts) = denominator ts + 4 * C ts := by
  have hr := rotation_denominator ts hD
  have hb := base_flipped_balance ts
  rw [← C_eq_total] at hb
  omega

theorem mask_normal_form (ts : List Token)
    (hD : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum) :
    weight (mask ts) + X ts = denominator ts + 4 * C ts := by
  have hb := base_mask_balance ts
  rw [← X_eq_selected] at hb
  rw [← hb, base_normal_form ts hD]

/-- Every edited numerator is D plus the nonnegative quantity 4C-X.
    Thus the final subtraction has no lost negative part. -/
theorem mask_exact_difference (ts : List Token)
    (hD : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum) :
    weight (mask ts) = denominator ts + (4 * C ts - X ts) := by
  have hn := mask_normal_form ts hD
  have hx := X_bounds ts
  omega

theorem mask_divisibility_iff (ts : List Token)
    (hD : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum) :
    denominator ts ∣ weight (mask ts) ↔ denominator ts ∣ 4 * C ts - X ts := by
  rw [mask_exact_difference ts hD]
  exact (Nat.dvd_add_iff_right (Nat.dvd_refl _)).symm

theorem base_append (pre post : List Token) :
    base (pre ++ post) = base pre ++ base post := by
  induction pre with
  | nil => rfl
  | cons t pre ih => cases t <;> simp [base, ih]

/-- Selected coefficients split across any token boundary. Coefficients in
    the prefix acquire one factor 3 per suffix symbol; coefficients in the
    suffix acquire one factor 2 per halving in the prefix. -/
theorem selected_append (pre post : List Token) :
    selectedCoefficients (pre ++ post) =
      3 ^ (base post).length * selectedCoefficients pre +
      2 ^ (base pre).sum * selectedCoefficients post := by
  induction pre with
  | nil => simp [selectedCoefficients, base]
  | cons t pre ih =>
    cases t with
    | none =>
      simp [selectedCoefficients, base, ih, Nat.pow_add]
      grind
    | some b =>
      cases b <;>
        simp [selectedCoefficients, base, base_append, ih, Nat.pow_add] <;> grind

/-- Toggling a single specified pair adds exactly its positive monomial,
    independently of every other selection. -/
theorem selected_pair_coefficient (pre post : List Token) :
    X (pre ++ some true :: post) = X (pre ++ some false :: post) +
      2 ^ (base pre).sum * 2 * 3 ^ (base post).length := by
  simp only [X_eq_selected, selected_append]
  simp [base, selectedCoefficients]
  grind

#print axioms flipped_is_rotation
#print axioms base_mask_balance
#print axioms base_normal_form
#print axioms mask_divisibility_iff
#print axioms selected_pair_coefficient

end MechanicalMaskArithmetic
