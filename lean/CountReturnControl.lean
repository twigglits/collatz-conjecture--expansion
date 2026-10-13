/-
  Exact restart accounting and deterministic descent at count returns.
  The probability estimates, fractional moments, and energy application
  are written arguments in docs/COUNT-RETURN-CONTROL.md, not Lean proofs.
-/
import EscapeWeightRefinements

namespace CountReturnControl
open CollatzAffine CoalescenceTail EscapeWeightRefinements

def rawGap (k n : Nat) : Nat := (gap k n).natAbs

def restart (k n : Nat) : Nat :=
  if gap k n = 0 ∧ orbit k n % 2 ≠ orbit k (n + 1) % 2 then 1 else 0

theorem absolute_pair_restart (d : Int) (a b : Nat) (ha : a ≤ 1) (hb : b ≤ 1) :
    (d + a - b).natAbs + (d + (1 - a : Nat) - (1 - b : Nat)).natAbs =
      2 * d.natAbs + 2 * (if d = 0 ∧ a ≠ b then 1 else 0) := by
  by_cases hd : d = 0
  · subst d
    have haa : a = 0 ∨ a = 1 := by omega
    have hbb : b = 0 ∨ b = 1 := by omega
    rcases haa with rfl | rfl <;> rcases hbb with rfl | rfl <;> decide
  · simp only [hd, false_and, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    exact absolute_pair d a b hd ha hb

theorem raw_children (k n : Nat) :
    rawGap (k + 1) n + rawGap (k + 1) (2 ^ k + n) =
      2 * rawGap k n + 2 * restart k n := by
  unfold rawGap restart
  rw [gap_snoc, gap_snoc_lift]
  exact absolute_pair_restart _ _ _ (by omega) (by omega)

theorem raw_mass_recurrence (k : Nat) :
    total (2 ^ (k + 1)) (rawGap (k + 1)) =
      2 * total (2 ^ k) (rawGap k) + 2 * total (2 ^ k) (restart k) := by
  rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
  have he := total_ext (2 ^ k)
    (fun r => rawGap (k + 1) r + rawGap (k + 1) (2 ^ k + r))
    (fun r => 2 * rawGap k r + 2 * restart k r)
    (fun r _ => raw_children k r)
  rw [he, total_sum, total_mul, total_mul]

/-- The coefficient controlling holding times has valuation less than 2d. -/
theorem holding_coefficient_bound (d : Nat) (hd : 0 < d) :
    0 < 3 ^ d - 1 ∧ 3 ^ d - 1 < 2 ^ (2 * d) := by
  have hp : 1 < 3 ^ d := Nat.one_lt_pow (by omega) (by decide)
  have hq : 3 ^ d < 4 ^ d := Nat.pow_lt_pow_left (by decide) (by omega)
  have he : 4 ^ d = 2 ^ (2 * d) := by rw [Nat.pow_mul]
  rw [he] at hq
  omega

theorem balanced_even_transition {x D : Nat} (hx : x % 2 = 0) (hD : D % 2 = 0) :
    U (x + D) = U x + D / 2 := by
  have hy : (x + D) % 2 = 0 := by omega
  simp [U, hx, hy]
  omega

theorem balanced_odd_departure {x D : Nat} (hx : x % 2 = 0) (hD : D % 2 = 1) :
    (x + D) % 2 = 1 ∧ U (x + D) = 3 * U x + (3 * D + 1) / 2 := by
  have hy : (x + D) % 2 = 1 := by omega
  constructor
  · exact hy
  · simp [U, hx, hy]
    omega

theorem positive_even_hold {x c : Nat} (hx : x % 2 = 0) (hc : c % 2 = 0) :
    (3 * x + c) % 2 = 0 ∧ U (3 * x + c) = 3 * U x + c / 2 := by
  have hy : (3 * x + c) % 2 = 0 := by omega
  constructor
  · exact hy
  · simp [U, hx, hy]
    omega

theorem positive_odd_return {x c : Nat} (hx : x % 2 = 1) (hc : c % 2 = 1) :
    (3 * x + c) % 2 = 0 ∧ U (3 * x + c) = U x + (c - 1) / 2 := by
  have hy : (3 * x + c) % 2 = 0 := by omega
  constructor
  · exact hy
  · simp [U, hx, hy]
    omega

theorem odd_return_descent {D c : Nat} (hD : D % 2 = 1)
    (hc : c % 2 = 1) (hb : c ≤ (3 * D + 1) / 2) :
    (c - 1) / 2 < D ∧ 4 * ((c - 1) / 2) ≤ 3 * D - 1 := by omega

theorem even_return_descent {D : Nat} (hp : 0 < D) (he : D % 2 = 0) :
    D / 2 < D ∧ 4 * (D / 2) ≤ 3 * D := by omega

/-- Integer comparisons used to bound the real fractional-moment constants. -/
theorem fractional_constant_checks :
    3 * 256 ^ 2 < 449 ^ 2 ∧
    256 ^ 16 < 2 * 246 ^ 16 ∧
    3 * 256 ^ 16 < 2 * 263 ^ 16 ∧
    51 ^ 20 < 2 * 50 ^ 20 ∧ 246 + 263 = 509 ∧ 509 < 512 := by decide

set_option exponentiation.threshold 512 in
theorem return_budget_constants :
    3 * 1093120 = 512 * 6405 ∧
    3 * (2186070 - 1093120) > 6404 * 512 ∧
    1093120 ^ 16 < 2 ^ 336 ∧
    3 ^ 4 < 2 ^ 7 ∧
    4 * 336 = 1344 ∧ 1344 * 338 = 454272 ∧
    1344 + 2186070 = 2187414 := by decide

#print axioms absolute_pair_restart
#print axioms raw_children
#print axioms raw_mass_recurrence
#print axioms holding_coefficient_bound
#print axioms balanced_even_transition
#print axioms balanced_odd_departure
#print axioms positive_even_hold
#print axioms positive_odd_return
#print axioms odd_return_descent
#print axioms even_return_descent
#print axioms fractional_constant_checks
#print axioms return_budget_constants

end CountReturnControl
