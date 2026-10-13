/-
  Arithmetic for slope-weighted occupation of count returns.
  Tilted laws, conditioning, logarithms and infinite sums remain written.
-/
import ReturnSlopeTilt

namespace ReturnSlopeOccupation
open CollatzAffine CoalescenceTail EscapeWeightRefinements ReturnCorrectionMoments

/-- The all-odd word maximizes the affine correction at a fixed clock. -/
theorem numerator_cap (t n : Nat) : numerator t n + 2 ^ t ≤ 3 ^ t := by
  induction t with
  | zero => simp [numerator, orbit, wt]
  | succ t ih =>
    have hp : orbit t n % 2 = 0 ∨ orbit t n % 2 = 1 := by omega
    rw [numerator_snoc]
    rcases hp with hp | hp <;> simp only [hp, Nat.pow_zero,
      Nat.one_mul, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.pow_succ] <;> omega

/-- Common parity halves the separation, with an extra factor three if odd. -/
theorem common_step (n D : Nat) :
    U (n + 2 * D) = U n + 3 ^ (n % 2) * D := by
  have h := affine 1 D n
  simpa [orbit, wt, Nat.add_comm, Nat.add_left_comm] using h

theorem returned_right_bound (t n D : Nat)
    (ha : wt t n = wt t (n + D)) :
    2 ^ t * orbit t (n + D) + 2 ^ t ≤
      2 ^ t * orbit t n + 3 ^ t * (D + 1) := by
  have hx := numerator_cap t n
  have hy := numerator_cap t (n + D)
  have hc := Nat.pow_le_pow_right (by decide : 0 < 3) (weight_le_length t n)
  have hm := Nat.mul_le_mul_right D hc
  rw [orbit_equation, orbit_equation, ← ha]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

theorem returned_left_bound (t n D : Nat)
    (ha : wt t n = wt t (n + D)) :
    2 ^ t * orbit t n + 2 ^ t ≤
      2 ^ t * orbit t (n + D) + 3 ^ t * (D + 1) := by
  have hx := numerator_cap t n
  rw [orbit_equation, orbit_equation, ← ha]
  simp only [Nat.mul_add, Nat.mul_one]
  omega

def separation (x y : Nat) : Nat := x - y + (y - x)

/-- At equal counts, D_next+1 <= (3/2)^t (D+1). -/
theorem returned_separation_cap (t n D : Nat)
    (ha : wt t n = wt t (n + D)) :
    2 ^ t * (separation (orbit t n) (orbit t (n + D)) + 1) ≤
      3 ^ t * (D + 1) := by
  have hl := returned_left_bound t n D ha
  have hr := returned_right_bound t n D ha
  simp only [separation, Nat.mul_add, Nat.mul_one, Nat.mul_sub] at hl hr ⊢
  omega

/-- Weighted geometric-mean comparison for the logarithmic zero-gap cost. -/
theorem logarithmic_step_polynomial (D : Nat) :
    (3 * D + 2) ^ 3 * (D + 2) + 18 * D ^ 2 + 28 * D + 11 =
      27 * (D + 1) ^ 4 := by grind

/-- This gives log_2(3)<8/5 and log_2(3/2)<3/5. -/
theorem logarithmic_constants : 3 ^ 5 < 2 ^ 8 := by decide

/-- A simple majorant for the tilted holding tail after 3v steps. -/
theorem tilted_tail_shift (v h : Nat) :
    2 ^ v * 3 ^ (3 * v + h) ≤ 4 ^ (3 * v) * 3 ^ h := by
  have he : 2 ^ v * 3 ^ (3 * v) = 54 ^ v := by
    rw [Nat.pow_mul, ← Nat.mul_pow]
  have hc : 54 ^ v ≤ 64 ^ v := Nat.pow_le_pow_left (by decide) v
  have hf : 4 ^ (3 * v) = 64 ^ v := by rw [Nat.pow_mul]
  rw [Nat.pow_add, ← Nat.mul_assoc, he, hf]
  exact Nat.mul_le_mul_right _ hc

/-- Source equation for the finite inward-biased Green row from one. -/
theorem inward_green_source (K : Nat) (hK : 2 ≤ K) :
    4 * (4 * (3 ^ (K - 1) - 1)) =
      3 * (4 * (3 ^ (K - 2) - 1)) + 4 * (3 ^ K - 1) := by
  have h0 : K - 1 = (K - 2) + 1 := by omega
  have h1 : K = (K - 2) + 2 := by omega
  have hp : 0 < 3 ^ (K - 2) := Nat.pow_pos (by decide)
  have he0 : 3 ^ (K - 1) = 3 ^ (K - 2) * 3 := by rw [h0, Nat.pow_succ]
  have he1 : 3 ^ K = 3 ^ (K - 2) * 9 := by
    calc
      3 ^ K = 3 ^ ((K - 2) + 2) := congrArg (fun j => 3 ^ j) h1
      _ = _ := by rw [Nat.pow_add]
  rw [he0, he1]
  omega

/-- Initial departure plus the partial Green holding cost is at most 27. -/
theorem tilted_clock_budget (H : Nat) :
    3 ^ H + 4 * ReturnSlopeTilt.fastCost H ≤ 27 * 3 ^ H := by
  have h := ReturnSlopeTilt.fast_cost_identity H
  omega

theorem macro_drift_budget (h : Nat) (L Q : Nat → Nat)
    (hd : ∀ j < h, 10 * L (j + 1) ≤ 6 * L j + 81 * Q j) :
    4 * total h L + 10 * L h ≤ 10 * L 0 + 81 * total h Q := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total]
    omega

theorem macro_mass_budget (h : Nat) (Q : Nat → Nat)
    (hd : ∀ j < h, 2 * Q (j + 1) ≤ Q j) :
    total h Q + 2 * Q h ≤ 2 * Q 0 := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total]
    omega

/-- The final 44 and 70 constants, with arbitrary common denominator q. -/
theorem occupation_constants (q mass logs returns ages : Nat)
    (hm : mass ≤ 2 * q)
    (hl : 4 * logs ≤ 10 * q + 81 * mass)
    (hr : 2 * returns ≤ 2 * logs + mass)
    (ha : 2 * ages ≤ 2 * logs + 27 * mass) :
    logs ≤ 43 * q ∧ returns ≤ 44 * q ∧ ages ≤ 70 * q := by omega

#print axioms numerator_cap
#print axioms common_step
#print axioms returned_right_bound
#print axioms returned_left_bound
#print axioms returned_separation_cap
#print axioms logarithmic_step_polynomial
#print axioms logarithmic_constants
#print axioms tilted_tail_shift
#print axioms inward_green_source
#print axioms tilted_clock_budget
#print axioms macro_drift_budget
#print axioms macro_mass_budget
#print axioms occupation_constants

end ReturnSlopeOccupation
