/-
  Arithmetic for logarithmic slope occupation and comparable-source overlaps.
  Infinite stopping, logarithms, Haar energy, and the probability law remain
  written in docs/RETURN-ANCESTRAL-OVERLAP.md.
-/
import ReturnSlopeOccupation

namespace ReturnAncestralOverlap
open CoalescenceTail

def clockPotential (k : Nat) : Nat := 6 * k ^ 2 + 20 * k

theorem clock_potential_curvature (k : Nat) (hk : 0 < k) :
    4 * clockPotential k =
      3 * clockPotential (k - 1) + clockPotential (k + 1) + 4 * (6 * k + 4) := by
  cases k with
  | zero => omega
  | succ k => simp only [clockPotential, Nat.add_sub_cancel]; grind

def geometricSecond : Nat → Nat
  | 0 => 0
  | H + 1 => 4 * geometricSecond H + 4 * (2 * H + 1) * 3 ^ H

theorem geometric_second_identity (H : Nat) :
    geometricSecond H + 4 * (2 * H + 7) * 3 ^ H = 28 * 4 ^ H := by
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [geometricSecond, Nat.pow_succ]
    grind

theorem holding_second_cap (v k : Nat) (h : v ≤ 2 * k) :
    9 * v ^ 2 + 24 * v + 28 ≤ 36 * k ^ 2 + 48 * k + 28 := by
  have hs := Nat.mul_self_le_mul_self h
  grind

def secondCost (k : Nat) : Nat :=
  72 * k ^ 3 + 468 * k ^ 2 + 616 * k + 236

theorem second_cost_identity (k : Nat) :
    secondCost k = 36 * k ^ 2 + 48 * k + 28 +
      2 * (6 * k + 4) * clockPotential (k + 1) := by
  simp only [secondCost, clockPotential]
  grind

def secondClockSum : Nat → Nat
  | 0 => 0
  | H + 1 => 3 * secondClockSum H + 4 * secondCost (H + 1)

theorem second_clock_series_identity (H : Nat) :
    secondClockSum H + 144 * H ^ 3 + 1584 * H ^ 2 + 5336 * H + 6316 =
      6316 * 3 ^ H := by
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [secondClockSum, secondCost, Nat.pow_succ]
    grind

theorem second_clock_constants (H : Nat) :
    secondClockSum H ≤ 6316 * 3 ^ H ∧ 1 + 2 * 26 + 6316 = 6369 := by
  have h := second_clock_series_identity H
  omega

theorem zero_log_square_cap (L v : Nat) (h : v ≤ L) :
    25 * L ^ 2 + 10 * v * L + v ^ 2 + 12 * v ≤
      36 * L ^ 2 + 12 * L := by
  have hs := Nat.mul_self_le_mul_self h
  have hm := Nat.mul_le_mul_right L h
  grind

theorem group_square_constants (m l q mb lb mn : Nat)
    (hm : 25 * mb ≤ 36 * m + 12 * l)
    (hl : 5 * lb ≤ 6 * l)
    (hn : 50 * mn ≤ 25 * mb + 810 * lb + 57321 * q) :
    50 * mn ≤ 36 * m + 984 * l + 57321 * q := by omega

theorem square_drift_budget (h : Nat) (M L Q : Nat → Nat)
    (hd : ∀ j < h, 50 * M (j + 1) ≤
      36 * M j + 984 * L j + 57321 * Q j) :
    14 * total h M + 50 * M h ≤
      50 * M 0 + 984 * total h L + 57321 * total h Q := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total]
    omega

theorem mixed_occupation_constants (q masses logs squares cost : Nat)
    (hm : masses ≤ 2 * q)
    (hl : logs ≤ 43 * q)
    (hs : 14 * squares ≤ 50 * q + 984 * logs + 57321 * masses)
    (hc : 10 * cost ≤ 11 * squares + logs + 420 * q) :
    squares ≤ 11215 * q ∧ cost ≤ 12383 * q := by omega

set_option exponentiation.threshold 512 in
/-- A kernel integer comparison for the logarithmic initial waiting bound. -/
theorem log_count_decay : 2 * 399 ^ 400 < 400 ^ 400 := by decide

theorem comparable_energy_constants (C diagonal nested logmass : Nat)
    (hd : diagonal ≤ 44)
    (hl : logmass ≤ 12383)
    (hn : nested ≤ (C + 2) * diagonal + 100 * logmass) :
    diagonal + 2 * nested ≤ 88 * C + 2476820 := by
  have hp := Nat.mul_le_mul_left (C + 2) hd
  omega

#print axioms clock_potential_curvature
#print axioms geometric_second_identity
#print axioms holding_second_cap
#print axioms second_cost_identity
#print axioms second_clock_series_identity
#print axioms second_clock_constants
#print axioms zero_log_square_cap
#print axioms group_square_constants
#print axioms square_drift_budget
#print axioms mixed_occupation_constants
#print axioms log_count_decay
#print axioms comparable_energy_constants

end ReturnAncestralOverlap
