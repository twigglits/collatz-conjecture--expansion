/-
  Arithmetic supporting joint clock/coefficient moments of lower returns.
  Fractional powers, probability, Holder, concentration and Lp norms
  remain written in docs/LOWER-RETURN-CLOCK-MOMENTS.md.
-/
import AllReturnLowerEnergy

namespace LowerReturnClockMoments
open CollatzAffine CoalescenceTail ReturnCorrectionMoments ReturnAffineBudget
open LowerReturnEnergy

theorem lower_augmented_le_first (t n : Nat) :
    lowerAugmented t n ≤ augmented t n := by
  exact Nat.min_le_left _ _

theorem lower_augmented_lift (t q n : Nat) :
    lowerAugmented t (2 ^ t * q + n) = lowerAugmented t n := by
  simp only [lowerAugmented, Nat.add_assoc, weight_lift, numerator_lift]

theorem selected_endpoint_count (t n a e : Nat)
    (he : e ≤ 1) (h0 : wt t n = a) (h1 : wt t (n + 1) = a) :
    wt t (n + e) = a := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [Nat.add_zero] using h0
  · exact h1

/-- Sum the two parts of the group-duration cost, with common denominators. -/
theorem group_duration_budget (vpart tpart cost m p z l l2 f : Nat)
    (hv : 8 * vpart ≤ 4 * m + 49 * l2 + 10 * l)
    (ht : 8 * tpart ≤ 108 * p + 27 * l + 1432 * z + 8 * f)
    (hc : cost ≤ vpart + tpart)
    (hl : l ≤ 8 * z) (hl2 : l2 ≤ 64 * z) :
    8 * cost ≤ 4 * m + 108 * p + 4864 * z + 8 * f := by omega

/-- Finite drift algebra for P times the total elapsed clock to power q. -/
theorem clocked_minimum_budget (h f : Nat) (R L T M P Z Q : Nat → Nat)
    (hd : ∀ j < h, 8 * R (j + 1) ≤ 4 * R j + 49 * L j +
      10 * T j + 4 * M j + 108 * P j + 4864 * Z j + 8 * f * Q j) :
    4 * total h R + 8 * R h ≤
      8 * R 0 + 49 * total h L + 10 * total h T + 4 * total h M +
      108 * total h P + 4864 * total h Z + 8 * f * total h Q := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total, Nat.mul_add]
    omega

/-- If alpha=a/d<1/3, q=(d+3a)/(4d) lies between 3alpha/2 and 1/2. -/
theorem power_window (a d : Nat) (ha : 3 * a < d) :
    6 * a < d + 3 * a ∧ d + 3 * a < 2 * d ∧ 0 < d - 3 * a := by
  omega

/-- The exceptional-count exponent (17alpha-8)/(1+alpha) is below -1. -/
theorem atypical_window (a d : Nat) (ha : 3 * a < d) :
    18 * a < 7 * d := by omega

#print axioms lower_augmented_le_first
#print axioms lower_augmented_lift
#print axioms selected_endpoint_count
#print axioms group_duration_budget
#print axioms clocked_minimum_budget
#print axioms power_window
#print axioms atypical_window

end LowerReturnClockMoments
