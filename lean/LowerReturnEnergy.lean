/-
  Arithmetic for the lower endpoint at grouped count returns.
  Fractional moments, stopping, logarithms and Haar energy remain written
  in docs/LOWER-RETURN-ENERGY.md.
-/
import ReturnAffineBudget
import ReturnSlopeTilt

namespace LowerReturnEnergy
open CollatzAffine CoalescenceTail ReturnCorrectionMoments ReturnAffineBudget

/-- Common denominator 2^t; the two formal starting values are one and two. -/
def lowerAugmented (t n : Nat) : Nat :=
  min (3 ^ wt t n + numerator t n)
      (2 * 3 ^ wt t (n + 1) + numerator t (n + 1))

theorem lower_formal_identity (t n a : Nat)
    (h0 : wt t n = a) (h1 : wt t (n + 1) = a) :
    2 ^ t * min (orbit t n) (orbit t (n + 1)) + 3 ^ a =
      3 ^ a * n + lowerAugmented t n := by
  have e0 := orbit_equation t n
  have e1 := orbit_equation t (n + 1)
  rw [h0] at e0
  rw [h1, Nat.mul_add, Nat.mul_one] at e1
  simp only [lowerAugmented, h0, h1]
  rcases Nat.le_total (orbit t n) (orbit t (n + 1)) with h | h
  · rw [Nat.min_eq_left h]
    have hm := Nat.mul_le_mul_left (2 ^ t) h
    have hc : 3 ^ a + numerator t n ≤
        2 * 3 ^ a + numerator t (n + 1) := by omega
    rw [Nat.min_eq_left hc]
    omega
  · rw [Nat.min_eq_right h]
    have hm := Nat.mul_le_mul_left (2 ^ t) h
    have hc : 2 * 3 ^ a + numerator t (n + 1) ≤
        3 ^ a + numerator t n := by omega
    rw [Nat.min_eq_right hc]
    omega

theorem lower_endpoint_augmented (t n a e : Nat)
    (he : e ≤ 1) (h0 : wt t n = a) (h1 : wt t (n + 1) = a)
    (hm : orbit t (n + e) = min (orbit t n) (orbit t (n + 1))) :
    augmented t (n + e) ≤ lowerAugmented t n := by
  have h := lower_formal_identity t n a h0 h1
  have ee := orbit_equation t (n + e)
  have hp : 0 < 3 ^ a := Nat.pow_pos (by decide)
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simp only [Nat.add_zero] at *
    rw [h0, hm] at ee
    simp only [augmented, h0]
    omega
  · rw [h1, hm, Nat.mul_add, Nat.mul_one] at ee
    simp only [augmented, h1]
    omega

theorem selected_even_source_injective (r s e f : Nat)
    (hr : r % 2 = 0) (hs : s % 2 = 0)
    (he : e ≤ 1) (hf : f ≤ 1) (h : r + e = s + f) : r = s := by
  omega

theorem selected_even_source_in_period (m r e : Nat)
    (hm : m % 2 = 0) (hr : r % 2 = 0)
    (hlt : r < m) (he : e ≤ 1) : r + e < m := by
  omega

theorem lower_continuation_bound (p d s f : Nat) :
    min (p + s) (p + d + f) ≤ p + f + min s d := by
  omega

theorem root_chord_endpoints :
    128 ^ 2 < 2 * 91 ^ 2 ∧
    3 * 128 ^ 2 < 2 * 157 ^ 2 ∧ 91 + 157 = 248 := by decide

/-- Finite geometric sums for the reciprocal-slope perpetuity estimate. -/
def geometricNumerator (h r s : Nat) : Nat :=
  match h with
  | 0 => 0
  | h + 1 => s * geometricNumerator h r s + r ^ h

theorem geometric_numerator_identity (h r s : Nat) :
    s * geometricNumerator h r s + r ^ h =
      r * geometricNumerator h r s + s ^ h := by
  induction h with
  | zero => simp [geometricNumerator]
  | succ h ih =>
    simp only [geometricNumerator, Nat.pow_succ]
    grind

theorem grouped_minimum_drift (p pb l lb v q pn : Nat)
    (hp : 4 * pb ≤ 4 * p + v)
    (hv : v ≤ l) (hl : lb ≤ l)
    (hn : 4 * pn ≤ 2 * pb + 24 * lb + 5 * q) :
    8 * pn ≤ 4 * p + 49 * l + 10 * q := by omega

theorem grouped_minimum_budget (h : Nat) (P L Q : Nat → Nat)
    (hd : ∀ j < h, 8 * P (j + 1) ≤
      4 * P j + 49 * L j + 10 * Q j) :
    4 * total h P + 8 * P h ≤
      8 * P 0 + 49 * total h L + 10 * total h Q := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total]
    omega

theorem lower_budget_constants (c q l p : Nat)
    (hq : q ≤ c) (hl : l ≤ 328 + 2880 * c)
    (hp : 4 * p ≤ 8 + 49 * l + 10 * q) :
    p ≤ 4100 + 36000 * c := by omega

theorem component_energy_budget (e p c : Nat)
    (he : e ≤ 2 * p) (hp : p ≤ 4100 + 36000 * c) :
    e ≤ 8200 + 72000 * c := by omega

#print axioms lower_formal_identity
#print axioms lower_endpoint_augmented
#print axioms selected_even_source_injective
#print axioms selected_even_source_in_period
#print axioms lower_continuation_bound
#print axioms root_chord_endpoints
#print axioms geometric_numerator_identity
#print axioms grouped_minimum_drift
#print axioms grouped_minimum_budget
#print axioms lower_budget_constants
#print axioms component_energy_budget

end LowerReturnEnergy
