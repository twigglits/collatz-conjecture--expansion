/-
  Exact returned-endpoint and squared-gap inputs for the obstruction to
  uniform complementary exponential moments. Real norms and limits remain
  written in docs/GRADIENT-ORLICZ-OBSTRUCTION.md.
-/
import ReturnOccupationDensity

namespace GradientOrliczObstruction
open CollatzAffine CoalescenceTail EscapeWeightRefinements
open OrderedWeightDrift ReversalPersistence ReturnOccupationDensity

theorem image_scale_mod_nine (m : Nat) : 2 ^ (12 * m + 6) % 9 = 1 := by
  have he : 12 * m + 6 = 6 * (2 * m + 1) := by omega
  rw [he, Nat.pow_mul]
  simp [Nat.pow_mod]

/-- The persistent endpoint is in the actual returned progression and interval. -/
theorem family_image_location (m : Nat) :
    let Q := 2 ^ (12 * m + 6)
    let q := 16 * (Q / 9) + 1
    Q ≤ q ∧ q < 2 * Q ∧ 9 * q + 8 = 16 * Q + 1 ∧
      9 * Q + 8 ≤ 16 * Q + 1 ∧ 16 * Q + 1 < 18 * Q + 8 := by
  dsimp
  have hm := image_scale_mod_nine m
  have hd := Nat.mod_add_div (2 ^ (12 * m + 6)) 9
  omega

theorem returned_scale_identity (m h : Nat) :
    (9 * 2 ^ (12 * m + 6)) * 2 ^ (h + 6) = 9 * 2 ^ (12 * m + 12 + h) := by
  rw [Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  omega

theorem returned_parent_half (m h : Nat) (hh : h ≤ 6 * m + 1) :
    2 ^ (h + 5) * orbit (12 * m + 12 + h) (2 ^ (12 * m + 10) + 1) ≤
      9 * 3 ^ wt (12 * m + 12 + h) (2 ^ (12 * m + 10) + 1) := by
  have hs := family_seed_equation (2 * m + 1)
  have he : 2 * (3 * (2 * m + 1) + 2) = 12 * m + 10 := by omega
  rw [he] at hs
  have hf := family_first_five hs
  have hp := family_persistent_half m h hh
  dsimp at hp
  have ht : 12 * m + 17 + h = 5 + (12 * m + 12 + h) := by omega
  rw [ht, orbit_add, weight_add, hf.1, hf.2] at hp
  simpa only [Nat.pow_add] using hp

theorem returned_child_ceiling (m h : Nat) :
    3 ^ wt (12 * m + 12 + h) (2 ^ (12 * m + 10)) ≤
      3 * (2 ^ h * orbit (12 * m + 12 + h) (2 ^ (12 * m + 10))) := by
  have hz := halving_data (12 * m + 10) 1
  simp only [Nat.mul_one] at hz
  have ht : 12 * m + 12 + h = (12 * m + 10) + (2 + h) := by omega
  rw [ht, orbit_add, weight_add, hz.1, hz.2, Nat.zero_add, orbit_add, weight_add]
  have ho : orbit 2 1 = 1 := by decide
  have hw : wt 2 1 = 1 := by decide
  rw [ho, hw, Nat.pow_add, Nat.pow_one]
  have hc := Nat.mul_le_mul_left 3 (coefficient_lower_bound h 1)
  simpa only [Nat.mul_one] using hc

/-- If p/u >= 1/2 and q/v <= 27/64, their difference is >= 5/64. -/
theorem gap_cross_product (p u q v : Nat) (hp : u ≤ 2 * p) (hq : 64 * q ≤ 27 * v) :
    5 * (u * v) ≤ 64 * (p * v - q * u) := by
  have h1 := Nat.mul_le_mul_right (32 * v) hp
  have h2 := Nat.mul_le_mul_right u hq
  have e1 : u * (32 * v) = 32 * (u * v) := by ac_rfl
  have e2 : 2 * p * (32 * v) = 64 * (p * v) := by grind
  have e3 : 64 * q * u = 64 * (q * u) := by ac_rfl
  have e4 : 27 * v * u = 27 * (u * v) := by ac_rfl
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [Nat.mul_sub_left_distrib]
  omega

theorem squared_gap_cross_product (p u q v : Nat)
    (hp : u ≤ 2 * p) (hq : 64 * q ≤ 27 * v) :
    25 * (u * v) ^ 2 ≤ 4096 * (p * v - q * u) ^ 2 := by
  have hh := Nat.pow_le_pow_left (gap_cross_product p u q v hp hq) 2
  simpa only [Nat.mul_pow] using hh

/-- A large exact example for the written unscaled quadratic-exponential bound. -/
theorem quadratic_exponential_witness :
    (25 * (6 * 16384 + 2)) ^ 2 >
      4096 ^ 2 * (12 * 16384 + 9 + 100000) := by decide

#print axioms image_scale_mod_nine
#print axioms family_image_location
#print axioms returned_scale_identity
#print axioms returned_parent_half
#print axioms returned_child_ceiling
#print axioms gap_cross_product
#print axioms squared_gap_cross_product
#print axioms quadratic_exponential_witness

end GradientOrliczObstruction
