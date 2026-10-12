/-
  Integer inputs for the written norm and essential spectral radius calculation
  of killed Collatz composition on l1(n^(-s)), s > 1.
  The Banach space, infinite sums, real powers, and spectral statements are NOT
  formalized here. No survivor-mass decay or Collatz conclusion is asserted.
-/
import EqualWeightFibres
import WeightedBasinBarrier

namespace KilledOperatorBounds

open CollatzPacking

theorem mixed_power_bound (k j : Nat) (hj : j ≤ k) :
    3 ^ j * 2 ^ (k - j) ≤ 3 ^ k := by
  have h := Nat.mul_le_mul_left (3 ^ j)
    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (k - j))
  simpa only [← Nat.pow_add, Nat.add_sub_of_le hj] using h

/-- A uniform additive error for conversion from coefficients to source weights. -/
theorem source_coefficient_error (k n : Nat) :
    2 ^ k * orbit k n ≤ 3 ^ wt k n * n + 3 ^ k := by
  have h := shifted_upper k n
  have he := mixed_power_bound k (wt k n) (weight_le_length k n)
  have h0 := Nat.mul_le_mul_left (2 ^ k) (Nat.le_add_right (orbit k n) 1)
  apply Nat.le_trans (Nat.le_trans h0 h)
  simpa only [Nat.mul_add] using Nat.add_le_add_left he (3 ^ wt k n * n)

/-- Above this target threshold, the actual source weight is at most 2^s
    times the affine coefficient weight, after division by the target weight. -/
theorem large_target_comparison (k n : Nat)
    (hy : 2 * 3 ^ k ≤ 2 ^ k * orbit k n) :
    2 ^ k * orbit k n ≤ 2 * (3 ^ wt k n * n) := by
  have h := source_coefficient_error k n
  omega

theorem global_image_bound (k n : Nat) :
    2 ^ k * orbit k n ≤ 3 ^ k * (n + 1) := by
  have h := source_coefficient_error k n
  have hw := Nat.mul_le_mul_right n
    (Nat.pow_le_pow_right (by decide : 0 < 3) (weight_le_length k n))
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- For fixed k, inverse fibres of targets tending to infinity leave every
    bounded source interval. This does not assume any convergence theorem. -/
theorem target_forces_source_escape (k B n : Nat)
    (hy : 3 ^ k * (B + 1) < 2 ^ k * orbit k n) : B < n := by
  have h := global_image_bound k n
  have ht : 3 ^ k * (B + 1) < 3 ^ k * (n + 1) := Nat.lt_of_lt_of_le hy h
  have := Nat.lt_of_mul_lt_mul_left ht
  omega

theorem orbit_bridge : ∀ k n,
    orbit k n = OrdinaryCollatz.shortcutIter k n
  | 0, _ => rfl
  | k + 1, n => by
    simpa only [orbit, OrdinaryCollatz.shortcutIter, U, OrdinaryCollatz.U]
      using orbit_bridge k (U n)

/-- Arbitrarily far out, every power of the killed operator has a column
    containing the full all-odd growth factor. -/
theorem growing_column (H k B : Nat) :
    ∃ x y, B < x ∧ B < y ∧ WeightedSurvivors.Survives H k x ∧
      orbit k x = y ∧ 3 ^ k * x ≤ 2 ^ k * y := by
  let q := H + B + 2
  let x := 2 ^ k * q - 1
  let y := 3 ^ k * q - 1
  have hq : 0 < q := by omega
  have hp2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hp3 : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by decide)
  have hqx : q ≤ 2 ^ k * q := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right q hp2
  have hqy : q ≤ 3 ^ k * q := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right q hp3
  have hx : H < x := by dsimp [x, q] at *; omega
  have hxb : B < x := by dsimp [x, q] at *; omega
  have hyb : B < y := by dsimp [y, q] at *; omega
  refine ⟨x, y, hxb, hyb, ?_, ?_, ?_⟩
  · intro i hi
    exact Nat.lt_of_lt_of_le hx
      (WeightedBasinBarrier.growth_prefix_lower k i q hq hi)
  · rw [orbit_bridge, WeightedBasinBarrier.growth_bridge]
    simpa only [x, y, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
      using CollatzGrowth.growth_formula k 0 q hq
  · have he : 3 ^ k * (x + 1) = 2 ^ k * (y + 1) := by
      have hx' : x + 1 = 2 ^ k * q := by dsimp [x]; omega
      have hy' : y + 1 = 3 ^ k * q := by dsimp [y]; omega
      rw [hx', hy']
      ac_rfl
    have hp : 2 ^ k ≤ 3 ^ k := Nat.pow_le_pow_left (by decide) k
    simp only [Nat.mul_add, Nat.mul_one] at he
    omega

/-- The growing columns can all use targets that are powers of two.
    Each selected source has an explicit path to one, at every K >= 7. -/
theorem convergent_column (K : Nat) (hK : 7 ≤ K) :
    ∃ q, 0 < q ∧ 3 ^ K * q = 2 ^ (3 ^ (K - 1)) + 1 ∧
      WeightedSurvivors.Survives 64 K (2 ^ K * q - 1) ∧
      orbit K (2 ^ K * q - 1) = 2 ^ (3 ^ (K - 1)) ∧
      OrdinaryCollatz.shortcutIter (K + 3 ^ (K - 1)) (2 ^ K * q - 1) = 1 ∧
      3 ^ K * (2 ^ K * q - 1) ≤ 2 ^ K * 2 ^ (3 ^ (K - 1)) := by
  obtain ⟨q, hq, ht⟩ := WeightedBasinBarrier.power_target_quotient (K - 1)
  have hk : K - 1 + 1 = K := by omega
  rw [hk] at ht
  have hp : 2 ^ 7 ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK
  have hm : 2 ^ K ≤ 2 ^ K * q := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ K) hq
  have hx : 64 < 2 ^ K * q - 1 := by omega
  refine ⟨q, hq, ht, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact Nat.lt_of_lt_of_le hx
      (WeightedBasinBarrier.growth_prefix_lower K i q hq hi)
  · rw [orbit_bridge]
    exact WeightedBasinBarrier.growth_to_power K _ q hq ht
  · exact WeightedBasinBarrier.growth_hits_one K _ q hq ht
  · exact WeightedBasinBarrier.growth_ratio K _ q hq ht

theorem cubic_ratio (k x y : Nat) (h : 3 ^ k * x ≤ 2 ^ k * y) :
    27 ^ k * x ^ 3 ≤ 8 ^ k * y ^ 3 := by
  have ht := Nat.pow_le_pow_left h 3
  have h3 : (3 ^ k) ^ 3 = 27 ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm k 3, Nat.pow_mul]
  have h2 : (2 ^ k) ^ 3 = 8 ^ k := by
    rw [← Nat.pow_mul, Nat.mul_comm k 3, Nat.pow_mul]
  simpa only [Nat.mul_pow, h3, h2] using ht

/-- These support the written constant 5 and the divergent spike example. -/
theorem numerical_constants :
    8 < 3 ^ 2 ∧ 5 ^ 2 < 27 ∧ 128 < 243 ∧ 4 * 3 ^ 7 * 4096 = 2187 * 4 ^ 7 := by
  decide

#print axioms mixed_power_bound
#print axioms source_coefficient_error
#print axioms large_target_comparison
#print axioms global_image_bound
#print axioms target_forces_source_escape
#print axioms orbit_bridge
#print axioms growing_column
#print axioms convergent_column
#print axioms cubic_ratio
#print axioms numerical_constants

end KilledOperatorBounds
