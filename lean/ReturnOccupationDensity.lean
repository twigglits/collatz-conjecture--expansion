/-
  Arithmetic for all-return occupation densities and a geometric cycle tail.
  Probability, real moments, and image-density integrals remain written in
  docs/RETURN-OCCUPATION-DENSITY.md.
-/
import ReturnCorrectionMoments
import ReturnImageBounds

namespace ReturnOccupationDensity
open CollatzAffine CoalescenceTail EscapeWeightRefinements ReturnImageBounds

/-- A fixed first-return cylinder, with separation one and reversed endpoints. -/
theorem return_class (q : Nat) :
    orbit 6 (64 * q + 48) = 9 * q + 8 ∧
    orbit 6 (64 * q + 49) = 9 * q + 7 ∧
    wt 6 (64 * q + 48) = 2 ∧ wt 6 (64 * q + 49) = 2 ∧
    alive 5 (64 * q + 48) = true := by
  have hx := affine 6 q 48
  have hy := affine 6 q 49
  have ha := weight_lift 6 q 48
  have hb := weight_lift 6 q 49
  have hp := alive_lift 5 (2 * q) 48
  change orbit 6 (64 * q + 48) = 9 * q + 8 at hx
  change orbit 6 (64 * q + 49) = 9 * q + 7 at hy
  change wt 6 (64 * q + 48) = 2 at ha
  change wt 6 (64 * q + 49) = 2 at hb
  have he : 2 ^ 5 * (2 * q) + 48 = 64 * q + 48 := by omega
  rw [he] at hp
  change alive 5 (64 * q + 48) = true at hp
  exact ⟨hx, hy, ha, hb, hp⟩

theorem family_early_return (m : Nat) :
    let n := 16 * familySeed (2 * m + 1)
    orbit 6 n = 2 ^ (12 * m + 10) + 1 ∧
    orbit 6 (n + 1) = 2 ^ (12 * m + 10) ∧
    wt 6 n = 2 ∧ wt 6 (n + 1) = 2 ∧ alive 5 n = true := by
  dsimp
  have hs := family_seed_equation (2 * m + 1)
  have he : 2 * (3 * (2 * m + 1) + 2) = 12 * m + 10 := by omega
  rw [he] at hs
  have hd := Nat.mod_add_div (familySeed (2 * m + 1)) 4
  have hm := Nat.mod_lt (familySeed (2 * m + 1)) (by decide : 0 < 4)
  have hu : familySeed (2 * m + 1) = 4 * (familySeed (2 * m + 1) / 4) + 3 := by omega
  have hc := return_class (familySeed (2 * m + 1) / 4)
  have hn : 16 * familySeed (2 * m + 1) =
      64 * (familySeed (2 * m + 1) / 4) + 48 := by omega
  rw [hn]
  have hp : 9 * (familySeed (2 * m + 1) / 4) + 7 = 2 ^ (12 * m + 10) := by omega
  have h49 : 64 * (familySeed (2 * m + 1) / 4) + 48 + 1 =
      64 * (familySeed (2 * m + 1) / 4) + 49 := by omega
  rw [h49, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
  have h8 : 9 * (familySeed (2 * m + 1) / 4) + 8 =
      2 ^ (12 * m + 10) + 1 := by omega
  simp [hp, h8]

theorem weight_prefix_mono (s t n : Nat) (hst : s ≤ t) : wt s n ≤ wt t n := by
  have he : t = s + (t - s) := by omega
  rw [he, weight_add]
  omega

/-- The adjacent returned pair has no second count return throughout this interval. -/
theorem power_pair_no_return (a t : Nat) (ha : 2 ≤ a) (ht : 0 < t)
    (hb : t ≤ 3 * a - 2) : wt t (2 ^ (2 * a)) < wt t (2 ^ (2 * a) + 1) := by
  by_cases hsmall : t ≤ 2 * a
  · have hp : 2 ^ (2 * a) = 2 ^ t * 2 ^ (2 * a - t) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hz := (halving_data t (2 ^ (2 * a - t))).2
    rw [← hp] at hz
    have hm := weight_prefix_mono 1 t (2 ^ (2 * a) + 1) (by omega)
    have ho : (2 ^ (2 * a) + 1) % 2 = 1 := by
      have he : 2 * a = (2 * a - 1) + 1 := by omega
      rw [he, Nat.pow_succ]
      omega
    have hw : wt 1 (2 ^ (2 * a) + 1) = 1 := by simp [wt, ho]
    omega
  · have he : t = 2 * a + (t - 2 * a) := by omega
    have hx := lifted_one a
    have hy := halving_data (2 * a) 1
    simp only [Nat.mul_one] at hy
    rw [he, weight_add, weight_add, hx.1, hx.2, hy.1, hy.2]
    have hw := weight_le_length (t - 2 * a) 1
    omega

/-- Clearing denominators in the multiplicative drift outside V >= 400. -/
theorem geometric_drift_arithmetic (e v q : Nat)
    (hd : 40 * e ≤ 39 * v + 360 * q) (hv : 400 * q ≤ v) :
    400 * e ≤ 399 * v := by omega

theorem inverse_bernoulli_step (m a b : Nat) :
    (b - (m + 1) * a) * (b + a) ≤ b * (b - m * a) := by
  by_cases h : (m + 1) * a ≤ b
  · have h1 := Nat.sub_add_cancel h
    have hma : m * a ≤ b := by
      have h' : m * a + a ≤ b := by simpa [Nat.add_mul] using h
      omega
    have h2 := Nat.sub_add_cancel hma
    have he : (b - (m + 1) * a) * (b + a) + (m + 1) * a * a =
        b * (b - m * a) := by grind
    omega
  · have hz : b - (m + 1) * a = 0 := by omega
    rw [hz, Nat.zero_mul]
    exact Nat.zero_le _

theorem inverse_bernoulli (m a b : Nat) :
    (b - m * a) * (b + a) ^ m ≤ b ^ (m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc
      (b - (m + 1) * a) * (b + a) ^ (m + 1) =
          ((b - (m + 1) * a) * (b + a)) * (b + a) ^ m := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ (b * (b - m * a)) * (b + a) ^ m :=
        Nat.mul_le_mul_right _ (inverse_bernoulli_step m a b)
      _ = b * ((b - m * a) * (b + a) ^ m) := by ac_rfl
      _ ≤ b * b ^ (m + 1) := Nat.mul_le_mul_left b ih
      _ = b ^ (m + 1) * b := Nat.mul_comm _ _
      _ = b ^ (m + 1 + 1) := (Nat.pow_succ b (m + 1)).symm

theorem exponential_linearization (m a b : Nat) (hb : 0 < b)
    (hsmall : 2 * m * a ≤ b) :
    b * (b + a) ^ m ≤ (b + 2 * m * a) * b ^ m := by
  have hma : m * a ≤ b := by
    have h' : 2 * (m * a) ≤ b := by simpa [Nat.mul_assoc] using hsmall
    omega
  have h1 := Nat.sub_add_cancel hma
  have h2 := Nat.sub_add_cancel hsmall
  have he : (b + 2 * m * a) * (b - m * a) =
      b * b + m * a * (b - 2 * m * a) := by grind
  have hpoly : b * b ≤ (b + 2 * m * a) * (b - m * a) := by omega
  have hpow := inverse_bernoulli m a b
  have hh : b * (b * (b + a) ^ m) ≤ b * ((b + 2 * m * a) * b ^ m) := by
    calc
      b * (b * (b + a) ^ m) = (b * b) * (b + a) ^ m := by ac_rfl
      _ ≤ ((b + 2 * m * a) * (b - m * a)) * (b + a) ^ m := Nat.mul_le_mul_right _ hpoly
      _ = (b + 2 * m * a) * ((b - m * a) * (b + a) ^ m) := by ac_rfl
      _ ≤ (b + 2 * m * a) * b ^ (m + 1) := Nat.mul_le_mul_left _ hpow
      _ = b * ((b + 2 * m * a) * b ^ m) := by rw [Nat.pow_succ]; ac_rfl
  exact Nat.le_of_mul_le_mul_left hh hb

theorem attempt_denominator (P Q : Nat) (h : P ≤ Q) :
    2048 * Q ≤ 4096 * Q - 399 * P ∧ 280 * P ≤ 4096 * Q := by omega

/-- The failure generating-function estimate after the linearizations. -/
theorem failed_attempt_contraction (P Q : Nat) (h : P ≤ Q) :
    2 * (4096 * Q + 280 * P) * (4096 * Q - 3296 * P) ≤
      4096 ^ 2 * Q * (2 * Q - P) := by
  have h1 := Nat.sub_add_cancel (show 3296 * P ≤ 4096 * Q by omega)
  have h2 := Nat.sub_add_cancel (show P ≤ 2 * Q by omega)
  have he : 2 * (4096 * Q + 280 * P) * (4096 * Q - 3296 * P) +
      7929856 * P * Q + 1845760 * P * P = 4096 ^ 2 * Q * (2 * Q - P) := by grind
  omega

theorem half_root_constants :
    140 ^ 2 < 2 * 101 ^ 2 ∧ 3 * 140 ^ 2 < 2 * 172 ^ 2 ∧
    101 + 172 = 273 ∧ 273 * 40 = 39 * 280 := by decide

theorem total_attempt_constant :
    (4096 + 280) * (4096 + 800) ≤ 2 * 4096 ^ 2 := by decide

def returnWeight (t n : Nat) : Nat :=
  if n % 2 = 0 ∧ wt t n = wt t (n + 1) ∧ orbit t n ≠ orbit t (n + 1)
  then 3 ^ wt t n else 0

theorem return_weight_bound (t n : Nat) : returnWeight t n ≤ 3 ^ wt t n := by
  unfold returnWeight
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem return_level_mass (t : Nat) :
    total (2 ^ t) (returnWeight t) ≤ 4 ^ t := by
  have hh := total_le (2 ^ t) (returnWeight t) (fun n => 3 ^ wt t n)
    (fun n _ => return_weight_bound t n)
  rw [cubic_mass] at hh
  exact hh

/-- 2^H times the sum of all nonfused even-return slopes through H. -/
def cumulativeColumn : Nat → Nat
  | 0 => 0
  | h + 1 => 2 * cumulativeColumn h + total (2 ^ (h + 1)) (returnWeight (h + 1))

theorem cumulative_column_bound (h : Nat) :
    cumulativeColumn h + 2 ^ (h + 1) ≤ 2 * 4 ^ h := by
  induction h with
  | zero => decide
  | succ h ih =>
    have hh := return_level_mass (h + 1)
    simp only [cumulativeColumn, Nat.pow_succ] at *
    omega

#print axioms return_class
#print axioms family_early_return
#print axioms weight_prefix_mono
#print axioms power_pair_no_return
#print axioms geometric_drift_arithmetic
#print axioms inverse_bernoulli_step
#print axioms inverse_bernoulli
#print axioms exponential_linearization
#print axioms attempt_denominator
#print axioms failed_attempt_contraction
#print axioms half_root_constants
#print axioms total_attempt_constant
#print axioms return_weight_bound
#print axioms return_level_mass
#print axioms cumulative_column_bound

end ReturnOccupationDensity
