/-
  Finite arithmetic for the smaller formal endpoint at every count return.
  Entropy, stopping, mixed moments and infinite energy remain written.
-/
import LowerReturnEnergy
import ReturnAncestralOverlap

namespace AllReturnLowerEnergy
open CollatzAffine CoalescenceTail ReturnCorrectionMoments ReturnAncestralOverlap

/-- Correction contributions weighted by their remaining physical age. -/
def correctionAge : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => 3 ^ (orbit t n % 2) * (correctionAge t n + numerator t n)

theorem correction_age_snoc (t n : Nat) :
    correctionAge (t + 1) n =
      3 ^ (orbit t n % 2) * (correctionAge t n + numerator t n) := rfl

theorem correction_age_bound (t n : Nat) :
    correctionAge t n ≤ t * numerator t n := by
  induction t with
  | zero => simp [correctionAge]
  | succ t ih =>
    rw [correction_age_snoc, numerator_snoc]
    have hm := Nat.mul_le_mul_left (3 ^ (orbit t n % 2)) ih
    grind

/-- Numerator of the finite fair Green row, with common denominator K. -/
def fairGreen (K j k : Nat) : Nat := 2 * min j k * (K - max j k)

theorem fair_green_cap (K j k : Nat) : fairGreen K j k ≤ 2 * k * K := by
  have h1 := Nat.min_le_right j k
  have h2 := Nat.sub_le K (max j k)
  have h := Nat.mul_le_mul h1 h2
  simpa only [fairGreen, Nat.mul_assoc] using Nat.mul_le_mul_left 2 h

def restartCost : Nat → Nat
  | 0 => 0
  | H + 1 => 3 * restartCost H + 3 * (H + 1) ^ 2 + 2 * (H + 1)

theorem restart_cost_identity (H : Nat) :
    2 * restartCost H + 3 * H ^ 2 + 11 * H + 12 = 12 * 3 ^ H := by
  induction H with
  | zero => rfl
  | succ H ih => simp only [restartCost, Nat.pow_succ]; grind

def ageCost : Nat → Nat
  | 0 => 0
  | H + 1 => 3 * ageCost H +
      3 * (2 * (H + 1) + 1) * clockPotential (H + 1) + clockPotential (H + 2)

theorem age_cost_identity (H : Nat) :
    2 * ageCost H + 36 * H ^ 3 + 306 * H ^ 2 + 848 * H + 893 =
      893 * 3 ^ H := by
  induction H with
  | zero => rfl
  | succ H ih => simp only [ageCost, clockPotential, Nat.pow_succ]; grind

theorem correction_cost_caps (H : Nat) :
    restartCost H ≤ 6 * 3 ^ H ∧
    4 * (26 * 3 ^ H + ageCost H) ≤ 1890 * 3 ^ H := by
  have h1 := restart_cost_identity H
  have h2 := age_cost_identity H
  omega

theorem entropy_and_clip_constants :
    5 + 4 * 107 * 4 < 4 * 430 ∧
    20 * 430 + 3 * 315 < 20 * 480 ∧
    6369 * 20 < 4 * 179 ^ 2 ∧
    4 * (480 + 2 * 13) = 2024 ∧
    2034 + 768 + 108 < 3000 := by decide

/-- Denominator d*4^h for the mean coefficient in a common-parity run. -/
def commonMass : Nat → Nat → Nat → Nat
  | 0, A, _ => A
  | h + 1, A, d => 4 * commonMass h A d + d * 4 ^ h

def commonOccupation : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | h + 1, A, d => 4 * commonOccupation h A d + commonMass (h + 1) A d

theorem common_mass_identity (h A d : Nat) :
    4 * commonMass h A d = 4 ^ (h + 1) * A + h * d * 4 ^ h := by
  induction h with
  | zero => simp [commonMass]
  | succ h ih => simp only [commonMass, Nat.pow_succ] at *; grind

theorem common_occupation_identity (h A d : Nat) :
    8 * commonOccupation h A d =
      8 * 4 ^ h * h * A + d * 4 ^ h * h * (h + 1) := by
  induction h with
  | zero => simp [commonOccupation]
  | succ h ih =>
    have hm := common_mass_identity (h + 1) A d
    simp only [commonOccupation, Nat.pow_succ] at *
    grind

/-- Combine the zero-gap and odd-excursion mixed moment bounds. -/
theorem grouped_mixed_drift (m p z mb pb zb l l2 mn : Nat)
    (hm : 5 * mb ≤ 6 * m + 2 * l2)
    (hp : 4 * pb ≤ 4 * p + l)
    (hz : zb ≤ z) (hl : l ≤ 8 * z) (hl2 : l2 ≤ 64 * z)
    (hn : 10 * mn ≤ 5 * mb + 81 * pb + 30000 * zb) :
    10 * mn ≤ 6 * m + 81 * p + 30300 * z := by omega

theorem mixed_drift_budget (h : Nat) (M P Z : Nat → Nat)
    (hd : ∀ j < h, 10 * M (j + 1) ≤
      6 * M j + 81 * P j + 30300 * Z j) :
    4 * total h M + 10 * M h ≤
      10 * M 0 + 81 * total h P + 30300 * total h Z := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hb := ih (fun j hj => hd j (by omega))
    have hs := hd h (by omega)
    simp only [total]
    omega

theorem all_return_budget (q c p z m a : Nat)
    (hp : p ≤ 4100 * q + 36000 * c)
    (hz : z ≤ 257 * q + 36864 * c)
    (hm : 4 * m ≤ 10 * q + 81 * p + 30300 * z)
    (ha : a ≤ p + m + 9 * z) :
    a ≤ 2100000 * q + 281000000 * c := by omega

theorem all_component_budget (q c a e : Nat)
    (ha : a ≤ 2100000 * q + 281000000 * c) (he : e ≤ 2 * a) :
    e ≤ 4200000 * q + 562000000 * c := by omega

#print axioms correction_age_snoc
#print axioms correction_age_bound
#print axioms fair_green_cap
#print axioms restart_cost_identity
#print axioms age_cost_identity
#print axioms correction_cost_caps
#print axioms entropy_and_clip_constants
#print axioms common_mass_identity
#print axioms common_occupation_identity
#print axioms grouped_mixed_drift
#print axioms mixed_drift_budget
#print axioms all_return_budget
#print axioms all_component_budget

end AllReturnLowerEnergy
