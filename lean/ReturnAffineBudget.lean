/-
  Arithmetic for affine-coefficient budgets over all count returns.
  Fractional powers, probability, concentration, Haar norms, and infinite
  series remain written in docs/RETURN-AFFINE-BUDGET.md.
-/
import BinaryImageEnergy

namespace ReturnAffineBudget
open CollatzAffine CoalescenceTail EscapeWeightRefinements
open ReturnCorrectionMoments BinaryImageEnergy

/-- 2^t times the affine image of the formal real input one. -/
def augmented (t n : Nat) : Nat := 3 ^ wt t n + numerator t n

theorem augmented_snoc (t n : Nat) :
    augmented (t + 1) n =
      3 ^ (orbit t n % 2) * augmented t n + 2 ^ t * (orbit t n % 2) := by
  simp only [augmented, numerator_snoc, weight_snoc, Nat.pow_add]
  rw [Nat.mul_add]
  ac_rfl

theorem augmented_lift (t q n : Nat) :
    augmented t (2 ^ t * q + n) = augmented t n := by
  simp only [augmented, weight_lift, numerator_lift]

theorem numerator_append (t h n : Nat) :
    numerator (t + h) n =
      3 ^ wt h (orbit t n) * numerator t n + 2 ^ t * numerator h (orbit t n) := by
  have he := orbit_equation (t + h) n
  have hh := orbit_equation h (orbit t n)
  have ht := orbit_equation t n
  have hx : 2 ^ (t + h) * orbit (t + h) n =
      3 ^ wt h (orbit t n) * (3 ^ wt t n * n + numerator t n) +
        2 ^ t * numerator h (orbit t n) := by
    rw [Nat.pow_add, orbit_add]
    calc
      2 ^ t * 2 ^ h * orbit h (orbit t n) =
          2 ^ t * (2 ^ h * orbit h (orbit t n)) := by ac_rfl
      _ = 2 ^ t * (3 ^ wt h (orbit t n) * orbit t n +
          numerator h (orbit t n)) := by rw [hh]
      _ = 3 ^ wt h (orbit t n) * (2 ^ t * orbit t n) +
          2 ^ t * numerator h (orbit t n) := by rw [Nat.mul_add]; ac_rfl
      _ = _ := by rw [ht]
  rw [hx, weight_add, Nat.pow_add] at he
  have hm : 3 ^ wt t n * 3 ^ wt h (orbit t n) * n =
      3 ^ wt h (orbit t n) * (3 ^ wt t n * n) := by ac_rfl
  rw [hm, Nat.mul_add] at he
  omega

theorem augmented_append (t h n : Nat) :
    augmented (t + h) n =
      3 ^ wt h (orbit t n) * augmented t n + 2 ^ t * numerator h (orbit t n) := by
  simp only [augmented, numerator_append, weight_add, Nat.pow_add]
  rw [Nat.mul_add]
  ac_rfl

/-- The parity-count generating polynomial, with a natural argument. -/
theorem power_count_children (t n z : Nat) :
    z ^ wt (t + 1) n + z ^ wt (t + 1) (2 ^ t + n) =
      (1 + z) * z ^ wt t n := by
  have hl := weight_lift t 1 n
  simp only [Nat.mul_one] at hl
  rw [weight_snoc, weight_snoc, hl, endpoint_parity_flip]
  have hp : orbit t n % 2 = 0 ∨ orbit t n % 2 = 1 := by omega
  rcases hp with hp | hp <;> simp [hp, Nat.pow_succ] <;> grind

theorem power_count_mass (t z : Nat) :
    total (2 ^ t) (fun n => z ^ wt t n) = (1 + z) ^ t := by
  induction t with
  | zero => simp [total, wt]
  | succ t ih =>
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    have he := total_ext (2 ^ t)
      (fun n => z ^ wt (t + 1) n + z ^ wt (t + 1) (2 ^ t + n))
      (fun n => (1 + z) * z ^ wt t n)
      (fun n _ => power_count_children t n z)
    rw [he, total_mul, ih, Nat.pow_succ]
    ac_rfl

/-- Finite rational-drift algebra, after clearing a common denominator. -/
theorem finite_drift_budget (h p d c : Nat) (A B : Nat → Nat)
    (hs : ∀ j, j < h → (p + d) * A (j + 1) ≤ p * A j + c * B j) :
    d * total h A + (p + d) * A h ≤
      (p + d) * A 0 + c * total h B := by
  induction h with
  | zero => simp [total]
  | succ h ih =>
    have hi := ih (fun j hj => hs j (by omega))
    have hh := hs h (by omega)
    simp only [total, Nat.mul_add]
    have ha : (p + d) * A h = p * A h + d * A h := Nat.add_mul _ _ _
    omega

/-- The ordered-fibre input to the written fractional-power estimate. -/
theorem augmented_fibre_rank (t a r j : Nat)
    (ha : wt t r = a) (hj : j ≤ numerator t r / 3 ^ a) :
    3 ^ a * (j + 1) ≤ augmented t r := by
  have he := Nat.mod_add_div (numerator t r) (3 ^ a)
  have hm := Nat.mul_le_mul_left (3 ^ a) hj
  simp only [augmented, ha, Nat.mul_add, Nat.mul_one]
  omega

#print axioms augmented_snoc
#print axioms augmented_lift
#print axioms numerator_append
#print axioms augmented_append
#print axioms power_count_children
#print axioms power_count_mass
#print axioms finite_drift_budget
#print axioms augmented_fibre_rank

end ReturnAffineBudget
