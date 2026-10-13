/-
  Exact finite moments for the auxiliary grade weight.
  These control V_t = 2^t U^t(n)/(4^wt n), not the escape weight W_t.
  No natural-density premise or universal convergence claim is used.
-/
import CoalescenceTail

namespace GradeWeightMoments
open CollatzAffine CoalescenceTail

def principal : Nat → Nat → Nat
  | 0, _ => 1
  | t + 1, n => if orbit t n % 2 = 1 then 3 * principal t n else 4 * principal t n

def scale : Nat → Nat → Nat
  | 0, _ => 1
  | t + 1, n => if orbit t n % 2 = 1 then scale t n else 4 * scale t n

def correction : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => if orbit t n % 2 = 1
      then 3 * correction t n + 2 ^ t * scale t n else 4 * correction t n

theorem step_equation (n : Nat) : 2 * U n = 3 ^ (n % 2) * n + n % 2 := by
  by_cases h : n % 2 = 1
  · simp [U, h]
    omega
  · have he : n % 2 = 0 := by omega
    simp [U, he]
    omega

theorem scale_identity : ∀ t n, scale t n * 4 ^ wt t n = 4 ^ t
  | 0, _ => by simp [scale, wt]
  | t + 1, n => by
    have ih := scale_identity t n
    by_cases h : orbit t n % 2 = 1
    · simp [scale, weight_snoc, h, Nat.pow_succ]
      rw [← Nat.mul_assoc, ih]
    · have he : orbit t n % 2 = 0 := by omega
      simp [scale, weight_snoc, he, Nat.pow_succ]
      calc
        4 * scale t n * 4 ^ wt t n = 4 * (scale t n * 4 ^ wt t n) := by ac_rfl
        _ = 4 ^ t * 4 := by rw [ih]; ac_rfl

theorem principal_identity : ∀ t n, principal t n = 3 ^ wt t n * scale t n
  | 0, _ => by simp [principal, wt, scale]
  | t + 1, n => by
    by_cases h : orbit t n % 2 = 1
    · simp [principal, scale, weight_snoc, h, Nat.pow_succ,
        principal_identity]
      ac_rfl
    · have he : orbit t n % 2 = 0 := by omega
      simp [principal, scale, weight_snoc, he,
        principal_identity]
      ac_rfl

theorem scaled_orbit_identity : ∀ t n,
    scale t n * (2 ^ t * orbit t n) = principal t n * n + correction t n
  | 0, _ => by simp [scale, principal, correction, orbit]
  | t + 1, n => by
    have ih := scaled_orbit_identity t n
    have hs := step_equation (orbit t n)
    by_cases h : orbit t n % 2 = 1
    · simp only [h, Nat.pow_one] at hs
      simp only [scale, principal, correction, if_pos h, orbit_snoc, Nat.pow_succ]
      calc
        scale t n * (2 ^ t * 2 * U (orbit t n)) =
            scale t n * (2 ^ t * (2 * U (orbit t n))) := by ac_rfl
        _ = scale t n * (2 ^ t * (3 * orbit t n + 1)) := by rw [hs]
        _ = 3 * (scale t n * (2 ^ t * orbit t n)) + 2 ^ t * scale t n := by
          simp only [Nat.mul_add, Nat.mul_one]
          ac_rfl
        _ = 3 * principal t n * n + (3 * correction t n + 2 ^ t * scale t n) := by
          rw [ih, Nat.mul_add]
          ac_rfl
    · have he : orbit t n % 2 = 0 := by omega
      simp only [he, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hs
      simp only [scale, principal, correction, if_neg h, orbit_snoc, Nat.pow_succ]
      calc
        4 * scale t n * (2 ^ t * 2 * U (orbit t n)) =
            4 * (scale t n * (2 ^ t * (2 * U (orbit t n)))) := by ac_rfl
        _ = 4 * (scale t n * (2 ^ t * orbit t n)) := by rw [hs]
        _ = 4 * principal t n * n + 4 * correction t n := by
          rw [ih, Nat.mul_add]
          ac_rfl

theorem correction_identity (t n : Nat) :
    correction t n = scale t n * numerator t n := by
  have h := scaled_orbit_identity t n
  rw [orbit_equation, Nat.mul_add, principal_identity] at h
  have hm : scale t n * (3 ^ wt t n * n) = 3 ^ wt t n * scale t n * n := by ac_rfl
  rw [hm] at h
  omega

theorem step_grade_bound (n : Nat) : 2 * U n ≤ 4 ^ (n % 2) * n := by
  rw [step_equation]
  by_cases h : n % 2 = 1
  · simp only [h, Nat.pow_one]
    omega
  · have he : n % 2 = 0 := by omega
    simp [he]

theorem grade_envelope : ∀ t n, 2 ^ t * orbit t n ≤ 4 ^ wt t n * n
  | 0, _ => by simp [orbit, wt]
  | t + 1, n => by
    have ih := grade_envelope t (U n)
    have hs := step_grade_bound n
    calc
      2 ^ (t + 1) * orbit (t + 1) n = 2 * (2 ^ t * orbit t (U n)) := by
        simp only [orbit, Nat.pow_succ]
        ac_rfl
      _ ≤ 2 * (4 ^ wt t (U n) * U n) := Nat.mul_le_mul_left 2 ih
      _ = 4 ^ wt t (U n) * (2 * U n) := by ac_rfl
      _ ≤ 4 ^ wt t (U n) * (4 ^ (n % 2) * n) := Nat.mul_le_mul_left _ hs
      _ = 4 ^ wt (t + 1) n * n := by
        simp only [wt, Nat.pow_add]
        ac_rfl

/-- Cross-multiplied monotonicity of the auxiliary weight at each time. -/
theorem grade_step_monotone (t n : Nat) :
    2 * orbit (t + 1) n * 4 ^ wt t n ≤ orbit t n * 4 ^ wt (t + 1) n := by
  have h := Nat.mul_le_mul_right (4 ^ wt t n) (step_grade_bound (orbit t n))
  rw [orbit_snoc, weight_snoc, Nat.pow_add]
  calc
    2 * U (orbit t n) * 4 ^ wt t n ≤
        4 ^ (orbit t n % 2) * orbit t n * 4 ^ wt t n := h
    _ = orbit t n * (4 ^ wt t n * 4 ^ (orbit t n % 2)) := by ac_rfl

theorem data_lift : ∀ t q n,
    principal t (2 ^ t * q + n) = principal t n ∧
    scale t (2 ^ t * q + n) = scale t n ∧
    correction t (2 ^ t * q + n) = correction t n
  | 0, _, _ => by simp [principal, scale, correction]
  | t + 1, q, n => by
    have hx : 2 ^ (t + 1) * q + n = 2 ^ t * (2 * q) + n := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have ih := data_lift t (2 * q) n
    have hp : orbit t (2 ^ t * (2 * q) + n) % 2 = orbit t n % 2 := by
      rw [affine]
      simp [Nat.add_mod, Nat.mul_mod]
    simp [principal, scale, correction, hx, hp, ih.1, ih.2.1, ih.2.2]

theorem data_children (t n : Nat) :
    principal (t + 1) n + principal (t + 1) (2 ^ t + n) = 7 * principal t n ∧
    scale (t + 1) n + scale (t + 1) (2 ^ t + n) = 5 * scale t n ∧
    correction (t + 1) n + correction (t + 1) (2 ^ t + n) =
      7 * correction t n + 2 ^ t * scale t n := by
  have hl := data_lift t 1 n
  simp only [Nat.mul_one] at hl
  have hp := endpoint_parity_flip t n
  by_cases h : orbit t n % 2 = 1
  · have he : orbit t (2 ^ t + n) % 2 = 0 := by omega
    simp [principal, scale, correction, h, he, hl.1, hl.2.1, hl.2.2]
    omega
  · have he : orbit t n % 2 = 0 := by omega
    have ho : orbit t (2 ^ t + n) % 2 = 1 := by omega
    simp [principal, scale, correction, he, ho, hl.1, hl.2.1, hl.2.2]
    omega

theorem principal_mass : ∀ t, total (2 ^ t) (principal t) = 7 ^ t
  | 0 => by simp [total, principal]
  | t + 1 => by
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => (data_children t n).1), total_mul, principal_mass]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem scale_mass : ∀ t, total (2 ^ t) (scale t) = 5 ^ t
  | 0 => by simp [total, scale]
  | t + 1 => by
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => (data_children t n).2.1), total_mul, scale_mass]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem correction_mass : ∀ t, 3 * total (2 ^ t) (correction t) + 7 ^ t = 10 ^ t
  | 0 => by simp [total, correction]
  | t + 1 => by
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => (data_children t n).2.2), total_sum,
      total_mul, total_mul, scale_mass]
    have ih := correction_mass t
    have hm : 2 ^ t * 5 ^ t = 10 ^ t := by rw [← Nat.mul_pow]
    rw [hm, Nat.pow_succ, Nat.pow_succ]
    omega

#print axioms step_equation
#print axioms scale_identity
#print axioms principal_identity
#print axioms scaled_orbit_identity
#print axioms correction_identity
#print axioms step_grade_bound
#print axioms grade_envelope
#print axioms grade_step_monotone
#print axioms data_lift
#print axioms data_children
#print axioms principal_mass
#print axioms scale_mass
#print axioms correction_mass
end GradeWeightMoments
