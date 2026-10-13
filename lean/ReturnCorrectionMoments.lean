/-
  Exact affine-correction identities and bounded stopping arithmetic.
  Unbounded stopping, real moments, and probability consequences remain
  written in docs/RETURN-CORRECTION-MOMENTS.md.
-/
import CountReturnControl
import CountReturnClock

namespace ReturnCorrectionMoments
open CollatzAffine CoalescenceTail EscapeWeightRefinements

theorem numerator_snoc (t n : Nat) :
    numerator (t + 1) n =
      3 ^ (orbit t n % 2) * numerator t n + 2 ^ t * (orbit t n % 2) := by
  have h := orbit_equation (t + 1) n
  have hs := step_equation (orbit t n)
  have he : 2 ^ (t + 1) * orbit (t + 1) n =
      3 ^ (orbit t n % 2) * (3 ^ wt t n * n + numerator t n) +
        2 ^ t * (orbit t n % 2) := by
    rw [orbit_snoc, Nat.pow_succ]
    calc
      2 ^ t * 2 * U (orbit t n) = 2 ^ t * (2 * U (orbit t n)) := by ac_rfl
      _ = 2 ^ t * (3 ^ (orbit t n % 2) * orbit t n + orbit t n % 2) := by rw [hs]
      _ = 3 ^ (orbit t n % 2) * (2 ^ t * orbit t n) +
          2 ^ t * (orbit t n % 2) := by rw [Nat.mul_add]; ac_rfl
      _ = _ := by rw [orbit_equation]
  rw [he, weight_snoc, Nat.pow_add] at h
  have hm : 3 ^ wt t n * 3 ^ (orbit t n % 2) * n =
      3 ^ (orbit t n % 2) * (3 ^ wt t n * n) := by ac_rfl
  rw [hm, Nat.mul_add] at h
  omega

theorem numerator_lift (t q n : Nat) :
    numerator t (2 ^ t * q + n) = numerator t n := by
  have h := orbit_equation t (2 ^ t * q + n)
  rw [weight_lift] at h
  have he := affine_numerator t n q
  omega

/-- Clearing the denominator in E[B_(t+1) | prefix] = B_t + 1/4. -/
theorem numerator_children (t n : Nat) :
    numerator (t + 1) n + numerator (t + 1) (2 ^ t + n) =
      4 * numerator t n + 2 ^ t := by
  have hl := numerator_lift t 1 n
  simp only [Nat.mul_one] at hl
  rw [numerator_snoc, numerator_snoc, hl, endpoint_parity_flip]
  have hp : orbit t n % 2 = 0 ∨ orbit t n % 2 = 1 := by omega
  rcases hp with hp | hp <;> simp [hp] <;> omega

inductive StopTree where
  | stop
  | branch (even odd : StopTree)

/-- 2^h times the expected additional clock in a tree truncated at h. -/
def clockNumerator : Nat → StopTree → Nat
  | 0, _ => 0
  | _ + 1, .stop => 0
  | h + 1, .branch even odd =>
      2 ^ (h + 1) + clockNumerator h even + clockNumerator h odd

/-- d*4^h times the terminal affine correction, starting from correction N/d. -/
def stoppedNumerator : Nat → Nat → Nat → StopTree → Nat
  | 0, _, N, _ => N
  | h + 1, _, N, .stop => 4 ^ (h + 1) * N
  | h + 1, d, N, .branch even odd =>
      stoppedNumerator h (2 * d) N even +
        stoppedNumerator h (2 * d) (3 * N + d) odd

theorem four_pow (h : Nat) : 4 ^ h = 2 ^ h * 2 ^ h := by
  rw [← Nat.mul_pow]

/-- Exact finite-tree optional stopping, with all denominators cleared. -/
theorem stopped_correction_identity (h d N : Nat) (tree : StopTree) :
    4 * stoppedNumerator h d N tree =
      4 ^ (h + 1) * N + d * 2 ^ h * clockNumerator h tree := by
  induction h generalizing d N tree with
  | zero => simp [stoppedNumerator, clockNumerator]
  | succ h ih =>
    cases tree with
    | stop => simp [stoppedNumerator, clockNumerator, Nat.pow_succ]; ac_rfl
    | branch even odd =>
      have he := ih (2 * d) N even
      have ho := ih (2 * d) (3 * N + d) odd
      simp only [stoppedNumerator, clockNumerator]
      rw [Nat.mul_add, he, ho]
      simp only [Nat.pow_succ, four_pow]
      grind

theorem clock_numerator_bound (h : Nat) (tree : StopTree) :
    clockNumerator h tree ≤ h * 2 ^ h := by
  induction h generalizing tree with
  | zero => simp [clockNumerator]
  | succ h ih =>
    cases tree with
    | stop => simp [clockNumerator]
    | branch even odd =>
      have he := ih even
      have ho := ih odd
      simp only [clockNumerator, Nat.pow_succ]
      grind

/-- d*4^h times the stopped slope, starting from slope A/d. -/
def stoppedSlope : Nat → Nat → StopTree → Nat
  | 0, A, _ => A
  | h + 1, A, .stop => 4 ^ (h + 1) * A
  | h + 1, A, .branch even odd =>
      stoppedSlope h A even + stoppedSlope h (3 * A) odd

theorem stopped_slope_identity (h A : Nat) (tree : StopTree) :
    stoppedSlope h A tree = 4 ^ h * A := by
  induction h generalizing A tree with
  | zero => simp [stoppedSlope]
  | succ h ih =>
    cases tree with
    | stop => rfl
    | branch even odd => simp [stoppedSlope, ih, Nat.pow_succ]; grind

/-- The previous Green-function estimate, retained as a named dependency. -/
theorem boundary_clock_budget (K : Nat) (hK : 0 < K) :
    1 + 2 * CountReturnClock.costMass (K - 1) ≤ 9 * K - 8 :=
  CountReturnClock.stopped_clock_budget K hK

/-- Integer comparisons for r_(1/4) < 39/40. Real root monotonicity is written. -/
theorem quarter_root_constants :
    120 ^ 4 < 2 * 101 ^ 4 ∧
    3 * 120 ^ 4 < 2 * 133 ^ 4 ∧
    101 + 133 = 234 ∧ 234 * 40 = 39 * 240 := by decide

theorem quarter_drift_constants :
    40 * 9 = 360 ∧ 400 - 360 = 40 ∧
    39 * 400 + 40 * 9 = 40 * 399 ∧
    400 ^ 4 = 25600000000 ∧ 400 ^ 4 < 2 ^ 35 := by decide

theorem prescribed_attempt_constants :
    3 ^ 4 < 2 ^ 7 ∧ 4 * 35 = 140 ∧ 35 + 2 = 37 ∧
    140 * 37 = 5180 ∧ 140 + 400 = 540 := by decide

theorem odd_offset_bit_bound (D : Nat) (hD : D < 2 ^ 35) :
    (3 * D + 1) / 2 < 2 ^ 36 := by omega

#print axioms numerator_snoc
#print axioms numerator_lift
#print axioms numerator_children
#print axioms four_pow
#print axioms stopped_correction_identity
#print axioms clock_numerator_bound
#print axioms stopped_slope_identity
#print axioms boundary_clock_budget
#print axioms quarter_root_constants
#print axioms quarter_drift_constants
#print axioms prescribed_attempt_constants
#print axioms odd_offset_bit_bound

end ReturnCorrectionMoments
