/-
  Exact count-pair certificates for distance from mechanical parity words.
  Standalone Lean 4; no Mathlib.
  Check: lean lean/MechanicalDistanceFinite.lean

  H is a half-Hamming-distance budget and B is a small-state threshold.
  The exported disjunction is finite integer arithmetic only. Its application
  to cycles uses written complexity, height, product, and logarithm arguments.
  The witness generator is not trusted for correctness: each generated row
  independently checks both adjacent powers of three. Kernel monotonicity
  extends the row to every eligible p. Only finite computations use native_decide.
-/
namespace MechanicalDistanceFinite

def Excluded (H B N p : Nat) : Prop :=
  3 ^ H * p * 2 ^ N ≤ (2 ^ N - 3 ^ p) * 2 ^ ((N - 2) / (2 * H + 1)) ∨
    p * 2 ^ N ≤ 3 * B * (2 ^ N - 3 ^ p)

instance (H B N p : Nat) : Decidable (Excluded H B N p) := inferInstanceAs
  (Decidable (3 ^ H * p * 2 ^ N ≤ (2 ^ N - 3 ^ p) * 2 ^ ((N - 2) / (2 * H + 1)) ∨
    p * 2 ^ N ≤ 3 * B * (2 ^ N - 3 ^ p)))

theorem excluded_downward (H B N p q : Nat) (hpq : p ≤ q)
    (hq : Excluded H B N q) : Excluded H B N p := by
  have hpowers : 3 ^ p ≤ 3 ^ q := Nat.pow_le_pow_right (by decide) hpq
  have hden : 2 ^ N - 3 ^ q ≤ 2 ^ N - 3 ^ p := Nat.sub_le_sub_left hpowers _
  rcases hq with hs | hm
  · left
    exact Nat.le_trans
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) hpq) (Nat.le_refl _))
      (Nat.le_trans hs (Nat.mul_le_mul hden (Nat.le_refl _)))
  · right
    exact Nat.le_trans (Nat.mul_le_mul hpq (Nat.le_refl _))
      (Nat.le_trans hm (Nat.mul_le_mul (Nat.le_refl _) hden))

theorem eligible_le_witness (N p q : Nat)
    (hupper : 2 ^ N ≤ 3 ^ (q + 1)) (heligible : 3 ^ p < 2 ^ N) : p ≤ q := by
  by_cases hpq : p ≤ q
  · exact hpq
  · have hq : q + 1 ≤ p := by omega
    have hpowers : 3 ^ (q + 1) ≤ 3 ^ p := Nat.pow_le_pow_right (by decide) hq
    omega

/-- Efficient candidate generation; correctness is independently checked below. -/
def witnesses (bound : Nat) : Array Nat := Id.run do
  let mut result := #[0]
  let mut q := 0
  let mut three := 1
  let mut two := 1
  for _ in [1:bound] do
    two := two * 2
    if three * 3 < two then
      q := q + 1
      three := three * 3
    result := result.push q
  return result

def checkMax (H B N q : Nat) : Bool :=
  decide (3 ^ q < 2 ^ N ∧ 2 ^ N ≤ 3 ^ (q + 1) ∧ Excluded H B N q)

def checked (H B bound : Nat) : Bool :=
  let qs := witnesses bound
  (List.range (bound - 3)).all fun i => checkMax H B (i + 3) qs[i + 3]!

theorem checked_sound (H B bound : Nat) (hc : checked H B bound = true)
    (N p : Nat) (hlo : 3 ≤ N) (hhi : N < bound) (heligible : 3 ^ p < 2 ^ N) :
    Excluded H B N p := by
  have hi : N - 3 ∈ List.range (bound - 3) := List.mem_range.mpr (by omega)
  have hrow := List.all_eq_true.mp hc (N - 3) hi
  have hN : N - 3 + 3 = N := by omega
  simp only [hN] at hrow
  have hw : 3 ^ (witnesses bound)[N]! < 2 ^ N ∧
      2 ^ N ≤ 3 ^ ((witnesses bound)[N]! + 1) ∧
      Excluded H B N (witnesses bound)[N]! := of_decide_eq_true hrow
  exact excluded_downward H B N p _ (eligible_le_witness N p _ hw.2.1 heligible) hw.2.2

theorem checked_16_100000_5120 : checked 16 100000 5120 = true := by native_decide

theorem finite_16 (N p : Nat) (hlo : 3 ≤ N) (hhi : N < 5120)
    (heligible : 3 ^ p < 2 ^ N) : Excluded 16 100000 N p :=
  checked_sound 16 100000 5120 checked_16_100000_5120 N p hlo hhi heligible

/-- Exact constants for the written H=16 reduction and window comparison. -/
theorem cutoff_16_arithmetic :
    99 * (31 * 602494200 + 63) < 2 * 10 ^ 12 ∧
    99 * (602494200 + 1) < 2 * 10 ^ 12 ∧
    3 ^ 16 < 2 ^ 26 ∧ 5152 < 2 ^ 13 ∧ (5120 - 2) / 33 = 155 ∧
    3 ^ 18 * 100000 + 1 < 2 ^ 62 := by decide

/-- The B=100000 arithmetic test alone cannot close H=17: this is a failure
    of this test, not evidence that a cycle with these counts exists. -/
theorem boundary_17 : 3 ^ 971 < 2 ^ 1539 ∧ ¬ Excluded 17 100000 1539 971 := by
  native_decide

/-- Stronger finite closure using unconditional convergence through one million. -/
theorem checked_31_1000000_12288 : checked 31 1000000 12288 = true := by native_decide

theorem finite_31 (N p : Nat) (hlo : 3 ≤ N) (hhi : N < 12288)
    (heligible : 3 ^ p < 2 ^ N) : Excluded 31 1000000 N p :=
  checked_sound 31 1000000 12288 checked_31_1000000_12288 N p hlo hhi heligible

/-- Constants for N<10^13 at every H≤100, then N<12288 at H=31. -/
theorem cutoff_31_arithmetic :
    603 * (34 * 602494200 + 234) < 2 * 10 ^ 13 ∧
    603 * (602494200 + 1) < 2 * 10 ^ 13 ∧
    3 ^ 31 < 2 ^ 50 ∧ 12350 < 2 ^ 14 ∧ (12288 - 2) / 63 = 195 := by decide

/-- This arithmetic method with B=1000000 fails at H=32 for these counts.
    It does not assert the existence of an integer cycle. -/
theorem boundary_32 : 3 ^ 2966 < 2 ^ 4701 ∧ ¬ Excluded 32 1000000 4701 2966 := by
  native_decide

#print axioms finite_31
#print axioms cutoff_31_arithmetic
#print axioms boundary_32

#print axioms excluded_downward
#print axioms eligible_le_witness
#print axioms checked_sound
#print axioms finite_16
#print axioms cutoff_16_arithmetic
#print axioms boundary_17
end MechanicalDistanceFinite
