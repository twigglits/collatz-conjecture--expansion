/-
  Finite biased-walk and correction-budget arithmetic.
  Change of measure, unbounded stopping, infinite means, and fractional
  powers remain written in docs/RETURN-SLOPE-TILT.md.
-/
import ReturnCorrectionMoments

namespace ReturnSlopeTilt

def awayHit (K j : Nat) : Nat := 3 ^ (K - j) - 1
def towardHit (K j : Nat) : Nat := 3 ^ K - 3 ^ j

theorem biased_boundaries (K : Nat) :
    awayHit K 0 = 3 ^ K - 1 ∧ awayHit K K = 0 ∧
    towardHit K 0 = 3 ^ K - 1 ∧ towardHit K K = 0 := by
  simp [awayHit, towardHit]

/-- Numerator of the zero-hit probability for the 3/4 outward walk. -/
theorem away_harmonic (K j : Nat) (hj : 0 < j) (hK : j < K) :
    4 * awayHit K j = 3 * awayHit K (j + 1) + awayHit K (j - 1) := by
  have h0 : K - j = (K - (j + 1)) + 1 := by omega
  have h1 : K - (j - 1) = (K - (j + 1)) + 2 := by omega
  have hp : 0 < 3 ^ (K - (j + 1)) := Nat.pow_pos (by decide)
  simp only [awayHit, h0, h1, Nat.pow_add, Nat.pow_one]
  omega

/-- Numerator of the zero-hit probability for the 3/4 inward walk. -/
theorem toward_harmonic (K j : Nat) (hj : 0 < j) (hK : j < K) :
    4 * towardHit K j = 3 * towardHit K (j - 1) + towardHit K (j + 1) := by
  have h0 : j = (j - 1) + 1 := by omega
  have h1 : j + 1 = (j - 1) + 2 := by omega
  have hb : 3 ^ (j + 1) ≤ 3 ^ K := Nat.pow_le_pow_right (by decide) (by omega)
  have he0 : 3 ^ j = 3 ^ (j - 1) * 3 :=
    (congrArg (fun k => 3 ^ k) h0).trans (Nat.pow_succ 3 (j - 1))
  have he1 : 3 ^ (j + 1) = 3 ^ (j - 1) * 9 := by rw [h1, Nat.pow_add]
  rw [he1] at hb
  simp only [towardHit, he0, he1]
  omega

theorem biased_numerator_ratio (K j : Nat) (hj : j ≤ K) :
    towardHit K j = 3 ^ j * awayHit K j := by
  unfold towardHit awayHit
  rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← Nat.pow_add,
      Nat.add_sub_of_le hj]

/-- d(K-d) pays one unit per step of the fair killed active walk. -/
theorem fair_exit_clock (K d : Nat) (hd : 0 < d) (hK : d < K) :
    2 * (d * (K - d)) =
      (d - 1) * (K - (d - 1)) + (d + 1) * (K - (d + 1)) + 2 := by
  have h0 : d = (d - 1) + 1 := by omega
  have h1 : K - d = (K - (d + 1)) + 1 := by omega
  have h2 : K - (d - 1) = (K - (d + 1)) + 2 := by omega
  rw [h1, h2]
  grind

/-- 3^H times sum_(k=1)^H (6k+4)3^-k. -/
def fastCost : Nat → Nat
  | 0 => 0
  | H + 1 => 3 * fastCost H + 6 * H + 10

theorem fast_cost_identity (H : Nat) :
    2 * fastCost H + 6 * H + 13 = 13 * 3 ^ H := by
  induction H with
  | zero => rfl
  | succ H ih =>
    simp only [fastCost, Nat.pow_succ]
    omega

/-- The initial 1/6 correction and the whole geometric cost are at most 5/4. -/
theorem fast_cost_budget (H : Nat) :
    2 * (3 ^ H + fastCost H) ≤ 15 * 3 ^ H := by
  have h := fast_cost_identity H
  omega

/-- Homogeneous algebra behind 1-z >= 1-(a+b) for the smaller root. -/
theorem root_gap_identity (a b c u v : Int)
    (h : b * u ^ 2 + a * v ^ 2 = c * u * v) :
    (v - u) * (c * v - b * (v + u)) = (c - a - b) * v ^ 2 := by
  grind

/-- Switching the endpoint exchanges the two active-step coefficients. -/
theorem root_endpoint_switch (a b c u v : Nat)
    (h : b * u ^ 2 + a * v ^ 2 = c * u * v) :
    a * (b * u) ^ 2 + b * (a * v) ^ 2 = c * (b * u) * (a * v) := by
  have hh := congrArg (fun x => a * b * x) h
  grind

#print axioms biased_boundaries
#print axioms away_harmonic
#print axioms toward_harmonic
#print axioms biased_numerator_ratio
#print axioms fair_exit_clock
#print axioms fast_cost_identity
#print axioms fast_cost_budget
#print axioms root_gap_identity
#print axioms root_endpoint_switch

end ReturnSlopeTilt
