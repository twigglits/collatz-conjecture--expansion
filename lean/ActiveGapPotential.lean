/-
  Finite Green-potential and geometric-budget arithmetic.
  Active stopping, fractional moments, and all-return density consequences
  remain written in docs/ACTIVE-GAP-POTENTIAL.md.
-/
import ReturnAffineBudget

namespace ActiveGapPotential
open CoalescenceTail BinaryImageEnergy

theorem min_curvature (d j : Nat) (hd : 0 < d) :
    2 * min d j = min (d - 1) j + min (d + 1) j +
      (if j = d then 1 else 0) := by
  split <;> omega

theorem total_diagonal (H e : Nat) (f : Nat → Nat) :
    total H (fun j => if j = e then f j else 0) =
      if e < H then f e else 0 := by
  induction H with
  | zero => simp [total]
  | succ H ih =>
    simp only [total, ih]
    by_cases he : e < H
    · simp [he, show e < H + 1 by omega, show H ≠ e by omega]
    · by_cases heq : H = e
      · subst e; simp
      · simp [he, heq, show ¬ e < H + 1 by omega]

/-- The actual potential is twice this sum, with geometric costs. -/
def greenSum (H : Nat) (cost : Nat → Nat) (d : Nat) : Nat :=
  total H (fun j => min d (j + 1) * cost j)

theorem green_boundary (H : Nat) (cost : Nat → Nat) :
    greenSum H cost 0 = 0 := by
  simp only [greenSum, Nat.zero_min, Nat.zero_mul]
  rw [total_const]
  simp

theorem green_cap (H d : Nat) (cost : Nat → Nat) :
    greenSum H cost d ≤ total H (fun j => (j + 1) * cost j) := by
  exact total_le H _ _ (fun j _ => Nat.mul_le_mul_right _ (Nat.min_le_right _ _))

theorem green_curvature (H d : Nat) (cost : Nat → Nat)
    (hd : 0 < d) (hH : d ≤ H) :
    2 * greenSum H cost d =
      greenSum H cost (d - 1) + greenSum H cost (d + 1) + cost (d - 1) := by
  have he := total_ext H
    (fun j => 2 * (min d (j + 1) * cost j))
    (fun j => min (d - 1) (j + 1) * cost j +
      min (d + 1) (j + 1) * cost j + (if j = d - 1 then cost j else 0)) (by
      intro j _
      have hm := congrArg (fun x => x * cost j) (min_curvature d (j + 1) hd)
      by_cases hj : j = d - 1
      · have hx : j + 1 = d := by omega
        simpa only [if_pos hj, if_pos hx, Nat.one_mul, Nat.add_mul, Nat.mul_assoc] using hm
      · have hx : j + 1 ≠ d := by omega
        simpa only [if_neg hj, if_neg hx, Nat.zero_mul, Nat.add_mul, Nat.mul_assoc] using hm)
  rw [total_mul, total_sum, total_sum, total_diagonal] at he
  simpa only [greenSum, if_pos (show d - 1 < H by omega)] using he

/-- Homogeneous numerator of sum_(j<H) (j+4)*(a/b)^j. -/
def linearGeom (a b : Nat) : Nat → Nat
  | 0 => 0
  | H + 1 => b * linearGeom a b H + (H + 4) * a ^ H

/-- Homogeneous numerator of sum_(j<H) (j+1)*(j+4)*(a/b)^j. -/
def quadraticGeom (a b : Nat) : Nat → Nat
  | 0 => 0
  | H + 1 => b * quadraticGeom a b H + (H + 1) * (H + 4) * a ^ H

theorem linear_geometric_identity (a c H : Nat) :
    c ^ 2 * linearGeom a (a + c) H + a ^ H * ((H + 4) * c + a) =
      (a + 4 * c) * (a + c) ^ H := by
  induction H with
  | zero => simp [linearGeom, Nat.add_comm]
  | succ H ih =>
    have hm := congrArg (fun x => (a + c) * x) ih
    simp only [linearGeom, Nat.pow_succ] at *
    grind

theorem quadratic_geometric_identity (a c H : Nat) :
    c ^ 3 * quadraticGeom a (a + c) H +
      a ^ H * ((H + 1) * (H + 4) * c ^ 2 + (2 * H + 6) * a * c + 2 * a ^ 2) =
      (2 * a + 4 * c) * (a + c) ^ (H + 1) := by
  induction H with
  | zero => simp [quadraticGeom]; grind
  | succ H ih =>
    have hm := congrArg (fun x => (a + c) * x) ih
    simp only [quadraticGeom, Nat.pow_succ] at *
    grind

/-- Nonnegative remainders yield uniform finite partial-sum caps. -/
theorem geometric_caps (a c H : Nat) :
    c ^ 2 * linearGeom a (a + c) H ≤ (a + 4 * c) * (a + c) ^ H ∧
    c ^ 3 * quadraticGeom a (a + c) H ≤
      (2 * a + 4 * c) * (a + c) ^ (H + 1) := by
  have hl := linear_geometric_identity a c H
  have hq := quadratic_geometric_identity a c H
  omega

/-- Real root monotonicity interprets these as three strict slope caps. -/
theorem fractional_slope_constants :
    2 * 91 ^ 2 > 128 ^ 2 ∧ 2 * 157 ^ 2 > 3 * 128 ^ 2 ∧
    91 + 157 = 248 ∧
    8 * 77 ^ 4 > 128 ^ 4 ∧ 8 * 174 ^ 4 > 27 * 128 ^ 4 ∧
    77 + 174 < 252 ∧
    128 * 70 ^ 8 > 128 ^ 8 ∧ 128 * 183 ^ 8 > 3 ^ 7 * 128 ^ 8 ∧
    70 + 183 < 254 := by decide

#print axioms min_curvature
#print axioms total_diagonal
#print axioms green_boundary
#print axioms green_cap
#print axioms green_curvature
#print axioms linear_geometric_identity
#print axioms quadratic_geometric_identity
#print axioms geometric_caps
#print axioms fractional_slope_constants

end ActiveGapPotential
