/-
  A bounded real pseudo-trajectory with incompatible integer parities.
  Its state after t=s+1 steps is -a(s)/2^(s+1), with a(s) odd.
  This is NOT a positive-integer Collatz trajectory.
  Real limits and aperiodicity are proved in APERIODIC-ATTEMPT.md.
-/
namespace RealShadowObstruction

def a : Nat → Nat
  | 0 => 5
  | s + 1 => if a s < 2 ^ (s + 2) then 3 * a s - 2 ^ (s + 1) else a s

def ones : Nat → Nat
  | 0 => 1
  | s + 1 => if a s < 2 ^ (s + 2) then ones s + 1 else ones s

theorem invariant (s : Nat) :
    2 ^ (s + 1) ≤ a s ∧ 2 * a s ≤ 5 * 2 ^ (s + 1) ∧ a s % 2 = 1 := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hp : 2 ^ (s + 2) = 2 * 2 ^ (s + 1) := by
      rw [Nat.pow_succ]
      ac_rfl
    have heven : 2 ^ (s + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
    have hpos : 0 < 2 ^ (s + 1) := Nat.pow_pos (by decide)
    simp only [a]
    split <;> rw [show s + 1 + 1 = s + 2 by omega, hp] <;> omega

/-- The numerator grows by at most 13/5 on a symbol 1, and is unchanged
    on a symbol 0. This is a finite, exact version of the density bound. -/
theorem numerator_bound (s : Nat) : 5 ^ ones s * a s ≤ 2 * 13 ^ ones s := by
  induction s with
  | zero => decide
  | succ s ih =>
    have hb := invariant s
    simp only [a, ones]
    split
    · rename_i h
      have hs : 5 * (3 * a s - 2 ^ (s + 1)) ≤ 13 * a s := by omega
      simp only [Nat.pow_succ]
      calc
        5 ^ ones s * 5 * (3 * a s - 2 ^ (s + 1)) =
            5 ^ ones s * (5 * (3 * a s - 2 ^ (s + 1))) := by ac_rfl
        _ ≤ 5 ^ ones s * (13 * a s) := Nat.mul_le_mul_left _ hs
        _ = 13 * (5 ^ ones s * a s) := by ac_rfl
        _ ≤ 13 * (2 * 13 ^ ones s) := Nat.mul_le_mul_left _ ih
        _ = 2 * (13 ^ ones s * 13) := by ac_rfl
    · exact ih

/-- 2^t <= 2*(13/5)^J_t after clearing denominators. -/
theorem density_constraint (s : Nat) :
    5 ^ ones s * 2 ^ (s + 1) ≤ 2 * 13 ^ ones s := by
  exact Nat.le_trans (Nat.mul_le_mul_left _ (invariant s).1) (numerator_bound s)

/-- No state of this shadow can be represented over an odd denominator.
    A sign on the numerator does not change this denominator obstruction. -/
theorem no_odd_denominator (s b d : Nat) (hd : d % 2 = 1) :
    a s * d ≠ b * 2 ^ (s + 1) := by
  intro he
  have hm := congrArg (fun x : Nat => x % 2) he
  have hp : 2 ^ (s + 1) % 2 = 0 := by rw [Nat.pow_succ]; omega
  simp [Nat.mul_mod, (invariant s).2.2, hd, hp] at hm

#print axioms invariant
#print axioms numerator_bound
#print axioms density_constraint
#print axioms no_odd_denominator

end RealShadowObstruction
