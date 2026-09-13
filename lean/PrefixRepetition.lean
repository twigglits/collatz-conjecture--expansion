/-
  A finite obstruction to long repeated parity prefixes.
  Kernel proofs only; the asymptotic consequences are written separately.
  Build CollatzRepetition.olean in a temporary LEAN_PATH before checking.
-/
import CollatzRepetition

namespace CollatzRepetition

theorem shortcut_growth_step (n : Nat) : 2 * (U n + 1) ≤ 3 * (n + 1) := by
  unfold U
  split <;> omega

/-- The worst possible shortcut growth, including the additive correction. -/
theorem shortcut_growth_bound (k n : Nat) :
    2 ^ k * (orbit k n + 1) ≤ 3 ^ k * (n + 1) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih =>
    simp only [Nat.pow_succ, orbit]
    calc
      2 ^ k * 2 * (orbit k (U n) + 1) =
          2 * (2 ^ k * (orbit k (U n) + 1)) := by ac_rfl
      _ ≤ 2 * (3 ^ k * (U n + 1)) := Nat.mul_le_mul_left 2 (ih (U n))
      _ = 3 ^ k * (2 * (U n + 1)) := by ac_rfl
      _ ≤ 3 ^ k * (3 * (n + 1)) :=
        Nat.mul_le_mul_left (3 ^ k) (shortcut_growth_step n)
      _ = 3 ^ k * 3 * (n + 1) := by ac_rfl

/-- A prefix agrees with its shift by ell for m bits. If the powers leave
    insufficient room for distinct congruent states, that shift returns n. -/
theorem prefix_repetition_forces_return {ell m n : Nat}
    (hp : SameParity m n (orbit ell n))
    (hsize : 3 ^ ell * (n + 1) ≤ 2 ^ (m + ell)) :
    orbit ell n = n := by
  have htwo : 0 < 2 ^ ell := Nat.pow_pos (by decide)
  have h23 : 2 ^ ell ≤ 3 ^ ell := Nat.pow_le_pow_left (by decide : 2 ≤ 3) ell
  have hpow : 2 ^ (m + ell) = 2 ^ ell * 2 ^ m := by
    rw [Nat.pow_add]
    ac_rfl
  have hn : n < 2 ^ m := by
    have h := Nat.le_trans (Nat.mul_le_mul_right (n + 1) h23) hsize
    rw [hpow] at h
    have hcancel := Nat.le_of_mul_le_mul_left h htwo
    omega
  have hx : orbit ell n < 2 ^ m := by
    have h := Nat.le_trans (shortcut_growth_bound ell n) hsize
    rw [hpow] at h
    have hcancel := Nat.le_of_mul_le_mul_left h htwo
    omega
  exact (collision_below_power hp hn hx).symm

theorem prefix_square_forces_return {ell n : Nat}
    (hp : SameParity ell n (orbit ell n))
    (hsize : 3 ^ ell * (n + 1) ≤ 4 ^ ell) :
    orbit ell n = n := by
  apply prefix_repetition_forces_return hp
  have hpow : 4 ^ ell = 2 ^ (ell + ell) := by
    rw [Nat.pow_add, ← Nat.mul_pow]
  simpa only [hpow] using hsize

theorem repeated_prefix_periodic {ell m n : Nat}
    (hp : SameParity m n (orbit ell n))
    (hsize : 3 ^ ell * (n + 1) ≤ 2 ^ (m + ell)) (t : Nat) :
    orbit (ell + t) n = orbit t n := by
  rw [orbit_add, prefix_repetition_forces_return hp hsize]

/-- Necessary integer inequality for every parity match at a nonreturning shift. -/
theorem nonreturn_prefix_size {ell m n : Nat}
    (hp : SameParity m n (orbit ell n)) (hn : orbit ell n ≠ n) :
    2 ^ (m + ell) < 3 ^ ell * (n + 1) := by
  apply Nat.lt_of_not_ge
  intro hsize
  exact hn (prefix_repetition_forces_return hp hsize)

#print axioms shortcut_growth_bound
#print axioms prefix_repetition_forces_return
#print axioms prefix_square_forces_return
#print axioms repeated_prefix_periodic
#print axioms nonreturn_prefix_size

end CollatzRepetition
