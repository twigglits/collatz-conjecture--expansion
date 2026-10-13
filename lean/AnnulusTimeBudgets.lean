/-
  Known-cycle arithmetic for complete temporal sums on finite annuli.
  Geometric limits and the conditional averaged-energy criterion remain
  written in docs/ANNULUS-TIME-BUDGETS.md.
-/
import EscapeWeightRefinements

namespace AnnulusTimeBudgets
open CollatzAffine EscapeWeightRefinements

theorem cycle_step (x : Nat) (hx : x = 1 ∨ x = 2) :
    U x = 1 ∨ U x = 2 := by
  rcases hx with rfl | rfl <;> decide

theorem cycle_two_steps (x : Nat) (hx : x = 1 ∨ x = 2) :
    orbit 2 x = x ∧ wt 2 x = 1 := by
  rcases hx with rfl | rfl <;> decide

theorem cycle_continuation (n T j : Nat)
    (hx : orbit T n = 1 ∨ orbit T n = 2) :
    orbit (T + 2 * j) n = orbit T n ∧ wt (T + 2 * j) n = wt T n + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have ht : T + 2 * (j + 1) = (T + 2 * j) + 2 := by omega
    rw [ht, orbit_add, weight_add, ih.1, ih.2,
      (cycle_two_steps _ hx).1, (cycle_two_steps _ hx).2]
    omega

theorem cycle_count_comparison (n m T j c : Nat)
    (hx : orbit T n = 1 ∨ orbit T n = 2)
    (hy : orbit T m = 1 ∨ orbit T m = 2) :
    (c + wt (T + 2 * j) m < wt (T + 2 * j) n) ↔
      c + wt T m < wt T n := by
  rw [(cycle_continuation n T j hx).2, (cycle_continuation m T j hy).2]
  omega

/-- After two cycle steps, the weight numerator triples and denominator quadruples. -/
theorem cycle_weight_data (n T : Nat)
    (hx : orbit T n = 1 ∨ orbit T n = 2) :
    3 ^ wt (T + 2) n = 3 * 3 ^ wt T n ∧
      2 ^ (T + 2) * orbit (T + 2) n = 4 * (2 ^ T * orbit T n) := by
  have h := cycle_continuation n T 1 hx
  simp only [Nat.mul_one] at h
  rw [h.1, h.2, Nat.pow_succ, Nat.pow_add]
  constructor
  · ac_rfl
  · change 2 ^ T * 4 * orbit T n = 4 * (2 ^ T * orbit T n)
    ac_rfl

def geometricNumerator : Nat → Nat
  | 0 => 0
  | j + 1 => 16 ^ j + 9 * geometricNumerator j

theorem quadratic_geometric_identity (j : Nat) :
    7 * geometricNumerator j + 9 ^ j = 16 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [geometricNumerator, Nat.pow_succ]
    grind

#print axioms cycle_step
#print axioms cycle_two_steps
#print axioms cycle_continuation
#print axioms cycle_count_comparison
#print axioms cycle_weight_data
#print axioms quadratic_geometric_identity

end AnnulusTimeBudgets
