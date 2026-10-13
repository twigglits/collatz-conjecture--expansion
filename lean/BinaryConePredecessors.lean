/-
  A convergent inverse spine and propagation through every binary cone.
  Density of its leading significands is a written irrational-rotation
  argument in docs/ANNULUS-TIME-BUDGETS.md, not a kernel theorem.
-/
import UniformInverseBranching
import EscapeWeightRefinements

namespace BinaryConePredecessors
open CollatzAffine UniformInverseBranching EscapeWeightRefinements

theorem child_error (a : Nat) (ha : a % 3 ≠ 0) :
    4 ≤ 64 * a - 3 * child a false ∧ 64 * a - 3 * child a false ≤ 32 := by
  have hr : a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 4 ∨
      a % 9 = 5 ∨ a % 9 = 7 ∨ a % 9 = 8 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals simp only [child, hr, Bool.false_eq_true, reduceIte]
  all_goals omega

def spine : Nat → Nat
  | 0 => 1
  | j + 1 => child (spine j) false

theorem spine_facts (j : Nat) :
    0 < spine j ∧ spine j % 3 ≠ 0 ∧
      orbit (6 * j) (spine j) = 1 ∧ wt (6 * j) (spine j) = j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hc := child_facts (spine j) ih.2.1 false
    have ht : 6 * (j + 1) = 6 + 6 * j := by omega
    refine ⟨hc.1, hc.2.1, ?_, ?_⟩
    · rw [spine, ht, orbit_add, hc.2.2.2.2.2, ih.2.2.1]
    · rw [spine, ht, weight_add, hc.2.2.2.2.1, hc.2.2.2.2.2, ih.2.2.2]
      omega

theorem spine_recurrence (j : Nat) :
    3 * spine (j + 1) + (64 * spine j - 3 * spine (j + 1)) = 64 * spine j ∧
      4 ≤ 64 * spine j - 3 * spine (j + 1) ∧
      64 * spine j - 3 * spine (j + 1) ≤ 32 := by
  have hc := child_facts (spine j) (spine_facts j).2.1 false
  have he := child_error (spine j) (spine_facts j).2.1
  change 3 * child (spine j) false + (64 * spine j - 3 * child (spine j) false) =
      64 * spine j ∧ _
  exact ⟨by omega, he⟩

theorem spine_upper (j : Nat) : 3 ^ j * spine j ≤ 64 ^ j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have he := (spine_recurrence j).1
    have h1 := Nat.mul_le_mul_left (3 ^ j) (show 3 * spine (j + 1) ≤ 64 * spine j by omega)
    have h2 := Nat.mul_le_mul_left 64 ih
    simp only [Nat.pow_succ]
    grind

theorem spine_lower (j : Nat) :
    29 * 64 ^ j + 32 * 3 ^ j ≤ 61 * 3 ^ j * spine j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have he := spine_recurrence j
    have hl : 64 * spine j ≤ 3 * spine (j + 1) + 32 := by omega
    have h1 := Nat.mul_le_mul_left (61 * 3 ^ j) hl
    have h2 := Nat.mul_le_mul_left 64 ih
    simp only [Nat.pow_succ]
    grind

/-- Closure under both children propagates through the entire binary cone. -/
theorem binary_cone_closed (P : Nat → Prop)
    (h0 : ∀ n, P n → P (2 * n)) (h1 : ∀ n, P n → P (2 * n + 1))
    (n : Nat) (hn : P n) (j r : Nat) (hr : r < 2 ^ j) : P (2 ^ j * n + r) := by
  induction j generalizing r with
  | zero =>
    have hz : r = 0 := by simpa using hr
    simpa [hz] using hn
  | succ j ih =>
    have hb : r / 2 < 2 ^ j := by
      rw [Nat.pow_succ] at hr
      omega
    have hp := ih (r / 2) hb
    have hd := Nat.mod_add_div r 2
    have he : 2 ^ (j + 1) * n + r = 2 * (2 ^ j * n + r / 2) + r % 2 := by
      rw [Nat.pow_succ]
      grind
    rw [he]
    have hm : r % 2 = 0 ∨ r % 2 = 1 := by omega
    rcases hm with hm | hm
    · simpa only [hm, Nat.add_zero] using h0 _ hp
    · simpa only [hm] using h1 _ hp

#print axioms child_error
#print axioms spine_facts
#print axioms spine_recurrence
#print axioms spine_upper
#print axioms spine_lower
#print axioms binary_cone_closed

end BinaryConePredecessors
