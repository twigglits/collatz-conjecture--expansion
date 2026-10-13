/-
  A comparison map, NOT the Collatz map. It has ordinary even halving and
  the known 1,4,2 cycle, but its altered odd branch has an explicit escape.
  The density and first-passage calculations are separate written proofs.
-/
import CollatzContradiction

namespace DensityCountermodel

def step (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else
  if n = 1 then 4 else
  let c := if n % 4 = 1 then 3 else 1
  let m := (n + c) / 4
  let p := 2 ^ m.log2
  if m = p then
    if c = 3 then 2 * (4 * (m / 2) - 3) else 2 * (8 * m - 1)
  else
    let r := m - p
    let h := if c = 3 ∧ r = 1 then m.log2 + 2 else m.log2 - r.log2 + 1
    2 ^ h * (4 * r - c)

def iterate : Nat → Nat → Nat
  | 0, n => n
  | t + 1, n => iterate t (step n)

def spine (k : Nat) : Nat := 4 * 2 ^ k - 1

theorem even_step (n : Nat) (h : n % 2 = 0) : step n = n / 2 := by
  simp [step, h]

theorem cycle_one : step 1 = 4 := rfl
theorem cycle_four : step 4 = 2 := rfl
theorem cycle_two : step 2 = 1 := rfl

theorem spine_lower (k : Nat) : 3 ≤ spine k := by
  have hp := Nat.two_pow_pos k
  unfold spine
  omega

theorem spine_step (k : Nat) : step (spine k) = 2 * spine (k + 1) := by
  have hp := Nat.two_pow_pos k
  have he : spine k % 2 ≠ 0 := by unfold spine; omega
  have h1 : spine k ≠ 1 := by have := spine_lower k; omega
  have h4 : spine k % 4 ≠ 1 := by unfold spine; omega
  have hm : (spine k + 1) / 4 = 2 ^ k := by unfold spine; omega
  simp only [step, if_neg he, if_neg h1, if_neg h4, hm, Nat.log2_two_pow,
    show ¬ (1 : Nat) = 3 by decide, if_false, ite_true]
  unfold spine
  rw [Nat.pow_succ]
  omega

theorem spine_two_steps (k : Nat) : iterate 2 (spine k) = spine (k + 1) := by
  simp only [iterate, spine_step]
  rw [even_step _ (by omega)]
  omega

theorem iterate_add : ∀ t u n, iterate (t + u) n = iterate u (iterate t n)
  | 0, _, _ => by simp [iterate]
  | t + 1, u, n => by
    have he : t + 1 + u = (t + u) + 1 := by omega
    rw [he]
    exact iterate_add t u (step n)

theorem iterate_even (t k : Nat) : iterate (2 * t) (spine k) = spine (k + t) := by
  induction t with
  | zero => simp [iterate]
  | succ t ih =>
    have he : 2 * (t + 1) = 2 * t + 2 := by omega
    rw [he, iterate_add, ih, spine_two_steps]
    exact congrArg spine (Nat.add_assoc k t 1)

theorem iterate_odd (t k : Nat) :
    iterate (2 * t + 1) (spine k) = 2 * spine (k + t + 1) := by
  rw [iterate_add, iterate_even]
  exact spine_step (k + t)

theorem spine_never_one (k t : Nat) : iterate t (spine k) ≠ 1 := by
  have ht := Nat.mod_lt t (by decide : 0 < 2)
  by_cases he : t % 2 = 0
  · have hr : t = 2 * (t / 2) := by omega
    rw [hr, iterate_even]
    have := spine_lower (k + t / 2)
    omega
  · have hr : t = 2 * (t / 2) + 1 := by omega
    rw [hr, iterate_odd]
    have := spine_lower (k + t / 2 + 1)
    omega

theorem exponent_lower (k : Nat) : k < 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

theorem spine_unbounded (R : Nat) : ∃ t, R < iterate t (spine 0) := by
  refine ⟨2 * (R + 1), ?_⟩
  rw [iterate_even]
  simp only [Nat.zero_add]
  have hp := exponent_lower (R + 1)
  unfold spine
  omega

theorem differs_from_collatz : step 3 ≠ OrdinaryCollatz.C 3 := by decide

#print axioms even_step
#print axioms cycle_one
#print axioms cycle_four
#print axioms cycle_two
#print axioms spine_lower
#print axioms spine_step
#print axioms spine_two_steps
#print axioms iterate_add
#print axioms iterate_even
#print axioms iterate_odd
#print axioms spine_never_one
#print axioms exponent_lower
#print axioms spine_unbounded
#print axioms differs_from_collatz

end DensityCountermodel
