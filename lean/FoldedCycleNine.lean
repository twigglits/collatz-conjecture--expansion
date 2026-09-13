/-
  Global closure repairs the first folded-order inversion.
  Build CollatzCycleCriterion and FoldedCycleBounds into LEAN_PATH first.
  Kernel proofs only. The finite sorting/permutation assembly is written in
  docs/FOLDED-CYCLE-INVERSIONS.md; no complete Collatz theorem is asserted.
-/
import FoldedCycleBounds

namespace FoldedCycleNine
open CollatzCycleCriterion FoldedCycleBounds

def Scale8 (c : Nat) : Prop := c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8

theorem oddPart_scale8 (c n : Nat) (hc : Scale8 c) :
    oddPart (c * n) = oddPart n := by
  rcases hc with rfl | rfl | rfl | rfl
  · simp
  · exact oddPart_twice n
  · have he : 4 * n = 2 * (2 * n) := by omega
    rw [he, oddPart_twice, oddPart_twice]
  · have he : 8 * n = 2 * (2 * (2 * n)) := by omega
    rw [he, oddPart_twice, oddPart_twice, oddPart_twice]

theorem folded_core8 (c x : Nat) (hc : Scale8 c) :
    oddPart (3 * (c * x) + c) = F x := by
  have he : 3 * (c * x) + c = c * (3 * x + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [he, oddPart_scale8 c (3 * x + 1) hc]
  rfl

/-- The only strict inversion with scales at most eight is the adjacent
    folded pair 8*x, 8*x+1. Oddness is essential. -/
theorem inversion_iff {c d x y : Nat}
    (hc : Scale8 c) (hd : Scale8 d) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (horder : c * x < d * y) :
    3 * (d * y) + d < 3 * (c * x) + c ↔
      c = 8 ∧ d = 1 ∧ y = 8 * x + 1 := by
  rcases hc with rfl | rfl | rfl | rfl <;>
    rcases hd with rfl | rfl | rfl | rfl <;> omega

theorem equal_numerators_same_successor {c d x y : Nat}
    (hc : Scale8 c) (hd : Scale8 d)
    (he : 3 * (c * x) + c = 3 * (d * y) + d) : F x = F y := by
  rw [← folded_core8 c x hc, ← folded_core8 d y hd]
  exact congrArg oddPart he

theorem strict_order_without_pair {c d x y : Nat}
    (hc : Scale8 c) (hd : Scale8 d) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (horder : c * x < d * y) (hnext : F x ≠ F y)
    (hpair : y ≠ 8 * x + 1) :
    3 * (c * x) + c < 3 * (d * y) + d := by
  have hne : 3 * (c * x) + c ≠ 3 * (d * y) + d := by
    intro he
    exact hnext (equal_numerators_same_successor hc hd he)
  have hn : ¬ 3 * (d * y) + d < 3 * (c * x) + c := by
    intro hi
    exact hpair ((inversion_iff hc hd hx hy horder).mp hi).2.2
  omega

/-- Two exact accelerated steps, valid for every positive odd x and also
    requiring only oddness as a natural-number premise. -/
theorem pair_two_steps (x : Nat) (hx : x % 2 = 1) :
    F (8 * x + 1) = 6 * x + 1 ∧ F (F (8 * x + 1)) = 9 * x + 2 := by
  have h1 := (actual_step 2 (8 * x + 1) (6 * x + 1) (by omega) (by omega)).1
  have h2 := (actual_step 1 (6 * x + 1) (9 * x + 2) (by omega) (by omega)).1
  exact ⟨h1, by rw [h1, h2]⟩

theorem pair_forces_maximum (S : Nat → Prop) (x M : Nat)
    (hx : x % 2 = 1) (hpair : S (8 * x + 1))
    (hclosed : ∀ n, S n → S (F n)) (hupper : ∀ n, S n → n ≤ M) :
    9 * x + 2 ≤ M := by
  have hmem := hclosed _ (hclosed _ hpair)
  rw [(pair_two_steps x hx).2] at hmem
  exact hupper _ hmem

/-- Successor closure eliminates inversions at a larger spread than the
    purely pointwise comparison. No periodicity is assumed in this lemma. -/
theorem strict_order_from_two_step_bound {m c d x y : Nat}
    (hc : Scale8 c) (hd : Scale8 d) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (horder : c * x < d * y) (hnext : F x ≠ F y)
    (hlower : m ≤ x) (hupper : F (F y) < 9 * m + 2) :
    3 * (c * x) + c < 3 * (d * y) + d := by
  apply strict_order_without_pair hc hd hx hy horder hnext
  intro he
  rw [he, (pair_two_steps x hx).2] at hupper
  omega

/-- In any bounded forward-invariant set with distinct successors, the
    folded numerators strictly preserve order when M < 9*m+2. -/
theorem closed_set_order (S : Nat → Prop) (m M c d x y : Nat)
    (hc : Scale8 c) (hd : Scale8 d) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (hsx : S x) (hsy : S y) (hxy : x ≠ y)
    (hclosed : ∀ n, S n → S (F n))
    (hinj : ∀ a b, S a → S b → F a = F b → a = b)
    (hlo : ∀ n, S n → m ≤ n) (hhi : ∀ n, S n → n ≤ M)
    (hspread : M < 9 * m + 2) (horder : c * x < d * y) :
    3 * (c * x) + c < 3 * (d * y) + d := by
  apply strict_order_from_two_step_bound hc hd hx hy horder
    (fun he => hxy (hinj x y hsx hsy he)) (hlo x hsx)
  have hb := hhi _ (hclosed _ (hclosed _ hsy))
  omega

theorem folded_numerator_range8 {m c x : Nat} (hm : 0 < m)
    (hc : Scale8 c) (hlo : 8 * m ≤ c * x) (hhi : c * x < 16 * m) :
    24 * m < 3 * (c * x) + c ∧ 3 * (c * x) + c ≤ 48 * m - 2 := by
  rcases hc with rfl | rfl | rfl | rfl <;> omega

theorem folded_numerator_span8 {m c d x y : Nat} (hm : 0 < m)
    (hc : Scale8 c) (hd : Scale8 d)
    (hxlo : 8 * m ≤ c * x) (hxhi : c * x < 16 * m)
    (hylo : 8 * m ≤ d * y) (hyhi : d * y < 16 * m) :
    3 * (d * y) + d < 2 * (3 * (c * x) + c) := by
  have ha := folded_numerator_range8 hm hc hxlo hxhi
  have hb := folded_numerator_range8 hm hd hylo hyhi
  omega

/-- An inversion with x=1 mod 4 forces the larger odd state (27*x+7)/2. -/
theorem pair_third_step (q : Nat) :
    F (F (F (8 * (4 * q + 1) + 1))) = 54 * q + 17 := by
  rw [(pair_two_steps (4 * q + 1) (by omega)).2]
  exact (actual_step 1 (9 * (4 * q + 1) + 2) (54 * q + 17)
    (by omega) (by omega)).1

/-- For x=5 mod 8, a fourth forced odd state already exceeds 16*x. -/
theorem pair_fourth_step (q : Nat) :
    F (F (F (F (8 * (8 * q + 5) + 1)))) = 162 * q + 107 ∧
      16 * (8 * q + 5) < 162 * q + 107 := by
  have he : 8 * q + 5 = 4 * (2 * q + 1) + 1 := by omega
  rw [he, pair_third_step]
  have hs := (actual_step 1 (54 * (2 * q + 1) + 17) (162 * q + 107)
    (by omega) (by omega)).1
  exact ⟨hs, by omega⟩

#print axioms inversion_iff
#print axioms strict_order_without_pair
#print axioms pair_two_steps
#print axioms pair_forces_maximum
#print axioms closed_set_order
#print axioms folded_numerator_range8
#print axioms folded_numerator_span8
#print axioms pair_third_step
#print axioms pair_fourth_step
end FoldedCycleNine
