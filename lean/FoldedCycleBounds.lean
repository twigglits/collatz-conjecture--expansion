/-
  Finite arithmetic supporting docs/FOLDED-CYCLES.md.
  The sorting/rank argument and its assembly for every cycle are written.
  Requires CollatzCycleCriterion.olean on LEAN_PATH.
-/
import CollatzCycleCriterion

namespace FoldedCycleBounds
open CollatzCycleCriterion

def SmallScale (c : Nat) : Prop := c = 1 ∨ c = 2 ∨ c = 4

theorem oddPart_twice (n : Nat) : oddPart (2 * n) = oddPart n := by
  by_cases hn : n = 0
  · simp only [hn, Nat.mul_zero]
  · rw [oddPart.eq_def, dif_pos (by omega)]
    congr 1
    omega

theorem oddPart_scale (c n : Nat) (hc : SmallScale c) :
    oddPart (c * n) = oddPart n := by
  rcases hc with rfl | rfl | rfl
  · simp
  · exact oddPart_twice n
  · have he : 4 * n = 2 * (2 * n) := by omega
    rw [he, oddPart_twice, oddPart_twice]

theorem folded_core (c x : Nat) (hc : SmallScale c) :
    oddPart (3 * (c * x) + c) = F x := by
  have he : 3 * (c * x) + c = c * (3 * x + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    ac_rfl
  rw [he, oddPart_scale c (3 * x + 1) hc]
  rfl

/-- Distinct successors remove the only possible tie in integer order. -/
theorem folded_numerators_strict {c d x y : Nat}
    (hc : SmallScale c) (hd : SmallScale d)
    (horder : c * x < d * y) (hnext : F x ≠ F y) :
    3 * (c * x) + c < 3 * (d * y) + d := by
  have hc4 : c ≤ 4 := by rcases hc with rfl | rfl | rfl <;> decide
  have hd1 : 1 ≤ d := by rcases hd with rfl | rfl | rfl <;> decide
  have hne : 3 * (c * x) + c ≠ 3 * (d * y) + d := by
    intro he
    apply hnext
    rw [← folded_core c x hc, ← folded_core d y hd]
    exact congrArg oddPart he
  omega

theorem folded_numerator_range {m c x : Nat} (hm : 0 < m)
    (hc : SmallScale c) (hlo : 4 * m ≤ c * x) (hhi : c * x < 8 * m) :
    12 * m < 3 * (c * x) + c ∧ 3 * (c * x) + c ≤ 24 * m - 2 := by
  rcases hc with rfl | rfl | rfl <;> omega

/-- The upper folded numerator is less than twice the lower one. -/
theorem folded_numerator_span {m c d x y : Nat} (hm : 0 < m)
    (hc : SmallScale c) (hd : SmallScale d)
    (hxlo : 4 * m ≤ c * x) (hxhi : c * x < 8 * m)
    (hylo : 4 * m ≤ d * y) (hyhi : d * y < 8 * m) :
    3 * (d * y) + d < 2 * (3 * (c * x) + c) := by
  have hx := folded_numerator_range hm hc hxlo hxhi
  have hy := folded_numerator_range hm hd hylo hyhi
  omega

/-- A rotation visiting every rank must have coprime step and size. -/
theorem full_rotation_coprime {k r : Nat} (hk : 0 < k)
    (hcover : ∀ i, i < k → ∃ j, (j * r) % k = i) : Nat.gcd k r = 1 := by
  by_cases hk1 : k = 1
  · simp [hk1]
  · obtain ⟨j, hj⟩ := hcover 1 (by omega)
    have hd : Nat.gcd k r ∣ j * r :=
      Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right k r) j
    have hm := (Nat.dvd_mod_iff (Nat.gcd_dvd_left k r)).mpr hd
    rw [hj] at hm
    exact Nat.eq_one_of_dvd_one hm

/-- Local order can reverse arbitrarily close above spread eight.
    These are two actual steps, not a claimed cycle. -/
theorem local_order_reversal (q : Nat) :
    let m := 4 * q + 3
    F m = 6 * q + 5 ∧ F (8 * m + 1) = 6 * m + 1 ∧
    m ≤ 6 * q + 5 ∧ 6 * q + 5 ≤ 8 * m + 1 ∧
    m ≤ 6 * m + 1 ∧ 6 * m + 1 ≤ 8 * m + 1 ∧
    8 * m < 8 * m + 1 ∧ 3 * (8 * m) + 8 > 3 * (8 * m + 1) + 1 := by
  dsimp
  have ha := actual_step 1 (4 * q + 3) (6 * q + 5) (by omega) (by omega)
  have hb := actual_step 2 (8 * (4 * q + 3) + 1) (6 * (4 * q + 3) + 1)
    (by omega) (by omega)
  exact ⟨ha.1, hb.1, by omega⟩

#print axioms oddPart_twice
#print axioms folded_core
#print axioms folded_numerators_strict
#print axioms folded_numerator_range
#print axioms folded_numerator_span
#print axioms full_rotation_coprime
#print axioms local_order_reversal
end FoldedCycleBounds
