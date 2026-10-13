/-
  Reflection between the two shortcut maps (3n+1)/2 and (3n-1)/2.
  This certifies a limitation of whole-residue coalescence statistics.
  It does not prove or disprove positive-integer Collatz.
-/
import CollatzAffine

namespace ReflectedCoalescence
open CollatzAffine

def minusU (n : Nat) : Nat := if n % 2 = 1 then (3 * n - 1) / 2 else n / 2

def minusOrbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => minusOrbit k (minusU n)

def minusWeight : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + minusWeight k (minusU n)

theorem reflected_pair (k q n m : Nat) (h : n + m = 2 ^ k * q) :
    minusOrbit k n + orbit k m = 3 ^ minusWeight k n * q ∧
      minusWeight k n = wt k m := by
  induction k generalizing q n m with
  | zero => simpa [minusOrbit, orbit, minusWeight, wt] using h
  | succ k ih =>
    have hs : n + m = 2 * (2 ^ k * q) := by
      simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    by_cases hn : n % 2 = 1
    · have hm : m % 2 = 1 := by omega
      have hnext : minusU n + U m = 2 ^ k * (3 * q) := by
        have hc : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := Nat.mul_left_comm _ _ _
        rw [hc]
        unfold minusU U
        rw [if_pos hn, if_pos hm]
        omega
      obtain ⟨he, hw⟩ := ih (3 * q) (minusU n) (U m) hnext
      constructor
      · change minusOrbit k (minusU n) + orbit k (U m) = _
        rw [he]
        simp only [minusWeight, hn, Nat.pow_add, Nat.pow_one]
        ac_rfl
      · simp only [minusWeight, wt, hn, hm, hw]
    · have hn0 : n % 2 = 0 := by omega
      have hm : ¬ m % 2 = 1 := by omega
      have hm0 : m % 2 = 0 := by omega
      have hnext : minusU n + U m = 2 ^ k * q := by
        unfold minusU U
        rw [if_neg hn, if_neg hm]
        omega
      obtain ⟨he, hw⟩ := ih q (minusU n) (U m) hnext
      constructor
      · simpa only [minusOrbit, orbit, minusWeight, hn0, Nat.zero_add] using he
      · simp only [minusWeight, wt, hn0, hm0, hw]

theorem reflected_residue (k r : Nat) (hr : r ≤ 2 ^ k) :
    minusOrbit k r + orbit k (2 ^ k - r) = 3 ^ minusWeight k r ∧
      minusWeight k r = wt k (2 ^ k - r) := by
  simpa only [Nat.mul_one] using reflected_pair k 1 r (2 ^ k - r) (by omega)

theorem reflected_adjacent_coalescence (k r : Nat) (hr : r < 2 ^ k) :
    (orbit k r = orbit k (r + 1) ∧ wt k r = wt k (r + 1)) ↔
    (minusOrbit k (2 ^ k - 1 - r) = minusOrbit k (2 ^ k - r) ∧
      minusWeight k (2 ^ k - 1 - r) = minusWeight k (2 ^ k - r)) := by
  have h0 := reflected_pair k 1 (2 ^ k - r) r (by omega)
  have h1 := reflected_pair k 1 (2 ^ k - 1 - r) (r + 1) (by omega)
  simp only [Nat.mul_one] at h0 h1
  constructor
  · rintro ⟨he, hw⟩
    have hm : minusWeight k (2 ^ k - 1 - r) = minusWeight k (2 ^ k - r) := by
      rw [h1.2, h0.2, hw]
    have hs0 := h0.1
    have hs1 := h1.1
    rw [hm] at hs1
    exact ⟨by omega, hm⟩
  · rintro ⟨he, hm⟩
    have hw : wt k r = wt k (r + 1) := by rw [← h0.2, ← h1.2, hm]
    have hs0 := h0.1
    have hs1 := h1.1
    rw [hm] at hs1
    exact ⟨by omega, hw⟩

theorem minus_cycle_closed {n : Nat} (h : n = 5 ∨ n = 7 ∨ n = 10) :
    minusU n = 5 ∨ minusU n = 7 ∨ minusU n = 10 := by
  rcases h with h | h | h <;> subst n <;> decide

theorem minus_cycle_trapped (k n : Nat) (h : n = 5 ∨ n = 7 ∨ n = 10) :
    minusOrbit k n = 5 ∨ minusOrbit k n = 7 ∨ minusOrbit k n = 10 := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => exact ih (minusU n) (minus_cycle_closed h)

theorem minus5_no_one (k : Nat) : minusOrbit k 5 ≠ 1 := by
  have h := minus_cycle_trapped k 5 (Or.inl rfl)
  omega

theorem plus5_hits_one : orbit 4 5 = 1 := by decide

#print axioms reflected_pair
#print axioms reflected_residue
#print axioms reflected_adjacent_coalescence
#print axioms minus_cycle_closed
#print axioms minus_cycle_trapped
#print axioms minus5_no_one
#print axioms plus5_hits_one
end ReflectedCoalescence
