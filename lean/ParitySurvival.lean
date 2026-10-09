/-
  Exact parity restrictions on surviving prefixes and linear credit bounds.
  Standalone Lean 4. No universal parity or credit bound is asserted.
-/
import CoalescenceGrades
import WeightedSurvivors

namespace CollatzPacking

def AvoidsFloor (H k n : Nat) : Prop := ∀ i, i < k → H < orbit i n

theorem growth_of_odd_bound (P Q H : Nat)
    (hodd : ∀ n, H < n → n % 2 = 1 → 2 * P * U n ≤ Q * n) :
    ∀ k n, AvoidsFloor H k n →
      P ^ wt k n * 2 ^ k * orbit k n ≤ Q ^ wt k n * n
  | 0, n, _ => by simp [wt, orbit]
  | k + 1, n, hs => by
    have hn := hs 0 (by omega)
    change H < n at hn
    have ht : AvoidsFloor H k (U n) := by
      intro i hi
      exact hs (i + 1) (by omega)
    have ih := growth_of_odd_bound P Q H hodd k (U n) ht
    by_cases ho : n % 2 = 1
    · have h := Nat.mul_le_mul_left (2 * P) ih
      have he : 2 * P * (Q ^ wt k (U n) * U n) =
          Q ^ wt k (U n) * (2 * P * U n) := by ac_rfl
      rw [he] at h
      have hc := Nat.le_trans h (Nat.mul_le_mul_left (Q ^ wt k (U n)) (hodd n hn ho))
      simpa only [wt, orbit, ho, Nat.pow_add, Nat.pow_one, Nat.pow_succ,
        Nat.pow_zero, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
    · have hz : n % 2 = 0 := by omega
      have hu : 2 * U n = n := by simp only [U, if_neg ho]; omega
      have h := Nat.mul_le_mul_left 2 ih
      have he : 2 * (Q ^ wt k (U n) * U n) =
          Q ^ wt k (U n) * (2 * U n) := by ac_rfl
      rw [he, hu] at h
      simpa only [wt, orbit, hz, Nat.zero_add, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

/-- Eliminate rational growth constants using one checked power comparison. -/
theorem growth_to_count {P Q a c k j n b : Nat} (hP : 0 < P)
    (h : P ^ j * 2 ^ k ≤ Q ^ j * n) (hn : n ≤ 2 ^ b)
    (hr : Q ^ a ≤ P ^ a * 2 ^ c) : a * k ≤ c * j + a * b := by
  have hp := Nat.pow_le_pow_left h a
  have hq := Nat.pow_le_pow_left hr j
  have hb := Nat.pow_le_pow_left hn a
  have hc := Nat.mul_le_mul hq hb
  simp only [Nat.mul_pow, ← Nat.pow_mul] at hp hc
  have he1 : j * a = a * j := Nat.mul_comm _ _
  have he2 : k * a = a * k := Nat.mul_comm _ _
  have he3 : b * a = a * b := Nat.mul_comm _ _
  rw [he1, he2] at hp
  rw [he3] at hc
  have hh := Nat.le_trans hp hc
  have he : (P ^ (a * j) * 2 ^ (c * j)) * 2 ^ (a * b) =
      P ^ (a * j) * 2 ^ (c * j + a * b) := by
    rw [Nat.pow_add, Nat.mul_assoc]
  rw [he] at hh
  have hle := Nat.le_of_mul_le_mul_left hh (Nat.pow_pos hP)
  by_cases hgoal : a * k ≤ c * j + a * b
  · exact hgoal
  · have hlt : 2 ^ (c * j + a * b) < 2 ^ (a * k) :=
      Nat.pow_lt_pow_right (by decide) (by omega)
    omega

theorem avoiding_one_count {k n b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hs : AvoidsFloor 1 k n) : 4 * k ≤ 7 * wt k n + 4 * b := by
  have hodd : ∀ x, 1 < x → x % 2 = 1 → 2 * 3 * U x ≤ 10 * x := by
    intro x hx ho
    simp only [U, if_pos ho]
    omega
  have hg := growth_of_odd_bound 3 10 1 hodd k n hs
  have hpos : 1 ≤ orbit k n := grade_orbit_positive k n hn
  have hm := Nat.mul_le_mul_left (3 ^ wt k n * 2 ^ k) hpos
  rw [Nat.mul_one] at hm
  exact growth_to_count (by decide : 0 < 3) (Nat.le_trans hm hg) hb
    (by decide : 10 ^ 4 ≤ 3 ^ 4 * 2 ^ 7)

theorem avoiding64_count {k n b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hs : AvoidsFloor 64 k n) : 5 * k ≤ 8 * wt k n + 5 * b := by
  have hodd : ∀ x, 64 < x → x % 2 = 1 → 2 * 65 * U x ≤ 196 * x := by
    intro x hx ho
    simp only [U, if_pos ho]
    omega
  have hg := growth_of_odd_bound 65 196 64 hodd k n hs
  have hpos : 1 ≤ orbit k n := grade_orbit_positive k n hn
  have hm := Nat.mul_le_mul_left (65 ^ wt k n * 2 ^ k) hpos
  rw [Nat.mul_one] at hm
  exact growth_to_count (by decide : 0 < 65) (Nat.le_trans hm hg) hb
    (by decide : 196 ^ 5 ≤ 65 ^ 5 * 2 ^ 8)

theorem packing_base64 {n : Nat} (hn : 0 < n) (h64 : n ≤ 64) :
    ∃ t, t ≤ 71 ∧ orbit t n = 1 := by
  obtain ⟨t, ht⟩ := WeightedSurvivors.base64 ⟨n, by omega⟩ hn
  refine ⟨t.val, by have := t.isLt; omega, ?_⟩
  rw [grade_ordinary_bridge]
  exact ht

/-- A single endpoint count bound suffices at this explicitly selected clock. -/
theorem endpoint_credit_hits_floor {n A b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hw : 2 * wt (4 * A + 5 * b + 1) n ≤ (4 * A + 5 * b + 1) + A) :
    ∃ t, t ≤ 4 * A + 5 * b ∧ orbit t n ≤ 64 := by
  apply Classical.byContradiction
  intro h
  have hs : AvoidsFloor 64 (4 * A + 5 * b + 1) n := by
    intro i hi
    by_cases hlow : orbit i n ≤ 64
    · exact False.elim (h ⟨i, by omega, hlow⟩)
    · omega
  have hc := avoiding64_count hn hb hs
  omega

theorem endpoint_credit_reaches {n A b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hw : 2 * wt (4 * A + 5 * b + 1) n ≤ (4 * A + 5 * b + 1) + A) :
    ∃ t, t ≤ 4 * A + 5 * b + 71 ∧ orbit t n = 1 := by
  obtain ⟨s, hs, hlow⟩ := endpoint_credit_hits_floor hn hb hw
  obtain ⟨t, ht, hone⟩ := packing_base64 (grade_orbit_positive s n hn) hlow
  exact ⟨t + s, by omega, by rw [orbit_add, hone]⟩

/-- This improves the earlier exponential-in-credit conditional time bound. -/
theorem linear_credit_reaches {n A b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hc : ∀ k, 2 * wt k n ≤ k + A) :
    ∃ t, t ≤ 4 * A + 5 * b + 71 ∧ orbit t n = 1 :=
  endpoint_credit_reaches hn hb (hc _)

theorem nonconvergent_avoids64 {n : Nat} (hn : 0 < n)
    (hbad : ¬ OrdinaryCollatz.ReachesOne n) (k : Nat) : 64 < orbit k n := by
  by_cases hsmall : orbit k n ≤ 64
  · obtain ⟨t, _, ht⟩ := packing_base64 (grade_orbit_positive k n hn) hsmall
    have he : orbit (t + k) n = 1 := by rw [orbit_add, ht]
    exact False.elim (hbad ((grade_reaches_bridge n).mpr ⟨t + k, he⟩))
  · omega

/-- Both a nontrivial cycle and a divergent counterexample would obey this. -/
theorem nonconvergent_count_lower {n b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hbad : ¬ OrdinaryCollatz.ReachesOne n) (k : Nat) :
    5 * k ≤ 8 * wt k n + 5 * b :=
  avoiding64_count hn hb (fun i _ => nonconvergent_avoids64 hn hbad i)

theorem nonconvergent_credit_at_clock {n b : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hbad : ¬ OrdinaryCollatz.ReachesOne n) (A : Nat) :
    (4 * A + 5 * b + 1) + A < 2 * wt (4 * A + 5 * b + 1) n := by
  have h := nonconvergent_count_lower hn hb hbad (4 * A + 5 * b + 1)
  omega

theorem sparse_prefix_reaches {n b k : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hsparse : 8 * wt k n + 5 * b < 5 * k) : OrdinaryCollatz.ReachesOne n := by
  apply Classical.byContradiction
  intro hbad
  have h := nonconvergent_count_lower hn hb hbad k
  omega

/-- A logarithmic credit proposal already implies a logarithmic time proposal. -/
theorem logarithmic_credit_to_time {n b C D A : Nat} (hn : 0 < n) (hb : n ≤ 2 ^ b)
    (hA : A ≤ C * b + D) (hc : ∀ k, 2 * wt k n ≤ k + A) :
    ∃ t, t ≤ (4 * C + 5) * b + (4 * D + 71) ∧ orbit t n = 1 := by
  obtain ⟨t, ht, hone⟩ := linear_credit_reaches hn hb hc
  refine ⟨t, ?_, hone⟩
  simp only [Nat.add_mul, Nat.mul_assoc]
  omega

theorem logarithmic_time_to_credit {n b C D T : Nat}
    (ht : T ≤ C * b + D) (hone : orbit T n = 1) :
    ∃ A, A ≤ C * b + (D + 1) ∧ ∀ k, 2 * wt k n ≤ k + A := by
  exact ⟨T + 1, by omega, arrival_credit_bound hone⟩

#print axioms growth_of_odd_bound
#print axioms growth_to_count
#print axioms avoiding_one_count
#print axioms avoiding64_count
#print axioms packing_base64
#print axioms endpoint_credit_reaches
#print axioms linear_credit_reaches
#print axioms nonconvergent_count_lower
#print axioms nonconvergent_credit_at_clock
#print axioms sparse_prefix_reaches
#print axioms logarithmic_credit_to_time
#print axioms logarithmic_time_to_credit

end CollatzPacking
