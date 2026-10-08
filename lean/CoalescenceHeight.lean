/- Quantitative and concrete limits on coalescence search.
   These results do not decide the Collatz conjecture. -/
import CoalescenceDescent

namespace CoalescenceHeight
open CollatzAffine CoalescenceDescent

/-- Reducing the constructive witness modulo 6^(k+1) retains both conditions. -/
theorem bounded_size_witness (k : Nat) : ∃ n : Nat,
    3 ^ (k + 1) ≤ n ∧ n < 6 ^ (k + 1) ∧
    2 ^ (k + 1) ∣ n + 1 ∧ 3 ^ (k + 1) ∣ n := by
  obtain ⟨N, _, h2, h3⟩ := growing_divisible_starts k
  let P := 2 ^ (k + 1)
  let Q := 3 ^ (k + 1)
  let M := P * Q
  let n := N % M
  have hP : 2 ≤ P := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ k + 1 by omega)
    simpa [P] using this
  have hQ : 3 ≤ Q := by
    have := Nat.pow_le_pow_right (n := 3) (by decide) (show 1 ≤ k + 1 by omega)
    simpa [Q] using this
  have hpmod : n % P = N % P := Nat.mod_mod_of_dvd N (Nat.dvd_mul_right P Q)
  have hqmod : n % Q = N % Q := Nat.mod_mod_of_dvd N (Nat.dvd_mul_left Q P)
  have hp : P ∣ n + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, hpmod, ← Nat.add_mod]
    exact Nat.mod_eq_zero_of_dvd h2
  have hq : Q ∣ n := Nat.dvd_of_mod_eq_zero (by
    rw [hqmod]; exact Nat.mod_eq_zero_of_dvd h3)
  have hn : 0 < n := by
    by_cases hz : n = 0
    · rw [hz] at hp
      have := Nat.le_of_dvd (by decide : 0 < 0 + 1) hp
      omega
    · omega
  have hl : Q ≤ n := Nat.le_of_dvd hn hq
  have hM : M = 6 ^ (k + 1) := by
    simp only [M, P, Q, ← Nat.mul_pow]
  have hu : n < 6 ^ (k + 1) := by
    rw [← hM]
    exact Nat.mod_lt N (Nat.mul_pos (by omega) (by omega))
  exact ⟨n, hl, hu, hp, hq⟩

/-- Thus infinitely many inputs need more than log_6(n) steps on at least
    one side of every meeting with a smaller start. No upper bound is claimed. -/
theorem logarithmic_horizon_obstruction (k : Nat) : ∃ n : Nat,
    3 ^ (k + 1) ≤ n ∧ n < 6 ^ (k + 1) ∧
    ∀ m a b : Nat, m < n → a ≤ k + 1 → b ≤ k + 1 →
      orbit a n ≠ orbit b m := by
  obtain ⟨n, hl, hu, h2, h3⟩ := bounded_size_witness k
  refine ⟨n, hl, hu, ?_⟩
  intro m a b hm ha hb he
  have := crt_class_meeting_bound (k + 1) a b n m ha hb h2 h3 he.symm
  omega

#print axioms bounded_size_witness
#print axioms logarithmic_horizon_obstruction

/-- All positive starts below 27 stay in this small invariant set. -/
def region27 : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17,
   18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 32, 35, 38, 40, 44, 53, 80]

theorem seeds27 : ∀ m : Fin 27, 0 < m.val → m.val ∈ region27 := by decide

theorem region27_closed {n : Nat} (hn : n ∈ region27) : U n ∈ region27 := by
  have hc : region27.all (fun x => decide (U x ∈ region27)) = true := by decide
  exact of_decide_eq_true (List.all_eq_true.mp hc n hn)

theorem region27_orbit : ∀ b n, n ∈ region27 → orbit b n ∈ region27
  | 0, _, hn => hn
  | b + 1, n, hn => region27_orbit b (U n) (region27_closed hn)

theorem prefix27_avoids : ∀ a : Fin 59, orbit a.val 27 ∉ region27 := by decide

/-- Even unlimited time on the smaller orbit cannot give an earlier meeting. -/
theorem no_early_meeting27 (m a b : Nat) (hm : 0 < m) (hlt : m < 27)
    (ha : a < 59) : orbit a 27 ≠ orbit b m := by
  intro he
  have hr := region27_orbit b m (seeds27 ⟨m, hlt⟩ hm)
  rw [← he] at hr
  exact prefix27_avoids ⟨a, ha⟩ hr

set_option maxRecDepth 10000 in
theorem meeting27_at59 : orbit 59 27 = orbit 0 23 := by decide

theorem first_slope_drop27 : FirstSlopeDrop 59 27 := by
  have h : ∀ a : Fin 59, 2 ^ a.val ≤ 3 ^ wt a.val 27 := by decide
  exact ⟨by decide, fun a ha => h ⟨a, ha⟩⟩

#print axioms region27_orbit
#print axioms no_early_meeting27
#print axioms meeting27_at59
#print axioms first_slope_drop27
end CoalescenceHeight
