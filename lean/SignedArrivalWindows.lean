/-
  Finite arithmetic for oriented arrival windows. Universal convergence
  remains a hypothesis of the written power-growth consequence.
  Real profiles, geometric sums and infinite moments are not formalized here.
-/
import GradientClockObstruction

namespace SignedArrivalWindows
open CollatzAffine CoalescenceTail EscapeWeightRefinements IntegerReturnCesaro
  GradientClockObstruction AnnulusTimeBudgets

theorem first_arrival_odd {n T : Nat} (hn : 0 < n)
    (h : FirstArrival (3 * n + 2) T) : FirstArrival (2 * n + 1) (T + 1) := by
  constructor
  · simpa only [(odd_refinement T n).1] using h.1
  · intro t ht
    cases t with
    | zero => change 2 * n + 1 ≠ 1; omega
    | succ t =>
      rw [(odd_refinement t n).1]
      exact h.2 t (by omega)

theorem cycle_after_arrival {n T t : Nat} (h : orbit T n = 1) (ht : T ≤ t) :
    orbit t n = 1 ∨ orbit t n = 2 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ht
  clear ht
  induction j with
  | zero => simp [h]
  | succ j ih =>
    have he : T + (j + 1) = (T + j) + 1 := by omega
    rw [he, orbit_add]
    exact cycle_step _ ih

theorem prearrival_endpoint {n T t : Nat} (hn : 0 < n)
    (h : FirstArrival n T) (ht : t < T) : 2 ≤ orbit t n := by
  have hs := source_bound t n
  have hp : 0 < orbit t n := by
    by_cases hc : 0 < orbit t n
    · exact hc
    · have hz : orbit t n = 0 := by omega
      rw [hz, Nat.mul_zero] at hs
      omega
  have he := h.2 t ht
  omega

/-- When the second endpoint is on the known cycle and the first has not
    arrived, a downward weight gap forces the current count order to reverse. -/
theorem gap_forces_reversal {a b X Y : Nat}
    (hX : 2 ≤ X) (hY : Y ≤ 2) (hgap : 3 ^ b * X < 3 ^ a * Y) : b < a := by
  by_cases h : b < a
  · exact h
  · have hab : a ≤ b := by omega
    have hp : 3 ^ a ≤ 3 ^ b := Nat.pow_le_pow_right (by decide) hab
    have hyx : Y ≤ X := by omega
    have hm := Nat.mul_le_mul hp hyx
    omega

theorem late_parent_reversal {n T S t : Nat} (hn : 0 < n)
    (hT : FirstArrival n T) (hS : FirstArrival (3 * n + 2) S)
    (hSt : S ≤ t) (htT : t < T)
    (hgap : 3 ^ (wt t (3 * n + 2) + 1) * orbit t n <
      3 ^ wt t n * orbit t (3 * n + 2)) :
    wt t (3 * n + 2) + 1 < wt t n := by
  have hx := prearrival_endpoint hn hT htT
  have hy : orbit t (3 * n + 2) ≤ 2 := by
    rcases cycle_after_arrival hS.1 hSt with hy | hy <;> omega
  exact gap_forces_reversal hx hy hgap

theorem signed_window_length (early late R : Nat) :
    late - early ≤ R + (late - (early + R)) := by omega

theorem prearrival_partition (parent child : Nat) :
    min parent child + (parent - child) = parent := by omega

theorem finite_gap_floor {A B D : Nat}
    (hA : 3 * D ≤ 8 * A) (hB : 16 * B ≤ 3 * D) :
    3 * D ≤ 16 * (A - B) := by omega

theorem finite_negative_product {A B D : Nat}
    (hA : 3 * D ≤ 8 * A) (hB : 16 * B ≤ 3 * D) :
    9 * D ^ 2 ≤ 128 * A * (A - B) := by
  have hg := finite_gap_floor hA hB
  have hp := Nat.mul_le_mul hA hg
  calc
    9 * D ^ 2 = (3 * D) * (3 * D) := by grind
    _ ≤ (8 * A) * (16 * (A - B)) := hp
    _ = 128 * A * (A - B) := by grind

theorem positive_clock_budget (K : Nat) (F P N : Nat → Nat)
    (h0 : F 0 = 0)
    (h : ∀ j < K, 2 * F (j + 1) + N j = 2 * F j + P j) :
    2 * F K ≤ total K P := by
  have ht := clock_telescope K F P N h
  rw [h0] at ht
  omega

/-- The first-arrival phase has squared profile sum 25/7 times its value
    squared, after using the already proved quadratic geometric identity. -/
theorem first_arrival_tail_constant :
    16 + 9 = 25 ∧ 16 - 9 = 7 ∧ 16 * 3 ^ 6 ≤ 3 * 4 ^ 6 := by decide

#print axioms first_arrival_odd
#print axioms cycle_after_arrival
#print axioms prearrival_endpoint
#print axioms gap_forces_reversal
#print axioms late_parent_reversal
#print axioms signed_window_length
#print axioms prearrival_partition
#print axioms finite_gap_floor
#print axioms finite_negative_product
#print axioms positive_clock_budget
#print axioms first_arrival_tail_constant

end SignedArrivalWindows
