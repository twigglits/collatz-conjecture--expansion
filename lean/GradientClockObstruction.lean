/-
  Finite arrival-clock inputs for a CONDITIONAL gradient-power obstruction.
  Infinite moment growth assumes universal convergence in the written note.
  No universal convergence or counterexample is asserted by this module.
-/
import IntegerReturnCesaro
import AnnulusTimeBudgets

namespace GradientClockObstruction
open CollatzAffine CoalescenceTail EscapeWeightRefinements IntegerReturnCesaro

def FirstArrival (n T : Nat) : Prop :=
  orbit T n = 1 ∧ ∀ t < T, orbit t n ≠ 1

theorem first_arrival_unique {n T S : Nat}
    (hT : FirstArrival n T) (hS : FirstArrival n S) : T = S := by
  by_cases h : T < S
  · exact False.elim (hS.2 T h hT.1)
  · by_cases h' : S < T
    · exact False.elim (hT.2 S h' hS.1)
    · omega

theorem first_arrival_even {n T : Nat} (_hn : 0 < n)
    (h : FirstArrival n T) : FirstArrival (2 * n) (T + 1) := by
  constructor
  · simpa only [(even_refinement T n).1] using h.1
  · intro t ht
    cases t with
    | zero => change 2 * n ≠ 1; omega
    | succ t =>
      rw [(even_refinement t n).1]
      exact h.2 t (by omega)

theorem arrival_clock_floor {k n T : Nat}
    (hn : 2 ^ k ≤ n) (hT : orbit T n = 1) : k ≤ T := by
  have hs := source_bound T n
  rw [hT, Nat.mul_one] at hs
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_trans hn hs)

/-- There remain at least as many clocks as the odd inputs already seen
    on a full binary source band. -/
theorem arrival_remaining_floor {k n T : Nat}
    (hn : 2 ^ k ≤ n) (hT : orbit T n = 1) : k + wt k n ≤ T := by
  have hk := arrival_clock_floor hn hT
  have hl := coefficient_lower_bound k n
  have hm := Nat.mul_le_mul_left (3 ^ wt k n) hn
  have hi : 2 ^ k * 3 ^ wt k n ≤ 2 ^ k * orbit k n := by
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Nat.le_trans hm hl
  have hc : 3 ^ wt k n ≤ orbit k n :=
    Nat.le_of_mul_le_mul_left hi (Nat.pow_pos (by decide))
  have he : orbit (T - k) (orbit k n) = 1 := by
    rw [← orbit_add, Nat.add_sub_of_le hk]
    exact hT
  have hb := source_bound (T - k) (orbit k n)
  rw [he, Nat.mul_one] at hb
  have hp : 2 ^ wt k n ≤ 2 ^ (T - k) :=
    Nat.le_trans (Nat.pow_le_pow_left (by decide) _) (Nat.le_trans hc hb)
  have hw := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  omega

theorem weight_children_sum (k n : Nat) :
    wt (k + 1) n + wt (k + 1) (2 ^ k + n) = 2 * wt k n + 1 := by
  rw [weight_snoc, weight_snoc, endpoint_parity_flip]
  have hl := weight_lift k 1 n
  simp only [Nat.mul_one] at hl
  rw [hl]
  have hp : orbit k n % 2 ≤ 1 := by omega
  omega

theorem weight_mass (k : Nat) :
    2 * total (2 ^ k) (wt k) = k * 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => weight_children_sum k n), total_sum, total_mul]
    have hconst : total (2 ^ k) (fun _ => 1) = 2 ^ k := by
      generalize 2 ^ k = m
      induction m with
      | zero => rfl
      | succ m hm => simp only [total, hm]
    rw [hconst]
    have hh := congrArg (fun x => 2 * x) ih
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at *
    omega

theorem weight_band_mass (k : Nat) :
    2 * total (2 ^ k) (fun r => wt k (2 ^ k + r)) = k * 2 ^ k := by
  have he := total_ext (2 ^ k) (fun r => wt k (2 ^ k + r)) (wt k) (by
    intro r _
    simpa only [Nat.mul_one] using weight_lift k 1 r)
  rw [he, weight_mass]

/-- If neither first arrival precedes the matching prefix, equal prefix
    endpoints force equal first-arrival clocks. Equal counts are stronger
    than needed for this particular clock statement. -/
theorem first_arrival_eq_of_prefix {n m T S k : Nat}
    (hn : FirstArrival n T) (hm : FirstArrival m S)
    (hkT : k ≤ T) (hkS : k ≤ S) (he : orbit k n = orbit k m) : T = S := by
  have hT : orbit T m = 1 := by
    rw [← Nat.add_sub_of_le hkT, orbit_add, ← he, ← orbit_add,
      Nat.add_sub_of_le hkT]
    exact hn.1
  have hS : orbit S n = 1 := by
    rw [← Nat.add_sub_of_le hkS, orbit_add, he, ← orbit_add,
      Nat.add_sub_of_le hkS]
    exact hm.1
  by_cases h : T < S
  · exact False.elim (hm.2 T h hT)
  · by_cases h' : S < T
    · exact False.elim (hn.2 S h' hS)
    · omega

theorem fused_child_arrival {k n T S : Nat} (hn : 2 ^ k ≤ n)
    (hT : FirstArrival n T) (hS : FirstArrival (2 * n + 1) S)
    (hf : balanced (k + 1) (2 * n) = true) : S = T + 1 := by
  have hp : 0 < n := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hn
  have he := first_arrival_even hp hT
  have hne : 2 ^ (k + 1) ≤ 2 * n := by
    have h := Nat.mul_le_mul_left 2 hn
    simpa only [Nat.pow_succ, Nat.mul_comm] using h
  have hno : 2 ^ (k + 1) ≤ 2 * n + 1 := by omega
  have ht := arrival_clock_floor hne he.1
  have hs := arrival_clock_floor hno hS.1
  have heq : orbit (k + 1) (2 * n) = orbit (k + 1) (2 * n + 1) :=
    (of_decide_eq_true hf).1
  exact (first_arrival_eq_of_prefix he hS ht hs heq).symm

/-- Clear a common dyadic denominator in the mean arrival-clock identity. -/
theorem clock_telescope (K : Nat) (F P N : Nat → Nat)
    (h : ∀ j < K, 2 * F (j + 1) + N j = 2 * F j + P j) :
    2 * F K + total K N = 2 * F 0 + total K P := by
  induction K with
  | zero => simp [total]
  | succ K ih =>
    have hp := ih (fun j hj => h j (by omega))
    have hs := h K (by omega)
    simp only [total]
    omega

theorem profile_window (early late R : Nat) (h : early ≤ late) :
    late - early ≤ R + (late - (early + R)) := by omega

theorem finite_profile_constants : 16 * 3 ^ 6 ≤ 3 * 4 ^ 6 := by decide

#print axioms first_arrival_unique
#print axioms first_arrival_even
#print axioms arrival_clock_floor
#print axioms arrival_remaining_floor
#print axioms weight_children_sum
#print axioms weight_mass
#print axioms weight_band_mass
#print axioms first_arrival_eq_of_prefix
#print axioms fused_child_arrival
#print axioms clock_telescope
#print axioms profile_window
#print axioms finite_profile_constants

end GradientClockObstruction
