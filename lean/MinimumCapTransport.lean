/- Exact finite-prefix minimum transport. The cap loss is nonincreasing in
   time; actual finite Collatz prefixes can have positive sampling and fair
   recurrence errors even when every future cap loss is zero. No assertion
   about uncomputed infinite minima or the full conjecture is made. -/
import MinimumTailRigidity

namespace MinimumCapTransport
open OrdinaryCollatz MinimumTailRigidity

def tailValue (h y : Nat) : Nat := if h < y then y else 0
def cap (h s y : Nat) : Nat := tailValue h y - tailValue h (min s y)
def capSum (h t x : Nat) : Nat :=
  sumPos (fun n => cap h (2 * n + 1) (prefixMinimum t (3 * n + 2))) x
def progressionSum (h t x : Nat) : Nat :=
  sumPos (fun n => tailTerm (prefixMinimum t) h (3 * n + 2)) x

theorem prefix_le_source (t n : Nat) : prefixMinimum t n ≤ n := by
  cases t with
  | zero => exact Nat.le_refl _
  | succ t => simp only [prefixMinimum]; omega

theorem prefix_succ_le (t n : Nat) : prefixMinimum (t + 1) n ≤ prefixMinimum t n := by
  induction t generalizing n with
  | zero => exact prefix_le_source 1 n
  | succ t ih =>
    have ht := ih (C n)
    simp only [prefixMinimum] at *
    omega

theorem prefix_clock_mono {t u : Nat} (htu : t ≤ u) (n : Nat) :
    prefixMinimum u n ≤ prefixMinimum t n := by
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact Nat.le_refl _
  | succ u ih =>
    by_cases he : t = u + 1
    · subst t; exact Nat.le_refl _
    · have hl := ih (by omega)
      have hs := prefix_succ_le u n
      omega

theorem even_minimum_transport (t n : Nat) :
    prefixMinimum (t + 1) (2 * n) = prefixMinimum t n := by
  have hc : C (2 * n) = n := by unfold C; split <;> omega
  have hl := prefix_le_source t n
  simp only [prefixMinimum, hc]
  omega

theorem odd_minimum_transport (t n : Nat) :
    prefixMinimum (t + 2) (2 * n + 1) =
      min (2 * n + 1) (prefixMinimum t (3 * n + 2)) := by
  have hc : C (2 * n + 1) = 2 * (3 * n + 2) := by unfold C; split <;> omega
  change min (2 * n + 1) (prefixMinimum (t + 1) (C (2 * n + 1))) = _
  rw [hc, even_minimum_transport]

theorem tail_value_mono (h : Nat) {y z : Nat} (hyz : y ≤ z) :
    tailValue h y ≤ tailValue h z := by
  simp only [tailValue]
  split <;> split <;> omega

theorem cap_add_identity (h s y : Nat) :
    tailValue h (min s y) + cap h s y = tailValue h y := by
  have hl := tail_value_mono h (show min s y ≤ y by omega)
  unfold cap
  omega

theorem cap_below_floor (h s y : Nat) (hs : s ≤ h) :
    cap h s y = tailValue h y := by
  have hl : ¬ h < min s y := by omega
  simp only [cap, tailValue, if_neg hl, Nat.sub_zero]

theorem cap_above_floor (h s y : Nat) (hs : h < s) : cap h s y = y - s := by
  simp only [cap, tailValue]
  split <;> split <;> omega

theorem cap_mono (h s : Nat) {y z : Nat} (hyz : y ≤ z) :
    cap h s y ≤ cap h s z := by
  by_cases hs : s ≤ h
  · rw [cap_below_floor h s y hs, cap_below_floor h s z hs]
    exact tail_value_mono h hyz
  · rw [cap_above_floor h s y (by omega), cap_above_floor h s z (by omega)]
    omega

theorem cap_zero_of_le (h s y : Nat) (hy : y ≤ s) : cap h s y = 0 := by
  have hm : min s y = y := by omega
  simp only [cap, hm, Nat.sub_self]

theorem cap_sum_clock_mono (h x : Nat) {t u : Nat} (htu : t ≤ u) :
    capSum h u x ≤ capSum h t x := by
  exact sum_mono _ _ x (fun n _ _ => cap_mono h (2 * n + 1)
    (prefix_clock_mono htu (3 * n + 2)))

theorem cap_sum_stays_zero (h x : Nat) {t u : Nat} (htu : t ≤ u)
    (hz : capSum h t x = 0) : capSum h u x = 0 := by
  have hl := cap_sum_clock_mono h x htu
  omega

theorem even_tail_transport (h t n : Nat) :
    tailTerm (prefixMinimum (t + 1)) h (2 * n) = tailTerm (prefixMinimum t) h n := by
  simp only [tailTerm, even_minimum_transport]

theorem odd_tail_transport (h t n : Nat) :
    tailTerm (prefixMinimum (t + 2)) h (2 * n + 1) +
      cap h (2 * n + 1) (prefixMinimum t (3 * n + 2)) =
      tailTerm (prefixMinimum t) h (3 * n + 2) := by
  change tailValue h (prefixMinimum (t + 2) (2 * n + 1)) + _ = _
  rw [odd_minimum_transport]
  exact cap_add_identity h (2 * n + 1) (prefixMinimum t (3 * n + 2))

theorem source_one_tail_zero (h t : Nat) (hh : 1 ≤ h) :
    tailTerm (prefixMinimum t) h 1 = 0 := by
  have hl := prefix_le_source t 1
  simp only [tailTerm, if_neg (by omega : ¬ h < prefixMinimum t 1)]

theorem odd_population_transport (h t x : Nat) (hh : 1 ≤ h) :
    tailSum (prefixMinimum (t + 2)) h (2 * x + 1) + capSum h t x =
      tailSum (prefixMinimum (t + 1)) h x + progressionSum h t x := by
  induction x with
  | zero => simp [tailSum, sumPos, capSum, progressionSum, source_one_tail_zero h _ hh]
  | succ x ih =>
    have he := even_tail_transport h (t + 1) (x + 1)
    have ho := odd_tail_transport h t (x + 1)
    have hn : 2 * (x + 1) + 1 = (2 * x + 1) + 1 + 1 := by omega
    have hm : 2 * (x + 1) = (2 * x + 1) + 1 := by omega
    rw [hm] at he
    rw [hn] at ho
    rw [hn]
    simp only [tailSum, capSum, progressionSum, sumPos, Nat.mul_add,
      Nat.mul_one, Nat.add_assoc, Nat.reduceAdd] at *
    omega

theorem even_population_transport (h t x : Nat) (hh : 1 ≤ h) :
    tailSum (prefixMinimum (t + 2)) h (2 * (x + 1)) + capSum h t x =
      tailSum (prefixMinimum (t + 1)) h (x + 1) + progressionSum h t x := by
  have ho := odd_population_transport h t x hh
  have he := even_tail_transport h (t + 1) (x + 1)
  have hn : 2 * (x + 1) = (2 * x + 1) + 1 := by omega
  rw [hn] at he
  rw [hn]
  simp only [tailSum, sumPos, Nat.add_assoc, Nat.reduceAdd] at *
  omega

theorem small_closed_sums :
    tailSum (prefixMinimum 6) 1 3 = 2 ∧
    tailSum (prefixMinimum 5) 1 1 = 0 ∧
    tailSum (prefixMinimum 4) 1 5 = 5 ∧
    progressionSum 1 4 1 = 2 ∧ capSum 1 4 1 = 0 := by decide

theorem small_sampling_error_positive :
    5 * progressionSum 1 4 1 > tailSum (prefixMinimum 4) 1 5 := by decide

theorem small_future_caps_zero (u : Nat) (hu : 4 ≤ u) : capSum 1 u 1 = 0 :=
  cap_sum_stays_zero 1 1 hu (by decide)

theorem small_future_cap_obstruction (w : Nat → Nat) (k : Nat) :
    10 * tailSum (prefixMinimum 6) 1 3 >
      15 * tailSum (prefixMinimum 5) 1 1 + 3 * tailSum (prefixMinimum 4) 1 5 +
      sumPos (fun j => w j * capSum 1 (3 + j) 1) k := by
  have hz : sumPos (fun j => w j * capSum 1 (3 + j) 1) k = 0 := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [sumPos, ih, small_future_caps_zero (3 + (k + 1)) (by omega),
        Nat.mul_zero, Nat.add_zero]
  rw [hz]
  decide

#print axioms prefix_le_source
#print axioms prefix_succ_le
#print axioms prefix_clock_mono
#print axioms even_minimum_transport
#print axioms odd_minimum_transport
#print axioms tail_value_mono
#print axioms cap_add_identity
#print axioms cap_below_floor
#print axioms cap_above_floor
#print axioms cap_mono
#print axioms cap_zero_of_le
#print axioms cap_sum_clock_mono
#print axioms cap_sum_stays_zero
#print axioms even_tail_transport
#print axioms odd_tail_transport
#print axioms source_one_tail_zero
#print axioms odd_population_transport
#print axioms even_population_transport
#print axioms small_closed_sums
#print axioms small_sampling_error_positive
#print axioms small_future_caps_zero
#print axioms small_future_cap_obstruction

end MinimumCapTransport
