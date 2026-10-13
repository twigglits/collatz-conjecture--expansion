/-
  Balanced coalescence gives time-uniform caps for individual refinement
  levels. Equal odd counts alone do not suffice, even for even inputs.
  No uniform bound on the sum over all levels is asserted.
-/
import EscapeWeightRefinements

namespace CoalescenceEnergyCaps
open CollatzAffine CoalescenceTail EscapeWeightRefinements

theorem balanced_add {h n : Nat} (hh : balanced h n = true) (s : Nat) :
    balanced (h + s) n = true := by
  induction s with
  | zero => simpa using hh
  | succ s ih => exact balanced_persists ih

theorem balanced_later {h t n : Nat} (ht : h ≤ t) (hh : balanced h n = true) :
    balanced t n = true := by
  have he : h + (t - h) = t := by omega
  simpa [he] using balanced_add hh (t - h)

theorem refinement_data_equal {h t n : Nat} (ht : h ≤ t + 1)
    (hh : balanced h (2 * n) = true) :
    orbit (t + 1) (2 * n + 1) = orbit t n ∧
    wt (t + 1) (2 * n + 1) = wt t n := by
  have hb := of_decide_eq_true (balanced_later ht hh)
  have he := even_refinement t n
  exact ⟨hb.1.symm.trans he.1, hb.2.symm.trans he.2⟩

theorem refinement_cross_equal {h t n : Nat} (ht : h ≤ t + 1)
    (hh : balanced h (2 * n) = true) :
    3 ^ wt (t + 1) (2 * n + 1) * orbit t n =
      3 ^ wt t n * orbit (t + 1) (2 * n + 1) := by
  rcases refinement_data_equal ht hh with ⟨hx, hw⟩
  rw [hx, hw]

theorem even_period (h q r : Nat) :
    unmerged (h + 1) (2 * (2 ^ h * q + r)) =
      unmerged (h + 1) (2 * r) := by
  have he : 2 * (2 ^ h * q + r) = 2 ^ (h + 1) * q + 2 * r := by
    rw [Nat.mul_add, Nat.pow_succ]
    ac_rfl
  simp only [he, unmerged, balanced_lift]

theorem even_block_count (h m q : Nat) :
    total (2 ^ h * m) (fun r => unmerged (h + 1) (2 * (2 ^ h * q + r))) =
      m * total (2 ^ h) (fun r => unmerged (h + 1) (2 * r)) := by
  induction m with
  | zero => simp [total]
  | succ m ih =>
    rw [Nat.mul_succ, total_add, ih]
    have he := total_ext (2 ^ h)
      (fun r => unmerged (h + 1) (2 * (2 ^ h * q + (2 ^ h * m + r))))
      (fun r => unmerged (h + 1) (2 * r)) (by
        intro r _
        have ha : 2 ^ h * q + (2 ^ h * m + r) = 2 ^ h * (q + m) + r := by
          rw [Nat.mul_add]
          omega
        rw [ha, even_period])
    rw [he, Nat.succ_mul]

theorem shell_count (h j : Nat) :
    total (2 ^ (h + j))
      (fun r => unmerged (h + 1) (2 * (2 ^ (h + j) + r))) =
      2 ^ j * total (2 ^ h) (fun r => unmerged (h + 1) (2 * r)) := by
  rw [Nat.pow_add]
  exact even_block_count h (2 ^ j) (2 ^ j)

def cutoff (s : Nat) : Nat := (121 * s + 49) / 50

theorem cutoff_close (s : Nat) :
    121 * s ≤ 50 * cutoff s ∧ 50 * cutoff s < 121 * s + 50 := by
  unfold cutoff
  omega

theorem cutoff_decomposition (s : Nat) :
    cutoff s = 121 * (s / 50) + cutoff (s % 50) := by
  unfold cutoff
  omega

set_option exponentiation.threshold 512 in
theorem cutoff_block : 2 ^ 271 ≤ 3 ^ 171 := by decide

set_option exponentiation.threshold 512 in
theorem cutoff_remainders : ∀ r : Fin 50,
    2 ^ (3 * r.val + cutoff r.val) ≤ 3 ^ (r.val + cutoff r.val) := by decide

theorem tail_cutoff (s : Nat) : 2 ^ (3 * s + cutoff s) ≤ 3 ^ (s + cutoff s) := by
  have hr : s % 50 < 50 := Nat.mod_lt s (by decide)
  have hh := cutoff_remainders ⟨s % 50, hr⟩
  have he := cutoff_decomposition s
  have h2 : 3 * s + cutoff s = 271 * (s / 50) + (3 * (s % 50) + cutoff (s % 50)) := by
    omega
  have h3 : s + cutoff s = 171 * (s / 50) + ((s % 50) + cutoff (s % 50)) := by
    omega
  rw [h2, h3]
  simpa only [Nat.pow_add, Nat.pow_mul] using
    Nat.mul_le_mul (Nat.pow_le_pow_left cutoff_block (s / 50)) hh

theorem six_first_return :
    alive 10 6 = true ∧ gap 11 6 = 0 ∧
    orbit 11 6 = 2 ∧ orbit 11 7 = 1 ∧ wt 11 6 = 5 ∧ wt 11 7 = 5 := by
  decide

theorem lifted_first_return (q : Nat) :
    alive 10 (2048 * q + 6) = true ∧
    gap 11 (2048 * q + 6) = 0 ∧
    orbit 11 (2048 * q + 6) = 243 * q + 2 ∧
    orbit 11 (2048 * q + 7) = 243 * q + 1 ∧
    wt 11 (2048 * q + 6) = 5 ∧ wt 11 (2048 * q + 7) = 5 := by
  have ha := alive_lift 10 (2 * q) 6
  have h6 := affine 11 q 6
  have h7 := affine 11 q 7
  have w6 := weight_lift 11 q 6
  have w7 := weight_lift 11 q 7
  have hb := six_first_return
  have hp : 2 ^ 10 * (2 * q) + 6 = 2048 * q + 6 := by omega
  simp only [hp, hb.1] at ha
  simp only [show 2 ^ 11 = 2048 by decide, hb.2.2.1, hb.2.2.2.1,
    hb.2.2.2.2.1, hb.2.2.2.2.2, show 3 ^ 5 = 243 by decide] at h6 h7 w6 w7
  refine ⟨ha, ?_, h6, h7, w6, w7⟩
  simp only [gap, show 2048 * q + 6 + 1 = 2048 * q + 7 by omega, w6, w7]
  decide

theorem stopped_but_unmerged (q : Nat) :
    stopped 11 (2048 * q + 6) = 0 ∧ unmerged 11 (2048 * q + 6) = 1 := by
  have hh := lifted_first_return q
  have hg := hh.2.1
  constructor
  · simp [stopped, hg]
  · have hn : orbit 11 (2048 * q + 6) ≠ orbit 11 (2048 * q + 6 + 1) := by
      rw [show 2048 * q + 6 + 1 = 2048 * q + 7 by omega,
        hh.2.2.1, hh.2.2.2.1]
      omega
    simp [unmerged, balanced, hn]

theorem cycle_pair : ∀ t,
    (orbit t 2 = 2 ∧ orbit t 1 = 1) ∨ (orbit t 2 = 1 ∧ orbit t 1 = 2)
  | 0 => by simp [orbit]
  | t + 1 => by
    rcases cycle_pair t with h | h
    · right
      rw [orbit_snoc, orbit_snoc, h.1, h.2]
      decide
    · left
      rw [orbit_snoc, orbit_snoc, h.1, h.2]
      decide

theorem six_never_balanced (t : Nat) : balanced t 6 = false := by
  by_cases ht : t < 11
  · have hf : ∀ i : Fin 11, balanced i.val 6 = false := by decide
    exact hf ⟨t, ht⟩
  · have he : t = 11 + (t - 11) := by omega
    have hb := six_first_return
    have hp := cycle_pair (t - 11)
    have hn : orbit t 6 ≠ orbit t 7 := by
      rw [he, orbit_add, orbit_add, hb.2.2.1, hb.2.2.2.1]
      rcases hp with h | h <;> omega
    simp [balanced, hn]

#print axioms balanced_add
#print axioms balanced_later
#print axioms refinement_data_equal
#print axioms refinement_cross_equal
#print axioms even_period
#print axioms even_block_count
#print axioms shell_count
#print axioms cutoff_close
#print axioms cutoff_decomposition
#print axioms cutoff_block
#print axioms cutoff_remainders
#print axioms tail_cutoff
#print axioms six_first_return
#print axioms lifted_first_return
#print axioms stopped_but_unmerged
#print axioms cycle_pair
#print axioms six_never_balanced

end CoalescenceEnergyCaps
