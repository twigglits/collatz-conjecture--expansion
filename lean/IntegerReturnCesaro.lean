/-
  Exact positive-integer inputs for the written return-image Cesaro argument.
  No density, clock limit, or Collatz convergence claim is formalized here.
  Standalone Lean 4; the external analytic sources are not imported.
-/
import CollatzPacking
import CoalescenceTail

namespace IntegerReturnCesaro
open CollatzAffine CoalescenceTail

theorem packing_orbit (t n : Nat) : CollatzPacking.orbit t n = orbit t n := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih => exact ih (U n)

theorem packing_weight (t n : Nat) : CollatzPacking.wt t n = wt t n := by
  induction t generalizing n with
  | zero => rfl
  | succ t ih =>
    change n % 2 + CollatzPacking.wt t (U n) = n % 2 + wt t (U n)
    rw [ih]

theorem residue_endpoint_bound (t r : Nat) (hr : r < 2 ^ t) :
    orbit t r < 3 ^ wt t r := by
  simpa only [packing_orbit, packing_weight] using
    CollatzPacking.residue_image_bound t r hr

theorem orbit_zero (t : Nat) : orbit t 0 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [orbit, U, Nat.zero_mod, Nat.zero_ne_one,
      if_false, Nat.zero_div] using ih

/-- A matching ternary column has an actual positive integer preimage.
The quotient is nonnegative because the residue endpoint is below 3^a. -/
theorem positive_column_iff (t r N : Nat) (hr : r < 2 ^ t) (hN : 0 < N) :
    N % (3 ^ wt t r) = orbit t r ↔
      ∃ q, 0 < 2 ^ t * q + r ∧ orbit t (2 ^ t * q + r) = N := by
  have hb := residue_endpoint_bound t r hr
  constructor
  · intro h
    have he : orbit t (2 ^ t * (N / (3 ^ wt t r)) + r) = N := by
      rw [affine, ← h, Nat.add_comm]
      exact Nat.mod_add_div N (3 ^ wt t r)
    refine ⟨N / (3 ^ wt t r), ?_, he⟩
    by_cases hz : 0 < 2 ^ t * (N / (3 ^ wt t r)) + r
    · exact hz
    · have hm : 2 ^ t * (N / (3 ^ wt t r)) + r = 0 := by omega
      rw [hm, orbit_zero] at he
      omega
  · rintro ⟨q, _, h⟩
    rw [← h, affine]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hb]

theorem column_quotient_unique (t r q₁ q₂ : Nat)
    (h : orbit t (2 ^ t * q₁ + r) = orbit t (2 ^ t * q₂ + r)) : q₁ = q₂ := by
  rw [affine, affine] at h
  have hm : 3 ^ wt t r * q₁ = 3 ^ wt t r * q₂ := Nat.add_right_cancel h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) hm

theorem source_residue (t r q : Nat) (hr : r < 2 ^ t) :
    (2 ^ t * q + r) % (2 ^ t) = r := by
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt hr]

theorem step_source_bound (n : Nat) : n ≤ 2 * U n := by
  unfold U
  split <;> omega

/-- Every positive target has a finite predecessor search interval. -/
theorem source_bound (t n : Nat) : n ≤ 2 ^ t * orbit t n := by
  induction t generalizing n with
  | zero => simp [orbit]
  | succ t ih =>
    have h := Nat.mul_le_mul_left 2 (ih (U n))
    have hs := step_source_bound n
    simp only [orbit, Nat.pow_succ]
    calc
      n ≤ 2 * U n := hs
      _ ≤ 2 * (2 ^ t * orbit t (U n)) := h
      _ = 2 ^ t * 2 * orbit t (U n) := by ac_rfl

theorem bounded_hit_source {t H n N : Nat} (ht : t ≤ H)
    (hhit : orbit t n = N) : n ≤ 2 ^ H * N := by
  have h := source_bound t n
  rw [hhit] at h
  exact Nat.le_trans h (Nat.mul_le_mul_right N (Nat.pow_le_pow_right (by decide) ht))

theorem balanced_persists_le {L t n : Nat} (hLt : L ≤ t)
    (h : balanced L n = true) : balanced t n = true := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hLt
  clear hLt
  induction d with
  | zero => simpa using h
  | succ d ih => exact balanced_persists ih

/-- A selected nonfused return at a later clock survives every earlier clock. -/
theorem nonfused_backwards {L t n : Nat} (hLt : L ≤ t)
    (h : balanced t n = false) : balanced L n = false := by
  cases he : balanced L n with
  | false => rfl
  | true => have hp := balanced_persists_le hLt he; simp [h] at hp

theorem nonfused_mask_lift (L q r : Nat) :
    unmerged L (2 ^ L * q + r) = unmerged L r := by
  simp only [unmerged, balanced_lift]

#print axioms residue_endpoint_bound
#print axioms positive_column_iff
#print axioms column_quotient_unique
#print axioms source_residue
#print axioms source_bound
#print axioms bounded_hit_source
#print axioms balanced_persists_le
#print axioms nonfused_backwards
#print axioms nonfused_mask_lift

end IntegerReturnCesaro
