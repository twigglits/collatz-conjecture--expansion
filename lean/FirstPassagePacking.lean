/-
  Exact finite arithmetic for the first-passage orbit-packing argument.
  Import CollatzPacking via a temporary LEAN_PATH. No native evaluation.
  Ballot estimates and the analytic induction remain written mathematics.
-/
import CollatzPacking

namespace CollatzPacking

/-- Lower counterpart to block_image_bound, using the actual prefix weight. -/
theorem block_image_lower : ∀ k p n, p * 2 ^ k ≤ n →
    p * 3 ^ wt k n ≤ orbit k n
  | 0, p, n, hn => by simpa [orbit, wt] using hn
  | k + 1, p, n, hn => by
    have hm : p * 2 ^ (k + 1) = 2 * (p * 2 ^ k) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [hm] at hn
    by_cases hp : n % 2 = 1
    · have hu : (3 * p) * 2 ^ k ≤ U n := by
        simp only [U, if_pos hp, Nat.mul_assoc]
        omega
      have hi := block_image_lower k (3 * p) (U n) hu
      simpa [orbit, wt, hp, Nat.pow_add, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hi
    · have he : n % 2 = 0 := by omega
      have hu : p * 2 ^ k ≤ U n := by
        simp only [U, if_neg hp]
        omega
      simpa [orbit, wt, he] using block_image_lower k p (U n) hu

/-- A shorter observation horizon still maps a fixed-weight group into one
    exact aligned interval; there is no extra residue-dependent error. -/
theorem shorter_horizon_image (ell t q j n : Nat) (ht : t ≤ ell)
    (hlo : q * 2 ^ ell ≤ n) (hhi : n < (q + 1) * 2 ^ ell)
    (hw : wt t n = j) :
    q * (2 ^ (ell - t) * 3 ^ j) ≤ orbit t n ∧
    orbit t n < (q + 1) * (2 ^ (ell - t) * 3 ^ j) := by
  have hp : 2 ^ ell = 2 ^ (ell - t) * 2 ^ t := by
    rw [← Nat.pow_add, Nat.sub_add_cancel ht]
  rw [hp, ← Nat.mul_assoc] at hlo hhi
  have hl := block_image_lower t (q * 2 ^ (ell - t)) n hlo
  have hh := block_image_bound t ((q + 1) * 2 ^ (ell - t)) n hhi
  rw [hw] at hl hh
  simpa only [Nat.mul_assoc] using And.intro hl hh

/-- The coefficient at its first crossing below 2^-b is in the interval
    [2^(-b-1), 2^-b). The two inequalities here encode that interval. -/
def CrossingWeight (b t j : Nat) : Prop :=
  2 ^ t ≤ 2 * (2 ^ b * 3 ^ j) ∧ 2 ^ b * 3 ^ j < 2 ^ t

theorem crossing_weight_unique {b t j k : Nat}
    (hj : CrossingWeight b t j) (hk : CrossingWeight b t k) : j = k := by
  have impossible : ∀ u v : Nat, CrossingWeight b t u →
      CrossingWeight b t v → u < v → False := by
    intro u v hu hv huv
    have hp : 3 * 3 ^ u ≤ 3 ^ v := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show u + 1 ≤ v by omega)
      simpa only [Nat.pow_succ, Nat.mul_comm] using h
    have hs := Nat.mul_le_mul_left (2 ^ b) hp
    have he : 2 ^ b * (3 * 3 ^ u) = 3 * (2 ^ b * 3 ^ u) := by ac_rfl
    rw [he] at hs
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hv1, hv2⟩ := hv
    omega
  by_cases he : j = k
  · exact he
  · have ho : j < k ∨ k < j := by omega
    rcases ho with h | h
    · exact False.elim (impossible j k hj hk h)
    · exact False.elim (impossible k j hk hj h)

/-- A first crossing cannot happen on the odd branch, whose slope is 3/2. -/
theorem no_odd_crossing (A M : Nat) (hprev : M ≤ A) : ¬ 3 * A < 2 * M := by
  omega

theorem crossing_image_width {ell t b j : Nat} (ht : t ≤ ell) (hb : b ≤ ell)
    (hc : 2 ^ b * 3 ^ j < 2 ^ t) :
    2 ^ (ell - t) * 3 ^ j < 2 ^ (ell - b) := by
  have h := Nat.mul_lt_mul_of_pos_right hc
    (Nat.pow_pos (n := ell - t) (by decide : 0 < 2))
  have hp : 2 ^ t * 2 ^ (ell - t) = 2 ^ ell := by
    rw [← Nat.pow_add, Nat.add_sub_of_le ht]
  have hp' : 2 ^ ell = 2 ^ b * 2 ^ (ell - b) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hb]
  have he : (2 ^ b * 3 ^ j) * 2 ^ (ell - t) =
      2 ^ b * (2 ^ (ell - t) * 3 ^ j) := by ac_rfl
  rw [he, hp, hp'] at h
  exact Nat.lt_of_mul_lt_mul_left h

#print axioms block_image_lower
#print axioms shorter_horizon_image
#print axioms crossing_weight_unique
#print axioms no_odd_crossing
#print axioms crossing_image_width

/-- Supporting exact comparisons for the written bound beta > 15/16. -/
theorem entropy_margin_constants :
    (2 : Nat) ^ 19 < 3 ^ 12 ∧
    (12 : Nat) ^ 2 < 3 * 7 ^ 2 ∧
    (2 : Nat) ^ 14 < 3 ^ 9 ∧ (9 : Nat) * 16 < 15 * 10 := by decide

#print axioms entropy_margin_constants

end CollatzPacking
