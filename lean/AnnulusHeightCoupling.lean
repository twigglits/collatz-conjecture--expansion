/-
  Actual-annulus endpoint heights after the available source bits.
  Integer normalized-height and signed-count identities are kernel proofs.
  Logarithms, probability consequences, and transport discussion are written.
-/
import CountReturnControl

namespace AnnulusHeightCoupling
open CollatzAffine CoalescenceTail EscapeWeightRefinements CountReturnControl

def height (t n : Nat) : Nat := scale t n * orbit t n

def heightGap (t n : Nat) : Nat :=
  (height t (n + 1) - height t n) + (height t n - height t (n + 1))

theorem height_affine_identity (t n : Nat) :
    2 ^ t * height t n = 3 ^ t * n + correction t n := by
  unfold height
  have he : 2 ^ t * (scale t n * orbit t n) = scale t n * (2 ^ t * orbit t n) := by ac_rfl
  rw [he, scaled_orbit_identity]

theorem height_lift (t q n : Nat) :
    height t (2 ^ t * q + n) = 3 ^ t * q + height t n := by
  unfold height
  rw [(data_lift t q n).1, affine, Nat.mul_add]
  have he : scale t n * (3 ^ wt t n * q) = (scale t n * 3 ^ wt t n) * q := by ac_rfl
  rw [he, scale_identity]

theorem height_annulus_lower (t r : Nat) :
    3 ^ t ≤ height t (2 ^ t + r) := by
  have hh := height_lift t 1 r
  simp only [Nat.mul_one] at hh
  omega

theorem height_gap_lift (t q n : Nat) :
    heightGap t (2 ^ t * q + n) = heightGap t n := by
  unfold heightGap
  rw [Nat.add_assoc, height_lift, height_lift]
  omega

theorem height_gap_bound (t n : Nat) :
    2 ^ t * heightGap t n ≤ 3 ^ t + correction t n + correction t (n + 1) := by
  have h0 := height_affine_identity t n
  have h1 := height_affine_identity t (n + 1)
  have hp : 0 < 3 ^ t := Nat.pow_pos (by decide)
  rw [Nat.mul_add, Nat.mul_one] at h1
  simp only [heightGap, Nat.mul_add, Nat.mul_sub_left_distrib]
  omega

theorem total_constant (m c : Nat) : total m (fun _ => c) = m * c := by
  induction m with
  | zero => simp [total]
  | succ m ih => simp only [total, ih, Nat.succ_mul]

theorem total_interleave (m : Nat) (f : Nat → Nat) :
    total (2 * m) f = total m (fun r => f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, total, total, ih, total]
    omega

/-- Integer form of mean |X/3^a-Y/3^b| <= (2/3)^(k+1) on the actual annulus. -/
theorem annulus_height_gap_mass (k : Nat) :
    2 ^ (k + 2) * total (2 ^ k)
      (fun r => heightGap (k + 1) (2 ^ (k + 1) + 2 * r)) ≤ 8 ^ (k + 1) := by
  let t := k + 1
  have hl := total_ext (2 ^ k)
    (fun r => heightGap t (2 ^ t + 2 * r)) (fun r => heightGap t (2 * r))
    (fun r _ => by simpa only [Nat.mul_one] using height_gap_lift t 1 (2 * r))
  have hb := total_le (2 ^ k) (fun r => 2 ^ t * heightGap t (2 * r))
    (fun r => 3 ^ t + (correction t (2 * r) + correction t (2 * r + 1)))
    (fun r _ => by have hh := height_gap_bound t (2 * r); omega)
  rw [total_mul, total_sum, total_constant, ← total_interleave] at hb
  have he : 2 * 2 ^ k = 2 ^ t := by dsimp [t]; rw [Nat.pow_succ]; ac_rfl
  rw [he] at hb
  have hm := correction_mass t
  have hh := Nat.mul_le_mul_left 2 hb
  rw [Nat.mul_add] at hh
  have hconst : 2 * (2 ^ k * 3 ^ t) = 6 ^ t := by
    calc
      2 * (2 ^ k * 3 ^ t) = (2 * 2 ^ k) * 3 ^ t := by ac_rfl
      _ = 2 ^ t * 3 ^ t := by rw [he]
      _ = 6 ^ t := by rw [← Nat.mul_pow]
  rw [hconst] at hh
  have hpow : 2 ^ (k + 2) = 2 * 2 ^ t := by
    dsimp [t]
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.pow_succ]
    ac_rfl
  change 2 ^ (k + 2) * total (2 ^ k) (fun r => heightGap t (2 ^ t + 2 * r)) ≤ 8 ^ t
  rw [hl, hpow, Nat.mul_assoc]
  omega

theorem weight_children (t n : Nat) :
    wt (t + 1) n + wt (t + 1) (2 ^ t + n) = 2 * wt t n + 1 := by
  rw [weight_snoc, weight_snoc, endpoint_parity_flip]
  have hl := weight_lift t 1 n
  simp only [Nat.mul_one] at hl
  rw [hl]
  omega

def parityMass (k e : Nat) : Nat := total (2 ^ k) (fun r => wt (k + 1) (2 * r + e))

theorem parity_mass_recurrence (k e : Nat) :
    parityMass (k + 1) e = 2 * parityMass k e + 2 ^ k := by
  unfold parityMass
  rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
  have he := total_ext (2 ^ k)
    (fun r => wt (k + 1 + 1) (2 * r + e) + wt (k + 1 + 1) (2 * (2 ^ k + r) + e))
    (fun r => 2 * wt (k + 1) (2 * r + e) + 1)
    (fun r _ => by
      have hs : 2 * (2 ^ k + r) + e = 2 ^ (k + 1) + (2 * r + e) := by
        rw [Nat.pow_succ]; omega
      rw [hs]
      exact weight_children (k + 1) (2 * r + e))
  rw [he, total_sum, total_mul, total_constant]
  simp only [Nat.mul_one]

theorem signed_even_count_mass (k : Nat) :
    parityMass k 1 = parityMass k 0 + 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [parity_mass_recurrence, parity_mass_recurrence, ih, Nat.pow_succ]
    omega

theorem annulus_signed_count_mass (k : Nat) :
    total (2 ^ k) (fun r => wt (k + 1) (2 ^ (k + 1) + 2 * r + 1)) =
      total (2 ^ k) (fun r => wt (k + 1) (2 ^ (k + 1) + 2 * r)) + 2 ^ k := by
  have h1 := total_ext (2 ^ k)
    (fun r => wt (k + 1) (2 ^ (k + 1) + 2 * r + 1))
    (fun r => wt (k + 1) (2 * r + 1))
    (fun r _ => by
      have hh := weight_lift (k + 1) 1 (2 * r + 1)
      simpa only [Nat.mul_one, Nat.add_assoc] using hh)
  have h0 := total_ext (2 ^ k)
    (fun r => wt (k + 1) (2 ^ (k + 1) + 2 * r))
    (fun r => wt (k + 1) (2 * r))
    (fun r _ => by simpa only [Nat.mul_one] using weight_lift (k + 1) 1 (2 * r))
  rw [h1, h0]
  simpa only [parityMass, Nat.add_zero] using signed_even_count_mass k

#print axioms height_affine_identity
#print axioms height_lift
#print axioms height_annulus_lower
#print axioms height_gap_lift
#print axioms height_gap_bound
#print axioms total_constant
#print axioms total_interleave
#print axioms annulus_height_gap_mass
#print axioms weight_children
#print axioms parity_mass_recurrence
#print axioms signed_even_count_mass
#print axioms annulus_signed_count_mass

end AnnulusHeightCoupling
