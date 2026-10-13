/-
  Arithmetic for the quadratic energy of finite binary-to-ternary images.
  Haar integration, fibre ordering, interpolation, and infinite return
  densities are written in docs/BINARY-IMAGE-ENERGY.md.
-/
import ReturnCorrectionMoments
import ReturnImageBounds
import Init.Data.Nat.Coprime

namespace BinaryImageEnergy
open CollatzAffine CoalescenceTail ReturnCorrectionMoments ReturnImageBounds

theorem total_const (m c : Nat) : total m (fun _ => c) = m * c := by
  induction m with
  | zero => simp [total]
  | succ m ih => simp only [total, ih, Nat.succ_mul]

/-- The full-period mean affine correction is exactly t/4. -/
theorem numerator_mass (t : Nat) :
    4 * total (2 ^ t) (numerator t) = t * 4 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    have he := total_ext (2 ^ t)
      (fun n => numerator (t + 1) n + numerator (t + 1) (2 ^ t + n))
      (fun n => 4 * numerator t n + 2 ^ t) (fun n _ => numerator_children t n)
    rw [he, total_sum, total_mul, total_const, ← four_pow]
    rw [Nat.mul_add, ih, Nat.pow_succ 4]
    grind

/-- The two source coordinates agree if their count and numerator agree. -/
theorem source_eq_of_numerator_eq (t a r s : Nat)
    (hr : r < 2 ^ t) (hs : s < 2 ^ t)
    (har : wt t r = a) (has : wt t s = a)
    (hn : numerator t r = numerator t s) : r = s := by
  have er := orbit_equation t r
  have es := orbit_equation t s
  rw [har, hn] at er
  rw [has] at es
  have hcop : Nat.Coprime (2 ^ t) (3 ^ a) :=
    Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)
  have he : 3 ^ a * (s - r) = 2 ^ t * orbit t s - 2 ^ t * orbit t r := by
    rw [Nat.mul_sub_left_distrib, er, es]
    omega
  have hd : 2 ^ t ∣ 3 ^ a * (s - r) := by
    rw [he]
    exact Nat.dvd_sub (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  have hm := Nat.mod_eq_zero_of_dvd (hcop.dvd_of_dvd_mul_left hd)
  rw [Nat.mod_eq_of_lt (show s - r < 2 ^ t by omega)] at hm
  have he' : 3 ^ a * (r - s) = 2 ^ t * orbit t r - 2 ^ t * orbit t s := by
    rw [Nat.mul_sub_left_distrib, er, es]
    omega
  have hd' : 2 ^ t ∣ 3 ^ a * (r - s) := by
    rw [he']
    exact Nat.dvd_sub (Nat.dvd_mul_right _ _) (Nat.dvd_mul_right _ _)
  have hm' := Nat.mod_eq_zero_of_dvd (hcop.dvd_of_dvd_mul_left hd')
  rw [Nat.mod_eq_of_lt (show r - s < 2 ^ t by omega)] at hm'
  omega

theorem numerator_image_residue (t a r : Nat) (ha : wt t r = a) :
    numerator t r % 3 ^ a = (2 ^ t * (orbit t r % 3 ^ a)) % 3 ^ a := by
  have he := congrArg (fun x => x % 3 ^ a) (orbit_equation t r)
  rw [ha, Nat.mul_add_mod] at he
  rw [← he, Nat.mul_mod (2 ^ t) (orbit t r), Nat.mul_mod (2 ^ t) (orbit t r % 3 ^ a)]
  simp

/-- Quotients of affine numerators are distinct within one image fibre. -/
theorem quotient_injective_on_fibre (t a r s : Nat)
    (hr : r < 2 ^ t) (hs : s < 2 ^ t)
    (har : wt t r = a) (has : wt t s = a)
    (hi : orbit t r % 3 ^ a = orbit t s % 3 ^ a)
    (hq : numerator t r / 3 ^ a = numerator t s / 3 ^ a) : r = s := by
  have hm : numerator t r % 3 ^ a = numerator t s % 3 ^ a := by
    rw [numerator_image_residue t a r har, numerator_image_residue t a s has, hi]
  have er := Nat.mod_add_div (numerator t r) (3 ^ a)
  have es := Nat.mod_add_div (numerator t s) (3 ^ a)
  rw [hm, hq] at er
  exact source_eq_of_numerator_eq t a r s hr hs har has (by omega)

theorem consecutive_mass (m : Nat) :
    2 * total m (fun j => j + 1) = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [total, Nat.mul_add, ih]; grind

/-- Sort distinct nonnegative quotients increasingly to apply this bound. -/
theorem ranked_numerator_cost (m d : Nat) (N : Nat → Nat)
    (hr : ∀ j, j < m → j ≤ N j / d) :
    d * m * m ≤ 2 * total m (fun j => d + N j) := by
  have he := total_le m (fun j => d * (j + 1)) (fun j => d + N j) (by
    intro j hj
    have hq := Nat.mul_le_mul_left d (hr j hj)
    have hn := Nat.mod_add_div (N j) d
    rw [Nat.mul_add, Nat.mul_one]
    omega)
  rw [total_mul] at he
  have hc := consecutive_mass m
  have hprod := Nat.mul_le_mul_left 2 he
  have hident : 2 * (d * total m (fun j => j + 1)) = d * (m * (m + 1)) := by
    calc
      2 * (d * total m (fun j => j + 1)) = d * (2 * total m (fun j => j + 1)) := by ac_rfl
      _ = _ := by rw [hc]
  rw [hident] at hprod
  have hsmall : d * m * m ≤ d * (m * (m + 1)) := by
    rw [← Nat.mul_assoc]
    exact Nat.mul_le_mul_left (d * m) (by omega)
  exact Nat.le_trans hsmall hprod

theorem image_cost_mass (t : Nat) :
    4 * total (2 ^ t) (fun r => 3 ^ wt t r + numerator t r) =
      (t + 4) * 4 ^ t := by
  rw [total_sum, Nat.mul_add, cubic_mass, numerator_mass]
  grind

/-- Squared L2 norm bound is (t+1)(t+4)/2, hence norm at most t+2. -/
theorem quadratic_norm_cap (t : Nat) :
    (t + 1) * (t + 4) ≤ 2 * (t + 2) ^ 2 := by grind

theorem cumulative_linear_mass (H : Nat) :
    2 * total H (fun j => j + 3) = H * (H + 5) := by
  induction H with
  | zero => rfl
  | succ H ih => simp only [total, Nat.mul_add, ih]; grind

theorem cumulative_quadratic_cap (H : Nat) (hH : 1 ≤ H) :
    total H (fun j => j + 3) ≤ 3 * H ^ 2 := by
  have he := cumulative_linear_mass H
  have hb := Nat.mul_le_mul_left H (show H + 5 ≤ 6 * H by omega)
  have hm : H * (6 * H) = 6 * H ^ 2 := by grind
  rw [← he, hm] at hb
  omega

#print axioms total_const
#print axioms numerator_mass
#print axioms source_eq_of_numerator_eq
#print axioms numerator_image_residue
#print axioms quotient_injective_on_fibre
#print axioms consecutive_mass
#print axioms ranked_numerator_cost
#print axioms image_cost_mass
#print axioms quadratic_norm_cap
#print axioms cumulative_linear_mass
#print axioms cumulative_quadratic_cap

end BinaryImageEnergy
