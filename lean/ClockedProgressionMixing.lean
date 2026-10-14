/- Finite arithmetic and coupling inequalities used in a written extension
   of the first-passage mixing argument. No asymptotic mixing is asserted. -/
import DeficitClockMoment

namespace ClockedProgressionMixing
open DeficitLimitLaw DeficitClockMoment

theorem preimage_residue_transfer (a m p n b r k : Int)
    (hp : p ≠ 0) (h : a * m = p * n + b) :
    a * m = b + p * r + 3 * p * k ↔ n = r + 3 * k := by
  constructor
  · intro hh
    have hc : p * n = p * (r + 3 * k) := by grind
    exact Int.eq_of_mul_eq_mul_left hp hc
  · intro hh
    grind

theorem seed_one_cleared (b p : Int) :
    2 * (b + 2 * p) = (2 * b + p) + 3 * p := by grind

theorem seed_two_cleared (b p : Int) :
    4 * (b + p) = (4 * b + p) + 3 * p := by grind

theorem prepend_affine_offset (a b d x : Rat) :
    a * (d * (3 * x + 1)) + b = (3 * a * d) * x + (b + a * d) := by
  grind

theorem matched_window_interval (t i : Nat) (e a p d l : Rat)
    (he : 0 ≤ e) (ha : 0 ≤ a ∧ a ≤ e * ((min t i : Nat) : Rat))
    (hp : 1 - e ≤ p ∧ p ≤ 1) (hd : 0 ≤ d ∧ d ≤ l)
    (hl : l ≤ ((t - i : Nat) : Rat)) :
    0 ≤ (a + p * d + (1 - p) * l) - d ∧
      (a + p * d + (1 - p) * l) - d ≤ e * (t : Rat) := by
  have hmin : min t i + (t - i) = t := by omega
  have hcast := congrArg (fun n : Nat => (n : Rat)) hmin
  simp only [Rat.natCast_add] at hcast
  have hb := splice_increase_bound p d l e a ((min t i : Nat) : Rat)
    hp.2 (by grind) hd.1 hd.2 ha.1 ha.2
  constructor
  · exact hb.1
  · have hi : ((min t i : Nat) : Rat) + l ≤ (t : Rat) := by grind
    exact Rat.le_trans hb.2 (Rat.mul_le_mul_of_nonneg_left hi he)

theorem matched_window_pair (t : Nat) (e x y d : Rat)
    (hx : 0 ≤ x - d ∧ x - d ≤ e * (t : Rat))
    (hy : 0 ≤ y - d ∧ y - d ≤ e * (t : Rat)) :
    x - y ≤ e * (t : Rat) ∧ y - x ≤ e * (t : Rat) := by
  grind

theorem matched_alive_cell (p q w e : Rat)
    (hp : 1 - e ≤ p ∧ p ≤ 1) (hq : 1 - e ≤ q ∧ q ≤ 1)
    (hw : 0 ≤ w ∧ w ≤ 1) :
    (1 - p * w) - (1 - q * w) ≤ e ∧
      (1 - q * w) - (1 - p * w) ≤ e := by
  have h := shared_terminal_weight_bound p q w e hp hq hw
  grind

theorem weighted_error_sum (n : Nat) (w d b : Nat → Rat) (e : Rat)
    (hw : ∀ j < n, 0 ≤ w j) (hd : ∀ j < n, d j ≤ e + b j) :
    total n (fun j => w j * d j) ≤ e * total n w + total n (fun j => w j * b j) := by
  induction n with
  | zero => simp only [total]; grind
  | succ n ih =>
    have hh := ih (by intro j hj; exact hw j (by omega))
      (by intro j hj; exact hd j (by omega))
    have ht := Rat.mul_le_mul_of_nonneg_left (hd n (by omega)) (hw n (by omega))
    simp only [total]
    grind

theorem coupling_mean_error (n : Nat) (w d b : Nat → Rat) (e eta : Rat)
    (hw : ∀ j < n, 0 ≤ w j) (hm : total n w = 1)
    (hd : ∀ j < n, d j ≤ e + b j ∧ -d j ≤ e + b j)
    (hb : total n (fun j => w j * b j) ≤ eta) :
    total n (fun j => w j * d j) ≤ e + eta ∧
      total n (fun j => w j * (-d j)) ≤ e + eta := by
  have h1 := weighted_error_sum n w d b e hw (by intro j hj; exact (hd j hj).1)
  have h2 := weighted_error_sum n w (fun j => -d j) b e hw (by intro j hj; exact (hd j hj).2)
  rw [hm, Rat.mul_one] at h1 h2
  grind

theorem neutral_bulk_balance (b t l u v : Rat) (h : 2 * u - v = 3) :
    2 * (b * (t + 2 - l - u)) = b * (t + 1 - l) + b * (t - l - v) := by
  grind

#print axioms preimage_residue_transfer
#print axioms seed_one_cleared
#print axioms seed_two_cleared
#print axioms prepend_affine_offset
#print axioms matched_window_interval
#print axioms matched_window_pair
#print axioms matched_alive_cell
#print axioms weighted_error_sum
#print axioms coupling_mean_error
#print axioms neutral_bulk_balance

end ClockedProgressionMixing
