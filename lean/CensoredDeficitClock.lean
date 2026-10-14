/- Finite rational accounting for deficits stopped at a first arrival.
   Logarithmic-clock limits and the external positivity implication are
   written mathematics, not assertions of this kernel module. -/
import DeficitClockMoment

namespace CensoredDeficitClock
open DeficitLimitLaw DeficitClockMoment

def cell (hit : Bool) (w : Rat) : Rat := if hit then 0 else 1 - w

theorem cell_accounting (hit : Bool) (w : Rat) :
    cell hit w = 1 - (if hit then 1 else 0) - w + (if hit then w else 0) := by
  cases hit <;> simp [cell] <;> grind

theorem cell_bounds (hit : Bool) (w : Rat) (hw : 0 ≤ w ∧ w ≤ 1) :
    0 ≤ cell hit w ∧ cell hit w ≤ 1 := by
  cases hit <;> simp [cell] <;> grind

theorem censored_sum_accounting (t : Nat) (hit : Nat → Bool) (w : Nat → Rat) :
    total t (fun j => cell (hit j) (w j)) =
      (t : Rat) - total t (fun j => if hit j then 1 else 0) - total t w +
        total t (fun j => if hit j then w j else 0) := by
  induction t with
  | zero => simp only [total]; grind
  | succ t ih =>
    simp only [total, ih, Rat.natCast_add]
    rw [cell_accounting]
    grind

theorem censored_sum_bounds (t : Nat) (hit : Nat → Bool) (w : Nat → Rat)
    (hw : ∀ j < t, 0 ≤ w j ∧ w j ≤ 1) :
    0 ≤ total t (fun j => cell (hit j) (w j)) ∧
      total t (fun j => cell (hit j) (w j)) ≤ (t : Rat) := by
  induction t with
  | zero => simp [total]
  | succ t ih =>
    have hp := ih (by intro j hj; exact hw j (by omega))
    have ht := cell_bounds (hit t) (w t) (hw t (by omega))
    simp only [total, Rat.natCast_add]
    grind

def stoppedDeficit : Nat → Nat → (Nat → Rat) → Rat
  | 0, _, _ => 0
  | t + 1, a, w => if a = 0 then 0 else
      (1 - w 0) + stoppedDeficit t (a - 1) (fun j => w (j + 1))

theorem stopped_is_shorter_prefix (t a : Nat) (w : Nat → Rat) :
    stoppedDeficit t a w = prefixDeficit (min t a) w := by
  induction t generalizing a w with
  | zero => simp [stoppedDeficit, prefixDeficit]
  | succ t ih =>
    cases a with
    | zero => simp [stoppedDeficit, prefixDeficit]
    | succ a => simp [stoppedDeficit, prefixDeficit, ih]

theorem cell_truncation_bound (hit : Bool) (w : Rat) (hw : 0 ≤ w ∧ w ≤ 1)
    (d h : Rat) (hd : 0 ≤ d ∧ d ≤ h) :
    0 ≤ d * cell hit w ∧ d * cell hit w ≤ h := by
  have hc := cell_bounds hit w hw
  have hlo := Rat.mul_nonneg hd.1 hc.1
  have hhi := Rat.mul_le_mul_of_nonneg_left hc.2 hd.1
  grind

theorem one_odd_loss_floor (a p w : Rat) (ha : 0 ≤ a)
    (hp : 0 ≤ p ∧ p ≤ 1) (hw : 0 ≤ w) (hloss : (a + 1) * w ≤ a) :
    1 ≤ (a + 1) * (1 - p * w) := by
  have h1 := Rat.mul_le_mul_of_nonneg_right hp.2 hw
  have h2 := Rat.mul_le_mul_of_nonneg_left h1 (show 0 ≤ a + 1 by grind)
  grind

theorem positive_density_forces_loss (b r v : Rat)
    (hv : 0 ≤ v) (hr : 0 < r) (h : r ≤ (3 * v + 1) * b) : 0 < b := by
  by_cases hp : 0 < b
  · exact hp
  · have hb : b ≤ 0 := by grind
    have hh := Rat.mul_le_mul_of_nonneg_left hb (show 0 ≤ 3 * v + 1 by grind)
    grind

theorem bad_mass_partition (known escape loss : Rat)
    (h : known + escape + loss = 1) :
    loss = 1 - known - escape := by grind

theorem integer_clock_above_transition : 2 ^ 3 * 3 ^ 8 < (4 : Nat) ^ 8 := by decide

#print axioms cell_accounting
#print axioms cell_bounds
#print axioms censored_sum_accounting
#print axioms censored_sum_bounds
#print axioms stopped_is_shorter_prefix
#print axioms cell_truncation_bound
#print axioms one_odd_loss_floor
#print axioms positive_density_forces_loss
#print axioms bad_mass_partition
#print axioms integer_clock_above_transition

end CensoredDeficitClock
