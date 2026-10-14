/- Finite rational algebra for the deficit's remaining-clock moment.
   Infinite density limits, moment interchange and Collatz remain unproved. -/
import DeficitLimitLaw

namespace DeficitClockMoment
open DeficitLimitLaw

def prefixDeficit : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | t + 1, w => (1 - w 0) + prefixDeficit t (fun j => w (j + 1))

def clockLoss : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | t + 1, w => (t : Rat) * (w 0 - w 1) + clockLoss t (fun j => w (j + 1))

theorem loss_age_identity (t : Nat) (w : Nat → Rat) :
    prefixDeficit t w = (t : Rat) * (1 - w 0) + clockLoss t w := by
  induction t generalizing w with
  | zero => simp only [prefixDeficit, clockLoss]; grind
  | succ t ih =>
    simp only [prefixDeficit, clockLoss, ih, Rat.natCast_add]
    grind

theorem normalized_loss_age (t : Nat) (w : Nat → Rat) (h : w 0 = 1) :
    prefixDeficit t w = clockLoss t w := by
  have hi := loss_age_identity t w
  rw [h] at hi
  grind

theorem total_nonneg (t : Nat) (f : Nat → Rat)
    (h : ∀ j < t, 0 ≤ f j) : 0 ≤ total t f := by
  induction t with
  | zero => simp [total]
  | succ t ih =>
    have hp := ih (by intro j hj; exact h j (by omega))
    have ht := h t (by omega)
    simp only [total]
    grind

theorem total_mono (t : Nat) (f g : Nat → Rat)
    (h : ∀ j < t, f j ≤ g j) : total t f ≤ total t g := by
  induction t with
  | zero => simp [total]
  | succ t ih =>
    have hp := ih (by intro j hj; exact h j (by omega))
    have ht := h t (by omega)
    simp only [total]
    grind

theorem total_scaled (t : Nat) (c : Rat) (f : Nat → Rat) :
    total t (fun j => c * f j) = c * total t f := by
  induction t with
  | zero => simp only [total]; grind
  | succ t ih => simp only [total, ih]; grind

theorem weighted_total_bounds (t : Nat) (c : Rat) (w f : Nat → Rat)
    (hw : ∀ j < t, c ≤ w j ∧ w j ≤ 1)
    (hf : ∀ j < t, 0 ≤ f j) :
    c * total t f ≤ total t (fun j => w j * f j) ∧
      total t (fun j => w j * f j) ≤ total t f := by
  have hl := total_mono t (fun j => c * f j) (fun j => w j * f j)
    (by intro j hj; exact Rat.mul_le_mul_of_nonneg_right (hw j hj).1 (hf j hj))
  have hu := total_mono t (fun j => w j * f j) (fun j => 1 * f j)
    (by intro j hj; exact Rat.mul_le_mul_of_nonneg_right (hw j hj).2 (hf j hj))
  rw [total_scaled] at hl hu
  constructor
  · exact hl
  · grind

theorem capped_moment_split (g l : Rat) :
    g = min g l + max (g - l) 0 := by
  grind

#print axioms loss_age_identity
#print axioms normalized_loss_age
#print axioms total_nonneg
#print axioms total_mono
#print axioms total_scaled
#print axioms weighted_total_bounds
#print axioms capped_moment_split

end DeficitClockMoment
