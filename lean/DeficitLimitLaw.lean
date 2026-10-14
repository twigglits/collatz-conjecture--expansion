/-
  Finite rational algebra for the written deficit-limit argument.
  These statements do not formalize the analytic coupling, packing,
  limiting probability law, or a universal convergence theorem.
-/
import Std

namespace DeficitLimitLaw

def deficit : List Rat → Rat
  | [] => 0
  | w :: ws => (1 - w) + deficit ws

theorem deficit_append (ws vs : List Rat) :
    deficit (ws ++ vs) = deficit ws + deficit vs := by
  induction ws with
  | nil => simp only [List.nil_append, deficit]; grind
  | cons w ws ih => simp only [List.cons_append, deficit, ih]; grind

theorem deficit_scaled (p : Rat) (ws : List Rat) :
    deficit (ws.map (p * ·)) =
      p * deficit ws + (1 - p) * (ws.length : Rat) := by
  induction ws with
  | nil => simp only [List.map_nil, deficit, List.length_nil]; grind
  | cons w ws ih =>
    simp only [List.map_cons, deficit, List.length_cons, Rat.natCast_add, ih]
    grind

theorem deficit_splice (p : Rat) (front tail : List Rat) :
    deficit (front ++ tail.map (p * ·)) =
      deficit tail + deficit front + (1 - p) * ((tail.length : Rat) - deficit tail) := by
  rw [deficit_append, deficit_scaled]
  grind

theorem deficit_range (ws : List Rat)
    (h : ∀ w ∈ ws, 0 ≤ w ∧ w ≤ 1) :
    0 ≤ deficit ws ∧ deficit ws ≤ (ws.length : Rat) := by
  induction ws with
  | nil => simp [deficit]
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht := ih (by intro v hv; exact h v (by simp [hv]))
    simp only [deficit, List.length_cons, Rat.natCast_add]
    grind

theorem deficit_prefix_bound (e : Rat) (ws : List Rat)
    (h : ∀ w ∈ ws, 1 - e ≤ w ∧ w ≤ 1) :
    0 ≤ deficit ws ∧ deficit ws ≤ e * (ws.length : Rat) := by
  induction ws with
  | nil => simp [deficit]
  | cons w ws ih =>
    have hw := h w (by simp)
    have ht := ih (by intro v hv; exact h v (by simp [hv]))
    simp only [deficit, List.length_cons, Rat.natCast_add]
    grind

theorem splice_increase_bound (p d t e a i : Rat)
    (hp : p ≤ 1) (he : 1 - p ≤ e)
    (hd : 0 ≤ d) (ht : d ≤ t)
    (ha : 0 ≤ a) (hae : a ≤ e * i) :
    0 ≤ a + p * d + (1 - p) * t - d ∧
      a + p * d + (1 - p) * t - d ≤ e * (i + t) := by
  have hpn : 0 ≤ 1 - p := by grind
  have htd : 0 ≤ t - d := by grind
  have htn : 0 ≤ t := by grind
  have hlo := Rat.mul_nonneg hpn htd
  have h1 := Rat.mul_le_mul_of_nonneg_left (show t - d ≤ t by grind) hpn
  have h2 := Rat.mul_le_mul_of_nonneg_right he htn
  grind

theorem common_tail_bound (d e x y tx ty : Rat)
    (hx : 0 ≤ x - d ∧ x - d ≤ e * tx)
    (hy : 0 ≤ y - d ∧ y - d ≤ e * ty) :
    x - y ≤ e * tx ∧ y - x ≤ e * ty := by grind

theorem shared_terminal_weight_bound (p q r e : Rat)
    (hp : 1 - e ≤ p ∧ p ≤ 1)
    (hq : 1 - e ≤ q ∧ q ≤ 1)
    (hr : 0 ≤ r ∧ r ≤ 1) :
    p * r - q * r ≤ e ∧ q * r - p * r ≤ e := by
  have hen : 0 ≤ e := by grind
  have h1 := Rat.mul_le_mul_of_nonneg_right (show p - q ≤ e by grind) hr.1
  have h2 := Rat.mul_le_mul_of_nonneg_right (show q - p ≤ e by grind) hr.1
  have h3 := Rat.mul_le_mul_of_nonneg_left hr.2 hen
  grind

def total : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | k + 1, f => total k f + f k

theorem deficit_chain (d e : Nat → Rat) (k : Nat)
    (h : ∀ j < k, d j - d (j + 1) ≤ e j) :
    d 0 - d k ≤ total k e := by
  induction k with
  | zero => simp only [total]; grind
  | succ k ih =>
    have ht := ih (by intro j hj; exact h j (by omega))
    have hl := h k (by omega)
    simp only [total]
    grind

theorem clock_chain (t l : Nat → Rat) (k : Nat)
    (h : ∀ j < k, t j ≤ l j + t (j + 1)) :
    t 0 ≤ t k + total k l := by
  have hc := deficit_chain t l k (by intro j hj; have := h j hj; grind)
  grind

#print axioms deficit_append
#print axioms deficit_scaled
#print axioms deficit_splice
#print axioms deficit_range
#print axioms deficit_prefix_bound
#print axioms splice_increase_bound
#print axioms common_tail_bound
#print axioms shared_terminal_weight_bound
#print axioms deficit_chain
#print axioms clock_chain

end DeficitLimitLaw
