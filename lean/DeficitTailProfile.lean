/- Finite tail-profile identities. Sequence-space convergence, moment
   interchange and uniform integrability remain written mathematics. -/
import DeficitClockMoment

namespace DeficitTailProfile
open DeficitLimitLaw DeficitClockMoment

def ageTail : Nat → Nat → (Nat → Rat) → Rat
  | 0, _, _ => 0
  | t + 1, l, w => ((t - l : Nat) : Rat) * (w 0 - w 1) +
      ageTail t l (fun j => w (j + 1))

theorem age_tail_is_shorter_clock (t l : Nat) (w : Nat → Rat) :
    ageTail t l w = clockLoss (t - l) w := by
  induction t generalizing w with
  | zero => simp [ageTail, clockLoss]
  | succ t ih =>
    by_cases h : l ≤ t
    · have he : t + 1 - l = (t - l) + 1 := by omega
      simp only [ageTail, ih, he, clockLoss]
    · have h0 : t - l = 0 := by omega
      have h1 : t + 1 - l = 0 := by omega
      simp only [ageTail, ih, h0, h1, clockLoss]
      grind

theorem age_tail_is_prefix (t l : Nat) (w : Nat → Rat) (h : w 0 = 1) :
    ageTail t l w = prefixDeficit (t - l) w := by
  rw [age_tail_is_shorter_clock, normalized_loss_age (t - l) w h]

theorem cutoff_in_tail (i t l : Nat) (h : l ≤ t) :
    i + t - l = i + (t - l) := by omega

theorem cutoff_in_front (i t l : Nat) (h : t ≤ l) :
    i + t - l ≤ i ∧ t - l = 0 := by omega

theorem simultaneous_common_tail (b x y : Nat → Rat) (ex ey : Rat)
    (hx : ∀ l, 0 ≤ x l - b l ∧ x l - b l ≤ ex)
    (hy : ∀ l, 0 ≤ y l - b l ∧ y l - b l ≤ ey) :
    ∀ l, x l - y l ≤ ex ∧ y l - x l ≤ ey := by
  intro l
  have hxl := hx l
  have hyl := hy l
  grind

theorem scalar_tail_below_clock_tail (d q k : Rat)
    (hq : 0 ≤ q) (hcap : d - q ≤ k) : max (d - k) 0 ≤ q := by grind

theorem tail_uniform_integrability_split (d q k e : Rat)
    (hqd : q ≤ d) (he : 0 ≤ e) :
    q ≤ e + (if e < q then k else 0) + max (d - k) 0 := by
  split <;> grind

theorem sparse_support_split (h d q l a : Rat)
    (ha : 0 ≤ a) (hcap : d - q ≤ l)
    (hh : h ≤ a * d + 1) :
    h ≤ a * l + 1 + a * q := by
  have hm := Rat.mul_le_mul_of_nonneg_left hcap ha
  grind

#print axioms age_tail_is_shorter_clock
#print axioms age_tail_is_prefix
#print axioms cutoff_in_tail
#print axioms cutoff_in_front
#print axioms simultaneous_common_tail
#print axioms scalar_tail_below_clock_tail
#print axioms tail_uniform_integrability_split
#print axioms sparse_support_split

end DeficitTailProfile
