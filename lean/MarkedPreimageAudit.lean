/- Exact valuation-word inversion, ordinary clocks, and interval endpoints.
   These lemmas audit the marked preimage formula's finite ingredients.
   No Fourier estimate, probability approximation, or Collatz claim is added. -/
import Std
import ClockedMinimum

namespace MarkedPreimageAudit
open OrdinaryCollatz ClockedMinimum

def numerator : List Nat → Nat
  | [] => 0
  | a :: w => 3 ^ w.length + 2 ^ a * numerator w

def PositiveWord (w : List Nat) : Prop := ∀ a ∈ w, 0 < a

def Chain : List Nat → Nat → Nat → Prop
  | [], n, m => n = m ∧ n % 2 = 1
  | a :: w, n, m => 0 < a ∧ n % 2 = 1 ∧
      ∃ q, 2 ^ a * q = 3 * n + 1 ∧ Chain w q m

def AffineEquation (w : List Nat) (n m : Nat) : Prop :=
  2 ^ w.sum * m = 3 ^ w.length * n + numerator w

theorem chain_start_odd (w : List Nat) (n m : Nat) (h : Chain w n m) : n % 2 = 1 := by
  cases w with
  | nil => exact h.2
  | cons a w => exact h.2.1

theorem chain_end_odd (w : List Nat) (n m : Nat) (h : Chain w n m) : m % 2 = 1 := by
  induction w generalizing n with
  | nil => exact h.1 ▸ h.2
  | cons a w ih => obtain ⟨_, _, q, _, ht⟩ := h; exact ih q ht

theorem chain_affine (w : List Nat) (n m : Nat) (h : Chain w n m) : AffineEquation w n m := by
  induction w generalizing n with
  | nil => simp only [AffineEquation, List.sum_nil, List.length_nil, numerator, Nat.pow_zero]; grind [Chain]
  | cons a w ih =>
    obtain ⟨_, _, q, hq, ht⟩ := h
    have hh := ih q ht
    simp only [AffineEquation, List.sum_cons, List.length_cons, numerator, Nat.pow_add, Nat.pow_succ] at *
    grind

theorem affine_chain (w : List Nat) (n m : Nat) (hw : PositiveWord w)
    (hm : m % 2 = 1) (h : AffineEquation w n m) : Chain w n m := by
  induction w generalizing n with
  | nil =>
    simp only [AffineEquation, List.sum_nil, List.length_nil, numerator, Nat.pow_zero,
      Nat.one_mul, Nat.add_zero] at h
    exact ⟨h.symm, h ▸ hm⟩
  | cons a w ih =>
    have ha : 0 < a := hw a (by simp)
    have hwt : PositiveWord w := by intro b hb; exact hw b (by simp [hb])
    have hp := Nat.two_pow_pos a
    have he : 2 ^ a * (2 ^ w.sum * m) =
        3 ^ w.length * (3 * n + 1) + 2 ^ a * numerator w := by
      simp only [AffineEquation, List.sum_cons, List.length_cons, numerator,
        Nat.pow_add, Nat.pow_succ] at h
      grind
    have hd : 2 ^ a ∣ 3 ^ w.length * (3 * n + 1) := by
      apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right (2 ^ a) (numerator w))).mpr
      rw [← he]
      exact Nat.dvd_mul_right _ _
    have hc : Nat.Coprime (2 ^ a) (3 ^ w.length) :=
      Nat.Coprime.pow a w.length (by decide : Nat.Coprime 2 3)
    obtain ⟨q, hq⟩ := hc.dvd_of_dvd_mul_left hd
    have ht : AffineEquation w q m := by
      apply Nat.eq_of_mul_eq_mul_left hp
      change 2 ^ a * (2 ^ w.sum * m) = 2 ^ a * (3 ^ w.length * q + numerator w)
      rw [he, hq]
      grind
    have htail := ih q hwt ht
    have hpmod := Nat.two_pow_mod_two_eq_zero.mpr ha
    have hodd : n % 2 = 1 := by
      have hh := congrArg (fun z : Nat => z % 2) hq
      rw [Nat.mul_mod (2 ^ a) q 2, hpmod, Nat.zero_mul, Nat.zero_mod] at hh
      omega
    exact ⟨ha, hodd, q, hq.symm, htail⟩

theorem affine_iff_chain (w : List Nat) (n m : Nat) (hw : PositiveWord w)
    (hm : m % 2 = 1) : AffineEquation w n m ↔ Chain w n m :=
  ⟨affine_chain w n m hw hm, chain_affine w n m⟩

theorem odd_power_unique (a b u v : Nat) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (he : 2 ^ a * u = 2 ^ b * v) : a = b ∧ u = v := by
  have ordered : ∀ a b u v : Nat, a ≤ b → u % 2 = 1 →
      2 ^ a * u = 2 ^ b * v → a = b ∧ u = v := by
    intro a b u v hab hu he
    have hb : b = a + (b - a) := by omega
    rw [hb, Nat.pow_add, Nat.mul_assoc] at he
    have hc := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos a) he
    have hz : b - a = 0 := by
      by_cases hz : b - a = 0
      · exact hz
      · have hp := Nat.two_pow_mod_two_eq_zero.mpr (by omega : 0 < b - a)
        have hh := congrArg (fun z : Nat => z % 2) hc
        simp only [Nat.mul_mod, hp, Nat.zero_mul, Nat.zero_mod, hu] at hh
        omega
    have hab' : a = b := by omega
    simp only [hz, Nat.pow_zero, Nat.one_mul] at hc
    exact ⟨hab', hc⟩
  by_cases hab : a ≤ b
  · exact ordered a b u v hab hu he
  · have ht := ordered b a v u (by omega) hv he.symm
    exact ⟨ht.1.symm, ht.2.symm⟩

theorem chain_unique (w z : List Nat) (n m q : Nat)
    (hl : w.length = z.length) (hw : Chain w n m) (hz : Chain z n q) :
    w = z ∧ m = q := by
  induction w generalizing z n with
  | nil =>
    have he : z = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst z
    exact ⟨rfl, by have h1 := hw.1; have h2 := hz.1; omega⟩
  | cons a w ih =>
    cases z with
    | nil => simp at hl
    | cons b z =>
      obtain ⟨_, _, u, hu, hwu⟩ := hw
      obtain ⟨_, _, v, hv, hzv⟩ := hz
      have hvu := odd_power_unique a b u v (chain_start_odd w u m hwu)
        (chain_start_odd z v q hzv) (by omega)
      obtain ⟨rfl, rfl⟩ := hvu
      have ht := ih z u (by simpa using hl) hwu hzv
      exact ⟨by rw [ht.1], ht.2⟩

theorem affine_inverse_unique (w z : List Nat) (n m q : Nat)
    (hl : w.length = z.length) (hw : PositiveWord w) (hz : PositiveWord z)
    (hm : m % 2 = 1) (hq : q % 2 = 1)
    (he : AffineEquation w n m) (hf : AffineEquation z n q) : w = z ∧ m = q :=
  chain_unique w z n m q hl (affine_chain w n m hw hm he) (affine_chain z n q hz hq hf)

theorem halve_power (a q : Nat) : iterate a (2 ^ a * q) = q := by
  induction a with
  | zero => simp [iterate]
  | succ a ih =>
    have hc : C (2 ^ (a + 1) * q) = 2 ^ a * q := by
      have he : 2 ^ (a + 1) * q = 2 * (2 ^ a * q) := by rw [Nat.pow_succ]; grind
      rw [he]
      simp only [C]
      have hm : (2 * (2 ^ a * q)) % 2 ≠ 1 := by omega
      rw [if_neg hm]
      omega
    simpa only [iterate, hc] using ih

theorem chain_clock (w : List Nat) (n m : Nat) (h : Chain w n m) :
    iterate (w.length + w.sum) n = m := by
  induction w generalizing n with
  | nil => simpa only [List.length_nil, List.sum_nil, Nat.zero_add, iterate] using h.1
  | cons a w ih =>
    obtain ⟨_, hn, q, hq, ht⟩ := h
    have hs : iterate (a + 1) n = q := by
      simp only [iterate, C, if_pos hn]
      rw [← hq]
      exact halve_power a q
    have hlen : (a :: w).length + (a :: w).sum = (a + 1) + (w.length + w.sum) := by simp; omega
    rw [hlen, iterate_add, hs]
    exact ih q ht

theorem first_odd_splice (h n i t : Nat)
    (hp : ∀ j, j < i → ¬ (iterate j n % 2 = 1 ∧ iterate j n ≤ h)) :
    FirstOddBelow h n (i + t) ↔ FirstOddBelow h (iterate i n) t := by
  constructor
  · intro ht
    refine ⟨?_, ?_, ?_⟩
    · simpa only [iterate_add] using ht.1
    · simpa only [iterate_add] using ht.2.1
    · intro j hj
      have hn := ht.2.2 (i + j) (by omega)
      simpa only [iterate_add] using hn
  · intro ht
    refine ⟨?_, ?_, ?_⟩
    · simpa only [iterate_add] using ht.1
    · simpa only [iterate_add] using ht.2.1
    · intro j hj
      by_cases hji : j < i
      · exact hp j hji
      · have he : j = i + (j - i) := by omega
        rw [he, iterate_add]
        exact ht.2.2 (j - i) (by omega)

theorem marked_chain_splice (w : List Nat) (h n m t : Nat) (hw : Chain w n m)
    (hp : ∀ j, j < w.length + w.sum → ¬ (iterate j n % 2 = 1 ∧ iterate j n ≤ h))
    (ht : FirstOddBelow h m t) :
    FirstOddBelow h n (w.length + w.sum + t) ∧
      iterate (w.length + w.sum + t) n = iterate t m := by
  have hc := chain_clock w n m hw
  constructor
  · apply (first_odd_splice h n (w.length + w.sum) t hp).mpr
    simpa only [hc] using ht
  · rw [iterate_add, hc]

theorem interval_mismatch_localization (n u y e : Rat)
    (he : 0 ≤ e ∧ e < 1) (hnu : n ≤ u)
    (hl : (1 - e) * u ≤ n)
    (hm : (y ≤ n ∧ n < 2 * y) ≠ (y ≤ u ∧ u < 2 * y)) :
    ((1 - e) * y ≤ n ∧ n < y) ∨
      (2 * (1 - e) * y ≤ n ∧ n < 2 * y) := by
  by_cases hold : y ≤ n ∧ n < 2 * y
  · have hnew : ¬ (y ≤ u ∧ u < 2 * y) := by intro hh; exact hm (propext (by simp [hold, hh]))
    have hu : 2 * y ≤ u := by grind
    have hp := Rat.mul_le_mul_of_nonneg_left hu (by grind : 0 ≤ 1 - e)
    right
    grind
  · have hnew : y ≤ u ∧ u < 2 * y := by
      apply Classical.byContradiction
      intro hh
      exact hm (propext (by simp [hold, hh]))
    have hp := Rat.mul_le_mul_of_nonneg_left hnew.1 (by grind : 0 ≤ 1 - e)
    left
    grind

theorem backward_envelope_gate (terminal state floor scale offset bound budget : Rat)
    (hs : 0 ≤ state) (hb : 0 ≤ bound) (hscale : scale ≤ bound)
    (hoff : offset ≤ budget) (he : terminal = scale * state + offset)
    (hgate : bound * floor + budget < terminal) : floor < state := by
  have hp := Rat.mul_le_mul_of_nonneg_right hscale hs
  by_cases ht : floor < state
  · exact ht
  · have hm := Rat.mul_le_mul_of_nonneg_left (by grind : state ≤ floor) hb
    grind

theorem ungated_preimage_witness :
    AffineEquation [1, 3, 1] 19 17 ∧ FirstOddBelow 16 17 3 ∧
      FirstOddBelow 16 19 6 ∧ ¬ FirstOddBelow 16 19 11 := by
  have htail : FirstOddBelow 16 17 3 := by
    refine ⟨by decide, by decide, ?_⟩
    intro j hj
    have hc : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hc with rfl | rfl | rfl <;> decide
  have hfirst : FirstOddBelow 16 19 6 := by
    refine ⟨by decide, by decide, ?_⟩
    intro j hj
    have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨by unfold AffineEquation; decide, htail, hfirst, ?_⟩
  intro hbad
  exact hbad.2.2 6 (by decide) ⟨hfirst.1, hfirst.2.1⟩

#print axioms affine_iff_chain
#print axioms odd_power_unique
#print axioms chain_unique
#print axioms affine_inverse_unique
#print axioms halve_power
#print axioms chain_clock
#print axioms first_odd_splice
#print axioms marked_chain_splice
#print axioms interval_mismatch_localization
#print axioms backward_envelope_gate
#print axioms ungated_preimage_witness

end MarkedPreimageAudit
