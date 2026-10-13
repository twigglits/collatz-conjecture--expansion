/-
  An explicit sparse perturbation, NOT the Collatz map.
  Swapping selected odd outputs preserves the even rule and inverse-image
  congruences but creates an escaping path. Analytic density assertions
  are separate written deductions. No native evaluation or added axioms.
-/
import CollatzContradiction

namespace SparseCollatzPerturbation
open OrdinaryCollatz

def spine : Nat → Nat
  | 0 => 21845
  | j + 1 => 64 * spine j + 21

def partner (j : Nat) : Nat := (128 * spine j + 41) / 3

theorem spine_lower (j : Nat) : j + 21845 ≤ spine j := by
  induction j with
  | zero => decide
  | succ j ih => simp only [spine]; omega

theorem spine_mod (j : Nat) : spine j % 12 = 5 := by
  induction j with
  | zero => decide
  | succ j ih => simp [spine, Nat.add_mod, Nat.mul_mod, ih]

theorem spine_le {i j : Nat} (h : i ≤ j) : spine i ≤ spine j := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact Nat.le_refl _
    · have hh := ih (by omega)
      simp only [spine]
      omega

theorem spine_strict {i j : Nat} (h : i < j) : spine i < spine j := by
  have hh := spine_le (show i + 1 ≤ j by omega)
  simp only [spine] at hh
  omega

theorem spine_injective {i j : Nat} (h : spine i = spine j) : i = j := by
  by_cases hij : i < j
  · have := spine_strict hij; omega
  · by_cases hji : j < i
    · have := spine_strict hji; omega
    · omega

theorem spine_power (j : Nat) : 3 * spine j + 1 = 4 ^ (3 * j + 8) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have he : 3 * (j + 1) + 8 = (3 * j + 8) + 3 := by omega
    rw [he, Nat.pow_add, ← ih]
    simp only [spine]
    omega

theorem partner_eq (j : Nat) : 3 * partner j = 128 * spine j + 41 := by
  have := spine_mod j
  unfold partner
  omega

theorem partner_mod (j : Nat) : partner j % 4 = 3 := by
  have := partner_eq j
  have := spine_mod j
  omega

theorem partner_between (j : Nat) : spine j < partner j ∧ partner j < spine (j + 1) := by
  have := partner_eq j
  simp only [spine]
  omega

theorem partner_injective {i j : Nat} (h : partner i = partner j) : i = j := by
  have hi := partner_eq i
  have hj := partner_eq j
  apply spine_injective
  omega

theorem spine_ne_partner (i j : Nat) : spine i ≠ partner j := by
  have := spine_mod i
  have := partner_mod j
  omega

noncomputable def swap (t n : Nat) : Nat := by
  classical
  exact if h : ∃ j, t ≤ j ∧ n = spine j then partner (Classical.choose h)
    else if h : ∃ j, t ≤ j ∧ n = partner j then spine (Classical.choose h)
    else n

theorem swap_spine (t j : Nat) (hj : t ≤ j) : swap t (spine j) = partner j := by
  classical
  have h : ∃ k, t ≤ k ∧ spine j = spine k := ⟨j, hj, rfl⟩
  rw [swap, dif_pos h]
  have hk := (Classical.choose_spec h).2
  exact congrArg partner (spine_injective hk).symm

theorem swap_partner (t j : Nat) (hj : t ≤ j) : swap t (partner j) = spine j := by
  classical
  have hno : ¬ ∃ k, t ≤ k ∧ partner j = spine k := by
    rintro ⟨k, _, hk⟩
    exact spine_ne_partner k j hk.symm
  have h : ∃ k, t ≤ k ∧ partner j = partner k := ⟨j, hj, rfl⟩
  rw [swap, dif_neg hno, dif_pos h]
  exact congrArg spine (partner_injective (Classical.choose_spec h).2).symm

theorem swap_cases (t n : Nat) :
    (∃ j, t ≤ j ∧ n = spine j ∧ swap t n = partner j) ∨
    (∃ j, t ≤ j ∧ n = partner j ∧ swap t n = spine j) ∨ swap t n = n := by
  classical
  by_cases ha : ∃ j, t ≤ j ∧ n = spine j
  · obtain ⟨j, hj, rfl⟩ := ha
    exact Or.inl ⟨j, hj, rfl, swap_spine t j hj⟩
  · by_cases hb : ∃ j, t ≤ j ∧ n = partner j
    · obtain ⟨j, hj, rfl⟩ := hb
      exact Or.inr (Or.inl ⟨j, hj, rfl, swap_partner t j hj⟩)
    · exact Or.inr (Or.inr (by simp [swap, ha, hb]))

theorem swap_involutive (t n : Nat) : swap t (swap t n) = n := by
  rcases swap_cases t n with ⟨j, hj, rfl, hs⟩ | ⟨j, hj, rfl, hs⟩ | hs
  · rw [hs, swap_partner t j hj]
  · rw [hs, swap_spine t j hj]
  · rw [hs, hs]

theorem swap_parity (t n : Nat) : swap t n % 2 = n % 2 := by
  rcases swap_cases t n with ⟨j, _, rfl, hs⟩ | ⟨j, _, rfl, hs⟩ | hs
  · have := spine_mod j; have := partner_mod j; omega
  · have := spine_mod j; have := partner_mod j; omega
  · rw [hs]

theorem swap_even (t n : Nat) (hn : n % 2 = 0) : swap t n = n := by
  rcases swap_cases t n with ⟨j, _, rfl, _⟩ | ⟨j, _, rfl, _⟩ | hs
  · have := spine_mod j; omega
  · have := partner_mod j; omega
  · exact hs

theorem swap_below (t n : Nat) (hn : n < spine t) : swap t n = n := by
  rcases swap_cases t n with ⟨j, hj, rfl, _⟩ | ⟨j, hj, rfl, _⟩ | hs
  · have := spine_le hj; omega
  · have := spine_le hj; have := partner_between j; omega
  · exact hs

noncomputable def step (t n : Nat) : Nat := C (swap t n)

noncomputable def iter (t : Nat) : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iter t k (step t n)

theorem step_even (t n : Nat) (hn : n % 2 = 0) : step t n = n / 2 := by
  rw [step, swap_even t n hn]
  simp [C, show ¬ n % 2 = 1 by omega]

theorem step_odd (t n : Nat) (hn : n % 2 = 1) : step t n = 3 * swap t n + 1 := by
  have hp := swap_parity t n
  simp [step, C, show swap t n % 2 = 1 by omega]

theorem unchanged_below (t n : Nat) (hn : n < spine t) : step t n = C n := by
  rw [step, swap_below t n hn]

theorem step_spine (t j : Nat) (hj : t ≤ j) : step t (spine j) = 2 * spine (j + 1) := by
  have hm := partner_mod j
  have hp := partner_eq j
  rw [step, swap_spine t j hj]
  simp only [C, if_pos (show partner j % 2 = 1 by omega), spine]
  omega

theorem step_partner (t j : Nat) (hj : t ≤ j) : step t (partner j) = 4 ^ (3 * j + 8) := by
  have hm := spine_mod j
  rw [step, swap_partner t j hj]
  simp only [C, if_pos (show spine j % 2 = 1 by omega)]
  exact spine_power j

theorem iter_add (t : Nat) : ∀ k l n, iter t (k + l) n = iter t l (iter t k n)
  | 0, _, _ => by simp [iter]
  | k + 1, l, n => by
    rw [show k + 1 + l = (k + l) + 1 by omega]
    exact iter_add t k l (step t n)

theorem spine_two_steps (t j : Nat) (hj : t ≤ j) : iter t 2 (spine j) = spine (j + 1) := by
  simp only [iter, step_spine t j hj]
  rw [step_even t _ (by omega)]
  omega

theorem escape_even (t k : Nat) : iter t (2 * k) (spine t) = spine (t + k) := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, iter_add, ih]
    simpa [Nat.add_assoc] using spine_two_steps t (t + k) (by omega)

theorem escape_odd (t k : Nat) : iter t (2 * k + 1) (spine t) = 2 * spine (t + k + 1) := by
  rw [iter_add, escape_even]
  exact step_spine t (t + k) (by omega)

theorem escape_never_one (t k : Nat) : iter t k (spine t) ≠ 1 := by
  have hr := Nat.mod_lt k (by decide : 0 < 2)
  by_cases he : k % 2 = 0
  · have hk : k = 2 * (k / 2) := by omega
    rw [hk, escape_even]
    have := spine_lower (t + k / 2)
    omega
  · have hk : k = 2 * (k / 2) + 1 := by omega
    rw [hk, escape_odd]
    have := spine_lower (t + k / 2 + 1)
    omega

theorem differs_from_collatz (t : Nat) : step t (spine t) ≠ C (spine t) := by
  have hm := spine_mod t
  rw [step_spine t t (Nat.le_refl _)]
  simp only [C, if_pos (show spine t % 2 = 1 by omega), spine]
  omega

theorem known_cycle (t : Nat) : step t 1 = 4 ∧ step t 4 = 2 ∧ step t 2 = 1 := by
  have hh := spine_lower t
  rw [unchanged_below t 1 (by omega), unchanged_below t 4 (by omega),
    unchanged_below t 2 (by omega)]
  decide

theorem known_cycle_iterate (t k n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    iter t k n = 1 ∨ iter t k n = 2 ∨ iter t k n = 4 := by
  induction k generalizing n with
  | zero => exact hn
  | succ k ih =>
    apply ih
    have hc := known_cycle t
    rcases hn with rfl | rfl | rfl <;> omega

theorem hits_spine_never_one (t n l : Nat) (hn : iter t l n = spine t) :
    ∀ k, iter t k n ≠ 1 := by
  intro k hk
  by_cases hle : l ≤ k
  · have he : k = l + (k - l) := by omega
    rw [he, iter_add, hn] at hk
    exact escape_never_one t (k - l) hk
  · have he : l = k + (l - k) := by omega
    rw [he, iter_add, hk] at hn
    have hc := known_cycle_iterate t (l - k) 1 (Or.inl rfl)
    have hl := spine_lower t
    omega

theorem unchanged_prefix (t k n : Nat)
    (h : ∀ i, i < k → step t (OrdinaryCollatz.iterate i n) =
      C (OrdinaryCollatz.iterate i n)) :
    iter t k n = OrdinaryCollatz.iterate k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    have h0 := h 0 (by omega)
    simp only [OrdinaryCollatz.iterate] at h0
    simp only [iter, h0, OrdinaryCollatz.iterate]
    apply ih
    intro i hi
    exact h (i + 1) (by omega)

theorem predecessor_iff (t n a : Nat) :
    step t n = a ↔ n = 2 * a ∨ (a % 6 = 4 ∧ n = swap t ((a - 1) / 3)) := by
  constructor
  · intro h
    by_cases hn : n % 2 = 1
    · rw [step_odd t n hn] at h
      have hp := swap_parity t n
      have he : swap t n = (a - 1) / 3 := by omega
      have hh := congrArg (swap t) he
      rw [swap_involutive] at hh
      exact Or.inr ⟨by omega, hh⟩
    · rw [step_even t n (by omega)] at h
      exact Or.inl (by omega)
  · rintro (h | ⟨ha, h⟩)
    · subst n
      rw [step_even t _ (by omega)]
      omega
    · rw [h, step, swap_involutive]
      simp only [C, if_pos (show (a - 1) / 3 % 2 = 1 by omega)]
      omega

theorem multiple_three_parent (t n a : Nat) (ha : a % 3 = 0) :
    step t n = a ↔ n = 2 * a := by
  rw [predecessor_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact h
    · omega
  · exact Or.inl

theorem iter_doubling (t k a : Nat) : iter t k (2 ^ k * a) = a := by
  induction k with
  | zero => simp [iter]
  | succ k ih =>
    rw [Nat.pow_succ]
    rw [show 2 ^ k * 2 * a = 2 * (2 ^ k * a) by ac_rfl]
    simp only [iter]
    rw [step_even t _ (by omega)]
    have hh : 2 * (2 ^ k * a) / 2 = 2 ^ k * a := by omega
    rw [hh, ih]

theorem multiple_three_fibre (t k n a : Nat) (ha : a % 3 = 0) :
    iter t k n = a ↔ n = 2 ^ k * a := by
  constructor
  · induction k generalizing n with
    | zero => simp [iter]
    | succ k ih =>
      intro h
      have he := ih (step t n) h
      have hm : (2 ^ k * a) % 3 = 0 := by simp [Nat.mul_mod, ha]
      have hn := (multiple_three_parent t n (2 ^ k * a) hm).mp he
      rw [hn, Nat.pow_succ]
      ac_rfl
  · rintro rfl
    exact iter_doubling t k a

def OldTrap (n : Nat) : Prop :=
  (∃ e, n = 2 ^ e) ∨ (∃ j, n = spine j) ∨
  (∃ j, n = partner j) ∨ (∃ j, n = 2 * spine j)

theorem old_trap_closed {n : Nat} (h : OldTrap n) : OldTrap (C n) := by
  rcases h with ⟨e, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · cases e with
    | zero => exact Or.inl ⟨2, rfl⟩
    | succ e =>
      apply Or.inl
      refine ⟨e, ?_⟩
      rw [Nat.pow_succ]
      simp [C]
  · apply Or.inl
    refine ⟨2 * (3 * j + 8), ?_⟩
    have hm := spine_mod j
    simp only [C, if_pos (show spine j % 2 = 1 by omega)]
    rw [spine_power, Nat.pow_mul]
  · apply Or.inr; apply Or.inr; apply Or.inr
    refine ⟨j + 1, ?_⟩
    have hm := partner_mod j
    have hp := partner_eq j
    simp only [C, if_pos (show partner j % 2 = 1 by omega), spine]
    omega
  · apply Or.inr; apply Or.inl
    refine ⟨j, ?_⟩
    simp [C]

theorem old_trap_iterate (k n : Nat) (h : OldTrap n) : OldTrap (OrdinaryCollatz.iterate k n) := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih => exact ih (C n) (old_trap_closed h)

def Safe (c : Nat) : Prop := 1 < c ∧ c % 12 = 1

theorem safe_outside_trap {c : Nat} (hc : Safe c) : ¬ OldTrap c := by
  rcases hc with ⟨hc, hm⟩
  rintro (⟨e, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩)
  · cases e with
    | zero => simp at hc
    | succ e => rw [Nat.pow_succ] at hm; omega
  · have := spine_mod j; omega
  · have := partner_mod j; omega
  · omega

theorem swap_outside_trap (t n : Nat) (hn : ¬ OldTrap n) : swap t n = n := by
  rcases swap_cases t n with ⟨j, _, rfl, _⟩ | ⟨j, _, rfl, _⟩ | hs
  · exact False.elim (hn (Or.inr (Or.inl ⟨j, rfl⟩)))
  · exact False.elim (hn (Or.inr (Or.inr (Or.inl ⟨j, rfl⟩))))
  · exact hs

theorem unchanged_safe_basin (t k n c : Nat) (hc : Safe c)
    (h : OrdinaryCollatz.iterate k n = c) : iter t k n = c := by
  induction k generalizing n with
  | zero => exact h
  | succ k ih =>
    have hn : ¬ OldTrap n := by
      intro hh
      have hh' := old_trap_iterate (k + 1) n hh
      rw [h] at hh'
      exact safe_outside_trap hc hh'
    have he : step t n = C n := by rw [step, swap_outside_trap t n hn]
    simp only [iter, he]
    exact ih (C n) h

theorem safe_ancestor (a : Nat) (ha : 0 < a) (h3 : a % 3 ≠ 0) :
    ∃ e c, 6 ≤ e ∧ e ≤ 11 ∧ Safe c ∧ 3 * c + 1 = 2 ^ e * a := by
  have hr : a % 9 = 1 ∨ a % 9 = 2 ∨ a % 9 = 4 ∨ a % 9 = 5 ∨
      a % 9 = 7 ∨ a % 9 = 8 := by omega
  rcases hr with h | h | h | h | h | h
  · refine ⟨8, (256 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega
  · refine ⟨7, (128 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega
  · refine ⟨6, (64 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega
  · refine ⟨9, (512 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega
  · refine ⟨10, (1024 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega
  · refine ⟨11, (2048 * a - 1) / 3, by decide, by decide, ?_, ?_⟩ <;> (try unfold Safe) <;> omega

theorem inherited_unit_basin (t a : Nat) (ha : 0 < a) (h3 : a % 3 ≠ 0) :
    ∃ c, 0 < c ∧ c % 3 ≠ 0 ∧
      ∀ n k, OrdinaryCollatz.iterate k n = c → ∃ l, iter t l n = a := by
  obtain ⟨e, c, _, _, hc, he⟩ := safe_ancestor a ha h3
  refine ⟨c, by have := hc.1; omega, by have := hc.2; omega, ?_⟩
  intro n k hn
  have ht := unchanged_safe_basin t k n c hc hn
  have hs : step t c = 2 ^ e * a := by
    rw [step, swap_outside_trap t c (safe_outside_trap hc)]
    simp only [C, if_pos (show c % 2 = 1 by have := hc.2; omega)]
    exact he
  refine ⟨k + (e + 1), ?_⟩
  rw [iter_add, ht]
  simp only [iter, hs]
  exact iter_doubling t e a

#print axioms spine_power
#print axioms partner_between
#print axioms swap_involutive
#print axioms swap_parity
#print axioms unchanged_below
#print axioms step_spine
#print axioms step_partner
#print axioms escape_even
#print axioms escape_odd
#print axioms escape_never_one
#print axioms differs_from_collatz
#print axioms known_cycle
#print axioms hits_spine_never_one
#print axioms unchanged_prefix
#print axioms predecessor_iff
#print axioms multiple_three_fibre
#print axioms old_trap_closed
#print axioms unchanged_safe_basin
#print axioms safe_ancestor
#print axioms inherited_unit_basin
end SparseCollatzPerturbation
