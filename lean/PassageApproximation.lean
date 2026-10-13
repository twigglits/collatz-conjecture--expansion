/-
  Exact first-passage comparison for arbitrary target sets under the
  ordinary Collatz map. The passage mark is noncomputable: no decision
  procedure for eventual entry or convergence is claimed.
  Analytic uniform-density limits remain written, not kernel theorems.
-/
import CollatzContradiction

namespace PassageApproximation

open OrdinaryCollatz

def Reaches (n a : Nat) : Prop := ∃ k, iterate k n = a

def FirstEntry (P : Nat → Prop) (t n : Nat) : Prop :=
  P (iterate t n) ∧ ∀ j, j < t → ¬ P (iterate j n)

theorem first_entry_exists (P : Nat → Prop) (n : Nat)
    (he : ∃ t, P (iterate t n)) : ∃ t, FirstEntry P t n := by
  classical
  have minimal : ∀ k, P (iterate k n) → ∃ t, FirstEntry P t n := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      by_cases hsmall : ∃ j, j < k ∧ P (iterate j n)
      · obtain ⟨j, hj, hp⟩ := hsmall
        exact ih j hj hp
      · exact ⟨k, hk, fun j hj hp => hsmall ⟨j, hj, hp⟩⟩
  obtain ⟨k, hk⟩ := he
  exact minimal k hk

theorem first_entry_unique {P : Nat → Prop} {n t u : Nat}
    (ht : FirstEntry P t n) (hu : FirstEntry P u n) : t = u := by
  by_cases htu : t < u
  · exact False.elim (hu.2 t htu ht.1)
  · by_cases hut : u < t
    · exact False.elim (ht.2 u hut hu.1)
    · omega

noncomputable def mark (P : Nat → Prop) (n : Nat) : Option Nat := by
  classical
  exact if h : ∃ t, FirstEntry P t n then
    some (iterate (Classical.choose h) n) else none

theorem mark_none_iff (P : Nat → Prop) (n : Nat) :
    mark P n = none ↔ ∀ t, ¬ P (iterate t n) := by
  classical
  unfold mark
  split
  · rename_i h
    constructor
    · intro he
      cases he
    · intro hn
      exact False.elim (hn (Classical.choose h) (Classical.choose_spec h).1)
  · rename_i h
    constructor
    · intro _ t ht
      exact h (first_entry_exists P n ⟨t, ht⟩)
    · intro _
      rfl

theorem mark_some_iff (P : Nat → Prop) (n b : Nat) :
    mark P n = some b ↔ ∃ t, FirstEntry P t n ∧ iterate t n = b := by
  classical
  unfold mark
  split
  · rename_i h
    constructor
    · intro he
      exact ⟨Classical.choose h, Classical.choose_spec h, Option.some.inj he⟩
    · rintro ⟨t, ht, hb⟩
      have he := first_entry_unique (Classical.choose_spec h) ht
      rw [he, hb]
  · rename_i h
    constructor
    · intro he
      cases he
    · rintro ⟨t, ht, _⟩
      exact False.elim (h ⟨t, ht⟩)

theorem reaches_trans {n b a : Nat} (hb : Reaches n b) (ha : Reaches b a) :
    Reaches n a := by
  obtain ⟨i, hi⟩ := hb
  obtain ⟨j, hj⟩ := ha
  exact ⟨i + j, by rw [iterate_add, hi, hj]⟩

theorem first_entry_suffix {P : Nat → Prop} {t k n a : Nat}
    (ht : FirstEntry P t n) (hk : k ≤ t) (ha : iterate k n = a) :
    FirstEntry P (t - k) a := by
  have terminal : iterate (t - k) a = iterate t n := by
    rw [← ha, ← iterate_add, Nat.add_sub_of_le hk]
  refine ⟨by rw [terminal]; exact ht.1, ?_⟩
  intro j hj hp
  have hs : iterate j a = iterate (k + j) n := by rw [iterate_add, ha]
  rw [hs] at hp
  exact ht.2 (k + j) (by omega) hp

theorem never_after_reach {P : Nat → Prop} {n a : Nat}
    (hn : mark P n = none) (ha : Reaches n a) : mark P a = none := by
  apply (mark_none_iff P a).mpr
  obtain ⟨k, hk⟩ := ha
  intro j hj
  have hnj := (mark_none_iff P n).mp hn (k + j)
  apply hnj
  simpa only [iterate_add, hk] using hj

def LandingReaches (P : Nat → Prop) (n a : Nat) : Prop :=
  ∃ b, mark P n = some b ∧ Reaches b a

theorem landing_reaches_subset {P : Nat → Prop} {n a : Nat}
    (h : LandingReaches P n a) : Reaches n a := by
  obtain ⟨b, hb, ha⟩ := h
  obtain ⟨t, _, ht⟩ := (mark_some_iff P n b).mp hb
  exact reaches_trans ⟨t, ht⟩ ha

/-- A hit occurs either after the landing, or in the single class having
    the same passage mark as the target. The latter includes nonentry. -/
theorem passage_comparison {P : Nat → Prop} {n a : Nat}
    (ha : Reaches n a) : LandingReaches P n a ∨ mark P n = mark P a := by
  cases hm : mark P n with
  | none =>
    exact Or.inr (never_after_reach hm ha).symm
  | some b =>
    obtain ⟨t, ht, hb⟩ := (mark_some_iff P n b).mp hm
    obtain ⟨k, hk⟩ := ha
    by_cases htk : t ≤ k
    · refine Or.inl ⟨b, hm, k - t, ?_⟩
      calc
        iterate (k - t) b = iterate (k - t) (iterate t n) := by rw [hb]
        _ = iterate (t + (k - t)) n := (iterate_add t (k - t) n).symm
        _ = iterate k n := by rw [Nat.add_sub_of_le htk]
        _ = a := hk
    · have hkt : k ≤ t := by omega
      have hs := first_entry_suffix ht hkt hk
      have hland : iterate (t - k) a = b := by
        rw [← hk, ← iterate_add, Nat.add_sub_of_le hkt]
        exact hb
      have ham : mark P a = some b := (mark_some_iff P a b).mpr ⟨t - k, hs, hland⟩
      exact Or.inr ham.symm

theorem early_hit_same_mark {P : Nat → Prop} {n a : Nat}
    (ha : Reaches n a) (hl : ¬ LandingReaches P n a) : mark P n = mark P a := by
  rcases passage_comparison ha with h | h
  · exact False.elim (hl h)
  · exact h

/-- Odd states at most H give exactly the Syracuse passage location after
    removal of initial powers of two, interpreted as an ordinary first hit. -/
def OddFloor (H n : Nat) : Prop := n % 2 = 1 ∧ n ≤ H

theorem odd_floor_comparison (H n a : Nat) (ha : Reaches n a) :
    LandingReaches (OddFloor H) n a ∨
      mark (OddFloor H) n = mark (OddFloor H) a := passage_comparison ha

#print axioms first_entry_exists
#print axioms first_entry_unique
#print axioms mark_none_iff
#print axioms mark_some_iff
#print axioms reaches_trans
#print axioms first_entry_suffix
#print axioms never_after_reach
#print axioms landing_reaches_subset
#print axioms passage_comparison
#print axioms early_hit_same_mark
#print axioms odd_floor_comparison

end PassageApproximation
