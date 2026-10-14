/-
  A defect must be counted when its parent is in the known basin.
  The harmonic divergence and infinite Green sums remain written in
  docs/KNOWN-BASIN-NONFUSION-TRACE.md. No universal convergence claim.
-/
import DyadicCoalescenceDefects

namespace KnownBasinNonfusionTrace
open CollatzPacking DyadicCoalescenceDefects

def Known (n : Nat) : Prop := ∃ g, HasGrade n g

def DefectiveParent (n : Nat) : Prop :=
  Known n ∧ ¬ ∃ t, EqualWeightMate t (2 * n) (2 * n + 1)

def BinaryChild (n m : Nat) : Prop := m = 2 * n ∨ m = 2 * n + 1

def MarkedEdge (n m : Nat) : Prop := m = 2 * n + 1 ∧ DefectiveParent n

theorem known_double {n : Nat} (h : Known n) : Known (2 * n) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g + 1, grade_double hg⟩

theorem same_grade_mate {n m : Nat} {g : Int}
    (hn : HasGrade n g) (hm : HasGrade m g) :
    ∃ t, EqualWeightMate t n m := by
  obtain ⟨s, hs, hsg⟩ := hn
  obtain ⟨t, ht, htg⟩ := hm
  apply (equal_weight_iff_arrival_grade hs ht).mpr
  omega

/-- An unmarked step from a known parent is balanced, even when the
    other child's basin membership has not been decided. -/
theorem unmarked_known_step {n m : Nat} (hn : Known n)
    (hc : BinaryChild n m) (hu : ¬ MarkedEdge n m) : SafeChild n m := by
  rcases hc with he | he
  · exact Or.inl he
  · apply Or.inr
    refine ⟨he, ?_⟩
    by_cases hm : ∃ t, EqualWeightMate t (2 * n) (2 * n + 1)
    · exact hm
    · exact False.elim (hu ⟨he, hn, hm⟩)

/-- After a known visit, an entire unmarked finite binary tail stays
    balanced and carries exactly the inherited arrival grade. -/
theorem unmarked_known_chain (v : Nat → Nat) (g : Int)
    (h0 : HasGrade (v 0) g) (k : Nat)
    (hc : ∀ j < k, BinaryChild (v j) (v (j + 1)))
    (hu : ∀ j < k, ¬ MarkedEdge (v j) (v (j + 1))) :
    HasGrade (v k) (g + k) ∧
      ∀ j < k, SafeChild (v j) (v (j + 1)) := by
  induction k with
  | zero => exact ⟨by simpa using h0, by omega⟩
  | succ k ih =>
    have hp := ih (fun j hj => hc j (by omega)) (fun j hj => hu j (by omega))
    have hs := unmarked_known_step ⟨g + k, hp.1⟩ (hc k (by omega)) (hu k (by omega))
    constructor
    · have hg := safe_child_grade hp.1 hs
      simpa only [Int.natCast_add, Int.natCast_one, Int.add_assoc] using hg
    · intro j hj
      by_cases h : j < k
      · exact hp.2 j h
      · have he : j = k := by omega
        simpa only [he] using hs

theorem defect_even_known {n : Nat} (h : DefectiveParent n) : Known (2 * n) :=
  known_double h.1

theorem defect_never_fused {n : Nat} (h : DefectiveParent n) (t : Nat) :
    ¬ EqualWeightMate t (2 * n) (2 * n + 1) := by
  intro ht
  exact h.2 ⟨t, ht⟩

/-- This finite grade test requires that both displayed arrivals are
    given. The definition of a defective parent does not require that. -/
theorem grade_detects_defect {n : Nat} {g h : Int}
    (hn : HasGrade n g) (hc : HasGrade (2 * n + 1) h) :
    DefectiveParent n ↔ h ≠ g + 1 := by
  constructor
  · intro hd he
    apply hd.2
    rw [he] at hc
    exact same_grade_mate (grade_double hn) hc
  · intro he
    refine ⟨⟨g, hn⟩, ?_⟩
    intro hm
    have hg := grade_transfer (grade_double hn) hm
    exact he (grade_unique hc hg)

/-- The linear, unsquared cycle coefficient has ratio 3/4. -/
def greenNumerator : Nat → Nat
  | 0 => 0
  | j + 1 => 4 ^ j + 3 * greenNumerator j

theorem linear_green_identity (j : Nat) :
    greenNumerator j + 3 ^ j = 4 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [greenNumerator, Nat.pow_succ]
    omega

#print axioms known_double
#print axioms same_grade_mate
#print axioms unmarked_known_step
#print axioms unmarked_known_chain
#print axioms defect_even_known
#print axioms defect_never_fused
#print axioms grade_detects_defect
#print axioms linear_green_identity

end KnownBasinNonfusionTrace
