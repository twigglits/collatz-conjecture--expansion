/-
  Cardinality of bounded-time fibres for the shortcut Collatz map.
  The limiting first-passage laws and inverse-basin density conclusions
  remain written analysis. No native evaluation or admitted proofs.
-/
import WeightedSurvivors
import CollatzPacking

namespace BoundedHitFibres

open OrdinaryCollatz WeightedSurvivors

/-- A list covering exactly the positive starts hitting a by time k.
    Repeated entries are retained; cardinality claims count distinct starts. -/
def hitCone (a : Nat) : Nat → List Nat
  | 0 => [a]
  | k + 1 => [a] ++ (hitCone a k).flatMap predecessors

theorem mem_hitCone (a k n : Nat) (ha : 0 < a) :
    n ∈ hitCone a k ↔
      0 < n ∧ ∃ j, j ≤ k ∧ shortcutIter j n = a := by
  induction k generalizing n with
  | zero =>
    simp only [hitCone, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · intro h
      subst n
      exact ⟨ha, 0, by omega, rfl⟩
    · rintro ⟨_, j, hj, he⟩
      have hz : j = 0 := by omega
      subst j
      exact he
  | succ k ih =>
    simp only [hitCone, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | ⟨y, hy, hn⟩
      · subst n
        exact ⟨ha, 0, by omega, rfl⟩
      · obtain ⟨hyp, j, hj, he⟩ := (ih y).mp hy
        obtain ⟨hnp, hu⟩ := (mem_predecessors n y hyp).mp hn
        exact ⟨hnp, j + 1, by omega, by simpa [shortcutIter, hu] using he⟩
    · rintro ⟨hn, j, hj, he⟩
      cases j with
      | zero => exact Or.inl he
      | succ j =>
        have hup := shortcut_positive hn
        exact Or.inr ⟨U n, (ih (U n)).mpr ⟨hup, j, by omega, he⟩,
          (mem_predecessors n (U n) hup).mpr ⟨hn, rfl⟩⟩

theorem predecessor_length (a : Nat) : (predecessors a).length ≤ 2 := by
  unfold predecessors
  split <;> simp

theorem flat_predecessor_length (xs : List Nat) :
    (xs.flatMap predecessors).length ≤ 2 * xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := predecessor_length x
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

theorem hitCone_length (a k : Nat) :
    (hitCone a k).length + 1 ≤ 2 ^ (k + 1) := by
  induction k with
  | zero => simp [hitCone]
  | succ k ih =>
    have hf := flat_predecessor_length (hitCone a k)
    simp only [hitCone, List.length_append, List.length_cons, List.length_nil]
    rw [Nat.pow_succ]
    omega

/-- The bound has no factor depending on the target's magnitude. -/
theorem distinct_bounded_hit_count (a k : Nat) (sources : List Nat)
    (ha : 0 < a) (hd : sources.Nodup)
    (hs : ∀ n ∈ sources, 0 < n ∧ ∃ j, j ≤ k ∧ shortcutIter j n = a) :
    sources.length + 1 ≤ 2 ^ (k + 1) := by
  have hsub : ∀ n ∈ sources, n ∈ hitCone a k := by
    intro n hn
    exact (mem_hitCone a k n ha).mpr (hs n hn)
  have hlen := CollatzPacking.nodup_length_le_of_subset hd hsub
  have hbound := hitCone_length a k
  omega

def FirstHit (a k n : Nat) : Prop :=
  shortcutIter k n = a ∧ ∀ j, j < k → shortcutIter j n ≠ a

theorem first_hit_unique {a k l n : Nat}
    (hk : FirstHit a k n) (hl : FirstHit a l n) : k = l := by
  by_cases hkl : k < l
  · exact False.elim (hl.2 k hkl hk.1)
  · by_cases hlk : l < k
    · exact False.elim (hk.2 l hlk hl.1)
    · omega

theorem first_hit_succ (a k n : Nat) :
    FirstHit a (k + 1) n ↔ n ≠ a ∧ FirstHit a k (U n) := by
  constructor
  · intro h
    refine ⟨h.2 0 (by omega), h.1, ?_⟩
    intro j hj
    exact h.2 (j + 1) (by omega)
  · rintro ⟨hne, he, hpre⟩
    refine ⟨he, ?_⟩
    intro j hj
    cases j with
    | zero => exact hne
    | succ j => exact hpre j (by omega)

/-- The following basin statements use the ordinary Collatz map C. -/
def Basin (a n : Nat) : Prop := ∃ k, iterate k n = a

def Nonperiodic (a : Nat) : Prop := ∀ k, 0 < k → iterate k a ≠ a

theorem ordinary_iterate_succ (k n : Nat) :
    iterate (k + 1) n = C (iterate k n) := by
  rw [iterate_add]
  rfl

theorem nonperiodic_hit_time_unique {a n i j : Nat}
    (ha : Nonperiodic a) (hi : iterate i n = a) (hj : iterate j n = a) :
    i = j := by
  have ordered : ∀ u v, u ≤ v → iterate u n = a → iterate v n = a → u = v := by
    intro u v huv hu hv
    by_cases he : u = v
    · exact he
    · have hp : 0 < v - u := by omega
      have hreturn : iterate (v - u) a = a := by
        rw [← hu, ← iterate_add, Nat.add_sub_of_le huv]
        exact hv.trans hu.symm
      exact False.elim (ha (v - u) hp hreturn)
  by_cases hij : i ≤ j
  · exact ordered i j hij hi hj
  · exact (ordered j i (by omega) hj hi).symm

/-- Distinct immediate predecessor basins can overlap at a periodic root.
    The nonperiodicity hypothesis is essential. -/
theorem predecessor_basins_disjoint {a p q n : Nat}
    (ha : Nonperiodic a) (hp : C p = a) (hq : C q = a) (hne : p ≠ q) :
    ¬ (Basin p n ∧ Basin q n) := by
  rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  have hia : iterate (i + 1) n = a := by rw [ordinary_iterate_succ, hi, hp]
  have hja : iterate (j + 1) n = a := by rw [ordinary_iterate_succ, hj, hq]
  have ht := nonperiodic_hit_time_unique ha hia hja
  have hij : i = j := by omega
  subst j
  exact hne (hi.symm.trans hj)

theorem ordinary_predecessor_iff (n a : Nat) (hn : 0 < n) (ha : 0 < a) :
    C n = a ↔ n = 2 * a ∨ (a % 6 = 4 ∧ n = (a - 1) / 3) := by
  unfold C
  split <;> omega

theorem basin_one_step (a n : Nat) :
    Basin a n ↔ n = a ∨ ∃ p, C p = a ∧ Basin p n := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => exact Or.inl hk
    | succ k =>
      exact Or.inr ⟨iterate k n, by simpa [ordinary_iterate_succ] using hk, k, rfl⟩
  · rintro (he | ⟨p, hp, k, hk⟩)
    · exact ⟨0, he⟩
    · exact ⟨k + 1, by rw [ordinary_iterate_succ, hk, hp]⟩

#print axioms mem_hitCone
#print axioms predecessor_length
#print axioms flat_predecessor_length
#print axioms hitCone_length
#print axioms distinct_bounded_hit_count
#print axioms first_hit_unique
#print axioms first_hit_succ
#print axioms ordinary_iterate_succ
#print axioms nonperiodic_hit_time_unique
#print axioms predecessor_basins_disjoint
#print axioms ordinary_predecessor_iff
#print axioms basin_one_step

end BoundedHitFibres
