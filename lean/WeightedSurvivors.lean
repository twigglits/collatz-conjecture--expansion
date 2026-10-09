/-
  Exact arithmetic underlying fixed-floor weighted survivor counting.
  The infinite sums and their analytic estimates are written arguments in
  docs/WEIGHTED-SURVIVORS.md, not theorems in this standalone Lean module.
  No uniform mass contraction or Collatz proof is asserted here.
-/
import CollatzContradiction

namespace WeightedSurvivors

open OrdinaryCollatz

def Survives (H k n : Nat) : Prop :=
  ∀ j, j ≤ k → H < shortcutIter j n

theorem survives_succ (H k n : Nat) :
    Survives H (k + 1) n ↔ H < n ∧ Survives H k (U n) := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), fun j hj => h (j + 1) (by omega)⟩
  · rintro ⟨hn, h⟩ j hj
    cases j with
    | zero => exact hn
    | succ j => exact h j (by omega)

theorem shortcut_positive {n : Nat} (hn : 0 < n) : 0 < U n := by
  unfold U
  split <;> omega

/-- Both inverse branches, including the exact ternary eligibility test. -/
theorem predecessor_iff (n y : Nat) (hn : 0 < n) (hy : 0 < y) :
    U n = y ↔ n = 2 * y ∨ (y % 3 = 2 ∧ n = (2 * y - 1) / 3) := by
  unfold U
  split <;> omega

/-- The cutoff on the odd source is essential to killed transport. -/
theorem odd_source_above (H y : Nat) (hy : y % 3 = 2) :
    H < (2 * y - 1) / 3 ↔ 3 * H + 1 < 2 * y := by omega

theorem killed_predecessor_iff (H k n y : Nat) (hy : H < y) :
    (U n = y ∧ Survives H (k + 1) n) ↔
    (Survives H k y ∧
      (n = 2 * y ∨
        (y % 3 = 2 ∧ 3 * H + 1 < 2 * y ∧ n = (2 * y - 1) / 3))) := by
  rw [survives_succ]
  constructor
  · rintro ⟨he, hn, hs⟩
    rw [he] at hs
    refine ⟨hs, ?_⟩
    rcases (predecessor_iff n y (by omega) (by omega)).mp he with heven | ⟨hr, ho⟩
    · exact Or.inl heven
    · exact Or.inr ⟨hr, (odd_source_above H y hr).mp (by omega), ho⟩
  · rintro ⟨hs, heven | ⟨hr, hc, ho⟩⟩
    · have hn : H < n := by omega
      have he := (predecessor_iff n y (by omega) (by omega)).mpr (Or.inl heven)
      exact ⟨he, hn, by simpa [he] using hs⟩
    · have hn : H < n := by
        have := (odd_source_above H y hr).mpr hc
        omega
      have he := (predecessor_iff n y (by omega) (by omega)).mpr (Or.inr ⟨hr, ho⟩)
      exact ⟨he, hn, by simpa [he] using hs⟩

def predecessors (y : Nat) : List Nat :=
  [2 * y] ++ if y % 3 = 2 then [(2 * y - 1) / 3] else []

theorem mem_predecessors (n y : Nat) (hy : 0 < y) :
    n ∈ predecessors y ↔ 0 < n ∧ U n = y := by
  have hp : 0 < (2 * y - 1) / 3 ∨ y % 3 ≠ 2 := by omega
  by_cases hr : y % 3 = 2
  · simp only [predecessors, hr, if_true, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · intro hn
      have hnpos : 0 < n := by rcases hn with h | h <;> omega
      exact ⟨hnpos, (predecessor_iff n y hnpos hy).mpr (by omega)⟩
    · rintro ⟨hn, he⟩
      have := (predecessor_iff n y hn hy).mp he
      omega
  · simp only [predecessors, hr, if_false, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · intro hn
      have hnpos : 0 < n := by omega
      exact ⟨hnpos, (predecessor_iff n y hnpos hy).mpr (Or.inl hn)⟩
    · rintro ⟨hn, he⟩
      have := (predecessor_iff n y hn hy).mp he
      omega

/-- A finite list presentation of every start absorbed by depth k.
    Duplicates are harmless; the Python replay uses a set and a BFS frontier. -/
def cone (H : Nat) : Nat → List Nat
  | 0 => (List.range H).map Nat.succ
  | k + 1 => cone H 0 ++ (cone H k).flatMap predecessors

theorem mem_cone_zero (H n : Nat) : n ∈ cone H 0 ↔ 0 < n ∧ n ≤ H := by
  simp only [cone, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, he⟩
    omega
  · rintro ⟨hn, hH⟩
    exact ⟨n - 1, by omega, by omega⟩

theorem mem_cone (H k n : Nat) :
    n ∈ cone H k ↔ 0 < n ∧ ∃ j, j ≤ k ∧ shortcutIter j n ≤ H := by
  induction k generalizing n with
  | zero =>
    rw [mem_cone_zero]
    simp [shortcutIter]
  | succ k ih =>
    simp only [cone, List.mem_append, List.mem_flatMap]
    constructor
    · intro h
      rcases h with h | ⟨y, hy, hn⟩
      · obtain ⟨hn, hh⟩ := (mem_cone_zero H n).mp (by simpa only [cone] using h)
        exact ⟨hn, 0, by omega, hh⟩
      · obtain ⟨hyp, j, hj, hh⟩ := (ih y).mp hy
        obtain ⟨hnp, he⟩ := (mem_predecessors n y hyp).mp hn
        exact ⟨hnp, j + 1, by omega, by simpa [shortcutIter, he] using hh⟩
    · rintro ⟨hn, j, hj, hh⟩
      cases j with
      | zero =>
        exact Or.inl (by simpa only [cone] using (mem_cone_zero H n).mpr ⟨hn, hh⟩)
      | succ j =>
        have hup := shortcut_positive hn
        exact Or.inr ⟨U n, (ih (U n)).mpr ⟨hup, j, by omega, hh⟩,
          (mem_predecessors n (U n) hup).mpr ⟨hn, rfl⟩⟩

theorem survives_iff_not_mem_cone (H k n : Nat) (hn : 0 < n) :
    Survives H k n ↔ n ∉ cone H k := by
  rw [mem_cone]
  unfold Survives
  constructor
  · intro hs h
    obtain ⟨_, j, hj, hh⟩ := h
    have := hs j hj
    omega
  · intro h j hj
    apply Classical.byContradiction
    intro hbad
    exact h ⟨hn, j, hj, by omega⟩

theorem iter_lower_bound (k n : Nat) : n ≤ 2 ^ k * shortcutIter k n := by
  induction k generalizing n with
  | zero => simp [shortcutIter]
  | succ k ih =>
    have hstep : n ≤ 2 * U n := by unfold U; split <;> omega
    have ht := Nat.mul_le_mul_left 2 (ih (U n))
    exact Nat.le_trans hstep (by
      simpa [shortcutIter, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using ht)

theorem cone_bound (H k n : Nat) (hn : n ∈ cone H k) : n ≤ 2 ^ k * H := by
  obtain ⟨_, j, hj, hh⟩ := (mem_cone H k n).mp hn
  exact Nat.le_trans (iter_lower_bound j n)
    (Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hj) hh)

/-- The infinite unenumerated tail is known to survive at every fixed depth. -/
theorem large_survives (H k n : Nat) (hn : 2 ^ k * H < n) : Survives H k n := by
  apply (survives_iff_not_mem_cone H k n (by omega)).mpr
  intro h
  have := cone_bound H k n h
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem base64 : ∀ n : Fin 65, 0 < n.val →
    ∃ j : Fin 72, shortcutIter j.val n.val = 1 := by decide

theorem conjecture_of_absorption (H : Nat)
    (hbase : ∀ n, 0 < n → n ≤ H → ReachesOne n)
    (habs : ∀ n, 0 < n → ∃ k, ¬ Survives H k n) : Conjecture := by
  intro n hn
  obtain ⟨k, hk⟩ := habs n hn
  have hm : n ∈ cone H k := by
    apply Classical.byContradiction
    intro hnot
    exact hk ((survives_iff_not_mem_cone H k n hn).mpr hnot)
  obtain ⟨_, j, _, hj⟩ := (mem_cone H k n).mp hm
  obtain ⟨t, _, _, ht⟩ := shortcut_iteration_simulation j n
  have hp : 0 < shortcutIter j n := by
    rw [← ht]
    exact iterate_positive t n hn
  exact reaches_of_iterate (n := n) (k := t) (by
    rw [ht]
    exact hbase _ hp hj)

theorem conjecture_iff_absorption64 : Conjecture ↔
    (∀ n, 0 < n → ∃ k, ¬ Survives 64 k n) := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := shortcut_reaches_of_ordinary (hc n hn)
    refine ⟨k, ?_⟩
    intro hs
    have := hs k (by omega)
    omega
  · apply conjecture_of_absorption 64
    intro n hn h64
    obtain ⟨j, hj⟩ := base64 ⟨n, by omega⟩ hn
    exact ordinary_reaches_of_shortcut hj

/-- Squared rational upper bounds used for the written 3/2-power estimate. -/
theorem contraction_arithmetic :
    500 ^ 2 < 8 * 177 ^ 2 ∧
    250 ^ 2 * 98 ^ 3 < 463 ^ 2 * 65 ^ 3 ∧
    1000 * (177 * 100 + 69 * 463) < 993 * 50000 := by decide

#print axioms survives_succ
#print axioms predecessor_iff
#print axioms killed_predecessor_iff
#print axioms mem_cone
#print axioms survives_iff_not_mem_cone
#print axioms cone_bound
#print axioms large_survives
#print axioms base64
#print axioms conjecture_iff_absorption64
#print axioms contraction_arithmetic

end WeightedSurvivors
