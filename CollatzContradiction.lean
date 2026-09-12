/-
  Ordinary positive-integer Collatz: exact contradiction reductions.
  Check: lean CollatzContradiction.lean
  Standalone Lean 4; no Mathlib, sorry, native_decide, or added axioms.
  This file does NOT prove the Collatz conjecture.
-/

namespace OrdinaryCollatz

/-- The ordinary map, exactly `T 3 1` from CollatzTheory.lean. -/
def C (n : Nat) : Nat := if n % 2 = 1 then 3 * n + 1 else n / 2

/-- The same iteration convention as `iterN` in CollatzTheory.lean. -/
def iterate : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate k (C n)

def ReachesOne (n : Nat) : Prop := ∃ k, iterate k n = 1

def Conjecture : Prop := ∀ n, 0 < n → ReachesOne n

/-- Descent has no uniform bound on the number of steps. -/
def Descent : Prop := ∀ n, 1 < n → ∃ k, iterate k n < n

def LeastCounterexample (n : Nat) : Prop :=
  0 < n ∧ ¬ ReachesOne n ∧ ∀ m, 0 < m → m < n → ReachesOne m

theorem C_positive {n : Nat} (hn : 0 < n) : 0 < C n := by
  unfold C
  split <;> omega

theorem iterate_positive : ∀ k n, 0 < n → 0 < iterate k n
  | 0, _, hn => hn
  | k + 1, n, hn => iterate_positive k (C n) (C_positive hn)

theorem iterate_add : ∀ k j n, iterate (k + j) n = iterate j (iterate k n)
  | 0, j, n => by simp [iterate]
  | k + 1, j, n => by
    have h : k + 1 + j = (k + j) + 1 := by omega
    rw [h]
    exact iterate_add k j (C n)

theorem reaches_one : ReachesOne 1 := ⟨0, rfl⟩

/-- Reaching a convergent orbit proves convergence of the original start. -/
theorem reaches_of_iterate {n k : Nat} (h : ReachesOne (iterate k n)) :
    ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨k + j, by rw [iterate_add]; exact hj⟩

/-- Contradiction/strong-induction reduction, with no assumption on bounds. -/
theorem conjecture_iff_descent : Conjecture ↔ Descent := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := hc n (by omega)
    exact ⟨k, by omega⟩
  · intro hd n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · rw [h1]; exact reaches_one
      · obtain ⟨k, hk⟩ := hd n (by omega)
        exact reaches_of_iterate (ih (iterate k n) hk (iterate_positive k n hn))

/-- Well-ordering supplies a least positive counterexample if one exists. -/
theorem least_counterexample_exists (h : ¬ Conjecture) :
    ∃ n, LeastCounterexample n := by
  classical
  have hex : ∃ n, 0 < n ∧ ¬ ReachesOne n := by
    apply Classical.byContradiction
    intro hno
    apply h
    intro n hn
    apply Classical.byContradiction
    intro hbad
    exact hno ⟨n, hn, hbad⟩
  obtain ⟨n, hn, hbad⟩ := hex
  have key : ∀ b, 0 < b → ¬ ReachesOne b → ∃ m, LeastCounterexample m := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb hbadb
      by_cases he : ∃ m, 0 < m ∧ m < b ∧ ¬ ReachesOne m
      · obtain ⟨m, hm, hmb, hbadm⟩ := he
        exact ih m hmb hm hbadm
      · refine ⟨b, hb, hbadb, ?_⟩
        intro m hm hmb
        apply Classical.byContradiction
        intro hbadm
        exact he ⟨m, hm, hmb, hbadm⟩
  exact key n hn hbad

theorem least_gt_one {n : Nat} (h : LeastCounterexample n) : 1 < n := by
  by_cases hn : n = 1
  · exact False.elim (h.2.1 (by rw [hn]; exact reaches_one))
  · have := h.1; omega

/-- Every forward iterate of a least counterexample stays at least its start. -/
theorem least_orbit_lower_bound {n : Nat} (h : LeastCounterexample n) (k : Nat) :
    n ≤ iterate k n := by
  apply Classical.byContradiction
  intro hlt
  exact h.2.1 (reaches_of_iterate
    (h.2.2 (iterate k n) (iterate_positive k n h.1) (by omega)))

/-- Convergence is preserved by a step, including steps after the first visit to 1. -/
theorem reaches_after_step {n : Nat} (h : ReachesOne n) : ReachesOne (C n) := by
  obtain ⟨k, hk⟩ := h
  cases k with
  | zero =>
    have hn : n = 1 := hk
    rw [hn]
    exact ⟨2, rfl⟩
  | succ k => exact ⟨k, hk⟩

theorem reaches_after_iterate : ∀ k n, ReachesOne n → ReachesOne (iterate k n)
  | 0, _, h => h
  | k + 1, n, h => reaches_after_iterate k (C n) (reaches_after_step h)

/-- Any smaller positive predecessor of a least counterexample is impossible. -/
theorem least_has_no_smaller_predecessor {n m k : Nat}
    (h : LeastCounterexample n) (hm : 0 < m) (hlt : m < n)
    (hp : iterate k m = n) : False := by
  have hc := reaches_after_iterate k m (h.2.2 m hm hlt)
  rw [hp] at hc
  exact h.2.1 hc

/-- Every positive even start immediately descends. -/
theorem even_descent {n : Nat} (hn : 0 < n) (he : n % 2 = 0) : iterate 1 n < n := by
  show C n < n
  unfold C
  rw [if_neg (by omega : ¬ n % 2 = 1)]
  omega

/-- An exact infinite-family path: 4q+1 reaches 3q+1 in three ordinary steps. -/
theorem path_mod4 (q : Nat) : iterate 3 (4 * q + 1) = 3 * q + 1 := by
  have h0 : C (4 * q + 1) = 12 * q + 4 := by unfold C; split <;> omega
  have h1 : C (12 * q + 4) = 6 * q + 2 := by unfold C; split <;> omega
  have h2 : C (6 * q + 2) = 3 * q + 1 := by unfold C; split <;> omega
  simp only [iterate, h0, h1, h2]

/-- Every start congruent to 1 modulo 4, except 1 itself, descends. -/
theorem mod4_descent {n : Nat} (hn : 1 < n) (hr : n % 4 = 1) : iterate 3 n < n := by
  have heq : n = 4 * (n / 4) + 1 := by omega
  rw [heq, path_mod4]
  omega

/-- A least counterexample must be 3 modulo 4. -/
theorem least_mod4 {n : Nat} (h : LeastCounterexample n) : n % 4 = 3 := by
  have hodd : n % 2 = 1 := by
    have hlow := least_orbit_lower_bound h 1
    by_cases he : n % 2 = 0
    · have := even_descent h.1 he; omega
    · omega
  have hnot1 : ¬ n % 4 = 1 := by
    intro hr
    have := mod4_descent (least_gt_one h) hr
    have := least_orbit_lower_bound h 3
    omega
  omega

/-- Another exact infinite-family path, now covering residue 3 modulo 16. -/
theorem path_mod16 (q : Nat) : iterate 6 (16 * q + 3) = 9 * q + 2 := by
  have h0 : C (16 * q + 3) = 48 * q + 10 := by unfold C; split <;> omega
  have h1 : C (48 * q + 10) = 24 * q + 5 := by unfold C; split <;> omega
  have h2 : C (24 * q + 5) = 72 * q + 16 := by unfold C; split <;> omega
  have h3 : C (72 * q + 16) = 36 * q + 8 := by unfold C; split <;> omega
  have h4 : C (36 * q + 8) = 18 * q + 4 := by unfold C; split <;> omega
  have h5 : C (18 * q + 4) = 9 * q + 2 := by unfold C; split <;> omega
  simp only [iterate, h0, h1, h2, h3, h4, h5]

theorem mod16_descent {n : Nat} (hr : n % 16 = 3) : iterate 6 n < n := by
  have heq : n = 16 * (n / 16) + 3 := by omega
  rw [heq, path_mod16]
  omega

theorem least_mod16 {n : Nat} (h : LeastCounterexample n) :
    n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by
  have hr := least_mod4 h
  have hnot3 : ¬ n % 16 = 3 := by
    intro hr3
    have := mod16_descent hr3
    have := least_orbit_lower_bound h 6
    omega
  omega

/-- Every 6q+5 has the smaller positive predecessor 4q+3. -/
theorem smaller_predecessor_path (q : Nat) : iterate 2 (4 * q + 3) = 6 * q + 5 := by
  have h0 : C (4 * q + 3) = 12 * q + 10 := by unfold C; split <;> omega
  have h1 : C (12 * q + 10) = 6 * q + 5 := by unfold C; split <;> omega
  simp only [iterate, h0, h1]

/-- A backward argument excludes 2 modulo 3 from least counterexamples. -/
theorem least_not_two_mod3 {n : Nat} (h : LeastCounterexample n) : n % 3 ≠ 2 := by
  intro hr
  have hm4 := least_mod4 h
  have heq : n = 6 * (n / 6) + 5 := by omega
  have hp : iterate 2 (4 * (n / 6) + 3) = n := by
    rw [smaller_predecessor_path]
    omega
  exact least_has_no_smaller_predecessor h (by omega) (by omega) hp

/-- Forward and backward restrictions combined into six residues modulo 48. -/
theorem least_mod48 {n : Nat} (h : LeastCounterexample n) :
    n % 48 = 7 ∨ n % 48 = 15 ∨ n % 48 = 27 ∨
    n % 48 = 31 ∨ n % 48 = 39 ∨ n % 48 = 43 := by
  have h16 := least_mod16 h
  have h3 := least_not_two_mod3 h
  omega

/-- The exact remaining contradiction target; the restrictions alone are consistent. -/
theorem counterexample_constraints (h : ¬ Conjecture) :
    ∃ n, LeastCounterexample n ∧ 1 < n ∧
      (∀ k, n ≤ iterate k n) ∧
      (n % 48 = 7 ∨ n % 48 = 15 ∨ n % 48 = 27 ∨
       n % 48 = 31 ∨ n % 48 = 39 ∨ n % 48 = 43) := by
  obtain ⟨n, hn⟩ := least_counterexample_exists h
  exact ⟨n, hn, least_gt_one hn, least_orbit_lower_bound hn, least_mod48 hn⟩

/-- It suffices, and is necessary, to prove descent on these six residue classes.
    This is still an infinite universal statement, not a finite certificate. -/
theorem conjecture_iff_restricted_descent : Conjecture ↔
    (∀ n, 1 < n →
      (n % 48 = 7 ∨ n % 48 = 15 ∨ n % 48 = 27 ∨
       n % 48 = 31 ∨ n % 48 = 39 ∨ n % 48 = 43) →
      ∃ k, iterate k n < n) := by
  constructor
  · intro hc n hn _
    exact conjecture_iff_descent.mp hc n hn
  · intro hd
    apply Classical.byContradiction
    intro hbad
    obtain ⟨n, hn⟩ := least_counterexample_exists hbad
    obtain ⟨k, hk⟩ := hd n (least_gt_one hn) (least_mod48 hn)
    have := least_orbit_lower_bound hn k
    omega

/-- The shortcut map is exactly `U` from CollatzFrontier.lean. -/
def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def shortcutIter : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => shortcutIter k (U n)

/-- A shortcut step consists of one or two ordinary steps. -/
theorem shortcut_step_simulation (n : Nat) :
    ∃ j, 1 ≤ j ∧ j ≤ 2 ∧ iterate j n = U n := by
  by_cases hn : n % 2 = 1
  · refine ⟨2, by omega, by omega, ?_⟩
    have he : (3 * n + 1) % 2 ≠ 1 := by omega
    simp only [iterate, C, U, if_pos hn, if_neg he]
  · exact ⟨1, by omega, by omega, by simp only [iterate, C, U, if_neg hn]⟩

/-- All shortcut computations are genuine ordinary orbits, with a rigorous step bound. -/
theorem shortcut_iteration_simulation : ∀ k n,
    ∃ j, k ≤ j ∧ j ≤ 2 * k ∧ iterate j n = shortcutIter k n
  | 0, n => ⟨0, by omega, by omega, rfl⟩
  | k + 1, n => by
    obtain ⟨j, hj1, hj2, he⟩ := shortcut_step_simulation n
    obtain ⟨l, hl1, hl2, htail⟩ := shortcut_iteration_simulation k (U n)
    refine ⟨j + l, by omega, by omega, ?_⟩
    rw [iterate_add, he, htail]
    rfl

/-- A shortcut hitting certificate certifies convergence of the ordinary map. -/
theorem ordinary_reaches_of_shortcut {n k : Nat} (hk : shortcutIter k n = 1) :
    ReachesOne n := by
  obtain ⟨j, _, _, hj⟩ := shortcut_iteration_simulation k n
  exact ⟨j, by rw [hj, hk]⟩

/-- Conversely, every ordinary hitting certificate yields a shortcut hitting certificate. -/
theorem shortcut_reaches_of_ordinary {n : Nat} (h : ReachesOne n) :
    ∃ k, shortcutIter k n = 1 := by
  have key : ∀ k n, iterate k n = 1 → ∃ j, shortcutIter j n = 1 := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n hk
      cases k with
      | zero => exact ⟨0, hk⟩
      | succ k =>
        by_cases hn : n % 2 = 1
        · cases k with
          | zero =>
            have hc : C n = 3 * n + 1 := by simp only [C, if_pos hn]
            change C n = 1 at hk
            omega
          | succ l =>
            have he : (3 * n + 1) % 2 ≠ 1 := by omega
            have hstep : C (C n) = U n := by
              simp only [C, U, if_pos hn, if_neg he]
            change iterate l (C (C n)) = 1 at hk
            rw [hstep] at hk
            obtain ⟨j, hj⟩ := ih l (by omega) (U n) hk
            exact ⟨j + 1, hj⟩
        · have hstep : C n = U n := by simp only [C, U, if_neg hn]
          change iterate k (C n) = 1 at hk
          rw [hstep] at hk
          obtain ⟨j, hj⟩ := ih k (by omega) (U n) hk
          exact ⟨j + 1, hj⟩
  obtain ⟨k, hk⟩ := h
  exact key k n hk

/-- Ordinary and shortcut convergence are equivalent for every natural start. -/
theorem reaches_iff_shortcut (n : Nat) :
    ReachesOne n ↔ ∃ k, shortcutIter k n = 1 := by
  constructor
  · exact shortcut_reaches_of_ordinary
  · intro h
    obtain ⟨k, hk⟩ := h
    exact ordinary_reaches_of_shortcut hk

/-- A shortcut descent certificate also certifies an ordinary descent. -/
theorem ordinary_descent_of_shortcut {n k : Nat} (hk : shortcutIter k n < n) :
    ∃ j, iterate j n < n := by
  obtain ⟨j, _, _, hj⟩ := shortcut_iteration_simulation k n
  exact ⟨j, by rw [hj]; exact hk⟩

/-- Exact all-positive reduction directly usable with shortcut descent searches. -/
theorem conjecture_iff_shortcut_descent : Conjecture ↔
    (∀ n, 1 < n → ∃ k, shortcutIter k n < n) := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := shortcut_reaches_of_ordinary (hc n (by omega))
    exact ⟨k, by omega⟩
  · intro hd
    apply conjecture_iff_descent.mpr
    intro n hn
    obtain ⟨k, hk⟩ := hd n hn
    exact ordinary_descent_of_shortcut hk

/-- Hence a least ordinary counterexample cannot descend under the shortcut map either. -/
theorem least_shortcut_lower_bound {n : Nat} (h : LeastCounterexample n) (k : Nat) :
    n ≤ shortcutIter k n := by
  obtain ⟨j, _, _, hj⟩ := shortcut_iteration_simulation k n
  rw [← hj]
  exact least_orbit_lower_bound h j

#print axioms conjecture_iff_descent
#print axioms least_counterexample_exists
#print axioms least_orbit_lower_bound
#print axioms least_has_no_smaller_predecessor
#print axioms least_mod48
#print axioms counterexample_constraints
#print axioms conjecture_iff_restricted_descent
#print axioms shortcut_iteration_simulation
#print axioms ordinary_reaches_of_shortcut
#print axioms reaches_iff_shortcut
#print axioms conjecture_iff_shortcut_descent
#print axioms least_shortcut_lower_bound

end OrdinaryCollatz
