/-
  Exact clock transfer through first odd passage for ordinary Collatz.
  MinimumBy records an attained global minimum, which need not be one.
  Probabilistic mixing, logarithms, and asymptotic density remain written
  analysis; this module does not prove Collatz.
-/
import CollatzContradiction

namespace ClockedMinimum
open OrdinaryCollatz

def MinimumAt (n t : Nat) : Prop := ∀ j, iterate t n ≤ iterate j n

def MinimumBy (n T : Nat) : Prop := ∃ t, t ≤ T ∧ MinimumAt n t

def FirstMinimumAt (n t : Nat) : Prop :=
  MinimumAt n t ∧ ∀ j, j < t → ¬ MinimumAt n j

def RecordEntry (n t : Nat) : Prop :=
  ∀ j, j < t → iterate t n < iterate j n

def FirstOddBelow (H n t : Nat) : Prop :=
  iterate t n % 2 = 1 ∧ iterate t n ≤ H ∧
    ∀ j, j < t → ¬ (iterate j n % 2 = 1 ∧ iterate j n ≤ H)

theorem minimum_exists (n : Nat) : ∃ t, MinimumAt n t := by
  classical
  have least : ∀ b, (∃ t, iterate t n = b) → ∃ t, MinimumAt n t := by
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih =>
      intro hb
      by_cases lower : ∃ c, c < b ∧ ∃ t, iterate t n = c
      · obtain ⟨c, hc, ht⟩ := lower
        exact ih c hc ht
      · obtain ⟨t, ht⟩ := hb
        refine ⟨t, ?_⟩
        intro j
        rw [ht]
        apply Classical.byContradiction
        intro h
        exact lower ⟨iterate j n, by omega, j, rfl⟩
  exact least n ⟨0, rfl⟩

theorem minimum_by_exists (n : Nat) : ∃ T, MinimumBy n T := by
  obtain ⟨t, ht⟩ := minimum_exists n
  exact ⟨t, t, by omega, ht⟩

theorem minimum_by_mono {n S T : Nat} (h : MinimumBy n S) (hst : S ≤ T) :
    MinimumBy n T := by
  obtain ⟨t, ht, hm⟩ := h
  exact ⟨t, by omega, hm⟩

theorem finite_population_minimum_clock (N : Nat) :
    ∃ T, ∀ n, n ≤ N → MinimumBy n T := by
  induction N with
  | zero =>
    obtain ⟨T, ht⟩ := minimum_by_exists 0
    refine ⟨T, ?_⟩
    intro n hn
    have he : n = 0 := by omega
    subst n
    exact ht
  | succ N ih =>
    obtain ⟨T, ht⟩ := ih
    obtain ⟨S, hs⟩ := minimum_by_exists (N + 1)
    refine ⟨T + S, ?_⟩
    intro n hn
    by_cases he : n = N + 1
    · subst n
      exact minimum_by_mono hs (by omega)
    · exact minimum_by_mono (ht n (by omega)) (by omega)

theorem first_odd_below_record {H n t : Nat} (hn : 0 < n)
    (he : FirstOddBelow H n t) : RecordEntry n t := by
  induction t generalizing n with
  | zero => intro j hj; omega
  | succ t ih =>
    have hs : FirstOddBelow H (C n) t := by
      refine ⟨he.1, he.2.1, ?_⟩
      intro j hj
      exact he.2.2 (j + 1) (by omega)
    have hr := ih (C_positive hn) hs
    have hle : iterate t (C n) ≤ C n := by
      cases t with
      | zero => exact Nat.le_refl _
      | succ t => exact Nat.le_of_lt (hr 0 (by omega))
    have hlt : iterate t (C n) < n := by
      by_cases ho : n % 2 = 1
      · have hno := he.2.2 0 (by omega)
        have hb := he.2.1
        simp only [iterate] at hno hb
        omega
      · have hd : C n < n := by unfold C; rw [if_neg ho]; omega
        omega
    intro j hj
    cases j with
    | zero => exact hlt
    | succ j => exact hr j (by omega)

theorem minimum_after_record {n i t : Nat} (hi : RecordEntry n i)
    (ht : MinimumAt n t) : i ≤ t := by
  apply Classical.byContradiction
  intro h
  have hl := hi t (by omega)
  have hu := ht i
  omega

theorem record_minimum_at {n i t : Nat} (hi : RecordEntry n i)
    (ht : MinimumAt (iterate i n) t) : MinimumAt n (i + t) := by
  intro j
  rw [iterate_add]
  by_cases hj : j < i
  · have h0 := ht 0
    have hp := hi j hj
    change iterate t (iterate i n) ≤ iterate i n at h0
    omega
  · have he : iterate j n = iterate (j - i) (iterate i n) := by
      rw [← iterate_add, Nat.add_sub_of_le (by omega : i ≤ j)]
    rw [he]
    exact ht (j - i)

theorem record_minimum_by {n i T : Nat} (hi : RecordEntry n i)
    (ht : MinimumBy (iterate i n) T) : MinimumBy n (i + T) := by
  obtain ⟨t, ht, hm⟩ := ht
  exact ⟨i + t, by omega, record_minimum_at hi hm⟩

theorem record_minimum_suffix {n i t : Nat} (hi : RecordEntry n i)
    (ht : MinimumAt n t) : MinimumAt (iterate i n) (t - i) := by
  have hit := minimum_after_record hi ht
  intro j
  rw [← iterate_add, Nat.add_sub_of_le hit, ← iterate_add]
  exact ht (i + j)

theorem first_minimum_unique {n s t : Nat}
    (hs : FirstMinimumAt n s) (ht : FirstMinimumAt n t) : s = t := by
  by_cases hst : s < t
  · exact False.elim (ht.2 s hst hs.1)
  · by_cases hts : t < s
    · exact False.elim (hs.2 t hts ht.1)
    · omega

theorem record_first_minimum {n i t : Nat} (hi : RecordEntry n i)
    (ht : FirstMinimumAt (iterate i n) t) : FirstMinimumAt n (i + t) := by
  refine ⟨record_minimum_at hi ht.1, ?_⟩
  intro j hj hmin
  have hij := minimum_after_record hi hmin
  exact ht.2 (j - i) (by omega) (record_minimum_suffix hi hmin)

theorem record_first_minimum_suffix {n i t : Nat} (hi : RecordEntry n i)
    (ht : FirstMinimumAt n t) : FirstMinimumAt (iterate i n) (t - i) := by
  refine ⟨record_minimum_suffix hi ht.1, ?_⟩
  intro j hj hmin
  have hit := minimum_after_record hi ht.1
  exact ht.2 (i + j) (by omega) (record_minimum_at hi hmin)

theorem coupled_first_minimum_clocks {n m i j s t : Nat}
    (hn : RecordEntry n i) (hm : RecordEntry m j)
    (he : iterate i n = iterate j m)
    (hs : FirstMinimumAt n s) (ht : FirstMinimumAt m t) : s + j = t + i := by
  have hns := record_first_minimum_suffix hn hs
  have hmt := record_first_minimum_suffix hm ht
  rw [he] at hns
  have hd := first_minimum_unique hns hmt
  have his := minimum_after_record hn hs.1
  have hjt := minimum_after_record hm ht.1
  omega

theorem coupled_record_minimum_by {n m i j T : Nat}
    (hn : RecordEntry n i) (hm : RecordEntry m j)
    (he : iterate i n = iterate j m) (ht : MinimumBy m T) :
    MinimumBy n (i + T) := by
  obtain ⟨t, ht, hmin⟩ := ht
  have hs := record_minimum_suffix hm hmin
  apply record_minimum_by hn
  rw [he]
  exact ⟨t - j, by omega, hs⟩

theorem coupled_first_odd_below_minimum_by {H n m i j T L : Nat}
    (hn : 0 < n) (hm : 0 < m)
    (hni : FirstOddBelow H n i) (hmj : FirstOddBelow H m j)
    (he : iterate i n = iterate j m) (hi : i ≤ L)
    (ht : MinimumBy m T) : MinimumBy n (L + T) := by
  exact minimum_by_mono
    (coupled_record_minimum_by (first_odd_below_record hn hni)
      (first_odd_below_record hm hmj) he ht) (by omega)

theorem minimum_by_of_hit_one {n T t : Nat} (hn : 0 < n)
    (ht : t ≤ T) (he : iterate t n = 1) : MinimumBy n T := by
  refine ⟨t, ht, ?_⟩
  intro j
  rw [he]
  exact iterate_positive j n hn

theorem minimum_by_iff_hit_one {n T : Nat} (hn : 0 < n)
    (hc : ReachesOne n) :
    MinimumBy n T ↔ ∃ t, t ≤ T ∧ iterate t n = 1 := by
  constructor
  · rintro ⟨t, ht, hmin⟩
    obtain ⟨j, hj⟩ := hc
    have hle := hmin j
    have hp := iterate_positive t n hn
    rw [hj] at hle
    exact ⟨t, ht, by omega⟩
  · rintro ⟨t, ht, he⟩
    exact minimum_by_of_hit_one hn ht he

theorem target_before_or_after {n a i : Nat} (he : ∃ t, iterate t n = a) :
    (∃ t, t ≤ i ∧ iterate t n = a) ∨
      (∃ t, iterate t (iterate i n) = a) := by
  obtain ⟨t, ht⟩ := he
  by_cases hti : t ≤ i
  · exact Or.inl ⟨t, hti, ht⟩
  · right
    refine ⟨t - i, ?_⟩
    rw [← iterate_add, Nat.add_sub_of_le (by omega : i ≤ t)]
    exact ht

/-- A Chernoff factor for Geom(2) sums at the threshold 201/100. -/
theorem geometric_chernoff_comparison :
    101 ^ 100 * 201 ^ 201 < 100 ^ 100 * 202 ^ 201 := by decide

/-- Four positive terms in the usual log(2) series exceed 693/1000. -/
theorem log_two_partial_sum_comparison : 693 * 76545 < 1000 * 53056 := by decide

/-- Combined with the written logarithm bound, this budgets 435 log n. -/
theorem clock_coefficient_comparison : 301000000 < 435 * 693 * 1001 := by decide

theorem ordinary_clock_budget (steps valuation n0 : Nat)
    (ht : steps ≤ n0) (hs : 100 * valuation ≤ 201 * n0) :
    100 * (steps + valuation) ≤ 301 * n0 := by omega

#print axioms minimum_exists
#print axioms minimum_by_exists
#print axioms minimum_by_mono
#print axioms finite_population_minimum_clock
#print axioms first_odd_below_record
#print axioms minimum_after_record
#print axioms record_minimum_at
#print axioms record_minimum_by
#print axioms record_minimum_suffix
#print axioms first_minimum_unique
#print axioms record_first_minimum
#print axioms record_first_minimum_suffix
#print axioms coupled_first_minimum_clocks
#print axioms coupled_record_minimum_by
#print axioms coupled_first_odd_below_minimum_by
#print axioms minimum_by_of_hit_one
#print axioms minimum_by_iff_hit_one
#print axioms target_before_or_after
#print axioms geometric_chernoff_comparison
#print axioms log_two_partial_sum_comparison
#print axioms clock_coefficient_comparison
#print axioms ordinary_clock_budget
end ClockedMinimum
