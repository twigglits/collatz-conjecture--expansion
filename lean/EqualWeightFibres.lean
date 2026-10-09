/-
  Exact shifted envelopes and equal-weight coalescence fibres.
  Standalone Lean 4. Infinite correction bounds remain written analysis.
  No conclusion asserting universal coalescence growth or Collatz is made.
-/
import FinitePathPacking

namespace CollatzPacking

theorem weight_le_length : ∀ k n, wt k n ≤ k
  | 0, n => by simp [wt]
  | k + 1, n => by
    have h := weight_le_length k (U n)
    have hp := Nat.mod_lt n (by decide : 0 < 2)
    simp only [wt]
    omega

/-- Moving the affine origin to -1 makes odd steps exactly homogeneous. -/
theorem shifted_lower : ∀ k n,
    3 ^ wt k n * (n + 1) ≤ 2 ^ k * orbit k n + 2 ^ wt k n
  | 0, n => by simp [wt, orbit]
  | k + 1, n => by
    have h := Nat.mul_le_mul_left 2 (shifted_lower k (U n))
    have hp : 2 ^ wt k (U n) ≤ 3 ^ wt k (U n) :=
      Nat.pow_le_pow_left (by decide) _
    by_cases hn : n % 2 = 1
    · have hu : 2 * (U n + 1) = 3 * (n + 1) := by
        simp only [U, if_pos hn]
        omega
      have he : 2 * (3 ^ wt k (U n) * (U n + 1)) =
          3 ^ wt k (U n) * (2 * (U n + 1)) := by ac_rfl
      rw [he, hu] at h
      simpa only [wt, orbit, hn, Nat.pow_add, Nat.pow_one,
        Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using h
    · have hz : n % 2 = 0 := by omega
      have hu : 2 * (U n + 1) = n + 2 := by
        simp only [U, if_neg hn]
        omega
      have he : 2 * (3 ^ wt k (U n) * (U n + 1)) =
          3 ^ wt k (U n) * (2 * (U n + 1)) := by ac_rfl
      rw [he, hu] at h
      simp only [Nat.mul_add, Nat.mul_two] at h
      simp only [wt, orbit, hz, Nat.zero_add, Nat.pow_succ]
      have he' : 2 ^ k * 2 * orbit k (U n) = 2 * (2 ^ k * orbit k (U n)) := by ac_rfl
      rw [he']
      simp only [Nat.mul_add, Nat.mul_one]
      omega

/-- The upper error depends on the number of even steps, not the full length. -/
theorem shifted_upper : ∀ k n,
    2 ^ k * (orbit k n + 1) ≤ 3 ^ wt k n * (n + 2 ^ (k - wt k n))
  | 0, n => by simp [wt, orbit]
  | k + 1, n => by
    have h := Nat.mul_le_mul_left 2 (shifted_upper k (U n))
    have hw := weight_le_length k (U n)
    have hp : 1 ≤ 2 ^ (k - wt k (U n)) := Nat.one_le_two_pow
    have he : 2 * (3 ^ wt k (U n) * (U n + 2 ^ (k - wt k (U n)))) =
        3 ^ wt k (U n) * (2 * U n + 2 * 2 ^ (k - wt k (U n))) := by
      simp only [Nat.mul_add]
      ac_rfl
    rw [he] at h
    by_cases hn : n % 2 = 1
    · have hu : 2 * U n = 3 * n + 1 := by
        simp only [U, if_pos hn]
        omega
      rw [hu] at h
      have hb : 3 * n + 1 + 2 * 2 ^ (k - wt k (U n)) ≤
          3 * (n + 2 ^ (k - wt k (U n))) := by omega
      have hc := Nat.le_trans h (Nat.mul_le_mul_left (3 ^ wt k (U n)) hb)
      have hd : k + 1 - (1 + wt k (U n)) = k - wt k (U n) := by omega
      simpa only [wt, orbit, hn, hd, Nat.pow_add, Nat.pow_one,
        Nat.pow_succ, Nat.pow_zero, Nat.mul_one, Nat.one_mul,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
    · have hz : n % 2 = 0 := by omega
      have hu : 2 * U n = n := by
        simp only [U, if_neg hn]
        omega
      rw [hu] at h
      have hd : k + 1 - wt k (U n) = (k - wt k (U n)) + 1 := by omega
      simpa only [wt, orbit, hz, Nat.zero_add, hd, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem shifted_base_lower (k n : Nat) :
    3 ^ wt k n * (n + 1) ≤ 2 ^ k * (orbit k n + 1) := by
  have h := shifted_lower k n
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (weight_le_length k n)
  have hc := Nat.le_trans h (Nat.add_le_add_left hp (2 ^ k * orbit k n))
  simpa only [Nat.mul_add, Nat.mul_one] using hc

def EqualWeightMate (k n m : Nat) : Prop :=
  orbit k m = orbit k n ∧ wt k m = wt k n

instance (k n m : Nat) : Decidable (EqualWeightMate k n m) :=
  inferInstanceAs (Decidable (orbit k m = orbit k n ∧ wt k m = wt k n))

theorem mate_endpoint_cap {k n m : Nat} (h : EqualWeightMate k n m) :
    3 ^ wt k n * (m + 1) ≤ 2 ^ k * orbit k n + 2 ^ wt k n := by
  simpa only [h.1, h.2] using shifted_lower k m

/-- All sources in one fibre have pairwise separation below 2^(number of evens). -/
theorem fibre_span {k n m : Nat} (h : EqualWeightMate k n m) :
    m < n + 2 ^ (k - wt k n) := by
  have hl := shifted_base_lower k m
  have hu := shifted_upper k n
  rw [h.1, h.2] at hl
  have hc := Nat.le_trans hl hu
  have hpos : 0 < 3 ^ wt k n := Nat.pow_pos (by decide)
  have hb := Nat.le_of_mul_le_mul_left hc hpos
  omega

theorem list_has_minimum (a : Nat) (xs : List Nat) :
    ∃ m, m ∈ a :: xs ∧ ∀ x ∈ a :: xs, m ≤ x := by
  induction xs generalizing a with
  | nil =>
    refine ⟨a, by simp, ?_⟩
    intro x hx
    have he : x = a := by simpa using hx
    omega
  | cons b xs ih =>
    obtain ⟨m, hm, hmin⟩ := ih b
    by_cases ha : a ≤ m
    · refine ⟨a, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · omega
      · exact Nat.le_trans ha (hmin x h)
    · refine ⟨m, List.mem_cons.mpr (Or.inr hm), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with h | h
      · omega
      · exact hmin x h

theorem fibre_cardinality (k y j : Nat) (xs : List Nat) (hd : xs.Nodup)
    (hf : ∀ x ∈ xs, orbit k x = y ∧ wt k x = j) :
    xs.length ≤ 2 ^ (k - j) := by
  cases xs with
  | nil => simp
  | cons a xs =>
    obtain ⟨m, hm, hmin⟩ := list_has_minimum a xs
    apply finite_image_packing (a :: xs) (fun x => x - m) (2 ^ (k - j)) hd
    · intro x hx z hz he
      have h1 := hmin x hx
      have h2 := hmin z hz
      omega
    · intro x hx
      have hx' := hf x hx
      have hm' := hf m hm
      have he : EqualWeightMate k m x := ⟨hx'.1.trans hm'.1.symm, hx'.2.trans hm'.2.symm⟩
      have hs := fibre_span he
      rw [hm'.2] at hs
      have hmx := hmin x hx
      have hpos : 0 < 2 ^ (k - j) := Nat.pow_pos (by decide)
      omega

/-- With at most one even step, a same-time same-weight merge is impossible. -/
theorem one_even_injective {k n m : Nat} (h : EqualWeightMate k n m)
    (he : k - wt k n ≤ 1) : m = n := by
  have bound : ∀ a b, EqualWeightMate k a b → k - wt k a ≤ 1 → b ≤ a := by
    intro a b hab habs
    have hspan := fibre_span hab
    by_cases hz : k - wt k a = 0
    · rw [hz] at hspan
      simp only [Nat.pow_zero] at hspan
      omega
    · have hone : k - wt k a = 1 := by omega
      have hk : k = wt k a + 1 := by have := weight_le_length k a; omega
      have hl := shifted_lower k b
      have hu := shifted_upper k a
      rw [hab.1, hab.2] at hl
      rw [hone] at hu
      have hp : 0 < 2 ^ wt k a := Nat.pow_pos (by decide)
      have heq : 2 ^ k = 2 * 2 ^ wt k a := by
        calc
          2 ^ k = 2 ^ (wt k a + 1) := congrArg (fun z => 2 ^ z) hk
          _ = 2 * 2 ^ wt k a := by rw [Nat.pow_succ, Nat.mul_comm]
      have hlt : 3 ^ wt k a * (b + 1) < 3 ^ wt k a * (a + 2) := by
        simp only [Nat.pow_one, Nat.mul_add, Nat.mul_one] at hu
        rw [heq] at hl hu
        simp only [Nat.mul_add, Nat.mul_one, Nat.mul_two] at hl hu ⊢
        omega
      have hba := Nat.lt_of_mul_lt_mul_left hlt
      omega
  have h1 := bound n m h he
  have h2 := bound m n ⟨h.1.symm, h.2.symm⟩ (by simpa [h.2] using he)
  omega

theorem weight_add_right : ∀ k t n, wt (k + t) n = wt t n + wt k (orbit t n)
  | k, 0, n => by simp [wt, orbit]
  | k, t + 1, n => by
    change n % 2 + wt (k + t) (U n) =
      n % 2 + wt t (U n) + wt k (orbit t (U n))
    rw [weight_add_right k t (U n)]
    omega

theorem mate_persists {k n m : Nat} (h : EqualWeightMate k n m) (t : Nat) :
    EqualWeightMate (k + t) n m := by
  constructor
  · rw [Nat.add_comm k t, orbit_add, orbit_add, h.1]
  · rw [Nat.add_comm k t, weight_add_right, weight_add_right, h.1, h.2]

/-- A supplied uniform bound on the normalized endpoint bounds every mate. -/
theorem mates_bounded {n M : Nat}
    (hb : ∀ k, 2 ^ k * (orbit k n + 1) ≤ 3 ^ wt k n * (M + 1))
    {k m : Nat} (h : EqualWeightMate k n m) : m ≤ M := by
  have hl := shifted_base_lower k m
  rw [h.1, h.2] at hl
  have hc := Nat.le_trans hl (hb k)
  have hpos : 0 < 3 ^ wt k n := Nat.pow_pos (by decide)
  have hm := Nat.le_of_mul_le_mul_left hc hpos
  omega

/-- Any increasing family contained in a fixed finite interval stabilizes. -/
theorem finite_monotone_stabilizes (P : Nat → Nat → Prop) (M : Nat)
    (hmono : ∀ k t m, k ≤ t → P k m → P t m)
    (hbound : ∀ k m, P k m → m ≤ M) :
    ∃ K, ∀ t, K ≤ t → ∀ m, P t m ↔ P K m := by
  have capture : ∀ B, ∃ K, ∀ m, m ≤ B → (∃ t, P t m) → P K m := by
    intro B
    induction B with
    | zero =>
      by_cases h : ∃ t, P t 0
      · obtain ⟨t, ht⟩ := h
        refine ⟨t, ?_⟩
        intro m hm _
        have he : m = 0 := by omega
        simpa [he] using ht
      · refine ⟨0, ?_⟩
        intro m hm hx
        have he : m = 0 := by omega
        exact False.elim (h (by simpa [he] using hx))
    | succ B ih =>
      obtain ⟨K, hK⟩ := ih
      by_cases h : ∃ t, P t (B + 1)
      · obtain ⟨t, ht⟩ := h
        refine ⟨K + t, ?_⟩
        intro m hm hx
        by_cases hsmall : m ≤ B
        · exact hmono K (K + t) m (by omega) (hK m hsmall hx)
        · have he : m = B + 1 := by omega
          subst m
          exact hmono t (K + t) (B + 1) (by omega) ht
      · refine ⟨K, ?_⟩
        intro m hm hx
        by_cases hsmall : m ≤ B
        · exact hK m hsmall hx
        · have he : m = B + 1 := by omega
          exact False.elim (h (by simpa [he] using hx))
  obtain ⟨K, hK⟩ := capture M
  refine ⟨K, ?_⟩
  intro t ht m
  exact ⟨fun h => hK m (hbound t m h) ⟨t, h⟩, hmono K t m ht⟩

theorem mates_stabilize {n M : Nat}
    (hb : ∀ k, 2 ^ k * (orbit k n + 1) ≤ 3 ^ wt k n * (M + 1)) :
    ∃ K, ∀ t, K ≤ t → ∀ m, EqualWeightMate t n m ↔ EqualWeightMate K n m := by
  apply finite_monotone_stabilizes (fun k m => EqualWeightMate k n m) M
  · intro k t m hkt hm
    have h := mate_persists hm (t - k)
    simpa [Nat.add_sub_of_le hkt] using h
  · intro k m hm
    exact mates_bounded hb hm

def StandardCore (n : Nat) : Prop := n = 1 ∨ n = 2

instance (n : Nat) : Decidable (StandardCore n) :=
  inferInstanceAs (Decidable (n = 1 ∨ n = 2))

theorem core_closed (n : Nat) (hn : StandardCore n) : StandardCore (U n) := by
  rcases hn with h | h <;> subst n <;> decide

theorem core_injective (n m : Nat) (hn : StandardCore n) (hm : StandardCore m)
    (he : U n = U m) : n = m := by
  rcases hn with h | h <;> rcases hm with h' | h' <;>
    subst n <;> subst m <;> simp_all [U]

/-- Once both states lie in the standard cycle, later equality cannot
    conceal unequal earlier states or unequal accumulated odd counts. -/
theorem mate_after_core_iff {K n m : Nat}
    (hn : StandardCore (orbit K n)) (hm : StandardCore (orbit K m)) (t : Nat) :
    EqualWeightMate (K + t) n m ↔ EqualWeightMate K n m := by
  constructor
  · intro h
    have he := h.1
    rw [Nat.add_comm K t, orbit_add, orbit_add] at he
    have hstate := orbit_injective_on_forward_closed StandardCore core_closed core_injective
      t (orbit K m) (orbit K n) hm hn he
    have hw := h.2
    rw [Nat.add_comm K t, weight_add_right, weight_add_right, hstate] at hw
    exact ⟨hstate, by omega⟩
  · intro h
    exact mate_persists h t

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Complete finite fibres: a long plateau does not certify stabilization. -/
theorem one_fibre_34 (m : Nat) : EqualWeightMate 34 1 m ↔ m = 1 := by
  constructor
  · intro h
    have hc := mate_endpoint_cap h
    have hbase : orbit 34 1 = 1 ∧ wt 34 1 = 17 := by decide
    rw [hbase.1, hbase.2] at hc
    change 129140163 * (m + 1) ≤ 17180000256 at hc
    have hm : m < 133 := by omega
    have table : ∀ r : Fin 133, EqualWeightMate 34 1 r.val → r.val = 1 := by decide
    exact table ⟨m, hm⟩ h
  · intro h
    subst m
    exact ⟨rfl, rfl⟩

theorem one_fibre_35 (m : Nat) : EqualWeightMate 35 1 m ↔ m = 1 ∨ m = 159 := by
  constructor
  · intro h
    have hc := mate_endpoint_cap h
    have hbase : orbit 35 1 = 2 ∧ wt 35 1 = 18 := by decide
    rw [hbase.1, hbase.2] at hc
    change 387420489 * (m + 1) ≤ 68719738880 at hc
    have hm : m < 177 := by omega
    have table : ∀ r : Fin 177, EqualWeightMate 35 1 r.val →
        r.val = 1 ∨ r.val = 159 := by decide
    exact table ⟨m, hm⟩ h
  · intro h
    rcases h with h | h
    · subst m
      exact ⟨rfl, rfl⟩
    · subst m
      decide

theorem core_certificate_27 :
    StandardCore (orbit 72 27) ∧
    ∀ m : Fin 27, 0 < m.val →
      StandardCore (orbit 72 m.val) ∧ ¬ EqualWeightMate 72 27 m.val := by decide

/-- 27 converges but has no smaller equal-time equal-weight mate at any time. -/
theorem no_smaller_equal_weight_27 (m k : Nat) (hm : 0 < m) (hlt : m < 27) :
    ¬ EqualWeightMate k 27 m := by
  intro h
  have hc := core_certificate_27.2 ⟨m, hlt⟩ hm
  by_cases hk : k ≤ 72
  · have hp := mate_persists h (72 - k)
    exact hc.2 (by simpa [Nat.add_sub_of_le hk] using hp)
  · have hk' : 72 ≤ k := by omega
    have he : 72 + (k - 72) = k := Nat.add_sub_of_le hk'
    have hp := (mate_after_core_iff core_certificate_27.1 hc.1 (k - 72)).mp
      (by simpa [he] using h)
    exact hc.2 hp

theorem convergent_27 : orbit 70 27 = 1 := by decide

#print axioms shifted_lower
#print axioms shifted_upper
#print axioms fibre_span
#print axioms fibre_cardinality
#print axioms one_even_injective
#print axioms mate_persists
#print axioms mates_bounded
#print axioms mates_stabilize
#print axioms one_fibre_34
#print axioms one_fibre_35
#print axioms mate_after_core_iff
#print axioms no_smaller_equal_weight_27
#print axioms convergent_27

end CollatzPacking
