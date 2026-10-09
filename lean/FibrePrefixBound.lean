/-
  A parity-prefix counting bound for every same-time, same-weight fibre.
  Standalone Lean 4. Analytic exponential estimates remain written.
  No universal descent, survivor contraction, or Collatz theorem is asserted.
-/
import EqualWeightFibres

namespace CollatzPacking

/-- A positive even count improves the earlier strict width by one. -/
theorem fibre_span_sharp {k n m : Nat} (h : EqualWeightMate k n m)
    (he : 0 < k - wt k n) : m + 1 < n + 2 ^ (k - wt k n) := by
  have hl := shifted_lower k m
  have hu := shifted_upper k n
  rw [h.1, h.2] at hl
  have hp : 2 ^ wt k n < 2 ^ k :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  have hh : 3 ^ wt k n * (m + 1) <
      3 ^ wt k n * (n + 2 ^ (k - wt k n)) := by
    simp only [Nat.mul_add, Nat.mul_one] at hl hu ⊢
    omega
  exact Nat.lt_of_mul_lt_mul_left hh

/-- Leaf count for the actual spacing cutoff. Both branches lower e-a. -/
def fibrePrefixBound (e a : Nat) : Nat :=
  if _h : 3 ^ a + 1 < 2 ^ e then
    fibrePrefixBound (e - 1) a + fibrePrefixBound e (a + 1)
  else 1
termination_by e - a
decreasing_by
  all_goals
    have ha : a < e := by
      by_cases hn : a < e
      · exact hn
      · have h1 : 2 ^ e ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) _
        omega
    omega

theorem fibrePrefixBound_pos (e a : Nat) : 0 < fibrePrefixBound e a := by
  rw [fibrePrefixBound]
  split
  · exact Nat.add_pos_left (fibrePrefixBound_pos (e - 1) a) _
  · decide
termination_by e - a
decreasing_by
  have ha : a < e := by
    by_cases hn : a < e
    · exact hn
    · have h1 : 2 ^ e ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ a ≤ 3 ^ a := Nat.pow_le_pow_left (by decide) _
      omega
  omega

theorem pow_three_odd (a : Nat) : 3 ^ a % 2 = 1 := by
  rw [Nat.pow_mod]
  simp

/-- The image of either parity part of an odd-spaced grid is another grid. -/
theorem grid_step (a r x : Nat) :
    U (3 ^ a * x + r) =
      if (3 ^ a * x + r) % 2 = 1 then
        3 ^ (a + 1) * (x / 2) + (3 * (3 ^ a * (x % 2) + r) + 1) / 2
      else 3 ^ a * (x / 2) + (3 ^ a * (x % 2) + r) / 2 := by
  have hx : x = 2 * (x / 2) + x % 2 := by omega
  have hm : 3 ^ a * x + r =
      2 * (3 ^ a * (x / 2)) + (3 ^ a * (x % 2) + r) := by
    calc
      3 ^ a * x + r = 3 ^ a * (2 * (x / 2) + x % 2) + r :=
        congrArg (fun z => 3 ^ a * z + r) hx
      _ = _ := by simp only [Nat.mul_add]; ac_rfl
  unfold U
  split <;> rename_i h
  · rw [hm, Nat.pow_succ]
    have hh : 3 * (2 * (3 ^ a * (x / 2)) + (3 ^ a * (x % 2) + r)) + 1 =
        2 * (3 ^ a * 3 * (x / 2)) + (3 * (3 ^ a * (x % 2) + r) + 1) := by
      simp only [Nat.mul_add]
      ac_rfl
    rw [hh]
    omega
  · rw [hm]
    omega

theorem grid_parity (a r x : Nat) :
    (3 ^ a * x + r) % 2 = (x % 2 + r % 2) % 2 := by
  rw [Nat.add_mod, Nat.mul_mod, pow_three_odd, Nat.one_mul, Nat.mod_mod]

def parityHalves (xs : List Nat) (b : Nat) : List Nat :=
  (xs.filter (fun x => decide (x % 2 = b))).map (fun x => x / 2)

theorem mem_parityHalves {xs : List Nat} {b z : Nat} :
    z ∈ parityHalves xs b ↔ ∃ x ∈ xs, x % 2 = b ∧ x / 2 = z := by
  simp only [parityHalves, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, ⟨hx, hb⟩, he⟩
    exact ⟨x, hx, hb, he⟩
  · rintro ⟨x, hx, hb, he⟩
    exact ⟨x, ⟨hx, hb⟩, he⟩

theorem parityHalves_nodup {xs : List Nat} (hd : xs.Nodup) (b : Nat) :
    (parityHalves xs b).Nodup := by
  apply List.pairwise_map.mpr
  have hfilter := List.Pairwise.filter (fun x => decide (x % 2 = b)) hd
  exact List.Pairwise.imp_of_mem (fun hx hz hne he => by
    have h1 : _ % 2 = b := of_decide_eq_true (List.mem_filter.mp hx).2
    have h2 : _ % 2 = b := of_decide_eq_true (List.mem_filter.mp hz).2
    apply hne
    omega) hfilter

theorem parityHalves_lengths (xs : List Nat) :
    (parityHalves xs 0).length + (parityHalves xs 1).length = xs.length := by
  simp only [parityHalves, List.length_map]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hp := Nat.mod_lt x (by decide : 0 < 2)
    by_cases h : x % 2 = 0
    · simp [h]
      omega
    · have ho : x % 2 = 1 := by omega
      simp [ho]
      omega

/-- When grid spacing exceeds the possible fibre diameter, only one remains. -/
theorem grid_fibre_singleton (k y j a r : Nat) (xs : List Nat) (hd : xs.Nodup)
    (hf : ∀ x ∈ xs, orbit k (3 ^ a * x + r) = y ∧ wt k (3 ^ a * x + r) = j)
    (hc : 2 ^ (k - j) ≤ 3 ^ a + 1) : xs.length ≤ 1 := by
  have le : ∀ x ∈ xs, ∀ z ∈ xs, z ≤ x := by
    intro x hx z hz
    have fx := hf x hx
    have fz := hf z hz
    have hm : EqualWeightMate k (3 ^ a * x + r) (3 ^ a * z + r) :=
      ⟨fz.1.trans fx.1.symm, fz.2.trans fx.2.symm⟩
    by_cases he : k - j = 0
    · have hh := one_even_injective hm (by rw [fx.2, he]; decide)
      have heq : 3 ^ a * z = 3 ^ a * x := by omega
      exact Nat.le_of_mul_le_mul_left (Nat.le_of_eq heq) (Nat.pow_pos (by decide))
    · have hs := fibre_span_sharp hm (by rw [fx.2]; omega)
      rw [fx.2] at hs
      have hmul : 3 ^ a * z < 3 ^ a * (x + 1) := by
        simp only [Nat.mul_add, Nat.mul_one]
        omega
      have hh := Nat.lt_of_mul_lt_mul_left hmul
      omega
  apply finite_image_packing xs (fun _ => 0) 1 hd
  · intro x hx z hz _
    have h1 := le x hx z hz
    have h2 := le z hz x hx
    omega
  · intros; decide

/-- All finite fibres on any grid of spacing 3^a satisfy the recurrence. -/
theorem grid_fibre_cardinality : ∀ k y j a r (xs : List Nat), xs.Nodup →
    (∀ x ∈ xs, orbit k (3 ^ a * x + r) = y ∧ wt k (3 ^ a * x + r) = j) →
    xs.length ≤ fibrePrefixBound (k - j) a
  | k, y, j, a, r, xs, hd, hf => by
    by_cases hc : 2 ^ (k - j) ≤ 3 ^ a + 1
    · have hs := grid_fibre_singleton k y j a r xs hd hf hc
      have hp := fibrePrefixBound_pos (k - j) a
      omega
    · have hsplit : 3 ^ a + 1 < 2 ^ (k - j) := by omega
      have hepos : 0 < k - j := by
        by_cases he : k - j = 0
        · rw [he] at hsplit
          simp only [Nat.pow_zero] at hsplit
          have hp : 0 < 3 ^ a := Nat.pow_pos (by decide)
          omega
        · omega
      cases k with
      | zero => simp at hepos
      | succ k =>
        let be := r % 2
        let bo := 1 - r % 2
        have hr : r % 2 < 2 := Nat.mod_lt r (by decide)
        have hlen : (parityHalves xs be).length + (parityHalves xs bo).length = xs.length := by
          have hh := parityHalves_lengths xs
          by_cases hz : r % 2 = 0
          · simpa only [be, bo, hz] using hh
          · have ho : r % 2 = 1 := by omega
            simpa only [be, bo, ho, Nat.sub_self, Nat.add_comm] using hh
        have even_bound : (parityHalves xs be).length ≤ fibrePrefixBound (k - j) a := by
          apply grid_fibre_cardinality k y j a ((3 ^ a * be + r) / 2)
            (parityHalves xs be) (parityHalves_nodup hd be)
          intro z hz
          obtain ⟨x, hx, hb, rfl⟩ := mem_parityHalves.mp hz
          have hp : (3 ^ a * x + r) % 2 = 0 := by
            rw [grid_parity, hb]
            change (r % 2 + r % 2) % 2 = 0
            omega
          have hu := grid_step a r x
          rw [hp, if_neg (by decide : ¬ (0 : Nat) = 1), hb] at hu
          have hh := hf x hx
          simp only [orbit, wt, hp, Nat.zero_add, hu] at hh
          exact hh
        have odd_bound : (parityHalves xs bo).length ≤
            fibrePrefixBound (k + 1 - j) (a + 1) := by
          by_cases hj : j = 0
          · have hn : parityHalves xs bo = [] := by
              apply List.eq_nil_iff_forall_not_mem.mpr
              intro z hz
              obtain ⟨x, hx, hb, _⟩ := mem_parityHalves.mp hz
              have hp : (3 ^ a * x + r) % 2 = 1 := by
                rw [grid_parity, hb]
                change (1 - r % 2 + r % 2) % 2 = 1
                omega
              have hh := (hf x hx).2
              simp only [wt, hp, hj] at hh
              omega
            simp only [hn, List.length_nil, Nat.zero_le]
          · have he : k - (j - 1) = k + 1 - j := by omega
            rw [← he]
            apply grid_fibre_cardinality k y (j - 1) (a + 1)
              ((3 * (3 ^ a * bo + r) + 1) / 2)
              (parityHalves xs bo) (parityHalves_nodup hd bo)
            intro z hz
            obtain ⟨x, hx, hb, rfl⟩ := mem_parityHalves.mp hz
            have hp : (3 ^ a * x + r) % 2 = 1 := by
              rw [grid_parity, hb]
              change (1 - r % 2 + r % 2) % 2 = 1
              omega
            have hu := grid_step a r x
            rw [hp, if_pos rfl, hb] at hu
            have hh := hf x hx
            simp only [orbit, wt, hp, hu] at hh
            exact ⟨hh.1, by omega⟩
        rw [fibrePrefixBound, dif_pos hsplit]
        have he : k + 1 - j - 1 = k - j := by omega
        rw [he]
        omega
termination_by k _ _ _ _ _ _ _ => k

theorem fibre_prefix_cardinality (k y j : Nat) (xs : List Nat) (hd : xs.Nodup)
    (hf : ∀ x ∈ xs, orbit k x = y ∧ wt k x = j) :
    xs.length ≤ fibrePrefixBound (k - j) 0 := by
  exact grid_fibre_cardinality k y j 0 0 xs hd (by simpa using hf)

theorem two_even_cardinality (k y j : Nat) (xs : List Nat) (hd : xs.Nodup)
    (hf : ∀ x ∈ xs, orbit k x = y ∧ wt k x = j) (he : k - j = 2) :
    xs.length ≤ 2 := by
  have h := fibre_prefix_cardinality k y j xs hd hf
  rw [he] at h
  have hb : fibrePrefixBound 2 0 = 2 := by
    simp [fibrePrefixBound]
  omega

/-- The two-even upper bound is attained at arbitrarily large targets. -/
theorem two_even_sharp (q : Nat) :
    orbit 3 (8 * q + 4) = 3 * q + 2 ∧ wt 3 (8 * q + 4) = 1 ∧
    orbit 3 (8 * q + 5) = 3 * q + 2 ∧ wt 3 (8 * q + 5) = 1 := by
  have u1 : U (8 * q + 4) = 4 * q + 2 := by simp only [U]; split <;> omega
  have u2 : U (4 * q + 2) = 2 * q + 1 := by simp only [U]; split <;> omega
  have u3 : U (2 * q + 1) = 3 * q + 2 := by simp only [U]; split <;> omega
  have v1 : U (8 * q + 5) = 12 * q + 8 := by simp only [U]; split <;> omega
  have v2 : U (12 * q + 8) = 6 * q + 4 := by simp only [U]; split <;> omega
  have v3 : U (6 * q + 4) = 3 * q + 2 := by simp only [U]; split <;> omega
  simp only [orbit, wt, u1, u2, u3, v1, v2, v3, true_and]
  constructor <;> omega

-- Exact integer supports for the written exponent 19/24 and its moment corollary.
theorem prefix_exponent_certificates :
    1000 ^ 24 < 2 ^ 19 * 579 ^ 24 ∧
    1000 ^ 24 < 3 ^ 19 * 421 ^ 24 ∧
    2 ^ 19 * 2000 ^ 24 < 3 ^ 12 * 1999 ^ 24 := by decide

#print axioms fibre_span_sharp
#print axioms grid_fibre_cardinality
#print axioms fibre_prefix_cardinality
#print axioms two_even_cardinality
#print axioms two_even_sharp
#print axioms prefix_exponent_certificates

end CollatzPacking
