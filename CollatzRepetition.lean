/-
  Finite parity repetition and exact collision certificates.
  Standalone Lean 4, using kernel proofs only.
  Check: lean CollatzRepetition.lean
-/
namespace CollatzRepetition

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbit k (U n)

def SameParity : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | k + 1, x, y => x % 2 = y % 2 ∧ SameParity k (U x) (U y)

theorem even_equation (n : Nat) (h : n % 2 ≠ 1) :
    2 * (U n : Int) = (n : Int) := by
  unfold U
  rw [if_neg h]
  omega

theorem odd_equation (n : Nat) (h : n % 2 = 1) :
    2 * (U n : Int) = 3 * (n : Int) + 1 := by
  unfold U
  rw [if_pos h]
  omega

/-- Agreement of k parities forces k bits of congruence, in exact integers. -/
theorem parity_gap_divisible : ∀ k x y, SameParity k x y →
    2 ^ k ∣ ((x : Int) - (y : Int)).natAbs
  | 0, x, y, _ => by simp
  | k + 1, x, y, h => by
    obtain ⟨hpar, htail⟩ := h
    have ih := parity_gap_divisible k (U x) (U y) htail
    have hd : 2 ^ (k + 1) ∣ 2 * ((U x : Int) - (U y : Int)).natAbs := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
      exact Nat.mul_dvd_mul_left 2 ih
    by_cases hx : x % 2 = 1
    · have hy : y % 2 = 1 := by omega
      have he : 2 * ((U x : Int) - (U y : Int)) = 3 * ((x : Int) - (y : Int)) := by
        rw [Int.mul_sub, Int.mul_sub, odd_equation x hx, odd_equation y hy]
        omega
      have habs := congrArg Int.natAbs he
      simp only [Int.natAbs_mul] at habs
      change 2 * ((U x : Int) - (U y : Int)).natAbs =
        3 * ((x : Int) - (y : Int)).natAbs at habs
      have hd3 : 2 ^ (k + 1) ∣ 3 * ((x : Int) - (y : Int)).natAbs := by
        simpa only [habs] using hd
      have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd3
      rw [Nat.gcd_pow_left_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1), Nat.one_mul] at hc
      exact hc
    · have hy : y % 2 ≠ 1 := by omega
      have he : 2 * ((U x : Int) - (U y : Int)) = (x : Int) - (y : Int) := by
        rw [Int.mul_sub, even_equation x hx, even_equation y hy]
      have habs := congrArg Int.natAbs he
      simp only [Int.natAbs_mul] at habs
      change 2 * ((U x : Int) - (U y : Int)).natAbs =
        ((x : Int) - (y : Int)).natAbs at habs
      simpa only [habs] using hd

/-- Equal parity windows in a small enough value interval imply an actual collision. -/
theorem collision_of_small_gap {k x y : Nat} (h : SameParity k x y)
    (hgap : ((x : Int) - (y : Int)).natAbs < 2 ^ k) : x = y := by
  have hd := parity_gap_divisible k x y h
  by_cases hz : ((x : Int) - (y : Int)).natAbs = 0
  · have he := Int.natAbs_eq_zero.mp hz
    omega
  · have hle := Nat.le_of_dvd (by omega) hd
    omega

theorem collision_below_power {k x y : Nat} (h : SameParity k x y)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) : x = y := by
  apply collision_of_small_gap h
  omega

theorem orbit_add (a b n : Nat) : orbit (a + b) n = orbit b (orbit a n) := by
  induction a generalizing n with
  | zero => simp [orbit]
  | succ a ih =>
    simpa only [Nat.succ_add, orbit] using ih (U n)

/-- Once a state repeats, all later states repeat with the same positive period. -/
theorem repeated_state_periodic {a b n : Nat} (h : orbit a n = orbit b n) (t : Nat) :
    orbit (a + t) n = orbit (b + t) n := by
  rw [orbit_add, orbit_add, h]

theorem parity_collision_periodic {a b k n : Nat}
    (hp : SameParity k (orbit a n) (orbit b n))
    (ha : orbit a n < 2 ^ k) (hb : orbit b n < 2 ^ k) (t : Nat) :
    orbit (a + t) n = orbit (b + t) n :=
  repeated_state_periodic (collision_below_power hp ha hb) t

/-- A natural-number encoding of the finite parity word. -/
def parityCode : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + 2 * parityCode k (U n)

theorem code_implies_same_parity : ∀ k x y,
    parityCode k x = parityCode k y → SameParity k x y
  | 0, _, _, _ => True.intro
  | k + 1, x, y, h => by
    simp only [parityCode] at h
    have hp : x % 2 = y % 2 := by omega
    have ht : parityCode k (U x) = parityCode k (U y) := by omega
    exact ⟨hp, code_implies_same_parity k (U x) (U y) ht⟩

private theorem distinct_subset_length {xs ys : List Nat} (hd : xs.Nodup)
    (hs : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ha : a ∈ ys := hs a (by simp)
    obtain ⟨hna, hdx⟩ := List.nodup_cons.mp hd
    have hsub : ∀ x ∈ xs, x ∈ ys.erase a := by
      intro x hx
      have hne : x ≠ a := by intro h; subst x; exact hna hx
      exact (List.mem_erase_of_ne hne).mpr (hs x (by simp [hx]))
    have hlen := ih hdx hsub
    have he := List.length_erase_of_mem ha
    have hpos : 0 < ys.length := List.length_pos_iff.mpr (by intro h; simp [h] at ha)
    simp only [List.length_cons]
    omega

/-- A finite catalog of parity factors, together with exact height bounds,
    forces an actual repeat by the end of the catalog's size. No global
    word-complexity or universal height premise is asserted here. -/
theorem factor_catalog_forces_repeat (k n : Nat) (catalog : List Nat)
    (hb : ∀ t, t ≤ catalog.length → orbit t n < 2 ^ k)
    (hc : ∀ t, t ≤ catalog.length → parityCode k (orbit t n) ∈ catalog) :
    ∃ i j, i < j ∧ j ≤ catalog.length ∧ orbit i n = orbit j n := by
  classical
  apply Classical.byContradiction
  intro hnone
  let f := fun t => parityCode k (orbit t n)
  have hi : ∀ i, i ≤ catalog.length → ∀ j, j ≤ catalog.length → f i = f j → i = j := by
    intro i hi j hj he
    have hs := code_implies_same_parity k (orbit i n) (orbit j n) he
    have ho := collision_below_power hs (hb i hi) (hb j hj)
    apply Classical.byContradiction
    intro hij
    have horder : i < j ∨ j < i := by omega
    cases horder with
    | inl hlt => exact hnone ⟨i, j, hlt, hj, ho⟩
    | inr hlt => exact hnone ⟨j, i, hlt, hi, ho.symm⟩
  have hd : ((List.range (catalog.length + 1)).map f).Nodup := by
    apply List.pairwise_map.mpr
    have hd0 : (List.range (catalog.length + 1)).Nodup := List.nodup_range
    exact List.Pairwise.imp_of_mem (fun hx hy hne he => hne (hi _ (by
      have := List.mem_range.mp hx; omega) _ (by
      have := List.mem_range.mp hy; omega) he)) hd0
  have hs : ∀ x ∈ (List.range (catalog.length + 1)).map f, x ∈ catalog := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact hc t (by have := List.mem_range.mp ht; omega)
  have hlen := distinct_subset_length hd hs
  simp only [List.length_map, List.length_range] at hlen
  omega

#print axioms parity_gap_divisible
#print axioms collision_of_small_gap
#print axioms parity_collision_periodic
#print axioms factor_catalog_forces_repeat

end CollatzRepetition
