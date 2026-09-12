/-
  Weight-sensitive finite growth and parity-catalog collision criteria.
  Standalone Lean 4.31; kernel proofs only, no Mathlib or native evaluation.
  The finite height/catalog backbone below is reused from CollatzRepetition.
  The new minimum-weight product bound and its descent-or-repeat consequence
  do not assert catalog coverage or suitable weight bounds for all integers.
  Check: lean +leanprover/lean4:v4.31.0 CollatzComplexity.lean
-/
namespace CollatzComplexity

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
private theorem height_catalog_forces_repeat (k n : Nat) (catalog : List Nat)
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


def wt : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => n % 2 + wt t (U n)

theorem weight_le_time : ∀ t n, wt t n ≤ t
  | 0, n => by simp [wt]
  | t + 1, n => by
    have := weight_le_time t (U n)
    simp only [wt]
    omega

/-- At an odd step, x≥M bounds the additive correction multiplicatively.
    At an even step the corresponding inequality is an equality. -/
theorem minimum_step (M n : Nat) (hn : M ≤ n) :
    2 * M ^ (n % 2) * U n ≤ n * (3 * M + 1) ^ (n % 2) := by
  by_cases hp : n % 2 = 1
  · have he : 2 * U n = 3 * n + 1 := by
      simp only [U, if_pos hp]
      omega
    simp only [hp, Nat.pow_one]
    calc
      2 * M * U n = M * (2 * U n) := by
        simp [Nat.mul_comm, Nat.mul_left_comm]
      _ = M * (3 * n + 1) := by rw [he]
      _ = 3 * M * n + M := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ 3 * M * n + n := Nat.add_le_add_left hn _
      _ = n * (3 * M + 1) := by
        simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  · have hz : n % 2 = 0 := by omega
    simp only [hz, Nat.pow_zero, Nat.mul_one, U, Nat.zero_ne_one, if_false]
    omega

/-- Exact cumulative odd-count growth bound under a floor on all preceding
    states. All quantities are natural-number products; no rounding or real
    logarithms occur. The last state need not satisfy the floor assumption. -/
theorem minimum_weight_growth : ∀ t M n,
    (∀ i, i < t → M ≤ orbit i n) →
    2 ^ t * M ^ wt t n * orbit t n ≤ n * (3 * M + 1) ^ wt t n
  | 0, M, n, _ => by simp [orbit, wt]
  | t + 1, M, n, hmin => by
    have hn : M ≤ n := hmin 0 (by omega)
    have htail : ∀ i, i < t → M ≤ orbit i (U n) := by
      intro i hi
      exact hmin (i + 1) (by omega)
    have ih := minimum_weight_growth t M (U n) htail
    have hm := Nat.mul_le_mul_left (2 * M ^ (n % 2)) ih
    have hs := Nat.mul_le_mul_right ((3 * M + 1) ^ wt t (U n)) (minimum_step M n hn)
    calc
      2 ^ (t + 1) * M ^ wt (t + 1) n * orbit (t + 1) n =
          (2 * M ^ (n % 2)) * (2 ^ t * M ^ wt t (U n) * orbit t (U n)) := by
        simp [orbit, wt, Nat.pow_succ, Nat.pow_add,
          Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ ≤ (2 * M ^ (n % 2)) * (U n * (3 * M + 1) ^ wt t (U n)) := hm
      _ = (2 * M ^ (n % 2) * U n) * (3 * M + 1) ^ wt t (U n) := by
        simp only [Nat.mul_assoc]
      _ ≤ (n * (3 * M + 1) ^ (n % 2)) * (3 * M + 1) ^ wt t (U n) := hs
      _ = n * (3 * M + 1) ^ wt (t + 1) n := by
        simp [wt, Nat.pow_add, Nat.mul_assoc]

/-- A proved upper bound on the number of odd steps can replace the exact count. -/
theorem minimum_weight_growth_of_le (t M n J : Nat)
    (hmin : ∀ i, i < t → M ≤ orbit i n) (hw : wt t n ≤ J) :
    2 ^ t * M ^ J * orbit t n ≤ n * (3 * M + 1) ^ J := by
  have hpow : M ^ (J - wt t n) ≤ (3 * M + 1) ^ (J - wt t n) :=
    Nat.pow_le_pow_left (by omega) _
  have hg := minimum_weight_growth t M n hmin
  have hmul := Nat.mul_le_mul_left (M ^ (J - wt t n)) hg
  have htail := Nat.mul_le_mul_left (n * (3 * M + 1) ^ wt t n) hpow
  have hsum : wt t n + (J - wt t n) = J := by omega
  calc
    2 ^ t * M ^ J * orbit t n =
        M ^ (J - wt t n) * (2 ^ t * M ^ wt t n * orbit t n) := by
      rw [← hsum, Nat.pow_add]
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    _ ≤ M ^ (J - wt t n) * (n * (3 * M + 1) ^ wt t n) := hmul
    _ = (n * (3 * M + 1) ^ wt t n) * M ^ (J - wt t n) := Nat.mul_comm _ _
    _ ≤ (n * (3 * M + 1) ^ wt t n) * (3 * M + 1) ^ (J - wt t n) := htail
    _ = n * (3 * M + 1) ^ J := by rw [Nat.mul_assoc, ← Nat.pow_add, hsum]

/-- Weight products and a parity catalog suffice; there is no direct height
    premise. The floor is needed only before the catalog's last position. -/
theorem minimum_weight_catalog_forces_repeat (k M n : Nat) (catalog : List Nat)
    (hmin : ∀ i, i < catalog.length → M ≤ orbit i n)
    (hg : ∀ t, t ≤ catalog.length →
      n * (3 * M + 1) ^ wt t n < 2 ^ k * (2 ^ t * M ^ wt t n))
    (hc : ∀ t, t ≤ catalog.length → parityCode k (orbit t n) ∈ catalog) :
    ∃ i j, i < j ∧ j ≤ catalog.length ∧ orbit i n = orbit j n := by
  apply height_catalog_forces_repeat k n catalog _ hc
  intro t ht
  have hb := minimum_weight_growth t M n (fun i hi => hmin i (by omega))
  have hs := Nat.lt_of_le_of_lt hb (hg t ht)
  rw [Nat.mul_comm (2 ^ k)] at hs
  exact Nat.lt_of_mul_lt_mul_left hs

/-- The same criterion accepts independently established prefix weight bounds. -/
theorem bounded_weight_catalog_forces_repeat (k M n : Nat)
    (catalog : List Nat) (J : Nat → Nat)
    (hmin : ∀ i, i < catalog.length → M ≤ orbit i n)
    (hw : ∀ t, t ≤ catalog.length → wt t n ≤ J t)
    (hg : ∀ t, t ≤ catalog.length →
      n * (3 * M + 1) ^ J t < 2 ^ k * (2 ^ t * M ^ J t))
    (hc : ∀ t, t ≤ catalog.length → parityCode k (orbit t n) ∈ catalog) :
    ∃ i j, i < j ∧ j ≤ catalog.length ∧ orbit i n = orbit j n := by
  apply height_catalog_forces_repeat k n catalog _ hc
  intro t ht
  have hb := minimum_weight_growth_of_le t M n (J t)
    (fun i hi => hmin i (by omega)) (hw t ht)
  have hs := Nat.lt_of_le_of_lt hb (hg t ht)
  rw [Nat.mul_comm (2 ^ k)] at hs
  exact Nat.lt_of_mul_lt_mul_left hs

/-- Specializing the floor to the seed removes the floor assumption in favor
    of the useful alternative: descend before P, or repeat by P.
    Both catalog coverage and the weight-product inequalities remain explicit. -/
theorem catalog_forces_descent_or_repeat (k n : Nat) (catalog : List Nat)
    (hg : ∀ t, t ≤ catalog.length →
      n * (3 * n + 1) ^ wt t n < 2 ^ k * (2 ^ t * n ^ wt t n))
    (hc : ∀ t, t ≤ catalog.length → parityCode k (orbit t n) ∈ catalog) :
    (∃ t, t < catalog.length ∧ orbit t n < n) ∨
    (∃ i j, i < j ∧ j ≤ catalog.length ∧ orbit i n = orbit j n) := by
  classical
  by_cases hd : ∃ t, t < catalog.length ∧ orbit t n < n
  · exact Or.inl hd
  · apply Or.inr
    apply minimum_weight_catalog_forces_repeat k n n catalog _ hg hc
    intro i hi
    have hnot : ¬ orbit i n < n := by intro h; exact hd ⟨i, hi, h⟩
    omega

/-- A strict deficit in the minimum-based weight product already forces a
    smaller state, even without any parity-complexity assumption. -/
theorem descent_of_weight_deficit (t n : Nat) (hn : 0 < n)
    (hgap : (3 * n + 1) ^ wt t n < 2 ^ t * n ^ wt t n) :
    ∃ i, i ≤ t ∧ orbit i n < n := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hmin : ∀ i, i ≤ t → n ≤ orbit i n := by
    intro i hi
    have hnot : ¬ orbit i n < n := by intro h; exact hnone ⟨i, hi, h⟩
    omega
  have hg := minimum_weight_growth t n n (fun i hi => hmin i (by omega))
  have hlo := Nat.mul_le_mul_left (2 ^ t * n ^ wt t n) (hmin t (by omega))
  rw [Nat.mul_comm (2 ^ t * n ^ wt t n) n] at hlo
  have hle := Nat.le_trans hlo hg
  have hlt := Nat.mul_lt_mul_of_pos_left (k := n) hgap hn
  exact Nat.not_lt_of_ge hle hlt

#print axioms minimum_step
#print axioms minimum_weight_growth
#print axioms minimum_weight_growth_of_le
#print axioms minimum_weight_catalog_forces_repeat
#print axioms bounded_weight_catalog_forces_repeat
#print axioms catalog_forces_descent_or_repeat
#print axioms descent_of_weight_deficit

end CollatzComplexity
