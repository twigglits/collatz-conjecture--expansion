/-
  Integer arithmetic for the narrow-cycle reduction in
  docs/NARROW-CYCLE-MASKS.md. Standalone Lean 4; kernel proofs only.

  The cyclic sorting and mechanical-rank assembly are written arguments.
  No classification of all positive integer cycles is assumed or concluded.
-/
namespace NarrowCycleMasks

def total (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => total h i + h i

/-- An elementary substitute for the real exponential estimate. -/
theorem sub_pow_bound (a k : Nat) (hk : k ≤ a) :
    (a - k) * (a + 1) ^ k ≤ a ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih' := ih (by omega)
    have he : a - k = (a - (k + 1)) + 1 := by omega
    have hs : (a - (k + 1)) * (a + 1) ≤ a * (a - k) := by
      rw [he, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.mul_one]
      rw [Nat.mul_comm (a - (k + 1)) a]
      exact Nat.add_le_add_left (Nat.sub_le _ _) _
    calc
      (a - (k + 1)) * (a + 1) ^ (k + 1) =
          ((a - (k + 1)) * (a + 1)) * (a + 1) ^ k := by
            rw [Nat.pow_succ]
            ac_rfl
      _ ≤ (a * (a - k)) * (a + 1) ^ k :=
        Nat.mul_le_mul_right _ hs
      _ = a * ((a - k) * (a + 1) ^ k) := by ac_rfl
      _ ≤ a * a ^ (k + 1) := Nat.mul_le_mul_left _ ih'
      _ = a ^ ((k + 1) + 1) := by simp only [Nat.pow_succ]; ac_rfl

theorem small_relative_power (m k : Nat) (hm : 0 < m) (hk : k ≤ m) :
    (3 * m + 1) ^ k < 2 * (3 * m) ^ k := by
  have hb := sub_pow_bound (3 * m) k (by omega)
  apply Nat.lt_of_not_ge
  intro hge
  have he := Nat.le_trans (Nat.mul_le_mul_left (3 * m - k) hge) hb
  have he' : (2 * (3 * m - k)) * (3 * m) ^ k ≤
      (3 * m) * (3 * m) ^ k := by
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he
  have hp : 0 < (3 * m) ^ k := Nat.pow_pos (by omega)
  have := Nat.le_of_mul_le_mul_right he' hp
  omega

theorem step_upper (m x y h : Nat) (hx : m ≤ x)
    (he : 2 ^ h * y = 3 * x + 1) :
    m * (2 ^ h * y) ≤ (3 * m + 1) * x := by
  rw [he]
  calc
    m * (3 * x + 1) = 3 * (m * x) + m := by
      simp [Nat.mul_add, Nat.mul_left_comm]
    _ ≤ 3 * (m * x) + x := Nat.add_le_add_left hx _
    _ = (3 * m + 1) * x := by simp [Nat.add_mul, Nat.mul_assoc]

theorem prefix_upper (m : Nat) (h x : Nat → Nat) (k : Nat)
    (hx : ∀ i, i < k → m ≤ x i)
    (he : ∀ i, i < k → 2 ^ h i * x (i + 1) = 3 * x i + 1) :
    m ^ k * 2 ^ total h k * x k ≤ (3 * m + 1) ^ k * x 0 := by
  induction k with
  | zero => simp [total]
  | succ k ih =>
    have hi := ih (fun i hi => hx i (by omega)) (fun i hi => he i (by omega))
    have hs := step_upper m (x k) (x (k + 1)) (h k) (hx k (by omega))
      (he k (by omega))
    calc
      m ^ (k + 1) * 2 ^ total h (k + 1) * x (k + 1) =
          (m ^ k * 2 ^ total h k) * (m * (2 ^ h k * x (k + 1))) := by
            simp only [total, Nat.pow_add, Nat.pow_succ]
            ac_rfl
      _ ≤ (m ^ k * 2 ^ total h k) * ((3 * m + 1) * x k) :=
        Nat.mul_le_mul_left _ hs
      _ = (3 * m + 1) * (m ^ k * 2 ^ total h k * x k) := by ac_rfl
      _ ≤ (3 * m + 1) * ((3 * m + 1) ^ k * x 0) :=
        Nat.mul_le_mul_left _ hi
      _ = (3 * m + 1) ^ (k + 1) * x 0 := by rw [Nat.pow_succ]; ac_rfl

theorem prefix_lower (h x : Nat → Nat) (k : Nat)
    (he : ∀ i, i < k → 2 ^ h i * x (i + 1) = 3 * x i + 1) :
    3 ^ k * x 0 ≤ 2 ^ total h k * x k := by
  induction k with
  | zero => simp [total]
  | succ k ih =>
    have hi := ih (fun i hi => he i (by omega))
    have hs : 3 * x k ≤ 2 ^ h k * x (k + 1) := by
      rw [he k (by omega)]; omega
    calc
      3 ^ (k + 1) * x 0 = 3 * (3 ^ k * x 0) := by rw [Nat.pow_succ]; ac_rfl
      _ ≤ 3 * (2 ^ total h k * x k) := Nat.mul_le_mul_left _ hi
      _ = 2 ^ total h k * (3 * x k) := by ac_rfl
      _ ≤ 2 ^ total h k * (2 ^ h k * x (k + 1)) := Nat.mul_le_mul_left _ hs
      _ = 2 ^ total h (k + 1) * x (k + 1) := by
        simp only [total, Nat.pow_add]; ac_rfl

theorem prefix_lower_strict (h x : Nat → Nat) (k : Nat) (hk : 0 < k)
    (he : ∀ i, i < k → 2 ^ h i * x (i + 1) = 3 * x i + 1) :
    3 ^ k * x 0 < 2 ^ total h k * x k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hi := prefix_lower h x j (fun i hi => he i (by omega))
  have hs : 3 * x j < 2 ^ h j * x (j + 1) := by
    rw [he j (by omega)]; omega
  calc
    3 ^ (j + 1) * x 0 = 3 * (3 ^ j * x 0) := by rw [Nat.pow_succ]; ac_rfl
    _ ≤ 3 * (2 ^ total h j * x j) := Nat.mul_le_mul_left _ hi
    _ = 2 ^ total h j * (3 * x j) := by ac_rfl
    _ < 2 ^ total h j * (2 ^ h j * x (j + 1)) :=
      Nat.mul_lt_mul_of_pos_left hs (Nat.pow_pos (by decide))
    _ = 2 ^ total h (j + 1) * x (j + 1) := by
      simp only [total, Nat.pow_add]; ac_rfl

/-- An exact cycle with at least as large a minimum as odd count has critical
    total halving count: 3^k < 2^H < 2*3^k. No real logarithms are used. -/
theorem cycle_critical (m k : Nat) (h x : Nat → Nat)
    (hm : 0 < m) (hk : 0 < k) (hkm : k ≤ m)
    (hx : ∀ i, i < k → m ≤ x i)
    (he : ∀ i, i < k → 2 ^ h i * x (i + 1) = 3 * x i + 1)
    (hclose : x k = x 0) :
    3 ^ k < 2 ^ total h k ∧ 2 ^ total h k < 2 * 3 ^ k := by
  have hx0 : 0 < x 0 := by have := hx 0 hk; omega
  have hl := prefix_lower_strict h x k hk he
  rw [hclose] at hl
  have hlu := Nat.lt_of_mul_lt_mul_right hl
  have hu := prefix_upper m h x k hx he
  rw [hclose] at hu
  have hu' := Nat.le_of_mul_le_mul_right hu hx0
  have hb := small_relative_power m k hm hkm
  have hc := Nat.lt_of_le_of_lt hu' hb
  have hc' : m ^ k * 2 ^ total h k < m ^ k * (2 * 3 ^ k) := by
    simpa only [Nat.mul_pow, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hc
  exact ⟨hlu, (Nat.mul_lt_mul_left (Nat.pow_pos hm)).mp hc'⟩

theorem odd_gap (x y : Nat) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (hxy : x < y) : x + 2 ≤ y := by omega

theorem sorted_odd_span (k : Nat) (x : Nat → Nat)
    (ho : ∀ i, i < k → x i % 2 = 1)
    (hi : ∀ i, i + 1 < k → x i < x (i + 1))
    (j : Nat) (hj : j < k) : x 0 + 2 * j ≤ x j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hp := ih (by omega)
    have hg := odd_gap (x j) (x (j + 1)) (ho j (by omega))
      (ho (j + 1) hj) (hi j hj)
    omega

/-- Sorting distinct odd states below three times the minimum gives k ≤ m. -/
theorem count_le_minimum (k : Nat) (x : Nat → Nat) (hk : 0 < k)
    (ho : ∀ i, i < k → x i % 2 = 1)
    (hi : ∀ i, i + 1 < k → x i < x (i + 1))
    (hspan : x (k - 1) < 3 * x 0) : k ≤ x 0 := by
  have := sorted_odd_span k x ho hi (k - 1) (by omega)
  omega

def layer (m x : Nat) : Nat := if 2 * m ≤ x then 1 else 0

def foldedExponent (m x y h : Nat) : Nat :=
  h + layer m y - layer m x

def scale (m x : Nat) : Nat := if 2 * m ≤ x then 1 else 2

theorem folded_range (m M x : Nat) (hxlo : m ≤ x) (hxhi : x ≤ M)
    (hspan : 3 * M + 1 < 8 * m) :
    2 * m ≤ scale m x * x ∧ scale m x * x < 4 * m := by
  unfold scale
  split <;> omega

theorem folded_injective (m x y : Nat) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (he : scale m x * x = scale m y * y) : x = y := by
  unfold scale at he
  split at he <;> split at he <;> omega

theorem folded_numerators_order (u v c d : Nat) (hc : c = 1 ∨ c = 2)
    (hd : d = 1 ∨ d = 2) (huv : u < v) :
    3 * u + c < 3 * v + d := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

theorem folded_numerators_span (m u v c d : Nat) (hc : c = 1 ∨ c = 2)
    (hd : d = 1 ∨ d = 2) (hu : 2 * m ≤ u) (hv : v < 4 * m) :
    3 * v + d < 2 * (3 * u + c) := by
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;> omega

theorem narrow_halvings (m M x y h : Nat) (hh : 0 < h)
    (hupper : x ≤ M) (hlower : m ≤ y)
    (hspan : 3 * M + 1 < 8 * m)
    (he : 2 ^ h * y = 3 * x + 1) : h = 1 ∨ h = 2 := by
  by_cases hn : h = 1 ∨ h = 2
  · exact hn
  have hh3 : 3 ≤ h := by omega
  have hp : 8 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide : 0 < 2) hh3
  have := Nat.mul_le_mul_right y hp
  omega

/-- A high state is isolated, entered by halving 1 and left by halving 2.
    Its folded edges are therefore 2 then 1, exactly one independent edit. -/
theorem narrow_edge (m M x y h : Nat) (hh : 0 < h)
    (hxhi : x ≤ M) (hylo : m ≤ y) (hyhi : y ≤ M)
    (hspan : 3 * M + 1 < 8 * m)
    (he : 2 ^ h * y = 3 * x + 1) :
    (foldedExponent m x y h = 1 ∨ foldedExponent m x y h = 2) ∧
    h + layer m y = foldedExponent m x y h + layer m x ∧
    (layer m x = 1 →
      h = 2 ∧ layer m y = 0 ∧ foldedExponent m x y h = 1) ∧
    (layer m y = 1 →
      h = 1 ∧ layer m x = 0 ∧ foldedExponent m x y h = 2) := by
  have hh12 := narrow_halvings m M x y h hh hxhi hylo hspan he
  rcases hh12 with rfl | rfl <;>
    simp only [Nat.pow_one, Nat.reducePow] at he <;>
    unfold foldedExponent layer <;>
    split <;> split <;> omega

theorem folded_edge_equation (m M x y h : Nat) (hh : 0 < h)
    (hxhi : x ≤ M) (hylo : m ≤ y)
    (hspan : 3 * M + 1 < 8 * m)
    (he : 2 ^ h * y = 3 * x + 1) :
    2 ^ foldedExponent m x y h * (scale m y * y) =
      3 * (scale m x * x) + scale m x := by
  have hh12 := narrow_halvings m M x y h hh hxhi hylo hspan he
  rcases hh12 with rfl | rfl <;>
    simp only [Nat.pow_one, Nat.reducePow] at he <;>
    unfold foldedExponent layer scale <;>
    split <;> split <;> simp_all <;> omega

/-- Two successive one-halving edges give an exact lower bound on the span. -/
theorem two_rises (m M x y z : Nat) (hx : m ≤ x) (hz : z ≤ M)
    (hfirst : 2 * y = 3 * x + 1) (hsecond : 2 * z = 3 * y + 1) :
    9 * m + 5 ≤ 4 * M := by omega

/-- Distinct starts of double rises consume two units of odd-state spacing. -/
theorem many_two_rises (m M q : Nat) (x : Nat → Nat) (hq : 0 < q)
    (hm : m ≤ x 0)
    (ho : ∀ i, i < q → x i % 2 = 1)
    (hi : ∀ i, i + 1 < q → x i < x (i + 1))
    (hbound : 9 * x (q - 1) + 5 ≤ 4 * M) :
    9 * m + 18 * q ≤ 4 * M + 13 := by
  have := sorted_odd_span q x ho hi (q - 1) (by omega)
  omega

#print axioms sub_pow_bound
#print axioms small_relative_power
#print axioms cycle_critical
#print axioms count_le_minimum
#print axioms folded_range
#print axioms folded_injective
#print axioms folded_numerators_order
#print axioms folded_numerators_span
#print axioms narrow_halvings
#print axioms narrow_edge
#print axioms folded_edge_equation
#print axioms two_rises
#print axioms many_two_rises
end NarrowCycleMasks
