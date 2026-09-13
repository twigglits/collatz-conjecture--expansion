/-
  A close rational approximation makes folded rank order automatic.
  Standalone Lean 4.33.1; no Mathlib or native evaluation.

  All values below are natural-number numerators. Multiplying a positive
  rational cycle by a common denominator supplies the same hypotheses.
  The mask construction and logarithm applications are written in
  docs/MASK-FOLDED-ORDER.md.
-/
namespace MaskFoldedOrder

def PositiveEdges (k N : Nat) (v : Nat → Nat) : Prop :=
  ∀ j, j < k →
    3 * v j < 2 ^ ((j + N) / k) * v ((j + N) % k)

def scaled (k N : Nat) (v : Nat → Nat) (j i : Nat) : Nat :=
  2 ^ ((j + i * N) / k) * v ((j + i * N) % k)

theorem carry_div {k : Nat} (hk : 0 < k) (a N : Nat) :
    (a + N) / k = a / k + (a % k + N) / k := by
  have he : a + N = (a % k + N) + k * (a / k) := by
    have := Nat.mod_add_div a k
    omega
  rw [he, Nat.add_mul_div_left _ _ hk]
  exact Nat.add_comm _ _

theorem carry_mod (k a N : Nat) :
    (a + N) % k = (a % k + N) % k := by
  have he : a + N = (a % k + N) + k * (a / k) := by
    have := Nat.mod_add_div a k
    omega
  rw [he, Nat.add_mul_mod_self_left]

theorem scaled_step {k N : Nat} {v : Nat → Nat} (hk : 0 < k)
    (he : PositiveEdges k N v) (j i : Nat) :
    3 * scaled k N v j i < scaled k N v j (i + 1) := by
  have ha : j + (i + 1) * N = (j + i * N) + N := by
    simp [Nat.add_mul, Nat.add_assoc]
  unfold scaled
  rw [ha, carry_div hk (j + i * N) N, carry_mod k (j + i * N) N,
    Nat.pow_add, Nat.mul_assoc]
  have hh := Nat.mul_lt_mul_of_pos_left
    (he ((j + i * N) % k) (Nat.mod_lt _ hk))
    (Nat.pow_pos (by decide : 0 < 2) (n := (j + i * N) / k))
  simpa only [Nat.mul_left_comm, Nat.mul_assoc] using hh

theorem scaled_iterate_le {k N : Nat} {v : Nat → Nat}
    (hk : 0 < k) (he : PositiveEdges k N v)
    (j : Nat) (hj : j < k) (i : Nat) :
    3 ^ i * v j ≤ scaled k N v j i := by
  induction i with
  | zero =>
      simp [scaled, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
  | succ i ih =>
      have hs := scaled_step hk he j i
      calc
        3 ^ (i + 1) * v j = 3 * (3 ^ i * v j) := by
          rw [Nat.pow_succ]
          ac_rfl
        _ ≤ 3 * scaled k N v j i := Nat.mul_le_mul_left 3 ih
        _ ≤ scaled k N v j (i + 1) := Nat.le_of_lt hs

theorem scaled_iterate_lt {k N : Nat} {v : Nat → Nat}
    (hk : 0 < k) (he : PositiveEdges k N v)
    (j : Nat) (hj : j < k) (q : Nat) (hq : 0 < q) :
    3 ^ q * v j < scaled k N v j q := by
  obtain ⟨i, rfl⟩ : ∃ i, q = i + 1 := ⟨q - 1, by omega⟩
  calc
    3 ^ (i + 1) * v j = 3 * (3 ^ i * v j) := by
      rw [Nat.pow_succ]
      ac_rfl
    _ ≤ 3 * scaled k N v j i :=
      Nat.mul_le_mul_left 3 (scaled_iterate_le hk he j hj i)
    _ < scaled k N v j (i + 1) := scaled_step hk he j i

/-- The Bezout relation makes q rank steps move exactly one place forward.
    Positivity and 2^t ≤ 3^q then force every neighboring comparison,
    including the doubled last-to-first comparison. -/
theorem automatic_order {k N q t : Nat} {v : Nat → Nat}
    (hk : 0 < k) (hq : 0 < q) (hbez : q * N = k * t + 1)
    (hexp : 2 ^ t ≤ 3 ^ q) (he : PositiveEdges k N v) :
    (∀ j, j + 1 < k → v j < v (j + 1)) ∧
      v (k - 1) < 2 * v 0 := by
  constructor
  · intro j hj
    have hg := scaled_iterate_lt hk he j (by omega) q hq
    have hn : j + q * N = (j + 1) + k * t := by omega
    rw [scaled, hn, Nat.add_mul_div_left _ _ hk,
      Nat.add_mul_mod_self_left, Nat.div_eq_of_lt hj,
      Nat.mod_eq_of_lt hj, Nat.zero_add] at hg
    have hh := Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (v j) hexp) hg
    exact (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < 2))).mp hh
  · have hg := scaled_iterate_lt hk he (k - 1) (by omega) q hq
    have hn : k - 1 + q * N = 0 + k * (t + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [scaled, hn, Nat.add_mul_div_left _ _ hk,
      Nat.add_mul_mod_self_left, Nat.zero_div, Nat.zero_mod,
      Nat.zero_add, Nat.pow_succ] at hg
    have hh := Nat.lt_of_le_of_lt
      (Nat.mul_le_mul_right (v (k - 1)) hexp) hg
    rw [Nat.mul_assoc] at hh
    exact (Nat.mul_lt_mul_left (Nat.pow_pos (by decide : 0 < 2))).mp hh

theorem monotone_in_range {k : Nat} {v : Nat → Nat}
    (hinc : ∀ j, j + 1 < k → v j < v (j + 1))
    (i j : Nat) (hij : i ≤ j) (hj : j < k) : v i ≤ v j := by
  induction j generalizing i with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact Nat.le_refl _
  | succ j ih =>
      by_cases he : i = j + 1
      · subst i; exact Nat.le_refl _
      · exact Nat.le_trans (ih i (by omega) (by omega))
          (Nat.le_of_lt (hinc j hj))

theorem folded_pair_bound {k N q t : Nat} {v : Nat → Nat}
    (hk : 0 < k) (hq : 0 < q) (hbez : q * N = k * t + 1)
    (hexp : 2 ^ t ≤ 3 ^ q) (he : PositiveEdges k N v)
    (i j : Nat) (hi : i < k) (hj : j < k) :
    v j < 2 * v i := by
  have ho := automatic_order hk hq hbez hexp he
  have hl := monotone_in_range ho.1 0 i (by omega) hi
  have hu := monotone_in_range ho.1 j (k - 1) (by omega) (by omega)
  exact Nat.lt_of_le_of_lt hu
    (Nat.lt_of_lt_of_le ho.2 (Nat.mul_le_mul_left 2 hl))

theorem positive_edges_of_equations {k N : Nat} {v a : Nat → Nat}
    (ha : ∀ j, j < k → 0 < a j)
    (he : ∀ j, j < k →
      2 ^ ((j + N) / k) * v ((j + N) % k) = 3 * v j + a j) :
    PositiveEdges k N v := by
  intro j hj
  rw [he j hj]
  have := ha j hj
  omega

/-- An entirely integer version of q*(N*log 2-k*log 3) < log 2.
    It makes the ordering theorem's power comparison automatic. -/
theorem expansive_from_power_gap {k N q t : Nat}
    (hbez : q * N = k * t + 1)
    (hclose : (2 ^ N) ^ q < 2 * (3 ^ k) ^ q) :
    2 ^ t < 3 ^ q := by
  have hNq : N * q = k * t + 1 := by
    simpa [Nat.mul_comm] using hbez
  rw [← Nat.pow_mul, ← Nat.pow_mul, hNq, Nat.pow_succ,
    Nat.mul_comm (2 ^ (k * t)) 2] at hclose
  have hh := (Nat.mul_lt_mul_left (by decide : 0 < 2)).mp hclose
  have hp : (2 ^ t) ^ k < (3 ^ q) ^ k := by
    simpa only [← Nat.pow_mul, Nat.mul_comm t k, Nat.mul_comm q k] using hh
  by_cases he : 2 ^ t < 3 ^ q
  · exact he
  · have hn := Nat.pow_le_pow_left (show 3 ^ q ≤ 2 ^ t by omega) k
    omega

/-- The two mask layers have scales 2 and 4. The conclusion applies to
    numerator ratios and hence to their common-denominator rational states. -/
theorem two_layer_spread {k N q t : Nat} {v c W : Nat → Nat}
    (hk : 0 < k) (hq : 0 < q) (hbez : q * N = k * t + 1)
    (hexp : 2 ^ t ≤ 3 ^ q) (he : PositiveEdges k N v)
    (hc : ∀ j, j < k → c j = 2 ∨ c j = 4)
    (hv : ∀ j, j < k → v j = c j * W j)
    (i j : Nat) (hi : i < k) (hj : j < k) :
    W j < 4 * W i := by
  have hh := folded_pair_bound hk hq hbez hexp he i j hi hj
  rw [hv i hi, hv j hj] at hh
  rcases hc i hi with hci | hci <;>
    rcases hc j hj with hcj | hcj <;>
    rw [hci, hcj] at hh <;> omega

set_option maxRecDepth 16384 in
set_option exponentiation.threshold 8192 in
theorem concrete_counts :
    53 * 485 = 306 * 84 + 1 ∧ 2 ^ 84 < 3 ^ 53 ∧
    665 * 4701 = 2966 * 1054 + 1 ∧ 2 ^ 1054 < 3 ^ 665 := by decide

#print axioms scaled_step
#print axioms scaled_iterate_lt
#print axioms automatic_order
#print axioms folded_pair_bound
#print axioms positive_edges_of_equations
#print axioms expansive_from_power_gap
#print axioms two_layer_spread
#print axioms concrete_counts
end MaskFoldedOrder
