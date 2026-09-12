/-
  From ordered cyclic numerators to actual positive odd Collatz cycles.
  Standalone Lean 4.31; no Mathlib, admitted proofs, or native evaluation.
  Check: lean +leanprover/lean4:v4.31.0 CollatzCycleCriterion.lean
-/
namespace CollatzCycleCriterion

def oddPart (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

def v2 (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then v2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

def F (n : Nat) : Nat := oddPart (3 * n + 1)

def iterate : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F (iterate k n)

/-- Factoring a power of two times an odd integer gives the exact exponent. -/
theorem odd_factor_exact (h y : Nat) (hy : y % 2 = 1) :
    oddPart (2 ^ h * y) = y ∧ v2 (2 ^ h * y) = h := by
  induction h with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    rw [oddPart.eq_def, dif_neg (by omega), v2.eq_def, dif_neg (by omega)]
    exact ⟨rfl, rfl⟩
  | succ h ih =>
    have hp : 0 < 2 ^ h * y := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    have he : 2 ^ (h + 1) * y = 2 * (2 ^ h * y) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [he, oddPart.eq_def, dif_pos (by omega), v2.eq_def, dif_pos (by omega)]
    simpa using ih

/-- An odd terminal factor turns a prescribed step equation into the actual map. -/
theorem actual_step (h x y : Nat) (hy : y % 2 = 1)
    (he : 2 ^ h * y = 3 * x + 1) : F x = y ∧ v2 (3 * x + 1) = h := by
  unfold F
  rw [← he]
  exact odd_factor_exact h y hy

/-- Coprimality with two permits divisibility to propagate to the next rotation. -/
theorem rotate_divisibility (D h A B : Nat) (hg : Nat.gcd 2 D = 1)
    (ha : D ∣ A) (he : 2 ^ h * B = 3 * A + D) : D ∣ B := by
  have hright : D ∣ 3 * A + D := Nat.dvd_add (Nat.dvd_mul_left_of_dvd ha 3) (Nat.dvd_refl D)
  rw [← he] at hright
  have hcancel := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hright
  rw [Nat.gcd_comm D (2 ^ h), Nat.gcd_pow_left_of_gcd_eq_one hg, Nat.one_mul] at hcancel
  exact hcancel

/-- An integral quotient of an odd numerator is again odd and positive. -/
theorem odd_quotient (D W : Nat) (hd : D ∣ W) (hw : W % 2 = 1) :
    (W / D) % 2 = 1 ∧ 0 < W / D := by
  have he : D * (W / D) = W := Nat.mul_div_cancel' hd
  have hm := congrArg (fun n => n % 2) he
  rw [Nat.mul_mod, hw] at hm
  have hn : (W / D) % 2 ≠ 0 := by
    intro hz
    simp only [hz, Nat.mul_zero, Nat.zero_mod] at hm
    contradiction
  have ho : (W / D) % 2 = 1 := by omega
  refine ⟨ho, Nat.pos_of_ne_zero ?_⟩
  intro hz
  rw [hz] at ho
  contradiction

theorem quotient_step (D h A B : Nat) (hD : 0 < D)
    (ha : D ∣ A) (hb : D ∣ B) (he : 2 ^ h * B = 3 * A + D) :
    2 ^ h * (B / D) = 3 * (A / D) + 1 := by
  have hea : D * (A / D) = A := Nat.mul_div_cancel' ha
  have heb : D * (B / D) = B := Nat.mul_div_cancel' hb
  apply Nat.eq_of_mul_eq_mul_left hD
  calc
    D * (2 ^ h * (B / D)) = 2 ^ h * B := by
      rw [Nat.mul_left_comm D, heb]
    _ = 3 * A + D := he
    _ = D * (3 * (A / D) + 1) := by
      rw [Nat.mul_add, Nat.mul_left_comm D, hea, Nat.mul_one]

/-- The complete bridge for any finite cyclic numerator sequence. The oddness
    and rotation equations are explicit premises, not facts inferred from a
    supplied label or an unchecked list of purported cycle members. -/
theorem cyclic_numerators_realize (k D : Nat) (h W : Nat → Nat)
    (hk : 0 < k) (hD : 0 < D) (hg : Nat.gcd 2 D = 1)
    (hodd : ∀ i, i ≤ k → W i % 2 = 1)
    (hrot : ∀ i, i < k → 2 ^ h i * W (i + 1) = 3 * W i + D)
    (hclose : W k = W 0) (hdiv : D ∣ W 0) :
    0 < W 0 / D ∧ (W 0 / D) % 2 = 1 ∧
    iterate k (W 0 / D) = W 0 / D ∧
    (∀ i, i ≤ k → iterate i (W 0 / D) = W i / D) ∧
    (∀ i, i < k → v2 (3 * iterate i (W 0 / D) + 1) = h i) := by
  have hall : ∀ i, i ≤ k → D ∣ W i := by
    intro i
    induction i with
    | zero => intro _; exact hdiv
    | succ i ih =>
      intro hi
      exact rotate_divisibility D (h i) (W i) (W (i + 1)) hg
        (ih (by omega)) (hrot i (by omega))
  have hq : ∀ i, i ≤ k → (W i / D) % 2 = 1 ∧ 0 < W i / D := by
    intro i hi
    exact odd_quotient D (W i) (hall i hi) (hodd i hi)
  have hs : ∀ i, i < k →
      F (W i / D) = W (i + 1) / D ∧ v2 (3 * (W i / D) + 1) = h i := by
    intro i hi
    exact actual_step (h i) (W i / D) (W (i + 1) / D)
      (hq (i + 1) (by omega)).1
      (quotient_step D (h i) (W i) (W (i + 1)) hD
        (hall i (by omega)) (hall (i + 1) (by omega)) (hrot i hi))
  have hit : ∀ i, i ≤ k → iterate i (W 0 / D) = W i / D := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [iterate, ih (by omega)]
      exact (hs i (by omega)).1
  refine ⟨(hq 0 (by omega)).2, (hq 0 (by omega)).1, ?_, hit, ?_⟩
  · rw [hit k (by omega), hclose]
  · intro i hi
    rw [hit i (by omega)]
    exact (hs i hi).2

#print axioms odd_factor_exact
#print axioms quotient_step
#print axioms cyclic_numerators_realize

end CollatzCycleCriterion
