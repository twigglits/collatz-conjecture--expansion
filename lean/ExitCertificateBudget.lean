/-
  Exact integer budget for successful exit-mass certificates.
  This is an abstract telescoping theorem, not a Collatz contraction theorem.
  Infinite sums, varying source cutoffs, and real logarithms are treated in
  docs/EXIT-CERTIFICATE-BUDGET.md, not in this standalone Lean module.
-/
namespace ExitCertificateBudget

def goodCount (good : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => goodCount good k + if good k then 1 else 0

/-- An exit lower bound plus an envelope decrement gives a contraction. -/
theorem contraction_of_exit (q h u next loss : Nat)
    (hdecr : next + loss ≤ u) (htest : h * u ≤ (q + h) * loss) :
    (q + h) * next ≤ q * u := by
  have hm := Nat.mul_le_mul_left (q + h) hdecr
  rw [Nat.mul_add, Nat.add_mul q h u] at hm
  omega

/-- Multiply the successful ratios; unsuccessful steps still decrease. -/
theorem envelope_product (good : Nat → Bool) (u : Nat → Nat) (p q : Nat)
    (hmono : ∀ k, u (k + 1) ≤ u k)
    (hgood : ∀ k, good k = true → p * u (k + 1) ≤ q * u k) (k : Nat) :
    p ^ goodCount good k * u k ≤ q ^ goodCount good k * u 0 := by
  induction k with
  | zero => simp [goodCount]
  | succ k ih =>
    cases hg : good k with
    | false =>
      simp only [goodCount, hg, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (hmono k)) ih
    | true =>
      simp only [goodCount, hg, ↓reduceIte, Nat.pow_succ]
      calc
        p ^ goodCount good k * p * u (k + 1)
            = p ^ goodCount good k * (p * u (k + 1)) := by ac_rfl
        _ ≤ p ^ goodCount good k * (q * u k) :=
          Nat.mul_le_mul_left _ (hgood k hg)
        _ = q * (p ^ goodCount good k * u k) := by ac_rfl
        _ ≤ q * (q ^ goodCount good k * u 0) := Nat.mul_le_mul_left q ih
        _ = q ^ goodCount good k * q * u 0 := by ac_rfl

/-- Any retained positive tail must fit in the product budget. -/
theorem tail_product (good : Nat → Bool) (u : Nat → Nat) (p q tail k : Nat)
    (hmono : ∀ i, u (i + 1) ≤ u i)
    (hgood : ∀ i, good i = true → p * u (i + 1) ≤ q * u i)
    (htail : tail ≤ u k) :
    p ^ goodCount good k * tail ≤ q ^ goodCount good k * u 0 := by
  exact Nat.le_trans (Nat.mul_le_mul_left _ htail)
    (envelope_product good u p q hmono hgood k)

/-- This applies directly to the fixed-cutoff integer certificate arrays. -/
theorem exit_tail_product (good : Nat → Bool) (u loss : Nat → Nat)
    (q h tail k : Nat)
    (hdecr : ∀ i, u (i + 1) + loss i ≤ u i)
    (htest : ∀ i, good i = true → h * u i ≤ (q + h) * loss i)
    (htail : tail ≤ u k) :
    (q + h) ^ goodCount good k * tail ≤ q ^ goodCount good k * u 0 := by
  apply tail_product good u (q + h) q tail k
  · intro i
    have := hdecr i
    omega
  · intro i hi
    exact contraction_of_exit q h (u i) (u (i + 1)) (loss i)
      (hdecr i) (htest i hi)
  · exact htail

theorem positive_success_decreases (p q u next : Nat)
    (hp : q < p) (hu : 0 < u) (hs : p * next ≤ q * u) : next < u := by
  have hstrict : q * u < p * u := Nat.mul_lt_mul_of_pos_right hp hu
  by_cases hn : next < u
  · exact hn
  · have hweak : u ≤ next := by omega
    have hmul := Nat.mul_le_mul_left p hweak
    omega

/-- At a fixed integer scale, a positive envelope permits finitely many successes.
    The product bound above is usually much stronger than this linear bound. -/
theorem good_count_plus_envelope (good : Nat → Bool) (u : Nat → Nat) (p q : Nat)
    (hp : q < p) (hpos : ∀ k, 0 < u k)
    (hmono : ∀ k, u (k + 1) ≤ u k)
    (hgood : ∀ k, good k = true → p * u (k + 1) ≤ q * u k) (k : Nat) :
    goodCount good k + u k ≤ u 0 := by
  induction k with
  | zero => simp [goodCount]
  | succ k ih =>
    cases hg : good k with
    | false =>
      simp only [goodCount, hg, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have := hmono k
      omega
    | true =>
      simp only [goodCount, hg, ↓reduceIte]
      have := positive_success_decreases p q (u k) (u (k + 1)) hp (hpos k)
        (hgood k hg)
      omega

theorem fixed_tail_good_count (good : Nat → Bool) (u : Nat → Nat)
    (p q tail : Nat) (hp : q < p) (ht : 0 < tail)
    (hfloor : ∀ k, tail ≤ u k) (hmono : ∀ k, u (k + 1) ≤ u k)
    (hgood : ∀ k, good k = true → p * u (k + 1) ≤ q * u k) (k : Nat) :
    goodCount good k ≤ u 0 - tail := by
  have hpos : ∀ i, 0 < u i := by intro i; have := hfloor i; omega
  have := good_count_plus_envelope good u p q hp hpos hmono hgood k
  have := hfloor k
  omega

#print axioms contraction_of_exit
#print axioms envelope_product
#print axioms tail_product
#print axioms exit_tail_product
#print axioms positive_success_decreases
#print axioms good_count_plus_envelope
#print axioms fixed_tail_good_count

end ExitCertificateBudget
