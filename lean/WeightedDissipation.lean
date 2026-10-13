/-
  Exact integer certificates for the relative +1 correction of ordinary
  Collatz.  No infinite product, density limit, or convergence theorem
  is asserted in this module.
-/
import CollatzContradiction

namespace WeightedDissipation
open OrdinaryCollatz

def numerator : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, n => if n % 2 = 1 then 3 * n * numerator k (C n)
                else numerator k (C n)

def denominator : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, n => if n % 2 = 1 then (3 * n + 1) * denominator k (C n)
                else denominator k (C n)

/-- Common-denominator sum of the lost weights, with visits counted
    separately even when a trajectory repeats a state. -/
def loss : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n % 2 = 1 then denominator k (C n) + 3 * n * loss k (C n)
                else loss k (C n)

def slopeNumerator : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, n => (if n % 2 = 1 then 3 else 1) * slopeNumerator k (C n)

def slopeDenominator : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, n => (if n % 2 = 1 then 1 else 2) * slopeDenominator k (C n)

theorem denominator_positive (k n : Nat) : 0 < denominator k n := by
  induction k generalizing n with
  | zero => simp [denominator]
  | succ k ih =>
    simp only [denominator]
    split
    · exact Nat.mul_pos (by omega) (ih _)
    · exact ih _

theorem numerator_positive (k n : Nat) : 0 < numerator k n := by
  induction k generalizing n with
  | zero => simp [numerator]
  | succ k ih =>
    simp only [numerator]
    split
    · rename_i ho
      exact Nat.mul_pos (by omega) (ih _)
    · exact ih _

theorem conservation (k n : Nat) : numerator k n + loss k n = denominator k n := by
  induction k generalizing n with
  | zero => simp [numerator, loss, denominator]
  | succ k ih =>
    by_cases ho : n % 2 = 1
    · simp only [numerator, loss, denominator, if_pos ho]
      calc
        3 * n * numerator k (C n) +
            (denominator k (C n) + 3 * n * loss k (C n)) =
            3 * n * (numerator k (C n) + loss k (C n)) + denominator k (C n) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]
        _ = (3 * n + 1) * denominator k (C n) := by rw [ih]; simp [Nat.add_mul]
    · simpa only [numerator, loss, denominator, if_neg ho] using ih (C n)

theorem numerator_le_denominator (k n : Nat) : numerator k n ≤ denominator k n := by
  have := conservation k n
  omega

theorem numerator_add (s t n : Nat) :
    numerator (s + t) n = numerator s n * numerator t (iterate s n) := by
  induction s generalizing n with
  | zero => simp [numerator, iterate]
  | succ s ih =>
    have he : s + 1 + t = (s + t) + 1 := by omega
    rw [he]
    by_cases ho : n % 2 = 1 <;>
      simp [numerator, iterate, ho, ih, Nat.mul_assoc]

theorem denominator_add (s t n : Nat) :
    denominator (s + t) n = denominator s n * denominator t (iterate s n) := by
  induction s generalizing n with
  | zero => simp [denominator, iterate]
  | succ s ih =>
    have he : s + 1 + t = (s + t) + 1 := by omega
    rw [he]
    by_cases ho : n % 2 = 1 <;>
      simp [denominator, iterate, ho, ih, Nat.mul_assoc]

theorem loss_add (s t n : Nat) :
    loss (s + t) n = loss s n * denominator t (iterate s n) +
                      numerator s n * loss t (iterate s n) := by
  have h := conservation (s + t) n
  rw [numerator_add, denominator_add] at h
  have he : numerator s n * numerator t (iterate s n) +
      (loss s n * denominator t (iterate s n) +
       numerator s n * loss t (iterate s n)) =
        denominator s n * denominator t (iterate s n) := by
    calc
      _ = numerator s n * (numerator t (iterate s n) + loss t (iterate s n)) +
            loss s n * denominator t (iterate s n) := by
              simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]
      _ = (numerator s n + loss s n) * denominator t (iterate s n) := by
              rw [conservation]; simp [Nat.add_mul]
      _ = _ := by rw [conservation]
  omega

theorem loss_zero_iff (k n : Nat) :
    loss k n = 0 ↔ ∀ j, j < k → iterate j n % 2 = 0 := by
  induction k generalizing n with
  | zero => simp [loss]
  | succ k ih =>
    by_cases ho : n % 2 = 1
    · have hd := denominator_positive k (C n)
      constructor
      · intro hz
        simp only [loss, if_pos ho] at hz
        omega
      · intro he
        have := he 0 (by omega)
        change n % 2 = 0 at this
        omega
    · simp only [loss, if_neg ho]
      rw [ih]
      constructor
      · intro ht j hj
        cases j with
        | zero => change n % 2 = 0; omega
        | succ j => exact ht j (by omega)
      · intro ht j hj
        exact ht (j + 1) (by omega)

theorem loss_positive_of_odd_visit {k n j : Nat}
    (hj : j < k) (ho : iterate j n % 2 = 1) : 0 < loss k n := by
  by_cases hz : loss k n = 0
  · have := (loss_zero_iff k n).mp hz j hj
    omega
  · omega

theorem all_even_nonincreasing {k n : Nat}
    (he : ∀ j, j < k → iterate j n % 2 = 0) : iterate k n ≤ n := by
  induction k generalizing n with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have ht : ∀ j, j < k → iterate j (C n) % 2 = 0 := by
      intro j hj
      exact he (j + 1) (by omega)
    have hb := ih ht
    have hn := he 0 (by omega)
    change n % 2 = 0 at hn
    have hc : C n = n / 2 := by unfold C; rw [if_neg (by omega : ¬ n % 2 = 1)]
    change iterate k (C n) ≤ n
    have hcn : C n ≤ n := by rw [hc]; omega
    exact Nat.le_trans hb hcn

theorem positive_return_has_odd {k n : Nat} (hk : 0 < k) (hn : 0 < n)
    (hr : iterate k n = n) : ∃ j, j < k ∧ iterate j n % 2 = 1 := by
  classical
  apply Classical.byContradiction
  intro h
  have he : ∀ j, j < k → iterate j n % 2 = 0 := by
    intro j hj
    have hno : ¬ iterate j n % 2 = 1 := by intro ho; exact h ⟨j, hj, ho⟩
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have ht : ∀ j, j < t → iterate j (C n) % 2 = 0 := by
    intro j hj
    exact he (j + 1) (by omega)
  have hb := all_even_nonincreasing ht
  have ho := he 0 (by omega)
  change n % 2 = 0 at ho
  have hc : C n = n / 2 := by unfold C; rw [if_neg (by omega : ¬ n % 2 = 1)]
  change iterate t (C n) = n at hr
  rw [hr, hc] at hb
  omega

theorem cycle_loss_positive {k n : Nat} (hk : 0 < k) (hn : 0 < n)
    (hr : iterate k n = n) : 0 < loss k n := by
  obtain ⟨j, hj, ho⟩ := positive_return_has_odd hk hn hr
  exact loss_positive_of_odd_visit hj ho

theorem cycle_weight_strict {k n : Nat} (hk : 0 < k) (hn : 0 < n)
    (hr : iterate k n = n) : numerator k n < denominator k n := by
  have := cycle_loss_positive hk hn hr
  have := conservation k n
  omega

theorem affine_product (k n : Nat) :
    denominator k n * slopeNumerator k n * n =
      numerator k n * slopeDenominator k n * iterate k n := by
  induction k generalizing n with
  | zero => simp [denominator, numerator, slopeNumerator, slopeDenominator, iterate]
  | succ k ih =>
    by_cases ho : n % 2 = 1
    · have hc : C n = 3 * n + 1 := by simp [C, ho]
      have ht := congrArg (fun z => 3 * n * z) (ih (C n))
      simp only [denominator, numerator, slopeNumerator, slopeDenominator, iterate,
        if_pos ho]
      simpa [hc, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht
    · have hc : C n = n / 2 := by simp [C, ho]
      have he : n = 2 * C n := by rw [hc]; omega
      have ht := congrArg (fun z => 2 * z) (ih (C n))
      simp only [denominator, numerator, slopeNumerator, slopeDenominator, iterate,
        if_neg ho, Nat.one_mul]
      calc
        _ = denominator k (C n) * slopeNumerator k (C n) * (2 * C n) :=
              congrArg (fun z => denominator k (C n) * slopeNumerator k (C n) * z) he
        _ = _ := by simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using ht

theorem cycle_slope_weight {k n : Nat} (hn : 0 < n)
    (hr : iterate k n = n) :
    denominator k n * slopeNumerator k n = numerator k n * slopeDenominator k n := by
  have h := affine_product k n
  rw [hr] at h
  exact Nat.eq_of_mul_eq_mul_right hn h

theorem repeated_return {k n : Nat} (hr : iterate k n = n) (m : Nat) :
    iterate (k * m) n = n := by
  induction m with
  | zero => simp [iterate]
  | succ m ih => rw [Nat.mul_succ, iterate_add, ih, hr]

theorem cycle_numerator_power {k n : Nat} (hr : iterate k n = n) (m : Nat) :
    numerator (k * m) n = numerator k n ^ m := by
  induction m with
  | zero => simp [numerator]
  | succ m ih => rw [Nat.mul_succ, numerator_add, repeated_return hr, ih, Nat.pow_succ]

theorem cycle_denominator_power {k n : Nat} (hr : iterate k n = n) (m : Nat) :
    denominator (k * m) n = denominator k n ^ m := by
  induction m with
  | zero => simp [denominator]
  | succ m ih => rw [Nat.mul_succ, denominator_add, repeated_return hr, ih, Nat.pow_succ]

theorem known_cycle_weights :
    numerator 3 1 = 3 ∧ denominator 3 1 = 4 ∧ loss 3 1 = 1 ∧
      slopeNumerator 3 1 = 3 ∧ slopeDenominator 3 1 = 4 := by decide

end WeightedDissipation

#print axioms WeightedDissipation.conservation
#print axioms WeightedDissipation.numerator_positive
#print axioms WeightedDissipation.denominator_positive
#print axioms WeightedDissipation.numerator_le_denominator
#print axioms WeightedDissipation.numerator_add
#print axioms WeightedDissipation.denominator_add
#print axioms WeightedDissipation.loss_add
#print axioms WeightedDissipation.loss_zero_iff
#print axioms WeightedDissipation.loss_positive_of_odd_visit
#print axioms WeightedDissipation.positive_return_has_odd
#print axioms WeightedDissipation.cycle_loss_positive
#print axioms WeightedDissipation.cycle_weight_strict
#print axioms WeightedDissipation.affine_product
#print axioms WeightedDissipation.cycle_slope_weight
#print axioms WeightedDissipation.repeated_return
#print axioms WeightedDissipation.cycle_numerator_power
#print axioms WeightedDissipation.cycle_denominator_power
#print axioms WeightedDissipation.known_cycle_weights
