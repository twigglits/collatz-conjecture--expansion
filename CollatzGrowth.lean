/-
  Arbitrarily long initial growth for the ordinary Collatz shortcut map.
  This rules out a uniform finite horizon for descent; it does NOT give
  an infinite divergent positive-integer orbit.
  Check: lean +leanprover/lean4:v4.31.0 CollatzGrowth.lean
-/

namespace CollatzGrowth

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbit k (U n)

theorem pow_pos (a k : Nat) (ha : 0 < a) : 0 < a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simpa [Nat.pow_succ] using Nat.mul_pos ih ha

theorem step_predecessor (x : Nat) (hx : 0 < x) :
    U (2 * x - 1) = 3 * x - 1 := by
  have hp : (2 * x - 1) % 2 = 1 := by omega
  simp only [U, hp, if_true]
  omega

/-- A closed formula, universally quantified in prefix length and seed. -/
theorem growth_formula (k m q : Nat) (hq : 0 < q) :
    orbit k (2 ^ (k + m) * q - 1) = 2 ^ m * 3 ^ k * q - 1 := by
  induction k generalizing q with
  | zero => simp [orbit]
  | succ k ih =>
    have hp : 0 < 2 ^ (k + m) * q := Nat.mul_pos (pow_pos 2 (k+m) (by decide)) hq
    have he : 2 ^ (k + 1 + m) * q = 2 * (2 ^ (k + m) * q) := by
      rw [show k + 1 + m = (k + m) + 1 by omega, Nat.pow_succ]
      simp [Nat.mul_comm, Nat.mul_left_comm]
    simp only [orbit, he, step_predecessor _ hp]
    have he' : 3 * (2 ^ (k + m) * q) = 2 ^ (k + m) * (3 * q) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    rw [he', ih (3*q) (by omega)]
    simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- Every prefix up to k stays at least as large as the start 2^(k+1)-1. -/
theorem growth_prefix (k j : Nat) (hj : j ≤ k) :
    2 ^ (k + 1) - 1 ≤ orbit j (2 ^ (k + 1) - 1) := by
  have he : j + (k + 1 - j) = k + 1 := by omega
  have hf := growth_formula j (k + 1 - j) 1 (by decide)
  simp only [he, Nat.mul_one] at hf
  rw [hf]
  have hl : 2 ^ j ≤ 3 ^ j := Nat.pow_le_pow_left (by decide) j
  have hmul := Nat.mul_le_mul_left (2 ^ (k + 1 - j)) hl
  have hpow : 2 ^ (k + 1 - j) * 2 ^ j = 2 ^ (k + 1) := by
    rw [← Nat.pow_add, show k + 1 - j + j = k + 1 by omega]
  rw [hpow] at hmul
  omega

/-- No single finite number of shortcut steps guarantees descent for all n>1. -/
theorem no_uniform_descent_horizon :
    ∀ k : Nat, ∃ n : Nat, 1 < n ∧ ∀ j : Nat, j ≤ k → n ≤ orbit j n := by
  intro k
  refine ⟨2 ^ (k + 2) - 1, ?_, ?_⟩
  · have hh : (2:Nat)^2 ≤ 2^(k+2) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh' : 4 ≤ 2^(k+2) := hh
    omega
  · intro j hj
    exact growth_prefix (k+1) j (by omega)

/-- Compatible residues -1 modulo every power of two contain no natural number.
    Finite growing prefixes therefore cannot be passed to a positive-integer
    limit by swapping `for every k, some n` with `some n, for every k`. -/
theorem no_natural_all_ones (n : Nat) : ¬ (∀ k : Nat, 2 ^ k ∣ n + 1) := by
  intro h
  have hd : 2 ^ (n + 1) ≤ n + 1 := Nat.le_of_dvd (by omega) (h (n+1))
  have hl : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

#print axioms growth_formula
#print axioms growth_prefix
#print axioms no_uniform_descent_horizon
#print axioms no_natural_all_ones

end CollatzGrowth
