/-
  Arithmetic for the square-root count-return clock estimate.
  Probability, Green-function interpretation, and real energy estimates
  are WRITTEN in docs/COUNT-RETURN-CLOCK.md, not fully formalized here.
-/
import Std

namespace CountReturnClock

theorem odd_power_mod_eight (u : Nat) (hu : u % 2 = 1) :
    3 ^ u % 8 = 3 := by
  have he : u = 2 * (u / 2) + 1 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

theorem odd_exponent_cofactor (u : Nat) (hu : u % 2 = 1) :
    ∃ q : Nat, q % 2 = 1 ∧ 3 ^ u = 1 + 2 * q := by
  have hm := odd_power_mod_eight u hu
  refine ⟨4 * (3 ^ u / 8) + 1, ?_, ?_⟩ <;> omega

theorem first_square_cofactor (n : Nat) (hn : n % 8 = 3) :
    ∃ q : Nat, q % 2 = 1 ∧ n ^ 2 = 1 + 8 * q := by
  let k := n / 8
  have he : n = 8 * k + 3 := by dsimp [k]; omega
  refine ⟨8 * k * k + 6 * k + 1, ?_, ?_⟩
  · simp [Nat.add_mod, Nat.mul_mod]
  · rw [he]; grind

theorem square_cofactor_step (e q n : Nat) (he : 2 ≤ e)
    (hq : q % 2 = 1) (hn : n = 1 + 2 ^ e * q) :
    ∃ Q : Nat, Q % 2 = 1 ∧ n ^ 2 = 1 + 2 ^ (e + 1) * Q := by
  have hp : 2 ^ e = 4 * 2 ^ (e - 2) := by
    calc
      2 ^ e = 2 ^ ((e - 2) + 2) := by congr 1; omega
      _ = 2 ^ (e - 2) * 4 := by rw [Nat.pow_add]
      _ = 4 * 2 ^ (e - 2) := by ac_rfl
  refine ⟨q + 2 * 2 ^ (e - 2) * q * q, ?_, ?_⟩
  · simp [Nat.add_mod, Nat.mul_mod, hq]
  · rw [hn, Nat.pow_succ 2 e, hp]
    grind

/-- Exact odd cofactor for every even exponent, stated via its binary factor. -/
theorem dyadic_exponent_cofactor (j u : Nat) (hu : u % 2 = 1) :
    ∃ q : Nat, q % 2 = 1 ∧
      3 ^ (2 ^ (j + 1) * u) = 1 + 2 ^ (j + 3) * q := by
  induction j with
  | zero =>
    have hh := first_square_cofactor (3 ^ u) (odd_power_mod_eight u hu)
    have he : 3 ^ (2 ^ (0 + 1) * u) = (3 ^ u) ^ 2 := by
      rw [← Nat.pow_mul]
      congr 1
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      ac_rfl
    simpa only [he] using hh
  | succ j ih =>
    obtain ⟨q, hq, hn⟩ := ih
    have hh := square_cofactor_step (j + 3) q (3 ^ (2 ^ (j + 1) * u))
      (by omega) hq hn
    have he : 3 ^ (2 ^ (j + 1 + 1) * u) = (3 ^ (2 ^ (j + 1) * u)) ^ 2 := by
      rw [← Nat.pow_mul, Nat.pow_succ 2 (j + 1)]
      congr 1
      ac_rfl
    simpa only [he, show j + 3 + 1 = j + 1 + 3 by omega] using hh

theorem odd_cofactor_not_next_power (e q : Nat) (hq : q % 2 = 1) :
    ¬ 2 ^ (e + 1) ∣ 2 ^ e * q := by
  rw [Nat.pow_succ, Nat.mul_dvd_mul_iff_left (Nat.pow_pos (by decide))]
  rw [Nat.dvd_iff_mod_eq_zero]
  omega

/-- Sum of floor(n/2^r), r >= 1; the valuation-mass interpretation is written. -/
def halveMass (n : Nat) : Nat :=
  if n = 0 then 0 else n / 2 + halveMass (n / 2)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem halve_mass_zero : halveMass 0 = 0 := by rw [halveMass]; decide

theorem halve_mass_rec (n : Nat) (hn : 0 < n) :
    halveMass n = n / 2 + halveMass (n / 2) := by
  rw [halveMass, if_neg (by omega)]

theorem halve_mass_lt (n : Nat) (hn : 0 < n) : halveMass n < n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [halve_mass_rec n hn]
    by_cases hz : n / 2 = 0
    · rw [hz, halve_mass_zero]; omega
    · have hh := ih (n / 2) (Nat.div_lt_self hn (by decide)) (by omega)
      omega

theorem halve_mass_le (n : Nat) : halveMass n ≤ n := by
  by_cases hz : n = 0
  · subst n; rw [halve_mass_zero]; omega
  · have hh := halve_mass_lt n (by omega); omega

/-- Sum of the holding-time bounds v_2(3^d-1)+2 for 1 <= d <= n. -/
def costMass (n : Nat) : Nat := 3 * n + n / 2 + halveMass n

theorem cost_mass_bound (n : Nat) : 2 * costMass n ≤ 9 * n := by
  have hh := halve_mass_le n
  unfold costMass
  omega

/-- K times the Green function from state one on the interval [0,K]. -/
def greenNumerator (K j : Nat) : Nat :=
  if j = 0 ∨ K ≤ j then 0 else 2 * (K - j)

theorem green_boundaries (K : Nat) :
    greenNumerator K 0 = 0 ∧ greenNumerator K K = 0 := by
  simp [greenNumerator]

theorem green_equation (K j : Nat) (hj : 0 < j) (hK : j < K) :
    2 * greenNumerator K j =
      greenNumerator K (j - 1) + greenNumerator K (j + 1) +
        (if j = 1 then 2 * K else 0) := by
  unfold greenNumerator
  split <;> split <;> split <;> split <;> omega

theorem green_cap (K j : Nat) : greenNumerator K j ≤ 2 * K := by
  unfold greenNumerator
  split <;> omega

theorem stopped_clock_budget (K : Nat) (hK : 0 < K) :
    1 + 2 * costMass (K - 1) ≤ 9 * K - 8 := by
  have hh := cost_mass_bound (K - 1)
  omega

#print axioms odd_power_mod_eight
#print axioms odd_exponent_cofactor
#print axioms first_square_cofactor
#print axioms square_cofactor_step
#print axioms dyadic_exponent_cofactor
#print axioms odd_cofactor_not_next_power
#print axioms halve_mass_zero
#print axioms halve_mass_rec
#print axioms halve_mass_lt
#print axioms halve_mass_le
#print axioms cost_mass_bound
#print axioms green_boundaries
#print axioms green_equation
#print axioms green_cap
#print axioms stopped_clock_budget

end CountReturnClock
