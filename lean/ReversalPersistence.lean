/-
  Long persistence of an actual reversed downward refinement.
  Finite endpoint bounds are kernel proofs. Real weighted conclusions
  and summation over offsets are stated separately in the written note.
-/
import OrderedWeightDrift

namespace ReversalPersistence
open CollatzAffine CoalescenceTail EscapeWeightRefinements OrderedWeightDrift

/-- Integer form of W_h(x) >= 3x/(3x+2^h-1). -/
theorem reciprocal_retention : ∀ h x,
    3 * (2 ^ h * orbit h x) + 3 ^ wt h x ≤
      3 ^ wt h x * (3 * x + 2 ^ h)
  | 0, x => by simp [orbit, wt]
  | h + 1, x => by
    have ih := reciprocal_retention h (U x)
    have hh := Nat.mul_le_mul_left 2 ih
    have hp : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    have hm := Nat.mul_le_mul_left (3 ^ wt h (U x)) hp
    by_cases ho : x % 2 = 1
    · have hs : 2 * U x = 3 * x + 1 := by simp [U, ho]; omega
      have he := congrArg (fun z => 3 ^ wt h (U x) * (3 * z)) hs
      simp only [Nat.mul_add, Nat.mul_one] at hh he hm
      simp only [orbit, wt, ho, Nat.pow_add, Nat.pow_succ]
      have e1 : 3 * (2 ^ h * 2 * orbit h (U x)) =
          2 * (3 * (2 ^ h * orbit h (U x))) := by ac_rfl
      have e2 : 3 * 3 ^ wt h (U x) * (3 * x + 2 ^ h * 2) =
          3 ^ wt h (U x) * (3 * (3 * x)) +
            6 * (3 ^ wt h (U x) * 2 ^ h) := by
        rw [show 6 = 3 * 2 from rfl]
        simp only [Nat.mul_add]; ac_rfl
      rw [e1, e2]
      have e3 : 3 ^ wt h (U x) * (3 * (2 * U x)) =
          2 * (3 ^ wt h (U x) * (3 * U x)) := by ac_rfl
      rw [e3] at he
      omega
    · have heven : x % 2 = 0 := by omega
      have hs : 2 * U x = x := by simp [U, ho]; omega
      have he := congrArg (fun z => 3 ^ wt h (U x) * (3 * z)) hs
      simp only [Nat.mul_add] at hh
      simp only [orbit, wt, heven, Nat.zero_add, Nat.pow_succ]
      have e1 : 3 * (2 ^ h * 2 * orbit h (U x)) =
          2 * (3 * (2 ^ h * orbit h (U x))) := by ac_rfl
      have e2 : 3 ^ wt h (U x) * (3 * x + 2 ^ h * 2) =
          3 ^ wt h (U x) * (3 * x) +
            2 * (3 ^ wt h (U x) * 2 ^ h) := by
        simp only [Nat.mul_add]; ac_rfl
      have e3 : 3 ^ wt h (U x) * (3 * (2 * U x)) =
          2 * (3 ^ wt h (U x) * (3 * U x)) := by ac_rfl
      rw [e3] at he
      rw [e1, e2]
      omega

/-- Integer form of z_h(x) >= 1/(x+2^h). -/
theorem shifted_retention : ∀ h x,
    2 ^ h * (orbit h x + 1) ≤ 3 ^ wt h x * (x + 2 ^ h)
  | 0, x => by simp [orbit, wt]
  | h + 1, x => by
    have ih := Nat.mul_le_mul_left 2 (shifted_retention h (U x))
    have hp : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    have hm := Nat.mul_le_mul_left (3 ^ wt h (U x)) hp
    have e1 : 2 * (2 ^ h * (orbit h (U x) + 1)) =
        2 ^ h * 2 * (orbit h (U x) + 1) := by ac_rfl
    rw [e1] at ih
    by_cases ho : x % 2 = 1
    · have hs : 2 * U x = 3 * x + 1 := by simp [U, ho]; omega
      have he := congrArg (fun z => 3 ^ wt h (U x) * z) hs
      have e0 : 2 * (3 ^ wt h (U x) * (U x + 2 ^ h)) =
          2 * (3 ^ wt h (U x) * U x) + 2 * (3 ^ wt h (U x) * 2 ^ h) := by
        simp only [Nat.mul_add]
      rw [e0] at ih
      simp only [Nat.mul_add, Nat.mul_one] at he hm
      simp only [orbit, wt, ho, Nat.pow_add, Nat.pow_succ]
      have e2 : 3 * 3 ^ wt h (U x) * (x + 2 ^ h * 2) =
          3 ^ wt h (U x) * (3 * x) +
            6 * (3 ^ wt h (U x) * 2 ^ h) := by
        rw [show 6 = 3 * 2 from rfl]
        simp only [Nat.mul_add]; ac_rfl
      have e3 : 3 ^ wt h (U x) * (2 * U x) =
          2 * (3 ^ wt h (U x) * U x) := by ac_rfl
      rw [e3] at he
      rw [e2]
      omega
    · have heven : x % 2 = 0 := by omega
      have hs : 2 * U x = x := by simp [U, ho]; omega
      simp only [orbit, wt, heven, Nat.zero_add, Nat.pow_succ]
      calc
        2 ^ h * 2 * (orbit h (U x) + 1) ≤
            2 * (3 ^ wt h (U x) * (U x + 2 ^ h)) := ih
        _ = 3 ^ wt h (U x) * (2 * U x + 2 ^ h * 2) := by
          simp only [Nat.mul_add]; ac_rfl
        _ = 3 ^ wt h (U x) * (x + 2 ^ h * 2) := by rw [hs]

theorem half_value_arithmetic {r q f v g : Nat}
    (h1 : 3 * r + q ≤ 3 * f + v) (h2 : 4 * v ≤ f)
    (h3 : 4 * f = g + q) (h4 : 26 * q ≤ g) :
    32 * r ≤ 9 * g := by omega

/-- Cross multiplication of the lower bound P_h >= 1/2 for our family. -/
theorem retained_half {h x A : Nat}
    (hA : 26 ≤ A) (hx : 4 * x = A + 1) (hh : 4 * 2 ^ h ≤ x) :
    32 * (2 ^ h * orbit h x) ≤ 9 * A * 3 ^ wt h x := by
  let q := 3 ^ wt h x
  have h1 : 3 * (2 ^ h * orbit h x) + q ≤ 3 * (q * x) + q * 2 ^ h := by
    have he : q * (3 * x + 2 ^ h) = 3 * (q * x) + q * 2 ^ h := by
      simp only [Nat.mul_add]; ac_rfl
    rw [← he]
    exact reciprocal_retention h x
  have h2 : 4 * (q * 2 ^ h) ≤ q * x := by
    calc
      4 * (q * 2 ^ h) = q * (4 * 2 ^ h) := by ac_rfl
      _ ≤ q * x := Nat.mul_le_mul_left q hh
  have h3 : 4 * (q * x) = q * A + q := by
    calc
      4 * (q * x) = q * (4 * x) := by ac_rfl
      _ = q * A + q := by rw [hx, Nat.mul_add, Nat.mul_one]
  have h4 : 26 * q ≤ q * A := by
    calc
      26 * q = q * 26 := by ac_rfl
      _ ≤ q * A := Nat.mul_le_mul_left q hA
  have hh := half_value_arithmetic h1 h2 h3 h4
  have he : 9 * (q * A) = 9 * A * 3 ^ wt h x := by dsimp [q]; ac_rfl
  simpa only [he] using hh

theorem family_horizon {m h : Nat} (hh : h ≤ 6 * m + 1) :
    4 * 2 ^ h ≤ (3 ^ (6 * m + 5) + 1) / 4 := by
  have he : 16 * 2 ^ h = 2 ^ (h + 4) := by
    rw [Nat.pow_add]; simp [Nat.mul_comm]
  have hpow : 2 ^ (h + 4) ≤ 2 ^ (6 * m + 5) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hbase : 2 ^ (6 * m + 5) ≤ 3 ^ (6 * m + 5) :=
    Nat.pow_le_pow_left (by decide) _
  rw [← he] at hpow
  omega

theorem family_persistent_half (m h : Nat) (hh : h ≤ 6 * m + 1) :
    let n := 8 * familySeed (2 * m + 1)
    2 ^ (h + 5) * orbit (12 * m + 17 + h) n ≤
      3 ^ wt (12 * m + 17 + h) n := by
  dsimp
  have hc := family_even_clock m
  dsimp at hc
  rw [orbit_add, weight_add, hc.1, hc.2.1]
  have hA : 26 ≤ 3 ^ (6 * m + 5) := by
    have hh : 3 ^ 5 ≤ 3 ^ (6 * m + 5) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hx : 4 * ((3 ^ (6 * m + 5) + 1) / 4) = 3 ^ (6 * m + 5) + 1 := by
    have hp := odd_power_mod_eight m
    omega
  have hr := retained_half hA hx (family_horizon hh)
  have e1 : 2 ^ (h + 5) = 32 * 2 ^ h := by rw [Nat.pow_add]; simp [Nat.mul_comm]
  have e2 : 3 ^ (6 * m + 7 + wt h ((3 ^ (6 * m + 5) + 1) / 4)) =
      9 * 3 ^ (6 * m + 5) * 3 ^ wt h ((3 ^ (6 * m + 5) + 1) / 4) := by
    rw [show 6 * m + 7 = (6 * m + 5) + 2 by omega, Nat.pow_add, Nat.pow_add]
    simp [Nat.mul_comm]
  rw [e1, e2, Nat.mul_assoc]
  exact hr

theorem family_child_ceiling (m h : Nat) :
    let n := 8 * familySeed (2 * m + 1)
    3 ^ (1 + wt (12 * m + 17 + h) (3 * n + 2)) ≤
      27 * (2 ^ h * orbit (12 * m + 17 + h) (3 * n + 2)) := by
  dsimp
  have hc := family_even_clock m
  dsimp at hc
  rw [orbit_add, weight_add, hc.2.2.1, hc.2.2.2.1]
  have he : 3 ^ (1 + (2 + wt h 1)) = 27 * 3 ^ wt h 1 := by
    rw [show 1 + (2 + wt h 1) = 3 + wt h 1 by omega, Nat.pow_add]
  rw [he]
  have hh := Nat.mul_le_mul_left 27 (coefficient_lower_bound h 1)
  simpa only [Nat.mul_one] using hh

theorem family_reversal_persists (m h : Nat) :
    ¬Ordered (12 * m + 18 + h) (8 * familySeed (2 * m + 1)) := by
  intro ho
  apply family_even_reversed m
  intro i hi ht
  exact ho i hi (by omega)

#print axioms reciprocal_retention
#print axioms shifted_retention
#print axioms half_value_arithmetic
#print axioms retained_half
#print axioms family_horizon
#print axioms family_persistent_half
#print axioms family_child_ceiling
#print axioms family_reversal_persists

end ReversalPersistence
