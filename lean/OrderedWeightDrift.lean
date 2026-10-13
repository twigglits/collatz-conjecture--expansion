/-
  Shifted reciprocal weights before reversal of adjacent odd-count order.
  These finite identities support a written Cesaro bound for one part of
  the actual refinement drift. The post-reversal contribution is open.
-/
import EscapeWeightRefinements

namespace OrderedWeightDrift
open CollatzAffine CoalescenceTail EscapeWeightRefinements

theorem shifted_step (n : Nat) :
    U n + 1 = 3 ^ (n % 2) * (n / 2 + 1) := by
  by_cases h : n % 2 = 1
  · simp [U, h]; omega
  · have he : n % 2 = 0 := by omega
    simp [U, he]

theorem halving_order {x y p : Nat} (h : y + 1 ≤ p * (x + 1)) :
    y / 2 + 1 ≤ p * (x / 2 + 1) := by
  have hx : x + 1 ≤ 2 * (x / 2 + 1) := by omega
  have hm := Nat.mul_le_mul_left p hx
  have he : p * (2 * (x / 2 + 1)) = 2 * (p * (x / 2 + 1)) := by ac_rfl
  rw [he] at hm
  omega

theorem shifted_order_step {x y d e : Nat}
    (h : y + 1 ≤ 3 ^ d * (x + 1))
    (he : e + x % 2 = d + y % 2) :
    U y + 1 ≤ 3 ^ e * (U x + 1) := by
  calc
    U y + 1 = 3 ^ (y % 2) * (y / 2 + 1) := shifted_step y
    _ ≤ 3 ^ (y % 2) * (3 ^ d * (x / 2 + 1)) :=
      Nat.mul_le_mul_left _ (halving_order h)
    _ = 3 ^ (d + y % 2) * (x / 2 + 1) := by rw [Nat.pow_add]; ac_rfl
    _ = 3 ^ (e + x % 2) * (x / 2 + 1) := by rw [he]
    _ = 3 ^ e * (U x + 1) := by rw [shifted_step, Nat.pow_add]; ac_rfl

/-- The odd member's accumulated count has never fallen below the even member's. -/
def Ordered (t n : Nat) : Prop :=
  ∀ i, 1 ≤ i → i ≤ t → wt i (2 * n) ≤ wt i (2 * n + 1)

theorem ordered_shifted_endpoints : ∀ t n, Ordered (t + 1) n →
    orbit (t + 1) (2 * n + 1) + 1 ≤
      3 ^ (wt (t + 1) (2 * n + 1) - wt (t + 1) (2 * n)) *
        (orbit (t + 1) (2 * n) + 1)
  | 0, n, _ => by
    simp [orbit, wt, even_step, odd_step]
    omega
  | t + 1, n, h => by
    have ho : Ordered (t + 1) n := fun i hi ht => h i hi (by omega)
    have ih := ordered_shifted_endpoints t n ho
    have hp := ho (t + 1) (by omega) (by omega)
    have hn := h (t + 1 + 1) (by omega) (by omega)
    rw [weight_snoc (t + 1) (2 * n), weight_snoc (t + 1) (2 * n + 1)] at hn
    have he :
        (wt (t + 1 + 1) (2 * n + 1) - wt (t + 1 + 1) (2 * n)) +
          orbit (t + 1) (2 * n) % 2 =
        (wt (t + 1) (2 * n + 1) - wt (t + 1) (2 * n)) +
          orbit (t + 1) (2 * n + 1) % 2 := by
      rw [weight_snoc (t + 1) (2 * n), weight_snoc (t + 1) (2 * n + 1)]
      omega
    simpa only [orbit_snoc] using shifted_order_step ih he

theorem ordered_cross_product (t n : Nat) (h : Ordered (t + 1) n) :
    3 ^ wt (t + 1) (2 * n) * (orbit (t + 1) (2 * n + 1) + 1) ≤
      3 ^ wt (t + 1) (2 * n + 1) * (orbit (t + 1) (2 * n) + 1) := by
  have hw := h (t + 1) (by omega) (by omega)
  have hm := Nat.mul_le_mul_left (3 ^ wt (t + 1) (2 * n))
    (ordered_shifted_endpoints t n h)
  have he : wt (t + 1) (2 * n) +
      (wt (t + 1) (2 * n + 1) - wt (t + 1) (2 * n)) =
        wt (t + 1) (2 * n + 1) := by omega
  simpa only [← Nat.mul_assoc, ← Nat.pow_add, he] using hm

theorem refinement_shifted_order (t n : Nat) (h : Ordered (t + 1) n) :
    3 ^ wt t n * (orbit t (3 * n + 2) + 1) ≤
      3 ^ (1 + wt t (3 * n + 2)) * (orbit t n + 1) := by
  have hh := ordered_cross_product t n h
  rcases even_refinement t n with ⟨hx, ha⟩
  rcases odd_refinement t n with ⟨hy, hb⟩
  simpa only [hx, ha, hy, hb] using hh

theorem alive_even_count_order : ∀ t n, 0 < t → alive t (2 * n) = true →
    wt t (2 * n) < wt t (2 * n + 1)
  | 0, _, ht, _ => by omega
  | 1, n, _, _ => by simp [wt]
  | t + 2, n, _, h => by
    have hh : alive (t + 1) (2 * n) = true ∧ gap (t + 2) (2 * n) ≠ 0 := by
      simpa only [alive, Bool.and_eq_true, decide_eq_true_eq] using h
    have ih := alive_even_count_order (t + 1) n (by omega) hh.1
    have hn := hh.2
    unfold gap at hn
    rw [weight_snoc (t + 1) (2 * n), weight_snoc (t + 1) (2 * n + 1)] at hn ⊢
    omega

theorem alive_prefix : ∀ t i n, i ≤ t → alive t n = true → alive i n = true
  | 0, i, n, hi, _ => by
    have : i = 0 := by omega
    subst i
    rfl
  | t + 1, i, n, hi, h => by
    by_cases he : i = t + 1
    · simpa [he] using h
    · have hh : alive t n = true ∧ gap (t + 1) n ≠ 0 := by
        simpa only [alive, Bool.and_eq_true, decide_eq_true_eq] using h
      have hp := hh.1
      exact alive_prefix t i n (by omega) hp

theorem first_return_order {t n : Nat} (ht : 0 < t)
    (ha : alive (t - 1) (2 * n) = true)
    (he : wt t (2 * n) = wt t (2 * n + 1)) :
    orbit t (2 * n + 1) ≤ orbit t (2 * n) := by
  have ho : Ordered t n := by
    intro i hi hit
    by_cases hie : i = t
    · simp [hie, he]
    · have hh := alive_prefix (t - 1) i (2 * n) (by omega) ha
      exact Nat.le_of_lt (alive_even_count_order i n (by omega) hh)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  change wt (j + 1) (2 * n) = wt (j + 1) (2 * n + 1) at he
  change orbit (j + 1) (2 * n + 1) ≤ orbit (j + 1) (2 * n)
  have hs := ordered_shifted_endpoints j n ho
  simp only [he, Nat.sub_self, Nat.pow_zero, Nat.one_mul] at hs
  omega

/-- Integer form of (A-B)_+ ≤ A/(X+1) under shifted order. -/
theorem reciprocal_downward_bound {p q x y : Nat}
    (h : p * (y + 1) ≤ q * (x + 1)) :
    (p * y - q * x) * (x + 1) ≤ p * y := by
  by_cases hz : p * y ≤ q * x
  · simp [Nat.sub_eq_zero_of_le hz]
  · have hd : p * y - q * x + q * x = p * y := by omega
    have hm := Nat.mul_le_mul_right x h
    have he : (p * (y + 1)) * x = p * y * x + p * x := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul]
    have he' : (q * (x + 1)) * x = q * x * x + q * x := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul]
    rw [he, he'] at hm
    have hx := congrArg (fun z => z * x) hd
    rw [Nat.add_mul] at hx
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem odd_charge_denominator (x : Nat) : 3 * x + 1 ≤ 3 * (x + 1) := by omega

theorem even_charge_denominator {x : Nat} (hp : 0 < x) (he : x % 2 = 0) :
    x + 2 ≤ 2 * x := by omega

def shiftedCorrection (t n : Nat) : Nat := correction t n + 2 ^ t * scale t n

theorem shifted_orbit_identity (t n : Nat) :
    scale t n * (2 ^ t * (orbit t n + 1)) =
      3 ^ t * n + shiftedCorrection t n := by
  simp only [Nat.mul_add, Nat.mul_one, shiftedCorrection, scaled_orbit_identity]
  ac_rfl

theorem shifted_correction_lift (t q n : Nat) :
    shiftedCorrection t (2 ^ t * q + n) = shiftedCorrection t n := by
  simp only [shiftedCorrection, (data_lift t q n).1, (data_lift t q n).2]

theorem shifted_correction_mass (t : Nat) :
    2 * total (2 ^ t) (shiftedCorrection t) + 6 ^ t = 3 * 8 ^ t := by
  have hm := correction_mass t
  change 2 * total (2 ^ t) (fun n => correction t n + 2 ^ t * scale t n) +
    6 ^ t = 3 * 8 ^ t
  rw [total_sum, total_mul, scale_mass]
  have he : 2 ^ t * 4 ^ t = 8 ^ t := by rw [← Nat.mul_pow]
  rw [he]
  omega

theorem reversal_example :
    orbit 12 74 = 5 ∧ orbit 12 75 = 2 ∧
    wt 12 74 = 5 ∧ wt 12 75 = 4 ∧
    orbit 11 37 = 5 ∧ wt 11 37 = 5 ∧
    orbit 12 37 = 8 ∧ wt 12 37 = 6 ∧
    orbit 13 37 = 4 ∧ wt 13 37 = 6 ∧ orbit 15 37 = 1 ∧
    orbit 13 75 = 1 := by decide

theorem reversed_shifted_order_fails :
    ¬Ordered 12 37 ∧
    3 ^ wt 12 75 * (orbit 12 74 + 1) <
      3 ^ wt 12 74 * (orbit 12 75 + 1) := by
  constructor
  · intro h
    have hh := h 12 (by decide) (by decide)
    have he := reversal_example
    rw [he.2.2.1, he.2.2.2.1] at hh
    omega
  · decide

theorem odd_power_mod_eight (m : Nat) : 3 ^ (6 * m + 5) % 8 = 3 := by
  have he : 6 * m + 5 = 2 * (3 * m + 2) + 1 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul]
  simp [Nat.mul_mod, Nat.pow_mod]

/-- An even-indexed subfamily of the prior fixed-offset jump family. -/
theorem family_even_clock (m : Nat) :
    let n := 8 * familySeed (2 * m + 1)
    let A := 3 ^ (6 * m + 5)
    orbit (12 * m + 17) n = (A + 1) / 4 ∧
    wt (12 * m + 17) n = 6 * m + 7 ∧
    orbit (12 * m + 17) (3 * n + 2) = 1 ∧
    wt (12 * m + 17) (3 * n + 2) = 2 ∧
    ((A + 1) / 4) % 2 = 1 := by
  dsimp
  have hs := family_seed_equation (2 * m + 1)
  have he : 3 * (2 * m + 1) + 2 = 6 * m + 5 := by omega
  rw [he] at hs
  have hc := family_common_clock hs
  have ht : 12 * m + 17 = (2 * (6 * m + 5) + 5) + 2 := by omega
  have hm := odd_power_mod_eight m
  have hh : 3 ^ (6 * m + 5) + 1 = 2 ^ 2 * ((3 ^ (6 * m + 5) + 1) / 4) := by
    omega
  have hd := halving_data 2 ((3 ^ (6 * m + 5) + 1) / 4)
  rw [← hh] at hd
  have htarg : 3 * (8 * familySeed (2 * m + 1)) + 2 =
      24 * familySeed (2 * m + 1) + 2 := by omega
  rw [htarg]
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · rw [ht, orbit_add, hc.1, hd.1]
  · rw [ht, weight_add, hc.1, hc.2.1, hd.2]
  · rw [ht, orbit_add, hc.2.2.1]
    decide
  · rw [ht, weight_add, hc.2.2.1, hc.2.2.2]
    decide

theorem family_even_reversed (m : Nat) :
    ¬Ordered (12 * m + 18) (8 * familySeed (2 * m + 1)) := by
  intro h
  have hh := h (12 * m + 18) (by omega) (by omega)
  have he : 12 * m + 18 = (12 * m + 17) + 1 := by omega
  rw [he, (even_refinement _ _).2, (odd_refinement _ _).2,
    (family_even_clock m).2.1, (family_even_clock m).2.2.2.1] at hh
  omega

/-- Once the unshifted order holds, it persists while the count order does. -/
theorem unshifted_order_step {x y d e : Nat}
    (h : y ≤ 3 ^ d * x) (he : e + x % 2 = d + y % 2) :
    U y ≤ 3 ^ e * U x := by
  have hx := step_equation x
  have hy := step_equation y
  by_cases px : x % 2 = 1
  · by_cases py : y % 2 = 1
    · have hed : e = d := by omega
      subst e
      simp only [px, py, Nat.pow_one] at hx hy
      have hm := congrArg (fun z => 3 ^ d * z) hx
      have hh := Nat.mul_le_mul_left 3 h
      have hp := Nat.pow_pos (by decide : 0 < 3) (n := d)
      simp only [Nat.mul_add, Nat.mul_one] at hm
      have h1 : 3 ^ d * (2 * U x) = 2 * (3 ^ d * U x) := by ac_rfl
      have h2 : 3 ^ d * (3 * x) = 3 * (3 ^ d * x) := by ac_rfl
      rw [h1, h2] at hm
      omega
    · have py0 : y % 2 = 0 := by omega
      have hed : d = e + 1 := by omega
      rw [hed, Nat.pow_succ] at h
      simp only [px, py0, Nat.pow_one, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hx hy
      have hm : 2 * (3 ^ e * U x) = 3 * (3 ^ e * x) + 3 ^ e := by
        calc
          _ = 3 ^ e * (2 * U x) := by ac_rfl
          _ = 3 ^ e * (3 * x + 1) := congrArg (fun z => 3 ^ e * z) hx
          _ = _ := by simp only [Nat.mul_add, Nat.mul_one]; ac_rfl
      have hh : y ≤ 3 * (3 ^ e * x) := by
        calc
          y ≤ 3 ^ e * 3 * x := h
          _ = _ := by ac_rfl
      have hc : 2 * U y ≤ 2 * (3 ^ e * U x) := by
        calc
          2 * U y = y := hy
          _ ≤ 3 * (3 ^ e * x) := hh
          _ ≤ 3 * (3 ^ e * x) + 3 ^ e := Nat.le_add_right _ _
          _ = _ := hm.symm
      exact Nat.le_of_mul_le_mul_left hc (by decide)
  · have px0 : x % 2 = 0 := by omega
    by_cases py : y % 2 = 1
    · have hed : e = d + 1 := by omega
      rw [hed, Nat.pow_succ]
      simp only [px0, py, Nat.pow_one, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hx hy
      have hm : 3 ^ d * x = 2 * (3 ^ d * U x) := by
        calc
          _ = 3 ^ d * (2 * U x) := congrArg (fun z => 3 ^ d * z) hx.symm
          _ = _ := by ac_rfl
      have hh : y + 1 ≤ 2 * (3 ^ d * U x) := by omega
      have hh3 := Nat.mul_le_mul_left 3 hh
      have hg : 3 ^ d * 3 * U x = 3 * (3 ^ d * U x) := by ac_rfl
      rw [hg]
      omega
    · have py0 : y % 2 = 0 := by omega
      have hed : e = d := by omega
      subst e
      simp only [px0, py0, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hx hy
      have hm : 3 ^ d * x = 2 * (3 ^ d * U x) := by
        calc
          _ = 3 ^ d * (2 * U x) := congrArg (fun z => 3 ^ d * z) hx.symm
          _ = _ := by ac_rfl
      omega

theorem initial_positive_transition (x : Nat) :
    (x % 2 = 1 → U (3 * x + 2) = 3 * U x + 2) ∧
    (x % 2 = 0 → U (3 * x + 2) = 3 * U x + 1) := by
  constructor <;> intro hx <;> simp [U, hx, Nat.mul_mod] <;> omega

theorem positive_even_transitions {x d : Nat} (hx : x % 2 = 0) :
    U (3 ^ d * x + 1) = 3 ^ (d + 1) * U x + 2 ∧
    U (3 ^ d * x + 2) = 3 ^ d * U x + 1 := by
  have he : x = 2 * (x / 2) := by omega
  have hm : 3 ^ d * x = 2 * (3 ^ d * (x / 2)) := by
    calc
      _ = 3 ^ d * (2 * (x / 2)) := congrArg (fun z => 3 ^ d * z) he
      _ = _ := by ac_rfl
  have h1 : 3 ^ d * x + 1 = 2 * (3 ^ d * (x / 2)) + 1 := by omega
  have h2 : 3 ^ d * x + 2 = 2 * (3 ^ d * (x / 2) + 1) := by omega
  rw [h1, h2, odd_step, even_step]
  have hu : U x = x / 2 := by simp [U, hx]
  rw [hu, Nat.pow_succ]
  constructor <;> ac_rfl

theorem first_odd_after_even_closes {x e : Nat} (hx : x % 2 = 1) :
    U (3 ^ (e + 1) * x + 1) ≤ 3 ^ e * U x ∧
    U (3 ^ (e + 2) * x + 2) ≤ 3 ^ (e + 2) * U x := by
  have hp : ∀ d, 3 ^ d % 2 = 1 := by intro d; simp [Nat.pow_mod]
  have h1 : (3 ^ (e + 1) * x + 1) % 2 = 0 := by simp [Nat.add_mod, Nat.mul_mod, hx, hp]
  have h2 : (3 ^ (e + 2) * x + 2) % 2 = 1 := by simp [Nat.mul_mod, hx, hp]
  have hu := step_equation x
  have hu1 := step_equation (3 ^ (e + 1) * x + 1)
  have hu2 := step_equation (3 ^ (e + 2) * x + 2)
  simp only [hx, h1, h2, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.add_zero] at hu hu1 hu2
  constructor
  · have hm := congrArg (fun z => 3 ^ e * z) hu
    have hpos := Nat.pow_pos (by decide : 0 < 3) (n := e)
    rw [Nat.pow_succ] at hu1 ⊢
    simp only [Nat.mul_add, Nat.mul_one] at hm
    have ha : 3 ^ e * (2 * U x) = 2 * (3 ^ e * U x) := by ac_rfl
    have hb : 3 ^ e * (3 * x) = 3 ^ e * 3 * x := by ac_rfl
    rw [ha, hb] at hm
    omega
  · have hm := congrArg (fun z => 3 ^ (e + 2) * z) hu
    have hpos : 9 ≤ 3 ^ (e + 2) := by
      have hh := Nat.pow_pos (by decide : 0 < 3) (n := e)
      rw [Nat.pow_add]
      omega
    simp only [Nat.mul_add, Nat.mul_one] at hm hu2
    have ha : 3 ^ (e + 2) * (2 * U x) = 2 * (3 ^ (e + 2) * U x) := by ac_rfl
    have hb : 3 ^ (e + 2) * (3 * x) = 3 * (3 ^ (e + 2) * x) := by ac_rfl
    rw [ha, hb] at hm
    omega

def oneTurn : Nat → Nat → Bool
  | 0, _ => true
  | t + 1, n => oneTurn t n &&
      (decide (orbit t n % 2 = 0) || decide (wt t n = t))

def mark (b : Bool) : Nat := if b then 1 else 0

theorem all_odd_one_turn : ∀ t n, wt t n = t → oneTurn t n = true
  | 0, _, _ => rfl
  | t + 1, n, h => by
    have hb := weight_le_length t n
    rw [weight_snoc] at h
    have hw : wt t n = t := by omega
    simp [oneTurn, all_odd_one_turn t n hw, hw]

theorem one_turn_lift : ∀ t q n,
    oneTurn t (2 ^ t * q + n) = oneTurn t n
  | 0, _, _ => rfl
  | t + 1, q, n => by
    have he : 2 ^ (t + 1) * q + n = 2 ^ t * (2 * q) + n := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have hp : orbit t (2 ^ t * (2 * q) + n) % 2 = orbit t n % 2 := by
      rw [affine]
      simp [Nat.add_mod, Nat.mul_mod]
    simp only [oneTurn, he, one_turn_lift, hp, weight_lift]

theorem all_odd_children (t n : Nat) :
    mark (decide (wt (t + 1) n = t + 1)) +
      mark (decide (wt (t + 1) (2 ^ t + n) = t + 1)) =
        mark (decide (wt t n = t)) := by
  have hl := weight_lift t 1 n
  simp only [Nat.mul_one] at hl
  rw [weight_snoc t n, weight_snoc t (2 ^ t + n), hl, endpoint_parity_flip]
  have hb := weight_le_length t n
  by_cases hw : wt t n = t
  · by_cases hp : orbit t n % 2 = 0
    · simp [mark, hw, hp]
    · have hp1 : orbit t n % 2 = 1 := by omega
      simp [mark, hw, hp1]
  · have h1 : wt t n + orbit t n % 2 ≠ t + 1 := by omega
    have h2 : wt t n + (1 - orbit t n % 2) ≠ t + 1 := by omega
    simp [mark, hw, h1, h2]

theorem one_turn_children (t n : Nat) :
    mark (oneTurn (t + 1) n) + mark (oneTurn (t + 1) (2 ^ t + n)) =
      mark (oneTurn t n) + mark (decide (wt t n = t)) := by
  have hl := one_turn_lift t 1 n
  have hw := weight_lift t 1 n
  simp only [Nat.mul_one] at hl hw
  simp only [oneTurn, hl, hw, endpoint_parity_flip]
  by_cases ha : wt t n = t
  · simp [mark, ha, all_odd_one_turn t n ha]
  · by_cases hp : orbit t n % 2 = 0
    · simp [mark, ha, hp]
    · have hp1 : orbit t n % 2 = 1 := by omega
      simp [mark, ha, hp1]

theorem all_odd_mass : ∀ t,
    total (2 ^ t) (fun n => mark (decide (wt t n = t))) = 1
  | 0 => by decide
  | t + 1 => by
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => all_odd_children t n)]
    exact all_odd_mass t

theorem one_turn_mass : ∀ t,
    total (2 ^ t) (fun n => mark (oneTurn t n)) = t + 1
  | 0 => by decide
  | t + 1 => by
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => one_turn_children t n), total_sum,
      one_turn_mass t, all_odd_mass]

theorem one_turn_annulus (t : Nat) :
    total (2 ^ t) (fun n => mark (oneTurn t (2 ^ t + n))) = t + 1 := by
  have hh := total_ext (2 ^ t)
    (fun n => mark (oneTurn t (2 ^ t + n))) (fun n => mark (oneTurn t n)) (by
      intro n _
      have hl := one_turn_lift t 1 n
      simp only [Nat.mul_one] at hl
      rw [hl])
  rw [hh, one_turn_mass]

#print axioms shifted_step
#print axioms halving_order
#print axioms shifted_order_step
#print axioms ordered_shifted_endpoints
#print axioms ordered_cross_product
#print axioms refinement_shifted_order
#print axioms alive_even_count_order
#print axioms alive_prefix
#print axioms first_return_order
#print axioms reciprocal_downward_bound
#print axioms odd_charge_denominator
#print axioms even_charge_denominator
#print axioms shifted_orbit_identity
#print axioms shifted_correction_lift
#print axioms shifted_correction_mass
#print axioms reversal_example
#print axioms reversed_shifted_order_fails
#print axioms odd_power_mod_eight
#print axioms family_even_clock
#print axioms family_even_reversed
#print axioms unshifted_order_step
#print axioms initial_positive_transition
#print axioms positive_even_transitions
#print axioms first_odd_after_even_closes
#print axioms all_odd_one_turn
#print axioms one_turn_lift
#print axioms all_odd_children
#print axioms one_turn_children
#print axioms all_odd_mass
#print axioms one_turn_mass
#print axioms one_turn_annulus

end OrderedWeightDrift
