/-
  Exact finite refinements of the actual correction/escape weight.
  Reciprocal affine moments and an infinite family of nonvanishing jumps.
  No infinite energy bound or convergence theorem is asserted.
-/
import CoalescenceTail

namespace EscapeWeightRefinements
open CollatzAffine CoalescenceTail

theorem even_step (n : Nat) : U (2 * n) = n := by simp [U]
theorem odd_step (n : Nat) : U (2 * n + 1) = 3 * n + 2 := by simp [U]; omega

theorem even_refinement (t n : Nat) :
    orbit (t + 1) (2 * n) = orbit t n ∧ wt (t + 1) (2 * n) = wt t n := by
  simp [orbit, wt, even_step]

theorem odd_refinement (t n : Nat) :
    orbit (t + 1) (2 * n + 1) = orbit t (3 * n + 2) ∧
    wt (t + 1) (2 * n + 1) = 1 + wt t (3 * n + 2) := by
  simp [orbit, wt, odd_step]

def scale : Nat → Nat → Nat
  | 0, _ => 1
  | t + 1, n => if orbit t n % 2 = 1 then scale t n else 3 * scale t n

def correction : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => if orbit t n % 2 = 1
      then 3 * correction t n + 2 ^ t * scale t n else 3 * correction t n

theorem step_equation (n : Nat) : 2 * U n = 3 ^ (n % 2) * n + n % 2 := by
  by_cases h : n % 2 = 1
  · simp [U, h]; omega
  · have he : n % 2 = 0 := by omega
    simp [U, he]; omega

theorem scale_identity : ∀ t n, scale t n * 3 ^ wt t n = 3 ^ t
  | 0, _ => by simp [scale, wt]
  | t + 1, n => by
    have ih := scale_identity t n
    by_cases h : orbit t n % 2 = 1
    · simp [scale, weight_snoc, h, Nat.pow_succ]
      rw [← Nat.mul_assoc, ih]
    · have he : orbit t n % 2 = 0 := by omega
      simp [scale, weight_snoc, he, Nat.pow_succ]
      calc
        3 * scale t n * 3 ^ wt t n = 3 * (scale t n * 3 ^ wt t n) := by ac_rfl
        _ = 3 ^ t * 3 := by rw [ih]; ac_rfl

theorem scaled_orbit_identity : ∀ t n,
    scale t n * (2 ^ t * orbit t n) = 3 ^ t * n + correction t n
  | 0, _ => by simp [scale, correction, orbit]
  | t + 1, n => by
    have ih := scaled_orbit_identity t n
    have hs := step_equation (orbit t n)
    by_cases h : orbit t n % 2 = 1
    · simp only [h, Nat.pow_one] at hs
      simp only [scale, correction, if_pos h, orbit_snoc, Nat.pow_succ]
      calc
        scale t n * (2 ^ t * 2 * U (orbit t n)) =
            scale t n * (2 ^ t * (2 * U (orbit t n))) := by ac_rfl
        _ = scale t n * (2 ^ t * (3 * orbit t n + 1)) := by rw [hs]
        _ = 3 * (scale t n * (2 ^ t * orbit t n)) + 2 ^ t * scale t n := by
          simp only [Nat.mul_add, Nat.mul_one]
          ac_rfl
        _ = 3 ^ t * 3 * n + (3 * correction t n + 2 ^ t * scale t n) := by
          rw [ih, Nat.mul_add]
          ac_rfl
    · have he : orbit t n % 2 = 0 := by omega
      simp only [he, Nat.pow_zero, Nat.one_mul, Nat.add_zero] at hs
      simp only [scale, correction, if_neg h, orbit_snoc, Nat.pow_succ]
      calc
        3 * scale t n * (2 ^ t * 2 * U (orbit t n)) =
            3 * (scale t n * (2 ^ t * (2 * U (orbit t n)))) := by ac_rfl
        _ = 3 * (scale t n * (2 ^ t * orbit t n)) := by rw [hs]
        _ = 3 ^ t * 3 * n + 3 * correction t n := by
          rw [ih, Nat.mul_add]
          ac_rfl

theorem correction_identity (t n : Nat) : correction t n = scale t n * numerator t n := by
  have h := scaled_orbit_identity t n
  rw [orbit_equation, Nat.mul_add] at h
  have hm : scale t n * (3 ^ wt t n * n) = 3 ^ t * n := by
    rw [← Nat.mul_assoc, scale_identity]
  rw [hm] at h
  omega

theorem data_lift : ∀ t q n,
    scale t (2 ^ t * q + n) = scale t n ∧
    correction t (2 ^ t * q + n) = correction t n
  | 0, _, _ => by simp [scale, correction]
  | t + 1, q, n => by
    have hx : 2 ^ (t + 1) * q + n = 2 ^ t * (2 * q) + n := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have ih := data_lift t (2 * q) n
    have hp : orbit t (2 ^ t * (2 * q) + n) % 2 = orbit t n % 2 := by
      rw [affine]
      simp [Nat.add_mod, Nat.mul_mod]
    simp [scale, correction, hx, hp, ih.1, ih.2]

theorem data_children (t n : Nat) :
    scale (t + 1) n + scale (t + 1) (2 ^ t + n) = 4 * scale t n ∧
    correction (t + 1) n + correction (t + 1) (2 ^ t + n) =
      6 * correction t n + 2 ^ t * scale t n := by
  have hl := data_lift t 1 n
  simp only [Nat.mul_one] at hl
  have hp := endpoint_parity_flip t n
  by_cases h : orbit t n % 2 = 1
  · have he : orbit t (2 ^ t + n) % 2 = 0 := by omega
    simp [scale, correction, h, he, hl.1, hl.2]
    omega
  · have he : orbit t n % 2 = 0 := by omega
    have ho : orbit t (2 ^ t + n) % 2 = 1 := by omega
    simp [scale, correction, he, ho, hl.1, hl.2]
    omega

theorem scale_mass : ∀ t, total (2 ^ t) (scale t) = 4 ^ t
  | 0 => by simp [total, scale]
  | t + 1 => by
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => (data_children t n).1), total_mul, scale_mass]
    simp [Nat.pow_succ, Nat.mul_comm]

theorem correction_mass : ∀ t, 2 * total (2 ^ t) (correction t) + 6 ^ t = 8 ^ t
  | 0 => by simp [total, correction]
  | t + 1 => by
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    rw [total_ext _ _ _ (fun n _ => (data_children t n).2), total_sum,
      total_mul, total_mul, scale_mass]
    have ih := correction_mass t
    have hm : 2 ^ t * 4 ^ t = 8 ^ t := by rw [← Nat.mul_pow]
    rw [hm, Nat.pow_succ, Nat.pow_succ]
    omega

theorem orbit_add (t s n : Nat) : orbit (t + s) n = orbit s (orbit t n) := by
  induction s with
  | zero => rfl
  | succ s ih => rw [show t + (s + 1) = (t + s) + 1 by omega, orbit_snoc, ih, orbit_snoc]

theorem weight_add (t s n : Nat) : wt (t + s) n = wt t n + wt s (orbit t n) := by
  induction s with
  | zero => simp [wt]
  | succ s ih =>
    rw [show t + (s + 1) = (t + s) + 1 by omega, weight_snoc, ih, orbit_add, weight_snoc]
    omega

theorem cycle_one (a : Nat) : orbit (2 * a) 1 = 1 ∧ wt (2 * a) 1 = a := by
  induction a with
  | zero => simp [orbit, wt]
  | succ a ih =>
    rw [show 2 * (a + 1) = 2 * a + 2 by omega, orbit_add, weight_add, ih.1, ih.2]
    simp [orbit, wt, U]

theorem zero_data : ∀ t, orbit t 0 = 0 ∧ wt t 0 = 0
  | 0 => by simp [orbit, wt]
  | t + 1 => by simpa [orbit, wt, U] using zero_data t

theorem halving_data (t m : Nat) : orbit t (2 ^ t * m) = m ∧ wt t (2 ^ t * m) = 0 := by
  have h := affine t m 0
  have w := weight_lift t m 0
  simpa [zero_data] using And.intro h w

theorem lifted_one (a : Nat) :
    orbit (2 * a) (2 ^ (2 * a) + 1) = 3 ^ a + 1 ∧
    wt (2 * a) (2 ^ (2 * a) + 1) = a := by
  have h := affine (2 * a) 1 1
  have w := weight_lift (2 * a) 1 1
  simpa [(cycle_one a).1, (cycle_one a).2] using And.intro h w

theorem family_first_five {u B : Nat} (h : 9 * u + 1 = 4 * B) :
    orbit 5 (8 * u) = B + 1 ∧ wt 5 (8 * u) = 2 := by
  have he8 : U (8 * u) = 4 * u := by simpa [← Nat.mul_assoc] using even_step (4 * u)
  have he4 : U (4 * u) = 2 * u := by simpa [← Nat.mul_assoc] using even_step (2 * u)
  have he2 : U (2 * u) = u := even_step u
  have ho : u % 2 = 1 := by omega
  have hu : U u = (3 * u + 1) / 2 := by simp [U, ho]
  have ho' : U u % 2 = 1 := by rw [hu]; omega
  have huu : U (U u) = B + 1 := by rw [U, if_pos ho', hu]; omega
  simp [orbit, wt, he8, he4, he2, ho, ho', huu, Nat.mul_mod]

theorem family_target_two {u B : Nat} (h : 9 * u + 1 = 4 * B) :
    orbit 2 (24 * u + 2) = 8 * B ∧ wt 2 (24 * u + 2) = 1 := by
  have he : U (24 * u + 2) = 12 * u + 1 := by
    rw [show 24 * u + 2 = 2 * (12 * u + 1) by omega, even_step]
  have hp : (12 * u + 1) % 2 = 1 := by omega
  have ho : U (12 * u + 1) = 8 * B := by rw [U, if_pos hp]; omega
  simp [orbit, wt, he, ho, hp, Nat.mul_mod]

theorem family_common_clock {a u : Nat} (h : 9 * u + 1 = 4 * 2 ^ (2 * a)) :
    orbit (2 * a + 5) (8 * u) = 3 ^ a + 1 ∧
    wt (2 * a + 5) (8 * u) = a + 2 ∧
    orbit (2 * a + 5) (24 * u + 2) = 1 ∧
    wt (2 * a + 5) (24 * u + 2) = 1 := by
  have hn := family_first_five h
  have hq := family_target_two h
  have hnT : 2 * a + 5 = 5 + 2 * a := by omega
  have hqT : 2 * a + 5 = 2 + (2 * a + 3) := by omega
  have hb : 8 * 2 ^ (2 * a) = 2 ^ (2 * a + 3) * 1 := by
    simp [Nat.pow_add, Nat.mul_comm]
  constructor
  · rw [hnT, orbit_add, hn.1, (lifted_one a).1]
  constructor
  · rw [hnT, weight_add, hn.1, hn.2, (lifted_one a).2]
    omega
  constructor
  · rw [hqT, orbit_add, hq.1, hb, (halving_data (2 * a + 3) 1).1]
  · rw [hqT, weight_add, hq.1, hq.2, hb, (halving_data (2 * a + 3) 1).2]

theorem family_shell {a u : Nat} (h : 9 * u + 1 = 4 * 2 ^ (2 * a)) :
    2 ^ (2 * a + 1) ≤ 8 * u ∧ 8 * u < 2 ^ (2 * a + 2) := by
  have hp := Nat.pow_pos (by decide : 0 < 2) (n := 2 * a)
  simp only [Nat.pow_succ]
  omega

def familySeed (j : Nat) : Nat := (64 ^ (j + 1) - 1) / 9

theorem family_seed_equation (j : Nat) :
    9 * familySeed j + 1 = 4 * 2 ^ (2 * (3 * j + 2)) := by
  have hp : 0 < 64 ^ (j + 1) := Nat.pow_pos (by decide)
  have hm : 64 ^ (j + 1) % 9 = 1 := by simp [Nat.pow_mod]
  have hd := Nat.mod_add_div (64 ^ (j + 1)) 9
  have he : (64 ^ (j + 1) - 1) / 9 = 64 ^ (j + 1) / 9 := by omega
  unfold familySeed
  rw [he]
  have hb : 64 ^ (j + 1) = 4 * 2 ^ (2 * (3 * j + 2)) := by
    rw [show 64 = 2 ^ 6 from rfl, ← Nat.pow_mul]
    have hx : 6 * (j + 1) = 2 + 2 * (3 * j + 2) := by omega
    rw [hx, Nat.pow_add]
  omega

/-- Two final steps give a uniform lower bound for the parent value.
    After division this yields a parent-minus-odd-child jump >= 27/512. -/
theorem two_step_jump_bound {A : Nat} (hA : 9 ≤ A) (ho : A % 2 = 1) :
    27 * orbit 2 (A + 1) ≤ 8 * A * 3 ^ wt 2 (A + 1) := by
  have he : (A + 1) % 2 = 0 := by omega
  have h1 : U (A + 1) = (A + 1) / 2 := by simp [U, he]
  change 27 * U (U (A + 1)) ≤ 8 * A * 3 ^ ((A + 1) % 2 + (U (A + 1) % 2 + 0))
  rw [he, Nat.zero_add, Nat.add_zero]
  by_cases h2 : U (A + 1) % 2 = 1
  · rw [h2, Nat.pow_one, U, if_pos h2, h1]
    rw [h1] at h2
    omega
  · have h2e : U (A + 1) % 2 = 0 := by omega
    rw [h2e, Nat.pow_zero, Nat.mul_one, U, if_neg h2, h1]
    rw [h1] at h2e
    omega

#print axioms even_refinement
#print axioms odd_refinement
#print axioms scale_identity
#print axioms scaled_orbit_identity
#print axioms correction_identity
#print axioms data_lift
#print axioms data_children
#print axioms scale_mass
#print axioms correction_mass
#print axioms orbit_add
#print axioms weight_add
#print axioms cycle_one
#print axioms zero_data
#print axioms halving_data
#print axioms lifted_one
#print axioms family_first_five
#print axioms family_target_two
#print axioms family_common_clock
#print axioms family_shell
#print axioms family_seed_equation
#print axioms two_step_jump_bound
end EscapeWeightRefinements
