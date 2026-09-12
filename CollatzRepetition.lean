/-
  Finite parity repetition and exact collision certificates.
  Standalone Lean 4.31, using kernel proofs only.
-/
namespace CollatzRepetition

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbit k (U n)

def SameParity : Nat → Nat → Nat → Prop
  | 0, _, _ => True
  | k + 1, x, y => x % 2 = y % 2 ∧ SameParity k (U x) (U y)

theorem even_equation (n : Nat) (h : n % 2 ≠ 1) :
    2 * (U n : Int) = (n : Int) := by
  unfold U
  rw [if_neg h]
  omega

theorem odd_equation (n : Nat) (h : n % 2 = 1) :
    2 * (U n : Int) = 3 * (n : Int) + 1 := by
  unfold U
  rw [if_pos h]
  omega

/-- Agreement of k parities forces k bits of congruence, in exact integers. -/
theorem parity_gap_divisible : ∀ k x y, SameParity k x y →
    2 ^ k ∣ ((x : Int) - (y : Int)).natAbs
  | 0, x, y, _ => by simp
  | k + 1, x, y, h => by
    obtain ⟨hpar, htail⟩ := h
    have ih := parity_gap_divisible k (U x) (U y) htail
    have hd : 2 ^ (k + 1) ∣ 2 * ((U x : Int) - (U y : Int)).natAbs := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2]
      exact Nat.mul_dvd_mul_left 2 ih
    by_cases hx : x % 2 = 1
    · have hy : y % 2 = 1 := by omega
      have he : 2 * ((U x : Int) - (U y : Int)) = 3 * ((x : Int) - (y : Int)) := by
        rw [Int.mul_sub, Int.mul_sub, odd_equation x hx, odd_equation y hy]
        omega
      have habs := congrArg Int.natAbs he
      simp only [Int.natAbs_mul] at habs
      have hd3 : 2 ^ (k + 1) ∣ 3 * ((x : Int) - (y : Int)).natAbs := by
        simpa only [habs] using hd
      have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd3
      rw [Nat.gcd_pow_left_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1), Nat.one_mul] at hc
      exact hc
    · have hy : y % 2 ≠ 1 := by omega
      have he : 2 * ((U x : Int) - (U y : Int)) = (x : Int) - (y : Int) := by
        rw [Int.mul_sub, even_equation x hx, even_equation y hy]
      have habs := congrArg Int.natAbs he
      simp only [Int.natAbs_mul] at habs
      simpa only [habs] using hd

/-- Equal parity windows in a small enough value interval imply an actual collision. -/
theorem collision_of_small_gap {k x y : Nat} (h : SameParity k x y)
    (hgap : ((x : Int) - (y : Int)).natAbs < 2 ^ k) : x = y := by
  have hd := parity_gap_divisible k x y h
  by_cases hz : ((x : Int) - (y : Int)).natAbs = 0
  · have he := Int.natAbs_eq_zero.mp hz
    omega
  · have hle := Nat.le_of_dvd (by omega) hd
    omega

theorem collision_below_power {k x y : Nat} (h : SameParity k x y)
    (hx : x < 2 ^ k) (hy : y < 2 ^ k) : x = y := by
  apply collision_of_small_gap h
  omega

theorem orbit_add (a b n : Nat) : orbit (a + b) n = orbit b (orbit a n) := by
  induction a generalizing n with
  | zero => rfl
  | succ a ih =>
    simpa only [Nat.succ_add, orbit] using ih b (U n)

/-- Once a state repeats, all later states repeat with the same positive period. -/
theorem repeated_state_periodic {a b n : Nat} (h : orbit a n = orbit b n) (t : Nat) :
    orbit (a + t) n = orbit (b + t) n := by
  rw [orbit_add, orbit_add, h]

theorem parity_collision_periodic {a b k n : Nat}
    (hp : SameParity k (orbit a n) (orbit b n))
    (ha : orbit a n < 2 ^ k) (hb : orbit b n < 2 ^ k) (t : Nat) :
    orbit (a + t) n = orbit (b + t) n :=
  repeated_state_periodic (collision_below_power hp ha hb) t

#print axioms parity_gap_divisible
#print axioms collision_of_small_gap
#print axioms parity_collision_periodic

end CollatzRepetition
