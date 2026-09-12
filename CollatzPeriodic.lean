/-
  CollatzPeriodic.lean — exact integrality obstruction to periodic-growth
  constructions. Standalone Lean 4, no Mathlib or native_decide.

  Main theorem: an infinite integer sequence satisfying
       Q * x(j+1) = P * x(j) + W,
  with Q > 1 and gcd(P,Q) = 1, is constant. Applied to repeated accelerated
  Collatz blocks, P = 3^k and Q = 2^H: an eventually periodic halving schedule
  forces an eventual cycle. It cannot produce a divergent integer orbit.

  The generic recurrence, its Collatz specialization, and the derivation of
  the block recurrence from a finite prescribed halving schedule are all
  formalized here. BlockRel describes exact step equations over Int, a weaker
  assumption than an actual positive odd Collatz orbit.

  Check: lean CollatzPeriodic.lean
-/

namespace CollatzPeriodic

/-- Iterating a homogeneous rational recurrence without division. -/
theorem difference_power {P Q : Nat} {d : Nat → Int}
    (h : ∀ j, (Q : Int) * d (j + 1) = (P : Int) * d j) :
    ∀ j, (Q : Int) ^ j * d j = (P : Int) ^ j * d 0
  | 0 => by simp
  | j + 1 => by
    calc
      (Q : Int) ^ (j + 1) * d (j + 1)
          = (Q : Int) ^ j * ((Q : Int) * d (j + 1)) := by
              rw [Int.pow_succ, Int.mul_assoc]
      _ = (Q : Int) ^ j * ((P : Int) * d j) := by rw [h j]
      _ = (P : Int) * ((Q : Int) ^ j * d j) := by
              rw [Int.mul_left_comm]
      _ = (P : Int) * ((P : Int) ^ j * d 0) := by
              rw [difference_power h j]
      _ = (P : Int) ^ (j + 1) * d 0 := by
              rw [Int.pow_succ, Int.mul_comm ((P : Int) ^ j) (P : Int),
                  Int.mul_assoc]

/-- Every denominator power divides the initial absolute difference. -/
theorem difference_divisibility {P Q : Nat} {d : Nat → Int}
    (hcop : Nat.gcd Q P = 1)
    (h : ∀ j, (Q : Int) * d (j + 1) = (P : Int) * d j) (j : Nat) :
    Q ^ j ∣ (d 0).natAbs := by
  have heq := congrArg Int.natAbs (difference_power h j)
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heq
  have hdvd : Q ^ j ∣ P ^ j * (d 0).natAbs := by
    rw [← heq]
    exact Nat.dvd_mul_right _ _
  have hcancel := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hdvd
  rw [Nat.pow_gcd_pow_of_gcd_eq_one hcop, Nat.one_mul] at hcancel
  exact hcancel

/-- An integer divisible by every power of Q > 1 is zero. -/
theorem zero_of_all_powers_dvd {Q D : Nat} (hQ : 1 < Q)
    (h : ∀ j, Q ^ j ∣ D) : D = 0 := by
  by_cases h0 : D = 0
  · exact h0
  · have hle := Nat.le_of_dvd (by omega : 0 < D) (h D)
    have hlt : D < Q ^ D := Nat.lt_pow_self hQ
    omega

/-- Core rigidity: an infinite integer affine recurrence with coprime
    numerator and nontrivial denominator is fixed from its first term. -/
theorem affine_first_fixed {P Q : Nat} {W : Int} {x : Nat → Int}
    (hQ : 1 < Q) (hcop : Nat.gcd Q P = 1)
    (h : ∀ j, (Q : Int) * x (j + 1) = (P : Int) * x j + W) :
    x 1 = x 0 := by
  let d : Nat → Int := fun j => x (j + 1) - x j
  have hd : ∀ j, (Q : Int) * d (j + 1) = (P : Int) * d j := by
    intro j
    dsimp [d]
    rw [Int.mul_sub, Int.mul_sub, h (j + 1), h j]
    omega
  have hzero : (d 0).natAbs = 0 :=
    zero_of_all_powers_dvd hQ (difference_divisibility hcop hd)
  have hz : d 0 = 0 := Int.natAbs_eq_zero.mp hzero
  dsimp [d] at hz
  omega

/-- The full sequence is constant; negative integers are included. -/
theorem affine_constant {P Q : Nat} {W : Int} {x : Nat → Int}
    (hQ : 1 < Q) (hcop : Nat.gcd Q P = 1)
    (h : ∀ j, (Q : Int) * x (j + 1) = (P : Int) * x j + W) :
    ∀ j, x j = x 0 := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
    have hshift : ∀ t, (Q : Int) * x (j + t + 1) =
        (P : Int) * x (j + t) + W := fun t => h (j + t)
    have heq := affine_first_fixed (x := fun t => x (j + t)) hQ hcop
      (by simpa only [Nat.add_assoc] using hshift)
    simpa only [Nat.add_zero] using heq.trans ih

/-- Specialization to a repeated block of k accelerated 3x+1 steps with
    a positive total H of halvings. The block-boundary values are fixed. -/
theorem collatz_block_constant {k H : Nat} {W : Int} {x : Nat → Int}
    (hH : 0 < H)
    (h : ∀ j, ((2 ^ H : Nat) : Int) * x (j + 1) =
        ((3 ^ k : Nat) : Int) * x j + W) : ∀ j, x j = x 0 := by
  exact affine_constant (Nat.one_lt_pow (by omega) (by decide))
    (Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1)) h

/-- Exact 3x+1 step equations following the prescribed halving exponents.
    No positivity or parity is assumed, so real Collatz steps imply this
    relation immediately from their defining equations. -/
def BlockRel : List Nat → Int → Int → Prop
  | [], x, y => y = x
  | h :: hs, x, y => ∃ z, (2 : Int) ^ h * z = 3 * x + 1 ∧ BlockRel hs z y

/-- Total number of halvings in a prescribed block. -/
def totalHalvings : List Nat → Nat
  | [] => 0
  | h :: hs => h + totalHalvings hs

/-- Affine additive coefficient for a block of accelerated 3x+1 steps. -/
def blockWeight : List Nat → Int
  | [] => 0
  | h :: hs => (3 : Int) ^ hs.length + (2 : Int) ^ h * blockWeight hs

/-- Derivation of the block affine equation from the individual steps. -/
theorem block_formula {hs : List Nat} {x y : Int} (h : BlockRel hs x y) :
    (2 : Int) ^ totalHalvings hs * y =
      (3 : Int) ^ hs.length * x + blockWeight hs := by
  induction hs generalizing x y with
  | nil => simpa [BlockRel, totalHalvings, blockWeight] using h
  | cons e hs ih =>
    obtain ⟨z, hz, htail⟩ := h
    have ht := ih htail
    simp only [totalHalvings, blockWeight, List.length_cons,
      Int.pow_add, Int.pow_succ]
    calc
      (2 : Int) ^ e * (2 : Int) ^ totalHalvings hs * y
          = (2 : Int) ^ e * ((2 : Int) ^ totalHalvings hs * y) := by
              rw [Int.mul_assoc]
      _ = (2 : Int) ^ e * ((3 : Int) ^ hs.length * z + blockWeight hs) := by rw [ht]
      _ = (3 : Int) ^ hs.length * ((2 : Int) ^ e * z) +
          (2 : Int) ^ e * blockWeight hs := by rw [Int.mul_add, Int.mul_left_comm]
      _ = (3 : Int) ^ hs.length * (3 * x + 1) +
          (2 : Int) ^ e * blockWeight hs := by rw [hz]
      _ = (3 : Int) ^ hs.length * 3 * x +
          ((3 : Int) ^ hs.length + (2 : Int) ^ e * blockWeight hs) := by
            rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc]
            omega

/-- An infinite integer orbit following repetitions of one finite prescribed
    halving block has identical values at all block boundaries. -/
theorem repeated_schedule_constant {hs : List Nat} {x : Nat → Int}
    (hH : 0 < totalHalvings hs)
    (h : ∀ j, BlockRel hs (x j) (x (j + 1))) : ∀ j, x j = x 0 := by
  apply collatz_block_constant (k := hs.length) (W := blockWeight hs) hH
  intro j
  simpa [Int.natCast_pow] using block_formula (h j)

/-- If each denominator contains a factor 2, every power of 2 divides
    every term of an infinite integer homogeneous recurrence. -/
theorem variable_denominator_divisibility {q d : Nat → Nat}
    (hq : ∀ i, 2 ∣ q i)
    (h : ∀ i, q i * d (i + 1) = 3 * d i) :
    ∀ m i, 2 ^ m ∣ d i
  | 0, i => by simp
  | m + 1, i => by
    have hmul := Nat.mul_dvd_mul (hq i) (variable_denominator_divisibility hq h m (i + 1))
    have hdvd : 2 ^ (m + 1) ∣ 3 * d i := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m) 2]
      rw [← h i]
      exact hmul
    have hcancel := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hdvd
    rw [Nat.gcd_pow_left_of_gcd_eq_one (by decide : Nat.gcd 2 3 = 1),
      Nat.one_mul] at hcancel
    exact hcancel

/-- Two integer sequences with the same positive halving exponents are
    identical. This applies to arbitrary, including nonperiodic, schedules. -/
theorem shared_schedule_unique {h : Nat → Nat} {x y : Nat → Int}
    (hpos : ∀ i, 0 < h i)
    (hx : ∀ i, (2 : Int) ^ h i * x (i + 1) = 3 * x i + 1)
    (hy : ∀ i, (2 : Int) ^ h i * y (i + 1) = 3 * y i + 1) :
    ∀ i, x i = y i := by
  let d : Nat → Nat := fun i => (x i - y i).natAbs
  have hq : ∀ i, 2 ∣ (2 : Nat) ^ h i := by
    intro i
    have hp := Nat.pow_dvd_pow 2 (by have := hpos i; omega : 1 ≤ h i)
    simpa using hp
  have hd : ∀ i, (2 : Nat) ^ h i * d (i + 1) = 3 * d i := by
    intro i
    have heq : (2 : Int) ^ h i * (x (i + 1) - y (i + 1)) =
        3 * (x i - y i) := by
      rw [Int.mul_sub, Int.mul_sub, hx i, hy i]
      omega
    have habs := congrArg Int.natAbs heq
    simpa [d, Int.natAbs_mul, Int.natAbs_pow] using habs
  intro i
  have hz : d i = 0 := zero_of_all_powers_dvd (by decide)
    (fun m => variable_denominator_divisibility hq hd m i)
  have heq : x i - y i = 0 := Int.natAbs_eq_zero.mp hz
  omega

/-- Full schedule statement: a period k of a positive halving schedule
    is also a period of the integer values from the same tail index s.
    This need not be the minimal period; k = 0 gives a tautology.
    Actual accelerated odd Collatz orbits satisfy the step hypothesis. -/
theorem eventually_periodic_halvings {h : Nat → Nat} {x : Nat → Int}
    (hpos : ∀ i, 0 < h i)
    (hx : ∀ i, (2 : Int) ^ h i * x (i + 1) = 3 * x i + 1)
    (s k : Nat) (hperiod : ∀ i, h (s + i + k) = h (s + i)) :
    ∀ i, x (s + i + k) = x (s + i) := by
  apply shared_schedule_unique (h := fun i => h (s + i))
  · exact fun i => hpos (s + i)
  · intro i
    have heq := hx (s + i + k)
    rw [hperiod i] at heq
    simpa only [Nat.add_assoc, Nat.add_comm k 1] using heq
  · intro i
    simpa only [Nat.add_assoc] using hx (s + i)

#print axioms difference_divisibility
#print axioms affine_constant
#print axioms collatz_block_constant
#print axioms block_formula
#print axioms repeated_schedule_constant
#print axioms shared_schedule_unique
#print axioms eventually_periodic_halvings

end CollatzPeriodic
