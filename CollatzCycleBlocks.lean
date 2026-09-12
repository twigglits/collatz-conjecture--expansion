/-
  Exact ordered obstruction for a repeated affine block followed by a connector.
  Standalone Lean 4. All statements are conditional finite algebra;
  no cycle enumeration, real asymptotics, or universal Collatz claim is made.
  Check: lean CollatzCycleBlocks.lean
-/
namespace CollatzCycleBlocks

def centered (a b d x : Int) : Int := (d - a) * x - b

/-- Centering an affine recurrence makes the recurrence homogeneous. -/
theorem centered_step {a b d x y : Int} (h : d * y = a * x + b) :
    d * centered a b d y = a * centered a b d x := by
  unfold centered
  grind

/-- The corresponding constant for the final connector. -/
def obstruction (a b d c e f : Int) : Int := b * (c - f) + e * (d - a)

theorem centered_connector {a b d c e f x y : Int}
    (h : f * x = c * y + e) :
    f * centered a b d x = c * centered a b d y + obstruction a b d c e f := by
  unfold centered obstruction
  grind

/-- Exact repeated-block identity, with no division. -/
theorem centered_iterates (a d : Int) (z : Nat → Int) (r : Nat)
    (h : ∀ i, i < r → d * z (i + 1) = a * z i) :
    d ^ r * z r = a ^ r * z 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hp := ih (fun i hi => h i (by omega))
    have hs := h r (by omega)
    calc
      d ^ (r + 1) * z (r + 1) = d ^ r * (d * z (r + 1)) := by
        simp [Int.pow_succ, Int.mul_assoc]
      _ = d ^ r * (a * z r) := by rw [hs]
      _ = a * (d ^ r * z r) := by ac_rfl
      _ = a * (a ^ r * z 0) := by rw [hp]
      _ = a ^ (r + 1) * z 0 := by simp [Int.pow_succ, Int.mul_assoc, Int.mul_comm]

/-- Eliminating the final block boundary isolates the fixed obstruction. -/
theorem eliminate_boundary {a d c f K x y : Int} {r : Nat}
    (hi : d ^ r * y = a ^ r * x) (hc : f * x = c * y + K) :
    (f * d ^ r - c * a ^ r) * x = K * d ^ r := by
  grind

/-- The full finite cycle identity for w^r followed by v. -/
theorem repeated_block_obstruction (a b d c e f : Int) (x : Nat → Int) (r : Nat)
    (hs : ∀ i, i < r → d * x (i + 1) = a * x i + b)
    (hc : f * x 0 = c * x r + e) :
    (f * d ^ r - c * a ^ r) * centered a b d (x 0) =
      obstruction a b d c e f * d ^ r := by
  apply eliminate_boundary
  · exact centered_iterates a d (fun i => centered a b d (x i)) r
      (fun i hi => centered_step (hs i hi))
  · exact centered_connector hc

/-- Cancellation is exact even for a negative centered value or obstruction. -/
theorem cancel_power_two {D E : Nat} {K z : Int}
    (hg : Nat.gcd 2 D = 1)
    (he : (D : Int) * z = K * (2 ^ E : Nat)) : D ∣ K.natAbs := by
  have ha := congrArg Int.natAbs he
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at ha
  have hd : D ∣ 2 ^ E * K.natAbs := by
    refine ⟨z.natAbs, ?_⟩
    simpa [Nat.mul_comm] using ha.symm
  have hcancel := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
  rw [Nat.gcd_comm D (2 ^ E), Nat.gcd_pow_left_of_gcd_eq_one hg, Nat.one_mul] at hcancel
  exact hcancel

/-- In the Collatz case d=2^s, an odd positive cycle denominator divides K. -/
theorem collatz_block_divisibility (a b c e f : Int) (s r D : Nat) (x : Nat → Int)
    (hs : ∀ i, i < r → (2 ^ s : Int) * x (i + 1) = a * x i + b)
    (hc : f * x 0 = c * x r + e)
    (hD : (D : Int) = f * (2 ^ s : Int) ^ r - c * a ^ r)
    (hg : Nat.gcd 2 D = 1) : D ∣ (obstruction a b (2 ^ s) c e f).natAbs := by
  apply cancel_power_two (E := s * r) (z := centered a b (2 ^ s) (x 0)) hg
  have he := repeated_block_obstruction a b (2 ^ s) c e f x r hs hc
  rw [← hD] at he
  simpa [← Int.pow_mul] using he

/-- A nonzero fixed obstruction bounds the denominator of every candidate. -/
theorem denominator_bound {D : Nat} {K : Int} (hK : K ≠ 0)
    (hd : D ∣ K.natAbs) : D ≤ K.natAbs := by
  apply Nat.le_of_dvd (n := K.natAbs) _ hd
  have hz : K.natAbs ≠ 0 := by
    intro h
    exact hK (Int.natAbs_eq_zero.mp h)
  omega

/-- A vanishing obstruction forces the repeated block itself to close,
    provided the full cycle denominator is nonzero. -/
theorem zero_obstruction_closes_block (a b d c e f : Int) (x : Nat → Int) (r : Nat)
    (hs : ∀ i, i < r → d * x (i + 1) = a * x i + b)
    (hc : f * x 0 = c * x r + e)
    (hD : f * d ^ r - c * a ^ r ≠ 0)
    (hK : obstruction a b d c e f = 0) : d * x 0 = a * x 0 + b := by
  have he := repeated_block_obstruction a b d c e f x r hs hc
  rw [hK] at he
  have hz : centered a b d (x 0) = 0 :=
    (Int.mul_eq_zero.mp (by simpa using he)).resolve_left hD
  unfold centered at hz
  clear hs hc he hD hK
  grind

#print axioms centered_step
#print axioms centered_iterates
#print axioms repeated_block_obstruction
#print axioms cancel_power_two
#print axioms collatz_block_divisibility
#print axioms denominator_bound
#print axioms zero_obstruction_closes_block

end CollatzCycleBlocks
