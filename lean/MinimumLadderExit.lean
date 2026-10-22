/- Smaller Mersenne sources join selected return ladders just after their
   growing prefixes. Least-counterexample exclusions do not assert convergence. -/
import MinimumLadderWindow

namespace MinimumLadderExit
open OrdinaryCollatz MinimumReturnLadder MinimumInverseEscape MinimumInverseLocality
open MinimumLadderWindow MinimumRootPredecessors

theorem source_identity (R : Nat) : blockValue R 0 = 8 ^ R - 5 := by
  simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero,
    Nat.pow_zero, Nat.mul_one, Nat.pow_mul]

theorem endpoint_clock (R : Nat) :
    iterate (5 * R) (blockValue R 0) = 9 ^ R - 5 := by
  have hh := (block_prefix R R (by omega)).1
  simpa only [blockValue, blockProduct, Nat.sub_self, Nat.mul_zero,
    Nat.pow_zero, Nat.one_mul, Nat.pow_mul] using hh

theorem mersenne_clock (j : Nat) :
    iterate (2 * j) (2 ^ j - 1) = 3 ^ j - 1 := by
  have hh := backtrack_actual (pure_inverse j 1 (by decide))
  simpa only [Nat.mul_one, Nat.zero_add] using hh

theorem plus_smaller (R : Nat) (hR : 3 ≤ R) :
    0 < 2 ^ (2 * R + 1) - 1 ∧ 2 ^ (2 * R + 1) - 1 < blockValue R 0 := by
  have hp : 4 ≤ 2 ^ (2 * R + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ 2 * R + 1 by omega)
  have he : 2 * R + 1 + 2 ≤ 3 * R := by omega
  have hb := Nat.pow_le_pow_right (by decide : 0 < 2) he
  rw [Nat.pow_add] at hb
  rw [source_identity, show 8 ^ R = 2 ^ (3 * R) by rw [Nat.pow_mul]]
  omega

theorem minus_smaller (R : Nat) (hR : 3 ≤ R) :
    0 < 2 ^ (2 * R - 1) - 1 ∧ 2 ^ (2 * R - 1) - 1 < blockValue R 0 := by
  have hp : 2 ≤ 2 ^ (2 * R - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ 2 * R - 1 by omega)
  have hl := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 2 * R - 1 ≤ 2 * R + 1 by omega)
  have hh := plus_smaller R hR
  omega

theorem cubic_gain_plus (R : Nat) :
    (2 ^ (2 * R + 1)) ^ 3 = 8 * (8 ^ R) ^ 2 := by
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  change 2 ^ ((2 * R + 1) * 3) = 2 ^ 3 * (2 ^ 3) ^ (R * 2)
  rw [← Nat.pow_mul, ← Nat.pow_add]
  congr 1
  omega

theorem cubic_gain_minus (R : Nat) (hR : 1 ≤ R) :
    8 * (2 ^ (2 * R - 1)) ^ 3 = (8 ^ R) ^ 2 := by
  rw [← Nat.pow_mul, ← Nat.pow_mul]
  change 2 ^ 3 * 2 ^ ((2 * R - 1) * 3) = (2 ^ 3) ^ (R * 2)
  rw [← Nat.pow_add, ← Nat.pow_mul]
  congr 1
  omega

theorem exit_seven_profile (u : Nat) :
    iterate 8 (64 * u + 52) = 9 * u + 8 ∧
    Backtrack 5 1 (9 * u + 8) (192 * u + 170) := by
  have h0 : C (64 * u + 52) = 32 * u + 26 := by unfold C; split <;> omega
  have h1 : C (32 * u + 26) = 16 * u + 13 := by unfold C; split <;> omega
  have h2 : C (16 * u + 13) = 48 * u + 40 := by unfold C; split <;> omega
  have h3 : C (48 * u + 40) = 24 * u + 20 := by unfold C; split <;> omega
  have h4 : C (24 * u + 20) = 12 * u + 10 := by unfold C; split <;> omega
  have h5 : C (12 * u + 10) = 6 * u + 5 := by unfold C; split <;> omega
  have h6 : C (6 * u + 5) = 18 * u + 16 := by unfold C; split <;> omega
  have h7 : C (18 * u + 16) = 9 * u + 8 := by unfold C; split <;> omega
  have g0 := Backtrack.nil (9 * u + 8)
  have g1 := Backtrack.even g0
  have v1 : 2 * (9 * u + 8) = 18 * u + 16 := by omega
  rw [v1] at g1
  have g2 := Backtrack.even g1
  have v2 : 2 * (18 * u + 16) = 36 * u + 32 := by omega
  rw [v2] at g2
  have g3 := Backtrack.even g2
  have v3 : 2 * (36 * u + 32) = 72 * u + 64 := by omega
  rw [v3] at g3
  have g4 := Backtrack.even g3
  have v4 : 2 * (72 * u + 64) = 144 * u + 128 := by omega
  rw [v4] at g4
  have g5 := Backtrack.odd g4 (show 3 * (96 * u + 85) + 1 = 2 * (144 * u + 128) by omega)
  have g6 := Backtrack.even g5
  have v6 : 2 * (96 * u + 85) = 192 * u + 170 := by omega
  rw [v6] at g6
  exact ⟨by simp only [iterate, h0, h1, h2, h3, h4, h5, h6, h7], g6⟩

theorem exit_eleven_profile (u : Nat) :
    iterate 9 (384 * u + 148) = 27 * u + 11 ∧
    Backtrack 4 3 (27 * u + 11) (128 * u + 50) := by
  have h0 : C (384 * u + 148) = 192 * u + 74 := by unfold C; split <;> omega
  have h1 : C (192 * u + 74) = 96 * u + 37 := by unfold C; split <;> omega
  have h2 : C (96 * u + 37) = 288 * u + 112 := by unfold C; split <;> omega
  have h3 : C (288 * u + 112) = 144 * u + 56 := by unfold C; split <;> omega
  have h4 : C (144 * u + 56) = 72 * u + 28 := by unfold C; split <;> omega
  have h5 : C (72 * u + 28) = 36 * u + 14 := by unfold C; split <;> omega
  have h6 : C (36 * u + 14) = 18 * u + 7 := by unfold C; split <;> omega
  have h7 : C (18 * u + 7) = 54 * u + 22 := by unfold C; split <;> omega
  have h8 : C (54 * u + 22) = 27 * u + 11 := by unfold C; split <;> omega
  have g0 := Backtrack.nil (27 * u + 11)
  have g1 := Backtrack.even g0
  have v1 : 2 * (27 * u + 11) = 54 * u + 22 := by omega
  rw [v1] at g1
  have g2 := Backtrack.even g1
  have v2 : 2 * (54 * u + 22) = 108 * u + 44 := by omega
  rw [v2] at g2
  have g3 := Backtrack.odd g2 (show 3 * (72 * u + 29) + 1 = 2 * (108 * u + 44) by omega)
  have g4 := Backtrack.odd g3 (show 3 * (48 * u + 19) + 1 = 2 * (72 * u + 29) by omega)
  have g5 := Backtrack.even g4
  have v5 : 2 * (48 * u + 19) = 96 * u + 38 := by omega
  rw [v5] at g5
  have g6 := Backtrack.odd g5 (show 3 * (64 * u + 25) + 1 = 2 * (96 * u + 38) by omega)
  have g7 := Backtrack.even g6
  have v7 : 2 * (64 * u + 25) = 128 * u + 50 := by omega
  rw [v7] at g7
  exact ⟨by simp only [iterate, h0, h1, h2, h3, h4, h5, h6, h7, h8], g7⟩

theorem exit_one_profile (u : Nat) :
    iterate 10 (128 * u + 4) = 27 * u + 2 ∧
    Backtrack 5 2 (27 * u + 2) (384 * u + 26) := by
  have h0 : C (128 * u + 4) = 64 * u + 2 := by unfold C; split <;> omega
  have h1 : C (64 * u + 2) = 32 * u + 1 := by unfold C; split <;> omega
  have h2 : C (32 * u + 1) = 96 * u + 4 := by unfold C; split <;> omega
  have h3 : C (96 * u + 4) = 48 * u + 2 := by unfold C; split <;> omega
  have h4 : C (48 * u + 2) = 24 * u + 1 := by unfold C; split <;> omega
  have h5 : C (24 * u + 1) = 72 * u + 4 := by unfold C; split <;> omega
  have h6 : C (72 * u + 4) = 36 * u + 2 := by unfold C; split <;> omega
  have h7 : C (36 * u + 2) = 18 * u + 1 := by unfold C; split <;> omega
  have h8 : C (18 * u + 1) = 54 * u + 4 := by unfold C; split <;> omega
  have h9 : C (54 * u + 4) = 27 * u + 2 := by unfold C; split <;> omega
  have g0 := Backtrack.nil (27 * u + 2)
  have g1 := Backtrack.even g0
  have v1 : 2 * (27 * u + 2) = 54 * u + 4 := by omega
  rw [v1] at g1
  have g2 := Backtrack.even g1
  have v2 : 2 * (54 * u + 4) = 108 * u + 8 := by omega
  rw [v2] at g2
  have g3 := Backtrack.odd g2 (show 3 * (72 * u + 5) + 1 = 2 * (108 * u + 8) by omega)
  have g4 := Backtrack.even g3
  have v4 : 2 * (72 * u + 5) = 144 * u + 10 := by omega
  rw [v4] at g4
  have g5 := Backtrack.even g4
  have v5 : 2 * (144 * u + 10) = 288 * u + 20 := by omega
  rw [v5] at g5
  have g6 := Backtrack.odd g5 (show 3 * (192 * u + 13) + 1 = 2 * (288 * u + 20) by omega)
  have g7 := Backtrack.even g6
  have v7 : 2 * (192 * u + 13) = 384 * u + 26 := by omega
  rw [v7] at g7
  exact ⟨by simp only [iterate, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9], g7⟩

theorem finite_exit_periods :
    9 ^ 8 % 64 = 1 ∧ 9 ^ 7 % 64 = 57 ∧
    3 ^ 32 % 128 = 1 ∧ 3 ^ 21 % 128 = 51 ∧
    9 ^ 16 % 128 = 1 := by
  decide +kernel

theorem residue_seven (R : Nat) (hR : R % 8 = 7) : 9 ^ R % 64 = 57 := by
  have he : R = 8 * (R / 8) + 7 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
    finite_exit_periods.1, finite_exit_periods.2.1]
  simp

theorem residue_eleven (R : Nat) (hR : R % 16 = 11) :
    3 ^ (2 * R - 1) % 128 = 51 := by
  have he : 2 * R - 1 = 32 * (R / 16) + 21 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
    finite_exit_periods.2.2.1, finite_exit_periods.2.2.2.1]
  simp

theorem residue_one (R : Nat) (hR : R % 16 = 1) : 9 ^ R % 128 = 9 := by
  have he : R = 16 * (R / 16) + 1 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
    finite_exit_periods.2.2.2.2]
  simp

theorem seven_escape (R : Nat) (hR3 : 3 ≤ R) (hR : R % 8 = 7) :
    0 < 2 ^ (2 * R + 1) - 1 ∧
    2 ^ (2 * R + 1) - 1 < blockValue R 0 ∧
    Backtrack 5 (2 * R + 2) (iterate (5 * R + 8) (blockValue R 0))
      (2 ^ (2 * R + 1) - 1) ∧
    iterate (4 * R + 9) (2 ^ (2 * R + 1) - 1) =
      iterate (5 * R + 8) (blockValue R 0) := by
  let u := 9 ^ R / 64
  have hr := residue_seven R hR
  have hx : 9 ^ R = 64 * u + 57 := by dsimp [u]; omega
  have hy : 3 ^ (2 * R + 1) - 1 = 192 * u + 170 := by
    have hh : 3 ^ (2 * R + 1) = 3 * 9 ^ R := by
      rw [Nat.pow_add, Nat.pow_mul]
      change 9 ^ R * 3 = 3 * 9 ^ R
      omega
    rw [hh, hx]
    omega
  have ht : iterate (5 * R + 8) (blockValue R 0) = 9 * u + 8 := by
    rw [iterate_add, endpoint_clock, hx]
    have he : 64 * u + 57 - 5 = 64 * u + 52 := by omega
    rw [he]
    exact (exit_seven_profile u).1
  have hp := pure_inverse (2 * R + 1) 1 (by decide)
  simp only [Nat.mul_one] at hp
  rw [hy] at hp
  have hh := backtrack_append (exit_seven_profile u).2 hp
  have hb : Backtrack 5 (2 * R + 2) (iterate (5 * R + 8) (blockValue R 0))
      (2 ^ (2 * R + 1) - 1) := by
    rw [ht]
    simpa only [Nat.add_zero, show 1 + (2 * R + 1) = 2 * R + 2 by omega] using hh
  have hc := backtrack_actual hb
  have hclock : 5 + 2 * (2 * R + 2) = 4 * R + 9 := by omega
  rw [hclock] at hc
  exact ⟨(plus_smaller R hR3).1, (plus_smaller R hR3).2, hb, hc⟩

theorem eleven_escape (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 11) :
    0 < 2 ^ (2 * R - 1) - 1 ∧
    2 ^ (2 * R - 1) - 1 < blockValue R 0 ∧
    Backtrack 4 (2 * R + 2) (iterate (5 * R + 9) (blockValue R 0))
      (2 ^ (2 * R - 1) - 1) ∧
    iterate (4 * R + 8) (2 ^ (2 * R - 1) - 1) =
      iterate (5 * R + 9) (blockValue R 0) := by
  let u := 3 ^ (2 * R - 1) / 128
  have hr := residue_eleven R hR
  have hx : 3 ^ (2 * R - 1) = 128 * u + 51 := by dsimp [u]; omega
  have hX : 9 ^ R = 384 * u + 153 := by
    have he : 2 * R = (2 * R - 1) + 1 := by omega
    have hh : 9 ^ R = 3 * 3 ^ (2 * R - 1) := by
      calc
        _ = 3 ^ (2 * R) := by rw [Nat.pow_mul]
        _ = 3 ^ ((2 * R - 1) + 1) := congrArg (fun j => 3 ^ j) he
        _ = _ := by rw [Nat.pow_add]; omega
    rw [hh, hx]
    omega
  have ht : iterate (5 * R + 9) (blockValue R 0) = 27 * u + 11 := by
    rw [iterate_add, endpoint_clock, hX]
    have he : 384 * u + 153 - 5 = 384 * u + 148 := by omega
    rw [he]
    exact (exit_eleven_profile u).1
  have hy : 3 ^ (2 * R - 1) - 1 = 128 * u + 50 := by omega
  have hp := pure_inverse (2 * R - 1) 1 (by decide)
  simp only [Nat.mul_one] at hp
  rw [hy] at hp
  have hh := backtrack_append (exit_eleven_profile u).2 hp
  have hb : Backtrack 4 (2 * R + 2) (iterate (5 * R + 9) (blockValue R 0))
      (2 ^ (2 * R - 1) - 1) := by
    rw [ht]
    simpa only [Nat.add_zero, show 3 + (2 * R - 1) = 2 * R + 2 by omega] using hh
  have hc := backtrack_actual hb
  have hclock : 4 + 2 * (2 * R + 2) = 4 * R + 8 := by omega
  rw [hclock] at hc
  exact ⟨(minus_smaller R hR3).1, (minus_smaller R hR3).2, hb, hc⟩

theorem one_escape (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 1) :
    0 < 2 ^ (2 * R + 1) - 1 ∧
    2 ^ (2 * R + 1) - 1 < blockValue R 0 ∧
    Backtrack 5 (2 * R + 3) (iterate (5 * R + 10) (blockValue R 0))
      (2 ^ (2 * R + 1) - 1) ∧
    iterate (4 * R + 11) (2 ^ (2 * R + 1) - 1) =
      iterate (5 * R + 10) (blockValue R 0) := by
  let u := 9 ^ R / 128
  have hr := residue_one R hR
  have hx : 9 ^ R = 128 * u + 9 := by dsimp [u]; omega
  have hy : 3 ^ (2 * R + 1) - 1 = 384 * u + 26 := by
    have hh : 3 ^ (2 * R + 1) = 3 * 9 ^ R := by
      rw [Nat.pow_add, Nat.pow_mul]
      change 9 ^ R * 3 = 3 * 9 ^ R
      omega
    rw [hh, hx]
    omega
  have ht : iterate (5 * R + 10) (blockValue R 0) = 27 * u + 2 := by
    rw [iterate_add, endpoint_clock, hx]
    have he : 128 * u + 9 - 5 = 128 * u + 4 := by omega
    rw [he]
    exact (exit_one_profile u).1
  have hp := pure_inverse (2 * R + 1) 1 (by decide)
  simp only [Nat.mul_one] at hp
  rw [hy] at hp
  have hh := backtrack_append (exit_one_profile u).2 hp
  have hb : Backtrack 5 (2 * R + 3) (iterate (5 * R + 10) (blockValue R 0))
      (2 ^ (2 * R + 1) - 1) := by
    rw [ht]
    simpa only [Nat.add_zero, show 2 + (2 * R + 1) = 2 * R + 3 by omega] using hh
  have hc := backtrack_actual hb
  have hclock : 5 + 2 * (2 * R + 3) = 4 * R + 11 := by omega
  rw [hclock] at hc
  exact ⟨(plus_smaller R hR3).1, (plus_smaller R hR3).2, hb, hc⟩

theorem residue_not_least (R : Nat) (hR3 : 3 ≤ R)
    (hR : R % 8 = 7 ∨ R % 16 = 11 ∨ R % 16 = 1) :
    ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  rcases hR with hr | hr | hr
  · have hh := seven_escape R hR3 hr
    have hl := least_coalescing_predecessor hn hh.1 hh.2.2.2
    omega
  · have hh := eleven_escape R hR3 hr
    have hl := least_coalescing_predecessor hn hh.1 hh.2.2.2
    omega
  · have hh := one_escape R hR3 hr
    have hl := least_coalescing_predecessor hn hh.1 hh.2.2.2
    omega

theorem window_seven (s a : Nat) : windowExponent s (4 * a + 2) % 8 = 7 := by
  have hp : 3 ^ windowPrecision s % 4 = 1 := by
    unfold windowPrecision
    rw [Nat.pow_mul, Nat.pow_mod]
    simp
  let q := 3 ^ windowPrecision s / 4
  have he : 3 ^ windowPrecision s = 4 * q + 1 := by dsimp [q]; omega
  unfold windowExponent
  rw [he]
  have hx : 1 + 2 * (4 * q + 1) * (4 * a + 2 + 1) =
      8 * (4 * q * a + 3 * q + a) + 7 := by grind
  rw [hx]
  omega

theorem window_exit (s a : Nat) :
    let R := windowExponent s (4 * a + 2)
    let N := blockValue R 0
    let P := 2 ^ (2 * R + 1) - 1
    MinimumTailRigidity.prefixMinimum (5 * R) N = N ∧
    (∀ i, i < R → ∀ e o p, e ≤ i + s → Backtrack e o (hitValue R i) p → N ≤ p) ∧
    0 < P ∧ P < N ∧ iterate (4 * R + 9) P = iterate (5 * R + 8) N ∧
    ¬ LeastCounterexample N := by
  dsimp only
  have hR := window_exponent s (4 * a + 2)
  have hh := seven_escape _ hR.1 (window_seven s a)
  exact ⟨(window_prefix s (4 * a + 2)).1,
    fun i hi => (window_exact_minimum s (4 * a + 2) i hi).2,
    hh.1, hh.2.1, hh.2.2.2, residue_not_least _ hR.1 (Or.inl (window_seven s a))⟩

theorem unbounded_delayed_escape (s L B : Nat) :
    ∃ R P, 3 ≤ R ∧ R % 2 = 1 ∧ L < R - 1 ∧ B < blockValue R 0 ∧
      MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      (∀ i, i < R → ∀ e o p, e ≤ i + s → Backtrack e o (hitValue R i) p → blockValue R 0 ≤ p) ∧
      0 < P ∧ P < blockValue R 0 ∧
      iterate (4 * R + 9) P = iterate (5 * R + 8) (blockValue R 0) ∧
      ¬ LeastCounterexample (blockValue R 0) := by
  let a := L + B + 2
  let R := windowExponent s (4 * a + 2)
  have hr := window_exponent s (4 * a + 2)
  have hg := MinimumReturnLadder.source_growth R hr.1
  have hlarge : 4 * (L + B + 2) + 2 < R := hr.2.2
  have hh := window_exit s a
  exact ⟨R, 2 ^ (2 * R + 1) - 1, hr.1, hr.2.1, by omega, by omega, hh⟩

#print axioms source_identity
#print axioms endpoint_clock
#print axioms mersenne_clock
#print axioms plus_smaller
#print axioms minus_smaller
#print axioms cubic_gain_plus
#print axioms cubic_gain_minus
#print axioms exit_seven_profile
#print axioms exit_eleven_profile
#print axioms exit_one_profile
#print axioms finite_exit_periods
#print axioms residue_seven
#print axioms residue_eleven
#print axioms residue_one
#print axioms seven_escape
#print axioms eleven_escape
#print axioms one_escape
#print axioms residue_not_least
#print axioms window_seven
#print axioms window_exit
#print axioms unbounded_delayed_escape

end MinimumLadderExit

