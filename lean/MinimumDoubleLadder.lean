/- A variable-length coalescence for doubled weighted ladders, and an exact
   exponent restriction for the pure doubled family. The other exit is open. -/
import MinimumLadderCover

namespace MinimumDoubleLadder
open OrdinaryCollatz MinimumLadderCover MinimumLadderBlockExit
open MinimumRootPredecessors

theorem nine_quotient_mod_four (s : Nat) :
    ∃ u, 9 ^ s = 1 + 8 * u ∧ u % 4 = s % 4 := by
  induction s with
  | zero => exact ⟨0, by decide, by decide⟩
  | succ s ih =>
    obtain ⟨u, hu, hm⟩ := ih
    refine ⟨9 * u + 1, ?_, ?_⟩
    · rw [Nat.pow_succ, hu]
      omega
    · omega

theorem nine_unit_lift (k s : Nat) :
    ∃ u, 9 ^ (2 ^ k * s) = 1 + 2 ^ (k + 3) * u ∧ u % 4 = s % 4 := by
  induction k with
  | zero => simpa using nine_quotient_mod_four s
  | succ k ih =>
    obtain ⟨u, hu, hm⟩ := ih
    refine ⟨u + 2 ^ (k + 2) * u ^ 2, ?_, ?_⟩
    · have he : 2 ^ (k + 1) * s = (2 ^ k * s) * 2 := by
        rw [Nat.pow_succ]
        ac_rfl
      have hscale : 2 ^ (k + 3) = 2 * 2 ^ (k + 2) := by
        rw [show k + 3 = (k + 2) + 1 by omega, Nat.pow_succ]
        omega
      rw [he, Nat.pow_mul, hu]
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Nat.pow_succ, hscale]
      grind
    · have hz : 2 ^ (k + 2) % 4 = 0 := by
        rw [Nat.pow_add, Nat.mul_mod]
        simp
      rw [Nat.add_mod, Nat.mul_mod, hz]
      simpa using hm

theorem nine_unit_positive (k s : Nat) (hs : 0 < s) :
    ∃ u, 0 < u ∧ 9 ^ (2 ^ k * s) = 1 + 2 ^ (k + 3) * u ∧
      u % 4 = s % 4 := by
  obtain ⟨u, hu, hm⟩ := nine_unit_lift k s
  have hR := Nat.mul_pos (Nat.two_pow_pos k) hs
  have hp : 9 ≤ 9 ^ (2 ^ k * s) :=
    Nat.pow_le_pow_right (by decide : 0 < 9) (show 1 ≤ 2 ^ k * s by omega)
  refine ⟨u, ?_, hu, hm⟩
  by_cases hz : u = 0
  · simp only [hz, Nat.mul_zero, Nat.add_zero] at hu
    omega
  · omega

theorem adjacent_bridges (v : Nat) :
    iterate 6 (32 * v + 29) = 18 * v + 17 ∧
      iterate 5 (16 * v + 12) = 18 * v + 16 := by
  have f0 : C (32 * v + 29) = 96 * v + 88 := by unfold C; split <;> omega
  have f1 : C (96 * v + 88) = 48 * v + 44 := by unfold C; split <;> omega
  have f2 : C (48 * v + 44) = 24 * v + 22 := by unfold C; split <;> omega
  have f3 : C (24 * v + 22) = 12 * v + 11 := by unfold C; split <;> omega
  have f4 : C (12 * v + 11) = 36 * v + 34 := by unfold C; split <;> omega
  have f5 : C (36 * v + 34) = 18 * v + 17 := by unfold C; split <;> omega
  have g0 : C (16 * v + 12) = 8 * v + 6 := by unfold C; split <;> omega
  have g1 : C (8 * v + 6) = 4 * v + 3 := by unfold C; split <;> omega
  have g2 : C (4 * v + 3) = 12 * v + 10 := by unfold C; split <;> omega
  have g3 : C (12 * v + 10) = 6 * v + 5 := by unfold C; split <;> omega
  have g4 : C (6 * v + 5) = 18 * v + 16 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0, f1, f2, f3, f4, f5],
    by simp only [iterate, g0, g1, g2, g3, g4]⟩

theorem double_source_bounds (R w : Nat) (hR : 0 < R) (hw : 0 < w) :
    0 < source R w ∧ source R w < source R (2 * w) ∧
      source R (2 * w) + 5 = 2 * (source R w + 5) := by
  have hp : 8 ≤ 8 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R by omega)
  have hq := Nat.mul_le_mul hp (show 1 ≤ w by omega)
  have he : 8 ^ R * (2 * w) = 2 * (8 ^ R * w) := by ac_rfl
  unfold source
  rw [he]
  omega

theorem weighted_adjacent_profiles (R w a : Nat) (hw : 0 < w)
    (ha : 0 < a) (he : a % 2 = 0) (hX : 9 ^ R * w = 8 * a + 1) :
    iterate (5 * R + 6) (source R (2 * w)) = 9 * a - 1 ∧
      iterate (5 * R + 5) (source R w) = 9 * a - 2 := by
  let v := a / 2 - 1
  have hv : a = 2 * v + 2 := by dsimp [v]; omega
  have hN : 9 ^ R * (2 * w) - 5 = 32 * v + 29 := by
    have hh : 9 ^ R * (2 * w) = 2 * (9 ^ R * w) := by ac_rfl
    rw [hh, hX, hv]
    omega
  have hP : 9 ^ R * w - 5 = 16 * v + 12 := by rw [hX, hv]; omega
  constructor
  · rw [iterate_add, weighted_clock R (2 * w) (by omega), hN,
      (adjacent_bridges v).1, hv]
    omega
  · rw [iterate_add, weighted_clock R w hw, hP, (adjacent_bridges v).2, hv]
    omega

theorem weighted_double_meeting (R w k u : Nat) (hw : 0 < w)
    (hk : 0 < k) (hu : 0 < u)
    (hX : 9 ^ R * w = 1 + 2 ^ (k + 3) * u)
    (hg : (3 ^ k * u) % 4 = 1) :
    iterate (5 * R + 2 * k + 7) (source R w) =
      iterate (5 * R + 2 * k + 8) (source R (2 * w)) := by
  have ha := Nat.mul_pos (Nat.two_pow_pos k) hu
  have he : (2 ^ k * u) % 2 = 0 := by
    have hh : 2 ^ k = 2 * 2 ^ (k - 1) := by
      calc
        _ = 2 ^ ((k - 1) + 1) := congrArg (fun j => 2 ^ j) (by omega)
        _ = _ := by rw [Nat.pow_succ]; omega
    rw [hh, Nat.mul_mod]
    simp
  have hx : 9 ^ R * w = 8 * (2 ^ k * u) + 1 := by
    rw [Nat.pow_add] at hX
    have hh : 2 ^ k * 2 ^ 3 * u = 8 * (2 ^ k * u) := by
      change 2 ^ k * 8 * u = _
      ac_rfl
    rw [hh] at hX
    omega
  have hp := weighted_adjacent_profiles R w (2 ^ k * u) hw ha he hx
  have hm : (3 ^ k * (9 * u)) % 4 = 1 := by
    have hh : 3 ^ k * (9 * u) = 9 * (3 ^ k * u) := by ac_rfl
    rw [hh, Nat.mul_mod, hg]
  have hlocal := adjacent_odd_block k (9 * u) hk (by omega) hm
  have hh : 2 ^ k * (9 * u) = 9 * (2 ^ k * u) := by ac_rfl
  rw [hh] at hlocal
  rw [show 5 * R + 2 * k + 7 = (5 * R + 5) + (2 * k + 2) by omega,
    show 5 * R + 2 * k + 8 = (5 * R + 6) + (2 * k + 2) by omega,
    iterate_add (5 * R + 5) (2 * k + 2),
    iterate_add (5 * R + 6) (2 * k + 2), hp.1, hp.2]
  exact hlocal

theorem weighted_double_not_least (R w k u : Nat) (hR : 0 < R)
    (hw : 0 < w) (hk : 0 < k) (hu : 0 < u)
    (hX : 9 ^ R * w = 1 + 2 ^ (k + 3) * u)
    (hg : (3 ^ k * u) % 4 = 1) : ¬ LeastCounterexample (source R (2 * w)) := by
  intro hn
  have hs := double_source_bounds R w hR hw
  have hm := weighted_double_meeting R w k u hw hk hu hX hg
  have hl := least_coalescing_predecessor hn hs.1 hm
  omega

theorem double_odd_exponent_not_least (R : Nat) (hR : R % 2 = 1) :
    ¬ LeastCounterexample (source R 2) := by
  intro hn
  have he : R = 2 * (R / 2) + 1 := by omega
  have hp : 8 ^ R % 3 = 2 := by
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
    simp
  have h8 : 8 ≤ 8 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R by omega)
  have hbad := least_not_two_mod3 hn
  unfold source at hbad
  omega

theorem double_exponent_meeting (k s : Nat) (hk : 0 < k) (hs : 0 < s)
    (hg : (3 ^ k * s) % 4 = 1) :
    iterate (5 * (2 ^ k * s) + 2 * k + 7) (source (2 ^ k * s) 1) =
      iterate (5 * (2 ^ k * s) + 2 * k + 8) (source (2 ^ k * s) 2) := by
  obtain ⟨u, hu, hX, hm⟩ := nine_unit_positive k s hs
  have hg' : (3 ^ k * u) % 4 = 1 := by
    rw [Nat.mul_mod, hm, ← Nat.mul_mod]
    exact hg
  exact weighted_double_meeting (2 ^ k * s) 1 k u (by decide) hk hu
    (by simpa using hX) hg'

theorem double_exponent_not_least (k s : Nat) (hk : 0 < k) (hs : 0 < s)
    (hg : (3 ^ k * s) % 4 = 1) : ¬ LeastCounterexample (source (2 ^ k * s) 2) := by
  intro hn
  have hR := Nat.mul_pos (Nat.two_pow_pos k) hs
  have hsources := double_source_bounds (2 ^ k * s) 1 hR (by decide)
  simp only [Nat.mul_one] at hsources
  have hm := double_exponent_meeting k s hk hs hg
  have hl := least_coalescing_predecessor hn hsources.1 hm
  omega

theorem least_double_exponent_constraint (R : Nat) (hR : 0 < R)
    (hn : LeastCounterexample (source R 2)) :
    ∃ k s, 0 < k ∧ 0 < s ∧ s % 2 = 1 ∧ R = 2 ^ k * s ∧
      (3 ^ k * s) % 4 = 3 := by
  obtain ⟨k, s, hs, hso, he⟩ := odd_factorization R hR
  have hk : 0 < k := by
    by_cases hz : k = 0
    · simp only [hz, Nat.pow_zero, Nat.one_mul] at he
      have hodd : R % 2 = 1 := by omega
      exact False.elim (double_odd_exponent_not_least R hodd hn)
    · omega
  have ho : (3 ^ k * s) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hso]
    simp
  have hm : (3 ^ k * s) % 4 = 3 := by
    by_cases hh : (3 ^ k * s) % 4 = 1
    · exact False.elim (double_exponent_not_least k s hk hs hh (he ▸ hn))
    · omega
  exact ⟨k, s, hk, hs, hso, he, hm⟩

#print axioms nine_quotient_mod_four
#print axioms nine_unit_lift
#print axioms nine_unit_positive
#print axioms adjacent_bridges
#print axioms double_source_bounds
#print axioms weighted_adjacent_profiles
#print axioms weighted_double_meeting
#print axioms weighted_double_not_least
#print axioms double_odd_exponent_not_least
#print axioms double_exponent_meeting
#print axioms double_exponent_not_least
#print axioms least_double_exponent_constraint

end MinimumDoubleLadder
