/- A variable-length post-ladder block, descent to a preceding ladder,
   and explicit necessary conditions that still leave cases unresolved. -/
import MinimumLadderExit
import MinimumCriticalClockLift

namespace MinimumLadderBlockExit
open OrdinaryCollatz MinimumReturnLadder MinimumInverseEscape MinimumInverseLocality
open MinimumLadderExit MinimumRootPredecessors MinimumFirstTarget MinimumClockBarrier

theorem nine_odd_residue (R : Nat) (hR : R % 2 = 1) : 9 ^ R % 16 = 9 := by
  have he : R = 2 * (R / 2) + 1 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  simp

theorem bridge_profile (u : Nat) :
    iterate 5 (16 * u + 4) = 3 * u + 1 ∧
    Backtrack 3 1 (9 * u + 5) (48 * u + 26) := by
  have f0 : C (16 * u + 4) = 8 * u + 2 := by unfold C; split <;> omega
  have f1 : C (8 * u + 2) = 4 * u + 1 := by unfold C; split <;> omega
  have f2 : C (4 * u + 1) = 12 * u + 4 := by unfold C; split <;> omega
  have f3 : C (12 * u + 4) = 6 * u + 2 := by unfold C; split <;> omega
  have f4 : C (6 * u + 2) = 3 * u + 1 := by unfold C; split <;> omega
  have h0 := Backtrack.even (Backtrack.nil (9 * u + 5))
  have h1 := Backtrack.even h0
  have h2 := Backtrack.odd h1 (show 3 * (24 * u + 13) + 1 = 2 * (2 * (2 * (9 * u + 5))) by omega)
  have h3 := Backtrack.even h2
  have he : 2 * (24 * u + 13) = 48 * u + 26 := by omega
  rw [he] at h3
  exact ⟨by simp only [iterate, f0, f1, f2, f3, f4], h3⟩

theorem preceding_profile (u : Nat) :
    iterate 8 (1152 * u + 724) = 27 * u + 17 ∧
    iterate 10 (128 * u + 76) = 27 * u + 17 := by
  have f0 : C (1152 * u + 724) = 576 * u + 362 := by unfold C; split <;> omega
  have f1 : C (576 * u + 362) = 288 * u + 181 := by unfold C; split <;> omega
  have f2 : C (288 * u + 181) = 864 * u + 544 := by unfold C; split <;> omega
  have f3 : C (864 * u + 544) = 432 * u + 272 := by unfold C; split <;> omega
  have f4 : C (432 * u + 272) = 216 * u + 136 := by unfold C; split <;> omega
  have f5 : C (216 * u + 136) = 108 * u + 68 := by unfold C; split <;> omega
  have f6 : C (108 * u + 68) = 54 * u + 34 := by unfold C; split <;> omega
  have f7 : C (54 * u + 34) = 27 * u + 17 := by unfold C; split <;> omega
  have g0 : C (128 * u + 76) = 64 * u + 38 := by unfold C; split <;> omega
  have g1 : C (64 * u + 38) = 32 * u + 19 := by unfold C; split <;> omega
  have g2 : C (32 * u + 19) = 96 * u + 58 := by unfold C; split <;> omega
  have g3 : C (96 * u + 58) = 48 * u + 29 := by unfold C; split <;> omega
  have g4 : C (48 * u + 29) = 144 * u + 88 := by unfold C; split <;> omega
  have g5 : C (144 * u + 88) = 72 * u + 44 := by unfold C; split <;> omega
  have g6 : C (72 * u + 44) = 36 * u + 22 := by unfold C; split <;> omega
  have g7 : C (36 * u + 22) = 18 * u + 11 := by unfold C; split <;> omega
  have g8 : C (18 * u + 11) = 54 * u + 34 := by unfold C; split <;> omega
  have g9 : C (54 * u + 34) = 27 * u + 17 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0, f1, f2, f3, f4, f5, f6, f7], by simp only [iterate, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]⟩

theorem preceding_source_size (R : Nat) (hR : 3 ≤ R) :
    0 < blockValue (R - 1) 0 ∧ blockValue (R - 1) 0 < blockValue R 0 ∧
    blockValue R 0 = 8 * blockValue (R - 1) 0 + 35 := by
  have hp : 64 ≤ 8 ^ (R - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 2 ≤ R - 1 by omega)
  have he : R = (R - 1) + 1 := by omega
  have hh : 8 ^ R = 8 * 8 ^ (R - 1) := by
    calc
      _ = 8 ^ ((R - 1) + 1) := congrArg (fun j => 8 ^ j) he
      _ = _ := by rw [Nat.pow_add]; omega
  rw [source_identity, source_identity, hh]
  omega

theorem preceding_escape (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 3) :
    iterate (5 * R + 5) (blockValue (R - 1) 0) =
      iterate (5 * R + 8) (blockValue R 0) := by
  have hr : 9 ^ (R - 1) % 128 = 81 := by
    have he : R - 1 = 16 * (R / 16) + 2 := by omega
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
      finite_exit_periods.2.2.2.2]
    simp
  let u := 9 ^ (R - 1) / 128
  have hx : 9 ^ (R - 1) = 128 * u + 81 := by dsimp [u]; omega
  have hX : 9 ^ R = 1152 * u + 729 := by
    calc
      _ = 9 ^ ((R - 1) + 1) := congrArg (fun j => 9 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_add, hx]; omega
  have hs : 5 * R + 5 = 5 * (R - 1) + 10 := by omega
  rw [hs, iterate_add, iterate_add, endpoint_clock, endpoint_clock, hx, hX]
  have h1 : 128 * u + 81 - 5 = 128 * u + 76 := by omega
  have h2 : 1152 * u + 729 - 5 = 1152 * u + 724 := by omega
  rw [h1, h2, (preceding_profile u).1, (preceding_profile u).2]

theorem preceding_not_least (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 3) :
    ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  have hs := preceding_source_size R hR3
  have hl := least_coalescing_predecessor hn hs.1 (preceding_escape R hR3 hR)
  omega

theorem block_escape (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hq4 : (3 ^ k * q) % 4 = 3) :
    0 < 2 ^ (2 * R + 1) - 1 ∧ 2 ^ (2 * R + 1) - 1 < blockValue R 0 ∧
    Backtrack 5 (2 * R + k + 2)
      (iterate (5 * R + 2 * k + 8) (blockValue R 0)) (2 ^ (2 * R + 1) - 1) ∧
    iterate (4 * R + 2 * k + 9) (2 ^ (2 * R + 1) - 1) =
      iterate (5 * R + 2 * k + 8) (blockValue R 0) := by
  let u := 9 ^ R / 16
  have hr := nine_odd_residue R hR
  have hx : 9 ^ R = 16 * u + 9 := by dsimp [u]; omega
  have hd : 2 ^ k * q = 3 * u + 2 := by
    rw [Nat.pow_add, hx] at hX
    have he : 2 ^ k * 16 * q = 16 * (2 ^ k * q) := by ac_rfl
    change 3 * (16 * u + 9) + 5 = 2 ^ k * 16 * q at hX
    rw [he] at hX
    omega
  let v := (3 ^ k * q) / 4
  have hv : 3 ^ k * q = 4 * v + 3 := by dsimp [v]; omega
  have hd' : 2 ^ k * q - 1 = 3 * u + 1 := by omega
  have ht : iterate (5 * R + 2 * k + 8) (blockValue R 0) = 3 * v + 2 := by
    have he : 5 * R + 2 * k + 8 = (5 * R + 5) + (2 * k + 3) := by omega
    rw [he, iterate_add (5 * R + 5) (2 * k + 3), iterate_add (5 * R) 5,
      endpoint_clock, hx]
    have hsub : 16 * u + 9 - 5 = 16 * u + 4 := by omega
    rw [hsub, (bridge_profile u).1, ← hd']
    exact (half_source_meeting k q v hq hv).1
  have h0 := Backtrack.even (Backtrack.even (Backtrack.nil (3 * v + 2)))
  have hp := pure_inverse k (3 * q) (by omega)
  have ha : 3 ^ k * (3 * q) - 1 = 2 * (2 * (3 * v + 2)) := by
    have he : 3 ^ k * (3 * q) = 3 * (3 ^ k * q) := by ac_rfl
    rw [he, hv]
    omega
  have hb : 2 ^ k * (3 * q) - 1 = 9 * u + 5 := by
    have he : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by ac_rfl
    rw [he, hd]
    omega
  rw [ha, hb] at hp
  have h1 := backtrack_append h0 hp
  have h2 := backtrack_append h1 (bridge_profile u).2
  have hP := pure_inverse (2 * R + 1) 1 (by decide)
  simp only [Nat.mul_one] at hP
  have hy : 3 ^ (2 * R + 1) - 1 = 48 * u + 26 := by
    have he : 3 ^ (2 * R + 1) = 3 * 9 ^ R := by
      rw [Nat.pow_add, Nat.pow_mul]
      change 9 ^ R * 3 = 3 * 9 ^ R
      omega
    rw [he, hx]
    omega
  rw [hy] at hP
  have h3 := backtrack_append h2 hP
  have hback : Backtrack 5 (2 * R + k + 2)
      (iterate (5 * R + 2 * k + 8) (blockValue R 0)) (2 ^ (2 * R + 1) - 1) := by
    rw [ht]
    simpa only [Nat.add_zero, Nat.zero_add,
      show k + 1 + (2 * R + 1) = 2 * R + k + 2 by omega] using h3
  have hc := backtrack_actual hback
  rw [show 5 + 2 * (2 * R + k + 2) = 4 * R + 2 * k + 9 by omega] at hc
  exact ⟨(plus_smaller R hR3).1, (plus_smaller R hR3).2, hback, hc⟩

theorem block_not_least (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hq4 : (3 ^ k * q) % 4 = 3) : ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  have hh := block_escape R k q hR3 hR hq hX hq4
  have hl := least_coalescing_predecessor hn hh.1 hh.2.2.2
  omega

theorem three_mod_four_not_least (R : Nat) (hR3 : 3 ≤ R) (hR : R % 4 = 3) :
    ¬ LeastCounterexample (blockValue R 0) := by
  have hc : R % 8 = 7 ∨ R % 16 = 3 ∨ R % 16 = 11 := by omega
  rcases hc with hc | hc | hc
  · exact residue_not_least R hR3 (Or.inl hc)
  · exact preceding_not_least R hR3 hc
  · exact residue_not_least R hR3 (Or.inr (Or.inl hc))

theorem odd_factorization (n : Nat) (hn : 0 < n) :
    ∃ k q, 0 < q ∧ q % 2 = 1 ∧ n = 2 ^ k * q := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases ho : n % 2 = 1
    · exact ⟨0, n, hn, ho, by simp⟩
    · have he : n = 2 * (n / 2) := by omega
      obtain ⟨k, q, hq, hodd, hk⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨k + 1, q, hq, hodd, ?_⟩
      calc
        n = 2 * (n / 2) := he
        _ = 2 * (2 ^ k * q) := by rw [hk]
        _ = _ := by rw [Nat.pow_succ]; ac_rfl

theorem least_exponent_odd (R : Nat) (hR3 : 3 ≤ R)
    (hn : LeastCounterexample (blockValue R 0)) : R % 2 = 1 := by
  have hnot := least_not_two_mod3 hn
  apply Classical.byContradiction
  intro hr
  have he : R = 2 * (R / 2) := by omega
  have hp : 8 ^ R % 3 = 1 := by
    rw [he, Nat.pow_mul, Nat.pow_mod]
    simp
  have hbig : 512 ≤ 8 ^ R := Nat.pow_le_pow_right (by decide : 0 < 8) hR3
  rw [source_identity] at hnot
  omega

theorem least_exit_constraint (R : Nat) (hR3 : 3 ≤ R)
    (hn : LeastCounterexample (blockValue R 0)) :
    R % 4 = 1 ∧ ∃ k q, 0 < k ∧ 0 < q ∧ q % 2 = 1 ∧
      3 * 9 ^ R + 5 = 2 ^ (k + 4) * q ∧ (3 ^ k * q) % 4 = 1 := by
  have ho := least_exponent_odd R hR3 hn
  have hnot := three_mod_four_not_least R hR3
  have hR4 : R % 4 = 1 := by
    by_cases hh : R % 4 = 3
    · exact False.elim (hnot hh hn)
    · omega
  have hx32 : 9 ^ R % 32 = 9 := by
    have he : R = 4 * (R / 4) + 1 := by omega
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
    simp
  let d := (3 * 9 ^ R + 5) / 16
  have hd : 3 * 9 ^ R + 5 = 16 * d := by dsimp [d]; omega
  have hdpos : 0 < d := by
    have hp := Nat.pow_pos (by decide : 0 < 9) (n := R)
    omega
  obtain ⟨k, q, hq, hqo, hk⟩ := odd_factorization d hdpos
  have hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q := by
    rw [hd, hk, Nat.pow_add]
    change 16 * (2 ^ k * q) = 2 ^ k * 16 * q
    ac_rfl
  have hkpos : 0 < k := by
    by_cases hz : k = 0
    · simp only [hz, Nat.pow_zero, Nat.one_mul] at hk
      dsimp [d] at hk
      omega
    · omega
  have hodd : (3 ^ k * q) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hqo]
    simp
  have hbad : (3 ^ k * q) % 4 ≠ 3 := by
    intro hh
    exact block_not_least R k q hR3 ho hq hX hh hn
  exact ⟨hR4, k, q, hkpos, hq, hqo, hX, by omega⟩

theorem finite_surviving_period :
    9 ^ 512 % 4096 = 1 ∧ 9 ^ 5 % 4096 = 1705 := by decide +kernel

theorem surviving_progression (h : Nat) :
    let R := 512 * h + 5
    3 ≤ R ∧ R % 4 = 1 ∧ h < R ∧
    ∃ q, 0 < q ∧ q % 4 = 1 ∧
      3 * 9 ^ R + 5 = 2 ^ (6 + 4) * q ∧ (3 ^ 6 * q) % 4 = 1 := by
  dsimp only
  have hx : 9 ^ (512 * h + 5) % 4096 = 1705 := by
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
      finite_surviving_period.1, finite_surviving_period.2]
    simp
  let u := (3 * 9 ^ (512 * h + 5) + 5) / 4096
  have he : 3 * 9 ^ (512 * h + 5) + 5 = 4096 * u + 1024 := by dsimp [u]; omega
  refine ⟨by omega, by omega, by omega, 4 * u + 1, by omega, by omega, ?_, by omega⟩
  omega

theorem odd_affine_lift (j A C : Nat) (hA : A % 2 = 1)
    (hbase : (A + C) % 8 = 0) :
    ∃ r q, r < 2 ^ j ∧ A * 9 ^ r + C = 2 ^ (j + 3) * q := by
  induction j with
  | zero =>
    refine ⟨0, (A + C) / 8, by decide, ?_⟩
    simp only [Nat.pow_zero, Nat.mul_one]
    omega
  | succ j ih =>
    obtain ⟨r, q, hr, hq⟩ := ih
    obtain ⟨c, hc⟩ := MinimumCriticalClockLift.nine_power_top_bit j
    have hscale : 2 ^ (j + 1 + 3) = 2 * 2 ^ (j + 3) := by
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, Nat.pow_succ]
      omega
    have hp := Nat.two_pow_pos j
    by_cases hqe : q % 2 = 0
    · refine ⟨r, q / 2, by rw [Nat.pow_succ]; omega, ?_⟩
      have he : q = 2 * (q / 2) := by omega
      calc
        _ = 2 ^ (j + 3) * q := hq
        _ = 2 ^ (j + 3) * (2 * (q / 2)) := congrArg (fun x => 2 ^ (j + 3) * x) he
        _ = _ := by rw [hscale]; ac_rfl
    · let delta := A * 9 ^ r * (2 * c + 1)
      have hdelta : delta % 2 = 1 := by
        have h9 : 9 ^ r % 2 = 1 := by rw [Nat.pow_mod]; simp
        have hm : (A * 9 ^ r) % 2 = 1 := by rw [Nat.mul_mod, hA, h9]
        have ho : (2 * c + 1) % 2 = 1 := by omega
        dsimp [delta]
        rw [Nat.mul_mod, hm, ho]
      have heven : (q + delta) % 2 = 0 := by omega
      have he : q + delta = 2 * ((q + delta) / 2) := by omega
      refine ⟨r + 2 ^ j, (q + delta) / 2, by rw [Nat.pow_succ]; omega, ?_⟩
      calc
        _ = 2 ^ (j + 3) * (q + delta) := by
          rw [Nat.pow_add, hc]
          dsimp [delta]
          grind
        _ = 2 ^ (j + 3) * (2 * ((q + delta) / 2)) :=
          congrArg (fun x => 2 ^ (j + 3) * x) he
        _ = _ := by rw [hscale]; ac_rfl

theorem exit_unit (k : Nat) :
    let eps := if k % 2 = 0 then 3 else 1
    (eps = 1 ∨ eps = 3) ∧ (3 ^ k * eps) % 4 = 3 := by
  dsimp only
  by_cases hk : k % 2 = 0
  · rw [if_pos hk]
    refine ⟨Or.inr rfl, ?_⟩
    have he : k = 2 * (k / 2) := by omega
    rw [he, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
    simp
  · rw [if_neg hk]
    refine ⟨Or.inl rfl, ?_⟩
    have he : k = 2 * (k / 2) + 1 := by omega
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_one]
    change (9 ^ (k / 2) * 3) % 4 = 3
    rw [Nat.mul_mod, Nat.pow_mod]
    simp

theorem block_seed (k : Nat) :
    ∃ r q, r < 2 ^ (k + 3) ∧ 0 < q ∧ q % 2 = 1 ∧
      3 * 9 ^ r + 5 = 2 ^ (k + 4) * q ∧ (3 ^ k * q) % 4 = 3 := by
  let D := 2 ^ (k + 4)
  let eps := if k % 2 = 0 then 3 else 1
  have hu := exit_unit k
  have hep : eps = 1 ∨ eps = 3 := hu.1
  have hepspos : 0 < eps := by omega
  have hepslt : eps < 4 := by omega
  have hD : D = 8 * 2 ^ (k + 1) := by
    dsimp [D]
    rw [show k + 4 = (k + 1) + 3 by omega, Nat.pow_add]
    omega
  have hbase : (3 + (5 + (4 - eps) * D)) % 8 = 0 := by
    have he : 3 + (5 + (4 - eps) * D) = 8 * (1 + (4 - eps) * 2 ^ (k + 1)) := by
      rw [hD]
      grind
    rw [he]
    omega
  obtain ⟨r, Q, hr, hQ⟩ := odd_affine_lift (k + 3) 3 (5 + (4 - eps) * D) (by decide) hbase
  have hm : 2 ^ (k + 3 + 3) = 4 * D := by
    dsimp [D]
    rw [show k + 3 + 3 = (k + 4) + 2 by omega, Nat.pow_add]
    omega
  rw [hm] at hQ
  have hQpos : 1 ≤ Q := by
    by_cases hz : Q = 0
    · rw [hz, Nat.mul_zero] at hQ
      omega
    · omega
  let q := 4 * (Q - 1) + eps
  have hqm : q % 4 = eps := by dsimp [q]; omega
  have hqpos : 0 < q := by dsimp [q]; omega
  have hqodd : q % 2 = 1 := by dsimp [q]; omega
  have hcancel : D * q + (4 - eps) * D = 4 * D * Q := by
    dsimp [q]
    have he : Q = (Q - 1) + 1 := by omega
    have heps : eps + (4 - eps) = 4 := by omega
    grind
  have hX : 3 * 9 ^ r + 5 = D * q := by omega
  have hguard : (3 ^ k * q) % 4 = 3 := by
    rw [Nat.mul_mod, hqm]
    have hh : (3 ^ k * eps) % 4 = 3 := hu.2
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hepslt] at hh
    exact hh
  exact ⟨r, q, hr, hqpos, hqodd, hX, hguard⟩

theorem block_lift_odd (R k q : Nat)
    (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q) : R % 2 = 1 := by
  have hmod : (3 * 9 ^ R + 5) % 16 = 0 := by
    rw [hX, Nat.pow_add]
    have he : 2 ^ k * 16 * q = 16 * (2 ^ k * q) := by ac_rfl
    change (2 ^ k * 16 * q) % 16 = 0
    rw [he]
    omega
  by_cases ho : R % 2 = 1
  · exact ho
  · have he : R = 2 * (R / 2) := by omega
    have hr : 9 ^ R % 16 = 1 := by
      rw [he, Nat.pow_mul, Nat.pow_mod]
      simp
    omega

theorem unbounded_block_lifts (k B : Nat) :
    ∃ R q, B < R ∧ 3 ≤ R ∧ R % 2 = 1 ∧ 0 < q ∧ q % 2 = 1 ∧
      3 * 9 ^ R + 5 = 2 ^ (k + 4) * q ∧ (3 ^ k * q) % 4 = 3 := by
  obtain ⟨r, q, _, hq, hqo, hX, hg⟩ := block_seed k
  let P := 2 ^ (k + 3)
  let R := r + P * (B + 3)
  obtain ⟨c, hc⟩ := MinimumCriticalClockLift.nine_power_top_bit (k + 3)
  obtain ⟨z, hz⟩ := one_residue_powers (2 ^ (k + 3 + 3)) (9 ^ P) (2 * c + 1) (B + 3) hc
  have hm : 2 ^ (k + 3 + 3) = 4 * 2 ^ (k + 4) := by
    rw [show k + 3 + 3 = (k + 4) + 2 by omega, Nat.pow_add]
    omega
  rw [hm] at hz
  let Q := q + 4 * (3 * 9 ^ r * z)
  have hRpow : 9 ^ R = 9 ^ r * (1 + (4 * 2 ^ (k + 4)) * z) := by
    dsimp [R]
    rw [Nat.pow_add, Nat.pow_mul, hz]
  have hnew : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * Q := by
    rw [hRpow]
    dsimp [Q]
    grind
  have hQ : 0 < Q := by dsimp [Q]; omega
  have hQo : Q % 2 = 1 := by dsimp [Q]; omega
  have hQm : Q % 4 = q % 4 := by dsimp [Q]; omega
  have hQg : (3 ^ k * Q) % 4 = 3 := by
    rw [Nat.mul_mod, hQm]
    have hh := hg
    rw [Nat.mul_mod] at hh
    exact hh
  have hP : 1 ≤ P := Nat.two_pow_pos (k + 3)
  have hlarge := Nat.mul_le_mul_right (B + 3) hP
  have hRlarge : B < R ∧ 3 ≤ R := by dsimp [R]; omega
  exact ⟨R, Q, hRlarge.1, hRlarge.2, block_lift_odd R k Q hnew, hQ, hQo, hnew, hQg⟩

theorem unbounded_block_escapes (k B : Nat) :
    ∃ R P, 3 ≤ R ∧ R % 2 = 1 ∧ B < blockValue R 0 ∧
      MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      0 < P ∧ P < blockValue R 0 ∧
      iterate (4 * R + 2 * k + 9) P = iterate (5 * R + 2 * k + 8) (blockValue R 0) ∧
      ¬ LeastCounterexample (blockValue R 0) := by
  obtain ⟨R, q, hlarge, hR3, hRo, hq, _, hX, hg⟩ := unbounded_block_lifts k B
  have hs := block_escape R k q hR3 hRo hq hX hg
  have hn := MinimumReturnLadder.source_growth R hR3
  exact ⟨R, 2 ^ (2 * R + 1) - 1, hR3, hRo, by omega,
    (block_prefix R R (by omega)).2, hs.1, hs.2.1, hs.2.2.2,
    block_not_least R k q hR3 hRo hq hX hg⟩


def GoodResidue (n : Nat) : Prop :=
  n % 27 = 1 ∨ n % 27 = 2 ∨ n % 27 = 17 ∨ n % 27 = 26

theorem good_odd_pair (n : Nat) (hn : n % 2 = 1) (hg : GoodResidue n) :
    C n % 27 ≠ 20 ∧ GoodResidue (iterate 2 n) := by
  have hc : C n = 3 * n + 1 := by unfold C; rw [if_pos hn]
  have hp := odd_meeting n hn
  unfold GoodResidue at *
  rcases hg with hg | hg | hg | hg
  all_goals constructor
  all_goals first | (rw [hc]; omega) | omega

theorem odd_block_avoids (k q : Nat) (hq : 0 < q)
    (hg : GoodResidue (2 ^ k * q - 1)) :
    ∀ t, t ≤ 2 * k → iterate t (2 ^ k * q - 1) % 27 ≠ 20 := by
  induction k generalizing q with
  | zero =>
    intro t ht
    have ht0 : t = 0 := by omega
    rw [ht0]
    exact by unfold GoodResidue at hg; simp only [iterate]; omega
  | succ k ih =>
    have hp := Nat.mul_pos (Nat.two_pow_pos k) hq
    have he : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by rw [Nat.pow_succ]; ac_rfl
    have hn : (2 ^ (k + 1) * q - 1) % 2 = 1 := by rw [he]; omega
    have hs := good_odd_pair _ hn hg
    have hpair := odd_meeting _ hn
    have he3 : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by ac_rfl
    have hnext : iterate 2 (2 ^ (k + 1) * q - 1) = 2 ^ k * (3 * q) - 1 := by
      rw [he] at hpair
      rw [he, he3]
      omega
    have hgn : GoodResidue (2 ^ k * (3 * q) - 1) := by rw [← hnext]; exact hs.2
    intro t ht
    by_cases ht0 : t = 0
    · rw [ht0]
      exact by unfold GoodResidue at hg; simp only [iterate]; omega
    · by_cases ht1 : t = 1
      · rw [ht1]
        exact hs.1
      · have htime : t = 2 + (t - 2) := by omega
        rw [htime, iterate_add, hnext]
        exact ih (3 * q) (by omega) hgn (t - 2) (by omega)

theorem bridge_residues (u : Nat) (hu : (16 * u + 9) % 27 = 0) :
    iterate 5 (16 * u + 4) % 27 = 1 ∧
      ∀ t, t < 5 → iterate t (16 * u + 4) % 27 ≠ 20 := by
  have h0 : C (16 * u + 4) = 8 * u + 2 := by unfold C; split <;> omega
  have h1 : C (8 * u + 2) = 4 * u + 1 := by unfold C; split <;> omega
  have h2 : C (4 * u + 1) = 12 * u + 4 := by unfold C; split <;> omega
  have h3 : C (12 * u + 4) = 6 * u + 2 := by unfold C; split <;> omega
  constructor
  · rw [(bridge_profile u).1]
    omega
  · intro t ht
    have hh : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
    rcases hh with hh | hh | hh | hh | hh <;> subst t
    all_goals simp only [iterate, h0, h1, h2, h3]
    all_goals omega

theorem first_late_target (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hk : 2 ≤ k) (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hq4 : (3 ^ k * q) % 4 = 3) :
    iterate (5 * R + 2 * k + 8) (blockValue R 0) % 27 = 20 ∧
      ∀ t, 5 * R ≤ t → t < 5 * R + 2 * k + 8 →
        iterate t (blockValue R 0) % 27 ≠ 20 := by
  let u := 9 ^ R / 16
  have hr := nine_odd_residue R hR
  have hx : 9 ^ R = 16 * u + 9 := by dsimp [u]; omega
  have hx27 : 9 ^ R % 27 = 0 := by
    have he : R = 3 + (R - 3) := by omega
    rw [he, Nat.pow_add, Nat.mul_mod]
    simp
  have hu : (16 * u + 9) % 27 = 0 := by rw [← hx]; exact hx27
  have hd : 2 ^ k * q = 3 * u + 2 := by
    rw [Nat.pow_add, hx] at hX
    have he : 2 ^ k * 16 * q = 16 * (2 ^ k * q) := by ac_rfl
    change 3 * (16 * u + 9) + 5 = 2 ^ k * 16 * q at hX
    rw [he] at hX
    omega
  have hd' : 2 ^ k * q - 1 = 3 * u + 1 := by omega
  let v := (3 ^ k * q) / 4
  have hv : 3 ^ k * q = 4 * v + 3 := by dsimp [v]; omega
  have hq9 : (3 ^ k * q) % 9 = 0 := by
    have he : k = 2 + (k - 2) := by omega
    rw [he, Nat.pow_add]
    change (9 * 3 ^ (k - 2) * q) % 9 = 0
    rw [Nat.mul_assoc]
    omega
  have hv9 : v % 9 = 6 := by omega
  have hB : iterate (5 * R) (blockValue R 0) = 16 * u + 4 := by
    rw [endpoint_clock, hx]
    omega
  have hA : iterate (5 * R + 5) (blockValue R 0) = 2 ^ k * q - 1 := by
    rw [iterate_add, hB, (bridge_profile u).1, hd']
  have hgood : GoodResidue (2 ^ k * q - 1) := by
    apply Or.inl
    rw [hd', ← (bridge_profile u).1]
    exact (bridge_residues u hu).1
  have hZ : iterate ((5 * R + 5) + 2 * k) (blockValue R 0) = 4 * v + 2 := by
    rw [iterate_add, hA]
    have ho := (odd_block k 0 q hq).1
    simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at ho
    rw [ho, hv]
    omega
  have hc0 : C (4 * v + 2) = 2 * v + 1 := by unfold C; split <;> omega
  have hc1 : C (2 * v + 1) = 6 * v + 4 := by unfold C; split <;> omega
  have hc2 : C (6 * v + 4) = 3 * v + 2 := by unfold C; split <;> omega
  have hlast : ∀ t, t < 3 → iterate t (4 * v + 2) % 27 ≠ 20 := by
    intro t ht
    have hh : t = 0 ∨ t = 1 ∨ t = 2 := by omega
    rcases hh with hh | hh | hh <;> subst t
    all_goals simp only [iterate, hc0, hc1]
    all_goals omega
  constructor
  · have ht : 5 * R + 2 * k + 8 = ((5 * R + 5) + 2 * k) + 3 := by omega
    rw [ht, iterate_add _ 3, hZ]
    simp only [iterate, hc0, hc1, hc2]
    omega
  · intro t ht hupper
    by_cases hfirst : t < 5 * R + 5
    · have he : t = 5 * R + (t - 5 * R) := by omega
      rw [he, iterate_add, hB]
      exact (bridge_residues u hu).2 _ (by omega)
    · by_cases hmiddle : t ≤ (5 * R + 5) + 2 * k
      · have he : t = (5 * R + 5) + (t - (5 * R + 5)) := by omega
        rw [he, iterate_add, hA]
        exact odd_block_avoids k q hq hgood _ (by omega)
      · have he : t = ((5 * R + 5) + 2 * k) + (t - ((5 * R + 5) + 2 * k)) := by omega
        rw [he, iterate_add, hZ]
        exact hlast _ (by omega)

theorem unbounded_first_late_targets (k B : Nat) (hk : 2 ≤ k) :
    ∃ R P, 3 ≤ R ∧ R % 2 = 1 ∧ B < blockValue R 0 ∧
      MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      0 < P ∧ P < blockValue R 0 ∧
      (iterate (5 * R + 2 * k + 8) (blockValue R 0) % 27 = 20 ∧
        ∀ t, 5 * R ≤ t → t < 5 * R + 2 * k + 8 → iterate t (blockValue R 0) % 27 ≠ 20) ∧
      Backtrack 5 (2 * R + k + 2)
        (iterate (5 * R + 2 * k + 8) (blockValue R 0)) P ∧
      iterate (4 * R + 2 * k + 9) P = iterate (5 * R + 2 * k + 8) (blockValue R 0) ∧
      ¬ LeastCounterexample (blockValue R 0) := by
  obtain ⟨R, q, hlarge, hR3, hRo, hq, _, hX, hg⟩ := unbounded_block_lifts k B
  have hs := block_escape R k q hR3 hRo hq hX hg
  have hn := MinimumReturnLadder.source_growth R hR3
  exact ⟨R, 2 ^ (2 * R + 1) - 1, hR3, hRo, by omega,
    (block_prefix R R (by omega)).2, hs.1, hs.2.1,
    first_late_target R k q hR3 hRo hk hq hX hg, hs.2.2.1, hs.2.2.2,
    block_not_least R k q hR3 hRo hq hX hg⟩


#print axioms nine_odd_residue
#print axioms bridge_profile
#print axioms preceding_profile
#print axioms preceding_source_size
#print axioms preceding_escape
#print axioms preceding_not_least
#print axioms block_escape
#print axioms block_not_least
#print axioms three_mod_four_not_least
#print axioms odd_factorization
#print axioms least_exponent_odd
#print axioms least_exit_constraint
#print axioms finite_surviving_period
#print axioms surviving_progression
#print axioms odd_affine_lift
#print axioms exit_unit
#print axioms block_seed
#print axioms block_lift_odd
#print axioms unbounded_block_lifts
#print axioms unbounded_block_escapes

#print axioms good_odd_pair
#print axioms odd_block_avoids
#print axioms bridge_residues
#print axioms first_late_target
#print axioms unbounded_first_late_targets

end MinimumLadderBlockExit

