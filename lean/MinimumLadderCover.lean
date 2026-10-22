/- Three smaller sources cover the final return-ladder exponent class.
   This excludes least counterexamples; universal convergence is not claimed. -/
import MinimumLadderComplement

namespace MinimumLadderCover
open OrdinaryCollatz MinimumReturnLadder MinimumInverseEscape MinimumInverseLocality
open MinimumLadderExit MinimumLadderBlockExit MinimumLadderComplement
open MinimumFirstTarget MinimumRootPredecessors MinimumClockBarrier

def Merges (p n : Nat) : Prop := ∃ s t, iterate s p = iterate t n
def source (R q : Nat) : Nat := 8 ^ R * q - 5
def mersenne (R q : Nat) : Nat := 2 ^ (2 * R - 1) * q - 1
def preceding (R q : Nat) : Nat := source (R - 1) q
def smaller (R q : Nat) : Nat := source (R - 2) (2 * q)

theorem double_partner_even (b : Nat) (hb : b % 4 = 2) :
    iterate 3 (2 * b + 1) = iterate 2 b := by
  let v := b / 4
  have he : b = 4 * v + 2 := by dsimp [v]; omega
  have f0 : C (8 * v + 5) = 24 * v + 16 := by unfold C; split <;> omega
  have f1 : C (24 * v + 16) = 12 * v + 8 := by unfold C; split <;> omega
  have f2 : C (12 * v + 8) = 6 * v + 4 := by unfold C; split <;> omega
  have g0 : C (4 * v + 2) = 2 * v + 1 := by unfold C; split <;> omega
  have g1 : C (2 * v + 1) = 6 * v + 4 := by unfold C; split <;> omega
  rw [he, show 2 * (4 * v + 2) + 1 = 8 * v + 5 by omega]
  simp only [iterate, f0, f1, f2, g0, g1]

theorem ninth_partner_even (a b : Nat) (hb : b = 9 * a + 5) (he : b % 4 = 0) :
    iterate 4 a = iterate 2 b := by
  have ha : a % 4 = 3 := by omega
  let v := a / 4
  have hv : a = 4 * v + 3 := by dsimp [v]; omega
  have hb' : b = 36 * v + 32 := by omega
  have f0 : C (4 * v + 3) = 12 * v + 10 := by unfold C; split <;> omega
  have f1 : C (12 * v + 10) = 6 * v + 5 := by unfold C; split <;> omega
  have f2 : C (6 * v + 5) = 18 * v + 16 := by unfold C; split <;> omega
  have f3 : C (18 * v + 16) = 9 * v + 8 := by unfold C; split <;> omega
  have g0 : C (36 * v + 32) = 18 * v + 16 := by unfold C; split <;> omega
  rw [hv, hb']
  simp only [iterate, f0, f1, f2, f3, g0]

theorem adjacent_odd_block (k q : Nat) (hk : 0 < k) (hq : 0 < q)
    (hg : (3 ^ k * q) % 4 = 1) :
    iterate (2 * k + 2) (2 ^ k * q - 2) =
      iterate (2 * k + 2) (2 ^ k * q - 1) := by
  have hthree : 3 ^ k * q = 3 * (3 ^ (k - 1) * q) := by
    calc
      _ = 3 ^ ((k - 1) + 1) * q := congrArg (fun j => 3 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have hmod : (3 ^ (k - 1) * q) % 4 = 3 := by rw [hthree] at hg; omega
  let v := (3 ^ (k - 1) * q) / 4
  have hv : 3 ^ (k - 1) * q = 4 * v + 3 := by dsimp [v]; omega
  have hm := half_source_meeting (k - 1) q v hq hv
  have htwo : 2 ^ k * q = 2 * (2 ^ (k - 1) * q) := by
    calc
      _ = 2 ^ ((k - 1) + 1) * q := congrArg (fun j => 2 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have hp := Nat.mul_pos (Nat.two_pow_pos (k - 1)) hq
  have he : 2 ^ k * q - 2 = 2 * (2 ^ (k - 1) * q - 1) := by omega
  have hleft : iterate (2 * k + 2) (2 ^ k * q - 2) = 3 * v + 2 := by
    rw [he, show 2 * k + 2 = 1 + (2 * (k - 1) + 3) by omega, iterate_add]
    simpa only [iterate, even_step] using hm.1
  have hright : iterate (2 * k + 2) (2 ^ k * q - 1) = 3 * v + 2 := by
    simpa only [show k - 1 + 1 = k by omega,
      show 2 * (k - 1) + 4 = 2 * k + 2 by omega] using hm.2
  exact hleft.trans hright.symm

theorem odd_two_partner_cover (b : Nat) (hb : b % 2 = 1) :
    Merges (2 * b + 1) b ∨ Merges (b - 1) b := by
  obtain ⟨k, q, hq, hqo, he⟩ := odd_factorization (b + 1) (by omega)
  have hk : 0 < k := by
    by_cases hz : k = 0
    · simp only [hz, Nat.pow_zero, Nat.one_mul] at he
      omega
    · omega
  have hrep : b = 2 ^ k * q - 1 := by omega
  have hodd : (3 ^ k * q) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hqo]
    simp
  have hcases : (3 ^ k * q) % 4 = 1 ∨ (3 ^ k * q) % 4 = 3 := by omega
  rcases hcases with hc | hc
  · apply Or.inr
    refine ⟨2 * k + 2, 2 * k + 2, ?_⟩
    rw [hrep, Nat.sub_sub]
    exact adjacent_odd_block k q hk hq hc
  · apply Or.inl
    let v := (3 ^ k * q) / 4
    have hv : 3 ^ k * q = 4 * v + 3 := by dsimp [v]; omega
    have hm := half_source_meeting k q v hq hv
    have hp := Nat.mul_pos (Nat.two_pow_pos k) hq
    have ht : 2 * b + 1 = 2 ^ (k + 1) * q - 1 := by
      rw [Nat.pow_succ]
      have heq : 2 ^ k * 2 * q = 2 * (2 ^ k * q) := by ac_rfl
      rw [heq]
      omega
    refine ⟨2 * k + 4, 2 * k + 3, ?_⟩
    rw [ht, hrep, hm.1, hm.2]

theorem three_partner_cover (a b : Nat) (hb : b = 9 * a + 5) :
    Merges (2 * b + 1) b ∨ Merges (b - 1) b ∨ Merges a b := by
  by_cases ho : b % 2 = 1
  · rcases odd_two_partner_cover b ho with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have he : b % 4 = 0 ∨ b % 4 = 2 := by omega
    rcases he with he | he
    · exact Or.inr (Or.inr ⟨4, 2, ninth_partner_even a b hb he⟩)
    · exact Or.inl ⟨3, 2, double_partner_even b he⟩

theorem merger_transport (P N p n s t : Nat)
    (hP : iterate s P = p) (hN : iterate t N = n) (hm : Merges p n) : Merges P N := by
  obtain ⟨u, v, huv⟩ := hm
  exact ⟨s + u, t + v, by rw [iterate_add s u, iterate_add t v, hP, hN, huv]⟩

theorem source_bounds (R q : Nat) (hR : 3 ≤ R) (hq : 0 < q) :
    (0 < mersenne R q ∧ mersenne R q < source R q) ∧
    (0 < preceding R q ∧ preceding R q < source R q) ∧
    (0 < smaller R q ∧ smaller R q < source R q) ∧
    source R q + 5 = 8 * (preceding R q + 5) ∧
    source R q + 5 = 32 * (smaller R q + 5) := by
  have h8 : 8 ≤ 8 ^ (R - 2) :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R - 2 by omega)
  have hp := Nat.mul_le_mul h8 (show 1 ≤ q by omega)
  have h0 : 8 ^ R * q = 64 * (8 ^ (R - 2) * q) := by
    calc
      _ = 8 ^ ((R - 2) + 2) * q := congrArg (fun j => 8 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_add]; ac_rfl
  have h1 : 8 ^ (R - 1) * q = 8 * (8 ^ (R - 2) * q) := by
    rw [show R - 1 = (R - 2) + 1 by omega, Nat.pow_succ]
    ac_rfl
  have h2 : 8 ^ (R - 2) * (2 * q) = 2 * (8 ^ (R - 2) * q) := by ac_rfl
  have hm := minus_smaller R hR
  have hpow := Nat.two_pow_pos (2 * R - 1)
  have hgap : 2 ^ (2 * R - 1) + 4 < 8 ^ R := by
    rw [source_identity] at hm
    omega
  have hmul := Nat.mul_lt_mul_of_pos_right hgap hq
  rw [Nat.add_mul] at hmul
  have hpos := Nat.mul_pos hpow hq
  have hmono := Nat.mul_le_mul_left (2 ^ (2 * R - 1)) (show 1 ≤ q by omega)
  have hq4 := Nat.mul_le_mul_left 4 (show 1 ≤ q by omega)
  unfold mersenne preceding smaller source
  rw [h0, h1, h2] at *
  omega

theorem weighted_clock (R q : Nat) (hq : 0 < q) :
    iterate (5 * R) (source R q) = 9 ^ R * q - 5 := by
  have h := backtrack_actual (weighted_ladder R q hq)
  simpa only [source, show R + 2 * (2 * R) = 5 * R by omega] using h

theorem weighted_mersenne_clock (R q : Nat) (hq : 0 < q) :
    iterate (2 * (2 * R - 1)) (mersenne R q) = 3 ^ (2 * R - 1) * q - 1 := by
  have h := backtrack_actual (pure_inverse (2 * R - 1) q hq)
  simpa only [mersenne, Nat.zero_add] using h

theorem weighted_coordinates (R q : Nat) (hR : 3 ≤ R)
    (hr : (9 ^ R * q) % 128 = 73) :
    ∃ u v w, 9 ^ R * q = 384 * u + 201 ∧
      3 ^ (2 * R - 1) * q = 128 * u + 67 ∧
      9 ^ (R - 1) * q = 128 * v + 65 ∧
      9 ^ (R - 2) * q = 128 * w + 121 ∧
      27 * u + 14 = 81 * v + 41 ∧
      27 * u + 14 = 729 * w + 689 := by
  have h3 : 9 ^ R * q = 3 * (3 ^ (2 * R - 1) * q) := by
    have he : 9 ^ R = 3 ^ (2 * R) := by rw [Nat.pow_mul]
    calc
      _ = 3 ^ ((2 * R - 1) + 1) * q := by
        rw [he]
        exact congrArg (fun j => 3 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have h9 : 9 ^ R * q = 9 * (9 ^ (R - 1) * q) := by
    calc
      _ = 9 ^ ((R - 1) + 1) * q := congrArg (fun j => 9 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have h81 : 9 ^ R * q = 81 * (9 ^ (R - 2) * q) := by
    calc
      _ = 9 ^ ((R - 2) + 2) * q := congrArg (fun j => 9 ^ j * q) (by omega)
      _ = _ := by rw [Nat.pow_add]; ac_rfl
  have hmr : (3 ^ (2 * R - 1) * q) % 128 = 67 := by
    calc
      _ = (129 * (3 ^ (2 * R - 1) * q)) % 128 := by simp [Nat.mul_mod]
      _ = (43 * (9 ^ R * q)) % 128 := by rw [h3]; congr 1; omega
      _ = 67 := by rw [Nat.mul_mod, hr]
  have hpr : (9 ^ (R - 1) * q) % 128 = 65 := by
    calc
      _ = (513 * (9 ^ (R - 1) * q)) % 128 := by simp [Nat.mul_mod]
      _ = (57 * (9 ^ R * q)) % 128 := by rw [h9]; congr 1; omega
      _ = 65 := by rw [Nat.mul_mod, hr]
  have hdr : (9 ^ (R - 2) * q) % 128 = 121 := by
    calc
      _ = (3969 * (9 ^ (R - 2) * q)) % 128 := by simp [Nat.mul_mod]
      _ = (49 * (9 ^ R * q)) % 128 := by rw [h81]; congr 1; omega
      _ = 121 := by rw [Nat.mul_mod, hr]
  let u := (3 ^ (2 * R - 1) * q) / 128
  let v := (9 ^ (R - 1) * q) / 128
  let w := (9 ^ (R - 2) * q) / 128
  have hu : 3 ^ (2 * R - 1) * q = 128 * u + 67 := by
    have hh := Nat.mod_add_div (3 ^ (2 * R - 1) * q) 128
    rw [hmr] at hh
    simpa only [u, Nat.add_comm] using hh.symm
  have hv : 9 ^ (R - 1) * q = 128 * v + 65 := by
    have hh := Nat.mod_add_div (9 ^ (R - 1) * q) 128
    rw [hpr] at hh
    simpa only [v, Nat.add_comm] using hh.symm
  have hw : 9 ^ (R - 2) * q = 128 * w + 121 := by
    have hh := Nat.mod_add_div (9 ^ (R - 2) * q) 128
    rw [hdr] at hh
    simpa only [w, Nat.add_comm] using hh.symm
  clear hr hmr hpr hdr
  exact ⟨u, v, w, by omega, hu, hv, hw, by omega, by omega⟩

theorem partner_profiles (u : Nat) :
    iterate 9 (128 * u + 66) = 54 * u + 29 ∧
      iterate 11 (128 * u + 60) = 81 * u + 40 ∧
      iterate 12 (256 * u + 237) = 81 * u + 76 := by
  have m0 : C (128 * u + 66) = 64 * u + 33 := by unfold C; split <;> omega
  have m1 : C (64 * u + 33) = 192 * u + 100 := by unfold C; split <;> omega
  have m2 : C (192 * u + 100) = 96 * u + 50 := by unfold C; split <;> omega
  have m3 : C (96 * u + 50) = 48 * u + 25 := by unfold C; split <;> omega
  have m4 : C (48 * u + 25) = 144 * u + 76 := by unfold C; split <;> omega
  have m5 : C (144 * u + 76) = 72 * u + 38 := by unfold C; split <;> omega
  have m6 : C (72 * u + 38) = 36 * u + 19 := by unfold C; split <;> omega
  have m7 : C (36 * u + 19) = 108 * u + 58 := by unfold C; split <;> omega
  have m8 : C (108 * u + 58) = 54 * u + 29 := by unfold C; split <;> omega
  have p0 : C (128 * u + 60) = 64 * u + 30 := by unfold C; split <;> omega
  have p1 : C (64 * u + 30) = 32 * u + 15 := by unfold C; split <;> omega
  have p2 : C (32 * u + 15) = 96 * u + 46 := by unfold C; split <;> omega
  have p3 : C (96 * u + 46) = 48 * u + 23 := by unfold C; split <;> omega
  have p4 : C (48 * u + 23) = 144 * u + 70 := by unfold C; split <;> omega
  have p5 : C (144 * u + 70) = 72 * u + 35 := by unfold C; split <;> omega
  have p6 : C (72 * u + 35) = 216 * u + 106 := by unfold C; split <;> omega
  have p7 : C (216 * u + 106) = 108 * u + 53 := by unfold C; split <;> omega
  have p8 : C (108 * u + 53) = 324 * u + 160 := by unfold C; split <;> omega
  have p9 : C (324 * u + 160) = 162 * u + 80 := by unfold C; split <;> omega
  have p10 : C (162 * u + 80) = 81 * u + 40 := by unfold C; split <;> omega
  have d0 : C (256 * u + 237) = 768 * u + 712 := by unfold C; split <;> omega
  have d1 : C (768 * u + 712) = 384 * u + 356 := by unfold C; split <;> omega
  have d2 : C (384 * u + 356) = 192 * u + 178 := by unfold C; split <;> omega
  have d3 : C (192 * u + 178) = 96 * u + 89 := by unfold C; split <;> omega
  have d4 : C (96 * u + 89) = 288 * u + 268 := by unfold C; split <;> omega
  have d5 : C (288 * u + 268) = 144 * u + 134 := by unfold C; split <;> omega
  have d6 : C (144 * u + 134) = 72 * u + 67 := by unfold C; split <;> omega
  have d7 : C (72 * u + 67) = 216 * u + 202 := by unfold C; split <;> omega
  have d8 : C (216 * u + 202) = 108 * u + 101 := by unfold C; split <;> omega
  have d9 : C (108 * u + 101) = 324 * u + 304 := by unfold C; split <;> omega
  have d10 : C (324 * u + 304) = 162 * u + 152 := by unfold C; split <;> omega
  have d11 : C (162 * u + 152) = 81 * u + 76 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, m0, m1, m2, m3, m4, m5, m6, m7, m8],
    by simp only [iterate, p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10],
    by simp only [iterate, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]⟩

theorem three_sources (R q : Nat) (hR : 3 ≤ R) (hq : 0 < q)
    (hr : (9 ^ R * q) % 128 = 73) :
    ∃ a b, b = 9 * a + 5 ∧
      iterate (5 * R + 9) (source R q) = b ∧
      iterate (4 * R + 7) (mersenne R q) = 2 * b + 1 ∧
      iterate (5 * R + 6) (preceding R q) = b - 1 ∧
      iterate (5 * R + 2) (smaller R q) = a := by
  obtain ⟨u, v, w, hX, hM, hP, hD, huv, huw⟩ := weighted_coordinates R q hR hr
  have hn : iterate (5 * R + 9) (source R q) = 27 * u + 14 := by
    rw [iterate_add, weighted_clock R q hq, hX]
    have he : 384 * u + 201 - 5 = 384 * u + 196 := by omega
    rw [he, (remaining_profile u).1]
  have hm : iterate (4 * R + 7) (mersenne R q) = 54 * u + 29 := by
    rw [show 4 * R + 7 = 2 * (2 * R - 1) + 9 by omega, iterate_add,
      weighted_mersenne_clock R q hq, hM]
    have he : 128 * u + 67 - 1 = 128 * u + 66 := by omega
    rw [he, (partner_profiles u).1]
  have hp : iterate (5 * R + 6) (preceding R q) = 81 * v + 40 := by
    rw [show 5 * R + 6 = 5 * (R - 1) + 11 by omega, iterate_add]
    change iterate 11 (iterate (5 * (R - 1)) (source (R - 1) q)) = _
    rw [weighted_clock (R - 1) q hq, hP]
    have he : 128 * v + 65 - 5 = 128 * v + 60 := by omega
    rw [he, (partner_profiles v).2.1]
  have hd : iterate (5 * R + 2) (smaller R q) = 81 * w + 76 := by
    rw [show 5 * R + 2 = 5 * (R - 2) + 12 by omega, iterate_add]
    change iterate 12 (iterate (5 * (R - 2)) (source (R - 2) (2 * q))) = _
    rw [weighted_clock (R - 2) (2 * q) (by omega)]
    have he : 9 ^ (R - 2) * (2 * q) - 5 = 256 * w + 237 := by
      have heq : 9 ^ (R - 2) * (2 * q) = 2 * (9 ^ (R - 2) * q) := by ac_rfl
      rw [heq, hD]
      omega
    rw [he, (partner_profiles w).2.2]
  exact ⟨81 * w + 76, 27 * u + 14, by omega, hn,
    by rw [hm]; omega, by rw [hp]; omega, hd⟩

theorem weighted_residual_escape (R q : Nat) (hR : 3 ≤ R) (hq : 0 < q)
    (hr : (9 ^ R * q) % 128 = 73) :
    ∃ P, 0 < P ∧ P < source R q ∧
      (P = mersenne R q ∨ P = preceding R q ∨ P = smaller R q) ∧
      Merges P (source R q) := by
  obtain ⟨a, b, hb, hn, hm, hp, hd⟩ := three_sources R q hR hq hr
  have hs := source_bounds R q hR hq
  rcases three_partner_cover a b hb with h | h | h
  · exact ⟨mersenne R q, hs.1.1, hs.1.2, Or.inl rfl,
      merger_transport _ _ _ _ _ _ hm hn h⟩
  · exact ⟨preceding R q, hs.2.1.1, hs.2.1.2, Or.inr (Or.inl rfl),
      merger_transport _ _ _ _ _ _ hp hn h⟩
  · exact ⟨smaller R q, hs.2.2.1.1, hs.2.2.1.2, Or.inr (Or.inr rfl),
      merger_transport _ _ _ _ _ _ hd hn h⟩

theorem weighted_residual_not_least (R q : Nat) (hR : 3 ≤ R) (hq : 0 < q)
    (hr : (9 ^ R * q) % 128 = 73) : ¬ LeastCounterexample (source R q) := by
  intro hn
  obtain ⟨P, hP, hsmall, _, s, t, hmeet⟩ := weighted_residual_escape R q hR hq hr
  have hl := least_coalescing_predecessor hn hP hmeet
  omega

theorem all_ladder_not_least (R : Nat) (hR : 3 ≤ R) :
    ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  have hres := (least_exponent_nine R hR hn).1
  have he : R = 16 * (R / 16) + 9 := by omega
  have hr : 9 ^ R % 128 = 73 := by
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
      finite_exit_periods.2.2.2.2]
    simp
  have hbad := weighted_residual_not_least R 1 hR (by decide) (by simpa using hr)
  have hid : source R 1 = blockValue R 0 := by rw [source_identity]; simp [source]
  rw [hid] at hbad
  exact hbad hn

theorem finite_small_ladders : iterate 7 3 = 1 ∧ iterate 32 59 = 1 := by
  decide +kernel

theorem positive_ladder_not_least (R : Nat) (hR : 0 < R) :
    ¬ LeastCounterexample (blockValue R 0) := by
  by_cases hlarge : 3 ≤ R
  · exact all_ladder_not_least R hlarge
  · have hc : R = 1 ∨ R = 2 := by omega
    rcases hc with rfl | rfl
    · intro hn
      change LeastCounterexample 3 at hn
      exact hn.2.1 ⟨7, finite_small_ladders.1⟩
    · intro hn
      change LeastCounterexample 59 at hn
      exact hn.2.1 ⟨32, finite_small_ladders.2⟩

#print axioms double_partner_even
#print axioms ninth_partner_even
#print axioms adjacent_odd_block
#print axioms odd_two_partner_cover
#print axioms three_partner_cover
#print axioms merger_transport
#print axioms source_bounds
#print axioms weighted_clock
#print axioms weighted_mersenne_clock
#print axioms weighted_coordinates
#print axioms partner_profiles
#print axioms three_sources
#print axioms weighted_residual_escape
#print axioms weighted_residual_not_least
#print axioms all_ladder_not_least
#print axioms finite_small_ladders
#print axioms positive_ladder_not_least

end MinimumLadderCover


