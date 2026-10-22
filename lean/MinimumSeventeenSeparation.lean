/- Fixed exit clocks cannot cover the three negative-seventeen transition
   sources. This is a finite-window separation, not noncoalescence for all time. -/
import MinimumSeventeenTransition

namespace MinimumSeventeenSeparation
open OrdinaryCollatz MinimumSeventeenTransition

attribute [local irreducible] OrdinaryCollatz.iterate

def shadowStep (c : Nat) : Nat := if c % 2 = 1 then 3 * c - 9 else c / 2
def mainShadows : List Nat :=
  [225, 666, 333, 990, 495, 1476, 738, 369, 1098, 549, 1638, 819,
   2448, 1224, 612, 306, 153, 450]
def firstShadows : List Nat := [234, 117, 342, 171, 504, 252, 126, 63, 180, 90, 45]
def secondShadows : List Nat :=
  [217, 642, 321, 954, 477, 1422, 711, 2124, 1062, 531, 1584,
   792, 396, 198, 99, 288, 144, 72, 36, 18, 9]

def ShadowClosed (S : List Nat) : Prop :=
  ∀ c ∈ S, 9 ≤ c ∧ c < 4096 ∧ shadowStep c ∈ S

theorem finite_shadow_sets :
    ShadowClosed mainShadows ∧ ShadowClosed firstShadows ∧ ShadowClosed secondShadows ∧
    (∀ c ∈ mainShadows, ∀ d ∈ firstShadows, c ≠ d) ∧
    (∀ c ∈ mainShadows, ∀ d ∈ secondShadows, c ≠ d) := by
  unfold ShadowClosed
  decide +kernel

theorem shadow_step (n c d : Nat) (hc : 9 ≤ c) (h : 2 * d ∣ 9 * n + c) :
    d ∣ 9 * C n + shadowStep c := by
  obtain ⟨q, hq⟩ := h
  rw [Nat.mul_assoc] at hq
  have hp : n % 2 = c % 2 := by omega
  by_cases hn : n % 2 = 1
  · have hcodd : c % 2 = 1 := by omega
    have he : 9 * C n + shadowStep c = 3 * (9 * n + c) := by
      unfold C shadowStep
      rw [if_pos hn, if_pos hcodd]
      omega
    rw [he]
    refine ⟨6 * q, ?_⟩
    have hd : d * (6 * q) = 6 * (d * q) := by ac_rfl
    rw [hd]
    omega
  · have hne : n % 2 = 0 := by omega
    have hce : c % 2 ≠ 1 := by omega
    unfold C shadowStep
    rw [if_neg hn, if_neg hce]
    refine ⟨q, ?_⟩
    omega

theorem shadow_track (S : List Nat) (hS : ShadowClosed S) (t k n c : Nat)
    (hc : c ∈ S) (h : 2 ^ (k + t) ∣ 9 * n + c) :
    ∃ d ∈ S, 2 ^ k ∣ 9 * iterate t n + d := by
  induction t generalizing n c with
  | zero =>
    exact ⟨c, hc, by simpa only [Nat.add_zero, iterate] using h⟩
  | succ t ih =>
    have hpow : 2 ^ (k + (t + 1)) = 2 * 2 ^ (k + t) := by
      rw [show k + (t + 1) = (k + t) + 1 by omega, Nat.pow_succ]
      omega
    rw [hpow] at h
    have hs := shadow_step n c (2 ^ (k + t)) (hS c hc).1 h
    obtain ⟨d, hd, he⟩ := ih (C n) (shadowStep c) (hS c hc).2.2 hs
    exact ⟨d, hd, by simpa only [iterate] using he⟩

theorem shadow_separation (S T : List Nat) (hS : ShadowClosed S) (hT : ShadowClosed T)
    (hne : ∀ c ∈ S, ∀ d ∈ T, c ≠ d) (H n p c d : Nat)
    (hc : c ∈ S) (hd : d ∈ T)
    (hn : 2 ^ (H + 12) ∣ 9 * n + c) (hp : 2 ^ (H + 12) ∣ 9 * p + d) :
    ∀ s t, s ≤ H → t ≤ H → iterate s p ≠ iterate t n := by
  intro s t hs ht he
  have hns : 2 ^ (12 + t) ∣ 9 * n + c :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hn
  have hps : 2 ^ (12 + s) ∣ 9 * p + d :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hp
  obtain ⟨cn, hcn, hnn⟩ := shadow_track S hS t 12 n c hc hns
  obtain ⟨cp, hcp, hpp⟩ := shadow_track T hT s 12 p d hd hps
  have hbn := (hS cn hcn).2.1
  have hbp := (hT cp hcp).2.1
  have hdiff := hne cn hcn cp hcp
  have hmn := Nat.mod_eq_zero_of_dvd hnn
  have hmp := Nat.mod_eq_zero_of_dvd hpp
  rw [he] at hmp
  change (9 * iterate t n + cn) % 4096 = 0 at hmn
  change (9 * iterate t n + cp) % 4096 = 0 at hmp
  omega

theorem scalar_separation (H a : Nat) (ha : 0 < a)
    (h : 2 ^ (H + 12) ∣ 9 * a + 1) :
    ∀ s t, s ≤ H → t ≤ H →
      iterate s (81 * a - 17) ≠ iterate t (72 * a - 17) ∧
      iterate s (64 * a - 17) ≠ iterate t (72 * a - 17) := by
  have hN : 9 * (72 * a - 17) + 225 = 72 * (9 * a + 1) := by omega
  have hP : 9 * (81 * a - 17) + 234 = 81 * (9 * a + 1) := by omega
  have hQ : 9 * (64 * a - 17) + 217 = 64 * (9 * a + 1) := by omega
  have hn : 2 ^ (H + 12) ∣ 9 * (72 * a - 17) + 225 := by
    rw [hN]
    exact Nat.dvd_mul_left_of_dvd h 72
  have hp : 2 ^ (H + 12) ∣ 9 * (81 * a - 17) + 234 := by
    rw [hP]
    exact Nat.dvd_mul_left_of_dvd h 81
  have hq : 2 ^ (H + 12) ∣ 9 * (64 * a - 17) + 217 := by
    rw [hQ]
    exact Nat.dvd_mul_left_of_dvd h 64
  have f := finite_shadow_sets
  have p := shadow_separation _ _ f.1 f.2.1 f.2.2.2.1 H
    (72 * a - 17) (81 * a - 17) 225 234 (by decide) (by decide) hn hp
  have q := shadow_separation _ _ f.1 f.2.2.1 f.2.2.2.2 H
    (72 * a - 17) (64 * a - 17) 225 217 (by decide) (by decide) hn hq
  intro s t hs ht
  exact ⟨p s t hs ht, q s t hs ht⟩

theorem odd_power_cancel (k c x : Nat) (hc : c % 2 = 1)
    (h : 2 ^ k ∣ c * x) : 2 ^ k ∣ x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    rw [he] at h
    have htwo : 2 ∣ c * x := Nat.dvd_trans (Nat.dvd_mul_right 2 (2 ^ k)) h
    have hm := Nat.mod_eq_zero_of_dvd htwo
    rw [Nat.mul_mod, hc] at hm
    have hx : x = 2 * (x / 2) := by omega
    have hr : c * x = 2 * (c * (x / 2)) := by
      calc
        _ = c * (2 * (x / 2)) := congrArg (fun z => c * z) hx
        _ = _ := by ac_rfl
    rw [hr] at h
    have hi := ih (x / 2) (Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) h)
    rw [he, hx]
    exact Nat.mul_dvd_mul_left 2 hi

theorem unbounded_affine_lift (j A C B : Nat) (hA : A % 2 = 1)
    (hbase : (A + C) % 8 = 0) :
    ∃ R q, B < R ∧ 14 ≤ R ∧ A * 9 ^ R + C = 2 ^ (j + 3) * q := by
  obtain ⟨b, q, _, hq⟩ := MinimumLadderBlockExit.odd_affine_lift j A C hA hbase
  let P := 2 ^ j
  obtain ⟨c, hc⟩ := MinimumCriticalClockLift.nine_power_top_bit j
  obtain ⟨z, hz⟩ := MinimumInverseLocality.one_residue_powers
    (2 ^ (j + 3)) (9 ^ P) (2 * c + 1) (B + 14) hc
  let R := b + P * (B + 14)
  have hpow : 9 ^ R = 9 ^ b * (1 + 2 ^ (j + 3) * z) := by
    dsimp [R]
    rw [Nat.pow_add, Nat.pow_mul, hz]
  have hpos : 1 ≤ P := Nat.two_pow_pos j
  have hmul := Nat.mul_le_mul_right (B + 14) hpos
  have hbound : B < R ∧ 14 ≤ R := by dsimp [R]; omega
  refine ⟨R, q + A * 9 ^ b * z, hbound.1, hbound.2, ?_⟩
  rw [hpow]
  grind

theorem pure_shadow_lift (r H B : Nat) :
    ∃ R u, B < R ∧ 14 ≤ R ∧ 0 < u ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      2 ^ (H + 12) ∣ 9 * scalar r u + 1 := by
  let m := 57 + 11 * r
  let D := 2 ^ m
  let A := 3 ^ (35 + 7 * r)
  have hA : A % 2 = 1 := by dsimp [A]; rw [Nat.pow_mod]; simp
  have hscale : D = 8 * 2 ^ (54 + 11 * r) := by
    dsimp [D, m]
    rw [show 57 + 11 * r = (54 + 11 * r) + 3 by omega, Nat.pow_add]
    omega
  have hbase : (A + (7 * A + D)) % 8 = 0 := by rw [hscale]; omega
  obtain ⟨R, q, hB, hR, hq⟩ :=
    unbounded_affine_lift (m + H + 9) A (7 * A + D) B hA hbase
  have hpow : 2 ^ (m + H + 9 + 3) = D * 2 ^ (H + 12) := by
    rw [show m + H + 9 + 3 = m + (H + 12) by omega, Nat.pow_add]
  have hsum : A * (9 ^ R + 7) + D = D * (2 ^ (H + 12) * q) := by
    rw [hpow] at hq
    rw [Nat.mul_add]
    have hs : A * 7 = 7 * A := by omega
    rw [hs]
    simpa only [Nat.add_assoc, Nat.mul_assoc] using hq
  have hdiv : D ∣ A * (9 ^ R + 7) := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_refl D)).mpr
    exact ⟨2 ^ (H + 12) * q, hsum⟩
  have hunit := odd_power_cancel m A (9 ^ R + 7) hA hdiv
  obtain ⟨u, hu⟩ := hunit
  have hpos : 0 < 9 ^ R + 7 := Nat.succ_pos (9 ^ R + 6)
  have hup : 0 < u := Nat.pos_of_mul_pos_left (hu ▸ hpos)
  have hprod : D * (A * u + 1) = D * (2 ^ (H + 12) * q) := by
    have hs : D * (A * u + 1) = A * (D * u) + D := by
      rw [Nat.mul_add, Nat.mul_one]
      congr 1
      ac_rfl
    rw [hs, ← hu]
    exact hsum
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) hprod
  have hscalar : A * u = 9 * scalar r u := by
    dsimp [A, scalar]
    rw [show 35 + 7 * r = (33 + 7 * r) + 2 by omega, Nat.pow_add]
    ac_rfl
  rw [hscalar] at hcancel
  exact ⟨R, u, hB, hR, hup, hu, q, hcancel⟩

theorem unbounded_pure_separation (r H B : Nat) :
    ∃ R u, B < R ∧ 14 ≤ R ∧ 0 < u ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 99 + 18 * r + s) (firstSource R 1) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R 1) ∧
        iterate (4 * R + 99 + 18 * r + s) (secondSource R 1) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R 1) := by
  obtain ⟨R, u, hB, hR, hu, hX, hshadow⟩ := pure_shadow_lift r H B
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have ht := three_sources R 1 r u (by decide) hu (by simpa only [Nat.mul_one] using hX)
  have hs := scalar_separation H (scalar r u) ha hshadow
  refine ⟨R, u, hB, hR, hu, hX, ?_⟩
  intro s t hss htt
  simp only [iterate_add (4 * R + 99 + 18 * r) s,
    iterate_add (5 * R + 91 + 18 * r) t, ht.1, ht.2.1, ht.2.2]
  exact hs s t hss htt

theorem shadow_exit_residue (H a : Nat) (h : 2 ^ (H + 12) ∣ 9 * a + 1) :
    a % 64 = 7 := by
  have hd : 2 ^ 6 ∣ 9 * a + 1 := Nat.dvd_trans (Nat.pow_dvd_pow 2 (by omega)) h
  have hm := Nat.mod_eq_zero_of_dvd hd
  change (9 * a + 1) % 64 = 0 at hm
  omega

theorem weighted_shadow_lift (R r H B : Nat) :
    ∃ w u, B < w ∧ 0 < u ∧ 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      2 ^ (H + 12) ∣ 9 * scalar r u + 1 := by
  obtain ⟨S, u, hS, _, hu, hX, hs⟩ := pure_shadow_lift r H (R + B + 1)
  refine ⟨9 ^ (S - R), u, ?_, hu, ?_, hs⟩
  · exact Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  · rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX

theorem weighted_window_separation (R r H B : Nat) (hR : 14 ≤ R) :
    ∃ w u, B < w ∧ 0 < u ∧ 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      (0 < firstSource R w ∧ firstSource R w < mainSource R w) ∧
      (0 < secondSource R w ∧ secondSource R w < mainSource R w) ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 99 + 18 * r + s) (firstSource R w) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R w) ∧
        iterate (4 * R + 99 + 18 * r + s) (secondSource R w) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R w) := by
  obtain ⟨w, u, hwB, hu, hX, hshadow⟩ := weighted_shadow_lift R r H B
  have hw : 0 < w := by omega
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have ht := three_sources R w r u hw hu hX
  have hb := source_bounds R w hR hw
  have hs := scalar_separation H (scalar r u) ha hshadow
  refine ⟨w, u, hwB, hu, hX, hb.1, hb.2, ?_⟩
  intro s t hss htt
  simp only [iterate_add (4 * R + 99 + 18 * r) s,
    iterate_add (5 * R + 91 + 18 * r) t, ht.1, ht.2.1, ht.2.2]
  exact hs s t hss htt

theorem no_uniform_scalar_clock (r : Nat) :
    ¬ ∃ H, ∀ u, 0 < u → ∃ s t, s ≤ H ∧ t ≤ H ∧
      (iterate s (81 * scalar r u - 17) = iterate t (72 * scalar r u - 17) ∨
       iterate s (64 * scalar r u - 17) = iterate t (72 * scalar r u - 17)) := by
  rintro ⟨H, hH⟩
  obtain ⟨_, u, _, _, hu, _, hshadow⟩ := pure_shadow_lift r H 0
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  obtain ⟨s, t, hs, ht, he⟩ := hH u hu
  have hn := scalar_separation H (scalar r u) ha hshadow s t hs ht
  rcases he with he | he
  · exact hn.1 he
  · exact hn.2 he

def witnessWeight : Nat := 40485997700533351330544314970746016563530061325119216724809
def witnessUnit : Nat := 6426732526204138646359478836023285044640257771279812973

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem finite_convergent_witness :
    9 ^ 14 * witnessWeight + 7 = 2 ^ 57 * witnessUnit ∧
    2 ^ 140 ∣ 9 * scalar 0 witnessUnit + 1 ∧
    iterate 1795 (mainSource 14 witnessWeight) = 1 ∧
    iterate 1978 (firstSource 14 witnessWeight) = 1 ∧
    iterate 2660 (secondSource 14 witnessWeight) = 1 := by
  decide +kernel

#print axioms finite_shadow_sets
#print axioms shadow_step
#print axioms shadow_track
#print axioms shadow_separation
#print axioms scalar_separation
#print axioms odd_power_cancel
#print axioms unbounded_affine_lift
#print axioms pure_shadow_lift
#print axioms unbounded_pure_separation
#print axioms shadow_exit_residue
#print axioms weighted_shadow_lift
#print axioms weighted_window_separation
#print axioms no_uniform_scalar_clock
#print axioms finite_convergent_witness

end MinimumSeventeenSeparation

