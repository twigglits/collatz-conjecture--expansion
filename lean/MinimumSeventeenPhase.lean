/- Halving phases distinguish positive trajectories even when their negative
   reference patterns share a cycle. All separations are finite-window results. -/
import MinimumSeventeenFourth

namespace MinimumSeventeenPhase
open OrdinaryCollatz MinimumSeventeenSeparation MinimumSeventeenTransition
open MinimumSeventeenFourth

attribute [local irreducible] OrdinaryCollatz.iterate

def refStep (M c : Nat) : Nat := if c % 2 = 1 then 3 * c - M else c / 2

def phaseStep (M L : Nat) (s : Nat × Nat) : Nat × Nat :=
  (refStep M s.1, if s.1 % 2 = 1 then s.2 else (s.2 + 1) % L)

def PhaseClosed (M L B : Nat) (S : List (Nat × Nat)) : Prop :=
  ∀ s ∈ S, M ≤ s.1 ∧ s.1 < 2 ^ B ∧ phaseStep M L s ∈ S

theorem binary_exponent_unique (e f u v : Nat) (hu : u % 2 = 1) (hv : v % 2 = 1)
    (h : 2 ^ e * u = 2 ^ f * v) : e = f := by
  induction e generalizing f with
  | zero =>
    cases f with
    | zero => rfl
    | succ f =>
      have hd : 2 ∣ 2 ^ (f + 1) * v :=
        Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 (show 1 ≤ f + 1 by omega)) v
      simp only [Nat.pow_zero, Nat.one_mul] at h
      rw [← h] at hd
      have hm := Nat.mod_eq_zero_of_dvd hd
      omega
  | succ e ih =>
    cases f with
    | zero =>
      have hd : 2 ∣ 2 ^ (e + 1) * u :=
        Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 (show 1 ≤ e + 1 by omega)) u
      simp only [Nat.pow_zero, Nat.one_mul] at h
      rw [h] at hd
      have hm := Nat.mod_eq_zero_of_dvd hd
      omega
    | succ f =>
      have he : 2 ^ (e + 1) * u = 2 * (2 ^ e * u) := by rw [Nat.pow_succ]; ac_rfl
      have hf : 2 ^ (f + 1) * v = 2 * (2 ^ f * v) := by rw [Nat.pow_succ]; ac_rfl
      rw [he, hf] at h
      have hi := ih f (Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h)
      omega

theorem exact_phase_step (M n c e u : Nat) (hM : M % 2 = 1) (hc : M ≤ c)
    (he : 0 < e) (hu : u % 2 = 1) (h : M * n + c = 2 ^ e * u) :
    ∃ f v d, v % 2 = 1 ∧ d ≤ 1 ∧ e = f + d ∧
      M * C n + refStep M c = 2 ^ f * v ∧
      d = if c % 2 = 1 then 0 else 1 := by
  have hp : 2 ^ e = 2 * 2 ^ (e - 1) := by
    calc
      _ = 2 ^ ((e - 1) + 1) := congrArg (fun z => 2 ^ z) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  have hmod : (M * n + c) % 2 = 0 := by rw [h, hp, Nat.mul_assoc]; omega
  rw [Nat.add_mod, Nat.mul_mod, hM] at hmod
  have hn : n % 2 = c % 2 := by omega
  by_cases ho : c % 2 = 1
  · have hno : n % 2 = 1 := hn.trans ho
    have hs : M * C n + refStep M c = 3 * (M * n + c) := by
      unfold C refStep
      rw [if_pos hno, if_pos ho, Nat.mul_add, Nat.mul_one]
      have hm : M * (3 * n) = 3 * (M * n) := by ac_rfl
      rw [hm]
      omega
    refine ⟨e, 3 * u, 0, ?_, by omega, by omega, ?_, by simp [ho]⟩
    · simp [Nat.mul_mod, hu]
    · rw [hs, h]
      ac_rfl
  · have hne : n % 2 ≠ 1 := by omega
    have hn2 : n = 2 * (n / 2) := by omega
    have hc2 : c = 2 * (c / 2) := by omega
    have hs : 2 * (M * C n + refStep M c) = M * n + c := by
      unfold C refStep
      rw [if_neg hne, if_neg ho]
      have hm : M * n = 2 * (M * (n / 2)) := by
        calc
          _ = M * (2 * (n / 2)) := congrArg (fun z => M * z) hn2
          _ = _ := by ac_rfl
      rw [hm]
      omega
    refine ⟨e - 1, u, 1, hu, by omega, by omega, ?_, by simp [ho]⟩
    rw [h, hp] at hs
    have heq : 2 * (M * C n + refStep M c) = 2 * (2 ^ (e - 1) * u) := by
      simpa only [Nat.mul_assoc] using hs
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) heq

theorem phase_track (M L B : Nat) (S : List (Nat × Nat))
    (hM : M % 2 = 1) (hS : PhaseClosed M L B S)
    (t k E n c h u : Nat) (hc : (c, h % L) ∈ S) (hE : k + t ≤ E)
    (hu : u % 2 = 1) (hx : M * n + c = 2 ^ E * u) :
    ∃ d e v h', (d, h' % L) ∈ S ∧ k ≤ e ∧ e + h' = E + h ∧
      v % 2 = 1 ∧ M * iterate t n + d = 2 ^ e * v := by
  induction t generalizing E n c h u with
  | zero =>
    exact ⟨c, E, u, h, hc, by omega, rfl, hu, by simpa only [iterate] using hx⟩
  | succ t ih =>
    obtain ⟨e, v, d, hv, hd, hEe, hs, hdelta⟩ :=
      exact_phase_step M n c E u hM (hS (c, h % L) hc).1 (by omega) hu hx
    have hnext : (refStep M c, (h + d) % L) ∈ S := by
      have hn := (hS (c, h % L) hc).2.2
      unfold phaseStep at hn
      dsimp at hn
      by_cases ho : c % 2 = 1
      · simp only [ho, if_true] at hn hdelta
        simpa only [hdelta, Nat.add_zero] using hn
      · simp only [ho, if_false] at hn hdelta
        simpa only [hdelta, Nat.add_mod, Nat.mod_mod] using hn
    obtain ⟨z, f, w, h', hz, hf, hh, hw, heq⟩ :=
      ih e (C n) (refStep M c) (h + d) v hnext (by omega) hv hs
    exact ⟨z, f, w, h', hz, hf, by omega, hw, by simpa only [iterate] using heq⟩

theorem phase_separation (M L B : Nat) (S T : List (Nat × Nat))
    (hM : M % 2 = 1) (hS : PhaseClosed M L B S) (hT : PhaseClosed M L B T)
    (A D : Nat)
    (hdis : ∀ c h, (c, h) ∈ S → ∀ d k, (d, k) ∈ T →
      c = d → (h + D) % L ≠ (k + A) % L)
    (H K n p c d u v : Nat) (hK : H + B ≤ K)
    (hc : (c, 0) ∈ S) (hd : (d, 0) ∈ T)
    (hu : u % 2 = 1) (hv : v % 2 = 1)
    (hn : M * n + c = 2 ^ (K + A) * u)
    (hp : M * p + d = 2 ^ (K + D) * v) :
    ∀ s t, s ≤ H → t ≤ H → iterate s p ≠ iterate t n := by
  intro s t hs ht heq
  obtain ⟨cn, en, un, hn', hcn, hen, hsumN, hun, hvalN⟩ :=
    phase_track M L B S hM hS t B (K + A) n c 0 u
      (by simpa only [Nat.zero_mod] using hc) (by omega) hu hn
  obtain ⟨cp, ep, up, hp', hcp, hep, hsumP, hup, hvalP⟩ :=
    phase_track M L B T hM hT s B (K + D) p d 0 v
      (by simpa only [Nat.zero_mod] using hd) (by omega) hv hp
  have hnD : 2 ^ B ∣ M * iterate t n + cn := by
    rw [hvalN]
    exact Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hen) un
  have hpD : 2 ^ B ∣ M * iterate s p + cp := by
    rw [hvalP]
    exact Nat.dvd_mul_right_of_dvd (Nat.pow_dvd_pow 2 hep) up
  have hnmod := Nat.mod_eq_zero_of_dvd hnD
  have hpmod := Nat.mod_eq_zero_of_dvd hpD
  rw [heq] at hpmod hvalP
  have hnBound := (hS (cn, hn' % L) hcn).2.1
  have hpBound := (hT (cp, hp' % L) hcp).2.1
  have heqc : cn = cp := by
    obtain ⟨i, j, hij⟩ := Nat.mod_eq_mod_iff.mp (hnmod.trans hpmod.symm)
    have hsmall : cn + i * 2 ^ B = cp + j * 2 ^ B := by omega
    have hmod := Nat.mod_eq_mod_iff.mpr ⟨i, j, hsmall⟩
    simpa only [Nat.mod_eq_of_lt hnBound, Nat.mod_eq_of_lt hpBound] using hmod
  rw [← heqc] at hvalP
  have he : en = ep := binary_exponent_unique en ep un up hun hup (hvalN.symm.trans hvalP)
  have hcount : hn' + D = hp' + A := by omega
  have hphase : (hn' % L + D) % L = (hp' % L + A) % L := by
    simpa only [Nat.add_mod, Nat.mod_mod] using congrArg (fun z => z % L) hcount
  exact hdis cn (hn' % L) hcn cp (hp' % L) hcp heqc hphase

def mainPhases : List (Nat × Nat) :=
  [(225, 0), (666, 0), (333, 1), (990, 1), (495, 2), (1476, 2), (738, 3), (369, 4), (1098, 4), (549, 5), (1638, 5), (819, 6), (2448, 6), (1224, 7), (612, 8), (306, 9), (153, 10), (450, 10)]

def fourthPhases : List (Nat × Nat) :=
  [(201, 0), (594, 0), (297, 1), (882, 1), (441, 2), (1314, 2), (657, 3), (1962, 3), (981, 4), (2934, 4), (1467, 5), (4392, 5), (2196, 6), (1098, 7), (549, 8), (1638, 8), (819, 9), (2448, 9), (1224, 10), (612, 0), (306, 1), (153, 2), (450, 2), (225, 3), (666, 3), (333, 4), (990, 4), (495, 5), (1476, 5), (738, 6), (369, 7)]

def exitMainPhases : List (Nat × Nat) :=
  [(13, 0), (38, 0), (19, 1), (56, 1), (28, 2), (14, 0), (7, 1), (20, 1), (10, 2), (5, 0)]

def exitPartnerPhases : List (Nat × Nat) :=
  [(14, 0), (7, 1), (20, 1), (10, 2), (5, 0)]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem finite_phase_sets :
    PhaseClosed 9 11 13 mainPhases ∧ PhaseClosed 9 11 13 fourthPhases ∧
    (∀ c h, (c, h) ∈ mainPhases → ∀ d k, (d, k) ∈ fourthPhases →
      c = d → (h + 4) % 11 ≠ (k + 3) % 11) ∧
    PhaseClosed 1 3 6 exitMainPhases ∧ PhaseClosed 1 3 6 exitPartnerPhases ∧
    (∀ c h, (c, h) ∈ exitMainPhases → ∀ d k, (d, k) ∈ exitPartnerPhases →
      c = d → (h + 0) % 3 ≠ (k + 2) % 3) := by
  refine ⟨by unfold PhaseClosed; decide +kernel, by unfold PhaseClosed; decide +kernel,
    ?_, by unfold PhaseClosed; decide +kernel, by unfold PhaseClosed; decide +kernel, ?_⟩
  · have h : ∀ x ∈ mainPhases, ∀ y ∈ fourthPhases,
        x.1 = y.1 → (x.2 + 4) % 11 ≠ (y.2 + 3) % 11 := by decide +kernel
    exact fun c h' hc d k hd => h (c, h') hc (d, k) hd
  · have h : ∀ x ∈ exitMainPhases, ∀ y ∈ exitPartnerPhases,
        x.1 = y.1 → (x.2 + 0) % 3 ≠ (y.2 + 2) % 3 := by decide +kernel
    exact fun c h' hc d k hd => h (c, h') hc (d, k) hd

theorem exact_binary_from_divisibility (n K : Nat) (hn : 0 < n) (hd : 2 ^ K ∣ n) :
    ∃ E u, K ≤ E ∧ u % 2 = 1 ∧ n = 2 ^ E * u := by
  obtain ⟨q, hq⟩ := hd
  have hqp : 0 < q := Nat.pos_of_mul_pos_left (hq ▸ hn)
  obtain ⟨k, u, _, hu, heq⟩ := MinimumLadderBlockExit.odd_factorization q hqp
  refine ⟨K + k, u, by omega, hu, ?_⟩
  rw [hq, heq, Nat.pow_add, Nat.mul_assoc]

theorem fourth_scalar_separation (H a : Nat) (ha : 0 < a)
    (h : 2 ^ (H + 13) ∣ 9 * a + 1) :
    ∀ s t, s ≤ H → t ≤ H →
      iterate s (48 * a - 17) ≠ iterate t (72 * a - 17) := by
  obtain ⟨K, u, hK, hu, hcoord⟩ :=
    exact_binary_from_divisibility (9 * a + 1) (H + 13) (by omega) h
  have hn : 9 * (72 * a - 17) + 225 = 2 ^ (K + 3) * (9 * u) := by
    have hl : 9 * (72 * a - 17) + 225 = 72 * (9 * a + 1) := by omega
    rw [hl, hcoord, Nat.pow_add]
    change (8 * 9) * (2 ^ K * u) = (2 ^ K * 8) * (9 * u)
    ac_rfl
  have hp : 9 * (48 * a - 17) + 201 = 2 ^ (K + 4) * (3 * u) := by
    have hl : 9 * (48 * a - 17) + 201 = 48 * (9 * a + 1) := by omega
    rw [hl, hcoord, Nat.pow_add]
    change (16 * 3) * (2 ^ K * u) = (2 ^ K * 16) * (3 * u)
    ac_rfl
  exact phase_separation 9 11 13 mainPhases fourthPhases (by decide)
    finite_phase_sets.1 finite_phase_sets.2.1 3 4 finite_phase_sets.2.2.1
    H K (72 * a - 17) (48 * a - 17) 225 201 (9 * u) (3 * u) hK
    (by decide) (by decide) (by simp [Nat.mul_mod, hu]) (by simp [Nat.mul_mod, hu]) hn hp

theorem four_scalar_separation (H a : Nat) (ha : 0 < a)
    (h : 2 ^ (H + 13) ∣ 9 * a + 1) :
    ∀ s t, s ≤ H → t ≤ H →
      iterate s (81 * a - 17) ≠ iterate t (72 * a - 17) ∧
      iterate s (64 * a - 17) ≠ iterate t (72 * a - 17) ∧
      iterate s (48 * a - 17) ≠ iterate t (72 * a - 17) := by
  have hold := scalar_separation H a ha
    (Nat.dvd_trans (Nat.pow_dvd_pow 2 (show H + 12 ≤ H + 13 by omega)) h)
  have hnew := fourth_scalar_separation H a ha h
  intro s t hs ht
  exact ⟨(hold s t hs ht).1, (hold s t hs ht).2, hnew s t hs ht⟩

def FourSeparated (H R w r : Nat) : Prop :=
  ∀ s t, s ≤ H → t ≤ H →
    iterate (4 * R + 99 + 18 * r + s) (firstSource R w) ≠
      iterate (5 * R + 91 + 18 * r + t) (mainSource R w) ∧
    iterate (4 * R + 99 + 18 * r + s) (secondSource R w) ≠
      iterate (5 * R + 91 + 18 * r + t) (mainSource R w) ∧
    iterate (4 * R + 100 + 18 * r + s) (fourthSource R w) ≠
      iterate (5 * R + 91 + 18 * r + t) (mainSource R w)

theorem four_source_separation (H R w r u : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (h : 2 ^ (H + 13) ∣ 9 * scalar r u + 1) : FourSeparated H R w r := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hs := four_scalar_separation H (scalar r u) ha h
  have hn := three_sources R w r u hw hu hX
  have hp := fourth_profile R w r u hr hw hu hX
  intro s t hss htt
  simp only [iterate_add (4 * R + 99 + 18 * r) s,
    iterate_add (4 * R + 100 + 18 * r) s,
    iterate_add (5 * R + 91 + 18 * r) t, hn.1, hn.2.1, hn.2.2, hp]
  exact hs s t hss htt

theorem pure_four_separation (r H B : Nat) (hr : 5 ≤ r) :
    ∃ R u, B < R ∧ 14 ≤ R ∧ 0 < u ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧ FourSeparated H R 1 r := by
  obtain ⟨R, u, hB, hR, hu, hX, hs⟩ := pure_shadow_lift r (H + 1) B
  have hh : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 := by
    simpa only [show H + 1 + 12 = H + 13 by omega] using hs
  exact ⟨R, u, hB, hR, hu, hX, four_source_separation H R 1 r u hr (by decide) hu
    (by simpa only [Nat.mul_one] using hX) hh⟩

theorem weighted_four_separation (R r H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) :
    ∃ w u, B < w ∧ 0 < u ∧ 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      (0 < fourthSource R w ∧ fourthSource R w < mainSource R w) ∧
      FourSeparated H R w r := by
  obtain ⟨w, u, hwB, hu, hX, hs⟩ := weighted_shadow_lift R r (H + 1) B
  have hw : 0 < w := by omega
  have hh : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 := by
    simpa only [show H + 1 + 12 = H + 13 by omega] using hs
  exact ⟨w, u, hwB, hu, hX, fourth_bounds R w hR hw,
    four_source_separation H R w r u hr hw hu hX hh⟩

theorem no_uniform_four_scalar_clock (r : Nat) :
    ¬ ∃ H, ∀ u, 0 < u → ∃ s t, s ≤ H ∧ t ≤ H ∧
      (iterate s (81 * scalar r u - 17) = iterate t (72 * scalar r u - 17) ∨
       iterate s (64 * scalar r u - 17) = iterate t (72 * scalar r u - 17) ∨
       iterate s (48 * scalar r u - 17) = iterate t (72 * scalar r u - 17)) := by
  rintro ⟨H, hH⟩
  obtain ⟨_, u, _, _, hu, _, hs⟩ := pure_shadow_lift r (H + 1) 0
  have hh : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 := by
    simpa only [show H + 1 + 12 = H + 13 by omega] using hs
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  obtain ⟨s, t, hss, htt, hm⟩ := hH u hu
  have hn := four_scalar_separation H (scalar r u) ha hh s t hss htt
  rcases hm with hm | hm | hm
  · exact hn.1 hm
  · exact hn.2.1 hm
  · exact hn.2.2 hm

theorem secondary_scalar_separation (H b : Nat) (hb : 6 ≤ b)
    (h : 2 ^ (H + 6) ∣ b - 1) :
    ∀ s t, s ≤ H → t ≤ H →
      iterate s (3 * b - 17) ≠ iterate t (4 * b - 17) := by
  obtain ⟨K, u, hK, hu, hcoord⟩ :=
    exact_binary_from_divisibility (b - 1) (H + 6) (by omega) h
  have hn : 1 * (4 * b - 17) + 13 = 2 ^ (K + 2) * u := by
    have hl : 1 * (4 * b - 17) + 13 = 4 * (b - 1) := by omega
    rw [hl, hcoord, Nat.pow_add]
    change 4 * (2 ^ K * u) = (2 ^ K * 4) * u
    ac_rfl
  have hp : 1 * (3 * b - 17) + 14 = 2 ^ (K + 0) * (3 * u) := by
    have hl : 1 * (3 * b - 17) + 14 = 3 * (b - 1) := by omega
    rw [hl, hcoord, Nat.add_zero]
    ac_rfl
  exact phase_separation 1 3 6 exitMainPhases exitPartnerPhases (by decide)
    finite_phase_sets.2.2.2.1 finite_phase_sets.2.2.2.2.1 2 0 finite_phase_sets.2.2.2.2.2
    H K (4 * b - 17) (3 * b - 17) 13 14 u (3 * u) hK
    (by decide) (by decide) hu (by simp [Nat.mul_mod, hu]) hn hp

theorem secondary_source_separation (H R w r u j q : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (h : 2 ^ (H + 6) ∣ secondaryScalar j q - 1) :
    ∀ s t, s ≤ H → t ≤ H →
      iterate (4 * R + 121 + 18 * r + 18 * j + s) (fourthSource R w) ≠
        iterate (5 * R + 107 + 18 * r + 18 * j + t) (mainSource R w) := by
  have hb : 6 ≤ secondaryScalar j q := by
    have hp : 729 ≤ 3 ^ (6 + 7 * j) :=
      Nat.pow_le_pow_right (by decide : 0 < 3) (show 6 ≤ 6 + 7 * j by omega)
    have hm := Nat.mul_le_mul hp (show 1 ≤ q by omega)
    unfold secondaryScalar
    omega
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hn := (three_sources R w r u hw hu hX).1
  have hp := fourth_profile R w r u hr hw hu hX
  have hsecond := secondary_profiles (scalar r u) j q ha hq hT
  have hsep := secondary_scalar_separation H (secondaryScalar j q) hb h
  intro s t hss htt
  have hclockN : 5 * R + 107 + 18 * r + 18 * j + t =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + t) := by omega
  have hclockS : 4 * R + 121 + 18 * r + 18 * j + s =
      (4 * R + 100 + 18 * r) + ((21 + 18 * j) + s) := by omega
  rw [hclockN, hclockS, iterate_add (5 * R + 91 + 18 * r),
    iterate_add (4 * R + 100 + 18 * r), hn, hp,
    iterate_add (16 + 18 * j) t, iterate_add (21 + 18 * j) s,
    hsecond.1, hsecond.2]
  exact hsep s t hss htt

theorem odd_binary_inverse (k c : Nat) (hc : c % 2 = 1) :
    ∃ e q, 0 < e ∧ e < 2 ^ (k + 1) ∧ e % 2 = 1 ∧
      c * e = 1 + 2 ^ (k + 1) * q := by
  induction k with
  | zero =>
    exact ⟨1, c / 2, by decide, by decide, by decide, by omega⟩
  | succ k ih =>
    obtain ⟨e, q, he, hbound, hodd, heq⟩ := ih
    let D := 2 ^ (k + 1)
    have hD : 2 ^ (k + 1 + 1) = 2 * D := by
      change 2 ^ (k + 1 + 1) = 2 * 2 ^ (k + 1)
      rw [Nat.pow_succ 2 (k + 1)]
      omega
    have hDeven : D % 2 = 0 := by
      have hd : 2 ∣ D := Nat.pow_dvd_pow 2 (show 1 ≤ k + 1 by omega)
      exact Nat.mod_eq_zero_of_dvd hd
    by_cases hq : q % 2 = 0
    · refine ⟨e, q / 2, he, ?_, hodd, ?_⟩
      · rw [hD]
        change e < 2 * D
        change e < D at hbound
        omega
      · have hq2 : q = 2 * (q / 2) := by omega
        rw [heq, hD]
        change 1 + D * q = 1 + (2 * D) * (q / 2)
        calc
          _ = 1 + D * (2 * (q / 2)) := congrArg (fun z => 1 + D * z) hq2
          _ = _ := by congr 1; ac_rfl
    · have hqc : q + c = 2 * ((q + c) / 2) := by omega
      refine ⟨e + D, (q + c) / 2, by omega, ?_, ?_, ?_⟩
      · rw [hD]
        change e < D at hbound
        omega
      · omega
      · rw [Nat.mul_add, heq, hD]
        change 1 + D * q + c * D = 1 + (2 * D) * ((q + c) / 2)
        calc
          _ = 1 + D * (q + c) := by rw [Nat.mul_add, Nat.mul_comm c D]; omega
          _ = 1 + D * (2 * ((q + c) / 2)) := congrArg (fun z => 1 + D * z) hqc
          _ = _ := by congr 1; ac_rfl

theorem pure_delayed_merger (r H B : Nat) (hr : 5 ≤ r) :
    ∃ R u q, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * (H + 1)) * q ∧
      secondaryScalar (H + 1) q % 64 = 23 ∧
      ¬ LeastCounterexample (mainSource R 1) ∧ FourSeparated H R 1 r ∧
      iterate (4 * R + 128 + 18 * r + 18 * (H + 1)) (fourthSource R 1) =
        iterate (5 * R + 117 + 18 * r + 18 * (H + 1)) (mainSource R 1) := by
  obtain ⟨R, u, q, hB, hR, hu, hq, hX, hT, hb⟩ := pure_nested_lift r (H + 1) B
  have hx : 9 ^ R * 1 + 7 = 2 ^ (57 + 11 * r) * u := by simpa only [Nat.mul_one] using hX
  have hd : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 := by
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show H + 13 ≤ 9 + 11 * (H + 1) by omega)) ⟨q, hT⟩
  exact ⟨R, u, q, hB, hR, hu, hq, hX, hT, hb,
    nested_not_least R 1 r u (H + 1) q hR hr (by decide) hu hq hx hT hb,
    four_source_separation H R 1 r u hr (by decide) hu hx hd,
    nested_meeting R 1 r u (H + 1) q hr (by decide) hu hq hx hT hb⟩

theorem weighted_delayed_merger (R r H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) :
    ∃ w u q, B < w ∧ 0 < u ∧ 0 < q ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * (H + 1)) * q ∧
      secondaryScalar (H + 1) q % 64 = 23 ∧
      ¬ LeastCounterexample (mainSource R w) ∧ FourSeparated H R w r ∧
      iterate (4 * R + 128 + 18 * r + 18 * (H + 1)) (fourthSource R w) =
        iterate (5 * R + 117 + 18 * r + 18 * (H + 1)) (mainSource R w) := by
  obtain ⟨w, u, q, hwB, hu, hq, hX, hT, hb⟩ := weighted_nested_lift R r (H + 1) B
  have hw : 0 < w := by omega
  have hd : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 := by
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show H + 13 ≤ 9 + 11 * (H + 1) by omega)) ⟨q, hT⟩
  exact ⟨w, u, q, hwB, hu, hq, hX, hT, hb,
    nested_not_least R w r u (H + 1) q hR hr hw hu hq hX hT hb,
    four_source_separation H R w r u hr hw hu hX hd,
    nested_meeting R w r u (H + 1) q hr hw hu hq hX hT hb⟩

theorem pure_secondary_unit_lift (r j H B : Nat) :
    ∃ R u q, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ q % 2 = 1 ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      2 ^ (H + 6) ∣ secondaryScalar j q - 1 := by
  let m := 57 + 11 * r
  let K := 9 + 11 * j
  let D := 2 ^ m
  let E := 2 ^ K
  let M := 2 ^ (H + 6)
  let A := 3 ^ (35 + 7 * r)
  let c := 3 ^ (6 + 7 * j)
  have hcodd : c % 2 = 1 := by dsimp [c]; rw [Nat.pow_mod]; simp
  obtain ⟨eps, z, hepos, helt, heodd, heunit⟩ := odd_binary_inverse (H + 5) c hcodd
  rw [show H + 5 + 1 = H + 6 by omega] at helt heunit
  change eps < M at helt
  change c * eps = 1 + M * z at heunit
  have hA : A % 2 = 1 := by dsimp [A]; rw [Nat.pow_mod]; simp
  have hD : D = 8 * 2 ^ (54 + 11 * r) := by
    dsimp [D, m]
    rw [show 57 + 11 * r = (54 + 11 * r) + 3 by omega, Nat.pow_add]
    omega
  let F := 7 * A + D + (M - eps) * D * E
  have hbase : (A + F) % 8 = 0 := by
    have he : A + F = 8 * (A + 2 ^ (54 + 11 * r) +
        (M - eps) * 2 ^ (54 + 11 * r) * E) := by
      unfold F
      rw [hD]
      grind
    rw [he]
    omega
  obtain ⟨R, Q, hB, hR, hQ⟩ := unbounded_affine_lift (m + K + H + 3) A F B hA hbase
  have hpow : 2 ^ (m + K + H + 3 + 3) = M * (D * E) := by
    rw [show m + K + H + 3 + 3 = (m + K) + (H + 6) by omega,
      Nat.pow_add, Nat.pow_add]
    change (D * E) * M = M * (D * E)
    ac_rfl
  rw [hpow] at hQ
  have hpositive : 0 < A * 9 ^ R + F := by
    have hp : 0 < D := Nat.two_pow_pos m
    unfold F
    omega
  have hQpos : 0 < Q := Nat.pos_of_mul_pos_left (hQ ▸ hpositive)
  let q := M * (Q - 1) + eps
  have hqpos : 0 < q := by dsimp [q]; omega
  have hMeven : M % 2 = 0 := by
    have hd : 2 ∣ M := Nat.pow_dvd_pow 2 (show 1 ≤ H + 6 by omega)
    exact Nat.mod_eq_zero_of_dvd hd
  have hqodd : q % 2 = 1 := by dsimp [q]; simp [Nat.add_mod, Nat.mul_mod, hMeven, heodd]
  have hMQ : M * Q = M * (Q - 1) + M := by
    calc
      _ = M * ((Q - 1) + 1) := congrArg (fun x => M * x) (by omega)
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have hqsum : q + (M - eps) = M * Q := by dsimp [q]; omega
  have hpad : D * E * q + (M - eps) * D * E = M * (D * E) * Q := by
    calc
      _ = (D * E) * (q + (M - eps)) := by
        rw [Nat.mul_add (D * E) q (M - eps)]
        ac_rfl
      _ = (D * E) * (M * Q) := congrArg (fun z => (D * E) * z) hqsum
      _ = _ := by ac_rfl
  have hstart : A * (9 ^ R + 7) + D + (M - eps) * D * E = M * (D * E) * Q := by
    rw [Nat.mul_add, show A * 7 = 7 * A by omega]
    simpa only [F, Nat.add_assoc] using hQ
  have hsum : A * (9 ^ R + 7) + D = D * (E * q) := by
    have hh := Nat.add_right_cancel (hstart.trans hpad.symm)
    simpa only [Nat.mul_assoc] using hh
  have hdiv : D ∣ A * (9 ^ R + 7) := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_refl D)).mpr
    exact ⟨E * q, hsum⟩
  obtain ⟨u, hu⟩ := odd_power_cancel m A (9 ^ R + 7) hA hdiv
  have hupositive : 0 < 9 ^ R + 7 := Nat.succ_pos (9 ^ R + 6)
  have hup : 0 < u := Nat.pos_of_mul_pos_left (hu ▸ hupositive)
  have hprod : D * (A * u + 1) = D * (E * q) := by
    have he : D * (A * u + 1) = A * (D * u) + D := by
      rw [Nat.mul_add, Nat.mul_one]
      congr 1
      ac_rfl
    rw [he, ← hu]
    exact hsum
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) hprod
  have hscalar : A * u = 9 * scalar r u := by
    unfold A scalar
    rw [show 35 + 7 * r = (33 + 7 * r) + 2 by omega, Nat.pow_add]
    ac_rfl
  rw [hscalar] at hcancel
  have hguard : M ∣ secondaryScalar j q - 1 := by
    have he : c * q = 1 + M * (c * (Q - 1) + z) := by
      dsimp [q]
      rw [Nat.mul_add, heunit, Nat.mul_add]
      have hr : c * (M * (Q - 1)) = M * (c * (Q - 1)) := by ac_rfl
      rw [hr]
      omega
    refine ⟨c * (Q - 1) + z, ?_⟩
    change c * q - 1 = M * (c * (Q - 1) + z)
    rw [he]
    omega
  exact ⟨R, u, q, hB, hR, hup, hqpos, hqodd, hu, hcancel, hguard⟩

theorem pure_secondary_separation (r j H B : Nat) (hr : 5 ≤ r) :
    ∃ R u q, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ q % 2 = 1 ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      2 ^ (H + 6) ∣ secondaryScalar j q - 1 ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 121 + 18 * r + 18 * j + s) (fourthSource R 1) ≠
          iterate (5 * R + 107 + 18 * r + 18 * j + t) (mainSource R 1) := by
  obtain ⟨R, u, q, hB, hR, hu, hq, hqo, hX, hT, hunit⟩ := pure_secondary_unit_lift r j H B
  exact ⟨R, u, q, hB, hR, hu, hq, hqo, hX, hT, hunit,
    secondary_source_separation H R 1 r u j q hr (by decide) hu hq
      (by simpa only [Nat.mul_one] using hX) hT hunit⟩

theorem weighted_secondary_separation (R r j H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) :
    ∃ w u q, B < w ∧ 0 < u ∧ 0 < q ∧ q % 2 = 1 ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      2 ^ (H + 6) ∣ secondaryScalar j q - 1 ∧
      (0 < fourthSource R w ∧ fourthSource R w < mainSource R w) ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 121 + 18 * r + 18 * j + s) (fourthSource R w) ≠
          iterate (5 * R + 107 + 18 * r + 18 * j + t) (mainSource R w) := by
  obtain ⟨T, u, q, hB, _, hu, hq, hqo, hX, hT, hunit⟩ :=
    pure_secondary_unit_lift r j H (R + B + 1)
  let w := 9 ^ (T - R)
  have hwB : B < w := Nat.lt_trans (show B < T - R by omega)
    (Nat.lt_pow_self (by decide : 1 < 9))
  have hw : 0 < w := by omega
  have hx : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u := by
    dsimp [w]
    rw [← Nat.pow_add, show R + (T - R) = T by omega]
    exact hX
  exact ⟨w, u, q, hwB, hu, hq, hqo, hx, hT, hunit, fourth_bounds R w hR hw,
    secondary_source_separation H R w r u j q hr hw hu hq hx hT hunit⟩

theorem no_uniform_secondary_exit_clock (j : Nat) :
    ¬ ∃ H, ∀ q, 0 < q → q % 2 = 1 →
      ∃ s t, s ≤ H ∧ t ≤ H ∧
        iterate s (3 * secondaryScalar j q - 17) =
          iterate t (4 * secondaryScalar j q - 17) := by
  rintro ⟨H, hH⟩
  obtain ⟨_, _, q, _, _, _, hq, hqo, _, _, hunit⟩ := pure_secondary_unit_lift 5 j H 0
  have hb : 6 ≤ secondaryScalar j q := by
    have hp : 729 ≤ 3 ^ (6 + 7 * j) :=
      Nat.pow_le_pow_right (by decide : 0 < 3) (show 6 ≤ 6 + 7 * j by omega)
    have hm := Nat.mul_le_mul hp (show 1 ≤ q by omega)
    unfold secondaryScalar
    omega
  obtain ⟨s, t, hs, ht, hm⟩ := hH q hq hqo
  exact secondary_scalar_separation H (secondaryScalar j q) hb hunit s t hs ht hm

def phaseWitnessWeight : Nat := 16768443090418316695505142264862585407984927798814999280451083865077921806854985
def phaseWitnessUnit : Nat := 73880250460211930691604536083959457230601810907118436165527
def phaseWitnessExit : Nat := 176366572999724355306485026645287596444635785045530339819442798453538989821683684113499

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
theorem finite_secondary_convergent_witness :
    0 < phaseWitnessWeight ∧ 0 < phaseWitnessUnit ∧ 0 < phaseWitnessExit ∧
    phaseWitnessExit % 2 = 1 ∧
    9 ^ 14 * phaseWitnessWeight + 7 = 2 ^ 112 * phaseWitnessUnit ∧
    9 * scalar 5 phaseWitnessUnit + 1 = 2 ^ 20 * phaseWitnessExit ∧
    2 ^ 134 ∣ secondaryScalar 1 phaseWitnessExit - 1 ∧
    iterate 2683 (mainSource 14 phaseWitnessWeight) = 1 ∧
    iterate 3675 (firstSource 14 phaseWitnessWeight) = 1 ∧
    iterate 2682 (secondSource 14 phaseWitnessWeight) = 1 ∧
    iterate 2680 (fourthSource 14 phaseWitnessWeight) = 1 := by
  decide +kernel

#print axioms finite_secondary_convergent_witness
#print axioms binary_exponent_unique
#print axioms exact_phase_step
#print axioms phase_track
#print axioms phase_separation
#print axioms finite_phase_sets
#print axioms exact_binary_from_divisibility
#print axioms fourth_scalar_separation
#print axioms four_scalar_separation
#print axioms four_source_separation
#print axioms pure_four_separation
#print axioms weighted_four_separation
#print axioms no_uniform_four_scalar_clock
#print axioms secondary_scalar_separation
#print axioms secondary_source_separation
#print axioms odd_binary_inverse
#print axioms pure_delayed_merger
#print axioms weighted_delayed_merger
#print axioms pure_secondary_unit_lift
#print axioms pure_secondary_separation
#print axioms weighted_secondary_separation
#print axioms no_uniform_secondary_exit_clock

end MinimumSeventeenPhase
