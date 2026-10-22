/- Two scalar partners cover every endpoint that is two modulo three.
   Weighted lifts give new doubled and quadrupled least-source exclusions. -/
import MinimumDoubleLadder

namespace MinimumPhaseCover
open OrdinaryCollatz MinimumLadderCover MinimumLadderComplement
open MinimumRootPredecessors

def plusSource (R w : Nat) : Nat := 2 ^ (2 * R + 1) * w - 1
def thirdSource (R w : Nat) : Nat := source (R - 1) (3 * w)
def halfSource (R w : Nat) : Nat := source R (2 * w)
def halfPreceding (R w : Nat) : Nat := source (R - 1) (2 * w)

theorem third_partner_even (a b : Nat) (hb : b = 3 * a + 2) (he : b % 4 = 0) :
    iterate 3 a = iterate 2 b := by
  have ha : a % 4 = 2 := by omega
  let v := a / 4
  have hv : a = 4 * v + 2 := by dsimp [v]; omega
  have hb' : b = 12 * v + 8 := by omega
  have f0 : C (4 * v + 2) = 2 * v + 1 := by unfold C; split <;> omega
  have f1 : C (2 * v + 1) = 6 * v + 4 := by unfold C; split <;> omega
  have f2 : C (6 * v + 4) = 3 * v + 2 := by unfold C; split <;> omega
  have g0 : C (12 * v + 8) = 6 * v + 4 := by unfold C; split <;> omega
  rw [hv, hb']
  simp only [iterate, f0, f1, f2, g0]

theorem two_partner_cover (a b : Nat) (hb : b = 3 * a + 2) :
    Merges (2 * b + 1) b ∨ Merges a b := by
  by_cases ho : b % 2 = 1
  · rcases odd_two_partner_cover b ho with hm | hm
    · exact Or.inl hm
    · have ha : a % 2 = 1 := by omega
      have hc : iterate 1 a = b - 1 := by
        change C a = _
        unfold C
        rw [ha]
        simp only [ite_true]
        omega
      exact Or.inr (merger_transport a b (b - 1) b 1 0 hc rfl hm)
  · have he : b % 4 = 0 ∨ b % 4 = 2 := by omega
    rcases he with he | he
    · exact Or.inr ⟨3, 2, third_partner_even a b hb he⟩
    · exact Or.inl ⟨3, 2, double_partner_even b he⟩

theorem two_source_escape (N P Q a b s t v : Nat)
    (hP : 0 < P ∧ P < N) (hQ : 0 < Q ∧ Q < N) (hb : b = 3 * a + 2)
    (hn : iterate s N = b) (hp : iterate t P = 2 * b + 1)
    (hq : iterate v Q = a) :
    ∃ S, 0 < S ∧ S < N ∧ (S = P ∨ S = Q) ∧ Merges S N := by
  rcases two_partner_cover a b hb with hm | hm
  · exact ⟨P, hP.1, hP.2, Or.inl rfl, merger_transport _ _ _ _ _ _ hp hn hm⟩
  · exact ⟨Q, hQ.1, hQ.2, Or.inr rfl, merger_transport _ _ _ _ _ _ hq hn hm⟩

theorem two_source_not_least (N P Q a b s t v : Nat)
    (hP : 0 < P ∧ P < N) (hQ : 0 < Q ∧ Q < N) (hb : b = 3 * a + 2)
    (hn : iterate s N = b) (hp : iterate t P = 2 * b + 1)
    (hq : iterate v Q = a) : ¬ LeastCounterexample N := by
  intro hleast
  obtain ⟨S, hS, hsmall, _, i, j, hm⟩ := two_source_escape N P Q a b s t v hP hQ hb hn hp hq
  have hl := least_coalescing_predecessor hleast hS hm
  omega

theorem double_source_bounds (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w) :
    (0 < plusSource R w ∧ plusSource R w < source R (2 * w)) ∧
      (0 < thirdSource R w ∧ thirdSource R w < source R (2 * w)) ∧
      3 * (source R (2 * w) + 5) = 16 * (thirdSource R w + 5) := by
  have h8 : 8 ≤ 8 ^ (R - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R - 1 by omega)
  have hpos := Nat.mul_le_mul h8 (show 1 ≤ w by omega)
  have h8R : 8 ^ R = 8 * 8 ^ (R - 1) := by
    calc
      _ = 8 ^ ((R - 1) + 1) := congrArg (fun j => 8 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  have hscale : 8 ^ R = 2 ^ (3 * R) := by rw [Nat.pow_mul]
  have hm : 2 ^ (2 * R + 1) ≤ 8 ^ R := by
    rw [hscale]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hmpos : 8 ≤ 2 ^ (2 * R + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ 2 * R + 1 by omega)
  have hmw := Nat.mul_le_mul_right w hm
  have hmp := Nat.mul_le_mul hmpos (show 1 ≤ w by omega)
  have hn : 8 ^ R * (2 * w) = 16 * (8 ^ (R - 1) * w) := by rw [h8R]; grind
  have hq : 8 ^ (R - 1) * (3 * w) = 3 * (8 ^ (R - 1) * w) := by ac_rfl
  have hh : 8 ^ R * w = 8 * (8 ^ (R - 1) * w) := by rw [h8R]; ac_rfl
  rw [hh] at hmw
  unfold plusSource thirdSource source
  rw [hn, hq]
  omega

theorem quad_source_bounds (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w) :
    (0 < halfSource R w ∧ halfSource R w < source R (4 * w)) ∧
      (0 < halfPreceding R w ∧ halfPreceding R w < source R (4 * w)) ∧
      source R (4 * w) + 5 = 2 * (halfSource R w + 5) ∧
      source R (4 * w) + 5 = 16 * (halfPreceding R w + 5) := by
  have h8 : 8 ≤ 8 ^ (R - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R - 1 by omega)
  have hpos := Nat.mul_le_mul h8 (show 1 ≤ w by omega)
  have h8R : 8 ^ R = 8 * 8 ^ (R - 1) := by
    calc
      _ = 8 ^ ((R - 1) + 1) := congrArg (fun j => 8 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  have hn : 8 ^ R * (4 * w) = 32 * (8 ^ (R - 1) * w) := by rw [h8R]; grind
  have hp : 8 ^ R * (2 * w) = 16 * (8 ^ (R - 1) * w) := by rw [h8R]; grind
  have hq : 8 ^ (R - 1) * (2 * w) = 2 * (8 ^ (R - 1) * w) := by ac_rfl
  unfold halfSource halfPreceding source
  rw [hn, hp, hq]
  omega

theorem double_coordinates (R w : Nat) (hR : 0 < R)
    (hr : (9 ^ R * w) % 256 = 17) :
    ∃ u, 9 ^ R * w = 768 * u + 273 ∧
      9 ^ (R - 1) * (3 * w) = 256 * u + 91 := by
  have h3 : 9 ^ R * w = 3 * (9 ^ (R - 1) * (3 * w)) := by
    calc
      _ = 9 ^ ((R - 1) + 1) * w := congrArg (fun j => 9 ^ j * w) (by omega)
      _ = _ := by rw [Nat.pow_succ]; grind
  have hmod : (9 ^ (R - 1) * (3 * w)) % 256 = 91 := by
    calc
      _ = (513 * (9 ^ (R - 1) * (3 * w))) % 256 := by simp [Nat.mul_mod]
      _ = (171 * (9 ^ R * w)) % 256 := by rw [h3]; congr 1; omega
      _ = 91 := by rw [Nat.mul_mod, hr]
  let u := (9 ^ (R - 1) * (3 * w)) / 256
  have hu : 9 ^ (R - 1) * (3 * w) = 256 * u + 91 := by dsimp [u]; omega
  exact ⟨u, by omega, hu⟩

theorem quad_coordinates (R w : Nat) (hR : 0 < R)
    (hr : (9 ^ R * w) % 512 = 473) :
    ∃ u, 9 ^ R * w = 4608 * u + 3033 ∧
      9 ^ (R - 1) * w = 512 * u + 337 := by
  have h9 : 9 ^ R * w = 9 * (9 ^ (R - 1) * w) := by
    calc
      _ = 9 ^ ((R - 1) + 1) * w := congrArg (fun j => 9 ^ j * w) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have hmod : (9 ^ (R - 1) * w) % 512 = 337 := by
    calc
      _ = (513 * (9 ^ (R - 1) * w)) % 512 := by simp [Nat.mul_mod]
      _ = (57 * (9 ^ R * w)) % 512 := by rw [h9]; congr 1; omega
      _ = 337 := by rw [Nat.mul_mod, hr]
  let u := (9 ^ (R - 1) * w) / 512
  have hu : 9 ^ (R - 1) * w = 512 * u + 337 := by dsimp [u]; omega
  exact ⟨u, by omega, hu⟩

theorem double_profiles (u : Nat) :
    iterate 13 (1536 * u + 541) = 243 * u + 86 ∧
      iterate 10 (2304 * u + 818) = 486 * u + 173 ∧
      iterate 12 (256 * u + 86) = 81 * u + 28 := by
  have f0_0 : C (1536 * u + 541) = 4608 * u + 1624 := by unfold C; split <;> omega
  have f0_1 : C (4608 * u + 1624) = 2304 * u + 812 := by unfold C; split <;> omega
  have f0_2 : C (2304 * u + 812) = 1152 * u + 406 := by unfold C; split <;> omega
  have f0_3 : C (1152 * u + 406) = 576 * u + 203 := by unfold C; split <;> omega
  have f0_4 : C (576 * u + 203) = 1728 * u + 610 := by unfold C; split <;> omega
  have f0_5 : C (1728 * u + 610) = 864 * u + 305 := by unfold C; split <;> omega
  have f0_6 : C (864 * u + 305) = 2592 * u + 916 := by unfold C; split <;> omega
  have f0_7 : C (2592 * u + 916) = 1296 * u + 458 := by unfold C; split <;> omega
  have f0_8 : C (1296 * u + 458) = 648 * u + 229 := by unfold C; split <;> omega
  have f0_9 : C (648 * u + 229) = 1944 * u + 688 := by unfold C; split <;> omega
  have f0_10 : C (1944 * u + 688) = 972 * u + 344 := by unfold C; split <;> omega
  have f0_11 : C (972 * u + 344) = 486 * u + 172 := by unfold C; split <;> omega
  have f0_12 : C (486 * u + 172) = 243 * u + 86 := by unfold C; split <;> omega
  have f1_0 : C (2304 * u + 818) = 1152 * u + 409 := by unfold C; split <;> omega
  have f1_1 : C (1152 * u + 409) = 3456 * u + 1228 := by unfold C; split <;> omega
  have f1_2 : C (3456 * u + 1228) = 1728 * u + 614 := by unfold C; split <;> omega
  have f1_3 : C (1728 * u + 614) = 864 * u + 307 := by unfold C; split <;> omega
  have f1_4 : C (864 * u + 307) = 2592 * u + 922 := by unfold C; split <;> omega
  have f1_5 : C (2592 * u + 922) = 1296 * u + 461 := by unfold C; split <;> omega
  have f1_6 : C (1296 * u + 461) = 3888 * u + 1384 := by unfold C; split <;> omega
  have f1_7 : C (3888 * u + 1384) = 1944 * u + 692 := by unfold C; split <;> omega
  have f1_8 : C (1944 * u + 692) = 972 * u + 346 := by unfold C; split <;> omega
  have f1_9 : C (972 * u + 346) = 486 * u + 173 := by unfold C; split <;> omega
  have f2_0 : C (256 * u + 86) = 128 * u + 43 := by unfold C; split <;> omega
  have f2_1 : C (128 * u + 43) = 384 * u + 130 := by unfold C; split <;> omega
  have f2_2 : C (384 * u + 130) = 192 * u + 65 := by unfold C; split <;> omega
  have f2_3 : C (192 * u + 65) = 576 * u + 196 := by unfold C; split <;> omega
  have f2_4 : C (576 * u + 196) = 288 * u + 98 := by unfold C; split <;> omega
  have f2_5 : C (288 * u + 98) = 144 * u + 49 := by unfold C; split <;> omega
  have f2_6 : C (144 * u + 49) = 432 * u + 148 := by unfold C; split <;> omega
  have f2_7 : C (432 * u + 148) = 216 * u + 74 := by unfold C; split <;> omega
  have f2_8 : C (216 * u + 74) = 108 * u + 37 := by unfold C; split <;> omega
  have f2_9 : C (108 * u + 37) = 324 * u + 112 := by unfold C; split <;> omega
  have f2_10 : C (324 * u + 112) = 162 * u + 56 := by unfold C; split <;> omega
  have f2_11 : C (162 * u + 56) = 81 * u + 28 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f0_7, f0_8, f0_9, f0_10, f0_11, f0_12],
    by simp only [iterate, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f1_7, f1_8, f1_9],
    by simp only [iterate, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7, f2_8, f2_9, f2_10, f2_11]⟩

theorem quad_profiles (u : Nat) :
    iterate 16 (18432 * u + 12127) = 2187 * u + 1439 ∧
      iterate 14 (9216 * u + 6061) = 4374 * u + 2879 ∧
      iterate 16 (1024 * u + 669) = 729 * u + 479 := by
  have f0_0 : C (18432 * u + 12127) = 55296 * u + 36382 := by unfold C; split <;> omega
  have f0_1 : C (55296 * u + 36382) = 27648 * u + 18191 := by unfold C; split <;> omega
  have f0_2 : C (27648 * u + 18191) = 82944 * u + 54574 := by unfold C; split <;> omega
  have f0_3 : C (82944 * u + 54574) = 41472 * u + 27287 := by unfold C; split <;> omega
  have f0_4 : C (41472 * u + 27287) = 124416 * u + 81862 := by unfold C; split <;> omega
  have f0_5 : C (124416 * u + 81862) = 62208 * u + 40931 := by unfold C; split <;> omega
  have f0_6 : C (62208 * u + 40931) = 186624 * u + 122794 := by unfold C; split <;> omega
  have f0_7 : C (186624 * u + 122794) = 93312 * u + 61397 := by unfold C; split <;> omega
  have f0_8 : C (93312 * u + 61397) = 279936 * u + 184192 := by unfold C; split <;> omega
  have f0_9 : C (279936 * u + 184192) = 139968 * u + 92096 := by unfold C; split <;> omega
  have f0_10 : C (139968 * u + 92096) = 69984 * u + 46048 := by unfold C; split <;> omega
  have f0_11 : C (69984 * u + 46048) = 34992 * u + 23024 := by unfold C; split <;> omega
  have f0_12 : C (34992 * u + 23024) = 17496 * u + 11512 := by unfold C; split <;> omega
  have f0_13 : C (17496 * u + 11512) = 8748 * u + 5756 := by unfold C; split <;> omega
  have f0_14 : C (8748 * u + 5756) = 4374 * u + 2878 := by unfold C; split <;> omega
  have f0_15 : C (4374 * u + 2878) = 2187 * u + 1439 := by unfold C; split <;> omega
  have f1_0 : C (9216 * u + 6061) = 27648 * u + 18184 := by unfold C; split <;> omega
  have f1_1 : C (27648 * u + 18184) = 13824 * u + 9092 := by unfold C; split <;> omega
  have f1_2 : C (13824 * u + 9092) = 6912 * u + 4546 := by unfold C; split <;> omega
  have f1_3 : C (6912 * u + 4546) = 3456 * u + 2273 := by unfold C; split <;> omega
  have f1_4 : C (3456 * u + 2273) = 10368 * u + 6820 := by unfold C; split <;> omega
  have f1_5 : C (10368 * u + 6820) = 5184 * u + 3410 := by unfold C; split <;> omega
  have f1_6 : C (5184 * u + 3410) = 2592 * u + 1705 := by unfold C; split <;> omega
  have f1_7 : C (2592 * u + 1705) = 7776 * u + 5116 := by unfold C; split <;> omega
  have f1_8 : C (7776 * u + 5116) = 3888 * u + 2558 := by unfold C; split <;> omega
  have f1_9 : C (3888 * u + 2558) = 1944 * u + 1279 := by unfold C; split <;> omega
  have f1_10 : C (1944 * u + 1279) = 5832 * u + 3838 := by unfold C; split <;> omega
  have f1_11 : C (5832 * u + 3838) = 2916 * u + 1919 := by unfold C; split <;> omega
  have f1_12 : C (2916 * u + 1919) = 8748 * u + 5758 := by unfold C; split <;> omega
  have f1_13 : C (8748 * u + 5758) = 4374 * u + 2879 := by unfold C; split <;> omega
  have f2_0 : C (1024 * u + 669) = 3072 * u + 2008 := by unfold C; split <;> omega
  have f2_1 : C (3072 * u + 2008) = 1536 * u + 1004 := by unfold C; split <;> omega
  have f2_2 : C (1536 * u + 1004) = 768 * u + 502 := by unfold C; split <;> omega
  have f2_3 : C (768 * u + 502) = 384 * u + 251 := by unfold C; split <;> omega
  have f2_4 : C (384 * u + 251) = 1152 * u + 754 := by unfold C; split <;> omega
  have f2_5 : C (1152 * u + 754) = 576 * u + 377 := by unfold C; split <;> omega
  have f2_6 : C (576 * u + 377) = 1728 * u + 1132 := by unfold C; split <;> omega
  have f2_7 : C (1728 * u + 1132) = 864 * u + 566 := by unfold C; split <;> omega
  have f2_8 : C (864 * u + 566) = 432 * u + 283 := by unfold C; split <;> omega
  have f2_9 : C (432 * u + 283) = 1296 * u + 850 := by unfold C; split <;> omega
  have f2_10 : C (1296 * u + 850) = 648 * u + 425 := by unfold C; split <;> omega
  have f2_11 : C (648 * u + 425) = 1944 * u + 1276 := by unfold C; split <;> omega
  have f2_12 : C (1944 * u + 1276) = 972 * u + 638 := by unfold C; split <;> omega
  have f2_13 : C (972 * u + 638) = 486 * u + 319 := by unfold C; split <;> omega
  have f2_14 : C (486 * u + 319) = 1458 * u + 958 := by unfold C; split <;> omega
  have f2_15 : C (1458 * u + 958) = 729 * u + 479 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f0_7, f0_8, f0_9, f0_10, f0_11, f0_12, f0_13, f0_14, f0_15],
    by simp only [iterate, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6, f1_7, f1_8, f1_9, f1_10, f1_11, f1_12, f1_13],
    by simp only [iterate, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7, f2_8, f2_9, f2_10, f2_11, f2_12, f2_13, f2_14, f2_15]⟩

theorem double_three_paths (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 256 = 17) :
    ∃ a b, b = 3 * a + 2 ∧
      iterate (5 * R + 13) (source R (2 * w)) = b ∧
      iterate (4 * R + 12) (plusSource R w) = 2 * b + 1 ∧
      iterate (5 * R + 7) (thirdSource R w) = a := by
  obtain ⟨u, hX, hY⟩ := double_coordinates R w (by omega) hr
  have hn : iterate (5 * R + 13) (source R (2 * w)) = 243 * u + 86 := by
    rw [iterate_add, weighted_clock R (2 * w) (by omega)]
    have he : 9 ^ R * (2 * w) - 5 = 1536 * u + 541 := by
      have hh : 9 ^ R * (2 * w) = 2 * (9 ^ R * w) := by ac_rfl
      rw [hh, hX]
      omega
    rw [he, (double_profiles u).1]
  have hc : iterate (4 * R + 2) (plusSource R w) = 3 * (9 ^ R * w) - 1 := by
    have hh := MinimumReturnLadder.backtrack_actual
      (MinimumInverseEscape.pure_inverse (2 * R + 1) w hw)
    have h3 : 3 ^ (2 * R + 1) * w = 3 * (9 ^ R * w) := by
      rw [Nat.pow_succ, Nat.pow_mul]
      ac_rfl
    simpa only [plusSource, Nat.zero_add,
      show 2 * (2 * R + 1) = 4 * R + 2 by omega, h3] using hh
  have hp : iterate (4 * R + 12) (plusSource R w) = 486 * u + 173 := by
    rw [show 4 * R + 12 = (4 * R + 2) + 10 by omega, iterate_add, hc, hX]
    have he : 3 * (768 * u + 273) - 1 = 2304 * u + 818 := by omega
    rw [he, (double_profiles u).2.1]
  have hq : iterate (5 * R + 7) (thirdSource R w) = 81 * u + 28 := by
    rw [show 5 * R + 7 = 5 * (R - 1) + 12 by omega, iterate_add]
    change iterate 12 (iterate (5 * (R - 1)) (source (R - 1) (3 * w))) = _
    rw [weighted_clock (R - 1) (3 * w) (by omega), hY]
    have he : 256 * u + 91 - 5 = 256 * u + 86 := by omega
    rw [he, (double_profiles u).2.2]
  exact ⟨81 * u + 28, 243 * u + 86, by omega, hn, by rw [hp]; omega, hq⟩

theorem quad_three_paths (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 512 = 473) :
    ∃ a b, b = 3 * a + 2 ∧
      iterate (5 * R + 16) (source R (4 * w)) = b ∧
      iterate (5 * R + 14) (halfSource R w) = 2 * b + 1 ∧
      iterate (5 * R + 11) (halfPreceding R w) = a := by
  obtain ⟨u, hX, hY⟩ := quad_coordinates R w (by omega) hr
  have hn : iterate (5 * R + 16) (source R (4 * w)) = 2187 * u + 1439 := by
    rw [iterate_add, weighted_clock R (4 * w) (by omega)]
    have he : 9 ^ R * (4 * w) - 5 = 18432 * u + 12127 := by
      have hh : 9 ^ R * (4 * w) = 4 * (9 ^ R * w) := by ac_rfl
      rw [hh, hX]
      omega
    rw [he, (quad_profiles u).1]
  have hp : iterate (5 * R + 14) (halfSource R w) = 4374 * u + 2879 := by
    rw [iterate_add]
    change iterate 14 (iterate (5 * R) (source R (2 * w))) = _
    rw [weighted_clock R (2 * w) (by omega)]
    have he : 9 ^ R * (2 * w) - 5 = 9216 * u + 6061 := by
      have hh : 9 ^ R * (2 * w) = 2 * (9 ^ R * w) := by ac_rfl
      rw [hh, hX]
      omega
    rw [he, (quad_profiles u).2.1]
  have hq : iterate (5 * R + 11) (halfPreceding R w) = 729 * u + 479 := by
    rw [show 5 * R + 11 = 5 * (R - 1) + 16 by omega, iterate_add]
    change iterate 16 (iterate (5 * (R - 1)) (source (R - 1) (2 * w))) = _
    rw [weighted_clock (R - 1) (2 * w) (by omega)]
    have he : 9 ^ (R - 1) * (2 * w) - 5 = 1024 * u + 669 := by
      have hh : 9 ^ (R - 1) * (2 * w) = 2 * (9 ^ (R - 1) * w) := by ac_rfl
      rw [hh, hY]
      omega
    rw [he, (quad_profiles u).2.2]
  exact ⟨729 * u + 479, 2187 * u + 1439, by omega, hn, by rw [hp]; omega, hq⟩

theorem double_residual_escape (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 256 = 17) :
    ∃ P, 0 < P ∧ P < source R (2 * w) ∧
      (P = plusSource R w ∨ P = thirdSource R w) ∧ Merges P (source R (2 * w)) := by
  obtain ⟨a, b, hb, hn, hp, hq⟩ := double_three_paths R w hR hw hr
  have hs := double_source_bounds R w hR hw
  exact two_source_escape _ _ _ a b _ _ _ hs.1 hs.2.1 hb hn hp hq

theorem quad_residual_escape (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 512 = 473) :
    ∃ P, 0 < P ∧ P < source R (4 * w) ∧
      (P = halfSource R w ∨ P = halfPreceding R w) ∧ Merges P (source R (4 * w)) := by
  obtain ⟨a, b, hb, hn, hp, hq⟩ := quad_three_paths R w hR hw hr
  have hs := quad_source_bounds R w hR hw
  exact two_source_escape _ _ _ a b _ _ _ hs.1 hs.2.1 hb hn hp hq

theorem double_residual_not_least (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 256 = 17) : ¬ LeastCounterexample (source R (2 * w)) := by
  obtain ⟨a, b, hb, hn, hp, hq⟩ := double_three_paths R w hR hw hr
  have hs := double_source_bounds R w hR hw
  exact two_source_not_least _ _ _ a b _ _ _ hs.1 hs.2.1 hb hn hp hq

theorem quad_residual_not_least (R w : Nat) (hR : 2 ≤ R) (hw : 0 < w)
    (hr : (9 ^ R * w) % 512 = 473) : ¬ LeastCounterexample (source R (4 * w)) := by
  obtain ⟨a, b, hb, hn, hp, hq⟩ := quad_three_paths R w hR hw hr
  have hs := quad_source_bounds R w hR hw
  exact two_source_not_least _ _ _ a b _ _ _ hs.1 hs.2.1 hb hn hp hq

theorem finite_phase_periods :
    9 ^ 32 % 256 = 1 ∧ 9 ^ 26 % 256 = 17 ∧
      9 ^ 64 % 512 = 1 ∧ 9 ^ 35 % 512 = 473 := by decide +kernel

theorem double_exponent_exclusion (R : Nat) (hR : R % 32 = 26) :
    ¬ LeastCounterexample (source R 2) := by
  have he : R = 32 * (R / 32) + 26 := by omega
  have hr : 9 ^ R % 256 = 17 := by
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, finite_phase_periods.1]
    simp
  simpa only [Nat.mul_one] using double_residual_not_least R 1 (by omega)
    (by decide) (by simpa using hr)

theorem quad_exponent_exclusion (R : Nat) (hR : R % 64 = 35) :
    ¬ LeastCounterexample (source R 4) := by
  have he : R = 64 * (R / 64) + 35 := by omega
  have hr : 9 ^ R % 512 = 473 := by
    rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, finite_phase_periods.2.2.1]
    simp
  simpa only [Nat.mul_one] using quad_residual_not_least R 1 (by omega)
    (by decide) (by simpa using hr)

#print axioms third_partner_even
#print axioms two_partner_cover
#print axioms two_source_escape
#print axioms two_source_not_least
#print axioms double_source_bounds
#print axioms quad_source_bounds
#print axioms double_coordinates
#print axioms quad_coordinates
#print axioms double_profiles
#print axioms quad_profiles
#print axioms double_three_paths
#print axioms quad_three_paths
#print axioms double_residual_escape
#print axioms quad_residual_escape
#print axioms double_residual_not_least
#print axioms quad_residual_not_least
#print axioms finite_phase_periods
#print axioms double_exponent_exclusion
#print axioms quad_exponent_exclusion

end MinimumPhaseCover
