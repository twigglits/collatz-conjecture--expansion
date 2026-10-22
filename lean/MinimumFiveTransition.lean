/- A variable negative-five block gives later mergers inside the normalized
   secondary window obstruction. Collatz remains unresolved. -/
import MinimumSeventeenPhase

namespace MinimumFiveTransition
open OrdinaryCollatz MinimumSeventeenTransition MinimumSeventeenFourth
open MinimumSeventeenPhase MinimumSeventeenSeparation MinimumRootPredecessors

attribute [local irreducible] OrdinaryCollatz.iterate

def thirdScalar (k v : Nat) : Nat := 9 ^ (k + 1) * v

theorem five_bridges (q : Nat) (hq : 0 < q) :
    iterate 9 (64 * q - 13) = 27 * q - 5 ∧
    iterate 4 (48 * q - 14) = 18 * q - 5 := by
  have n0 : C (64 * q - 13) = 192 * q - 38 := by unfold C; split <;> omega
  have n1 : C (192 * q - 38) = 96 * q - 19 := by unfold C; split <;> omega
  have n2 : C (96 * q - 19) = 288 * q - 56 := by unfold C; split <;> omega
  have n3 : C (288 * q - 56) = 144 * q - 28 := by unfold C; split <;> omega
  have n4 : C (144 * q - 28) = 72 * q - 14 := by unfold C; split <;> omega
  have n5 : C (72 * q - 14) = 36 * q - 7 := by unfold C; split <;> omega
  have n6 : C (36 * q - 7) = 108 * q - 20 := by unfold C; split <;> omega
  have n7 : C (108 * q - 20) = 54 * q - 10 := by unfold C; split <;> omega
  have n8 : C (54 * q - 10) = 27 * q - 5 := by unfold C; split <;> omega
  have s0 : C (48 * q - 14) = 24 * q - 7 := by unfold C; split <;> omega
  have s1 : C (24 * q - 7) = 72 * q - 20 := by unfold C; split <;> omega
  have s2 : C (72 * q - 20) = 36 * q - 10 := by unfold C; split <;> omega
  have s3 : C (36 * q - 10) = 18 * q - 5 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, n0, n1, n2, n3, n4, n5, n6, n7, n8],
    by simp only [iterate, s0, s1, s2, s3]⟩

theorem third_profiles (b k v : Nat) (hv : 0 < v)
    (h : b = 1 + 2 ^ (3 * k + 4) * v) :
    iterate (9 + 5 * k) (4 * b - 17) = 3 * thirdScalar k v - 5 ∧
    iterate (4 + 5 * k) (3 * b - 17) = 2 * thirdScalar k v - 5 := by
  let q := 8 ^ k * v
  have hq : 0 < q := Nat.mul_pos (Nat.pow_pos (by decide)) hv
  have hpow : 2 ^ (3 * k + 4) * v = 16 * q := by
    rw [Nat.pow_add, Nat.pow_mul]
    change (8 ^ k * 16) * v = 16 * (8 ^ k * v)
    ac_rfl
  rw [hpow] at h
  have hn : 4 * b - 17 = 64 * q - 13 := by omega
  have hs : 3 * b - 17 = 48 * q - 14 := by omega
  have hb := five_bridges q hq
  have hmidN : 27 * q - 5 = MinimumLadderCover.source k (27 * v) := by
    unfold MinimumLadderCover.source q
    congr 1
    ac_rfl
  have hmidS : 18 * q - 5 = MinimumLadderCover.source k (18 * v) := by
    unfold MinimumLadderCover.source q
    congr 1
    ac_rfl
  have hfinalN : 9 ^ k * (27 * v) = 3 * thirdScalar k v := by
    unfold thirdScalar
    rw [Nat.pow_succ]
    change 9 ^ k * ((3 * 9) * v) = 3 * ((9 ^ k * 9) * v)
    ac_rfl
  have hfinalS : 9 ^ k * (18 * v) = 2 * thirdScalar k v := by
    unfold thirdScalar
    rw [Nat.pow_succ]
    change 9 ^ k * ((2 * 9) * v) = 2 * ((9 ^ k * 9) * v)
    ac_rfl
  exact ⟨by rw [iterate_add 9 (5 * k), hn, hb.1, hmidN,
    MinimumLadderCover.weighted_clock k (27 * v) (by omega), hfinalN],
    by rw [iterate_add 4 (5 * k), hs, hb.2, hmidS,
    MinimumLadderCover.weighted_clock k (18 * v) (by omega), hfinalS]⟩

theorem local_profiles (t : Nat) :
    iterate 4 (48 * t + 10) = 18 * t + 4 ∧
    iterate 6 (32 * t + 5) = 18 * t + 4 := by
  have n0 : C (48 * t + 10) = 24 * t + 5 := by unfold C; split <;> omega
  have n1 : C (24 * t + 5) = 72 * t + 16 := by unfold C; split <;> omega
  have n2 : C (72 * t + 16) = 36 * t + 8 := by unfold C; split <;> omega
  have n3 : C (36 * t + 8) = 18 * t + 4 := by unfold C; split <;> omega
  have s0 : C (32 * t + 5) = 96 * t + 16 := by unfold C; split <;> omega
  have s1 : C (96 * t + 16) = 48 * t + 8 := by unfold C; split <;> omega
  have s2 : C (48 * t + 8) = 24 * t + 4 := by unfold C; split <;> omega
  have s3 : C (24 * t + 4) = 12 * t + 2 := by unfold C; split <;> omega
  have s4 : C (12 * t + 2) = 6 * t + 1 := by unfold C; split <;> omega
  have s5 : C (6 * t + 1) = 18 * t + 4 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, n0, n1, n2, n3],
    by simp only [iterate, s0, s1, s2, s3, s4, s5]⟩

theorem local_meeting (d : Nat) (hd : d % 16 = 5) :
    iterate 6 (2 * d - 5) = iterate 4 (3 * d - 5) := by
  let t := d / 16
  have ht : d = 16 * t + 5 := by dsimp [t]; omega
  have hn : 3 * d - 5 = 48 * t + 10 := by omega
  have hs : 2 * d - 5 = 32 * t + 5 := by omega
  rw [hn, hs, (local_profiles t).1, (local_profiles t).2]

theorem third_meeting (b k v : Nat) (hv : 0 < v)
    (h : b = 1 + 2 ^ (3 * k + 4) * v) (hd : thirdScalar k v % 16 = 5) :
    iterate (10 + 5 * k) (3 * b - 17) = iterate (13 + 5 * k) (4 * b - 17) := by
  have hp := third_profiles b k v hv h
  rw [show 10 + 5 * k = (4 + 5 * k) + 6 by omega,
    show 13 + 5 * k = (9 + 5 * k) + 4 by omega,
    iterate_add (4 + 5 * k) 6, iterate_add (9 + 5 * k) 4, hp.1, hp.2,
    local_meeting _ hd]

theorem full_third_meeting (R w r u j q k v : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v % 16 = 5) :
    iterate (4 * R + 131 + 18 * r + 18 * j + 5 * k) (fourthSource R w) =
      iterate (5 * R + 120 + 18 * r + 18 * j + 5 * k) (mainSource R w) := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hn := (three_sources R w r u hw hu hX).1
  have hs := fourth_profile R w r u hr hw hu hX
  have hp := secondary_profiles (scalar r u) j q ha hq hT
  have hcN : 5 * R + 120 + 18 * r + 18 * j + 5 * k =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + (13 + 5 * k)) := by omega
  have hcS : 4 * R + 131 + 18 * r + 18 * j + 5 * k =
      (4 * R + 100 + 18 * r) + ((21 + 18 * j) + (10 + 5 * k)) := by omega
  rw [hcN, hcS, iterate_add (5 * R + 91 + 18 * r), iterate_add (4 * R + 100 + 18 * r),
    hn, hs, iterate_add (16 + 18 * j) (13 + 5 * k),
    iterate_add (21 + 18 * j) (10 + 5 * k), hp.1, hp.2, third_meeting _ k v hv hB hd]

theorem third_not_least (R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v % 16 = 5) : ¬ LeastCounterexample (mainSource R w) := by
  intro hn
  have hb := fourth_bounds R w hR hw
  have hm := full_third_meeting R w r u j q k v hr hw hu hq hv hX hT hB hd
  have hle := least_coalescing_predecessor hn hb.1 hm
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem finite_five_units :
    ∀ c : Fin 16, c.val % 2 = 1 →
      ∃ e : Fin 16, e.val % 2 = 1 ∧ (c.val * e.val) % 16 = 5 := by
  decide +kernel

theorem secondary_scale_bound (j : Nat) :
    2 ^ (9 + 11 * j) ≤ 3 ^ (6 + 7 * j) := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
  exact Nat.mul_le_mul (by decide : 512 ≤ 729)
    (Nat.pow_le_pow_left (by decide : 2048 ≤ 2187) j)

theorem third_units_odd (r u j q k v : Nat)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v % 16 = 5) : u % 2 = 1 ∧ q % 2 = 1 ∧ v % 2 = 1 := by
  have hbin : (2 ^ (3 * k + 4)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (show 1 ≤ 3 * k + 4 by omega))
  have hq : q % 2 = 1 := by
    have he := congrArg (fun z => z % 2) hB
    simpa [secondaryScalar, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hbin] using he
  have hexp : (2 ^ (9 + 11 * j)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (show 1 ≤ 9 + 11 * j by omega))
  have hs : scalar r u % 2 = 1 := by
    have he := congrArg (fun z => z % 2) hT
    rw [Nat.mul_mod, hexp] at he
    omega
  have hu : u % 2 = 1 := by simpa [scalar, Nat.mul_mod, Nat.pow_mod] using hs
  have hdodd : thirdScalar k v % 2 = 1 := by omega
  have hv : v % 2 = 1 := by simpa [thirdScalar, Nat.mul_mod, Nat.pow_mod] using hdodd
  exact ⟨hu, hq, hv⟩

theorem pure_third_lift (r j k B : Nat) :
    ∃ R u q v, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v % 16 = 5 := by
  let m := 57 + 11 * r
  let K := 9 + 11 * j
  let D := 2 ^ m
  let E := 2 ^ K
  let T := 2 ^ (3 * k + 4)
  let A := 3 ^ (35 + 7 * r)
  let c := 3 ^ (6 + 7 * j)
  let f := 9 ^ (k + 1)
  have hfodd : f % 2 = 1 := by dsimp [f]; rw [Nat.pow_mod]; simp
  have hcf : (f % 16) % 2 = 1 := by omega
  obtain ⟨eps, heodd, heunit⟩ := finite_five_units ⟨f % 16, Nat.mod_lt _ (by decide)⟩ hcf
  have hepos : 0 < eps.val := by omega
  have helt : eps.val < 16 := eps.isLt
  have heunit' : (f * eps.val) % 16 = 5 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt helt]
    exact heunit
  have hA : A % 2 = 1 := by dsimp [A]; rw [Nat.pow_mod]; simp
  have hcodd : c % 2 = 1 := by dsimp [c]; rw [Nat.pow_mod]; simp
  have hca : (c * A) % 2 = 1 := by simp [Nat.mul_mod, hcodd, hA]
  have hEc : E ≤ c := secondary_scale_bound j
  have hD : D = 8 * 2 ^ (54 + 11 * r) := by
    dsimp [D, m]
    rw [show 57 + 11 * r = (54 + 11 * r) + 3 by omega, Nat.pow_add]
    omega
  let F := 7 * (c * A) + D * (c - E) + (16 - eps.val) * D * E * T
  have hbase : (c * A + F) % 8 = 0 := by
    have he : c * A + F = 8 * (c * A + 2 ^ (54 + 11 * r) * (c - E) +
        (16 - eps.val) * 2 ^ (54 + 11 * r) * E * T) := by
      unfold F
      rw [hD]
      grind
    rw [he]
    omega
  obtain ⟨R, Q, hB, hR, hQ⟩ := unbounded_affine_lift (m + K + 3 * k + 5) (c * A) F B hca hbase
  have hpow : 2 ^ (m + K + 3 * k + 5 + 3) = 16 * (D * E * T) := by
    rw [show m + K + 3 * k + 5 + 3 = ((m + K) + (3 * k + 4)) + 4 by omega,
      Nat.pow_add, Nat.pow_add, Nat.pow_add]
    change ((D * E) * T) * 16 = 16 * (D * E * T)
    ac_rfl
  rw [hpow] at hQ
  have hpositive : 0 < (c * A) * 9 ^ R + F := by
    have hp : 0 < (c * A) * 9 ^ R :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
        (Nat.pow_pos (by decide))
    omega
  have hQpos : 0 < Q := Nat.pos_of_mul_pos_left (hQ ▸ hpositive)
  let v := 16 * (Q - 1) + eps.val
  have hvpos : 0 < v := by dsimp [v]; omega
  have hvmod : v % 16 = eps.val := by dsimp [v]; omega
  have hvsum : v + (16 - eps.val) = 16 * Q := by dsimp [v]; omega
  have hpad : D * E * T * v + (16 - eps.val) * D * E * T =
      16 * (D * E * T) * Q := by
    calc
      _ = (D * E * T) * (v + (16 - eps.val)) := by
        rw [Nat.mul_add (D * E * T) v (16 - eps.val)]
        ac_rfl
      _ = (D * E * T) * (16 * Q) := congrArg (fun z => (D * E * T) * z) hvsum
      _ = _ := by ac_rfl
  have hstart : (c * A) * (9 ^ R + 7) + D * (c - E) =
      D * E * T * v := by
    have he : (c * A) * (9 ^ R + 7) + D * (c - E) +
        (16 - eps.val) * D * E * T = 16 * (D * E * T) * Q := by
      rw [Nat.mul_add, show (c * A) * 7 = 7 * (c * A) by omega]
      simpa only [F, Nat.add_assoc] using hQ
    exact Nat.add_right_cancel (he.trans hpad.symm)
  have hdiv : D ∣ (c * A) * (9 ^ R + 7) := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_mul_right D (c - E))).mpr
    exact ⟨E * T * v, by rw [hstart]; ac_rfl⟩
  obtain ⟨u, hu⟩ := odd_power_cancel m (c * A) (9 ^ R + 7) hca hdiv
  have hupositive : 0 < 9 ^ R + 7 := Nat.succ_pos (9 ^ R + 6)
  have hup : 0 < u := Nat.pos_of_mul_pos_left (hu ▸ hupositive)
  have hde : c * D = D * (c - E) + D * E := by
    rw [← Nat.mul_add]
    have he : c - E + E = c := by omega
    rw [he]
    ac_rfl
  have hs2 : (c * A) * (9 ^ R + 7) + c * D = D * (E * (1 + T * v)) := by
    rw [hde, ← Nat.add_assoc, hstart]
    grind
  have hscaled : D * (c * (A * u + 1)) = D * (E * (1 + T * v)) := by
    calc
      _ = (c * A) * (D * u) + c * D := by grind
      _ = _ := by rw [← hu]; exact hs2
  have hcprod := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) hscaled
  have hEdiv : E ∣ c * (A * u + 1) := ⟨1 + T * v, hcprod⟩
  obtain ⟨q, hq⟩ := odd_power_cancel K c (A * u + 1) hcodd hEdiv
  have hqpositive : 0 < A * u + 1 := Nat.succ_pos (A * u)
  have hqp : 0 < q := Nat.pos_of_mul_pos_left (hq ▸ hqpositive)
  have hlast : c * q = 1 + T * v := by
    have he : E * (c * q) = E * (1 + T * v) := by
      calc
        _ = c * (E * q) := by ac_rfl
        _ = _ := by rw [← hq]; exact hcprod
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos K) he
  have hscalar : A * u = 9 * scalar r u := by
    unfold A scalar
    rw [show 35 + 7 * r = (33 + 7 * r) + 2 by omega, Nat.pow_add]
    ac_rfl
  rw [hscalar] at hq
  have hguard : thirdScalar k v % 16 = 5 := by
    change (f * v) % 16 = 5
    rw [Nat.mul_mod, hvmod]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt helt] at heunit'
    exact heunit'
  exact ⟨R, u, q, v, hB, hR, hup, hqp, hvpos, hu, hq, hlast, hguard⟩

theorem weighted_third_lift (R r j k B : Nat) :
    ∃ w u q v, B < w ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v % 16 = 5 := by
  obtain ⟨S, u, q, v, hS, _, hu, hq, hv, hX, hT, hB, hd⟩ := pure_third_lift r j k (R + B + 1)
  refine ⟨9 ^ (S - R), u, q, v, ?_, hu, hq, hv, ?_, hT, hB, hd⟩
  · exact Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  · rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX

def SecondarySeparated (H R w r j : Nat) : Prop :=
  ∀ s t, s ≤ H → t ≤ H →
    iterate (4 * R + 121 + 18 * r + 18 * j + s) (fourthSource R w) ≠
      iterate (5 * R + 107 + 18 * r + 18 * j + t) (mainSource R w)

def ThirdEscape (H R w r j k : Nat) : Prop :=
  ∃ u q v, 0 < u ∧ 0 < q ∧ 0 < v ∧
    9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
    9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
    secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
    thirdScalar k v % 16 = 5 ∧
    (u % 2 = 1 ∧ q % 2 = 1 ∧ v % 2 = 1) ∧
    ¬ LeastCounterexample (mainSource R w) ∧ SecondarySeparated H R w r j ∧
    iterate (4 * R + 131 + 18 * r + 18 * j + 5 * k) (fourthSource R w) =
      iterate (5 * R + 120 + 18 * r + 18 * j + 5 * k) (mainSource R w)

theorem third_window_separation (H R w r u j q k v : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q)
    (hH : H + 6 ≤ 3 * k + 4)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    SecondarySeparated H R w r j := by
  have hdiv : 2 ^ (H + 6) ∣ secondaryScalar j q - 1 := by
    apply Nat.dvd_trans (Nat.pow_dvd_pow 2 hH)
    exact ⟨v, by rw [hB]; omega⟩
  exact secondary_source_separation H R w r u j q hr hw hu hq hX hT hdiv

theorem build_third_escape (H R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hH : H + 6 ≤ 3 * k + 4)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v % 16 = 5) : ThirdEscape H R w r j k := by
  exact ⟨u, q, v, hu, hq, hv, hX, hT, hB, hd, third_units_odd r u j q k v hT hB hd,
    third_not_least R w r u j q k v hR hr hw hu hq hv hX hT hB hd,
    third_window_separation H R w r u j q k v hr hw hu hq hH hX hT hB,
    full_third_meeting R w r u j q k v hr hw hu hq hv hX hT hB hd⟩

theorem pure_third_escape (r j k H B : Nat) (hr : 5 ≤ r) (hH : H + 6 ≤ 3 * k + 4) :
    ∃ R, B < R ∧ 14 ≤ R ∧ ThirdEscape H R 1 r j k := by
  obtain ⟨R, u, q, v, hB, hR, hu, hq, hv, hX, hT, hb, hd⟩ := pure_third_lift r j k B
  exact ⟨R, hB, hR, build_third_escape H R 1 r u j q k v hR hr (by decide) hu hq hv
    hH (by simpa only [Nat.mul_one] using hX) hT hb hd⟩

theorem weighted_third_escape (R r j k H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hH : H + 6 ≤ 3 * k + 4) : ∃ w, B < w ∧ ThirdEscape H R w r j k := by
  obtain ⟨w, u, q, v, hwB, hu, hq, hv, hX, hT, hb, hd⟩ := weighted_third_lift R r j k B
  have hw : 0 < w := by omega
  exact ⟨w, hwB, build_third_escape H R w r u j q k v hR hr hw hu hq hv hH hX hT hb hd⟩

theorem escape_primary_window (H R w r j k : Nat) (hr : 5 ≤ r) (hw : 0 < w)
    (hH : H + 13 ≤ 9 + 11 * j) (he : ThirdEscape H R w r j k) :
    FourSeparated H R w r := by
  obtain ⟨u, q, _, hu, _, _, hX, hT, _⟩ := he
  have hdiv : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hH) ⟨q, hT⟩
  exact four_source_separation H R w r u hr hw hu hX hdiv

theorem pure_both_windows (r H B : Nat) (hr : 5 ≤ r) :
    ∃ R, B < R ∧ 14 ≤ R ∧
      ThirdEscape H R 1 r (H + 1) (H + 1) ∧ FourSeparated H R 1 r := by
  obtain ⟨R, hB, hR, he⟩ := pure_third_escape r (H + 1) (H + 1) H B hr (by omega)
  exact ⟨R, hB, hR, he, escape_primary_window H R 1 r (H + 1) (H + 1) hr (by decide) (by omega) he⟩

theorem weighted_both_windows (R r H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) :
    ∃ w, B < w ∧ ThirdEscape H R w r (H + 1) (H + 1) ∧ FourSeparated H R w r := by
  obtain ⟨w, hwB, he⟩ := weighted_third_escape R r (H + 1) (H + 1) H B hR hr (by omega)
  exact ⟨w, hwB, he, escape_primary_window H R w r (H + 1) (H + 1) hr (by omega) (by omega) he⟩

#print axioms five_bridges
#print axioms third_profiles
#print axioms local_profiles
#print axioms local_meeting
#print axioms third_meeting
#print axioms full_third_meeting
#print axioms third_not_least
#print axioms finite_five_units
#print axioms secondary_scale_bound
#print axioms third_units_odd
#print axioms pure_third_lift
#print axioms weighted_third_lift
#print axioms third_window_separation
#print axioms build_third_escape
#print axioms pure_third_escape
#print axioms weighted_third_escape
#print axioms escape_primary_window
#print axioms pure_both_windows
#print axioms weighted_both_windows

end MinimumFiveTransition
