/- Variable odd-block exits after the negative-five transition.
   The complementary merger uses a larger companion, not a least-source proof. -/
import MinimumFiveTransition

namespace MinimumFiveOddExit
open OrdinaryCollatz MinimumSeventeenTransition MinimumSeventeenFourth
open MinimumSeventeenPhase MinimumSeventeenSeparation MinimumFiveTransition
open MinimumRootPredecessors

attribute [local irreducible] OrdinaryCollatz.iterate

theorem adjacent_bridges (l z d : Nat) (hz : 0 < z)
    (hd : d = 1 + 2 ^ (l + 1) * z) :
    iterate 1 (3 * d - 5) = 2 ^ l * (3 * z) - 1 ∧
    iterate 3 (2 * d - 5) = 2 ^ l * (3 * z) - 2 := by
  let x := 2 ^ l * z
  have hx : 0 < x := Nat.mul_pos (Nat.two_pow_pos l) hz
  have he : d = 1 + 2 * x := by rw [hd, Nat.pow_succ]; dsimp [x]; congr 1; ac_rfl
  have hn : 3 * d - 5 = 6 * x - 2 := by omega
  have hs : 2 * d - 5 = 4 * x - 3 := by omega
  have hq : 2 ^ l * (3 * z) = 3 * x := by dsimp [x]; ac_rfl
  have n0 : C (6 * x - 2) = 3 * x - 1 := by unfold C; split <;> omega
  have s0 : C (4 * x - 3) = 12 * x - 8 := by unfold C; split <;> omega
  have s1 : C (12 * x - 8) = 6 * x - 4 := by unfold C; split <;> omega
  have s2 : C (6 * x - 4) = 3 * x - 2 := by unfold C; split <;> omega
  exact ⟨by simp only [hn, hq, iterate, n0], by simp only [hs, hq, iterate, s0, s1, s2]⟩

theorem odd_exit_meeting (l z d : Nat) (hl : 0 < l) (hz : 0 < z)
    (hd : d = 1 + 2 ^ (l + 1) * z) (hg : (3 ^ (l + 1) * z) % 4 = 1) :
    iterate (2 * l + 5) (2 * d - 5) = iterate (2 * l + 3) (3 * d - 5) := by
  have hb := adjacent_bridges l z d hz hd
  have hg' : (3 ^ l * (3 * z)) % 4 = 1 := by rw [Nat.pow_succ] at hg; simpa only [Nat.mul_assoc] using hg
  have hm := MinimumLadderCover.adjacent_odd_block l (3 * z) hl (by omega) hg'
  rw [show 2 * l + 5 = 3 + (2 * l + 2) by omega,
    show 2 * l + 3 = 1 + (2 * l + 2) by omega, iterate_add 3, iterate_add 1, hb.1, hb.2]
  exact hm

theorem opposite_exit_meeting (l z d : Nat) (hz : 0 < z)
    (hd : d = 1 + 2 ^ (l + 1) * z) (hg : (3 ^ (l + 1) * z) % 4 = 3) :
    iterate (2 * l + 4) (3 * d - 4) = iterate (2 * l + 4) (3 * d - 5) := by
  let t := (3 ^ (l + 1) * z) / 4
  have ht : 3 ^ l * (3 * z) = 4 * t + 3 := by
    have he : 3 ^ l * (3 * z) = 3 ^ (l + 1) * z := by rw [Nat.pow_succ]; ac_rfl
    rw [he]; dsimp [t]; omega
  have hm := MinimumFirstTarget.half_source_meeting l (3 * z) t (by omega) ht
  have hp := Nat.mul_pos (Nat.two_pow_pos l) hz
  have he : 3 * d - 4 = 2 ^ (l + 1) * (3 * z) - 1 := by
    have heq : 2 ^ (l + 1) * (3 * z) = 3 * (2 ^ (l + 1) * z) := by ac_rfl
    rw [heq, hd]; omega
  rw [he, hm.2, show 2 * l + 4 = 1 + (2 * l + 3) by omega,
    iterate_add 1, (adjacent_bridges l z d hz hd).1, hm.1]

theorem full_odd_exit_meeting (R w r u j q k v l z : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hz : 0 < z)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 1 + 2 ^ (l + 1) * z)
    (hg : (3 ^ (l + 1) * z) % 4 = 1) :
    iterate (4 * R + 130 + 18 * r + 18 * j + 5 * k + 2 * l) (fourthSource R w) =
      iterate (5 * R + 119 + 18 * r + 18 * j + 5 * k + 2 * l) (mainSource R w) := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hn := (three_sources R w r u hw hu hX).1
  have hs := fourth_profile R w r u hr hw hu hX
  have hp := secondary_profiles (scalar r u) j q ha hq hT
  have ht := third_profiles (secondaryScalar j q) k v hv hB
  have hcN : 5 * R + 119 + 18 * r + 18 * j + 5 * k + 2 * l =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + ((9 + 5 * k) + (2 * l + 3))) := by omega
  have hcS : 4 * R + 130 + 18 * r + 18 * j + 5 * k + 2 * l =
      (4 * R + 100 + 18 * r) + ((21 + 18 * j) + ((4 + 5 * k) + (2 * l + 5))) := by omega
  rw [hcN, hcS, iterate_add (5 * R + 91 + 18 * r), iterate_add (4 * R + 100 + 18 * r),
    hn, hs, iterate_add (16 + 18 * j), iterate_add (21 + 18 * j), hp.1, hp.2,
    iterate_add (9 + 5 * k), iterate_add (4 + 5 * k), ht.1, ht.2,
    odd_exit_meeting l z _ hl hz hd hg]

theorem odd_exit_not_least (R w r u j q k v l z : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hz : 0 < z)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 1 + 2 ^ (l + 1) * z)
    (hg : (3 ^ (l + 1) * z) % 4 = 1) : ¬ LeastCounterexample (mainSource R w) := by
  intro hn
  have hb := fourth_bounds R w hR hw
  have hm := full_odd_exit_meeting R w r u j q k v l z hr hw hu hq hv hl hz hX hT hB hd hg
  have hle := least_coalescing_predecessor hn hb.1 hm
  omega

theorem pure_residue_lift (r j k h eps B : Nat) (hepos : 0 < eps)
    (helt : eps < 2 ^ (h + 1)) :
    ∃ R u q v, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      v % (2 ^ (h + 1)) = eps := by
  let m := 57 + 11 * r
  let K := 9 + 11 * j
  let D := 2 ^ m
  let E := 2 ^ K
  let T := 2 ^ (3 * k + 4)
  let A := 3 ^ (35 + 7 * r)
  let c := 3 ^ (6 + 7 * j)
  let V := 2 ^ (h + 1)
  change eps < V at helt
  have hA : A % 2 = 1 := by dsimp [A]; rw [Nat.pow_mod]; simp
  have hcodd : c % 2 = 1 := by dsimp [c]; rw [Nat.pow_mod]; simp
  have hca : (c * A) % 2 = 1 := by simp [Nat.mul_mod, hcodd, hA]
  have hEc : E ≤ c := secondary_scale_bound j
  have hD : D = 8 * 2 ^ (54 + 11 * r) := by
    dsimp [D, m]
    rw [show 57 + 11 * r = (54 + 11 * r) + 3 by omega, Nat.pow_add]
    omega
  let F := 7 * (c * A) + D * (c - E) + (V - eps) * D * E * T
  have hbase : (c * A + F) % 8 = 0 := by
    have he : c * A + F = 8 * (c * A + 2 ^ (54 + 11 * r) * (c - E) +
        (V - eps) * 2 ^ (54 + 11 * r) * E * T) := by
      unfold F
      rw [hD]
      grind
    rw [he]
    omega
  obtain ⟨R, Q, hB, hR, hQ⟩ := unbounded_affine_lift (m + K + 3 * k + h + 2) (c * A) F B hca hbase
  have hpow : 2 ^ (m + K + 3 * k + h + 2 + 3) = V * (D * E * T) := by
    rw [show m + K + 3 * k + h + 2 + 3 = ((m + K) + (3 * k + 4)) + (h + 1) by omega,
      Nat.pow_add, Nat.pow_add, Nat.pow_add]
    change ((D * E) * T) * V = V * (D * E * T)
    ac_rfl
  rw [hpow] at hQ
  have hpositive : 0 < (c * A) * 9 ^ R + F := by
    have hp : 0 < (c * A) * 9 ^ R :=
      Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))
        (Nat.pow_pos (by decide))
    omega
  have hQpos : 0 < Q := Nat.pos_of_mul_pos_left (hQ ▸ hpositive)
  let v := V * (Q - 1) + eps
  have hvpos : 0 < v := by dsimp [v]; omega
  have hvmod : v % V = eps := by simp only [v, Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_eq_of_lt helt]
  have hvsum : v + (V - eps) = V * Q := by
    have hcancel : eps + (V - eps) = V := by omega
    calc
      _ = V * (Q - 1) + (eps + (V - eps)) := by dsimp [v]; omega
      _ = V * ((Q - 1) + 1) := by rw [hcancel, Nat.mul_add, Nat.mul_one]
      _ = V * Q := congrArg (V * ·) (by omega)
  have hpad : D * E * T * v + (V - eps) * D * E * T =
      V * (D * E * T) * Q := by
    calc
      _ = (D * E * T) * (v + (V - eps)) := by
        rw [Nat.mul_add (D * E * T) v (V - eps)]
        ac_rfl
      _ = (D * E * T) * (V * Q) := congrArg (fun z => (D * E * T) * z) hvsum
      _ = _ := by ac_rfl
  have hstart : (c * A) * (9 ^ R + 7) + D * (c - E) =
      D * E * T * v := by
    have he : (c * A) * (9 ^ R + 7) + D * (c - E) +
        (V - eps) * D * E * T = V * (D * E * T) * Q := by
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
  exact ⟨R, u, q, v, hB, hR, hup, hqp, hvpos, hu, hq, hlast, hvmod⟩

theorem binary_target (h c g : Nat) (hc : c % 2 = 1) (hg : g % 2 = 1)
    (hgt : g < 2 ^ (h + 1)) :
    ∃ eps, 0 < eps ∧ eps < 2 ^ (h + 1) ∧ eps % 2 = 1 ∧
      (c * eps) % (2 ^ (h + 1)) = g := by
  obtain ⟨e, t, _, _, heodd, heq⟩ := odd_binary_inverse h c hc
  let V := 2 ^ (h + 1)
  change g < V at hgt
  let eps := (e * g) % V
  have hVpos : 0 < V := Nat.two_pow_pos (h + 1)
  have hdiv : 2 ∣ V := Nat.pow_dvd_pow 2 (by omega : 1 ≤ h + 1)
  have hepsodd : eps % 2 = 1 := by
    change (e * g) % V % 2 = 1
    rw [Nat.mod_mod_of_dvd _ hdiv, Nat.mul_mod, heodd, hg]
  have hepspos : 0 < eps := by omega
  refine ⟨eps, hepspos, Nat.mod_lt _ hVpos, hepsodd, ?_⟩
  change (c * eps) % V = g
  calc
    _ = (c * (e * g)) % V := by simp only [eps, Nat.mul_mod, Nat.mod_mod]
    _ = ((1 + V * t) * g) % V := by rw [← Nat.mul_assoc, heq]
    _ = g := by simp only [Nat.add_mul, Nat.one_mul, Nat.add_mod,
      Nat.mul_assoc, Nat.mul_mod_right, Nat.add_zero, Nat.mod_eq_of_lt hgt]

theorem pure_odd_exit_lift (r j k l g B : Nat) (hg : g = 1 ∨ g = 3) :
    ∃ R u q v z, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧ 0 < z ∧ z % 2 = 1 ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v = 1 + 2 ^ (l + 1) * z ∧ (3 ^ (l + 1) * z) % 4 = g := by
  have hgodd : g % 2 = 1 := by omega
  have h3odd : (3 ^ (l + 1)) % 2 = 1 := by rw [Nat.pow_mod]; simp
  obtain ⟨z0, hz0, hz04, hz0odd, hz0g⟩ := binary_target 1 (3 ^ (l + 1)) g h3odd hgodd (by omega)
  let D := 2 ^ (l + 1)
  let V := 2 ^ (l + 3)
  let target := 1 + D * z0
  have hV : V = 4 * D := by dsimp [V, D]; rw [show l + 3 = (l + 1) + 2 by omega, Nat.pow_add]; omega
  have hD : 2 ≤ D := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ l + 1)
  have hDeven : D % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1 ≤ l + 1))
  have htargetodd : target % 2 = 1 := by simp [target, Nat.add_mod, Nat.mul_mod, hDeven]
  have htargetlt : target < 2 ^ ((l + 2) + 1) := by
    have hh := Nat.mul_le_mul_left D (show z0 ≤ 3 by omega)
    change target < V
    dsimp [target]; rw [hV]; omega
  have hfodd : (9 ^ (k + 1)) % 2 = 1 := by rw [Nat.pow_mod]; simp
  obtain ⟨eps, heps, hepslt, _, heq⟩ := binary_target (l + 2) (9 ^ (k + 1)) target hfodd htargetodd htargetlt
  obtain ⟨R, u, q, v, hR, hR14, hu, hq, hv, hX, hT, hB, hvmod⟩ :=
    pure_residue_lift r j k (l + 2) eps B heps hepslt
  have hdmod : thirdScalar k v % V = target := by
    change (9 ^ (k + 1) * v) % V = target
    change v % V = eps at hvmod
    change (9 ^ (k + 1) * eps) % V = target at heq
    change eps < V at hepslt
    rw [Nat.mul_mod, hvmod]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hepslt] at heq
    exact heq
  let z := 4 * (thirdScalar k v / V) + z0
  have hz : 0 < z := by dsimp [z]; omega
  have hzodd : z % 2 = 1 := by dsimp [z]; omega
  have hcoord : thirdScalar k v = 1 + D * z := by
    have he := Nat.mod_add_div (thirdScalar k v) V
    rw [hdmod, hV] at he
    dsimp [target] at he
    dsimp [z]
    grind
  have hguard : (3 ^ (l + 1) * z) % 4 = g := by
    change (3 ^ (l + 1) * z0) % 4 = g at hz0g
    have hzmod : z % 4 = z0 := by dsimp [z]; omega
    rw [Nat.mul_mod, hzmod]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hz04] at hz0g
    exact hz0g
  exact ⟨R, u, q, v, z, hR, hR14, hu, hq, hv, hz, hzodd, hX, hT, hB, hcoord, hguard⟩

theorem weighted_odd_exit_lift (R r j k l g B : Nat) (hg : g = 1 ∨ g = 3) :
    ∃ w u q v z, B < w ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧ 0 < z ∧ z % 2 = 1 ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v = 1 + 2 ^ (l + 1) * z ∧ (3 ^ (l + 1) * z) % 4 = g := by
  obtain ⟨S, u, q, v, z, hS, _, hu, hq, hv, hz, hzo, hX, hT, hB, hd, hg⟩ :=
    pure_odd_exit_lift r j k l g (R + B + 1) hg
  refine ⟨9 ^ (S - R), u, q, v, z, ?_, hu, hq, hv, hz, hzo, ?_, hT, hB, hd, hg⟩
  · exact Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  · rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX

theorem exit_growth_bound (s t : Nat) :
    5 * 2 ^ (167 + 11 * s + 3 * t) ≤ 3 ^ (107 + 7 * s + 2 * t) := by
  have hb : 5 * 2 ^ 167 ≤ 3 ^ 107 := by decide
  have hs := Nat.pow_le_pow_left (by decide : 2 ^ 11 ≤ 3 ^ 7) s
  have ht := Nat.pow_le_pow_left (by decide : 2 ^ 3 ≤ 3 ^ 2) t
  have h := Nat.mul_le_mul (Nat.mul_le_mul hb hs) ht
  simpa only [Nat.pow_add, Nat.pow_mul, Nat.mul_assoc] using h

theorem companion_above_source (R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    mainSource R w < 3 * thirdScalar k v - 4 := by
  let D := 2 ^ (57 + 11 * r)
  let E := 2 ^ (9 + 11 * j)
  let T := 2 ^ (3 * k + 4)
  let A := 3 ^ (35 + 7 * r)
  let c := 3 ^ (6 + 7 * j)
  let f := 9 ^ (k + 1)
  have hEc : E ≤ c := secondary_scale_bound j
  have hA : A * u = 9 * scalar r u := by
    dsimp [A, scalar]
    rw [show 35 + 7 * r = (33 + 7 * r) + 2 by omega, Nat.pow_add]
    ac_rfl
  have ht : A * u + 1 = E * q := by rw [hA]; exact hT
  have hb : c * q = 1 + T * v := hB
  have he : c * (A * u) + c = E + E * (T * v) := by
    calc
      _ = c * (A * u + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = E * (c * q) := by rw [ht]; ac_rfl
      _ = _ := by rw [hb, Nat.mul_add, Nat.mul_one]
  have hc : c * (A * u) ≤ E * (T * v) := by omega
  have hmul := Nat.mul_le_mul_left D hc
  have hlhs : D * (c * (A * u)) = c * A * (9 ^ R * w + 7) := by
    calc
      _ = c * A * (D * u) := by ac_rfl
      _ = _ := by rw [← hX]
  rw [hlhs] at hmul
  have hsmall : c * A * (9 ^ R * w) ≤ D * (E * (T * v)) :=
    Nat.le_trans (Nat.mul_le_mul_left (c * A) (Nat.le_add_right _ _)) hmul
  have hbig := Nat.mul_le_mul_left (3 * f) hsmall
  have hbound : 5 * (8 ^ R * (D * E * T)) ≤ 3 * (f * (c * (A * 9 ^ R))) := by
    have hh := exit_growth_bound (r - 5 + j) (R - 14 + k)
    have h2 : 167 + 11 * (r - 5 + j) + 3 * (R - 14 + k) =
        3 * R + ((57 + 11 * r) + (9 + 11 * j) + (3 * k + 4)) := by omega
    have h3 : 107 + 7 * (r - 5 + j) + 2 * (R - 14 + k) =
        1 + (2 * (k + 1) + ((6 + 7 * j) + ((35 + 7 * r) + 2 * R))) := by omega
    rw [h2, h3, Nat.pow_add, Nat.pow_mul] at hh
    simpa only [D, E, T, A, c, f, Nat.pow_add, Nat.pow_mul, Nat.pow_one,
      Nat.reducePow, Nat.mul_assoc] using hh
  have hlow := Nat.mul_le_mul_right w hbound
  have hall : (D * E * T) * (5 * (8 ^ R * w)) ≤ (D * E * T) * (3 * thirdScalar k v) := by
    calc
      _ = (5 * (8 ^ R * (D * E * T))) * w := by ac_rfl
      _ ≤ (3 * (f * (c * (A * 9 ^ R)))) * w := hlow
      _ = (3 * f) * (c * A * (9 ^ R * w)) := by ac_rfl
      _ ≤ (3 * f) * (D * (E * (T * v))) := hbig
      _ = _ := by change _ = (D * E * T) * (3 * (f * v)); ac_rfl
  have hpos : 0 < D * E * T := Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) (Nat.two_pow_pos _)
  have hfin := Nat.le_of_mul_le_mul_left hall hpos
  have hy : 0 < 8 ^ R * w := Nat.mul_pos (Nat.pow_pos (by decide)) hw
  unfold mainSource MinimumLadderCover.source
  have hy4 : 8 ^ R * (4 * w) = 4 * (8 ^ R * w) := by ac_rfl
  rw [hy4]
  omega

theorem exit_units_odd (r u j q k v l z : Nat)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 1 + 2 ^ (l + 1) * z) :
    u % 2 = 1 ∧ q % 2 = 1 ∧ v % 2 = 1 := by
  have hq2 : (2 ^ (3 * k + 4)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 3 * k + 4))
  have hqodd : q % 2 = 1 := by
    have he := congrArg (fun t => t % 2) hB
    simpa [secondaryScalar, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hq2] using he
  have hu2 : (2 ^ (9 + 11 * j)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1 ≤ 9 + 11 * j))
  have hs : scalar r u % 2 = 1 := by
    have he := congrArg (fun t => t % 2) hT
    rw [Nat.mul_mod, hu2] at he
    omega
  have huodd : u % 2 = 1 := by simpa [scalar, Nat.mul_mod, Nat.pow_mod] using hs
  have hv2 : (2 ^ (l + 1)) % 2 = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by omega : 1 ≤ l + 1))
  have hvodd : v % 2 = 1 := by
    have he := congrArg (fun t => t % 2) hd
    simpa [thirdScalar, Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hv2] using he
  exact ⟨huodd, hqodd, hvodd⟩

def ExitRealization (R w r j k l g : Nat) : Prop :=
  ∃ u q v z, 0 < u ∧ 0 < q ∧ 0 < v ∧ 0 < z ∧ z % 2 = 1 ∧
    9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
    9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
    secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
    thirdScalar k v = 1 + 2 ^ (l + 1) * z ∧ (3 ^ (l + 1) * z) % 4 = g

def OddEscape (H R w r j k l : Nat) : Prop :=
  ExitRealization R w r j k l 1 ∧ ¬ LeastCounterexample (mainSource R w) ∧
    FourSeparated H R w r ∧ SecondarySeparated H R w r j ∧
    iterate (4 * R + 130 + 18 * r + 18 * j + 5 * k + 2 * l) (fourthSource R w) =
      iterate (5 * R + 119 + 18 * r + 18 * j + 5 * k + 2 * l) (mainSource R w)

theorem realization_windows (H R w r j k l g : Nat) (hr : 5 ≤ r) (hw : 0 < w)
    (hHj : H + 13 ≤ 9 + 11 * j) (hHk : H + 6 ≤ 3 * k + 4)
    (he : ExitRealization R w r j k l g) :
    FourSeparated H R w r ∧ SecondarySeparated H R w r j := by
  obtain ⟨u, q, v, _, hu, hq, _, _, _, hX, hT, hB, _⟩ := he
  have hdiv : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hHj) ⟨q, hT⟩
  exact ⟨four_source_separation H R w r u hr hw hu hX hdiv,
    third_window_separation H R w r u j q k v hr hw hu hq hHk hX hT hB⟩

theorem build_odd_escape (H R w r j k l : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hl : 0 < l) (hHj : H + 13 ≤ 9 + 11 * j) (hHk : H + 6 ≤ 3 * k + 4)
    (he : ExitRealization R w r j k l 1) : OddEscape H R w r j k l := by
  have hsep := realization_windows H R w r j k l 1 hr hw hHj hHk he
  refine ⟨he, ?_, hsep.1, hsep.2, ?_⟩
  · obtain ⟨u, q, v, z, hu, hq, hv, hz, _, hX, hT, hB, hd, hg⟩ := he
    exact odd_exit_not_least R w r u j q k v l z hR hr hw hu hq hv hl hz hX hT hB hd hg
  · obtain ⟨u, q, v, z, hu, hq, hv, hz, _, hX, hT, hB, hd, hg⟩ := he
    exact full_odd_exit_meeting R w r u j q k v l z hr hw hu hq hv hl hz hX hT hB hd hg

theorem pure_odd_escape (r j k l H B : Nat) (hr : 5 ≤ r) (hl : 0 < l)
    (hHj : H + 13 ≤ 9 + 11 * j) (hHk : H + 6 ≤ 3 * k + 4) :
    ∃ R, B < R ∧ 14 ≤ R ∧ OddEscape H R 1 r j k l := by
  obtain ⟨R, u, q, v, z, hR, hR14, hu, hq, hv, hz, hzo, hX, hT, hB, hd, hg⟩ :=
    pure_odd_exit_lift r j k l 1 B (Or.inl rfl)
  have he : ExitRealization R 1 r j k l 1 :=
    ⟨u, q, v, z, hu, hq, hv, hz, hzo, by simpa only [Nat.mul_one] using hX, hT, hB, hd, hg⟩
  exact ⟨R, hR, hR14, build_odd_escape H R 1 r j k l hR14 hr (by decide) hl hHj hHk he⟩

theorem weighted_odd_escape (R r j k l H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) (hl : 0 < l)
    (hHj : H + 13 ≤ 9 + 11 * j) (hHk : H + 6 ≤ 3 * k + 4) :
    ∃ w, B < w ∧ OddEscape H R w r j k l := by
  obtain ⟨w, u, q, v, z, hw, hu, hq, hv, hz, hzo, hX, hT, hB, hd, hg⟩ :=
    weighted_odd_exit_lift R r j k l 1 B (Or.inl rfl)
  have he : ExitRealization R w r j k l 1 := ⟨u, q, v, z, hu, hq, hv, hz, hzo, hX, hT, hB, hd, hg⟩
  exact ⟨w, hw, build_odd_escape H R w r j k l hR hr (by omega) hl hHj hHk he⟩

theorem full_opposite_meeting (R w r u j q k v l z : Nat)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hz : 0 < z)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 1 + 2 ^ (l + 1) * z)
    (hg : (3 ^ (l + 1) * z) % 4 = 3) :
    iterate (2 * l + 4) (3 * thirdScalar k v - 4) =
      iterate (5 * R + 120 + 18 * r + 18 * j + 5 * k + 2 * l) (mainSource R w) := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hn := (three_sources R w r u hw hu hX).1
  have hp := (secondary_profiles (scalar r u) j q ha hq hT).1
  have ht := (third_profiles (secondaryScalar j q) k v hv hB).1
  rw [show 5 * R + 120 + 18 * r + 18 * j + 5 * k + 2 * l =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + ((9 + 5 * k) + (2 * l + 4))) by omega,
    iterate_add (5 * R + 91 + 18 * r), hn, iterate_add (16 + 18 * j), hp,
    iterate_add (9 + 5 * k), ht]
  exact opposite_exit_meeting l z _ hz hd hg

theorem odd_exit_dichotomy (d : Nat) (hd : 1 < d) (hd4 : d % 4 = 1) :
    ∃ l z, 0 < l ∧ 0 < z ∧ z % 2 = 1 ∧ d = 1 + 2 ^ (l + 1) * z ∧
      (((3 ^ (l + 1) * z) % 4 = 1 ∧
        iterate (2 * l + 5) (2 * d - 5) = iterate (2 * l + 3) (3 * d - 5)) ∨
       ((3 ^ (l + 1) * z) % 4 = 3 ∧
        iterate (2 * l + 4) (3 * d - 4) = iterate (2 * l + 4) (3 * d - 5))) := by
  obtain ⟨K, z, hz, hzo, he⟩ := MinimumLadderBlockExit.odd_factorization (d - 1) (by omega)
  have hK : 2 ≤ K := by
    by_cases h : 2 ≤ K
    · exact h
    exfalso
    have hc : K = 0 ∨ K = 1 := by omega
    rcases hc with h0 | h1
    · rw [h0] at he; simp only [Nat.pow_zero, Nat.one_mul] at he; omega
    · rw [h1] at he; simp only [Nat.pow_one] at he; omega
  have hcoord : d = 1 + 2 ^ ((K - 1) + 1) * z := by rw [show K - 1 + 1 = K by omega]; omega
  have hodd : (3 ^ ((K - 1) + 1) * z) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hzo]
  refine ⟨K - 1, z, by omega, hz, hzo, hcoord, ?_⟩
  have hc : (3 ^ ((K - 1) + 1) * z) % 4 = 1 ∨ (3 ^ ((K - 1) + 1) * z) % 4 = 3 := by omega
  rcases hc with hg | hg
  · exact Or.inl ⟨hg, odd_exit_meeting (K - 1) z d (by omega) hz hcoord hg⟩
  · exact Or.inr ⟨hg, opposite_exit_meeting (K - 1) z d hz hcoord hg⟩

theorem least_odd_exit_constraint (R w r u j q k v l z : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hz : 0 < z)
    (hzo : z % 2 = 1)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 1 + 2 ^ (l + 1) * z)
    (hn : LeastCounterexample (mainSource R w)) : (3 ^ (l + 1) * z) % 4 = 3 := by
  have hodd : (3 ^ (l + 1) * z) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hzo]
  by_cases hg : (3 ^ (l + 1) * z) % 4 = 3
  · exact hg
  exfalso
  have hg1 : (3 ^ (l + 1) * z) % 4 = 1 := by omega
  exact odd_exit_not_least R w r u j q k v l z hR hr hw hu hq hv hl hz hX hT hB hd hg1 hn

theorem opposite_exit_profiles (l z d h : Nat) (hl : 0 < l) (hz : 0 < z)
    (hd : d = 1 + 2 ^ (l + 1) * z) (he : 3 ^ l * z = 4 * h + 1) :
    iterate (2 * l + 4) (3 * d - 5) = 9 * h + 2 ∧
    iterate (2 * l + 4) (2 * d - 5) = h := by
  have hthree : 3 ^ l * (3 * z) = 4 * (3 * h) + 3 := by
    have hh : 3 ^ l * (3 * z) = 3 * (3 ^ l * z) := by ac_rfl
    rw [hh, he]; omega
  have hn := (MinimumFirstTarget.half_source_meeting l (3 * z) (3 * h) (by omega) hthree).1
  have hbridge := adjacent_bridges l z d hz hd
  have htwo : 2 ^ l * (3 * z) - 2 = 2 * (2 ^ (l - 1) * (3 * z) - 1) := by
    have hp := Nat.mul_pos (Nat.two_pow_pos (l - 1)) (show 0 < 3 * z by omega)
    have hh : 2 ^ l * (3 * z) = 2 * (2 ^ (l - 1) * (3 * z)) := by
      calc
        _ = 2 ^ ((l - 1) + 1) * (3 * z) := congrArg (fun t => 2 ^ t * (3 * z)) (by omega)
        _ = _ := by rw [Nat.pow_succ]; ac_rfl
    rw [hh]; omega
  have hs := (MinimumClockBarrier.odd_block (l - 1) 0 (3 * z) (by omega)).1
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hs
  have hfinal : 3 ^ (l - 1) * (3 * z) - 1 = 4 * h := by
    have hh : 3 ^ (l - 1) * (3 * z) = 3 ^ l * z := by
      calc
        _ = 3 ^ ((l - 1) + 1) * z := by rw [Nat.pow_succ]; ac_rfl
        _ = _ := congrArg (fun t => 3 ^ t * z) (by omega)
    rw [hh, he]; omega
  constructor
  · rw [show 2 * l + 4 = 1 + (2 * l + 3) by omega, iterate_add 1, hbridge.1, hn]
    omega
  · rw [show 2 * l + 4 = 3 + (1 + (2 * (l - 1) + 2)) by omega,
      iterate_add 3, hbridge.2, htwo, iterate_add 1]
    have hstep : iterate 1 (2 * (2 ^ (l - 1) * (3 * z) - 1)) =
        2 ^ (l - 1) * (3 * z) - 1 := by simp only [iterate, MinimumFirstTarget.even_step]
    rw [hstep, iterate_add (2 * (l - 1)) 2, hs, hfinal]
    have hh : 4 * h = 2 * (2 * h) := by omega
    simp only [hh, iterate, MinimumFirstTarget.even_step]

#print axioms adjacent_bridges
#print axioms odd_exit_meeting
#print axioms opposite_exit_meeting
#print axioms full_odd_exit_meeting
#print axioms odd_exit_not_least
#print axioms pure_residue_lift
#print axioms binary_target
#print axioms pure_odd_exit_lift
#print axioms weighted_odd_exit_lift
#print axioms exit_growth_bound
#print axioms companion_above_source
#print axioms exit_units_odd
#print axioms realization_windows
#print axioms build_odd_escape
#print axioms pure_odd_escape
#print axioms weighted_odd_escape
#print axioms full_opposite_meeting
#print axioms odd_exit_dichotomy
#print axioms least_odd_exit_constraint
#print axioms opposite_exit_profiles

end MinimumFiveOddExit
