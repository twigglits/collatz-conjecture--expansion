/- A contracting adjacent pair gives later mergers in the d=3 mod4 branch. -/
import MinimumFiveInverseCone

namespace MinimumFiveEvenExit
open OrdinaryCollatz MinimumSeventeenTransition MinimumSeventeenFourth
open MinimumSeventeenPhase MinimumSeventeenSeparation MinimumFiveTransition
open MinimumFiveOddExit MinimumFivePredecessor MinimumRootPredecessors

attribute [local irreducible] OrdinaryCollatz.iterate

theorem adjacent_even_step (q : Nat) :
    iterate 3 (4 * q + 2) = 3 * q + 2 ∧ iterate 3 (4 * q + 1) = 3 * q + 1 := by
  have n0 : C (4 * q + 2) = 2 * q + 1 := by unfold C; split <;> omega
  have n1 : C (2 * q + 1) = 6 * q + 4 := by unfold C; split <;> omega
  have n2 : C (6 * q + 4) = 3 * q + 2 := by unfold C; split <;> omega
  have s0 : C (4 * q + 1) = 12 * q + 4 := by unfold C; split <;> omega
  have s1 : C (12 * q + 4) = 6 * q + 2 := by unfold C; split <;> omega
  have s2 : C (6 * q + 2) = 3 * q + 1 := by unfold C; split <;> omega
  constructor <;> simp only [iterate, n0, n1, n2, s0, s1, s2]

theorem adjacent_even_blocks (t q : Nat) :
    iterate (3 * t) (4 ^ t * q + 2) = 3 ^ t * q + 2 ∧
    iterate (3 * t) (4 ^ t * q + 1) = 3 ^ t * q + 1 := by
  induction t generalizing q with
  | zero => simp [iterate]
  | succ t ih =>
    have h0 := adjacent_even_step (4 ^ t * q)
    have h1 := ih (3 * q)
    have hs : 4 ^ (t + 1) * q = 4 * (4 ^ t * q) := by rw [Nat.pow_succ]; ac_rfl
    have he : 3 * (t + 1) = 3 + 3 * t := by omega
    have hm : 3 * (4 ^ t * q) = 4 ^ t * (3 * q) := by ac_rfl
    have ht : 3 ^ (t + 1) * q = 3 ^ t * (3 * q) := by rw [Nat.pow_succ]; ac_rfl
    constructor
    · rw [he, hs, iterate_add 3, h0.1, hm, h1.1, ht]
    · rw [he, hs, iterate_add 3, h0.2, hm, h1.2, ht]

theorem even_bridges (t z d : Nat) (hd : d = 3 + 2 * 4 ^ t * z) :
    iterate (1 + 3 * t) (3 * d - 5) = 2 + 3 ^ (t + 1) * z ∧
    iterate (3 + 3 * t) (2 * d - 5) = 1 + 3 ^ (t + 1) * z := by
  have h0 := adjacent_bridges 0 (1 + 4 ^ t * z) d (by omega)
    (by rw [hd]; grind)
  have hm : 4 ^ t * (3 * z) = 3 * (4 ^ t * z) := by ac_rfl
  have hn : 2 ^ 0 * (3 * (1 + 4 ^ t * z)) - 1 = 4 ^ t * (3 * z) + 2 := by rw [hm]; omega
  have hs : 2 ^ 0 * (3 * (1 + 4 ^ t * z)) - 2 = 4 ^ t * (3 * z) + 1 := by rw [hm]; omega
  have he : 3 ^ t * (3 * z) = 3 ^ (t + 1) * z := by rw [Nat.pow_succ]; ac_rfl
  have h1 := adjacent_even_blocks t (3 * z)
  constructor
  · rw [iterate_add 1, h0.1, hn, h1.1, he]; omega
  · rw [iterate_add 3, h0.2, hs, h1.2, he]; omega

theorem even_exit_meeting (t z l y d : Nat) (hl : 0 < l) (hy : 0 < y)
    (hd : d = 3 + 2 * 4 ^ t * z) (he : 1 + 3 ^ t * z = 2 ^ l * y)
    (hg : (3 ^ (l + 1) * y) % 4 = 1) :
    iterate (3 * t + 2 * l + 5) (2 * d - 5) =
      iterate (3 * t + 2 * l + 3) (3 * d - 5) := by
  have hb := even_bridges t z d hd
  have ha : 2 + 3 ^ (t + 1) * z = 2 ^ l * (3 * y) - 1 := by
    have hx : 3 ^ (t + 1) * z = 3 * (3 ^ t * z) := by rw [Nat.pow_succ]; ac_rfl
    have hyx : 2 ^ l * (3 * y) = 3 * (2 ^ l * y) := by ac_rfl
    rw [hx, hyx]; omega
  have hs : 1 + 3 ^ (t + 1) * z = 2 ^ l * (3 * y) - 2 := by omega
  have hguard : (3 ^ l * (3 * y)) % 4 = 1 := by
    rw [Nat.pow_succ] at hg
    simpa only [Nat.mul_assoc] using hg
  rw [show 3 * t + 2 * l + 5 = (3 + 3 * t) + (2 * l + 2) by omega,
    show 3 * t + 2 * l + 3 = (1 + 3 * t) + (2 * l + 2) by omega,
    iterate_add (3 + 3 * t), iterate_add (1 + 3 * t), hb.1, hb.2, ha, hs]
  exact MinimumLadderCover.adjacent_odd_block l (3 * y) hl (by omega) hguard

theorem even_opposite_profiles (t z l y d h : Nat) (hl : 0 < l) (hy : 0 < y)
    (hd : d = 3 + 2 * 4 ^ t * z) (he : 1 + 3 ^ t * z = 2 ^ l * y)
    (hh : 3 ^ l * y = 4 * h + 1) :
    iterate (3 * t + 2 * l + 4) (3 * d - 5) = 9 * h + 2 ∧
    iterate (3 * t + 2 * l + 4) (2 * d - 5) = h := by
  let d' := 1 + 2 ^ (l + 1) * y
  have hp := opposite_exit_profiles l y d' h hl hy rfl hh
  have hv := adjacent_bridges l y d' hy rfl
  rw [show 2 * l + 4 = 1 + (2 * l + 3) by omega, iterate_add 1, hv.1] at hp
  have hs := hp.2
  rw [show 1 + (2 * l + 3) = 3 + (2 * l + 1) by omega, iterate_add 3, hv.2] at hs
  have hb := even_bridges t z d hd
  have ha : 2 + 3 ^ (t + 1) * z = 2 ^ l * (3 * y) - 1 := by
    have hx : 3 ^ (t + 1) * z = 3 * (3 ^ t * z) := by rw [Nat.pow_succ]; ac_rfl
    have hyx : 2 ^ l * (3 * y) = 3 * (2 ^ l * y) := by ac_rfl
    rw [hx, hyx]; omega
  have hs' : 1 + 3 ^ (t + 1) * z = 2 ^ l * (3 * y) - 2 := by omega
  constructor
  · rw [show 3 * t + 2 * l + 4 = (1 + 3 * t) + (2 * l + 3) by omega,
      iterate_add (1 + 3 * t), hb.1, ha]
    exact hp.1
  · rw [show 3 * t + 2 * l + 4 = (3 + 3 * t) + (2 * l + 1) by omega,
      iterate_add (3 + 3 * t), hb.2, hs']
    exact hs

theorem fourth_third_profile (R w r u j q k v : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    iterate (4 * R + 125 + 18 * r + 18 * j + 5 * k) (fourthSource R w) =
      2 * thirdScalar k v - 5 := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hs := fourth_profile R w r u hr hw hu hX
  have hp := (secondary_profiles (scalar r u) j q ha hq hT).2
  have ht := (third_profiles (secondaryScalar j q) k v hv hB).2
  rw [show 4 * R + 125 + 18 * r + 18 * j + 5 * k =
      (4 * R + 100 + 18 * r) + ((21 + 18 * j) + (4 + 5 * k)) by omega,
    iterate_add (4 * R + 100 + 18 * r), hs, iterate_add (21 + 18 * j), hp, ht]

theorem full_even_exit_meeting (R w r u j q k v t z l y : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hy : 0 < y)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 3 + 2 * 4 ^ t * z)
    (he : 1 + 3 ^ t * z = 2 ^ l * y) (hg : (3 ^ (l + 1) * y) % 4 = 1) :
    iterate (4 * R + 130 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (fourthSource R w) =
      iterate (5 * R + 119 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (mainSource R w) := by
  have hn := main_third_profile R w r u j q k v hw hu hq hv hX hT hB
  have hs := fourth_third_profile R w r u j q k v hr hw hu hq hv hX hT hB
  rw [show 4 * R + 130 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l =
      (4 * R + 125 + 18 * r + 18 * j + 5 * k) + (3 * t + 2 * l + 5) by omega,
    show 5 * R + 119 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l =
      (5 * R + 116 + 18 * r + 18 * j + 5 * k) + (3 * t + 2 * l + 3) by omega,
    iterate_add (4 * R + 125 + 18 * r + 18 * j + 5 * k),
    iterate_add (5 * R + 116 + 18 * r + 18 * j + 5 * k), hs, hn]
  exact even_exit_meeting t z l y _ hl hy hd he hg

theorem even_exit_not_least (R w r u j q k v t z l y : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hy : 0 < y)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 3 + 2 * 4 ^ t * z)
    (he : 1 + 3 ^ t * z = 2 ^ l * y) (hg : (3 ^ (l + 1) * y) % 4 = 1) :
    ¬ LeastCounterexample (mainSource R w) := by
  intro hN
  have hb := fourth_bounds R w hR hw
  have hm := full_even_exit_meeting R w r u j q k v t z l y hr hw hu hq hv hl hy hX hT hB hd he hg
  have hle := least_coalescing_predecessor hN hb.1 hm
  omega

theorem even_branch_residue (t z d : Nat) (ht : 0 < t)
    (hd : d = 3 + 2 * 4 ^ t * z) : d % 8 = 3 := by
  have h4 : 4 ^ t = 4 * 4 ^ (t - 1) := by
    calc
      _ = 4 ^ ((t - 1) + 1) := congrArg (4 ^ ·) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ac_rfl
  have he : d = 3 + 8 * (4 ^ (t - 1) * z) := by rw [hd, h4]; grind
  omega

theorem exit_residue (t l g : Nat) (hl : 0 < l) (hg : g = 1 ∨ g = 3) :
    ∃ z0 y0, 0 < z0 ∧ z0 < 2 ^ (l + 2) ∧ z0 % 2 = 1 ∧
      0 < y0 ∧ y0 < 4 ∧ y0 % 2 = 1 ∧
      (1 + 3 ^ t * z0) % (2 ^ (l + 2)) = 2 ^ l * y0 ∧
      (3 ^ (l + 1) * y0) % 4 = g := by
  have hc : (3 ^ (l + 1)) % 2 = 1 := by rw [Nat.pow_mod]; simp
  obtain ⟨y0, hy0, hy4, hyo, hyg⟩ := binary_target 1 (3 ^ (l + 1)) g hc (by omega) (by omega)
  let D := 2 ^ l
  let V := 2 ^ (l + 2)
  have hD : 2 ≤ D := Nat.pow_le_pow_right (by decide : 0 < 2) hl
  have hV : V = 4 * D := by dsimp [V, D]; rw [Nat.pow_add]; omega
  have hDe : D % 2 = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hl)
  have hprod : 0 < D * y0 := Nat.mul_pos (by omega) hy0
  have hpmod : (D * y0) % 2 = 0 := by simp [Nat.mul_mod, hDe]
  have hplt : D * y0 < V := by
    have hh := Nat.mul_lt_mul_of_pos_left hy4 (by omega : 0 < D)
    rw [hV]; omega
  have h3 : (3 ^ t) % 2 = 1 := by rw [Nat.pow_mod]; simp
  obtain ⟨z0, hz0, hzlt, hzo, hzm⟩ := binary_target (l + 1) (3 ^ t) (D * y0 - 1)
    h3 (by omega) (by change D * y0 - 1 < V; omega)
  have hm : (1 + 3 ^ t * z0) % V = D * y0 := by
    change (3 ^ t * z0) % V = D * y0 - 1 at hzm
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by rw [hV]; omega : 1 < V), hzm]
    rw [show 1 + (D * y0 - 1) = D * y0 by omega, Nat.mod_eq_of_lt hplt]
  exact ⟨z0, y0, hz0, hzlt, hzo, hy0, hy4, hyo, hm, hyg⟩

theorem pure_even_exit_lift (r j k t l g B : Nat) (ht : 0 < t) (hl : 0 < l)
    (hg : g = 1 ∨ g = 3) :
    ∃ R u q v z y, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧
      0 < z ∧ z % 2 = 1 ∧ 0 < y ∧ y % 2 = 1 ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v = 3 + 2 * 4 ^ t * z ∧
      1 + 3 ^ t * z = 2 ^ l * y ∧ (3 ^ (l + 1) * y) % 4 = g := by
  obtain ⟨z0, y0, hz0, hzlt, hzo, hy0, hylt, hyo, hmod, hguard⟩ := exit_residue t l g hl hg
  let A := 2 * 4 ^ t
  let V := 2 ^ (l + 2)
  let M := 2 ^ (2 * t + l + 3)
  let target := 3 + A * z0
  have hA : 8 ≤ A := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 4) ht
    dsimp [A]; omega
  have hM : M = A * V := by
    dsimp [M, A, V]
    rw [show 2 * t + l + 3 = (2 * t + 1) + (l + 2) by omega, Nat.pow_add,
      Nat.pow_succ, Nat.pow_mul]
    ac_rfl
  have hAe : A % 2 = 0 := by dsimp [A]; omega
  have hto : target % 2 = 1 := by simp [target, Nat.add_mod, Nat.mul_mod, hAe]
  have htl : target < M := by
    have hh := Nat.mul_le_mul_left A (show z0 + 1 ≤ V by omega)
    rw [Nat.mul_add, Nat.mul_one] at hh
    dsimp [target]; rw [hM]; omega
  have hf : (9 ^ (k + 1)) % 2 = 1 := by rw [Nat.pow_mod]; simp
  obtain ⟨eps, heps, helt, _, heq⟩ := binary_target (2 * t + l + 2) (9 ^ (k + 1)) target hf hto htl
  obtain ⟨R, u, q, v, hR, hR14, hu, hq, hv, hX, hT, hB, hvmod⟩ :=
    pure_residue_lift r j k (2 * t + l + 2) eps B heps helt
  have hdmod : thirdScalar k v % M = target := by
    change (9 ^ (k + 1) * v) % M = target
    change v % M = eps at hvmod
    change (9 ^ (k + 1) * eps) % M = target at heq
    change eps < M at helt
    rw [Nat.mul_mod, hvmod]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt helt] at heq
    exact heq
  let z := V * (thirdScalar k v / M) + z0
  have hV4 : V = 4 * 2 ^ l := by dsimp [V]; rw [Nat.pow_add]; omega
  have hzm : z % V = z0 := by
    dsimp [z]
    simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt hzlt
  have hz : 0 < z := by dsimp [z]; omega
  have hze : z % 2 = 1 := by simp [z, hV4, Nat.add_mod, Nat.mul_mod, hzo]
  have hd : thirdScalar k v = 3 + A * z := by
    have hh := Nat.mod_add_div (thirdScalar k v) M
    rw [hdmod, hM] at hh
    dsimp [target, z] at *
    grind
  have hm : (1 + 3 ^ t * z) % V = 2 ^ l * y0 := by
    change (1 + 3 ^ t * z0) % V = 2 ^ l * y0 at hmod
    simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, hzm, Nat.mod_eq_of_lt hzlt] using hmod
  let y := 4 * ((1 + 3 ^ t * z) / V) + y0
  have hy : 0 < y := by dsimp [y]; omega
  have hye : y % 2 = 1 := by dsimp [y]; omega
  have he : 1 + 3 ^ t * z = 2 ^ l * y := by
    have hh := Nat.mod_add_div (1 + 3 ^ t * z) V
    rw [hm, hV4] at hh
    dsimp [y]
    grind
  have hy4 : y % 4 = y0 := by dsimp [y]; omega
  have hg' : (3 ^ (l + 1) * y) % 4 = g := by
    rw [Nat.mul_mod, hy4]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt hylt] at hguard
    exact hguard
  exact ⟨R, u, q, v, z, y, hR, hR14, hu, hq, hv, hz, hze, hy, hye, hX, hT, hB, hd, he, hg'⟩

theorem weighted_even_exit_lift (R r j k t l g B : Nat) (ht : 0 < t) (hl : 0 < l)
    (hg : g = 1 ∨ g = 3) :
    ∃ w u q v z y, B < w ∧ 0 < u ∧ 0 < q ∧ 0 < v ∧
      0 < z ∧ z % 2 = 1 ∧ 0 < y ∧ y % 2 = 1 ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
      thirdScalar k v = 3 + 2 * 4 ^ t * z ∧
      1 + 3 ^ t * z = 2 ^ l * y ∧ (3 ^ (l + 1) * y) % 4 = g := by
  obtain ⟨S, u, q, v, z, y, hS, _, hu, hq, hv, hz, hzo, hy, hyo, hX, hT, hB, hd, he, hg⟩ :=
    pure_even_exit_lift r j k t l g (R + B + 1) ht hl hg
  refine ⟨9 ^ (S - R), u, q, v, z, y, ?_, hu, hq, hv, hz, hzo, hy, hyo, ?_, hT, hB, hd, he, hg⟩
  · exact Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  · rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX

def EvenRealization (R w r j k t l g : Nat) : Prop :=
  ∃ u q v z y, 0 < u ∧ 0 < q ∧ 0 < v ∧ 0 < z ∧ z % 2 = 1 ∧ 0 < y ∧ y % 2 = 1 ∧
    9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
    9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
    secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
    thirdScalar k v = 3 + 2 * 4 ^ t * z ∧
    1 + 3 ^ t * z = 2 ^ l * y ∧ (3 ^ (l + 1) * y) % 4 = g

def EvenEscape (R w r j k t l : Nat) : Prop :=
  EvenRealization R w r j k t l 1 ∧ ¬ LeastCounterexample (mainSource R w) ∧
    iterate (4 * R + 130 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (fourthSource R w) =
      iterate (5 * R + 119 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (mainSource R w)

theorem build_even_escape (R w r j k t l : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hl : 0 < l) (h : EvenRealization R w r j k t l 1) :
    EvenEscape R w r j k t l := by
  refine ⟨h, ?_, ?_⟩
  · obtain ⟨u, q, v, z, y, hu, hq, hv, _, _, hy, _, hX, hT, hB, hd, he, hg⟩ := h
    exact even_exit_not_least R w r u j q k v t z l y hR hr hw hu hq hv hl hy hX hT hB hd he hg
  · obtain ⟨u, q, v, z, y, hu, hq, hv, _, _, hy, _, hX, hT, hB, hd, he, hg⟩ := h
    exact full_even_exit_meeting R w r u j q k v t z l y hr hw hu hq hv hl hy hX hT hB hd he hg

theorem pure_even_escape (r j k t l B : Nat) (hr : 5 ≤ r) (ht : 0 < t) (hl : 0 < l) :
    ∃ R, B < R ∧ 14 ≤ R ∧ EvenEscape R 1 r j k t l := by
  obtain ⟨R, u, q, v, z, y, hR, hR14, hu, hq, hv, hz, hzo, hy, hyo, hX, hT, hB, hd, he, hg⟩ :=
    pure_even_exit_lift r j k t l 1 B ht hl (Or.inl rfl)
  have hh : EvenRealization R 1 r j k t l 1 :=
    ⟨u, q, v, z, y, hu, hq, hv, hz, hzo, hy, hyo, by simpa using hX, hT, hB, hd, he, hg⟩
  exact ⟨R, hR, hR14, build_even_escape R 1 r j k t l hR14 hr (by decide) hl hh⟩

theorem weighted_even_escape (R r j k t l B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (ht : 0 < t) (hl : 0 < l) : ∃ w, B < w ∧ EvenEscape R w r j k t l := by
  obtain ⟨w, u, q, v, z, y, hw, hu, hq, hv, hz, hzo, hy, hyo, hX, hT, hB, hd, he, hg⟩ :=
    weighted_even_exit_lift R r j k t l 1 B ht hl (Or.inl rfl)
  have hh : EvenRealization R w r j k t l 1 :=
    ⟨u, q, v, z, y, hu, hq, hv, hz, hzo, hy, hyo, hX, hT, hB, hd, he, hg⟩
  exact ⟨w, hw, build_even_escape R w r j k t l hR hr (by omega) hl hh⟩

theorem realization_windows (H R w r j k t l g : Nat) (hr : 5 ≤ r) (hw : 0 < w)
    (hHj : H + 13 ≤ 9 + 11 * j) (hHk : H + 6 ≤ 3 * k + 4)
    (he : EvenRealization R w r j k t l g) :
    FourSeparated H R w r ∧ SecondarySeparated H R w r j := by
  obtain ⟨u, q, v, _, _, hu, hq, _, _, _, _, _, hX, hT, hB, _⟩ := he
  have hdiv : 2 ^ (H + 13) ∣ 9 * scalar r u + 1 :=
    Nat.dvd_trans (Nat.pow_dvd_pow 2 hHj) ⟨q, hT⟩
  exact ⟨four_source_separation H R w r u hr hw hu hX hdiv,
    third_window_separation H R w r u j q k v hr hw hu hq hHk hX hT hB⟩

theorem realized_inverse_obstruction (R w r j k t l g : Nat) (hR : 26 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (he : EvenRealization R w r j k t l g) :
    ∃ H, iterate (5 * R + 117 + 18 * r + 18 * j + 5 * k) (mainSource R w) = H ∧
      ∀ e o p, MinimumReturnLadder.Backtrack e o H p → e ≤ k → mainSource R w < p := by
  obtain ⟨u, q, v, z, _, hu, hq, hv, _, _, _, _, hX, hT, hB, hd, _⟩ := he
  let H := 2 + 3 * (4 ^ t * z)
  have hH : 2 * H + 5 = 3 * thirdScalar k v := by rw [hd]; dsimp [H]; grind
  refine ⟨H, MinimumFiveInverseCone.half_third_profile R w r u j q k v H hw hu hq hv hX hT hB hH, ?_⟩
  intro e o p hp he
  exact MinimumFiveInverseCone.weighted_half_third_obstruction R w r u j q k v hR hr hw hv hX hT hB hH hp he

theorem even_exit_dichotomy (t z d : Nat) (ht : 0 < t) (hzo : z % 2 = 1)
    (hd : d = 3 + 2 * 4 ^ t * z) :
    d % 8 = 3 ∧ ∃ l y, 0 < l ∧ 0 < y ∧ y % 2 = 1 ∧ 1 + 3 ^ t * z = 2 ^ l * y ∧
      (((3 ^ (l + 1) * y) % 4 = 1 ∧
        iterate (3 * t + 2 * l + 5) (2 * d - 5) = iterate (3 * t + 2 * l + 3) (3 * d - 5)) ∨
       ((3 ^ (l + 1) * y) % 4 = 3 ∧ ∃ h, 3 ^ l * y = 4 * h + 1 ∧
        iterate (3 * t + 2 * l + 4) (3 * d - 5) = 9 * h + 2 ∧
        iterate (3 * t + 2 * l + 4) (2 * d - 5) = h)) := by
  obtain ⟨l, y, hy, hyo, he⟩ := MinimumLadderBlockExit.odd_factorization (1 + 3 ^ t * z) (by omega)
  have heven : (1 + 3 ^ t * z) % 2 = 0 := by simp [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hzo]
  have hl : 0 < l := by
    by_cases h0 : l = 0
    · rw [h0] at he; simp only [Nat.pow_zero, Nat.one_mul] at he; omega
    · omega
  have hodd : (3 ^ (l + 1) * y) % 2 = 1 := by simp [Nat.mul_mod, Nat.pow_mod, hyo]
  refine ⟨even_branch_residue t z d ht hd, l, y, hl, hy, hyo, he, ?_⟩
  have hg : (3 ^ (l + 1) * y) % 4 = 1 ∨ (3 ^ (l + 1) * y) % 4 = 3 := by omega
  rcases hg with hg | hg
  · exact Or.inl ⟨hg, even_exit_meeting t z l y d hl hy hd he hg⟩
  · have hprod : 3 ^ (l + 1) * y = 3 * (3 ^ l * y) := by rw [Nat.pow_succ]; ac_rfl
    have hmod : (3 ^ l * y) % 4 = 1 := by rw [hprod] at hg; omega
    let h := (3 ^ l * y) / 4
    have hh : 3 ^ l * y = 4 * h + 1 := by dsimp [h]; omega
    have hp := even_opposite_profiles t z l y d h hl hy hd he hh
    exact Or.inr ⟨hg, h, hh, hp.1, hp.2⟩

theorem full_even_opposite_profiles (R w r u j q k v t z l y h : Nat) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hl : 0 < l) (hy : 0 < y)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hd : thirdScalar k v = 3 + 2 * 4 ^ t * z)
    (he : 1 + 3 ^ t * z = 2 ^ l * y) (hh : 3 ^ l * y = 4 * h + 1) :
    iterate (5 * R + 120 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (mainSource R w) = 9 * h + 2 ∧
    iterate (4 * R + 129 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l) (fourthSource R w) = h := by
  have hn := main_third_profile R w r u j q k v hw hu hq hv hX hT hB
  have hs := fourth_third_profile R w r u j q k v hr hw hu hq hv hX hT hB
  have hp := even_opposite_profiles t z l y _ h hl hy hd he hh
  constructor
  · rw [show 5 * R + 120 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l =
      (5 * R + 116 + 18 * r + 18 * j + 5 * k) + (3 * t + 2 * l + 4) by omega,
      iterate_add (5 * R + 116 + 18 * r + 18 * j + 5 * k), hn, hp.1]
  · rw [show 4 * R + 129 + 18 * r + 18 * j + 5 * k + 3 * t + 2 * l =
      (4 * R + 125 + 18 * r + 18 * j + 5 * k) + (3 * t + 2 * l + 4) by omega,
      iterate_add (4 * R + 125 + 18 * r + 18 * j + 5 * k), hs, hp.2]

theorem pure_later_escape (r j k t l B : Nat) (hr : 5 ≤ r) (ht : 0 < t) (hl : 0 < l) :
    ∃ R H, B < R ∧ 36 ≤ R ∧ EvenEscape R 1 r j k t l ∧
      iterate (5 * R + 117 + 18 * r + 18 * j + 5 * k) (mainSource R 1) = H ∧
      ∀ e o p, MinimumReturnLadder.Backtrack e o H p → e ≤ k → mainSource R 1 < p := by
  obtain ⟨R, hR, _, hE⟩ := pure_even_escape r j k t l B hr ht hl
  obtain ⟨u, _, _, _, _, hu, _, _, _, _, _, _, hX, _⟩ := hE.1
  have hR36 := pure_exponent_bound R r u hr hu (by simpa using hX)
  obtain ⟨H, hp, hi⟩ := realized_inverse_obstruction R 1 r j k t l 1 (by omega) hr (by decide) hE.1
  exact ⟨R, H, hR, hR36, hE, hp, hi⟩

#print axioms adjacent_even_step
#print axioms adjacent_even_blocks
#print axioms even_bridges
#print axioms even_exit_meeting
#print axioms even_opposite_profiles
#print axioms fourth_third_profile
#print axioms full_even_exit_meeting
#print axioms even_exit_not_least
#print axioms even_branch_residue
#print axioms exit_residue
#print axioms pure_even_exit_lift
#print axioms weighted_even_exit_lift
#print axioms build_even_escape
#print axioms pure_even_escape
#print axioms weighted_even_escape
#print axioms realization_windows
#print axioms realized_inverse_obstruction
#print axioms even_exit_dichotomy
#print axioms full_even_opposite_profiles
#print axioms pure_later_escape

end MinimumFiveEvenExit
