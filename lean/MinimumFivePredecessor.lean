/- An immediate predecessor gives an exact weighted-source size boundary.
   Pure sources and larger inverse budgets remain unresolved. -/
import MinimumFiveOddExit

namespace MinimumFivePredecessor
open OrdinaryCollatz MinimumSeventeenTransition MinimumSeventeenFourth
open MinimumSeventeenPhase MinimumSeventeenSeparation MinimumFiveTransition
open MinimumFiveOddExit MinimumRootPredecessors MinimumReturnLadder

attribute [local irreducible] OrdinaryCollatz.iterate

def SmallRegion (s t : Nat) : Prop :=
  (s ≤ 6 ∧ t ≤ 19) ∨ (s ≤ 8 ∧ t ≤ 18) ∨ (s ≤ 10 ∧ t ≤ 17) ∨
  (s ≤ 11 ∧ t ≤ 16) ∨ (s ≤ 13 ∧ t ≤ 15) ∨ (s ≤ 15 ∧ t ≤ 14)

instance (s t : Nat) : Decidable (SmallRegion s t) := by unfold SmallRegion; infer_instance

def coefficient (s t : Nat) : Nat := 3 ^ (43 + 7 * s + 2 * t)
def scale (s t : Nat) : Nat := 2 ^ (72 + 11 * s + 3 * t)
def denominator (r j k : Nat) : Nat := 2 ^ (70 + 11 * (r + j) + 3 * k)
def multiplier (r j k : Nat) : Nat := 3 ^ (43 + 7 * (r + j) + 2 * k)
def padding (r j k : Nat) : Nat :=
  7 * multiplier r j k + 9 ^ (k + 1) * 2 ^ (57 + 11 * r) *
    (3 ^ (6 + 7 * j) - 2 ^ (9 + 11 * j))

theorem immediate_predecessor (k v : Nat) (hv : 0 < v) (hvo : v % 2 = 1) :
    0 < thirdScalar k v - 2 ∧ C (thirdScalar k v - 2) = 3 * thirdScalar k v - 5 := by
  have hp : 9 ≤ thirdScalar k v := by
    have h9 : 9 ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by decide : 0 < 9) (by omega : 1 ≤ k + 1)
    exact Nat.le_trans h9 (Nat.le_mul_of_pos_right _ hv)
  have ho : thirdScalar k v % 2 = 1 := by simp [thirdScalar, Nat.mul_mod, Nat.pow_mod, hvo]
  refine ⟨by omega, ?_⟩
  unfold C
  split <;> omega

theorem main_third_profile (R w r u j q k v : Nat)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    iterate (5 * R + 116 + 18 * r + 18 * j + 5 * k) (mainSource R w) =
      3 * thirdScalar k v - 5 := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hn := (three_sources R w r u hw hu hX).1
  have hp := (secondary_profiles (scalar r u) j q ha hq hT).1
  have ht := (third_profiles (secondaryScalar j q) k v hv hB).1
  rw [show 5 * R + 116 + 18 * r + 18 * j + 5 * k =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + (9 + 5 * k)) by omega,
    iterate_add (5 * R + 91 + 18 * r), hn, iterate_add (16 + 18 * j), hp, ht]

theorem scaled_coordinates (R w r u j q k v : Nat)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    denominator r j k * thirdScalar k v = multiplier r j k * (9 ^ R * w) + padding r j k := by
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
  have hsub : c * (A * u) + (c - E) = E * (T * v) := by omega
  have hmul := congrArg (D * ·) hsub
  have hlhs : D * (c * (A * u)) = c * A * (9 ^ R * w + 7) := by
    calc
      _ = c * A * (D * u) := by ac_rfl
      _ = _ := by rw [← hX]
  rw [Nat.mul_add, hlhs] at hmul
  have hden : denominator r j k = D * E * T := by
    unfold denominator
    rw [show 70 + 11 * (r + j) + 3 * k = (57 + 11 * r) + (9 + 11 * j) + (3 * k + 4) by omega,
      Nat.pow_add, Nat.pow_add]
  have hfac : multiplier r j k = f * c * A := by
    dsimp [multiplier, f, c, A]
    rw [show 43 + 7 * (r + j) + 2 * k = 2 * (k + 1) + (6 + 7 * j) + (35 + 7 * r) by omega,
      Nat.pow_add, Nat.pow_add, Nat.pow_mul]
  change denominator r j k * (f * v) = multiplier r j k * (9 ^ R * w) +
    (7 * multiplier r j k + f * D * (c - E))
  rw [hden, hfac]
  calc
    _ = f * (D * (E * (T * v))) := by ac_rfl
    _ = f * (c * A * (9 ^ R * w + 7) + D * (c - E)) := congrArg (f * ·) hmul.symm
    _ = _ := by grind

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem finite_size_boundary :
    (∀ s : Fin 16, ∀ t : Fin 20, 5 ≤ s.val → 14 ≤ t.val →
      (SmallRegion s.val t.val → 1000 * coefficient s.val t.val ≤ 993 * scale s.val t.val) ∧
      (¬ SmallRegion s.val t.val → scale s.val t.val ≤ coefficient s.val t.val)) ∧
    scale 16 14 ≤ coefficient 16 14 ∧ scale 5 20 ≤ coefficient 5 20 := by
  decide +kernel

theorem growth_transport (s t a b : Nat) (h : scale s t ≤ coefficient s t) :
    scale (s + a) (t + b) ≤ coefficient (s + a) (t + b) := by
  have ha := Nat.pow_le_pow_left (by decide : 2 ^ 11 ≤ 3 ^ 7) a
  have hb := Nat.pow_le_pow_left (by decide : 2 ^ 3 ≤ 3 ^ 2) b
  have hm := Nat.mul_le_mul (Nat.mul_le_mul h ha) hb
  unfold scale coefficient at *
  rw [show 72 + 11 * (s + a) + 3 * (t + b) = (72 + 11 * s + 3 * t) + 11 * a + 3 * b by omega,
    show 43 + 7 * (s + a) + 2 * (t + b) = (43 + 7 * s + 2 * t) + 7 * a + 2 * b by omega]
  simpa only [Nat.pow_add, Nat.pow_mul] using hm

theorem slope_boundary (s t : Nat) (hs : 5 ≤ s) (ht : 14 ≤ t) :
    (SmallRegion s t → 1000 * coefficient s t ≤ 993 * scale s t) ∧
    (¬ SmallRegion s t → scale s t ≤ coefficient s t) := by
  constructor
  · intro h
    have hbounds : s < 16 ∧ t < 20 := by unfold SmallRegion at h; omega
    exact (finite_size_boundary.1 ⟨s, hbounds.1⟩ ⟨t, hbounds.2⟩ hs ht).1 h
  · intro h
    by_cases hs16 : 16 ≤ s
    · have hh := growth_transport 16 14 (s - 16) (t - 14) finite_size_boundary.2.1
      simpa only [show 16 + (s - 16) = s by omega, show 14 + (t - 14) = t by omega] using hh
    · by_cases ht20 : 20 ≤ t
      · have hh := growth_transport 5 20 (s - 5) (t - 20) finite_size_boundary.2.2
        simpa only [show 5 + (s - 5) = s by omega, show 20 + (t - 20) = t by omega] using hh
      · exact (finite_size_boundary.1 ⟨s, by omega⟩ ⟨t, by omega⟩ hs ht).2 h

theorem denominator_bound (r : Nat) (hr : 5 ≤ r) :
    2 ^ (57 + 11 * r) ≤ 3 * 3 ^ (35 + 7 * r) := by
  have h := Nat.mul_le_mul (by decide : 2 ^ 112 ≤ 3 ^ 71)
    (Nat.pow_le_pow_left (by decide : 2 ^ 11 ≤ 3 ^ 7) (r - 5))
  have h2 : 112 + 11 * (r - 5) = 57 + 11 * r := by omega
  have h3 : 71 + 7 * (r - 5) = (35 + 7 * r) + 1 := by omega
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add, h2, h3, Nat.pow_succ] at h
  omega

theorem padding_bound (r j k : Nat) (hr : 5 ≤ r) : padding r j k ≤ 10 * multiplier r j k := by
  have hD := denominator_bound r hr
  have h0 : 3 ^ (6 + 7 * j) - 2 ^ (9 + 11 * j) ≤ 3 ^ (6 + 7 * j) := Nat.sub_le _ _
  have hm := Nat.mul_le_mul hD h0
  have hf := Nat.mul_le_mul_left (9 ^ (k + 1)) hm
  have hfac : multiplier r j k = 9 ^ (k + 1) * 3 ^ (6 + 7 * j) * 3 ^ (35 + 7 * r) := by
    unfold multiplier
    rw [show 43 + 7 * (r + j) + 2 * k = 2 * (k + 1) + (6 + 7 * j) + (35 + 7 * r) by omega,
      Nat.pow_add, Nat.pow_add, Nat.pow_mul]
  have hh : 9 ^ (k + 1) * (3 * 3 ^ (35 + 7 * r) * 3 ^ (6 + 7 * j)) =
      3 * multiplier r j k := by rw [hfac]; ac_rfl
  rw [hh] at hf
  unfold padding
  have he : 9 ^ (k + 1) * 2 ^ (57 + 11 * r) * (3 ^ (6 + 7 * j) - 2 ^ (9 + 11 * j)) =
      9 ^ (k + 1) * (2 ^ (57 + 11 * r) * (3 ^ (6 + 7 * j) - 2 ^ (9 + 11 * j))) := by ac_rfl
  rw [he]
  omega

theorem normalized_scales (R r j k : Nat) :
    multiplier r j k * 9 ^ R = coefficient (r + j) (R + k) ∧
    denominator r j k * (4 * 8 ^ R) = scale (r + j) (R + k) := by
  constructor
  · unfold multiplier coefficient
    have h9 : 9 ^ R = 3 ^ (2 * R) := by rw [Nat.pow_mul]
    rw [h9, ← Nat.pow_add]
    congr 1
    omega
  · unfold denominator scale
    have h8 : 4 * 8 ^ R = 2 ^ (2 + 3 * R) := by rw [Nat.pow_add, Nat.pow_mul]
    rw [h8, ← Nat.pow_add]
    congr 1
    omega

theorem candidate_size (R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) (hw : 0 < w)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    (SmallRegion (r + j) (R + k) → thirdScalar k v - 2 < mainSource R w) ∧
    (¬ SmallRegion (r + j) (R + k) → mainSource R w < thirdScalar k v - 2) := by
  let L := denominator r j k
  let A := multiplier r j k
  let P := padding r j k
  let X := 9 ^ R * w
  let Y := 8 ^ R * w
  let d := thirdScalar k v
  have hL : 0 < L := Nat.two_pow_pos _
  have hid : L * d = A * X + P := scaled_coordinates R w r u j q k v hX hT hB
  have hN : mainSource R w = 4 * Y - 5 := by unfold mainSource MinimumLadderCover.source Y; congr 1; ac_rfl
  have hXmin : 10000 ≤ X := by
    have hp : 9 ^ 5 ≤ 9 ^ R := Nat.pow_le_pow_right (by decide : 0 < 9) (by omega : 5 ≤ R)
    exact Nat.le_trans (by decide : 10000 ≤ 9 ^ 5) (Nat.le_trans hp (Nat.le_mul_of_pos_right _ hw))
  have hYmin : 512 ≤ Y := by
    have hp : 8 ^ 3 ≤ 8 ^ R := Nat.pow_le_pow_right (by decide : 0 < 8) (by omega : 3 ≤ R)
    exact Nat.le_trans hp (Nat.le_mul_of_pos_right _ hw)
  have hn := normalized_scales R r j k
  have hco : A * X = coefficient (r + j) (R + k) * w := by
    change multiplier r j k * (9 ^ R * w) = _
    rw [← Nat.mul_assoc, hn.1]
  have hsc : L * (4 * Y) = scale (r + j) (R + k) * w := by
    calc
      _ = (denominator r j k * (4 * 8 ^ R)) * w := by dsimp [L, Y]; ac_rfl
      _ = _ := by rw [hn.2]
  have hs := slope_boundary (r + j) (R + k) (by omega) (by omega)
  constructor
  · intro hg
    have hb : P ≤ 10 * A := padding_bound r j k hr
    have hpad : 1000 * P ≤ A * X := by
      calc
        _ ≤ 1000 * (10 * A) := Nat.mul_le_mul_left _ hb
        _ = A * 10000 := by omega
        _ ≤ _ := Nat.mul_le_mul_left _ hXmin
    have hh : 1000 * (A * X) ≤ 993 * (L * (4 * Y)) := by
      rw [hco, hsc]
      simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right w (hs.1 hg)
    have hlow : A * X ≤ L * (4 * Y) := by omega
    have hscaled : L * (1000 * d) ≤ L * (3976 * Y) := by
      calc
        _ = 1000 * (L * d) := by ac_rfl
        _ = 1000 * (A * X + P) := congrArg (1000 * ·) hid
        _ ≤ 994 * (L * (4 * Y)) := by omega
        _ = _ := by change 994 * (L * (4 * Y)) = L * ((994 * 4) * Y); ac_rfl
    have hd := Nat.le_of_mul_le_mul_left hscaled hL
    rw [hN]
    change d - 2 < 4 * Y - 5
    omega
  · intro hg
    have hh : L * (4 * Y) ≤ A * X := by
      rw [hco, hsc]
      exact Nat.mul_le_mul_right w (hs.2 hg)
    have hd := Nat.le_of_mul_le_mul_left (Nat.le_trans hh (show A * X ≤ L * d by omega)) hL
    rw [hN]
    change 4 * Y - 5 < d - 2
    omega

theorem candidate_size_iff (R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) (hw : 0 < w)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    thirdScalar k v - 2 < mainSource R w ↔ SmallRegion (r + j) (R + k) := by
  have h := candidate_size R w r u j q k v hR hr hw hX hT hB
  constructor
  · intro hp
    by_cases hs : SmallRegion (r + j) (R + k)
    · exact hs
    · have hh := h.2 hs; omega
  · exact h.1

theorem candidate_meeting (R w r u j q k v : Nat)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hvo : v % 2 = 1)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    iterate 1 (thirdScalar k v - 2) =
      iterate (5 * R + 116 + 18 * r + 18 * j + 5 * k) (mainSource R w) := by
  rw [main_third_profile R w r u j q k v hw hu hq hv hX hT hB]
  simpa only [iterate] using (immediate_predecessor k v hv hvo).2

theorem candidate_not_least (R w r u j q k v : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v) (hvo : v % 2 = 1)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hs : SmallRegion (r + j) (R + k)) : ¬ LeastCounterexample (mainSource R w) := by
  intro hn
  have hpos := (immediate_predecessor k v hv hvo).1
  have hlt := (candidate_size R w r u j q k v hR hr hw hX hT hB).1 hs
  have hm := candidate_meeting R w r u j q k v hw hu hq hv hvo hX hT hB
  have hle := least_coalescing_predecessor hn hpos hm
  omega

theorem pure_exponent_bound (R r u : Nat) (hr : 5 ≤ r) (hu : 0 < u)
    (hX : 9 ^ R + 7 = 2 ^ (57 + 11 * r) * u) : 36 ≤ R := by
  by_cases h : 36 ≤ R
  · exact h
  have hp : 9 ^ R ≤ 9 ^ 35 := Nat.pow_le_pow_right (by decide : 0 < 9) (by omega : R ≤ 35)
  have hD : 2 ^ 112 ≤ 2 ^ (57 + 11 * r) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hdu := Nat.le_mul_of_pos_right (2 ^ (57 + 11 * r)) hu
  have hfin : 9 ^ 35 + 7 < 2 ^ 112 := by decide
  omega

theorem pure_candidate_above (R r u j q k v : Nat) (hr : 5 ≤ r) (hu : 0 < u)
    (hX : 9 ^ R + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    mainSource R 1 < thirdScalar k v - 2 := by
  have hR := pure_exponent_bound R r u hr hu hX
  apply (candidate_size R 1 r u j q k v (by omega) hr (by decide)
    (by simpa only [Nat.mul_one] using hX) hT hB).2
  unfold SmallRegion
  omega

def CandidateEscape (R w r j k : Nat) : Prop :=
  ∃ u q v, 0 < u ∧ 0 < q ∧ 0 < v ∧ v % 2 = 1 ∧
    9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
    9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
    secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v ∧
    0 < thirdScalar k v - 2 ∧ thirdScalar k v - 2 < mainSource R w ∧
    ¬ LeastCounterexample (mainSource R w) ∧
    iterate 1 (thirdScalar k v - 2) =
      iterate (5 * R + 116 + 18 * r + 18 * j + 5 * k) (mainSource R w)

theorem weighted_candidate_escape (R r j k B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hs : SmallRegion (r + j) (R + k)) :
    ∃ w, B < w ∧ CandidateEscape R w r j k := by
  obtain ⟨S, u, q, v, hS, _, hu, hq, hv, hX, hT, hB, hvo⟩ :=
    pure_residue_lift r j k 0 1 (R + B + 1) (by decide) (by decide)
  let w := 9 ^ (S - R)
  have hwB : B < w := Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  have hw : 0 < w := by omega
  have hX' : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u := by
    dsimp [w]
    rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX
  refine ⟨w, hwB, u, q, v, hu, hq, hv, hvo, hX', hT, hB, (immediate_predecessor k v hv hvo).1,
    (candidate_size R w r u j q k v hR hr hw hX' hT hB).1 hs,
    candidate_not_least R w r u j q k v hR hr hw hu hq hv hvo hX' hT hB hs,
    candidate_meeting R w r u j q k v hw hu hq hv hvo hX' hT hB⟩

def InverseCertificate (B K : Nat) (S : List (Nat × Nat × Nat)) : Prop :=
  (0, 0, 2) ∈ S ∧ ∀ s ∈ S,
    s.1 ≤ B ∧ s.2.1 < K ∧ 2 ≤ s.2.2 ∧
    s.2.2 + 3 ^ K ≤ 2 + 2 ^ (s.1 + s.2.1) * 3 ^ (K - s.2.1) ∧
    (s.1 < B → (s.1 + 1, s.2.1, 2 * s.2.2) ∈ S) ∧
    ((2 * s.2.2 + 1) % 3 = 0 → (s.1, s.2.1 + 1, (2 * s.2.2 + 1) / 3) ∈ S)

def inverseStates : List (Nat × Nat × Nat) :=
[
  (0, 0, 2), (1, 0, 4), (1, 1, 3), (2, 0, 8), (2, 1, 6), (3, 0, 16),
  (3, 1, 11), (3, 1, 12), (4, 0, 32), (4, 1, 22), (4, 1, 24), (4, 2, 15),
  (5, 0, 64), (5, 1, 43), (5, 1, 44), (5, 1, 48), (5, 2, 29), (5, 2, 30),
  (6, 0, 128), (6, 1, 86), (6, 1, 88), (6, 1, 96), (6, 2, 58), (6, 2, 59),
  (6, 2, 60), (6, 3, 39), (7, 0, 256), (7, 1, 171), (7, 1, 172), (7, 1, 176),
  (7, 1, 192), (7, 2, 115), (7, 2, 116), (7, 2, 118), (7, 2, 120), (7, 3, 77),
  (7, 3, 78), (7, 3, 79), (7, 4, 53), (8, 0, 512), (8, 1, 342), (8, 1, 344),
  (8, 1, 352), (8, 1, 384), (8, 2, 230), (8, 2, 232), (8, 2, 235), (8, 2, 236),
  (8, 2, 240), (8, 3, 154), (8, 3, 155), (8, 3, 156), (8, 3, 157), (8, 3, 158),
  (8, 4, 103), (8, 4, 105), (8, 4, 106), (8, 5, 69), (8, 5, 71), (9, 0, 1024),
  (9, 1, 683), (9, 1, 684), (9, 1, 688), (9, 1, 704), (9, 1, 768), (9, 2, 459),
  (9, 2, 460), (9, 2, 464), (9, 2, 470), (9, 2, 472), (9, 2, 480), (9, 3, 307),
  (9, 3, 308), (9, 3, 310), (9, 3, 312), (9, 3, 314), (9, 3, 315), (9, 3, 316),
  (9, 4, 205), (9, 4, 206), (9, 4, 207), (9, 4, 210), (9, 4, 211), (9, 4, 212),
  (9, 5, 137), (9, 5, 138), (9, 5, 141), (9, 5, 142), (9, 6, 95), (10, 0, 2048),
  (10, 1, 1366), (10, 1, 1368), (10, 1, 1376), (10, 1, 1408), (10, 1, 1536), (10, 2, 911),
  (10, 2, 918), (10, 2, 920), (10, 2, 928), (10, 2, 939), (10, 2, 940), (10, 2, 944),
  (10, 2, 960), (10, 3, 614), (10, 3, 616), (10, 3, 619), (10, 3, 620), (10, 3, 624),
  (10, 3, 627), (10, 3, 628), (10, 3, 630), (10, 3, 632), (10, 4, 410), (10, 4, 411),
  (10, 4, 412), (10, 4, 413), (10, 4, 414), (10, 4, 419), (10, 4, 420), (10, 4, 422),
  (10, 4, 424), (10, 5, 274), (10, 5, 275), (10, 5, 276), (10, 5, 282), (10, 5, 283),
  (10, 5, 284), (10, 6, 183), (10, 6, 189), (10, 6, 190), (10, 7, 127), (10, 8, 85),
  (10, 9, 57), (11, 0, 4096), (11, 1, 2731), (11, 1, 2732), (11, 1, 2736), (11, 1, 2752),
  (11, 1, 2816), (11, 1, 3072), (11, 2, 1821), (11, 2, 1822), (11, 2, 1835), (11, 2, 1836),
  (11, 2, 1840), (11, 2, 1856), (11, 2, 1878), (11, 2, 1880), (11, 2, 1888), (11, 2, 1920),
  (11, 3, 1215), (11, 3, 1227), (11, 3, 1228), (11, 3, 1232), (11, 3, 1238), (11, 3, 1240),
  (11, 3, 1248), (11, 3, 1254), (11, 3, 1256), (11, 3, 1259), (11, 3, 1260), (11, 3, 1264),
  (11, 4, 819), (11, 4, 820), (11, 4, 822), (11, 4, 824), (11, 4, 826), (11, 4, 827),
  (11, 4, 828), (11, 4, 838), (11, 4, 840), (11, 4, 843), (11, 4, 844), (11, 4, 848),
  (11, 5, 547), (11, 5, 548), (11, 5, 550), (11, 5, 551), (11, 5, 552), (11, 5, 559),
  (11, 5, 563), (11, 5, 564), (11, 5, 566), (11, 5, 568), (11, 6, 365), (11, 6, 366),
  (11, 6, 367), (11, 6, 373), (11, 6, 378), (11, 6, 379), (11, 6, 380), (11, 7, 245),
  (11, 7, 249), (11, 7, 253), (11, 7, 254), (11, 8, 169), (11, 8, 170), (11, 9, 113),
  (11, 9, 114), (12, 0, 8192), (12, 1, 5462), (12, 1, 5464), (12, 1, 5472), (12, 1, 5504),
  (12, 1, 5632), (12, 1, 6144), (12, 2, 3642), (12, 2, 3643), (12, 2, 3644), (12, 2, 3670),
  (12, 2, 3672), (12, 2, 3680), (12, 2, 3712), (12, 2, 3755), (12, 2, 3756), (12, 2, 3760),
  (12, 2, 3776), (12, 2, 3840), (12, 3, 2429), (12, 3, 2430), (12, 3, 2447), (12, 3, 2454),
  (12, 3, 2456), (12, 3, 2464), (12, 3, 2475), (12, 3, 2476), (12, 3, 2480), (12, 3, 2496),
  (12, 3, 2507), (12, 3, 2508), (12, 3, 2512), (12, 3, 2518), (12, 3, 2520), (12, 3, 2528),
  (12, 4, 1638), (12, 4, 1640), (12, 4, 1643), (12, 4, 1644), (12, 4, 1648), (12, 4, 1651),
  (12, 4, 1652), (12, 4, 1654), (12, 4, 1656), (12, 4, 1675), (12, 4, 1676), (12, 4, 1679),
  (12, 4, 1680), (12, 4, 1686), (12, 4, 1688), (12, 4, 1696), (12, 5, 1094), (12, 5, 1096),
  (12, 5, 1099), (12, 5, 1100), (12, 5, 1101), (12, 5, 1102), (12, 5, 1103), (12, 5, 1104),
  (12, 5, 1117), (12, 5, 1118), (12, 5, 1126), (12, 5, 1128), (12, 5, 1131), (12, 5, 1132),
  (12, 5, 1136), (12, 6, 730), (12, 6, 731), (12, 6, 732), (12, 6, 733), (12, 6, 734),
  (12, 6, 735), (12, 6, 745), (12, 6, 746), (12, 6, 751), (12, 6, 755), (12, 6, 756),
  (12, 6, 758), (12, 6, 760), (12, 7, 487), (12, 7, 489), (12, 7, 490), (12, 7, 497),
  (12, 7, 498), (12, 7, 501), (12, 7, 506), (12, 7, 507), (12, 7, 508), (12, 8, 325),
  (12, 8, 327), (12, 8, 338), (12, 8, 339), (12, 8, 340), (12, 9, 217), (12, 9, 226),
  (12, 9, 227), (12, 9, 228), (12, 10, 145), (12, 10, 151), (12, 11, 97), (12, 11, 101),
  (12, 12, 65), (13, 0, 16384), (13, 1, 10923), (13, 1, 10924), (13, 1, 10928), (13, 1, 10944),
  (13, 1, 11008), (13, 1, 11264), (13, 1, 12288), (13, 2, 7283), (13, 2, 7284), (13, 2, 7286),
  (13, 2, 7288), (13, 2, 7339), (13, 2, 7340), (13, 2, 7344), (13, 2, 7360), (13, 2, 7424),
  (13, 2, 7510), (13, 2, 7512), (13, 2, 7520), (13, 2, 7552), (13, 2, 7680), (13, 3, 4858),
  (13, 3, 4859), (13, 3, 4860), (13, 3, 4893), (13, 3, 4894), (13, 3, 4907), (13, 3, 4908),
  (13, 3, 4912), (13, 3, 4928), (13, 3, 4950), (13, 3, 4952), (13, 3, 4960), (13, 3, 4992),
  (13, 3, 5007), (13, 3, 5014), (13, 3, 5016), (13, 3, 5024), (13, 3, 5035), (13, 3, 5036),
  (13, 3, 5040), (13, 3, 5056), (13, 4, 3239), (13, 4, 3263), (13, 4, 3275), (13, 4, 3276),
  (13, 4, 3280), (13, 4, 3286), (13, 4, 3288), (13, 4, 3296), (13, 4, 3302), (13, 4, 3304),
  (13, 4, 3307), (13, 4, 3308), (13, 4, 3312), (13, 4, 3343), (13, 4, 3350), (13, 4, 3352),
  (13, 4, 3357), (13, 4, 3358), (13, 4, 3360), (13, 4, 3371), (13, 4, 3372), (13, 4, 3376),
  (13, 4, 3392), (13, 5, 2187), (13, 5, 2188), (13, 5, 2191), (13, 5, 2192), (13, 5, 2198),
  (13, 5, 2200), (13, 5, 2202), (13, 5, 2203), (13, 5, 2204), (13, 5, 2205), (13, 5, 2206),
  (13, 5, 2208), (13, 5, 2229), (13, 5, 2234), (13, 5, 2235), (13, 5, 2236), (13, 5, 2239),
  (13, 5, 2251), (13, 5, 2252), (13, 5, 2256), (13, 5, 2262), (13, 5, 2264), (13, 5, 2272),
  (13, 6, 1459), (13, 6, 1460), (13, 6, 1461), (13, 6, 1462), (13, 6, 1464), (13, 6, 1466),
  (13, 6, 1467), (13, 6, 1468), (13, 6, 1469), (13, 6, 1470), (13, 6, 1471), (13, 6, 1490),
  (13, 6, 1491), (13, 6, 1492), (13, 6, 1493), (13, 6, 1501), (13, 6, 1502), (13, 6, 1510),
  (13, 6, 1512), (13, 6, 1515), (13, 6, 1516), (13, 6, 1520), (13, 7, 973), (13, 7, 974),
  (13, 7, 975), (13, 7, 978), (13, 7, 979), (13, 7, 980), (13, 7, 981), (13, 7, 994),
  (13, 7, 995), (13, 7, 996), (13, 7, 1001), (13, 7, 1002), (13, 7, 1007), (13, 7, 1011),
  (13, 7, 1012), (13, 7, 1014), (13, 7, 1016), (13, 8, 649), (13, 8, 650), (13, 8, 653),
  (13, 8, 654), (13, 8, 663), (13, 8, 675), (13, 8, 676), (13, 8, 678), (13, 8, 680),
  (13, 9, 433), (13, 9, 434), (13, 9, 451), (13, 9, 452), (13, 9, 454), (13, 9, 456),
  (13, 10, 289), (13, 10, 290), (13, 10, 301), (13, 10, 302), (13, 10, 303), (13, 11, 193),
  (13, 11, 194), (13, 11, 201), (13, 11, 202), (13, 12, 129), (13, 12, 130), (13, 12, 135),
  (13, 13, 87), (14, 0, 32768), (14, 1, 21846), (14, 1, 21848), (14, 1, 21856), (14, 1, 21888),
  (14, 1, 22016), (14, 1, 22528), (14, 1, 24576), (14, 2, 14566), (14, 2, 14568), (14, 2, 14571),
  (14, 2, 14572), (14, 2, 14576), (14, 2, 14678), (14, 2, 14680), (14, 2, 14688), (14, 2, 14720),
  (14, 2, 14848), (14, 2, 15019), (14, 2, 15020), (14, 2, 15024), (14, 2, 15040), (14, 2, 15104),
  (14, 2, 15360), (14, 3, 9711), (14, 3, 9715), (14, 3, 9716), (14, 3, 9718), (14, 3, 9720),
  (14, 3, 9786), (14, 3, 9787), (14, 3, 9788), (14, 3, 9814), (14, 3, 9816), (14, 3, 9824),
  (14, 3, 9856), (14, 3, 9899), (14, 3, 9900), (14, 3, 9904), (14, 3, 9920), (14, 3, 9984),
  (14, 3, 10013), (14, 3, 10014), (14, 3, 10027), (14, 3, 10028), (14, 3, 10032), (14, 3, 10048),
  (14, 3, 10070), (14, 3, 10072), (14, 3, 10080), (14, 3, 10112), (14, 4, 6477), (14, 4, 6478),
  (14, 4, 6479), (14, 4, 6525), (14, 4, 6526), (14, 4, 6543), (14, 4, 6550), (14, 4, 6552),
  (14, 4, 6560), (14, 4, 6571), (14, 4, 6572), (14, 4, 6576), (14, 4, 6592), (14, 4, 6603),
  (14, 4, 6604), (14, 4, 6608), (14, 4, 6614), (14, 4, 6616), (14, 4, 6624), (14, 4, 6685),
  (14, 4, 6686), (14, 4, 6699), (14, 4, 6700), (14, 4, 6704), (14, 4, 6714), (14, 4, 6715),
  (14, 4, 6716), (14, 4, 6720), (14, 4, 6742), (14, 4, 6744), (14, 4, 6752), (14, 4, 6784),
  (14, 5, 4319), (14, 5, 4351), (14, 5, 4367), (14, 5, 4374), (14, 5, 4376), (14, 5, 4381),
  (14, 5, 4382), (14, 5, 4384), (14, 5, 4395), (14, 5, 4396), (14, 5, 4400), (14, 5, 4403),
  (14, 5, 4404), (14, 5, 4406), (14, 5, 4408), (14, 5, 4410), (14, 5, 4411), (14, 5, 4412),
  (14, 5, 4416), (14, 5, 4457), (14, 5, 4458), (14, 5, 4467), (14, 5, 4468), (14, 5, 4470),
  (14, 5, 4472), (14, 5, 4477), (14, 5, 4478), (14, 5, 4495), (14, 5, 4502), (14, 5, 4504),
  (14, 5, 4512), (14, 5, 4523), (14, 5, 4524), (14, 5, 4528), (14, 5, 4544), (14, 6, 2901),
  (14, 6, 2918), (14, 6, 2920), (14, 6, 2921), (14, 6, 2922), (14, 6, 2923), (14, 6, 2924),
  (14, 6, 2928), (14, 6, 2931), (14, 6, 2932), (14, 6, 2934), (14, 6, 2936), (14, 6, 2938),
  (14, 6, 2939), (14, 6, 2940), (14, 6, 2941), (14, 6, 2942), (14, 6, 2979), (14, 6, 2980),
  (14, 6, 2982), (14, 6, 2984), (14, 6, 2985), (14, 6, 2986), (14, 6, 2997), (14, 6, 3002),
  (14, 6, 3003), (14, 6, 3004), (14, 6, 3019), (14, 6, 3020), (14, 6, 3024), (14, 6, 3030),
  (14, 6, 3032), (14, 6, 3040), (14, 7, 1946), (14, 7, 1947), (14, 7, 1948), (14, 7, 1949),
  (14, 7, 1950), (14, 7, 1955), (14, 7, 1956), (14, 7, 1958), (14, 7, 1959), (14, 7, 1960),
  (14, 7, 1961), (14, 7, 1962), (14, 7, 1987), (14, 7, 1988), (14, 7, 1990), (14, 7, 1991),
  (14, 7, 1992), (14, 7, 2002), (14, 7, 2003), (14, 7, 2004), (14, 7, 2013), (14, 7, 2014),
  (14, 7, 2022), (14, 7, 2024), (14, 7, 2027), (14, 7, 2028), (14, 7, 2032), (14, 8, 1298),
  (14, 8, 1299), (14, 8, 1300), (14, 8, 1306), (14, 8, 1307), (14, 8, 1308), (14, 8, 1325),
  (14, 8, 1326), (14, 8, 1327), (14, 8, 1335), (14, 8, 1343), (14, 8, 1350), (14, 8, 1352),
  (14, 8, 1355), (14, 8, 1356), (14, 8, 1360), (14, 9, 866), (14, 9, 867), (14, 9, 868),
  (14, 9, 871), (14, 9, 885), (14, 9, 902), (14, 9, 904), (14, 9, 907), (14, 9, 908),
  (14, 9, 912), (14, 10, 578), (14, 10, 579), (14, 10, 580), (14, 10, 581), (14, 10, 602),
  (14, 10, 603), (14, 10, 604), (14, 10, 605), (14, 10, 606), (14, 11, 386), (14, 11, 387),
  (14, 11, 388), (14, 11, 402), (14, 11, 403), (14, 11, 404), (14, 12, 258), (14, 12, 259),
  (14, 12, 260), (14, 12, 269), (14, 12, 270), (14, 13, 173), (14, 13, 174)
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem finite_inverse_certificate : InverseCertificate 14 14 inverseStates := by
  unfold InverseCertificate
  decide +kernel

theorem certificate_lift {e o b p : Nat} (h : Backtrack e o b p)
    (B K0 K v : Nat) (S : List (Nat × Nat × Nat))
    (hc : InverseCertificate B K0 S) (hK : K0 ≤ K) (he : e ≤ B)
    (hb : b + 2 = 3 ^ K * v) :
    ∃ m, (e, o, m) ∈ S ∧ p + m = 2 ^ (e + o) * 3 ^ (K - o) * v := by
  induction h with
  | nil b => exact ⟨2, hc.1, by simpa using hb⟩
  | @even e o b x h ih =>
    obtain ⟨m, hm, hx⟩ := ih (by omega) hb
    have hs := hc.2 (e, o, m) hm
    have hn := hs.2.2.2.2.1 (by omega : e < B)
    have hpow : 2 ^ (e + 1 + o) * 3 ^ (K - o) * v =
        2 * (2 ^ (e + o) * 3 ^ (K - o) * v) := by
      rw [show e + 1 + o = (e + o) + 1 by omega, Nat.pow_succ]
      ac_rfl
    exact ⟨2 * m, hn, by rw [hpow]; omega⟩
  | @odd e o b x p h hp ih =>
    obtain ⟨m, hm, hx⟩ := ih he hb
    have hs := hc.2 (e, o, m) hm
    have ho : o < K0 := hs.2.1
    let Z := 2 ^ (e + o) * 3 ^ (K - (o + 1)) * v
    have hpow : 2 ^ (e + o) * 3 ^ (K - o) * v = 3 * Z := by
      rw [show K - o = (K - (o + 1)) + 1 by omega, Nat.pow_succ]
      dsimp [Z]
      ac_rfl
    rw [hpow] at hx
    have hmod : (2 * m + 1) % 3 = 0 := by omega
    have hn := hs.2.2.2.2.2 hmod
    have hnext : 2 ^ (e + (o + 1)) * 3 ^ (K - (o + 1)) * v = 2 * Z := by
      rw [show e + (o + 1) = (e + o) + 1 by omega, Nat.pow_succ]
      dsimp [Z]
      ac_rfl
    exact ⟨(2 * m + 1) / 3, hn, by rw [hnext]; omega⟩

theorem certificate_lower {e o b p : Nat} (h : Backtrack e o b p)
    (B K0 K v : Nat) (S : List (Nat × Nat × Nat))
    (hc : InverseCertificate B K0 S) (hK : K0 ≤ K) (hv : 0 < v) (he : e ≤ B)
    (hb : b + 2 = 3 ^ K * v) : b ≤ p := by
  obtain ⟨m, hm, hp⟩ := certificate_lift h B K0 K v S hc hK he hb
  have hs := hc.2 (e, o, m) hm
  have ho : o < K0 := hs.2.1
  have hm2 : 2 ≤ m := hs.2.2.1
  have hbound : m + 3 ^ K0 ≤ 2 + 2 ^ (e + o) * 3 ^ (K0 - o) := hs.2.2.2.1
  let V := 3 ^ (K - K0) * v
  have hV : 0 < V := Nat.mul_pos (Nat.pow_pos (by decide)) hv
  have hbase : m - 2 + 3 ^ K0 ≤ 2 ^ (e + o) * 3 ^ (K0 - o) := by omega
  have hmul := Nat.mul_le_mul_right V hbase
  have hfirst : 3 ^ K0 * V = 3 ^ K * v := by
    dsimp [V]
    rw [← Nat.mul_assoc, ← Nat.pow_add, show K0 + (K - K0) = K by omega]
  have hsecond : (2 ^ (e + o) * 3 ^ (K0 - o)) * V =
      2 ^ (e + o) * 3 ^ (K - o) * v := by
    calc
      _ = 2 ^ (e + o) * (3 ^ (K0 - o) * 3 ^ (K - K0)) * v := by dsimp [V]; ac_rfl
      _ = _ := by rw [← Nat.pow_add, show K0 - o + (K - K0) = K - o by omega]
  rw [Nat.add_mul, hfirst, hsecond] at hmul
  have hmin : m - 2 ≤ (m - 2) * V := Nat.le_mul_of_pos_right _ hV
  omega

theorem fourteen_even_minimum {e o p : Nat} (k v : Nat) (hk : 6 ≤ k) (hv : 0 < v)
    (h : Backtrack e o (thirdScalar k v - 2) p) (he : e ≤ 14) : thirdScalar k v - 2 ≤ p := by
  have h9 : 9 ^ (k + 1) = 3 ^ (2 * (k + 1)) := by rw [Nat.pow_mul]
  have hsmall : 2 ≤ thirdScalar k v := by
    have hp : 9 ≤ 9 ^ (k + 1) := Nat.pow_le_pow_right (by decide : 0 < 9) (by omega : 1 ≤ k + 1)
    have hm := Nat.le_mul_of_pos_right (9 ^ (k + 1)) hv
    change 2 ≤ 9 ^ (k + 1) * v
    omega
  have hb : thirdScalar k v - 2 + 2 = 3 ^ (2 * (k + 1)) * v := by
    rw [Nat.sub_add_cancel hsmall]
    unfold thirdScalar
    rw [h9]
  exact certificate_lower h 14 14 (2 * (k + 1)) v inverseStates finite_inverse_certificate (by omega) hv he hb

theorem fourteen_even_above_source {e o p : Nat} (R w r u j q k v : Nat)
    (hR : 14 ≤ R) (hr : 5 ≤ r) (hw : 0 < w) (hk : 6 ≤ k) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (h : Backtrack e o (thirdScalar k v - 2) p) (he : e ≤ 14) : mainSource R w < p := by
  have hn := (candidate_size R w r u j q k v hR hr hw hX hT hB).2
    (by unfold SmallRegion; omega)
  exact Nat.lt_of_lt_of_le hn (fourteen_even_minimum k v hk hv h he)

#print axioms immediate_predecessor
#print axioms main_third_profile
#print axioms scaled_coordinates
#print axioms finite_size_boundary
#print axioms growth_transport
#print axioms slope_boundary
#print axioms denominator_bound
#print axioms padding_bound
#print axioms normalized_scales
#print axioms candidate_size
#print axioms candidate_size_iff
#print axioms candidate_meeting
#print axioms candidate_not_least
#print axioms pure_exponent_bound
#print axioms pure_candidate_above
#print axioms weighted_candidate_escape
#print axioms finite_inverse_certificate
#print axioms certificate_lift
#print axioms certificate_lower
#print axioms fourteen_even_minimum
#print axioms fourteen_even_above_source

end MinimumFivePredecessor
