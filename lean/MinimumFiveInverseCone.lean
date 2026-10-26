/- Bounds for complete inverse trees with a parameter-dependent even budget. -/
import MinimumFivePredecessor

namespace MinimumFiveInverseCone
open OrdinaryCollatz MinimumReturnLadder MinimumFivePredecessor
open MinimumSeventeenTransition MinimumSeventeenFourth MinimumFiveTransition

inductive Reference (c : Nat) : Nat → Nat → Nat → Prop
  | nil : Reference c 0 0 c
  | even {e o m : Nat} : Reference c e o m → Reference c (e + 1) o (2 * m)
  | odd {e o m z : Nat} : Reference c e o m →
      3 * z = 2 * m + 1 → Reference c e (o + 1) z

def SmallState (e o m : Nat) : Prop :=
  (e = 0 ∧ o = 0 ∧ m = 2) ∨ (e = 1 ∧ o = 0 ∧ m = 4) ∨
  (e = 1 ∧ o = 1 ∧ m = 3)

theorem two_reference {e o m : Nat} (h : Reference 2 e o m) :
    2 ≤ m ∧ o ≤ 2 * e ∧ (5 ≤ m ∨ SmallState e o m) ∧
      2 ^ (2 * e - o) * (m - 1) ≤ 2 * 3 ^ (2 * e - o) := by
  induction h with
  | nil => exact ⟨by decide, by decide, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by decide⟩
  | @even e o m h ih =>
    obtain ⟨hm, ho, hs, hb⟩ := ih
    have hd : 2 * (e + 1) - o = (2 * e - o) + 2 := by omega
    refine ⟨by omega, by omega, ?_, ?_⟩
    · rcases hs with hs | hs
      · exact Or.inl (by omega)
      · unfold SmallState at *
        omega
    · rw [hd, Nat.pow_add, Nat.pow_add]
      by_cases h5 : 5 ≤ m
      · have hstep := Nat.mul_le_mul_left (2 ^ (2 * e - o))
          (show 4 * (2 * m - 1) ≤ 9 * (m - 1) by omega)
        have hmul := Nat.mul_le_mul_left 9 hb
        grind
      · have hx : SmallState e o m := hs.resolve_left h5
        rcases hx with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> decide
  | @odd e o m z h hz ih =>
    obtain ⟨hm, ho, hs, hb⟩ := ih
    have hd : 0 < 2 * e - o := by
      by_cases he : 2 * e - o = 0
      · rw [he] at hb
        simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one] at hb
        omega
      · omega
    have hsmall : 5 ≤ z ∨ SmallState e (o + 1) z := by
      rcases hs with hs | hs
      · exact Or.inl (by omega)
      · unfold SmallState at *
        omega
    refine ⟨by omega, by omega, hsmall, ?_⟩
    have he : 2 * e - o = (2 * e - (o + 1)) + 1 := by omega
    rw [he, Nat.pow_succ, Nat.pow_succ] at hb
    have hr : 3 * (z - 1) = 2 * (m - 1) := by omega
    have hm' : 3 * (2 ^ (2 * e - (o + 1)) * (z - 1)) ≤
        3 * (2 * 3 ^ (2 * e - (o + 1))) := by
      calc
        _ = 2 ^ (2 * e - (o + 1)) * (3 * (z - 1)) := by ac_rfl
        _ = 2 ^ (2 * e - (o + 1)) * (2 * (m - 1)) := by rw [hr]
        _ = (2 ^ (2 * e - (o + 1)) * 2) * (m - 1) := by ac_rfl
        _ ≤ _ := by omega
    omega

theorem five_reference {e o m : Nat} (h : Reference 5 e o m) :
    5 ≤ m ∧ o ≤ 2 * e ∧
      2 ^ (2 * e - o) * (m - 1) ≤ 4 * 3 ^ (2 * e - o) := by
  induction h with
  | nil => exact ⟨by decide, by decide, by decide⟩
  | @even e o m h ih =>
    obtain ⟨hm, ho, hb⟩ := ih
    have he : 2 * (e + 1) - o = (2 * e - o) + 2 := by omega
    exact ⟨by omega, by omega, he ▸ companion_even (2 * e - o) m hm hb⟩
  | @odd e o m z h hz ih =>
    obtain ⟨hm, ho, hb⟩ := ih
    have ht := companion_odd (2 * e - o) m z hm hz hb
    refine ⟨ht.2.1, by omega, ?_⟩
    have he : 2 * e - (o + 1) = (2 * e - o) - 1 := by omega
    rw [he]
    exact ht.2.2.2

theorem reference_odd_bound {c e o m : Nat} (h : Reference c e o m)
    (hc : c = 2 ∨ c = 5) : o ≤ 2 * e := by
  rcases hc with rfl | rfl
  · exact (two_reference h).2.1
  · exact (five_reference h).2.1

theorem reference_lift {e o b p : Nat} (h : Backtrack e o b p)
    (c K v : Nat) (hc : c = 2 ∨ c = 5) (hK : 2 * e < K)
    (hb : b + c = 3 ^ K * v) :
    ∃ m, Reference c e o m ∧ p + m = 2 ^ (e + o) * 3 ^ (K - o) * v := by
  induction h with
  | nil b => exact ⟨c, Reference.nil, by simpa using hb⟩
  | @even e o b x h ih =>
    obtain ⟨m, hm, hx⟩ := ih (by omega) hb
    have he : 2 ^ (e + 1 + o) * 3 ^ (K - o) * v =
        2 * (2 ^ (e + o) * 3 ^ (K - o) * v) := by
      rw [show e + 1 + o = (e + o) + 1 by omega, Nat.pow_succ]
      ac_rfl
    exact ⟨2 * m, Reference.even hm, by rw [he]; omega⟩
  | @odd e o b x p h hp ih =>
    obtain ⟨m, hm, hx⟩ := ih hK hb
    have ho := reference_odd_bound hm hc
    let Z := 2 ^ (e + o) * 3 ^ (K - (o + 1)) * v
    have he : 2 ^ (e + o) * 3 ^ (K - o) * v = 3 * Z := by
      rw [show K - o = (K - (o + 1)) + 1 by omega, Nat.pow_succ]
      dsimp [Z]
      ac_rfl
    rw [he] at hx
    have hz : 3 * ((2 * m + 1) / 3) = 2 * m + 1 := by omega
    have hn : 2 ^ (e + (o + 1)) * 3 ^ (K - (o + 1)) * v = 2 * Z := by
      rw [show e + (o + 1) = (e + o) + 1 by omega, Nat.pow_succ]
      dsimp [Z]
      ac_rfl
    exact ⟨(2 * m + 1) / 3, Reference.odd hm hz, by rw [hn]; omega⟩

theorem potential_lower (e o K v p m a : Nat) (ho : o ≤ 2 * e) (hK : 2 * e ≤ K)
    (hm : 1 ≤ m) (hp : p + m = 2 ^ (e + o) * 3 ^ (K - o) * v)
    (hb : 2 ^ (2 * e - o) * (m - 1) ≤ a * 3 ^ (2 * e - o)) :
    8 ^ e * 3 ^ (K - 2 * e) * v ≤ p + a + 1 := by
  let d := 2 * e - o
  have hid : 2 ^ d * (p + m) = 3 ^ d * (8 ^ e * 3 ^ (K - 2 * e) * v) := by
    rw [hp]
    have h3 : K - o = d + (K - 2 * e) := by dsimp [d]; omega
    have h2 : d + (e + o) = 3 * e := by dsimp [d]; omega
    rw [h3, Nat.pow_add 3]
    calc
      _ = (2 ^ d * 2 ^ (e + o)) * (3 ^ d * 3 ^ (K - 2 * e)) * v := by ac_rfl
      _ = _ := by rw [← Nat.pow_add, h2, Nat.pow_mul]; ac_rfl
  have hpow : 2 ^ d ≤ 3 ^ d := Nat.pow_le_pow_left (by decide) d
  have hle : 3 ^ d * (8 ^ e * 3 ^ (K - 2 * e) * v) ≤ 3 ^ d * (p + a + 1) := by
    calc
      _ = 2 ^ d * (p + 1) + 2 ^ d * (m - 1) := by rw [← hid, ← Nat.mul_add]; congr 1; omega
      _ ≤ 3 ^ d * (p + 1) + a * 3 ^ d :=
        Nat.add_le_add (Nat.mul_le_mul_right _ hpow) hb
      _ = _ := by grind
  exact Nat.le_of_mul_le_mul_left hle (Nat.pow_pos (by decide))

theorem budget_monotone (e B K v : Nat) (he : e ≤ B) (hK : 2 * B ≤ K) :
    8 ^ B * 3 ^ (K - 2 * B) * v ≤ 8 ^ e * 3 ^ (K - 2 * e) * v := by
  have hg := Nat.pow_le_pow_left (by decide : 8 ≤ 9) (B - e)
  have hm := Nat.mul_le_mul_right (3 ^ (K - 2 * B) * v) (Nat.mul_le_mul_left (8 ^ e) hg)
  have hB : e + (B - e) = B := by omega
  have h3 : 2 * (B - e) + (K - 2 * B) = K - 2 * e := by omega
  have h9 : 9 ^ (B - e) = 3 ^ (2 * (B - e)) := by rw [Nat.pow_mul]
  rw [h9] at hm
  have hl : (8 ^ e * 8 ^ (B - e)) * (3 ^ (K - 2 * B) * v) =
      8 ^ B * 3 ^ (K - 2 * B) * v := by rw [← Nat.pow_add, hB]; ac_rfl
  have hr : (8 ^ e * 3 ^ (2 * (B - e))) * (3 ^ (K - 2 * B) * v) =
      8 ^ e * 3 ^ (K - 2 * e) * v := by
    rw [Nat.mul_assoc, ← Nat.mul_assoc (3 ^ (2 * (B - e))), ← Nat.pow_add, h3]
    ac_rfl
  rw [hl, hr] at hm
  exact hm

theorem two_lower {e o b p : Nat} (h : Backtrack e o b p)
    (B K v : Nat) (he : e ≤ B) (hK : 2 * B < K) (hb : b + 2 = 3 ^ K * v) :
    o ≤ 2 * e ∧ 8 ^ B * 3 ^ (K - 2 * B) * v ≤ p + 3 := by
  obtain ⟨m, hm, hp⟩ := reference_lift h 2 K v (Or.inl rfl) (by omega) hb
  have hi := two_reference hm
  have hl := potential_lower e o K v p m 2 hi.2.1 (by omega) (by omega) hp hi.2.2.2
  exact ⟨hi.2.1, Nat.le_trans (budget_monotone e B K v he (by omega)) hl⟩

theorem five_lower {e o b p : Nat} (h : Backtrack e o b p)
    (B K v : Nat) (he : e ≤ B) (hK : 2 * B < K) (hb : b + 5 = 3 ^ K * v) :
    o ≤ 2 * e ∧ 8 ^ B * 3 ^ (K - 2 * B) * v ≤ p + 5 := by
  obtain ⟨m, hm, hp⟩ := reference_lift h 5 K v (Or.inr rfl) (by omega) hb
  have hi := five_reference hm
  have hl := potential_lower e o K v p m 4 hi.2.1 (by omega) (by omega) hp hi.2.2
  exact ⟨hi.2.1, Nat.le_trans (budget_monotone e B K v he (by omega)) hl⟩

theorem five_block (q : Nat) (hq : 0 < q) :
    Backtrack 1 2 (9 * q - 5) (8 * q - 5) := by
  have h0 := Backtrack.even (Backtrack.nil (9 * q - 5))
  have h1 := Backtrack.odd h0
    (show 3 * (12 * q - 7) + 1 = 2 * (2 * (9 * q - 5)) by omega)
  exact Backtrack.odd h1 (show 3 * (8 * q - 5) + 1 = 2 * (12 * q - 7) by omega)

theorem five_blocks (B q : Nat) (hq : 0 < q) :
    Backtrack B (2 * B) (9 ^ B * q - 5) (8 ^ B * q - 5) := by
  induction B generalizing q with
  | zero => simpa using Backtrack.nil (q - 5)
  | succ B ih =>
    have h1 := ih (9 * q) (by omega)
    have h2 := five_block (8 ^ B * q) (Nat.mul_pos (Nat.pow_pos (by decide)) hq)
    rw [show 8 ^ B * (9 * q) = 9 * (8 ^ B * q) by ac_rfl] at h1
    have h := backtrack_append h1 h2
    simpa only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using h

theorem five_exact_minimum (B K v b : Nat) (hK : 2 * B < K) (hv : 0 < v)
    (hb : b + 5 = 3 ^ K * v) :
    Backtrack B (2 * B) b (8 ^ B * 3 ^ (K - 2 * B) * v - 5) ∧
    ∀ e o p, Backtrack e o b p → e ≤ B → 8 ^ B * 3 ^ (K - 2 * B) * v - 5 ≤ p := by
  have he : 9 ^ B * (3 ^ (K - 2 * B) * v) = 3 ^ K * v := by
    rw [show 9 ^ B = 3 ^ (2 * B) by rw [Nat.pow_mul], ← Nat.mul_assoc, ← Nat.pow_add,
      show 2 * B + (K - 2 * B) = K by omega]
  have ha := five_blocks B (3 ^ (K - 2 * B) * v) (Nat.mul_pos (Nat.pow_pos (by decide)) hv)
  rw [he, ← hb, Nat.add_sub_cancel] at ha
  refine ⟨by simpa only [Nat.mul_assoc] using ha, ?_⟩
  intro e o p hp he
  have hh := (five_lower hp B K v he hK hb).2
  omega

theorem precision_boundary_witness :
    Backtrack 2 5 76 39 ∧ 39 < 8 ^ 2 - 5 ∧ 76 + 5 = 3 ^ (2 * 2) := by
  have h := five_blocks 2 1 (by decide)
  change Backtrack 2 4 76 59 at h
  exact ⟨Backtrack.odd h (by decide), by decide, by decide⟩

theorem backtrack_first {e o b p : Nat} (h : Backtrack e o b p) :
    (e = 0 ∧ o = 0 ∧ p = b) ∨
    (∃ f, e = f + 1 ∧ Backtrack f o (2 * b) p) ∨
    (∃ f x, o = f + 1 ∧ 3 * x + 1 = 2 * b ∧ Backtrack e f x p) := by
  induction h with
  | nil b => exact Or.inl ⟨rfl, rfl, rfl⟩
  | @even e o b x h ih =>
    rcases ih with ⟨rfl, rfl, rfl⟩ | ⟨f, he, hf⟩ | ⟨f, y, ho, hy, hf⟩
    · exact Or.inr (Or.inl ⟨0, rfl, Backtrack.nil _⟩)
    · exact Or.inr (Or.inl ⟨f + 1, by omega, Backtrack.even hf⟩)
    · exact Or.inr (Or.inr ⟨f, y, ho, hy, Backtrack.even hf⟩)
  | @odd e o b x p h hp ih =>
    rcases ih with ⟨rfl, rfl, rfl⟩ | ⟨f, he, hf⟩ | ⟨f, y, ho, hy, hf⟩
    · exact Or.inr (Or.inr ⟨0, p, rfl, hp, Backtrack.nil _⟩)
    · exact Or.inr (Or.inl ⟨f, he, Backtrack.odd hf hp⟩)
    · exact Or.inr (Or.inr ⟨f + 1, y, by omega, hy, Backtrack.odd hf hp⟩)

theorem third_inverse_minimum (k v : Nat) (hv : 0 < v) :
    Backtrack (k + 1) (2 * (k + 1)) (3 * thirdScalar k v - 5)
      (3 * 8 ^ (k + 1) * v - 5) ∧
    ∀ e o p, Backtrack e o (3 * thirdScalar k v - 5) p → e ≤ k + 1 →
      3 * 8 ^ (k + 1) * v - 5 ≤ p := by
  have hp : 9 ≤ thirdScalar k v := by
    have h9 := Nat.pow_le_pow_right (by decide : 0 < 9) (show 1 ≤ k + 1 by omega)
    exact Nat.le_trans h9 (Nat.le_mul_of_pos_right _ hv)
  have h3 : 3 * thirdScalar k v = 3 ^ (2 * k + 3) * v := by
    unfold thirdScalar
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
      Nat.pow_succ 3, Nat.pow_mul 3]
    ac_rfl
  have h := five_exact_minimum (k + 1) (2 * k + 3) v (3 * thirdScalar k v - 5)
    (by omega) hv (by omega)
  have he : 2 * k + 3 - 2 * (k + 1) = 1 := by omega
  rw [he, Nat.pow_one] at h
  simpa only [Nat.mul_comm, Nat.mul_left_comm] using h

theorem half_third_lower {e o p H : Nat} (k v : Nat) (hv : 0 < v)
    (hH : 2 * H + 5 = 3 * thirdScalar k v)
    (h : Backtrack e o H p) (he : e ≤ k) : 9 * 8 ^ k * v ≤ p + 3 := by
  have h3 : 3 * thirdScalar k v = 3 ^ (2 * k + 3) * v := by
    unfold thirdScalar
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
      Nat.pow_succ 3, Nat.pow_mul 3]
    ac_rfl
  have h9 : thirdScalar k v = 3 ^ (2 * k + 2) * v := by
    unfold thirdScalar
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, Nat.pow_mul]
  have hpos : 0 < 8 ^ k * v := Nat.mul_pos (Nat.pow_pos (by decide)) hv
  have hlo : 9 * 8 ^ k * v ≤ thirdScalar k v := by
    have hg := Nat.mul_le_mul_right v (Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left (by decide : 8 ≤ 9) k))
    simpa only [thirdScalar, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm] using hg
  rcases backtrack_first h with ⟨_, _, rfl⟩ | ⟨f, hf, hh⟩ | ⟨f, x, _, hx, hh⟩
  · omega
  · have hb : 2 * H + 5 = 3 ^ (2 * k + 3) * v := hH.trans h3
    have hl := (five_lower hh k (2 * k + 3) v (by omega) (by omega) hb).2
    rw [show 2 * k + 3 - 2 * k = 3 by omega] at hl
    have hg : 8 ^ k * 3 ^ 3 * v = 27 * (8 ^ k * v) := by ac_rfl
    rw [hg] at hl
    have ht : 9 * 8 ^ k * v = 9 * (8 ^ k * v) := by ac_rfl
    rw [ht]
    omega
  · have hb : x + 2 = 3 ^ (2 * k + 2) * v := by omega
    have hl := (two_lower hh k (2 * k + 2) v he (by omega) hb).2
    rw [show 2 * k + 2 - 2 * k = 2 by omega] at hl
    change 8 ^ k * 9 * v ≤ p + 3 at hl
    simpa only [Nat.mul_comm, Nat.mul_left_comm] using hl

theorem doubled_growth (s t : Nat) (hs : 5 ≤ s) (ht : 26 ≤ t) :
    2 * scale s t ≤ coefficient s t := by
  have hbase : 2 * scale 5 26 ≤ coefficient 5 26 := by decide +kernel
  have ha := Nat.pow_le_pow_left (by decide : 2 ^ 11 ≤ 3 ^ 7) (s - 5)
  have hb := Nat.pow_le_pow_left (by decide : 2 ^ 3 ≤ 3 ^ 2) (t - 26)
  have hm := Nat.mul_le_mul (Nat.mul_le_mul hbase ha) hb
  unfold scale coefficient at *
  have he2 : (72 + 11 * 5 + 3 * 26) + 11 * (s - 5) + 3 * (t - 26) = 72 + 11 * s + 3 * t := by omega
  have he3 : (43 + 7 * 5 + 2 * 26) + 7 * (s - 5) + 2 * (t - 26) = 43 + 7 * s + 2 * t := by omega
  simpa only [← Nat.pow_mul, Nat.mul_assoc, ← Nat.pow_add, he2, he3] using hm

theorem source_gap (R w r u j q k v : Nat) (hR : 26 ≤ R) (hr : 5 ≤ r) (hw : 0 < w)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v) :
    mainSource R w + 3 < 9 * 8 ^ k * v := by
  let z := 8 ^ k * v
  have hz : secondaryScalar j q = 1 + 2 ^ (3 * 0 + 4) * z := by
    have he : 2 ^ (3 * k + 4) * v = 16 * z := by
      dsimp [z]
      rw [Nat.pow_add, Nat.pow_mul]
      ac_rfl
    simpa only [he] using hB
  have hid := scaled_coordinates R w r u j q 0 z hX hT hz
  have hn := normalized_scales R r j 0
  have hg := Nat.mul_le_mul_right w (doubled_growth (r + j) R (by omega) hR)
  have hlo : denominator r j 0 * (8 * (8 ^ R * w)) ≤ denominator r j 0 * (9 * z) := by
    calc
      _ = 2 * scale (r + j) R * w := by
        rw [← show R + 0 = R by omega, ← hn.2]
        grind
      _ ≤ coefficient (r + j) R * w := hg
      _ = multiplier r j 0 * (9 ^ R * w) := by rw [← show R + 0 = R by omega, ← hn.1]; ac_rfl
      _ ≤ denominator r j 0 * thirdScalar 0 z := by omega
      _ = _ := by simp [thirdScalar]
  have hcancel := Nat.le_of_mul_le_mul_left hlo (Nat.two_pow_pos (70 + 11 * (r + j) + 3 * 0))
  have hY : 0 < 8 ^ R * w := Nat.mul_pos (Nat.pow_pos (by decide)) hw
  have he : mainSource R w = 4 * (8 ^ R * w) - 5 := by
    unfold mainSource MinimumLadderCover.source
    congr 1
    ac_rfl
  rw [he]
  rw [Nat.mul_assoc 9]
  change 8 * (8 ^ R * w) ≤ 9 * (8 ^ k * v) at hcancel
  omega

theorem pure_half_third_obstruction {e o p H : Nat} (R r u j q k v : Nat)
    (hr : 5 ≤ r) (hu : 0 < u) (hv : 0 < v)
    (hX : 9 ^ R + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hH : 2 * H + 5 = 3 * thirdScalar k v)
    (h : Backtrack e o H p) (he : e ≤ k) : mainSource R 1 < p := by
  have hR := pure_exponent_bound R r u hr hu hX
  have hg := source_gap R 1 r u j q k v (by omega) hr (by decide) (by simpa using hX) hT hB
  have hl := half_third_lower k v hv hH h he
  omega

theorem weighted_half_third_obstruction {e o p H : Nat} (R w r u j q k v : Nat)
    (hR : 26 ≤ R) (hr : 5 ≤ r) (hw : 0 < w) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hH : 2 * H + 5 = 3 * thirdScalar k v)
    (h : Backtrack e o H p) (he : e ≤ k) : mainSource R w < p := by
  have hg := source_gap R w r u j q k v hR hr hw hX hT hB
  have hl := half_third_lower k v hv hH h he
  omega

attribute [local irreducible] OrdinaryCollatz.iterate in
theorem half_third_profile (R w r u j q k v H : Nat)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q) (hv : 0 < v)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hB : secondaryScalar j q = 1 + 2 ^ (3 * k + 4) * v)
    (hH : 2 * H + 5 = 3 * thirdScalar k v) :
    iterate (5 * R + 117 + 18 * r + 18 * j + 5 * k) (mainSource R w) = H := by
  have h0 := main_third_profile R w r u j q k v hw hu hq hv hX hT hB
  have ht : 5 * R + 117 + 18 * r + 18 * j + 5 * k =
      (5 * R + 116 + 18 * r + 18 * j + 5 * k) + 1 := by omega
  rw [ht, iterate_add, h0]
  simp only [iterate]
  rw [show 3 * thirdScalar k v - 5 = 2 * H by omega]
  unfold C
  split <;> omega

#print axioms two_reference
#print axioms five_reference
#print axioms reference_odd_bound
#print axioms reference_lift
#print axioms potential_lower
#print axioms budget_monotone
#print axioms two_lower
#print axioms five_lower
#print axioms five_block
#print axioms five_blocks
#print axioms five_exact_minimum
#print axioms precision_boundary_witness
#print axioms backtrack_first
#print axioms third_inverse_minimum
#print axioms half_third_lower
#print axioms doubled_growth
#print axioms source_gap
#print axioms pure_half_third_obstruction
#print axioms weighted_half_third_obstruction
#print axioms half_third_profile

end MinimumFiveInverseCone
