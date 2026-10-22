/- A fixed extra inverse budget can fail at every target in an arbitrarily
   long growing return-ladder prefix. This does not supply a divergent orbit. -/
import MinimumInverseLocality

namespace MinimumLadderWindow
open OrdinaryCollatz MinimumReturnLadder MinimumInverseEscape MinimumInverseLocality

theorem shadow_bounds {e o m : Nat} (h : Shadow e o m) :
    5 ≤ m ∧ o ≤ 2 * e + 1 ∧
      m ≤ (if o % 2 = 0 then 7 else 5) * 2 ^ (e - o / 2) := by
  induction h with
  | nil => exact ⟨by decide, by decide, by decide⟩
  | @even e o m h ih =>
    have he : e + 1 - o / 2 = (e - o / 2) + 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [he, Nat.pow_succ]
    have hh := Nat.mul_le_mul_left 2 ih.2.2
    calc
      _ ≤ 2 * ((if o % 2 = 0 then 7 else 5) * 2 ^ (e - o / 2)) := hh
      _ = _ := by ac_rfl
  | @odd e o m z h hz ih =>
    have hz5 : 5 ≤ z := by omega
    by_cases hp : o % 2 = 0
    · have hp' : (o + 1) % 2 ≠ 0 := by omega
      have he : (o + 1) / 2 = o / 2 := by omega
      have ht := Nat.two_pow_pos (e - o / 2)
      rw [if_pos hp] at ih
      refine ⟨hz5, by omega, ?_⟩
      rw [if_neg hp', he]
      omega
    · have hp' : (o + 1) % 2 = 0 := by omega
      have hlt : o < 2 * e + 1 := by
        by_cases heq : o = 2 * e + 1
        · have hd : e - o / 2 = 0 := by omega
          rw [if_neg hp, hd] at ih
          simp only [Nat.pow_zero, Nat.mul_one] at ih
          omega
        · omega
      have he : e - o / 2 = (e - (o + 1) / 2) + 1 := by omega
      rw [if_neg hp, he, Nat.pow_succ] at ih
      have ht := Nat.two_pow_pos (e - (o + 1) / 2)
      refine ⟨hz5, by omega, ?_⟩
      rw [if_pos hp']
      omega

theorem shadow_not_eight {e o m : Nat} (h : Shadow e o m) : m ≠ 8 := by
  cases h with
  | nil => decide
  | even h => have hm := (shadow_bounds h).1; omega
  | odd h hz => omega

theorem frontier_shadow_bound {i f m : Nat} (h : Shadow (i + f) (2 * i + 1) m) :
    5 ≤ m ∧ m ≤ 5 * 2 ^ f ∧ m ≠ 8 := by
  have hh := shadow_bounds h
  have ho : (2 * i + 1) % 2 ≠ 0 := by omega
  have hd : i + f - (2 * i + 1) / 2 = f := by omega
  rw [if_neg ho, hd] at hh
  exact ⟨hh.1, hh.2.2, shadow_not_eight h⟩

theorem sharp_shadow_attained (i f : Nat) : Shadow (i + f) (2 * i + 1) (5 * 2 ^ f) := by
  have hbase : ∀ i, Shadow i (2 * i + 1) 5 := by
    intro i
    induction i with
    | zero => exact Shadow.odd Shadow.nil (by decide)
    | succ i ih =>
      have h1 := Shadow.even ih
      have h2 := Shadow.odd h1 (show 3 * 7 = 2 * (2 * 5) + 1 by decide)
      have h3 := Shadow.odd h2 (show 3 * 5 = 2 * 7 + 1 by decide)
      have hc : 2 * (i + 1) + 1 = (2 * i + 1) + 1 + 1 := by omega
      rw [hc]
      exact h3
  induction f with
  | zero => simpa using hbase i
  | succ f ih =>
    have hh := Shadow.even ih
    have he : i + (f + 1) = (i + f) + 1 := by omega
    have hp : 5 * 2 ^ (f + 1) = 2 * (5 * 2 ^ f) := by rw [Nat.pow_succ]; omega
    rw [he, hp]
    exact hh

theorem backtrack_split_odd {e o b p : Nat} (h : Backtrack e o b p)
    (L : Nat) (hL : L ≤ o) :
    ∃ a c x, e = a + c ∧ Backtrack a L b x ∧ Backtrack c (o - L) x p := by
  induction h with
  | nil b =>
    have hz : L = 0 := by omega
    subst L
    exact ⟨0, 0, b, rfl, Backtrack.nil b, Backtrack.nil b⟩
  | @even e o b p h ih =>
    obtain ⟨a, c, x, he, ha, hc⟩ := ih hL
    exact ⟨a, c + 1, x, by omega, ha, Backtrack.even hc⟩
  | @odd e o b x p h hp ih =>
    by_cases heq : L = o + 1
    · subst L
      exact ⟨e, 0, p, by omega, Backtrack.odd h hp, by simpa using Backtrack.nil p⟩
    · obtain ⟨a, c, y, he, ha, hc⟩ := ih (by omega)
      have ht : o + 1 - L = (o - L) + 1 := by omega
      refine ⟨a, c, y, he, ha, ?_⟩
      rw [ht]
      exact Backtrack.odd hc hp

theorem cycle_closed (t n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    iterate t n = 1 ∨ iterate t n = 2 ∨ iterate t n = 4 := by
  induction t generalizing n with
  | zero => exact hn
  | succ t ih =>
    apply ih
    rcases hn with hn | hn | hn <;> simp [C, hn]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_small_paths :
    (∀ p : Fin 7, 0 < p.val →
      iterate 8 p.val = 1 ∨ iterate 8 p.val = 2 ∨ iterate 8 p.val = 4) ∧
    (∀ p : Fin 7, ∀ t : Fin 8, iterate t.val p.val ≤ 16) ∧
    (∀ p : Fin 7, ∀ t : Fin 8, ∀ f : Fin 3, ∀ o : Fin 4,
      2 * o.val ≤ t.val →
      3 * 2 ^ f.val ≤ iterate t.val p.val →
      iterate t.val p.val + 5 ≤ 2 ^ (f.val + 3) →
      iterate t.val p.val + 8 ≠ 2 ^ (f.val + 3) →
      3 ^ o.val ≤ 2 ^ (f.val + t.val - o.val)) := by
  decide +kernel

theorem reference_bounds (f m x : Nat) (hm : 5 ≤ m) (hmu : m ≤ 5 * 2 ^ f)
    (hx : x + m = 2 ^ (f + 3)) :
    3 * 2 ^ f ≤ x ∧ x + 5 ≤ 2 ^ (f + 3) ∧
      x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 4 := by
  have hp : 2 ^ (f + 3) = 8 * 2 ^ f := by rw [Nat.pow_add]; omega
  have ht := Nat.two_pow_pos f
  have hl : 3 * 2 ^ f ≤ x := by omega
  refine ⟨hl, by omega, by omega, by omega, ?_⟩
  by_cases hf : f = 0
  · simp only [hf, Nat.pow_zero, Nat.mul_one] at hmu hl
    omega
  · have ht2 : 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ f by omega)
    omega

theorem reference_predecessor {e o p : Nat} (f m x : Nat)
    (hm : 5 ≤ m) (hmu : m ≤ 5 * 2 ^ f) (hm8 : m ≠ 8)
    (hx : x + m = 2 ^ (f + 3)) (h : Backtrack e o x p) :
    3 ≤ p ∧ 3 ^ o ≤ 2 ^ (f + e + o) := by
  have hb := reference_bounds f m x hm hmu hx
  have ht := Nat.two_pow_pos f
  have hxpos : 0 < x := by omega
  have hp := backtrack_positive h hxpos
  have hactual := backtrack_actual h
  have hp3 : 3 ≤ p := by
    apply Classical.byContradiction
    intro hn
    have hcycle := cycle_closed (e + 2 * o) p (show p = 1 ∨ p = 2 ∨ p = 4 by omega)
    rw [hactual] at hcycle
    rcases hcycle with hc | hc | hc <;> omega
  refine ⟨hp3, ?_⟩
  apply Classical.byContradiction
  intro hn
  have hlt : 2 ^ (f + e + o) < 3 ^ o := by omega
  have hs := backtrack_size h
  have hxup : x + 1 ≤ 8 * 2 ^ f := by
    have he : 2 ^ (f + 3) = 8 * 2 ^ f := by rw [Nat.pow_add]; omega
    omega
  have hsmall : 3 ^ o * (p + 1) < 3 ^ o * 8 := by
    calc
      _ ≤ 2 ^ (e + o) * (x + 1) := hs
      _ ≤ 2 ^ (e + o) * (8 * 2 ^ f) := Nat.mul_le_mul_left _ hxup
      _ = 8 * 2 ^ (f + e + o) := by
        simp only [Nat.pow_add]
        ac_rfl
      _ < 8 * 3 ^ o := Nat.mul_lt_mul_of_pos_left hlt (by decide)
      _ = _ := by ac_rfl
  have hp6 : p < 7 := by have hh := Nat.lt_of_mul_lt_mul_left hsmall; omega
  have hc := finite_small_paths.1 ⟨p, hp6⟩ hp
  have htime : e + 2 * o < 8 := by
    apply Classical.byContradiction
    intro hh
    have he : e + 2 * o = 8 + (e + 2 * o - 8) := by omega
    have hcycle := cycle_closed (e + 2 * o - 8) (iterate 8 p) hc
    rw [he, iterate_add] at hactual
    rw [hactual] at hcycle
    rcases hcycle with hc | hc | hc <;> omega
  have hx16 := finite_small_paths.2.1 ⟨p, hp6⟩ ⟨e + 2 * o, htime⟩
  rw [hactual] at hx16
  have hf3 : f < 3 := by
    apply Classical.byContradiction
    intro hh
    have hpow : 8 ≤ 2 ^ f := Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ f by omega)
    omega
  have hfinite := finite_small_paths.2.2 ⟨p, hp6⟩ ⟨e + 2 * o, htime⟩
    ⟨f, hf3⟩ ⟨o, by omega⟩ (show 2 * o ≤ e + 2 * o by omega)
  simp only at hfinite
  rw [hactual] at hfinite
  have hh := hfinite hb.1 hb.2.1 (by omega)
  have he : f + (e + 2 * o) - o = f + e + o := by omega
  rw [he] at hh
  omega

theorem frontier_suffix_lower {e o P : Nat} (s f m x X K q : Nat)
    (hf : f ≤ s) (hm : 5 ≤ m) (hmu : m ≤ 5 * 2 ^ f) (hm8 : m ≠ 8)
    (hx : x + m = 2 ^ f * X) (hX : X = 8 + 3 ^ K * q)
    (hK : 2 * (s + 3) ≤ K) (he : e ≤ s - f)
    (h : Backtrack e o x P) : X ≤ P + 5 := by
  let a := 2 ^ (f + 3) - m
  have hp : 2 ^ (f + 3) = 8 * 2 ^ f := by rw [Nat.pow_add]; omega
  have ha : a + m = 2 ^ (f + 3) := by dsimp [a]; omega
  have hab := reference_bounds f m a hm hmu ha
  have hapos : 0 < a := by have hh := Nat.two_pow_pos f; omega
  have hB : x = a + 3 ^ K * (2 ^ f * q) := by
    have hh : 2 ^ f * X = 2 ^ (f + 3) + 3 ^ K * (2 ^ f * q) := by
      rw [hX, hp]
      grind
    rw [hh] at hx
    omega
  obtain ⟨p, hbase, ho, hP⟩ := inverse_locality h a (f + 3) (s - f) K (2 ^ f * q)
    hapos (by omega) (by omega) he hB
  have hb := reference_predecessor f m a hm hmu hm8 ha hbase
  have hpow : 3 ^ o * 3 ^ (K - o) = 3 ^ K := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hh := Nat.mul_le_mul_right (3 ^ (K - o) * q) hb.2
  have hgain : 3 ^ K * q ≤ 2 ^ (e + o) * 3 ^ (K - o) * (2 ^ f * q) := by
    calc
      _ = 3 ^ o * (3 ^ (K - o) * q) := by rw [← Nat.mul_assoc, hpow]
      _ ≤ 2 ^ (f + e + o) * (3 ^ (K - o) * q) := hh
      _ = _ := by
        rw [show f + e + o = f + (e + o) by omega, Nat.pow_add]
        ac_rfl
  omega

theorem all_target_lower {e o p : Nat} (R i s K q : Nat)
    (hR : R % 2 = 1) (hR3 : 3 ≤ R) (hi : i < R)
    (hX : 8 ^ R = 8 + 3 ^ K * q) (hK : 2 * (s + 3) ≤ K)
    (he : e ≤ i + s) (h : Backtrack e o (hitValue R i) p) :
    blockValue R 0 ≤ p := by
  by_cases ho : o ≤ 2 * i + 1
  · exact before_escape_lower R i hR hR3 hi ho h
  · obtain ⟨a, c, x, hec, hprefix, hsuffix⟩ :=
      backtrack_split_odd h (2 * i + 1) (by omega)
    obtain ⟨m0, hshadow0, _, _, hcount, _, _⟩ :=
      truncated_companion hprefix R i hi (hit_lift R i hi) (by omega)
    have hai : i ≤ a := by omega
    let f := a - i
    have haf : a = i + f := by dsimp [f]; omega
    rw [haf] at hprefix
    obtain ⟨m, hshadow, hm, _, hfront⟩ := escape_frontier R i f hi hprefix
    have hb := frontier_shadow_bound hshadow
    have hfront' : x + m = 2 ^ f * 8 ^ R := by
      rw [hfront, Nat.pow_add, Nat.pow_mul]
      change 8 ^ R * 2 ^ f = _
      ac_rfl
    have hl := frontier_suffix_lower s f m x (8 ^ R) K q
      (by dsimp [f]; omega) hm hb.2.1 hb.2.2 hfront' hX hK
      (by dsimp [f]; omega) hsuffix
    have hn : blockValue R 0 = 8 ^ R - 5 := by
      simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero,
        Nat.pow_zero, Nat.mul_one, Nat.pow_mul]
    rw [hn]
    omega

@[irreducible] def windowPrecision (s : Nat) : Nat := 2 * (s + 3)
@[irreducible] def windowExponent (s h : Nat) : Nat :=
  1 + 2 * 3 ^ windowPrecision s * (h + 1)

theorem window_exponent (s h : Nat) :
    3 ≤ windowExponent s h ∧ windowExponent s h % 2 = 1 ∧ h < windowExponent s h := by
  have hp := Nat.pow_pos (by decide : 0 < 3) (n := windowPrecision s)
  have hh := Nat.mul_le_mul_right (h + 1) (show 1 ≤ 3 ^ windowPrecision s by omega)
  unfold windowExponent
  rw [Nat.mul_assoc]
  constructor
  · omega
  · constructor <;> omega

theorem window_lift (s h : Nat) :
    ∃ q, 8 ^ windowExponent s h = 8 + 3 ^ windowPrecision s * q := by
  obtain ⟨z, hz⟩ := eight_period (windowPrecision s) (h + 1)
  refine ⟨8 * z, ?_⟩
  unfold windowExponent
  rw [Nat.pow_add, hz]
  change 8 * (1 + 3 ^ windowPrecision s * z) = _
  grind

theorem window_exact_minimum (s h i : Nat) (hi : i < windowExponent s h) :
    Backtrack i (2 * i + 1) (hitValue (windowExponent s h) i)
      (blockValue (windowExponent s h) 0) ∧
    ∀ e o p, e ≤ i + s → Backtrack e o (hitValue (windowExponent s h) i) p →
      blockValue (windowExponent s h) 0 ≤ p := by
  have hR := window_exponent s h
  obtain ⟨q, hq⟩ := window_lift s h
  refine ⟨?_, ?_⟩
  · simpa only [Nat.sub_self] using ladder_attained (windowExponent s h) i i hi (by omega)
  · intro e o p he hp
    exact all_target_lower (windowExponent s h) i s (windowPrecision s) q
      hR.2.1 hR.1 hi hq (by unfold windowPrecision; omega) he hp

theorem window_prefix (s h : Nat) :
    let R := windowExponent s h
    MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
    (∀ t, t < 5 * R →
      (iterate t (blockValue R 0) % 27 = 20 ↔ t % 5 = 2 ∧ 0 < t / 5)) ∧
    (∀ i, i < R → iterate (5 * i + 2) (blockValue R 0) = hitValue R i) := by
  dsimp only
  exact ⟨(block_prefix _ _ (by omega)).2,
    fun _ ht => all_hit_positions _ _ (window_exponent s h).2.1 ht,
    fun _ hi => hit_clock _ _ hi⟩

theorem unbounded_whole_window (s L B : Nat) :
    ∃ R, 3 ≤ R ∧ R % 2 = 1 ∧ L < R - 1 ∧ B < blockValue R 0 ∧
      MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      ∀ i, i < R →
        Backtrack i (2 * i + 1) (hitValue R i) (blockValue R 0) ∧
        ∀ e o p, e ≤ i + s → Backtrack e o (hitValue R i) p → blockValue R 0 ≤ p := by
  let h := L + B + 2
  let R := windowExponent s h
  have hR := window_exponent s h
  have hg := MinimumReturnLadder.source_growth R hR.1
  have hlarge : L + B + 2 < R := hR.2.2
  exact ⟨R, hR.1, hR.2.1, by omega, by omega, (window_prefix s h).1,
    fun i hi => window_exact_minimum s h i hi⟩

#print axioms shadow_bounds
#print axioms shadow_not_eight
#print axioms frontier_shadow_bound
#print axioms sharp_shadow_attained
#print axioms backtrack_split_odd
#print axioms cycle_closed
#print axioms finite_small_paths
#print axioms reference_bounds
#print axioms reference_predecessor
#print axioms frontier_suffix_lower
#print axioms all_target_lower
#print axioms window_exponent
#print axioms window_lift
#print axioms window_exact_minimum
#print axioms window_prefix
#print axioms unbounded_whole_window

end MinimumLadderWindow
