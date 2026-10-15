/- A three-even detour supplies smaller coalescing sources beyond the
   return ladder's previous inverse budget. No universal convergence claim. -/
import MinimumReturnLadder

namespace MinimumInverseEscape
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier
open MinimumRootPredecessors MinimumFirstTarget MinimumReturnLadder

theorem odd_meeting (n : Nat) (hn : n % 2 = 1) :
    2 * iterate 2 n = 3 * n + 1 := by
  have h1 : C n = 3 * n + 1 := by unfold C; rw [if_pos hn]
  have h2 : C (3 * n + 1) = (3 * n + 1) / 2 := by unfold C; split <;> omega
  simp only [iterate, h1, h2]
  omega

theorem three_even_detour (n : Nat) (hn : n % 2 = 1) :
    Backtrack 3 1 (iterate 2 n) (8 * n + 2) := by
  have hb := odd_meeting n hn
  have h1 := Backtrack.even (Backtrack.nil (iterate 2 n))
  have h2 := Backtrack.even h1
  have h3 := Backtrack.odd h2
    (show 3 * (4 * n + 1) + 1 = 2 * (2 * (2 * iterate 2 n)) by omega)
  have h4 := Backtrack.even h3
  have he : 2 * (4 * n + 1) = 8 * n + 2 := by omega
  rw [he] at h4
  exact h4

theorem pure_inverse (k q : Nat) (hq : 0 < q) :
    Backtrack 0 k (3 ^ k * q - 1) (2 ^ k * q - 1) := by
  induction k generalizing q with
  | zero => simpa only [Nat.pow_zero, Nat.one_mul] using Backtrack.nil (q - 1)
  | succ k ih =>
    have hp := ih (3 * q) (by omega)
    have h3 : 3 ^ k * (3 * q) = 3 ^ (k + 1) * q := by rw [Nat.pow_succ]; ac_rfl
    rw [h3] at hp
    have hpos := Nat.mul_pos (Nat.two_pow_pos k) hq
    have h2 : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by rw [Nat.pow_succ]; ac_rfl
    have hx : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by ac_rfl
    apply Backtrack.odd hp
    rw [h2, hx]
    omega

theorem detour_predecessor (n j q : Nat) (hn : n % 2 = 1) (hq : 0 < q)
    (he : 3 ^ j * q = 8 * n + 3) :
    Backtrack 3 (j + 1) (iterate 2 n) (2 ^ j * q - 1) := by
  have hp := pure_inverse j q hq
  have hy : 3 ^ j * q - 1 = 8 * n + 2 := by omega
  rw [hy] at hp
  have hc := backtrack_append (three_even_detour n hn) hp
  simpa only [Nat.add_zero, Nat.add_comm] using hc

theorem detour_clock (n j q : Nat) (hn : n % 2 = 1) (hq : 0 < q)
    (he : 3 ^ j * q = 8 * n + 3) :
    iterate (2 * j + 5) (2 ^ j * q - 1) = iterate 2 n := by
  have hh := backtrack_actual (detour_predecessor n j q hn hq he)
  have ht : 3 + 2 * (j + 1) = 2 * j + 5 := by omega
  rw [ht] at hh
  exact hh

theorem six_power_gain (j : Nat) (hj : 6 ≤ j) : 8 * 2 ^ j < 3 ^ j := by
  have he : j = 6 + (j - 6) := by omega
  have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (j - 6)
  have hpos := Nat.pow_pos (by decide : 0 < 3) (n := j - 6)
  rw [he, Nat.pow_add, Nat.pow_add]
  omega

theorem detour_smaller (n j q : Nat) (hj : 6 ≤ j) (hq : 0 < q)
    (he : 3 ^ j * q = 8 * n + 3) : 0 < 2 ^ j * q - 1 ∧ 2 ^ j * q - 1 < n := by
  have hp := Nat.mul_lt_mul_of_pos_right (six_power_gain j hj) hq
  have hmul : 8 * 2 ^ j * q = 8 * (2 ^ j * q) := by ac_rfl
  rw [hmul, he] at hp
  have h2 : 64 ≤ 2 ^ j := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have hq' := Nat.mul_le_mul_left (2 ^ j) hq
  omega

theorem least_detour_exclusion {n : Nat} (hn : LeastCounterexample n) :
    (8 * n + 3) % 729 ≠ 0 := by
  intro hz
  let q := (8 * n + 3) / 729
  have he : 3 ^ 6 * q = 8 * n + 3 := by unfold q; omega
  have hq : 0 < q := by omega
  have ho : n % 2 = 1 := by have hh := least_mod4 hn; omega
  have hs := detour_smaller n 6 q (by decide) hq he
  have hp := least_coalescing_predecessor hn hs.1 (detour_clock n 6 q ho hq he)
  omega

theorem least_not_273_mod_729 {n : Nat} (hn : LeastCounterexample n) : n % 729 ≠ 273 := by
  have hh := least_detour_exclusion hn
  omega

theorem hit_to_initial (R i : Nat) (hi : i < R) :
    Backtrack i (2 * i) (hitValue R i) (hitValue R 0) := by
  induction i with
  | zero => simpa only [Nat.mul_zero] using Backtrack.nil (hitValue R 0)
  | succ i ih =>
    have hp := ih (by omega)
    obtain ⟨u, _, hx, hu⟩ := block_coordinates R i (by omega)
    obtain ⟨v, hv, _, ht⟩ := block_coordinates R (i + 1) hi
    have h0 := Backtrack.odd (Backtrack.nil (hitValue R (i + 1)))
      (show 3 * blockValue R (i + 1) + 1 = 2 * hitValue R (i + 1) by rw [hv, ht]; omega)
    have h1 := Backtrack.even h0
    have h2 := Backtrack.odd h1
      (show 3 * hitValue R i + 1 = 2 * (2 * blockValue R (i + 1)) by rw [hu, hx]; omega)
    have hc := backtrack_append h2 hp
    have hcount : 2 * (i + 1) = 2 + 2 * i := by omega
    rw [hcount]
    simpa only [Nat.add_comm] using hc

def exponent (h : Nat) : Nat := 162 * h + 85
def source (h : Nat) : Nat := 8 ^ exponent h - 5
def quotient (h : Nat) : Nat := (8 ^ (exponent h + 1) - 37) / 729
def predecessor (h : Nat) : Nat := 64 * quotient h - 1

theorem family_exponent (h : Nat) : exponent h % 2 = 1 ∧ 85 ≤ exponent h := by
  unfold exponent
  omega

theorem family_congruence (h : Nat) : 8 ^ (exponent h + 1) % 729 = 37 := by
  have hperiod : 8 ^ 162 % 729 = 1 := by decide +kernel
  have hbase : 8 ^ 86 % 729 = 37 := by decide +kernel
  have he : exponent h + 1 = 162 * h + 86 := by unfold exponent; omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, hperiod, hbase]
  simp

theorem family_lift (h : Nat) : 0 < quotient h ∧ 729 * quotient h = 8 * source h + 3 := by
  have hc := family_congruence h
  have hE := (family_exponent h).2
  have hpow : 4096 ≤ 8 ^ exponent h :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 4 ≤ exponent h by omega)
  have hx : 8 ^ (exponent h + 1) = 8 * 8 ^ exponent h := by rw [Nat.pow_succ, Nat.mul_comm]
  unfold quotient source
  rw [hx]
  rw [hx] at hc
  omega

theorem family_source (h : Nat) : source h = blockValue (exponent h) 0 ∧ source h % 2 = 1 := by
  have he : 2 ^ (3 * exponent h) = 8 ^ exponent h := by rw [Nat.pow_mul]
  have hpos := (family_exponent h).2
  have hp : 8 ^ exponent h % 2 = 0 := by
    have hx : exponent h = (exponent h - 1) + 1 := by omega
    rw [hx, Nat.pow_succ, Nat.mul_mod]
    simp
  have hlarge : 8 ≤ 8 ^ exponent h :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ exponent h by omega)
  simp only [source, blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, he]
  simp only [true_and]
  omega

theorem family_smaller (h : Nat) : 0 < predecessor h ∧ predecessor h < source h := by
  have hl := family_lift h
  exact detour_smaller (source h) 6 (quotient h) (by decide) hl.1 (by omega)

theorem family_coalescence (h : Nat) : iterate 17 (predecessor h) = iterate 2 (source h) := by
  have hl := family_lift h
  exact detour_clock (source h) 6 (quotient h) (family_source h).2 hl.1 (by omega)

theorem family_later_inverse (h i : Nat) (hi : i < exponent h) :
    Backtrack (i + 3) (2 * i + 7) (hitValue (exponent h) i) (predecessor h) := by
  have hl := family_lift h
  have hp := detour_predecessor (source h) 6 (quotient h) (family_source h).2 hl.1 (by omega)
  have hs : iterate 2 (source h) = hitValue (exponent h) 0 := by
    rw [(family_source h).1]
    exact hit_clock (exponent h) 0 (by have hh := (family_exponent h).2; omega)
  rw [hs] at hp
  exact backtrack_append (hit_to_initial (exponent h) i hi) hp

theorem family_later_clock (h i : Nat) (hi : i < exponent h) :
    iterate (5 * i + 17) (predecessor h) = hitValue (exponent h) i := by
  have hp := backtrack_actual (family_later_inverse h i hi)
  have ht : i + 3 + 2 * (2 * i + 7) = 5 * i + 17 := by omega
  rw [ht] at hp
  exact hp

theorem family_not_least (h : Nat) : ¬ LeastCounterexample (source h) := by
  intro ha
  have hs := family_smaller h
  have hp := least_coalescing_predecessor ha hs.1 (family_coalescence h)
  omega

theorem family_growth (h : Nat) : h < source h := by
  have hx := MinimumReturnLadder.source_growth (exponent h)
    (by have hh := (family_exponent h).2; omega)
  rw [← (family_source h).1] at hx
  unfold exponent at hx
  omega

inductive Shadow : Nat → Nat → Nat → Prop
  | nil : Shadow 0 0 7
  | even {e o m : Nat} : Shadow e o m → Shadow (e + 1) o (2 * m)
  | odd {e o m z : Nat} : Shadow e o m → 3 * z = 2 * m + 1 → Shadow e (o + 1) z

def negativeStep (m : Nat) : Nat := if m % 2 = 1 then (3 * m - 1) / 2 else m / 2
def negativeIter : Nat → Nat → Nat
  | 0, m => m
  | k + 1, m => negativeIter k (negativeStep m)
def negativeOdds : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, m => (if m % 2 = 1 then 1 else 0) + negativeOdds k (negativeStep m)

theorem shadow_actual {e o m : Nat} (h : Shadow e o m) :
    negativeIter (e + o) m = 7 ∧ negativeOdds (e + o) m = o := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | @even e o m h ih =>
    have hs : negativeStep (2 * m) = m := by unfold negativeStep; split <;> omega
    have hp : (2 * m) % 2 ≠ 1 := by omega
    have he : e + 1 + o = (e + o) + 1 := by omega
    simp only [he, negativeIter, negativeOdds, if_neg hp, hs, ih.1, ih.2, Nat.zero_add, and_self]
  | @odd e o m z h hz ih =>
    have hp : z % 2 = 1 := by omega
    have hs : negativeStep z = m := by unfold negativeStep; rw [if_pos hp]; omega
    have he : e + (o + 1) = (e + o) + 1 := by omega
    rw [he]
    change negativeIter (e + o) (negativeStep z) = 7 ∧
      (if z % 2 = 1 then 1 else 0) + negativeOdds (e + o) (negativeStep z) = o + 1
    rw [hs, if_pos hp, ih.1, ih.2]
    simp only [true_and]
    omega

theorem truncated_companion {e o b p : Nat} (h : Backtrack e o b p)
    (R i : Nat) (_hi : i < R)
    (hb : b + 7 = 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1)) (hoL : o ≤ 2 * i + 1) :
    ∃ m, Shadow e o m ∧ 5 ≤ m ∧ m ≤ 7 * 2 ^ e ∧ o ≤ 2 * e + 1 ∧
      2 ^ (2 * e + 1 - o) * (m - 1) ≤ 4 * 3 ^ (2 * e + 1 - o) ∧
      3 ^ o * (p + m) = 2 ^ (e + o) * (b + 7) := by
  induction h with
  | nil b => exact ⟨7, Shadow.nil, by decide, by decide, by decide, by decide, by simp⟩
  | @even e o b x h ih =>
    obtain ⟨m, hsh, hm, hmup, ho, hsize, hid⟩ := ih hb hoL
    have hd : 2 * (e + 1) + 1 - o = (2 * e + 1 - o) + 2 := by omega
    refine ⟨2 * m, Shadow.even hsh, by omega, ?_, by omega, ?_, ?_⟩
    · rw [Nat.pow_succ]
      omega
    · rw [hd]
      exact companion_even _ _ hm hsize
    · have hc := congrArg (fun a => 2 * a) hid
      have ht : e + 1 + o = (e + o) + 1 := by omega
      rw [ht, Nat.pow_succ]
      grind
  | @odd e o b x p h hp ih =>
    obtain ⟨m, hsh, hm, hmup, ho, hsize, hid⟩ := ih hb (by omega)
    have hx : x % 3 = 2 := by omega
    have hol : o < 2 * i + 1 := by omega
    have h3 : 3 ^ (2 * i + 1) = 3 ^ o * 3 ^ (2 * i + 1 - o) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hh : 3 ^ o * (x + m) = 3 ^ o *
        (2 ^ (e + o) * 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1 - o)) := by
      rw [hb, h3] at hid
      calc
        _ = _ := hid
        _ = _ := by ac_rfl
    have hc := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
    have hp3 : 3 ^ (2 * i + 1 - o) % 3 = 0 := by
      have hd : 2 * i + 1 - o = (2 * i - o) + 1 := by omega
      rw [hd, Nat.pow_succ, Nat.mul_mod]
      simp
    have hxm : (x + m) % 3 = 0 := by rw [hc, Nat.mul_mod, hp3]; simp
    have hdiv : 3 * ((2 * m + 1) / 3) = 2 * m + 1 := by omega
    have hs := companion_odd (2 * e + 1 - o) m ((2 * m + 1) / 3) hm hdiv hsize
    have hd : 2 * e + 1 - (o + 1) = (2 * e + 1 - o) - 1 := by omega
    refine ⟨(2 * m + 1) / 3, Shadow.odd hsh hdiv, hs.2.1, by omega, by omega, ?_, ?_⟩
    · rw [hd]
      exact hs.2.2.2
    · have hsum : 3 * (p + (2 * m + 1) / 3) = 2 * (x + m) := by omega
      rw [Nat.pow_succ, ← Nat.add_assoc, Nat.pow_succ]
      calc
        _ = 3 ^ o * (3 * (p + (2 * m + 1) / 3)) := by ac_rfl
        _ = 3 ^ o * (2 * (x + m)) := by rw [hsum]
        _ = 2 * (3 ^ o * (x + m)) := by ac_rfl
        _ = _ := by rw [hid]; ac_rfl

theorem before_escape_lower {e o p : Nat} (R i : Nat) (hR : R % 2 = 1)
    (hR3 : 3 ≤ R) (hi : i < R) (hoL : o ≤ 2 * i + 1)
    (h : Backtrack e o (hitValue R i) p) : blockValue R 0 ≤ p := by
  by_cases hei : e ≤ i
  · have hl := inverse_ladder_lower R i hR hi hei h
    exact Nat.le_trans (block_monotone R 0 (i - e) (by omega) (by omega)) hl
  · obtain ⟨m, _, _, hmup, _, _, hid⟩ :=
      truncated_companion h R i hi (hit_lift R i hi) hoL
    have h3 : 3 ^ (2 * i + 1) = 3 ^ o * 3 ^ (2 * i + 1 - o) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hh : 3 ^ o * (p + m) = 3 ^ o *
        (2 ^ (e + o) * 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1 - o)) := by
      rw [hit_lift R i hi, h3] at hid
      calc
        _ = _ := hid
        _ = _ := by ac_rfl
    have hc := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
    have hratio := Nat.mul_le_mul_left (2 ^ (e + o) * 2 ^ (3 * (R - i) - 1))
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (2 * i + 1 - o))
    rw [← hc, ← Nat.pow_add, ← Nat.pow_add] at hratio
    have he : e + o + (3 * (R - i) - 1) + (2 * i + 1 - o) = (e - i) + 3 * R := by omega
    rw [he, Nat.pow_add] at hratio
    have hp : 2 ^ (i + 4) ≤ 2 ^ (3 * R) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    rw [Nat.pow_add] at hp
    have h14 : 14 * 2 ^ i ≤ 2 ^ (3 * R) := by omega
    have hmul := Nat.mul_le_mul_left (2 ^ (e - i)) h14
    have hpow : 2 ^ (e - i) * 2 ^ i = 2 ^ e := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hm2 : 14 * 2 ^ e ≤ 2 ^ (e - i) * 2 ^ (3 * R) := by
      calc
        _ = 2 ^ (e - i) * (14 * 2 ^ i) := by rw [← hpow]; ac_rfl
        _ ≤ _ := hmul
    have hA : 2 ≤ 2 ^ (e - i) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ e - i by omega)
    have hAX := Nat.mul_le_mul_right (2 ^ (3 * R)) hA
    simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    omega

theorem smaller_requires_escape {e o p : Nat} (R i : Nat) (hR : R % 2 = 1)
    (hR3 : 3 ≤ R) (hi : i < R) (h : Backtrack e o (hitValue R i) p)
    (hp : p < blockValue R 0) : 2 * i + 1 < o := by
  by_cases ho : o ≤ 2 * i + 1
  · have hh := before_escape_lower R i hR hR3 hi ho h
    omega
  · omega

theorem escape_frontier {p : Nat} (R i f : Nat) (hi : i < R)
    (h : Backtrack (i + f) (2 * i + 1) (hitValue R i) p) :
    ∃ m, Shadow (i + f) (2 * i + 1) m ∧ 5 ≤ m ∧
      4 ^ f * (m - 1) ≤ 4 * 9 ^ f ∧ p + m = 2 ^ (3 * R + f) := by
  obtain ⟨m, hsh, hm, _, _, hs, hid⟩ :=
    truncated_companion h R i hi (hit_lift R i hi) (by omega)
  have hd : 2 * (i + f) + 1 - (2 * i + 1) = 2 * f := by omega
  rw [hd, Nat.pow_mul, Nat.pow_mul] at hs
  have hh : 3 ^ (2 * i + 1) * (p + m) = 3 ^ (2 * i + 1) *
      (2 ^ (i + f + (2 * i + 1)) * 2 ^ (3 * (R - i) - 1)) := by
    rw [hit_lift R i hi] at hid
    calc
      _ = _ := hid
      _ = _ := by ac_rfl
  have hc := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
  rw [← Nat.pow_add] at hc
  have ht : i + f + (2 * i + 1) + (3 * (R - i) - 1) = 3 * R + f := by omega
  rw [ht] at hc
  exact ⟨m, hsh, hm, hs, hc⟩

theorem finite_negative_cycles :
    negativeIter 1 1 = 1 ∧ negativeIter 3 7 = 7 ∧ negativeOdds 3 7 = 2 ∧
    (∀ t : Fin 3, negativeIter t.val 7 = 7 ↔ t.val = 0) ∧
    negativeIter 11 17 = 17 ∧ (∀ t : Fin 11, negativeIter t.val 17 ≠ 7) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finite_escape_witness :
    iterate 17 5311 = iterate 2 7563 ∧ 5311 < 7563 ∧
    exponent 0 = 85 ∧ source 0 = 8 ^ 85 - 5 ∧ predecessor 0 < source 0 ∧
    iterate 17 (predecessor 0) = iterate 2 (source 0) ∧
    iterate 22 (predecessor 0) = hitValue 85 1 ∧
    ReachesOne 7563 ∧ ReachesOne 5311 ∧ ReachesOne (source 0) ∧ ReachesOne (predecessor 0) := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨83, by decide +kernel⟩, ⟨98, by decide +kernel⟩,
    ⟨2119, by decide +kernel⟩, ⟨2134, by decide +kernel⟩⟩

end MinimumInverseEscape

#print axioms MinimumInverseEscape.odd_meeting
#print axioms MinimumInverseEscape.three_even_detour
#print axioms MinimumInverseEscape.pure_inverse
#print axioms MinimumInverseEscape.detour_predecessor
#print axioms MinimumInverseEscape.detour_clock
#print axioms MinimumInverseEscape.six_power_gain
#print axioms MinimumInverseEscape.detour_smaller
#print axioms MinimumInverseEscape.least_detour_exclusion
#print axioms MinimumInverseEscape.least_not_273_mod_729
#print axioms MinimumInverseEscape.hit_to_initial
#print axioms MinimumInverseEscape.family_exponent
#print axioms MinimumInverseEscape.family_congruence
#print axioms MinimumInverseEscape.family_lift
#print axioms MinimumInverseEscape.family_source
#print axioms MinimumInverseEscape.family_smaller
#print axioms MinimumInverseEscape.family_coalescence
#print axioms MinimumInverseEscape.family_later_inverse
#print axioms MinimumInverseEscape.family_later_clock
#print axioms MinimumInverseEscape.family_not_least
#print axioms MinimumInverseEscape.family_growth
#print axioms MinimumInverseEscape.shadow_actual
#print axioms MinimumInverseEscape.truncated_companion
#print axioms MinimumInverseEscape.before_escape_lower
#print axioms MinimumInverseEscape.smaller_requires_escape
#print axioms MinimumInverseEscape.escape_frontier
#print axioms MinimumInverseEscape.finite_negative_cycles
#print axioms MinimumInverseEscape.finite_escape_witness
