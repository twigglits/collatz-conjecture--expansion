/- Exact bounded-even inverse minima along repeated growing OO E blocks.
   Negative companions are arithmetic bookkeeping, not positive orbits. -/
import MinimumFirstTarget

namespace MinimumReturnLadder
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier
open MinimumMixedAncestry MinimumFirstTarget

inductive Backtrack : Nat → Nat → Nat → Nat → Prop
  | nil (b : Nat) : Backtrack 0 0 b b
  | even {e o b x : Nat} : Backtrack e o b x → Backtrack (e + 1) o b (2 * x)
  | odd {e o b x p : Nat} : Backtrack e o b x →
      3 * p + 1 = 2 * x → Backtrack e (o + 1) b p

theorem backtrack_actual {e o b p : Nat} (h : Backtrack e o b p) :
    iterate (e + 2 * o) p = b := by
  induction h with
  | nil b => rfl
  | @even e o b x h ih =>
    have ht : e + 1 + 2 * o = 1 + (e + 2 * o) := by omega
    rw [ht, iterate_add]
    simpa only [iterate, even_step] using ih
  | @odd e o b x p h hp ih =>
    have hodd : p % 2 = 1 := by omega
    have he : iterate 2 p = x := by
      change C (C p) = x
      unfold C
      rw [if_pos hodd, hp]
      split <;> omega
    have ht : e + 2 * (o + 1) = 2 + (e + 2 * o) := by omega
    rw [ht, iterate_add, he]
    exact ih

theorem companion_even (d m : Nat) (hm : 5 ≤ m)
    (hh : 2 ^ d * (m - 1) ≤ 4 * 3 ^ d) :
    2 ^ (d + 2) * (2 * m - 1) ≤ 4 * 3 ^ (d + 2) := by
  have h1 := Nat.mul_le_mul_left (2 ^ d)
    (show 4 * (2 * m - 1) ≤ 9 * (m - 1) by omega)
  have h2 := Nat.mul_le_mul_left 9 hh
  simp only [Nat.pow_add] at *
  grind

theorem companion_odd (d m z : Nat) (hm : 5 ≤ m)
    (hz : 3 * z = 2 * m + 1)
    (hh : 2 ^ d * (m - 1) ≤ 4 * 3 ^ d) :
    0 < d ∧ 5 ≤ z ∧ z ≤ m ∧
    2 ^ (d - 1) * (z - 1) ≤ 4 * 3 ^ (d - 1) := by
  have hm7 : 7 ≤ m := by omega
  have hd : 0 < d := by
    by_cases he : d = 0
    · simp only [he, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at hh
      omega
    · omega
  refine ⟨hd, by omega, by omega, ?_⟩
  have he : d = (d - 1) + 1 := by omega
  rw [he, Nat.pow_succ, Nat.pow_succ] at hh
  have hrel : 3 * (z - 1) = 2 * (m - 1) := by omega
  have ht : 3 * (2 ^ (d - 1) * (z - 1)) ≤ 3 * (4 * 3 ^ (d - 1)) := by
    calc
      _ = 2 ^ (d - 1) * (3 * (z - 1)) := by ac_rfl
      _ = 2 ^ (d - 1) * (2 * (m - 1)) := by rw [hrel]
      _ = 2 ^ (d - 1) * 2 * (m - 1) := by ac_rfl
      _ ≤ _ := by omega
  omega

theorem odd_power_residue (R : Nat) (hR : R % 2 = 1) :
    2 ^ (3 * R) % 3 = 2 := by
  have he : 3 * R = 2 * (3 * (R / 2) + 1) + 1 := by omega
  rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
  simp

theorem odd_budget_gap (d : Nat) (hd : 0 < d) : 3 * 2 ^ d ≤ 2 * 3 ^ d := by
  have he : d = (d - 1) + 1 := by omega
  have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (d - 1)
  rw [he, Nat.pow_succ, Nat.pow_succ]
  omega

theorem offset_buffer (e : Nat) : 14 * 2 ^ e ≤ 2 ^ (3 * (e + 1)) + 10 := by
  induction e with
  | zero => decide
  | succ e ih =>
    have hp : 8 ≤ 2 ^ (3 * (e + 1)) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ 3 * (e + 1) by omega)
    have he : 3 * (e + 1 + 1) = 3 * (e + 1) + 3 := by omega
    rw [Nat.pow_succ, he, Nat.pow_add]
    omega

theorem companion {e o b p : Nat} (h : Backtrack e o b p)
    (R i : Nat) (hR : R % 2 = 1) (hi : i < R)
    (hb : b + 7 = 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1)) (he : e ≤ i) :
    ∃ m, 5 ≤ m ∧ m ≤ 7 * 2 ^ e ∧ o ≤ 2 * e + 1 ∧
      2 ^ (2 * e + 1 - o) * (m - 1) ≤ 4 * 3 ^ (2 * e + 1 - o) ∧
      3 ^ o * (p + m) = 2 ^ (e + o) * (b + 7) := by
  induction h with
  | nil b => exact ⟨7, by decide, by decide, by decide, by decide, by simp⟩
  | @even e o b x h ih =>
    obtain ⟨m, hm, hmup, ho, hsize, hid⟩ := ih hb (by omega)
    have hd : 2 * (e + 1) + 1 - o = (2 * e + 1 - o) + 2 := by omega
    refine ⟨2 * m, by omega, ?_, by omega, ?_, ?_⟩
    · rw [Nat.pow_succ]
      omega
    · rw [hd]
      exact companion_even _ _ hm hsize
    · have hc := congrArg (fun a => 2 * a) hid
      have ht : e + 1 + o = (e + o) + 1 := by omega
      rw [ht, Nat.pow_succ]
      grind
  | @odd e o b x p h hp ih =>
    obtain ⟨m, hm, hmup, ho, hsize, hid⟩ := ih hb he
    have hx : x % 3 = 2 := by omega
    have hol : o < 2 * i + 1 := by
      by_cases heq : o = 2 * i + 1
      · have hei : e = i := by omega
        have hd : 2 * e + 1 - o = 0 := by omega
        rw [hd] at hsize
        simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one] at hsize
        have hmf : m = 5 := by omega
        rw [hmf, hb] at hid
        have hpow : 3 ^ (2 * i + 1) = 3 ^ o := by rw [heq]
        rw [hpow] at hid
        have hh : 3 ^ o * (x + 5) = 3 ^ o *
            (2 ^ (e + o) * 2 ^ (3 * (R - i) - 1)) := by
          calc
            _ = _ := hid
            _ = _ := by ac_rfl
        have hc := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
        rw [← Nat.pow_add] at hc
        have ht : e + o + (3 * (R - i) - 1) = 3 * R := by omega
        rw [ht] at hc
        have hr := odd_power_residue R hR
        omega
      · omega
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
    refine ⟨(2 * m + 1) / 3, hs.2.1, by omega, by omega, ?_, ?_⟩
    · rw [hd]
      exact hs.2.2.2
    · have hsum : 3 * (p + (2 * m + 1) / 3) = 2 * (x + m) := by omega
      rw [Nat.pow_succ, ← Nat.add_assoc, Nat.pow_succ]
      calc
        _ = 3 ^ o * (3 * (p + (2 * m + 1) / 3)) := by ac_rfl
        _ = 3 ^ o * (2 * (x + m)) := by rw [hsum]
        _ = 2 * (3 ^ o * (x + m)) := by ac_rfl
        _ = _ := by rw [hid]; ac_rfl

def blockProduct (R i : Nat) : Nat := 2 ^ (3 * (R - i)) * 3 ^ (2 * i)
def blockValue (R i : Nat) : Nat := blockProduct R i - 5
def hitValue (R i : Nat) : Nat := 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1) - 7

theorem product_lower (R i : Nat) (hi : i < R) : 8 ≤ blockProduct R i := by
  have h2 : 8 ≤ 2 ^ (3 * (R - i)) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 3 ≤ 3 * (R - i) by omega)
  have h3 := Nat.pow_pos (by decide : 0 < 3) (n := 2 * i)
  have hp := Nat.mul_le_mul_left (2 ^ (3 * (R - i))) h3
  unfold blockProduct
  omega

theorem hit_lift (R i : Nat) (hi : i < R) :
    hitValue R i + 7 = 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1) := by
  have h2 : 4 ≤ 2 ^ (3 * (R - i) - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ 3 * (R - i) - 1 by omega)
  have h3 : 3 ≤ 3 ^ (2 * i + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ 2 * i + 1 by omega)
  have hp := Nat.mul_le_mul h2 h3
  unfold hitValue
  omega

theorem scaled_companion (R i e o p m : Nat) (hi : i < R) (he : e ≤ i)
    (ho : o ≤ 2 * e + 1)
    (hid : 3 ^ o * (p + m) = 2 ^ (e + o) *
      (2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1))) :
    2 ^ (2 * e + 1 - o) * (p + m) =
      3 ^ (2 * e + 1 - o) * blockProduct R (i - e) := by
  have h2 : 2 ^ (2 * e + 1 - o) * 2 ^ (e + o) * 2 ^ (3 * (R - i) - 1) =
      2 ^ (3 * (R - (i - e))) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have h3 : 3 ^ o * 3 ^ (2 * e + 1 - o) * 3 ^ (2 * (i - e)) = 3 ^ (2 * i + 1) := by
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  have hc : 3 ^ o * (2 ^ (2 * e + 1 - o) * (p + m)) =
      3 ^ o * (3 ^ (2 * e + 1 - o) * blockProduct R (i - e)) := by
    unfold blockProduct
    calc
      _ = 2 ^ (2 * e + 1 - o) * (3 ^ o * (p + m)) := by ac_rfl
      _ = (2 ^ (2 * e + 1 - o) * 2 ^ (e + o) * 2 ^ (3 * (R - i) - 1)) *
          3 ^ (2 * i + 1) := by rw [hid]; ac_rfl
      _ = _ := by rw [h2, ← h3]; ac_rfl
  exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hc

theorem inverse_ladder_lower {e o p : Nat} (R i : Nat) (hR : R % 2 = 1)
    (hi : i < R) (he : e ≤ i) (h : Backtrack e o (hitValue R i) p) :
    blockValue R (i - e) ≤ p := by
  obtain ⟨m, hm, hmup, ho, hsize, hid⟩ := companion h R i hR hi (hit_lift R i hi) he
  rw [hit_lift R i hi] at hid
  have hs := scaled_companion R i e o p m hi he ho hid
  by_cases hd : 2 * e + 1 - o = 0
  · rw [hd] at hs hsize
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_one] at hs hsize
    unfold blockValue
    omega
  · have hgap := odd_budget_gap (2 * e + 1 - o) (by omega)
    have hmul := Nat.mul_le_mul_right (blockProduct R (i - e)) hgap
    have hh : 2 ^ (2 * e + 1 - o) * (3 * blockProduct R (i - e)) ≤
        2 ^ (2 * e + 1 - o) * (2 * (p + m)) := by
      calc
        _ = (3 * 2 ^ (2 * e + 1 - o)) * blockProduct R (i - e) := by ac_rfl
        _ ≤ (2 * 3 ^ (2 * e + 1 - o)) * blockProduct R (i - e) := hmul
        _ = 2 * (3 ^ (2 * e + 1 - o) * blockProduct R (i - e)) := by ac_rfl
        _ = _ := by rw [← hs]; ac_rfl
    have hbound := Nat.le_of_mul_le_mul_left hh (Nat.two_pow_pos _)
    have hpow : 2 ^ (3 * (e + 1)) ≤ 2 ^ (3 * (R - (i - e))) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
    have h3 := Nat.pow_pos (by decide : 0 < 3) (n := 2 * (i - e))
    have hprod := Nat.mul_le_mul hpow h3
    have hb := offset_buffer e
    unfold blockProduct at hprod
    have hp : 2 ^ (3 * (e + 1)) ≤ blockProduct R (i - e) := by
      simpa only [Nat.mul_one, blockProduct] using hprod
    unfold blockValue
    omega


theorem product_monotone (R i j : Nat) (hij : i ≤ j) (hj : j ≤ R) :
    blockProduct R i ≤ blockProduct R j := by
  have h2 : 2 ^ (3 * (R - i)) = 2 ^ (3 * (R - j)) * 2 ^ (3 * (j - i)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have h3 : 3 ^ (2 * j) = 3 ^ (2 * i) * 3 ^ (2 * (j - i)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hp : 2 ^ (3 * (j - i)) ≤ 3 ^ (2 * (j - i)) := by
    simp only [Nat.pow_mul]
    exact Nat.pow_le_pow_left (by decide : 8 ≤ 9) (j - i)
  calc
    blockProduct R i = (2 ^ (3 * (R - j)) * 3 ^ (2 * i)) * 2 ^ (3 * (j - i)) := by
      unfold blockProduct
      rw [h2]
      ac_rfl
    _ ≤ (2 ^ (3 * (R - j)) * 3 ^ (2 * i)) * 3 ^ (2 * (j - i)) := Nat.mul_le_mul_left _ hp
    _ = blockProduct R j := by unfold blockProduct; rw [h3]; ac_rfl

theorem block_monotone (R i j : Nat) (hij : i ≤ j) (hj : j ≤ R) :
    blockValue R i ≤ blockValue R j :=
  Nat.sub_le_sub_right (product_monotone R i j hij hj) 5

theorem bounded_inverse_lower {e o p : Nat} (R i r : Nat) (hR : R % 2 = 1)
    (hi : i < R) (hr : r ≤ i) (he : e ≤ r)
    (h : Backtrack e o (hitValue R i) p) : blockValue R (i - r) ≤ p := by
  have hl := inverse_ladder_lower R i hR hi (by omega) h
  exact Nat.le_trans (block_monotone R (i - r) (i - e) (by omega) (by omega)) hl

theorem backtrack_append {e o b x f a p : Nat}
    (h : Backtrack e o b x) (g : Backtrack f a x p) :
    Backtrack (e + f) (o + a) b p := by
  induction g with
  | nil x => simpa using h
  | even g ih => simpa only [← Nat.add_assoc] using Backtrack.even (ih h)
  | odd g hp ih => simpa only [← Nat.add_assoc] using Backtrack.odd (ih h) hp

theorem five_block (u : Nat) :
    iterate 1 (8 * u + 3) = 24 * u + 10 ∧
    iterate 2 (8 * u + 3) = 12 * u + 5 ∧
    iterate 3 (8 * u + 3) = 36 * u + 16 ∧
    iterate 4 (8 * u + 3) = 18 * u + 8 ∧
    iterate 5 (8 * u + 3) = 9 * u + 4 ∧
    prefixMinimum 5 (8 * u + 3) = 8 * u + 3 := by
  have h1 : C (8 * u + 3) = 24 * u + 10 := by unfold C; split <;> omega
  have h2 : C (24 * u + 10) = 12 * u + 5 := by unfold C; split <;> omega
  have h3 : C (12 * u + 5) = 36 * u + 16 := by unfold C; split <;> omega
  have h4 : C (36 * u + 16) = 18 * u + 8 := by unfold C; split <;> omega
  have h5 : C (18 * u + 8) = 9 * u + 4 := by unfold C; split <;> omega
  simp only [iterate, prefixMinimum, h1, h2, h3, h4, h5]
  simp only [true_and]
  omega

theorem five_block_inverse (u : Nat) : Backtrack 1 2 (9 * u + 4) (8 * u + 3) := by
  have h0 := Backtrack.even (Backtrack.nil (9 * u + 4))
  have h1 := Backtrack.odd h0 (show 3 * (12 * u + 5) + 1 = 2 * (2 * (9 * u + 4)) by omega)
  exact Backtrack.odd h1 (by omega)

theorem block_coordinates (R i : Nat) (hi : i < R) :
    ∃ u, blockValue R i = 8 * u + 3 ∧ blockValue R (i + 1) = 9 * u + 4 ∧
      hitValue R i = 12 * u + 5 := by
  let q := 2 ^ (3 * (R - (i + 1))) * 3 ^ (2 * i)
  have hq : 0 < q := Nat.mul_pos (Nat.two_pow_pos _) (Nat.pow_pos (by decide : 0 < 3))
  have he : 3 * (R - i) = 3 * (R - (i + 1)) + 3 := by omega
  have hp : blockProduct R i = 8 * q := by
    unfold blockProduct q
    rw [he, Nat.pow_add]
    grind
  have he' : 2 * (i + 1) = 2 * i + 2 := by omega
  have hp' : blockProduct R (i + 1) = 9 * q := by
    unfold blockProduct q
    rw [he', Nat.pow_add]
    grind
  have he2 : 3 * (R - i) - 1 = 3 * (R - (i + 1)) + 2 := by omega
  have ht := hit_lift R i hi
  have hh : 2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i + 1) = 12 * q := by
    unfold q
    rw [he2, Nat.pow_add, Nat.pow_succ]
    grind
  rw [hh] at ht
  refine ⟨q - 1, ?_, ?_, ?_⟩
  · unfold blockValue
    rw [hp]
    omega
  · unfold blockValue
    rw [hp']
    omega
  · omega

theorem block_prefix (R i : Nat) (hi : i ≤ R) :
    iterate (5 * i) (blockValue R 0) = blockValue R i ∧
    prefixMinimum (5 * i) (blockValue R 0) = blockValue R 0 := by
  induction i with
  | zero => simp only [iterate, prefixMinimum, and_self]
  | succ i ih =>
    have hp := ih (by omega)
    obtain ⟨u, hu, hv, _⟩ := block_coordinates R i (by omega)
    have hb := five_block u
    have hm := block_monotone R 0 i (by omega) (by omega)
    have he : 5 * (i + 1) = 5 * i + 5 := by omega
    rw [he, iterate_add, prefix_concatenation, hp.1, hp.2, hu, hb.2.2.2.2.1, hb.2.2.2.2.2]
    rw [hu] at hm
    omega

theorem ladder_attained (R i r : Nat) (hi : i < R) (hr : r ≤ i) :
    Backtrack r (2 * r + 1) (hitValue R i) (blockValue R (i - r)) := by
  have hp : Backtrack 0 1 (hitValue R i) (blockValue R i) := by
    obtain ⟨u, hu, _, ht⟩ := block_coordinates R i hi
    apply Backtrack.odd (Backtrack.nil _)
    rw [hu, ht]
    omega
  have hb : ∀ s, s ≤ i → Backtrack s (2 * s + 1) (hitValue R i) (blockValue R (i - s)) := by
    intro s
    induction s with
    | zero => simpa using hp
    | succ s ih =>
      intro hs
      have hprev := ih (by omega)
      obtain ⟨u, hu, hv, _⟩ := block_coordinates R (i - (s + 1)) (by omega)
      have he : i - (s + 1) + 1 = i - s := by omega
      rw [he] at hv
      have hg := five_block_inverse u
      rw [← hu, ← hv] at hg
      have hc := backtrack_append hprev hg
      have ha : 2 * (s + 1) + 1 = 2 * s + 1 + 2 := by omega
      rw [ha]
      exact hc
  exact hb r hr

theorem hit_clock (R i : Nat) (hi : i < R) :
    iterate (5 * i + 2) (blockValue R 0) = hitValue R i := by
  obtain ⟨u, hu, _, ht⟩ := block_coordinates R i hi
  rw [iterate_add, (block_prefix R i (by omega)).1, hu, (five_block u).2.1, ht]

theorem hit_residue (R i : Nat) (hi : i < R) (hi1 : 1 ≤ i) : hitValue R i % 27 = 20 := by
  have he : 2 * i + 1 = (2 * i - 2) + 3 := by omega
  have ht := hit_lift R i hi
  rw [he, Nat.pow_add] at ht
  have hfac : 2 ^ (3 * (R - i) - 1) * (3 ^ (2 * i - 2) * 3 ^ 3) =
      27 * (2 ^ (3 * (R - i) - 1) * 3 ^ (2 * i - 2)) := by
    change 2 ^ _ * (3 ^ _ * 27) = _
    ac_rfl
  rw [hfac] at ht
  omega

theorem block_residues (R i : Nat) (hR : R % 2 = 1) (hi : i < R) :
    (i = 0 → blockValue R i % 9 = 3) ∧
    (0 < i → blockValue R i % 9 = 4) := by
  have hl := product_lower R i hi
  constructor
  · intro hiz
    subst i
    have he : 3 * R = 6 * (R / 2) + 3 := by omega
    have hp : 2 ^ (3 * R) % 9 = 8 := by
      rw [he, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      simp
    simp only [blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one] at hl
    simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    omega
  · intro hi0
    have he : 2 * i = (2 * i - 2) + 2 := by omega
    have hp : blockProduct R i % 9 = 0 := by
      unfold blockProduct
      rw [he, Nat.pow_add, Nat.mul_mod, Nat.mul_mod]
      simp
    unfold blockValue
    omega

theorem block_hit_positions (u t : Nat) (ht : t < 5)
    (hu : (8 * u + 3) % 9 = 3 ∨ (8 * u + 3) % 9 = 4) :
    iterate t (8 * u + 3) % 27 = 20 ↔ t = 2 ∧ (8 * u + 3) % 9 = 4 := by
  have hb := five_block u
  have hh : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · change (8 * u + 3) % 27 = 20 ↔ _
    omega
  · rw [hb.1]
    omega
  · rw [hb.2.1]
    omega
  · rw [hb.2.2.1]
    omega
  · rw [hb.2.2.2.1]
    omega

theorem all_hit_positions (R t : Nat) (hR : R % 2 = 1) (ht : t < 5 * R) :
    iterate t (blockValue R 0) % 27 = 20 ↔ t % 5 = 2 ∧ 0 < t / 5 := by
  have hi : t / 5 < R := by omega
  have hp := block_prefix R (t / 5) (by omega)
  obtain ⟨u, hu, _, _⟩ := block_coordinates R (t / 5) hi
  have hr := block_residues R (t / 5) hR hi
  have h9 : (8 * u + 3) % 9 = 3 ∨ (8 * u + 3) % 9 = 4 := by
    by_cases hz : t / 5 = 0
    · have hh := hr.1 hz
      rw [hu] at hh
      exact Or.inl hh
    · have hh := hr.2 (by omega)
      rw [hu] at hh
      exact Or.inr hh
  have hb := block_hit_positions u (t % 5) (by omega) h9
  have hc : t = 5 * (t / 5) + t % 5 := by omega
  have hs : iterate t (blockValue R 0) = iterate (t % 5) (8 * u + 3) := by
    calc
      _ = iterate (5 * (t / 5) + t % 5) (blockValue R 0) := congrArg (fun k => iterate k (blockValue R 0)) hc
      _ = _ := by rw [iterate_add, hp.1, hu]
  rw [hs, hb]
  by_cases hz : t / 5 = 0
  · have hh := hr.1 hz
    rw [hu] at hh
    omega
  · have hh := hr.2 (by omega)
    rw [hu] at hh
    omega

theorem exact_inverse_minimum (R i r : Nat) (hR : R % 2 = 1)
    (hi : i < R) (hr : r ≤ i) :
    Backtrack r (2 * r + 1) (hitValue R i) (blockValue R (i - r)) ∧
    ∀ e o p, e ≤ r → Backtrack e o (hitValue R i) p → blockValue R (i - r) ≤ p := by
  refine ⟨ladder_attained R i r hi hr, ?_⟩
  intro e o p he hp
  exact bounded_inverse_lower R i r hR hi hr he hp

theorem source_strict (R j : Nat) (hj : 0 < j) (hjr : j ≤ R) :
    blockValue R 0 < blockValue R j := by
  obtain ⟨u, hu, hv, _⟩ := block_coordinates R 0 (by omega)
  have hm := block_monotone R 1 j (by omega) hjr
  simp only [Nat.zero_add] at hv
  rw [hv] at hm
  rw [hu]
  omega

theorem required_even_budget {e o p : Nat} (R i : Nat) (hR : R % 2 = 1)
    (hi : i < R) (h : Backtrack e o (hitValue R i) p) (hp : p ≤ blockValue R 0) : i ≤ e := by
  by_cases he : i ≤ e
  · exact he
  · have hl := inverse_ladder_lower R i hR hi (by omega) h
    have hs := source_strict R (i - e) (by omega) (by omega)
    omega

theorem source_growth (R : Nat) (hR : 3 ≤ R) : R < blockValue R 0 := by
  have hp := Nat.lt_two_pow_self (n := 3 * R)
  simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
  omega

theorem arbitrarily_many_unhelpful_visits (r L B : Nat) :
    ∃ R, R % 2 = 1 ∧ B < blockValue R 0 ∧
      prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      ∀ j, j < L →
        iterate (5 * (r + j + 1) + 2) (blockValue R 0) = hitValue R (r + j + 1) ∧
        hitValue R (r + j + 1) % 27 = 20 ∧
        ∀ e o p, e ≤ r → Backtrack e o (hitValue R (r + j + 1)) p → blockValue R 0 < p := by
  let R := 2 * (r + L + B + 3) + 1
  have hR : R % 2 = 1 := by unfold R; omega
  have hR3 : 3 ≤ R := by unfold R; omega
  have hs := source_growth R hR3
  refine ⟨R, hR, by unfold R at *; omega, (block_prefix R R (by omega)).2, ?_⟩
  intro j hj
  have hi : r + j + 1 < R := by unfold R; omega
  refine ⟨hit_clock R _ hi, hit_residue R _ hi (by omega), ?_⟩
  intro e o p he hp
  have hl := bounded_inverse_lower R (r + j + 1) r hR hi (by omega) he hp
  have hb := source_strict R (r + j + 1 - r) (by omega) (by omega)
  omega

set_option maxRecDepth 100000 in
theorem finite_ladder_witness :
    blockValue 3 0 = 507 ∧ blockValue 3 1 = 571 ∧ blockValue 3 2 = 643 ∧
    hitValue 3 1 = 857 ∧ hitValue 3 2 = 965 ∧
    iterate 7 507 = 857 ∧ iterate 12 507 = 965 ∧ prefixMinimum 15 507 = 507 ∧
    (∀ t : Fin 15, iterate t.val 507 % 27 = 20 ↔ t.val = 7 ∨ t.val = 12) ∧
    blockValue 5 0 = 32763 ∧ hitValue 5 4 = 78725 ∧
    ReachesOne 507 ∧ ReachesOne 857 ∧ ReachesOne 965 ∧ ReachesOne 32763 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ⟨35, by decide +kernel⟩,
    ⟨28, by decide +kernel⟩, ⟨23, by decide +kernel⟩, ⟨160, by decide +kernel⟩⟩

#print axioms backtrack_actual
#print axioms companion_even
#print axioms companion_odd
#print axioms odd_power_residue
#print axioms odd_budget_gap
#print axioms offset_buffer
#print axioms companion
#print axioms product_lower
#print axioms hit_lift
#print axioms scaled_companion
#print axioms inverse_ladder_lower
#print axioms product_monotone
#print axioms block_monotone
#print axioms bounded_inverse_lower
#print axioms backtrack_append
#print axioms five_block
#print axioms five_block_inverse
#print axioms block_coordinates
#print axioms block_prefix
#print axioms ladder_attained
#print axioms hit_clock
#print axioms hit_residue
#print axioms block_residues
#print axioms block_hit_positions
#print axioms all_hit_positions
#print axioms exact_inverse_minimum
#print axioms source_strict
#print axioms required_even_budget
#print axioms source_growth
#print axioms arbitrarily_many_unhelpful_visits
#print axioms finite_ladder_witness

end MinimumReturnLadder
