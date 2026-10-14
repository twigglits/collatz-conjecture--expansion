/- A second forced growing block at an infinite family of positive Mersenne
   sources. All statements concern finite ordinary prefixes. -/
import MinimumClockBarrier

namespace MinimumCriticalClockLift
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier

theorem scaled_endpoint_buffer (o d t n z : Nat)
    (hm : prefixMinimum (o + d) n = n) (he : iterate (o + d) n = z)
    (hs : 3 ^ o * n ≤ 2 ^ d * z) (ht : 2 ^ t ≤ 6 ^ o) :
    prefixMinimum t n = n := by
  by_cases hc : t ≤ o + d
  · have hl := prefix_clock_mono hc n
    have hu := prefix_le_source t n
    omega
  · let s := t - (o + d)
    have htime : t = o + (d + s) := by dsimp [s]; omega
    have hp : 2 ^ (d + s) ≤ 3 ^ o := by
      rw [htime, Nat.pow_add] at ht
      have h6 : 6 ^ o = 2 ^ o * 3 ^ o := by rw [← Nat.mul_pow]
      rw [h6] at ht
      exact Nat.le_of_mul_le_mul_left ht (Nat.two_pow_pos o)
    have hb : 2 ^ s * n ≤ z := by
      have hl := Nat.mul_le_mul_right n hp
      have hchain := Nat.le_trans hl hs
      rw [Nat.pow_add, Nat.mul_assoc] at hchain
      exact Nat.le_of_mul_le_mul_left hchain (Nat.two_pow_pos d)
    have hl := halving_buffer s z n hb
    have hu := prefix_le_source t n
    have hr : t = (o + d) + s := by omega
    rw [hr, prefix_concatenation, hm, he]
    omega

theorem nine_power_top_bit (j : Nat) :
    ∃ c, 9 ^ (2 ^ j) = 1 + 2 ^ (j + 3) * (2 * c + 1) := by
  induction j with
  | zero => exact ⟨0, by decide⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c + 2 ^ (j + 1) * (2 * c + 1) ^ 2, ?_⟩
    have hscale : 2 ^ (j + 3) = 4 * 2 ^ (j + 1) := by
      rw [show j + 3 = (j + 1) + 2 by omega, Nat.pow_add]
      grind
    rw [Nat.pow_succ, Nat.pow_mul, hc]
    rw [show j + 1 + 3 = (j + 3) + 1 by omega, Nat.pow_succ, hscale]
    grind

def liftExponent : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let a := liftExponent j
    if ((9 ^ a + 7) / 2 ^ (j + 3)) % 2 = 0 then a else a + 2 ^ j

theorem lift_exponent_spec (j : Nat) :
    liftExponent j < 2 ^ j ∧ ∃ q, 9 ^ liftExponent j + 7 = 2 ^ (j + 3) * q := by
  induction j with
  | zero => exact ⟨by decide, 1, by decide⟩
  | succ j ih =>
    obtain ⟨ha, q, hq⟩ := ih
    obtain ⟨c, hc⟩ := nine_power_top_bit j
    have hdiv : (9 ^ liftExponent j + 7) / 2 ^ (j + 3) = q := by
      rw [hq, Nat.mul_div_right _ (Nat.two_pow_pos _)]
    have hpow : 2 ^ (j + 1 + 3) = 2 * 2 ^ (j + 3) := by
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, Nat.pow_succ]
      omega
    have hodd : 9 ^ liftExponent j % 2 = 1 := by
      rw [Nat.pow_mod]
      simp
    simp only [liftExponent, hdiv]
    by_cases he : q % 2 = 0
    · rw [if_pos he]
      constructor
      · rw [Nat.pow_succ]; have hp := Nat.two_pow_pos j; omega
      · refine ⟨q / 2, ?_⟩
        have hq2 := Nat.mod_add_div q 2
        rw [he] at hq2
        rw [hpow, hq]
        grind
    · rw [if_neg he]
      constructor
      · rw [Nat.pow_succ]; omega
      · let w := q + 9 ^ liftExponent j * (2 * c + 1)
        have hw : w % 2 = 0 := by
          have hqodd : q % 2 = 1 := by omega
          have hcodd : (2 * c + 1) % 2 = 1 := by omega
          dsimp [w]
          rw [Nat.add_mod, Nat.mul_mod, hqodd, hodd, hcodd]
        have hw2 := Nat.mod_add_div w 2
        rw [hw] at hw2
        refine ⟨w / 2, ?_⟩
        rw [Nat.pow_add, hc, hpow]
        dsimp [w] at hw2
        grind

def blockLength (j : Nat) : Nat := 2 * (liftExponent j + 2 ^ j)

theorem block_length_bounds (j : Nat) :
    2 ^ (j + 1) ≤ blockLength j ∧ blockLength j < 2 ^ (j + 2) := by
  have ha := (lift_exponent_spec j).1
  simp only [blockLength, Nat.pow_succ]
  omega

theorem block_length_log2 (j : Nat) : (blockLength j).log2 = j + 1 := by
  have hb := block_length_bounds j
  have hp := Nat.two_pow_pos (j + 1)
  apply (Nat.log2_eq_iff (by omega : blockLength j ≠ 0)).mpr
  exact hb

theorem second_block_congruence (j : Nat) :
    ∃ q, 0 < q ∧ 3 ^ blockLength j + 7 = 2 ^ (j + 3) * q := by
  obtain ⟨_, q, hq⟩ := lift_exponent_spec j
  obtain ⟨c, hc⟩ := nine_power_top_bit j
  have hp : 3 ^ blockLength j = 9 ^ liftExponent j * 9 ^ (2 ^ j) := by
    simp only [blockLength, Nat.pow_mul, Nat.pow_add]
  refine ⟨q + 9 ^ liftExponent j * (2 * c + 1), ?_, ?_⟩
  · have ha : 0 < 9 ^ liftExponent j := Nat.pow_pos (by decide)
    have hb : 0 < 9 ^ liftExponent j * (2 * c + 1) := Nat.mul_pos ha (by omega)
    omega
  · rw [hp, hc]
    grind

theorem three_halves (x : Nat) :
    iterate 3 (8 * x) = x ∧ prefixMinimum 3 (8 * x) = x := by
  have he (y : Nat) : C (2 * y) = y := by
    have hm : (2 * y) % 2 ≠ 1 := by omega
    simp only [C, if_neg hm]
    omega
  have h8 : 8 * x = 2 * (4 * x) := by omega
  have h4 : 4 * x = 2 * (2 * x) := by omega
  have hc8 : C (8 * x) = 4 * x := by rw [h8, he]
  have hc4 : C (4 * x) = 2 * x := by rw [h4, he]
  simp only [iterate, prefixMinimum, hc8, hc4, he]
  exact ⟨trivial, by omega⟩

theorem three_halves_safe (k : Nat) (hk : 6 ≤ k) :
    8 * (2 ^ k - 1) ≤ 3 ^ k - 1 := by
  have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (k - 6)
  have he : k = 6 + (k - 6) := by omega
  have h2 : 2 ^ k = 64 * 2 ^ (k - 6) := by
    calc
      2 ^ k = 2 ^ (6 + (k - 6)) := congrArg (fun e => 2 ^ e) he
      _ = 64 * 2 ^ (k - 6) := by rw [Nat.pow_add]
  have h3 : 3 ^ k = 729 * 3 ^ (k - 6) := by
    calc
      3 ^ k = 3 ^ (6 + (k - 6)) := congrArg (fun e => 3 ^ e) he
      _ = 729 * 3 ^ (k - 6) := by rw [Nat.pow_add]
  rw [h2, h3]
  have hpos := Nat.two_pow_pos (k - 6)
  omega

theorem odd_endpoint_scale (k q : Nat) (hq : 0 < q) :
    3 ^ k * (2 ^ k * q - 1) ≤ 2 ^ k * (3 ^ k * q - 1) := by
  have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) k
  have h2 := Nat.sub_add_cancel (n := 2 ^ k * q) (m := 1)
    (Nat.mul_pos (Nat.two_pow_pos k) hq)
  have h3 := Nat.sub_add_cancel (n := 3 ^ k * q) (m := 1)
    (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3)) hq)
  have h2m := congrArg (fun x => 3 ^ k * x) h2
  have h3m := congrArg (fun x => 2 ^ k * x) h3
  grind

theorem two_growing_blocks (k j q : Nat) (hk : 6 ≤ k) (hq : 0 < q)
    (hlift : 3 ^ k + 7 = 2 ^ (j + 3) * q) :
    iterate (2 * k + 3 + 2 * j) (2 ^ k - 1) = 3 ^ j * q - 1 ∧
    prefixMinimum (2 * k + 3 + 2 * j) (2 ^ k - 1) = 2 ^ k - 1 ∧
    3 ^ (k + j) * (2 ^ k - 1) ≤ 2 ^ (k + j + 3) * (3 ^ j * q - 1) := by
  have hp : 0 < 2 ^ j * q := Nat.mul_pos (Nat.two_pow_pos j) hq
  have hsub := Nat.sub_add_cancel (n := 2 ^ j * q) (m := 1) hp
  have hscale : 2 ^ (j + 3) = 8 * 2 ^ j := by rw [Nat.pow_add]; grind
  have hbridge : 3 ^ k - 1 = 8 * (2 ^ j * q - 1) := by
    rw [hscale] at hlift
    grind
  have hs := three_halves_safe k hk
  rw [hbridge] at hs
  have habove : 2 ^ k - 1 ≤ 2 ^ j * q - 1 := by omega
  have hfirst := odd_block k 0 1 (by decide)
  have hsecond := odd_block j 0 q hq
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, Nat.mul_one] at hfirst hsecond
  have hmiddle := three_halves (2 ^ j * q - 1)
  have he : iterate (2 * k + 3) (2 ^ k - 1) = 2 ^ j * q - 1 := by
    rw [iterate_add, hfirst.1, hbridge, hmiddle.1]
  have hm : prefixMinimum (2 * k + 3) (2 ^ k - 1) = 2 ^ k - 1 := by
    rw [prefix_concatenation, hfirst.1, hfirst.2, hbridge, hmiddle.2]
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [iterate_add, he, hsecond.1]
  · rw [prefix_concatenation, he, hm, hsecond.2]
    omega
  · have hstart := odd_endpoint_scale k 1 (by decide)
    simp only [Nat.mul_one] at hstart
    rw [hbridge] at hstart
    have hleft := Nat.mul_le_mul_left (3 ^ j) hstart
    have hright := Nat.mul_le_mul_left (2 ^ k * 8) (odd_endpoint_scale j q hq)
    rw [Nat.pow_add, Nat.pow_add, Nat.pow_add]
    grind

theorem two_block_clock (k j q t : Nat) (hk : 6 ≤ k) (hq : 0 < q)
    (hlift : 3 ^ k + 7 = 2 ^ (j + 3) * q) (ht : 2 ^ t ≤ 6 ^ (k + j)) :
    prefixMinimum t (2 ^ k - 1) = 2 ^ k - 1 := by
  obtain ⟨he, hm, hs⟩ := two_growing_blocks k j q hk hq hlift
  have hc : 2 * k + 3 + 2 * j = (k + j) + (k + j + 3) := by omega
  rw [hc] at he hm
  exact scaled_endpoint_buffer (k + j) (k + j + 3) t _ _ hm he hs ht

def source (j : Nat) : Nat := 2 ^ blockLength j - 1

theorem source_growth (j : Nat) : j < source j := by
  have hk := (block_length_bounds j).1
  have hj := Nat.lt_two_pow_self (n := j + 1)
  have hp := Nat.lt_two_pow_self (n := blockLength j)
  dsimp [source]
  omega

theorem family_no_descent (j t : Nat) (hj : 2 ≤ j)
    (ht : 2 ^ t ≤ 6 ^ (blockLength j + j)) :
    prefixMinimum t (source j) = source j := by
  obtain ⟨q, hq, hlift⟩ := second_block_congruence j
  have hlow := (block_length_bounds j).1
  have he : 8 ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ j + 1)
  exact two_block_clock (blockLength j) j q t (by omega) hq hlift ht

theorem family_tail_diagonal (h j t : Nat) (hj : 2 ≤ j) (hh : h < source j)
    (ht : 2 ^ t ≤ 6 ^ (blockLength j + j)) :
    source j ≤ tailSum (prefixMinimum t) h (source j) := by
  have hm := family_no_descent j t hj ht
  have hg := source_growth j
  have hs := term_le_sum (tailTerm (prefixMinimum t) h)
    (show 0 < source j by omega) (Nat.le_refl (source j))
  simp only [tailTerm, hm, if_pos hh] at hs
  exact hs

theorem strict_budget_requires_clock (h j t : Nat) (hj : 2 ≤ j) (hh : h < source j)
    (hb : tailSum (prefixMinimum t) h (source j) < source j) :
    6 ^ (blockLength j + j) < 2 ^ t := by
  by_cases ht : 2 ^ t ≤ 6 ^ (blockLength j + j)
  · have hs := family_tail_diagonal h j t hj hh ht
    omega
  · omega

def criticalClock (l n : Nat) : Nat := (6 ^ (n + 1).log2).log2 + l

theorem critical_clock_at_source (l j : Nat) :
    criticalClock l (source j) = (6 ^ blockLength j).log2 + l := by
  have he := Nat.sub_add_cancel (n := 2 ^ blockLength j) (m := 1)
    (Nat.two_pow_pos (blockLength j))
  simp only [criticalClock, source, he, Nat.log2_two_pow]

theorem shifted_critical_power (k j l : Nat) (hl : l ≤ j) :
    2 ^ ((6 ^ k).log2 + l) ≤ 6 ^ (k + j) := by
  have hpos : 0 < 6 ^ k := Nat.pow_pos (by decide)
  have hk := Nat.log2_self_le (by omega : 6 ^ k ≠ 0)
  have hj := Nat.le_trans (Nat.pow_le_pow_left (by decide : 2 ≤ 6) l)
    (Nat.pow_le_pow_right (by decide : 0 < 6) hl)
  rw [Nat.pow_add, Nat.pow_add]
  exact Nat.mul_le_mul hk hj

theorem shifted_critical_no_descent (l j : Nat) (hj : 2 ≤ j) (hl : l ≤ j) :
    prefixMinimum (criticalClock l (source j)) (source j) = source j := by
  apply family_no_descent j _ hj
  rw [critical_clock_at_source]
  exact shifted_critical_power (blockLength j) j l hl

theorem critical_budget_failure (h l b : Nat) :
    ∃ n, b < n ∧ n ≤ tailSum (prefixMinimum (criticalClock l n)) h n := by
  let j := h + l + b + 2
  have hj : j = h + l + b + 2 := rfl
  have hg := source_growth j
  refine ⟨source j, by omega, ?_⟩
  apply family_tail_diagonal h j _ (by omega) (by omega)
  rw [critical_clock_at_source]
  exact shifted_critical_power (blockLength j) j l (by omega)

theorem closed_block_lengths : blockLength 2 = 14 ∧ blockLength 3 = 30 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem closed_sources_converge : ReachesOne (source 2) ∧ ReachesOne (source 3) := by
  have hs2 : source 2 = 16383 := by rw [source, closed_block_lengths.1]
  have hs3 : source 3 = 1073741823 := by rw [source, closed_block_lengths.2]
  rw [hs2, hs3]
  exact ⟨⟨159, by decide +kernel⟩, ⟨449, by decide +kernel⟩⟩

#print axioms scaled_endpoint_buffer
#print axioms nine_power_top_bit
#print axioms lift_exponent_spec
#print axioms block_length_bounds
#print axioms block_length_log2
#print axioms second_block_congruence
#print axioms three_halves
#print axioms three_halves_safe
#print axioms odd_endpoint_scale
#print axioms two_growing_blocks
#print axioms two_block_clock
#print axioms source_growth
#print axioms family_no_descent
#print axioms family_tail_diagonal
#print axioms strict_budget_requires_clock
#print axioms critical_clock_at_source
#print axioms shifted_critical_power
#print axioms shifted_critical_no_descent
#print axioms critical_budget_failure
#print axioms closed_block_lengths
#print axioms closed_sources_converge

end MinimumCriticalClockLift
