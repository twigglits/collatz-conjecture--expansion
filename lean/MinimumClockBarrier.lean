/- The adaptive prefix clock 2*log2(cutoff)+L has an unbounded minimum
   tail mean for every fixed L and floor. An actual all-odd residue family
   supplies the lower bound. This is a finite-prefix obstruction, not
   nonconvergence of an orbit or a lower bound on actual global minima. -/
import MinimumGreenKernel

namespace MinimumClockBarrier
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport
open MinimumLinearBoundary MinimumGreenKernel CutoffDescent

theorem step_halving_bound (n : Nat) : n ≤ 2 * C n := by
  unfold C
  split <;> omega

theorem prefix_concatenation (s t n : Nat) :
    prefixMinimum (s + t) n = min (prefixMinimum s n) (prefixMinimum t (iterate s n)) := by
  induction s generalizing n with
  | zero => have hl := prefix_le_source t n; simp only [Nat.zero_add, prefixMinimum, iterate]; omega
  | succ s ih =>
    simp only [Nat.succ_add, prefixMinimum, iterate, ih]
    omega

theorem halving_buffer (t n b : Nat) (hn : 2 ^ t * b ≤ n) : b ≤ prefixMinimum t n := by
  induction t generalizing n with
  | zero => simpa only [Nat.pow_zero, Nat.one_mul, prefixMinimum] using hn
  | succ t ih =>
    have hc := step_halving_bound n
    have he : 2 ^ (t + 1) * b = 2 * (2 ^ t * b) := by rw [Nat.pow_succ]; grind
    rw [he] at hn
    have ht := ih (C n) (by omega)
    have hp := Nat.two_pow_pos t
    have hb := Nat.mul_le_mul_right b (show 1 ≤ 2 ^ t by omega)
    simp only [prefixMinimum]
    omega

theorem odd_pair (x : Nat) (hx : 0 < x) :
    C (2 * x - 1) = 2 * (3 * x - 1) ∧ C (C (2 * x - 1)) = 3 * x - 1 := by
  have ho : (2 * x - 1) % 2 = 1 := by omega
  have he : (2 * (3 * x - 1)) % 2 ≠ 1 := by omega
  have hs : C (2 * x - 1) = 2 * (3 * x - 1) := by
    simp only [C, if_pos ho]
    omega
  constructor
  · exact hs
  · rw [hs]
    simp only [C, if_neg he]
    omega

theorem odd_pair_prefix (t x : Nat) (hx : 0 < x) :
    prefixMinimum (t + 2) (2 * x - 1) =
      min (2 * x - 1) (prefixMinimum t (3 * x - 1)) := by
  have hs := odd_pair x hx
  have hl := prefix_le_source t (3 * x - 1)
  simp only [prefixMinimum, hs.1]
  have he : C (2 * (3 * x - 1)) = 3 * x - 1 := by
    rw [← hs.1]
    exact hs.2
  rw [he]
  omega

theorem odd_block (k m q : Nat) (hq : 0 < q) :
    iterate (2 * k) (2 ^ (k + m) * q - 1) = 2 ^ m * 3 ^ k * q - 1 ∧
    prefixMinimum (2 * k) (2 ^ (k + m) * q - 1) = 2 ^ (k + m) * q - 1 := by
  induction k generalizing q with
  | zero => simp [iterate, prefixMinimum]
  | succ k ih =>
    have hp := Nat.mul_pos (Nat.two_pow_pos (k + m)) hq
    have he : 2 ^ (k + 1 + m) * q = 2 * (2 ^ (k + m) * q) := by
      rw [show k + 1 + m = k + m + 1 by omega, Nat.pow_succ]
      grind
    have ht : 3 * (2 ^ (k + m) * q) = 2 ^ (k + m) * (3 * q) := by grind
    have hi := ih (3 * q) (by omega)
    have hs := odd_pair (2 ^ (k + m) * q) hp
    rw [he]
    constructor
    · have hc : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [hc, iterate_add]
      change iterate (2 * k) (C (C (2 * (2 ^ (k + m) * q) - 1))) = _
      rw [hs.2, ht, hi.1, Nat.pow_succ]
      grind
    · have hc : 2 * (k + 1) = 2 * k + 2 := by omega
      rw [hc, odd_pair_prefix (2 * k) _ hp, ht, hi.2]
      have hu : 2 * (2 ^ (k + m) * q) - 1 ≤ 2 ^ (k + m) * (3 * q) - 1 := by
        rw [← ht]
        omega
      omega

theorem odd_block_with_buffer (k t q : Nat) (hq : 0 < q)
    (hb : 2 ^ t * (2 ^ k * q - 1) ≤ 3 ^ k * q - 1) :
    prefixMinimum (2 * k + t) (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
  have hg := odd_block k 0 q hq
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hg
  have ht := halving_buffer t (3 ^ k * q - 1) (2 ^ k * q - 1) hb
  rw [prefix_concatenation, hg.1, hg.2]
  omega

theorem paired_power_buffer (m q : Nat) (hq : 0 < q) :
    2 ^ m * (2 ^ (2 * m) * q - 1) ≤ 3 ^ (2 * m) * q - 1 := by
  have hp := Nat.pow_le_pow_left (by decide : 8 ≤ 9) m
  have h2 : 2 ^ (3 * m) = 8 ^ m := by rw [Nat.pow_mul]
  have h3 : 3 ^ (2 * m) = 9 ^ m := by rw [Nat.pow_mul]
  rw [← h2, ← h3] at hp
  have hm := Nat.mul_le_mul_right q hp
  have he : 2 ^ (3 * m) * q = 2 ^ m * (2 ^ (2 * m) * q) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add, show m + 2 * m = 3 * m by omega]
  rw [he] at hm
  have hpos := Nat.mul_pos (Nat.two_pow_pos (2 * m)) hq
  have hh : 2 ^ m * (2 ^ (2 * m) * q - 1) + 2 ^ m =
      2 ^ m * (2 ^ (2 * m) * q) := by
    have heq : 2 ^ (2 * m) * q - 1 + 1 = 2 ^ (2 * m) * q :=
      Nat.sub_add_cancel hpos
    have ht := congrArg (fun x => 2 ^ m * x) heq
    simpa only [Nat.mul_add, Nat.mul_one] using ht
  have hg := Nat.two_pow_pos m
  omega

theorem five_clock_no_descent (m q : Nat) (hq : 0 < q) :
    prefixMinimum (5 * m) (2 ^ (2 * m) * q - 1) = 2 ^ (2 * m) * q - 1 := by
  have ht := odd_block_with_buffer (2 * m) m q hq (paired_power_buffer m q hq)
  simpa only [show 2 * (2 * m) + m = 5 * m by omega] using ht

theorem buffer_from_power (k t q : Nat) (hq : 0 < q) (hp : 2 ^ (k + t) ≤ 3 ^ k) :
    2 ^ t * (2 ^ k * q - 1) ≤ 3 ^ k * q - 1 := by
  have hm := Nat.mul_le_mul_right q hp
  have he : 2 ^ (k + t) * q = 2 ^ t * (2 ^ k * q) := by
    rw [Nat.pow_add]
    grind
  rw [he] at hm
  have hpos := Nat.mul_pos (Nat.two_pow_pos k) hq
  have heq : 2 ^ k * q - 1 + 1 = 2 ^ k * q := Nat.sub_add_cancel hpos
  have ht := congrArg (fun x => 2 ^ t * x) heq
  simp only [Nat.mul_add, Nat.mul_one] at ht
  have hg := Nat.two_pow_pos t
  omega

theorem exponential_clock_no_descent (k t q : Nat) (hq : 0 < q)
    (ht : 2 ^ t ≤ 6 ^ k) :
    prefixMinimum t (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
  by_cases hc : t ≤ 2 * k
  · have hg := (odd_block k 0 q hq).2
    simp only [Nat.add_zero] at hg
    have hl := prefix_clock_mono hc (2 ^ k * q - 1)
    have hu := prefix_le_source t (2 ^ k * q - 1)
    omega
  · have he : t = k + (k + (t - 2 * k)) := by omega
    have hp : 2 ^ (k + (t - 2 * k)) ≤ 3 ^ k := by
      rw [he, Nat.pow_add] at ht
      have h6 : 6 ^ k = 2 ^ k * 3 ^ k := by rw [← Nat.mul_pow]
      rw [h6] at ht
      exact Nat.le_of_mul_le_mul_left ht (Nat.two_pow_pos k)
    have hb := odd_block_with_buffer k (t - 2 * k) q hq
      (buffer_from_power k (t - 2 * k) q hq hp)
    simpa only [show 2 * k + (t - 2 * k) = t by omega] using hb

theorem sum_length_mono (f : Nat → Nat) {a b : Nat} (hab : a ≤ b) :
    MinimumTailRigidity.sumPos f a ≤ MinimumTailRigidity.sumPos f b := by
  induction b with
  | zero =>
    have he : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases he : a = b + 1
    · subst a; exact Nat.le_refl _
    · have ht := ih (by omega)
      simp only [MinimumTailRigidity.sumPos]
      omega

theorem prefix_plus_term (f : Nat → Nat) {b i n : Nat} (hbi : b < i) (hin : i ≤ n) :
    MinimumTailRigidity.sumPos f b + f i ≤ MinimumTailRigidity.sumPos f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n + 1
    · subst i
      have ht := sum_length_mono f (show b ≤ n by omega)
      simp only [MinimumTailRigidity.sumPos]
      omega
    · have ht := ih (by omega)
      simp only [MinimumTailRigidity.sumPos]
      omega

theorem residue_sum_le (f : Nat → Nat) (m q : Nat) (hm : 2 ≤ m) :
    MinimumTailRigidity.sumPos (fun j => f (m * j - 1)) q ≤
      MinimumTailRigidity.sumPos f (m * q) := by
  induction q with
  | zero => simp only [Nat.mul_zero, MinimumTailRigidity.sumPos]; omega
  | succ q ih =>
    have ht := prefix_plus_term f
      (show m * q < m * (q + 1) - 1 by rw [Nat.mul_add]; omega)
      (show m * (q + 1) - 1 ≤ m * (q + 1) by omega)
    simp only [MinimumTailRigidity.sumPos]
    omega

theorem residue_source_sum (m q : Nat) (hm : 1 ≤ m) :
    2 * MinimumTailRigidity.sumPos (fun j => m * j - 1) q + 2 * q = m * q * (q + 1) := by
  induction q with
  | zero => simp only [MinimumTailRigidity.sumPos, Nat.mul_zero, Nat.zero_add]
  | succ q ih =>
    have hp : 0 < m * (q + 1) := Nat.mul_pos hm (by omega)
    have he := Nat.sub_add_cancel (n := m * (q + 1)) (m := 1) hp
    simp only [MinimumTailRigidity.sumPos]
    grind

theorem residue_tail_budget (h t m q : Nat) (hm : 2 ≤ m) (hh : h < m - 1)
    (hs : ∀ j, 0 < j → j ≤ q → prefixMinimum t (m * j - 1) = m * j - 1) :
    m * q * q ≤ 2 * tailSum (prefixMinimum t) h (m * q) := by
  have hl := residue_sum_le (tailTerm (prefixMinimum t) h) m q hm
  have he : MinimumTailRigidity.sumPos (fun j => m * j - 1) q =
      MinimumTailRigidity.sumPos (fun j => tailTerm (prefixMinimum t) h (m * j - 1)) q := by
    apply Nat.le_antisymm
    · apply MinimumTailRigidity.sum_mono
      intro j hj hjq
      have hp := Nat.mul_le_mul_left m (show 1 ≤ j by omega)
      simp only [Nat.mul_one] at hp
      simp only [tailTerm, hs j hj hjq, if_pos (by omega : h < m * j - 1)]
      exact Nat.le_refl _
    · apply MinimumTailRigidity.sum_mono
      intro j hj hjq
      have hp := Nat.mul_le_mul_left m (show 1 ≤ j by omega)
      simp only [Nat.mul_one] at hp
      simp only [tailTerm, hs j hj hjq, if_pos (by omega : h < m * j - 1)]
      exact Nat.le_refl _
  have hb := residue_source_sum m q (by omega)
  rw [he] at hb
  have hp := Nat.mul_le_mul_right q hm
  change _ ≤ tailSum (prefixMinimum t) h (m * q) at hl
  grind

theorem strict_dyadic_budget_requires_clock (h d t : Nat) (hd : 1 ≤ d)
    (hh : h < 2 ^ d - 1)
    (hb : tailSum (prefixMinimum t) h (2 ^ (d + 1)) < 2 ^ (d + 1)) :
    6 ^ d < 2 ^ t := by
  by_cases ht : 2 ^ t ≤ 6 ^ d
  · have hm : 2 ≤ 2 ^ d := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    have hl := residue_tail_budget h t (2 ^ d) 2 hm hh
      (by intro q hq _; exact exponential_clock_no_descent d t q hq ht)
    have he : 2 ^ d * 2 = 2 ^ (d + 1) := by rw [Nat.pow_succ]
    rw [he] at hl
    omega
  · omega

def adaptiveClock (l n : Nat) : Nat := l + 2 * n.log2
def adaptiveMean (h l n : Nat) : Rat := tailMean h (adaptiveClock l n) n

theorem dyadic_adaptive_clock (l d : Nat) :
    adaptiveClock l (2 ^ d) = l + 2 * d := by
  have hp := Nat.two_pow_pos d
  have he : (2 ^ d).log2 = d := (Nat.log2_eq_iff (by omega)).mpr
    ⟨Nat.le_refl _, by rw [Nat.pow_succ]; omega⟩
  simp only [adaptiveClock, he]

theorem adaptive_dyadic_population (h l j : Nat) (hj : 0 < j)
    (hh : h < 2 ^ (4 * j + 2 * l) - 1) :
    (2 ^ j : Nat) / (2 : Rat) ≤ adaptiveMean h l (2 ^ (5 * j + 2 * l)) := by
  let m := 2 ^ (4 * j + 2 * l)
  let q := 2 ^ j
  have hm : 2 ≤ m := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ 4 * j + 2 * l)
  have hclock := dyadic_adaptive_clock l (5 * j + 2 * l)
  have he : m * q = 2 ^ (5 * j + 2 * l) := by
    simp only [m, q, ← Nat.pow_add]
    congr 1
    omega
  have hb := residue_tail_budget h (5 * (2 * j + l)) m q hm hh (by
    intro b hb _
    have ht := five_clock_no_descent (2 * j + l) b hb
    simpa only [show 2 * (2 * j + l) = 4 * j + 2 * l by omega] using ht)
  rw [he] at hb
  have hp : (0 : Rat) < (2 ^ (5 * j + 2 * l) : Nat) :=
    Rat.natCast_lt_natCast.mpr (Nat.two_pow_pos _)
  have hc := Rat.natCast_le_natCast.mpr hb
  simp only [Rat.natCast_mul] at hc
  have hd := Rat.div_mul_cancel (a := (tailSum (prefixMinimum (5 * (2 * j + l))) h
    (2 ^ (5 * j + 2 * l)) : Rat)) (show ((2 ^ (5 * j + 2 * l) : Nat) : Rat) ≠ 0 by grind)
  apply Rat.le_of_mul_le_mul_right (c := ((2 ^ (5 * j + 2 * l) : Nat) : Rat)) _ hp
  simp only [adaptiveMean, tailMean, hclock,
    show l + 2 * (5 * j + 2 * l) = 5 * (2 * j + l) by omega]
  change ((q : Rat) / 2) * ((2 ^ (5 * j + 2 * l) : Nat) : Rat) ≤ _
  grind

theorem adaptive_mean_unbounded (h l b : Nat) :
    ∃ n, 0 < n ∧ (b : Rat) ≤ adaptiveMean h l n := by
  let j := h + b + 2
  have hj : 0 < j := by omega
  have hp := Nat.lt_two_pow_self (n := 4 * j + 2 * l)
  have hh : h < 2 ^ (4 * j + 2 * l) - 1 := by omega
  have hl := adaptive_dyadic_population h l j hj hh
  have hb := Nat.lt_two_pow_self (n := b)
  have hq := Nat.pow_le_pow_right (by decide : 0 < 2) (show b + 1 ≤ j by omega)
  rw [Nat.pow_succ] at hq
  have hm := Rat.natCast_le_natCast.mpr (show 2 * b ≤ 2 ^ j by omega)
  simp only [Rat.natCast_mul] at hm
  refine ⟨2 ^ (5 * j + 2 * l), Nat.two_pow_pos _, ?_⟩
  grind

theorem adaptive_budget_failure (h l : Nat) :
    ∃ n, 0 < n ∧ n ≤ tailSum (prefixMinimum (adaptiveClock l n)) h n := by
  obtain ⟨n, hn, hb⟩ := adaptive_mean_unbounded h l 1
  have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  have hm := Rat.mul_le_mul_of_nonneg_right hb (Rat.natCast_nonneg (a := n))
  have he := Rat.div_mul_cancel (a := (tailSum (prefixMinimum (adaptiveClock l n)) h n : Rat))
    (show (n : Rat) ≠ 0 by grind)
  simp only [adaptiveMean, tailMean] at hm
  have ht : (n : Rat) ≤ (tailSum (prefixMinimum (adaptiveClock l n)) h n : Rat) := by grind
  exact ⟨n, hn, Rat.natCast_le_natCast.mp ht⟩

theorem adaptive_mean_below_floor (h l n : Nat) (hn : n ≤ h) : adaptiveMean h l n = 0 :=
  tail_mean_below_floor h (adaptiveClock l n) n hn

theorem adaptive_mean_nonnegative (h l n : Nat) : 0 ≤ adaptiveMean h l n := by
  by_cases hn : n = 0
  · subst n
    rw [adaptive_mean_below_floor h l 0 (Nat.zero_le _)]
    exact Rat.le_refl
  · exact tail_mean_nonnegative h (adaptiveClock l n) n (by omega)

theorem adaptive_mean_decreasing (h l s n : Nat) (hls : l ≤ s) :
    adaptiveMean h s n ≤ adaptiveMean h l n := by
  by_cases hn : n = 0
  · subst n
    rw [adaptive_mean_below_floor h s 0 (Nat.zero_le _),
      adaptive_mean_below_floor h l 0 (Nat.zero_le _)]
    exact Rat.le_refl
  · have ht : adaptiveClock l n ≤ adaptiveClock s n := by unfold adaptiveClock; omega
    have hs := MinimumTailRigidity.sum_mono
      (tailTerm (prefixMinimum (adaptiveClock s n)) h)
      (tailTerm (prefixMinimum (adaptiveClock l n)) h) n
      (by intro j _ _; exact tail_term_mono _ _ h j (prefix_clock_mono ht j))
    have hc := Rat.natCast_le_natCast.mpr hs
    have hn0 : 0 < n := by omega
    have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn0
    have he1 := Rat.div_mul_cancel (a := (tailSum (prefixMinimum (adaptiveClock s n)) h n : Rat))
      (show (n : Rat) ≠ 0 by grind)
    have he2 := Rat.div_mul_cancel (a := (tailSum (prefixMinimum (adaptiveClock l n)) h n : Rat))
      (show (n : Rat) ≠ 0 by grind)
    apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hp
    unfold adaptiveMean tailMean tailSum at *
    grind

theorem prefix_le_endpoint (t n : Nat) : prefixMinimum t n ≤ iterate t n := by
  induction t generalizing n with
  | zero => exact Nat.le_refl _
  | succ t ih =>
    have ht := ih (C n)
    simp only [prefixMinimum, iterate]
    omega

theorem prefix_at_global_minimum (t n : Nat) (ht : minimumClock n ≤ t) :
    prefixMinimum t n = minimum n := by
  have hl := minimum_le_prefix t n
  have hu := prefix_clock_mono ht n
  have he := prefix_le_endpoint (minimumClock n) n
  change prefixMinimum (minimumClock n) n ≤ minimum n at he
  omega

theorem adaptive_pointwise_stabilization (h n : Nat) :
    ∃ l, ∀ s, l ≤ s → adaptiveMean h s n = globalMean h n := by
  refine ⟨MinimumTailRigidity.sumPos minimumClock n, ?_⟩
  intro s hs
  have ht : ∀ j, 0 < j → j ≤ n →
      prefixMinimum (adaptiveClock s n) j = minimum j := by
    intro j hj hjn
    have hc := term_le_sum minimumClock hj hjn
    apply prefix_at_global_minimum
    unfold adaptiveClock
    omega
  have he : tailSum (prefixMinimum (adaptiveClock s n)) h n = tailSum minimum h n := by
    apply Nat.le_antisymm
    · apply MinimumTailRigidity.sum_mono
      intro j hj hjn
      simp only [tailTerm, ht j hj hjn, Nat.le_refl]
    · apply MinimumTailRigidity.sum_mono
      intro j hj hjn
      simp only [tailTerm, ht j hj hjn, Nat.le_refl]
  simp only [adaptiveMean, tailMean, globalMean, he]

theorem adaptive_residual_lower (h l j depth : Nat) (hh : 1 ≤ h) (hj : 0 < j)
    (hfloor : h < 2 ^ (4 * j + 2 * l) - 1)
    (hmajorant : ∀ n, adaptiveMean h l n ≤ 3 * gauge n) :
    (2 ^ j : Nat) / (2 : Rat) - 3 * rho ^ depth * gauge (2 ^ (5 * j + 2 * l)) ≤
      occupation h depth (localResidual (adaptiveMean h l)) (2 ^ (5 * j + 2 * l)) := by
  have hl := adaptive_dyadic_population h l j hj hfloor
  have ht := (residual_truncation_bound h depth hh (adaptiveMean h l)
    (fun n => ⟨adaptive_mean_nonnegative h l n, hmajorant n⟩)
    (adaptive_mean_below_floor h l) (2 ^ (5 * j + 2 * l))).2
  grind

theorem closed_subset_tail_lower : 2556 ≤ tailSum (prefixMinimum 20) 64 1024 := by
  have hl := residue_sum_le (tailTerm (prefixMinimum 20) 64) 256 4 (by decide)
  have he : ∀ q, 0 < q → q ≤ 4 →
      tailTerm (prefixMinimum 20) 64 (256 * q - 1) = 256 * q - 1 := by
    intro q hq _
    have ht := five_clock_no_descent 4 q hq
    change prefixMinimum 20 (256 * q - 1) = 256 * q - 1 at ht
    have hp := Nat.mul_le_mul_left 256 (show 1 ≤ q by omega)
    simp only [tailTerm, ht, if_pos (by omega : 64 < 256 * q - 1)]
  have hs : MinimumTailRigidity.sumPos
      (fun q => tailTerm (prefixMinimum 20) 64 (256 * q - 1)) 4 = 2556 := by
    simp only [MinimumTailRigidity.sumPos]
    rw [he 1 (by decide) (by decide), he 2 (by decide) (by decide),
      he 3 (by decide) (by decide), he 4 (by decide) (by decide)]
  rw [hs] at hl
  exact hl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem closed_subset_converges :
    ReachesOne 255 ∧ ReachesOne 511 ∧ ReachesOne 767 ∧ ReachesOne 1023 := by
  exact ⟨⟨47, by decide +kernel⟩, ⟨61, by decide +kernel⟩,
    ⟨59, by decide +kernel⟩, ⟨62, by decide +kernel⟩⟩

#print axioms step_halving_bound
#print axioms prefix_concatenation
#print axioms halving_buffer
#print axioms odd_pair
#print axioms odd_pair_prefix
#print axioms odd_block
#print axioms odd_block_with_buffer
#print axioms paired_power_buffer
#print axioms five_clock_no_descent
#print axioms buffer_from_power
#print axioms exponential_clock_no_descent
#print axioms sum_length_mono
#print axioms prefix_plus_term
#print axioms residue_sum_le
#print axioms residue_source_sum
#print axioms residue_tail_budget
#print axioms strict_dyadic_budget_requires_clock
#print axioms dyadic_adaptive_clock
#print axioms adaptive_dyadic_population
#print axioms adaptive_mean_unbounded
#print axioms adaptive_budget_failure
#print axioms adaptive_mean_below_floor
#print axioms adaptive_mean_nonnegative
#print axioms adaptive_mean_decreasing
#print axioms prefix_le_endpoint
#print axioms prefix_at_global_minimum
#print axioms adaptive_pointwise_stabilization
#print axioms adaptive_residual_lower
#print axioms closed_subset_tail_lower
#print axioms closed_subset_converges

end MinimumClockBarrier
