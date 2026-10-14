/- Mixed inverse words can cross the all-odd ancestry height barrier.
   These finite paths do not establish that a least counterexample meets them. -/
import MinimumRootPredecessors
import MinimumCriticalClockLift
import MarkedPreimageAudit

namespace MinimumMixedAncestry
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier
open MinimumRootPredecessors MinimumCriticalClockLift

theorem word_minimum_transport (w : List Nat) (n b : Nat)
    (hw : MarkedPreimageAudit.Chain w n b) :
    minimum n = min (prefixMinimum (w.length + w.sum) n) (minimum b) := by
  rw [minimum_cut (w.length + w.sum), MarkedPreimageAudit.chain_clock w n b hw]

theorem least_word_predecessor {a p t : Nat} (ha : LeastCounterexample a)
    (w : List Nat) (hw : MarkedPreimageAudit.PositiveWord w)
    (hb : iterate t a % 2 = 1)
    (he : MarkedPreimageAudit.AffineEquation w p (iterate t a)) : a ≤ p := by
  have hc := MarkedPreimageAudit.affine_chain w p (iterate t a) hw hb he
  have hp := MarkedPreimageAudit.chain_start_odd w p (iterate t a) hc
  exact least_coalescing_predecessor ha (by omega)
    (MarkedPreimageAudit.chain_clock w p (iterate t a) hc)

theorem least_word_affine_lower {a p t : Nat} (ha : LeastCounterexample a)
    (w : List Nat) (hw : MarkedPreimageAudit.PositiveWord w)
    (hb : iterate t a % 2 = 1)
    (he : MarkedPreimageAudit.AffineEquation w p (iterate t a)) :
    3 ^ w.length * a + MarkedPreimageAudit.numerator w ≤ 2 ^ w.sum * iterate t a := by
  have hl := Nat.mul_le_mul_left (3 ^ w.length) (least_word_predecessor ha w hw hb he)
  unfold MarkedPreimageAudit.AffineEquation at he
  omega

theorem two_binary_below_ternary (k : Nat) (hk : 2 ≤ k) : 2 * 2 ^ k ≤ 3 ^ k := by
  have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (k - 2)
  have hk' : k = (k - 2) + 2 := by omega
  have h2 : 2 ^ k = 4 * 2 ^ (k - 2) := by
    calc
      2 ^ k = 2 ^ ((k - 2) + 2) := congrArg (fun t => 2 ^ t) hk'
      _ = _ := by rw [Nat.pow_add]; omega
  have h3 : 3 ^ k = 9 * 3 ^ (k - 2) := by
    calc
      3 ^ k = 3 ^ ((k - 2) + 2) := congrArg (fun t => 3 ^ t) hk'
      _ = _ := by rw [Nat.pow_add]; omega
  rw [h2, h3]
  omega

theorem one_even_block (k j q v : Nat) (hk : 2 ≤ k) (hq : 0 < q)
    (hv : 0 < v) (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v) :
    iterate (2 * k + 1 + 2 * j) (2 ^ k * q - 1) = 3 ^ j * v - 1 ∧
    prefixMinimum (2 * k + 1 + 2 * j) (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
  have hp := Nat.mul_pos (Nat.two_pow_pos j) hv
  have hbridge : 3 ^ k * q - 1 = 2 * (2 ^ j * v - 1) := by
    rw [Nat.pow_succ] at hlift
    have hs := Nat.sub_add_cancel (n := 2 ^ j * v) (m := 1) hp
    grind
  have hs := Nat.mul_le_mul_right q (two_binary_below_ternary k hk)
  have habove : 2 ^ k * q - 1 ≤ 2 ^ j * v - 1 := by
    have hh : 2 * 2 ^ k * q = 2 * (2 ^ k * q) := by grind
    omega
  have hf := odd_block k 0 q hq
  have ht := odd_block j 0 v hv
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hf ht
  have hC : C (3 ^ k * q - 1) = 2 ^ j * v - 1 := by
    rw [hbridge]
    unfold C
    split <;> omega
  have he : iterate (2 * k + 1) (2 ^ k * q - 1) = 2 ^ j * v - 1 := by
    rw [iterate_add, hf.1]
    exact hC
  have hm : prefixMinimum (2 * k + 1) (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
    rw [prefix_concatenation, hf.1, hf.2]
    simp only [prefixMinimum, hC]
    omega
  constructor
  · rw [iterate_add, he, ht.1]
  · rw [prefix_concatenation, he, hm, ht.2]
    omega

theorem one_even_global_transport (k j q v : Nat) (hk : 2 ≤ k) (hq : 0 < q)
    (hv : 0 < v) (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v) :
    minimum (2 ^ k * q - 1) = min (2 ^ k * q - 1) (minimum (3 ^ j * v - 1)) := by
  have h := one_even_block k j q v hk hq hv hlift
  rw [minimum_cut (2 * k + 1 + 2 * j), h.1, h.2]

theorem one_even_root_predecessor (k j q v : Nat) (hk : 2 ≤ k) (hq : 0 < q)
    (hv : 0 < v) (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v)
    (hm : minimum (3 ^ j * v - 1) = 3 ^ j * v - 1) :
    minimum (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
  have h := one_even_block k j q v hk hq hv hlift
  have hl := prefix_le_endpoint (2 * k + 1 + 2 * j) (2 ^ k * q - 1)
  rw [h.1, h.2] at hl
  rw [one_even_global_transport k j q v hk hq hv hlift, hm]
  omega

theorem least_one_even_predecessor {a : Nat} (ha : LeastCounterexample a)
    (k j q v t : Nat) (hk : 2 ≤ k) (hq : 0 < q) (hv : 0 < v)
    (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v)
    (htarget : iterate t a = 3 ^ j * v - 1) : a + 1 ≤ 2 ^ k * q := by
  have h := (one_even_block k j q v hk hq hv hlift).1
  have h2 : 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hq' := Nat.mul_le_mul_left (2 ^ k) hq
  have hl := least_coalescing_predecessor ha (show 0 < 2 ^ k * q - 1 by omega)
    (h.trans htarget.symm)
  omega

theorem doubled_nonterminal_has_no_odd_parent (c : Nat) (hc : c % 3 = 2) :
    ¬ 3 ∣ 2 * c + 1 := by
  rintro ⟨q, hq⟩
  omega

theorem doubling_inverse_improves_iff (c k q : Nat) (hc : 0 < c) (hq : 0 < q)
    (he : 2 * c + 1 = 3 ^ k * q) : 2 ^ k * q - 1 < c ↔ 2 ≤ k := by
  constructor
  · intro hl
    by_cases hk : 2 ≤ k
    · exact hk
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> simp only [Nat.pow_zero, Nat.pow_one, Nat.one_mul] at * <;> omega
  · intro hk
    have hh := Nat.mul_le_mul_right q (two_binary_below_ternary k hk)
    have hs : 2 * 2 ^ k * q = 2 * (2 ^ k * q) := by grind
    omega

theorem maximal_doubling_inverse_residue (c k q : Nat) (hq : q % 3 ≠ 0)
    (he : 2 * c + 1 = 3 ^ k * q) : 2 ≤ k ↔ c % 9 = 4 := by
  constructor
  · intro hk
    have hk' : k = (k - 2) + 2 := by omega
    have hp : 3 ^ k = 9 * 3 ^ (k - 2) := by
      calc
        3 ^ k = 3 ^ ((k - 2) + 2) := congrArg (fun t => 3 ^ t) hk'
        _ = _ := by rw [Nat.pow_add]; omega
    rw [hp] at he
    have hm : 9 * 3 ^ (k - 2) * q = 9 * (3 ^ (k - 2) * q) := by grind
    omega
  · intro hc
    by_cases hk : 2 ≤ k
    · exact hk
    · have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> simp only [Nat.pow_zero, Nat.pow_one, Nat.one_mul] at * <;> omega

theorem least_not_four_mod_nine {a : Nat} (ha : LeastCounterexample a) : a % 9 ≠ 4 := by
  intro hmod
  have he : a = 9 * (a / 9) + 4 := by omega
  have hlift : 3 ^ 2 * (2 * (a / 9) + 1) + 1 = 2 ^ (0 + 1) * (a + 1) := by omega
  have hl := least_one_even_predecessor ha 2 0 (2 * (a / 9) + 1) (a + 1) 0
    (by decide) (by omega) (by omega) hlift (by simp only [iterate, Nat.pow_zero, Nat.one_mul]; omega)
  omega

theorem shortcut_append (k t n : Nat) :
    CollatzAffine.orbit (k + t) n = CollatzAffine.orbit t (CollatzAffine.orbit k n) ∧
    CollatzAffine.wt (k + t) n = CollatzAffine.wt k n + CollatzAffine.wt t (CollatzAffine.orbit k n) := by
  induction k generalizing n with
  | zero => simp [CollatzAffine.orbit, CollatzAffine.wt]
  | succ k ih =>
    have h := ih (CollatzAffine.U n)
    simp only [Nat.succ_add, CollatzAffine.orbit, CollatzAffine.wt, h.1, h.2, Nat.add_assoc]
    constructor <;> trivial

theorem shortcut_odd_block (k m q : Nat) (hq : 0 < q) :
    CollatzAffine.orbit k (2 ^ (k + m) * q - 1) = 2 ^ m * 3 ^ k * q - 1 ∧
    CollatzAffine.wt k (2 ^ (k + m) * q - 1) = k := by
  induction k generalizing q with
  | zero => simp [CollatzAffine.orbit, CollatzAffine.wt]
  | succ k ih =>
    have hp := Nat.mul_pos (Nat.two_pow_pos (k + m)) hq
    have he : 2 ^ (k + 1 + m) * q = 2 * (2 ^ (k + m) * q) := by
      rw [show k + 1 + m = k + m + 1 by omega, Nat.pow_succ]
      grind
    have ho : (2 * (2 ^ (k + m) * q) - 1) % 2 = 1 := by omega
    have hu : CollatzAffine.U (2 * (2 ^ (k + m) * q) - 1) =
        2 ^ (k + m) * (3 * q) - 1 := by
      unfold CollatzAffine.U
      rw [if_pos ho]
      have hh : 2 ^ (k + m) * (3 * q) = 3 * (2 ^ (k + m) * q) := by grind
      omega
    have ht := ih (3 * q) (by omega)
    rw [he]
    simp only [CollatzAffine.orbit, CollatzAffine.wt, hu, ho, ht.1, ht.2, Nat.pow_succ]
    exact ⟨by grind, by omega⟩

theorem one_even_shortcut_count (k j q v : Nat) (hq : 0 < q) (hv : 0 < v)
    (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v) :
    CollatzAffine.orbit (k + 1 + j) (2 ^ k * q - 1) = 3 ^ j * v - 1 ∧
    CollatzAffine.wt (k + 1 + j) (2 ^ k * q - 1) = k + j := by
  have hf := shortcut_odd_block k 0 q hq
  have ht := shortcut_odd_block j 0 v hv
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hf ht
  have hp := Nat.mul_pos (Nat.two_pow_pos j) hv
  have hbridge : 3 ^ k * q - 1 = 2 * (2 ^ j * v - 1) := by
    rw [Nat.pow_succ] at hlift
    have hs := Nat.sub_add_cancel (n := 2 ^ j * v) (m := 1) hp
    grind
  have ho : (3 ^ k * q - 1) % 2 = 0 := by omega
  have hu : CollatzAffine.U (3 ^ k * q - 1) = 2 ^ j * v - 1 := by
    unfold CollatzAffine.U
    rw [if_neg (by omega)]
    omega
  have ha := shortcut_append k (1 + j) (2 ^ k * q - 1)
  rw [hf.1, hf.2] at ha
  have h1 : 1 + j = j + 1 := by omega
  have ht1 : CollatzAffine.orbit (1 + j) (3 ^ k * q - 1) = 3 ^ j * v - 1 ∧
      CollatzAffine.wt (1 + j) (3 ^ k * q - 1) = j := by
    simp only [h1, CollatzAffine.orbit, CollatzAffine.wt, ho, hu, ht.1, ht.2, Nat.zero_add]
    constructor <;> trivial
  rw [ht1.1, ht1.2] at ha
  simpa only [Nat.add_assoc] using ha

def mixedLift : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let a := mixedLift j
    if ((15 * 9 ^ a + 1) / 2 ^ (j + 3)) % 2 = 0 then a else a + 2 ^ j

theorem mixed_lift_spec (j : Nat) :
    mixedLift j < 2 ^ j ∧ ∃ q, 15 * 9 ^ mixedLift j + 1 = 2 ^ (j + 3) * q := by
  induction j with
  | zero => exact ⟨by decide, 2, by decide⟩
  | succ j ih =>
    obtain ⟨ha, q, hq⟩ := ih
    obtain ⟨c, hc⟩ := nine_power_top_bit j
    have hdiv : (15 * 9 ^ mixedLift j + 1) / 2 ^ (j + 3) = q := by
      rw [hq, Nat.mul_div_right _ (Nat.two_pow_pos _)]
    have hpow : 2 ^ (j + 1 + 3) = 2 * 2 ^ (j + 3) := by
      rw [show j + 1 + 3 = (j + 3) + 1 by omega, Nat.pow_succ]
      omega
    have hodd : (15 * 9 ^ mixedLift j) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.pow_mod]
      simp
    simp only [mixedLift, hdiv]
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
      · let w := q + (15 * 9 ^ mixedLift j) * (2 * c + 1)
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

def firstLength (j : Nat) : Nat := 2 * (mixedLift j + 2 ^ j) + 1
def mixedSource (j : Nat) : Nat := 5 * 2 ^ firstLength j - 1
def mixedQuotient (j : Nat) : Nat := (5 * 3 ^ firstLength j + 1) / 2 ^ (j + 3)
def mixedTarget (j : Nat) : Nat := 3 ^ (j + 2) * mixedQuotient j - 1
def mixedClock (j : Nat) : Nat := 2 * firstLength j + 1 + 2 * (j + 2)

theorem first_length_bounds (j : Nat) :
    2 ^ (j + 1) + 1 ≤ firstLength j ∧ firstLength j < 2 ^ (j + 2) + 1 := by
  have ha := (mixed_lift_spec j).1
  simp only [firstLength, Nat.pow_succ]
  omega

theorem mixed_family_congruence (j : Nat) :
    0 < mixedQuotient j ∧ 5 * 3 ^ firstLength j + 1 = 2 ^ (j + 3) * mixedQuotient j := by
  obtain ⟨_, q, hq⟩ := mixed_lift_spec j
  obtain ⟨c, hc⟩ := nine_power_top_bit j
  have hp : 5 * 3 ^ firstLength j = 15 * 9 ^ mixedLift j * 9 ^ (2 ^ j) := by
    simp only [firstLength, Nat.pow_succ, Nat.pow_mul, Nat.pow_add]
    grind
  let v := q + 15 * 9 ^ mixedLift j * (2 * c + 1)
  have hv : 0 < v := by
    have ha : 0 < 9 ^ mixedLift j := Nat.pow_pos (by decide)
    have hb := Nat.mul_pos (show 0 < 15 * 9 ^ mixedLift j by omega) (show 0 < 2 * c + 1 by omega)
    dsimp [v]
    omega
  have he : 5 * 3 ^ firstLength j + 1 = 2 ^ (j + 3) * v := by
    rw [hp, hc]
    dsimp [v]
    grind
  have hvq : mixedQuotient j = v := by
    unfold mixedQuotient
    rw [he, Nat.mul_div_right _ (Nat.two_pow_pos _)]
  rw [hvq]
  exact ⟨hv, he⟩

theorem mixed_family_path (j : Nat) :
    iterate (mixedClock j) (mixedSource j) = mixedTarget j ∧
    prefixMinimum (mixedClock j) (mixedSource j) = mixedSource j := by
  have h := mixed_family_congruence j
  have hk := (first_length_bounds j).1
  have hp := Nat.two_pow_pos (j + 1)
  have he : 3 ^ firstLength j * 5 + 1 = 2 ^ (j + 2 + 1) * mixedQuotient j := by
    simpa only [Nat.mul_comm, Nat.add_assoc] using h.2
  have ht := one_even_block (firstLength j) (j + 2) 5 (mixedQuotient j)
    (by omega) (by decide) h.1 he
  simpa only [mixedClock, mixedSource, mixedTarget, Nat.mul_comm] using ht

theorem mixed_family_one_even (j : Nat) :
    CollatzAffine.orbit (firstLength j + 1 + (j + 2)) (mixedSource j) = mixedTarget j ∧
    CollatzAffine.wt (firstLength j + 1 + (j + 2)) (mixedSource j) = firstLength j + (j + 2) := by
  have h := mixed_family_congruence j
  have he : 3 ^ firstLength j * 5 + 1 = 2 ^ (j + 2 + 1) * mixedQuotient j := by
    simpa only [Nat.mul_comm, Nat.add_assoc] using h.2
  have ht := one_even_shortcut_count (firstLength j) (j + 2) 5 (mixedQuotient j)
    (by decide) h.1 he
  simpa only [mixedSource, mixedTarget, Nat.mul_comm] using ht

theorem mixed_source_scale (j : Nat) :
    mixedSource j + 1 = 5 * 2 ^ firstLength j ∧
    mixedSource j + 2 < 2 ^ (firstLength j + 3) := by
  have hp := Nat.two_pow_pos (firstLength j)
  simp only [mixedSource, Nat.pow_add]
  omega

theorem mixed_source_growth (j : Nat) : j < mixedSource j := by
  have hk := (first_length_bounds j).1
  have hj := Nat.lt_two_pow_self (n := j + 1)
  have hp := Nat.lt_two_pow_self (n := firstLength j)
  simp only [mixedSource]
  omega

theorem mixed_target_scale (j : Nat) :
    2 ^ (j + 3) * (mixedTarget j + 1) =
      3 ^ (j + 2) * (5 * 3 ^ firstLength j + 1) := by
  have h := mixed_family_congruence j
  have hp := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3) (n := j + 2)) h.1
  have hs : mixedTarget j + 1 = 3 ^ (j + 2) * mixedQuotient j := by
    unfold mixedTarget
    omega
  rw [hs, h.2]
  grind

theorem mixed_target_height (j h : Nat) (hh : 24 * h * 2 ^ j ≤ 5 * 3 ^ j) :
    h * 3 ^ (firstLength j + 3) ≤ mixedTarget j + 1 := by
  have he := mixed_target_scale j
  have hp := Nat.mul_le_mul_right (9 * 3 ^ firstLength j) hh
  have hm : (24 * h * 2 ^ j) * (9 * 3 ^ firstLength j) =
      2 ^ (j + 3) * (h * 3 ^ (firstLength j + 3)) := by
    rw [Nat.pow_add, Nat.pow_add]
    grind
  have hb : (5 * 3 ^ j) * (9 * 3 ^ firstLength j) ≤
      3 ^ (j + 2) * (5 * 3 ^ firstLength j + 1) := by
    rw [Nat.pow_add]
    grind
  rw [hm] at hp
  have ht := Nat.le_trans hp hb
  rw [← he] at ht
  exact Nat.le_of_mul_le_mul_left ht (Nat.two_pow_pos (j + 3))

theorem linear_three_two (j : Nat) : (j + 2) * 2 ^ j ≤ 2 * 3 ^ j := by
  induction j with
  | zero => decide
  | succ j ih =>
    have hi := Nat.mul_le_mul_left 3 ih
    have hc := Nat.mul_le_mul_right (2 ^ j) (show 2 * (j + 3) ≤ 3 * (j + 2) by omega)
    rw [Nat.pow_succ, Nat.pow_succ]
    grind

theorem mixed_family_height_factor (j h : Nat) (hh : 10 * h ≤ j) :
    h * 3 ^ (firstLength j + 3) ≤ mixedTarget j + 1 := by
  apply mixed_target_height j h
  have hp := Nat.mul_le_mul_left 5 (linear_three_two j)
  have hl := Nat.mul_le_mul_right (2 ^ j) (show 48 * h ≤ 5 * (j + 2) by omega)
  grind

theorem one_even_beats_all_odd (j : Nat) (hj : 10 ≤ j) :
    ∀ s q, 0 < q → mixedTarget j = 3 ^ s * q - 1 →
      mixedSource j + 2 ≤ 2 ^ s * q - 1 := by
  have hh := mixed_family_height_factor j 1 (by omega)
  simp only [Nat.one_mul] at hh
  intro s q hq htarget
  have hp := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3) (n := s)) hq
  have he : 3 ^ (firstLength j + 3) ≤ 3 ^ s * q := by omega
  exact all_odd_height_barrier (mixedSource j + 2) (firstLength j + 3) s q hq
    (mixed_source_scale j).2 he

theorem unbounded_mixed_improvement (h bound : Nat) :
    ∃ n b d t, bound < n ∧ n + 2 < 2 ^ d ∧
      iterate t n = b ∧ prefixMinimum t n = n ∧
      (h + 1) * 3 ^ d ≤ b + 1 ∧
      ∀ s q, 0 < q → b = 3 ^ s * q - 1 → n + 2 ≤ 2 ^ s * q - 1 := by
  let j := 10 * (h + bound + 1)
  have hj : j = 10 * (h + bound + 1) := rfl
  have hg := mixed_source_growth j
  have hp := mixed_family_path j
  refine ⟨mixedSource j, mixedTarget j, firstLength j + 3, mixedClock j,
    by omega, (mixed_source_scale j).2, hp.1, hp.2, ?_, ?_⟩
  · exact mixed_family_height_factor j (h + 1) (by omega)
  · exact one_even_beats_all_odd j (by omega)

set_option maxRecDepth 100000 in
theorem finite_mixed_witness :
    mixedSource 0 = 39 ∧ mixedTarget 0 = 152 ∧ mixedClock 0 = 11 ∧
    iterate 11 39 = 152 ∧ prefixMinimum 11 39 = 39 ∧
    ReachesOne 39 ∧ ReachesOne 152 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel,
    ⟨34, by decide +kernel⟩, ⟨23, by decide +kernel⟩⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem finite_height_witness :
    mixedSource 4 = 45035996273704959 ∧ mixedTarget 4 = 551968206708544316592375437 ∧
    mixedClock 4 = 119 ∧
    iterate 119 45035996273704959 = 551968206708544316592375437 ∧
    prefixMinimum 119 45035996273704959 = 45035996273704959 ∧
    45035996273704959 + 2 < 2 ^ 56 ∧
    3 ^ 56 ≤ 551968206708544316592375437 + 1 ∧
    ReachesOne 45035996273704959 ∧ ReachesOne 551968206708544316592375437 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨751, by decide +kernel⟩, ⟨632, by decide +kernel⟩⟩

#print axioms word_minimum_transport
#print axioms least_word_predecessor
#print axioms least_word_affine_lower
#print axioms two_binary_below_ternary
#print axioms one_even_block
#print axioms one_even_global_transport
#print axioms one_even_root_predecessor
#print axioms least_one_even_predecessor
#print axioms doubled_nonterminal_has_no_odd_parent
#print axioms doubling_inverse_improves_iff
#print axioms maximal_doubling_inverse_residue
#print axioms least_not_four_mod_nine
#print axioms shortcut_append
#print axioms shortcut_odd_block
#print axioms one_even_shortcut_count
#print axioms mixed_lift_spec
#print axioms first_length_bounds
#print axioms mixed_family_congruence
#print axioms mixed_family_path
#print axioms mixed_family_one_even
#print axioms mixed_source_scale
#print axioms mixed_source_growth
#print axioms mixed_target_scale
#print axioms mixed_target_height
#print axioms linear_three_two
#print axioms mixed_family_height_factor
#print axioms one_even_beats_all_odd
#print axioms unbounded_mixed_improvement
#print axioms finite_mixed_witness
#print axioms finite_height_witness

end MinimumMixedAncestry
