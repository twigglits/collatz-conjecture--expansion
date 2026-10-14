/- Actual inverse branches of attained minimum roots. The least-counterexample
   hypotheses are retained: these necessary restrictions do not prove descent
   for all positive integers or exclude every nontrivial cycle. -/
import MinimumRootSpine

namespace MinimumRootPredecessors
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier
open MinimumGreenKernel MinimumRootSpine

theorem minimum_cut (t n : Nat) :
    minimum n = min (prefixMinimum t n) (minimum (iterate t n)) := by
  induction t generalizing n with
  | zero =>
    have h := MinimumRootSpine.minimum_le_source n
    simp only [prefixMinimum, iterate]
    omega
  | succ t ih =>
    rw [minimum_bellman n, ih (C n)]
    simp only [prefixMinimum, iterate, Nat.min_assoc]

theorem all_odd_prefix_transport (k t q : Nat) (hq : 0 < q) :
    prefixMinimum (2 * k + t) (2 ^ k * q - 1) =
      min (2 ^ k * q - 1) (prefixMinimum t (3 ^ k * q - 1)) := by
  have h := odd_block k 0 q hq
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at h
  rw [prefix_concatenation, h.1, h.2]

theorem all_odd_global_transport (k q : Nat) (hq : 0 < q) :
    minimum (2 ^ k * q - 1) = min (2 ^ k * q - 1) (minimum (3 ^ k * q - 1)) := by
  have h := odd_block k 0 q hq
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at h
  rw [minimum_cut (2 * k), h.1, h.2]

theorem all_odd_root_predecessor (k q : Nat) (hq : 0 < q)
    (hm : minimum (3 ^ k * q - 1) = 3 ^ k * q - 1) :
    minimum (2 ^ k * q - 1) = 2 ^ k * q - 1 := by
  have hp := Nat.mul_le_mul_right q (Nat.pow_le_pow_left (by decide : 2 ≤ 3) k)
  rw [all_odd_global_transport k q hq, hm]
  omega

theorem contracting_parent (q : Nat) (hm : minimum (3 * q + 2) = 3 * q + 2) :
    minimum (2 * q + 1) = 2 * q + 1 ∧ nextRoot (2 * q + 1) = 3 * q + 2 := by
  have hc : C (2 * q + 1) = 2 * (3 * q + 2) := by unfold C; split <;> omega
  constructor
  · rw [minimum_odd, hm]
    omega
  · simp only [nextRoot, hc, minimum_even, hm]

theorem contracting_parent_smallest {a q : Nat} (ha : 0 < a) (hm : minimum a = a)
    (hs : nextRoot a = 3 * q + 2) : 2 * q + 1 ≤ a := by
  have hu := next_root_upper ha hm
  rw [hs] at hu
  omega

theorem contracting_parent_divisible_three (q : Nat) :
    (2 * q + 1) % 3 = 0 ↔ (3 * q + 2) % 9 = 5 := by omega

theorem root_index_mono (n : Nat) {i j : Nat} (hij : i ≤ j) : root i n ≤ root j n := by
  induction j with
  | zero =>
    have hi : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases he : i = j + 1
    · subst i; exact Nat.le_refl _
    · have hl := ih (by omega)
      have hr := root_monotone j n
      omega

theorem contracting_parent_off_spine {n j q : Nat}
    (hnp : ¬ EventuallyPeriodic n) (he : root (j + 1) n = 3 * q + 2)
    (hlt : 2 * q + 1 < root j n) :
    minimum (2 * q + 1) = 2 * q + 1 ∧ ∀ i, root i n ≠ 2 * q + 1 := by
  have hm : minimum (3 * q + 2) = 3 * q + 2 := by
    rw [← he]
    exact root_self (j + 1) n
  have hp := contracting_parent q hm
  refine ⟨hp.1, ?_⟩
  intro i hi
  have hj := root_strict hnp j
  by_cases hil : i < j
  · have hb := root_index_mono n (show i + 1 ≤ j by omega)
    have hs : root (i + 1) n = 3 * q + 2 := by
      change nextRoot (root i n) = _
      rw [hi, hp.2]
    omega
  · have hb := root_index_mono n (show j ≤ i by omega)
    omega

theorem least_coalescing_predecessor {a p s t : Nat} (ha : LeastCounterexample a)
    (hp : 0 < p) (he : iterate s p = iterate t a) : a ≤ p := by
  apply Classical.byContradiction
  intro hno
  have hr := reaches_after_iterate s p (ha.2.2 p hp (by omega))
  rw [he] at hr
  exact ha.2.1 (reaches_of_iterate hr)

theorem contracting_parent_off_orbit {n j q : Nat}
    (hnp : ¬ EventuallyPeriodic n) (he : root (j + 1) n = 3 * q + 2)
    (hlt : 2 * q + 1 < root j n) : ∀ t, iterate t n ≠ 2 * q + 1 := by
  have hm : minimum (3 * q + 2) = 3 * q + 2 := by
    rw [← he]
    exact root_self (j + 1) n
  have hp := contracting_parent q hm
  have hj := root_strict hnp j
  intro t ht
  by_cases hc : t < rootClock j n
  · have hpath : iterate (rootClock j n - t) (2 * q + 1) = root j n := by
      rw [← ht, ← iterate_add, Nat.add_sub_of_le (Nat.le_of_lt hc), root_clock_attained]
    cases hd : rootClock j n - t with
    | zero => omega
    | succ d =>
      have hl := minimum_le (C (2 * q + 1)) d
      change nextRoot (2 * q + 1) ≤ iterate d (C (2 * q + 1)) at hl
      rw [hp.2] at hl
      rw [hd] at hpath
      change iterate d (C (2 * q + 1)) = root j n at hpath
      omega
  · have hpath : iterate (t - rootClock j n) (root j n) = 2 * q + 1 := by
      rw [← root_clock_attained j n, ← iterate_add, Nat.add_sub_of_le (by omega)]
      exact ht
    have hl := (minimum_self_iff (root j n)).mp (root_self j n) (t - rootClock j n)
    rw [hpath] at hl
    omega

theorem least_root_predecessor {a p s k : Nat} (ha : LeastCounterexample a)
    (hp : 0 < p) (he : iterate s p = root k a) : a ≤ p := by
  apply least_coalescing_predecessor (s := s) (t := rootClock k a) ha hp
  rw [root_clock_attained k a]
  exact he

theorem least_successor_alternative {a : Nat} (ha : LeastCounterexample a) :
    nextRoot a % 3 = 1 ∨ 2 * nextRoot a = 3 * a + 1 := by
  have hm := least_minimum ha
  have h3 := next_root_not_zero_mod3 ha.1 hm
  have hu := next_root_upper ha.1 hm
  by_cases he : nextRoot a % 3 = 1
  · exact Or.inl he
  · have hb : nextRoot a = 3 * (nextRoot a / 3) + 2 := by omega
    let p := 2 * (nextRoot a / 3) + 1
    have hpath : iterate 2 p = nextRoot a := by
      change C (C p) = _
      have hc : C p = 2 * nextRoot a := by unfold p C; split <;> omega
      rw [hc]
      unfold C
      split <;> omega
    have hl := least_root_predecessor (k := 1) ha (show 0 < p by unfold p; omega)
      (show iterate 2 p = root 1 a by
        change iterate 2 p = nextRoot (minimum a)
        rwa [hm])
    right
    unfold p at hl
    omega

theorem least_ternary_power_excluded {a : Nat} (ha : LeastCounterexample a) (k : Nat) :
    ¬ 3 ^ (k + 1) ∣ root k a + 1 := by
  rintro ⟨q, hq⟩
  have hqp : 0 < q := by
    by_cases hz : q = 0
    · subst q; simp only [Nat.mul_zero] at hq; omega
    · omega
  have h2 := Nat.two_pow_pos k
  have h3 : 0 < 3 ^ k := Nat.pow_pos (by decide)
  have hsp : 0 < 2 ^ (k + 1) * q - 1 := by
    have hp := Nat.mul_pos h2 hqp
    rw [Nat.pow_succ]
    have he : 2 ^ k * 2 * q = 2 * (2 ^ k * q) := by grind
    omega
  have hblock := (odd_block (k + 1) 0 q hqp).1
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hblock
  have he : iterate (2 * (k + 1)) (2 ^ (k + 1) * q - 1) = root k a := by
    rw [hblock]
    omega
  have hl := least_root_predecessor ha hsp he
  have hp : a + 1 ≤ 2 ^ (k + 1) * q := by omega
  have hu := root_upper k a ha.1
  rw [least_minimum ha] at hu
  have hc : 3 * (2 ^ k * 3 ^ k * q) ≤ 2 * (2 ^ k * 3 ^ k * q) := by
    calc
      _ = 2 ^ k * (root k a + 1) := by rw [hq, Nat.pow_succ]; grind
      _ ≤ 3 ^ k * (a + 1) := hu
      _ ≤ 3 ^ k * (2 ^ (k + 1) * q) := Nat.mul_le_mul_left (3 ^ k) hp
      _ = _ := by rw [Nat.pow_succ]; grind
  have hpos := Nat.mul_pos (Nat.mul_pos h2 h3) hqp
  omega

theorem least_saturated_ternary_block {a : Nat} (ha : LeastCounterexample a)
    (k : Nat) (hk : 0 < k) (hd : 3 ^ k ∣ root k a + 1) :
    ∃ q, 0 < q ∧ a = 2 ^ k * q - 1 ∧ root k a = 3 ^ k * q - 1 ∧
      iterate (2 * k) a = root k a := by
  obtain ⟨q, hq⟩ := hd
  have hqp : 0 < q := by
    by_cases hz : q = 0
    · subst q; simp only [Nat.mul_zero] at hq; omega
    · omega
  have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hsp : 0 < 2 ^ k * q - 1 := by
    have hp := Nat.mul_le_mul_left (2 ^ k) hqp
    simp only [Nat.pow_one] at h2
    omega
  have hblock := (odd_block k 0 q hqp).1
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hblock
  have he : iterate (2 * k) (2 ^ k * q - 1) = root k a := by rw [hblock]; omega
  have hl := least_root_predecessor ha hsp he
  have hu := root_upper k a ha.1
  rw [least_minimum ha, hq] at hu
  have hswap : 2 ^ k * (3 ^ k * q) = 3 ^ k * (2 ^ k * q) := by grind
  rw [hswap] at hu
  have hc := Nat.le_of_mul_le_mul_left hu (Nat.pow_pos (by decide : 0 < 3))
  have haeq : a = 2 ^ k * q - 1 := by omega
  refine ⟨q, hqp, haeq, by omega, ?_⟩
  exact (congrArg (iterate (2 * k)) haeq).trans he

theorem least_saturated_binary_divisibility {a : Nat} (ha : LeastCounterexample a)
    (k : Nat) (hk : 0 < k) (hd : 3 ^ k ∣ root k a + 1) : 2 ^ k ∣ a + 1 := by
  obtain ⟨q, hq, he, _, _⟩ := least_saturated_ternary_block ha k hk hd
  refine ⟨q, ?_⟩
  have hp := Nat.mul_pos (Nat.two_pow_pos k) hq
  omega

theorem least_successor_strict {a : Nat} (ha : LeastCounterexample a)
    (hs : 2 * nextRoot a < 3 * a + 1) : nextRoot a % 3 = 1 := by
  have h := least_successor_alternative ha
  omega

theorem least_odd_predecessor_bound {a : Nat} (ha : LeastCounterexample a)
    (j t q : Nat) (hj : 0 < j) (hq : 0 < q)
    (he : iterate t a = 3 ^ j * q - 1) : a + 1 ≤ 2 ^ j * q := by
  have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) hj
  have hsp : 0 < 2 ^ j * q - 1 := by
    have hp := Nat.mul_le_mul_left (2 ^ j) hq
    simp only [Nat.pow_one] at h2
    omega
  have hblock := (odd_block j 0 q hq).1
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hblock
  have hp := least_coalescing_predecessor ha hsp (hblock.trans he.symm)
  omega

theorem odd_ancestor_height_compare (d j q : Nat) (hq : 0 < q)
    (hh : 3 ^ d ≤ 3 ^ j * q) : 2 ^ d ≤ 2 ^ j * q := by
  by_cases hj : d ≤ j
  · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    have hm := Nat.mul_le_mul_left (2 ^ j) hq
    omega
  · have hd : d = j + (d - j) := by omega
    rw [hd, Nat.pow_add] at hh ⊢
    have hc := Nat.le_of_mul_le_mul_left hh (Nat.pow_pos (by decide : 0 < 3))
    have hp := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (d - j)
    exact Nat.mul_le_mul_left (2 ^ j) (by omega)

theorem all_odd_height_barrier (a d j q : Nat) (hq : 0 < q)
    (ha : a < 2 ^ d) (hh : 3 ^ d ≤ 3 ^ j * q) : a ≤ 2 ^ j * q - 1 := by
  have h := odd_ancestor_height_compare d j q hq hh
  omega

set_option maxRecDepth 100000 in
theorem finite_branch_witness :
    iterate 26 27 = 155 ∧ iterate 44 27 = 167 ∧
      prefixMinimum 38 155 = 155 ∧ prefixMinimum 37 (C 155) = 167 ∧
      iterate 2 111 = 167 ∧ (∀ t : Fin 65, iterate t.val 27 ≠ 111) ∧
      ReachesOne 155 ∧ ReachesOne 167 ∧ ReachesOne 111 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨85, by decide +kernel⟩, ⟨67, by decide +kernel⟩, ⟨69, by decide +kernel⟩⟩

#print axioms minimum_cut
#print axioms all_odd_prefix_transport
#print axioms all_odd_global_transport
#print axioms all_odd_root_predecessor
#print axioms contracting_parent
#print axioms contracting_parent_smallest
#print axioms contracting_parent_divisible_three
#print axioms root_index_mono
#print axioms contracting_parent_off_spine
#print axioms least_coalescing_predecessor
#print axioms contracting_parent_off_orbit
#print axioms least_root_predecessor
#print axioms least_successor_alternative
#print axioms least_ternary_power_excluded
#print axioms least_saturated_ternary_block
#print axioms least_saturated_binary_divisibility
#print axioms least_successor_strict
#print axioms least_odd_predecessor_bound
#print axioms odd_ancestor_height_compare
#print axioms all_odd_height_barrier
#print axioms finite_branch_witness

end MinimumRootPredecessors
