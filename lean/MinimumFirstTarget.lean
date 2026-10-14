/- A smaller coalescing source after a two-halving exit, and exact
   first visits where one-extra-even ancestry does not improve the source. -/
import MinimumMixedAncestry

namespace MinimumFirstTarget
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport MinimumClockBarrier
open MinimumRootPredecessors MinimumMixedAncestry

theorem even_step (x : Nat) : C (2 * x) = x := by
  unfold C
  split <;> omega

theorem half_source_meeting (k q v : Nat) (hq : 0 < q)
    (he : 3 ^ k * q = 4 * v + 3) :
    iterate (2 * k + 3) (2 ^ k * q - 1) = 3 * v + 2 ∧
    iterate (2 * k + 4) (2 ^ (k + 1) * q - 1) = 3 * v + 2 := by
  have hp := odd_block k 0 q hq
  have hn := odd_block (k + 1) 0 q hq
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hp hn
  have hpend : 3 ^ k * q - 1 = 2 * (2 * v + 1) := by omega
  have hnend : 3 ^ (k + 1) * q - 1 = 4 * (3 * v + 2) := by
    rw [Nat.pow_succ]
    have hh : 3 ^ k * 3 * q = 3 * (3 ^ k * q) := by grind
    omega
  constructor
  · rw [iterate_add, hp.1, hpend]
    change C (C (C (2 * (2 * v + 1)))) = _
    rw [even_step]
    exact (odd_pair (v + 1) (by omega)).2
  · have hc : 2 * k + 4 = 2 * (k + 1) + 2 := by omega
    rw [hc, iterate_add, hn.1, hnend]
    change C (C (4 * (3 * v + 2))) = _
    have hh : 4 * (3 * v + 2) = 2 * (2 * (3 * v + 2)) := by omega
    rw [hh, even_step, even_step]

theorem least_half_source_bound {a : Nat} (ha : LeastCounterexample a)
    (k q v t : Nat) (hk : 0 < k) (hq : 0 < q)
    (he : 3 ^ k * q = 4 * v + 3)
    (hy : iterate t a = 2 ^ (k + 1) * q - 1) :
    2 * a + 1 ≤ iterate t a := by
  have hm := half_source_meeting k q v hq he
  have h2 : 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hqp := Nat.mul_le_mul_left (2 ^ k) hq
  have hp : 0 < 2 ^ k * q - 1 := by omega
  have hmeet : iterate (2 * k + 3) (2 ^ k * q - 1) = iterate (t + (2 * k + 4)) a := by
    rw [iterate_add t (2 * k + 4) a, hy, hm.1, hm.2]
  have hl := least_coalescing_predecessor ha hp hmeet
  rw [hy, Nat.pow_succ]
  have hh : 2 ^ k * 2 * q = 2 * (2 ^ k * q) := by grind
  omega

theorem near_source_exit_constraint {a : Nat} (ha : LeastCounterexample a)
    (k q t : Nat) (hk : 0 < k) (hq : q % 2 = 1)
    (hy : iterate t a = 2 ^ (k + 1) * q - 1) (hnear : iterate t a ≤ 2 * a) :
    (3 ^ (k + 1) * q) % 4 = 3 := by
  have hqp : 0 < q := by omega
  have hpodd : (3 ^ k * q) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hq]
    simp
  by_cases he : (3 ^ k * q) % 4 = 3
  · have hv : 3 ^ k * q = 4 * ((3 ^ k * q) / 4) + 3 := by omega
    have hl := least_half_source_bound ha k q ((3 ^ k * q) / 4) t hk hqp hv hy
    omega
  · have hm : (3 ^ k * q) % 4 = 1 := by omega
    rw [Nat.pow_succ]
    have heq : 3 ^ k * 3 * q = 3 * (3 ^ k * q) := by grind
    rw [heq]
    omega

theorem least_initial_exit_constraint {a : Nat} (ha : LeastCounterexample a)
    (k q : Nat) (hk : 0 < k) (hq : q % 2 = 1)
    (hy : a = 2 ^ (k + 1) * q - 1) : (3 ^ (k + 1) * q) % 4 = 3 := by
  exact near_source_exit_constraint ha k q 0 hk hq hy (by simp only [iterate]; omega)

def blockLength (h : Nat) : Nat := 6 * h + 3
def source (h : Nat) : Nat := 5 * 2 ^ blockLength h - 1
def quotient (h : Nat) : Nat := (5 * 3 ^ blockLength h + 1) / 4
def target (h : Nat) : Nat := 3 * quotient h - 1
def targetClock (h : Nat) : Nat := 2 * blockLength h + 3

theorem family_congruence (h : Nat) :
    0 < quotient h ∧ 4 * quotient h = 5 * 3 ^ blockLength h + 1 := by
  have hp : 3 ^ blockLength h % 4 = 3 := by
    simp only [blockLength, Nat.pow_add, Nat.pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    simp
  have hh : (5 * 3 ^ blockLength h + 1) % 4 = 0 := by omega
  have he := Nat.mod_add_div (5 * 3 ^ blockLength h + 1) 4
  rw [hh] at he
  simp only [quotient]
  omega

theorem family_path (h : Nat) :
    iterate (targetClock h) (source h) = target h ∧
    prefixMinimum (targetClock h) (source h) = source h := by
  have hc := family_congruence h
  have he : 3 ^ blockLength h * 5 + 1 = 2 ^ (1 + 1) * quotient h := by omega
  have hp := one_even_block (blockLength h) 1 5 (quotient h)
    (by unfold blockLength; omega) (by decide) hc.1 he
  simpa only [source, target, targetClock, Nat.pow_one, Nat.mul_comm, Nat.add_assoc] using hp

theorem family_one_even (h : Nat) :
    CollatzAffine.orbit (blockLength h + 2) (source h) = target h ∧
    CollatzAffine.wt (blockLength h + 2) (source h) = blockLength h + 1 := by
  have hc := family_congruence h
  have he : 3 ^ blockLength h * 5 + 1 = 2 ^ (1 + 1) * quotient h := by omega
  have hp := one_even_shortcut_count (blockLength h) 1 5 (quotient h) (by decide) hc.1 he
  simpa only [source, target, Nat.pow_one, Nat.mul_comm, Nat.add_assoc] using hp

theorem family_target_residue (h : Nat) : target h % 27 = 20 := by
  have hc := family_congruence h
  have hp : 3 ^ blockLength h = 27 * 729 ^ h := by
    simp only [blockLength, Nat.pow_add, Nat.pow_mul]
    grind
  have he : 4 * target h + 1 = 15 * 3 ^ blockLength h := by
    unfold target
    omega
  rw [hp] at he
  have hh : 15 * (27 * 729 ^ h) = 27 * (15 * 729 ^ h) := by grind
  omega

theorem family_source_residue (h : Nat) : source h % 3 = 0 := by
  have hp : 2 ^ blockLength h % 3 = 2 := by
    simp only [blockLength, Nat.pow_add, Nat.pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    simp
  have hpos := Nat.two_pow_pos (blockLength h)
  unfold source
  omega

theorem family_pair_endpoint (h i : Nat) (hi : i ≤ blockLength h) :
    iterate (2 * i) (source h) = 2 ^ (blockLength h - i) * 3 ^ i * 5 - 1 := by
  have hh := odd_block i (blockLength h - i) 5 (by decide)
  have he : i + (blockLength h - i) = blockLength h := by omega
  rw [he] at hh
  simpa only [source, Nat.mul_comm] using hh.1

theorem family_first_pair_residue (h : Nat) : iterate 2 (source h) % 27 = 5 := by
  have hb : 1 ≤ blockLength h := by unfold blockLength; omega
  have he := family_pair_endpoint h 1 hb
  have hk : blockLength h - 1 = 6 * h + 2 := by unfold blockLength; omega
  have hp : 2 ^ (blockLength h - 1) % 9 = 4 := by
    rw [hk]
    simp only [Nat.pow_add, Nat.pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    simp
  rw [he]
  simp only [Nat.pow_one]
  have hn := Nat.two_pow_pos (blockLength h - 1)
  omega

theorem family_pair_avoids_target (h i : Nat) (hi : i ≤ blockLength h) :
    iterate (2 * i) (source h) % 27 ≠ 20 := by
  by_cases hz : i = 0
  · subst i
    have hs := family_source_residue h
    simp only [iterate]
    omega
  · by_cases ho : i = 1
    · subst i
      have hs := family_first_pair_residue h
      simp only [Nat.mul_one]
      omega
    · have hi2 : 2 ≤ i := by omega
      have he := family_pair_endpoint h i hi
      have hp : 3 ^ i = 9 * 3 ^ (i - 2) := by
        calc
          3 ^ i = 3 ^ ((i - 2) + 2) := congrArg (fun e => 3 ^ e) (by omega)
          _ = _ := by rw [Nat.pow_add]; omega
      have hv : 0 < 2 ^ (blockLength h - i) * 3 ^ (i - 2) * 5 := by
        have ht := Nat.mul_pos (Nat.two_pow_pos (blockLength h - i))
          (Nat.pow_pos (by decide : 0 < 3) (n := i - 2))
        omega
      have hfactor : 2 ^ (blockLength h - i) * 3 ^ i * 5 =
          9 * (2 ^ (blockLength h - i) * 3 ^ (i - 2) * 5) := by rw [hp]; grind
      rw [hfactor] at he
      omega

theorem family_odd_clock_avoids_target (h i : Nat) (hi : i < blockLength h) :
    iterate (2 * i + 1) (source h) % 27 ≠ 20 := by
  have he := family_pair_endpoint h i (by omega)
  have hd : blockLength h - i = (blockLength h - i - 1) + 1 := by omega
  have hp : 0 < 2 ^ (blockLength h - i - 1) * 3 ^ i * 5 := by
    have ht := Nat.mul_pos (Nat.two_pow_pos (blockLength h - i - 1))
      (Nat.pow_pos (by decide : 0 < 3) (n := i))
    omega
  have hfactor : 2 ^ (blockLength h - i) * 3 ^ i * 5 =
      2 * (2 ^ (blockLength h - i - 1) * 3 ^ i * 5) := by
    rw [hd, Nat.pow_succ]
    grind
  rw [hfactor] at he
  have ho : iterate (2 * i) (source h) % 2 = 1 := by omega
  rw [iterate_add (2 * i) 1 (source h)]
  change C (iterate (2 * i) (source h)) % 27 ≠ 20
  unfold C
  rw [if_pos ho]
  omega

theorem family_bridge (h : Nat) :
    iterate (2 * blockLength h + 1) (source h) = 2 * quotient h - 1 ∧
    iterate (2 * blockLength h + 2) (source h) = 2 * target h := by
  have hc := family_congruence h
  have he := family_pair_endpoint h (blockLength h) (Nat.le_refl _)
  simp only [Nat.sub_self, Nat.pow_zero, Nat.one_mul] at he
  have hb : 3 ^ blockLength h * 5 - 1 = 2 * (2 * quotient h - 1) := by omega
  have hs : iterate (2 * blockLength h + 1) (source h) = 2 * quotient h - 1 := by
    rw [iterate_add (2 * blockLength h) 1 (source h), he, hb]
    exact even_step _
  refine ⟨hs, ?_⟩
  have hclock : 2 * blockLength h + 2 = (2 * blockLength h + 1) + 1 := by omega
  rw [hclock, iterate_add, hs]
  exact (odd_pair (quotient h) hc.1).1

theorem family_first_target (h : Nat) :
    iterate (targetClock h) (source h) % 27 = 20 ∧
    ∀ t, t < targetClock h → iterate t (source h) % 27 ≠ 20 := by
  constructor
  · rw [(family_path h).1]
    exact family_target_residue h
  · intro t ht
    by_cases hl : t ≤ 2 * blockLength h
    · by_cases he : t % 2 = 0
      · have ht' : t = 2 * (t / 2) := by omega
        rw [ht']
        exact family_pair_avoids_target h (t / 2) (by omega)
      · have ht' : t = 2 * (t / 2) + 1 := by omega
        rw [ht']
        exact family_odd_clock_avoids_target h (t / 2) (by omega)
    · have hclock : targetClock h = 2 * blockLength h + 3 := rfl
      have ht' : t = 2 * blockLength h + 1 ∨ t = 2 * blockLength h + 2 := by omega
      have hb := family_bridge h
      have hr := family_target_residue h
      have hq := (family_congruence h).1
      have htarget : target h = 3 * quotient h - 1 := rfl
      rcases ht' with rfl | rfl
      · rw [hb.1]
        omega
      · rw [hb.2]
        omega

theorem family_odd_depth (h j v : Nat) (hv : 0 < v)
    (he : target h = 3 ^ j * v - 1) : j ≤ 1 := by
  by_cases hj : j ≤ 1
  · exact hj
  · have hp : 3 ^ j = 9 * 3 ^ (j - 2) := by
      calc
        3 ^ j = 3 ^ ((j - 2) + 2) := congrArg (fun e => 3 ^ e) (by omega)
        _ = _ := by rw [Nat.pow_add]; omega
    have hpos := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3) (n := j - 2)) hv
    rw [hp] at he
    have hh : 9 * 3 ^ (j - 2) * v = 9 * (3 ^ (j - 2) * v) := by grind
    have hr := family_target_residue h
    omega

theorem inverse_five_source_lower (k K q : Nat) (he : 3 ^ k * q = 5 * 3 ^ K) :
    5 * 2 ^ K ≤ 2 ^ k * q := by
  by_cases hk : k ≤ K
  · have h3 : 3 ^ K = 3 ^ k * 3 ^ (K - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h3] at he
    have hh : 3 ^ k * q = 3 ^ k * (5 * 3 ^ (K - k)) := by grind
    have hq := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
    have h2 : 2 ^ K = 2 ^ k * 2 ^ (K - k) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    have hp := Nat.mul_le_mul_left (5 * 2 ^ k)
      (Nat.pow_le_pow_left (by decide : 2 ≤ 3) (K - k))
    rw [hq, h2]
    grind
  · have h3 : 3 ^ k = 3 ^ K * 3 ^ (k - K) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    rw [h3] at he
    have hh : 3 ^ K * (3 ^ (k - K) * q) = 3 ^ K * 5 := by grind
    have hq := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide : 0 < 3)) hh
    have hp : 3 ^ (k - K) % 3 = 0 := by
      rw [Nat.pow_mod]
      have hd : k - K = (k - K - 1) + 1 := by omega
      rw [hd, Nat.pow_succ]
      simp
    have hm := congrArg (fun x : Nat => x % 3) hq
    rw [Nat.mul_mod, hp] at hm
    omega

theorem family_one_even_source_lower (h k j q v : Nat) (hv : 0 < v)
    (hlift : 3 ^ k * q + 1 = 2 ^ (j + 1) * v)
    (he : target h = 3 ^ j * v - 1) : source h ≤ 2 ^ k * q - 1 := by
  have hj := family_odd_depth h j v hv he
  have hr := family_target_residue h
  have hq := family_congruence h
  have htarget : target h = 3 * quotient h - 1 := rfl
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simp only [Nat.pow_zero, Nat.one_mul, Nat.zero_add, Nat.pow_one] at he hlift
    have hk : k = 0 := by
      by_cases hz : k = 0
      · exact hz
      · have hp : 3 ^ k % 3 = 0 := by
          rw [Nat.pow_mod]
          have hd : k = (k - 1) + 1 := by omega
          rw [hd, Nat.pow_succ]
          simp
        have hm := congrArg (fun x : Nat => x % 3) hlift
        rw [Nat.add_mod, Nat.mul_mod, hp] at hm
        omega
    subst k
    simp only [Nat.pow_zero, Nat.one_mul]
    have hp := prefix_le_endpoint (targetClock h) (source h)
    rw [(family_path h).1, (family_path h).2] at hp
    omega
  · simp only [Nat.pow_one] at he
    have hvq : v = quotient h := by omega
    have hf : 3 ^ k * q = 5 * 3 ^ blockLength h := by rw [hvq] at hlift; omega
    have hl := inverse_five_source_lower k (blockLength h) q hf
    unfold source
    omega

theorem family_all_odd_source_lower (h j v : Nat) (hv : 0 < v)
    (he : target h = 3 ^ j * v - 1) : source h ≤ 2 ^ j * v - 1 := by
  have hj := family_odd_depth h j v hv he
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simp only [Nat.pow_zero, Nat.one_mul] at he ⊢
    have hp := prefix_le_endpoint (targetClock h) (source h)
    rw [(family_path h).1, (family_path h).2] at hp
    omega
  · simp only [Nat.pow_one] at he ⊢
    have hq := family_congruence h
    have htarget : target h = 3 * quotient h - 1 := rfl
    have hvq : v = quotient h := by omega
    rw [hvq]
    have hp := Nat.mul_le_mul_left 5 (two_binary_below_ternary (blockLength h)
      (by unfold blockLength; omega))
    unfold source
    omega

theorem family_height_factor (h : Nat) :
    (h + 1) * (source h + 1) ≤ target h + 1 := by
  have hk : blockLength h = 6 * h + 3 := rfl
  have hp := Nat.mul_le_mul_left 3 (linear_three_two (blockLength h))
  have hl := Nat.mul_le_mul_right (2 ^ blockLength h)
    (show 8 * (h + 1) ≤ 3 * (blockLength h + 2) by omega)
  have hs : 4 * (h + 1) * 2 ^ blockLength h ≤ 3 * 3 ^ blockLength h := by grind
  have hc := Nat.mul_le_mul_left 5 hs
  have hq := family_congruence h
  have h2 := Nat.two_pow_pos (blockLength h)
  unfold source target
  have hswap : 5 * (4 * (h + 1) * 2 ^ blockLength h) =
      4 * ((h + 1) * (5 * 2 ^ blockLength h)) := by grind
  have ht : 4 * ((h + 1) * (5 * 2 ^ blockLength h)) ≤ 4 * (3 * quotient h) := by
    rw [← hswap]
    grind
  have hc' := Nat.le_of_mul_le_mul_left ht (by decide : 0 < 4)
  have hp' : 5 * 2 ^ blockLength h - 1 + 1 = 5 * 2 ^ blockLength h := by omega
  rw [hp']
  omega

theorem family_source_growth (h : Nat) : h < source h := by
  have hk : blockLength h = 6 * h + 3 := rfl
  have hp := Nat.lt_two_pow_self (n := blockLength h)
  unfold source
  omega

set_option maxRecDepth 100000 in
theorem finite_first_target_witness :
    source 0 = 39 ∧ target 0 = 101 ∧ targetClock 0 = 9 ∧
    iterate 9 39 = 101 ∧ (∀ t : Fin 9, iterate t.val 39 % 27 ≠ 20) ∧
    source 1 = 2559 ∧ target 1 = 73811 ∧ targetClock 1 = 21 ∧
    iterate 21 2559 = 73811 ∧ (∀ t : Fin 21, iterate t.val 2559 % 27 ≠ 20) ∧
    ReachesOne 39 ∧ ReachesOne 101 ∧ ReachesOne 2559 ∧ ReachesOne 73811 := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨34, by decide +kernel⟩, ⟨25, by decide +kernel⟩,
    ⟨115, by decide +kernel⟩, ⟨94, by decide +kernel⟩⟩

#print axioms even_step
#print axioms half_source_meeting
#print axioms least_half_source_bound
#print axioms near_source_exit_constraint
#print axioms least_initial_exit_constraint
#print axioms family_congruence
#print axioms family_path
#print axioms family_one_even
#print axioms family_target_residue
#print axioms family_source_residue
#print axioms family_pair_endpoint
#print axioms family_first_pair_residue
#print axioms family_pair_avoids_target
#print axioms family_odd_clock_avoids_target
#print axioms family_bridge
#print axioms family_first_target
#print axioms family_odd_depth
#print axioms inverse_five_source_lower
#print axioms family_one_even_source_lower
#print axioms family_all_odd_source_lower
#print axioms family_height_factor
#print axioms family_source_growth
#print axioms finite_first_target_witness

end MinimumFirstTarget
