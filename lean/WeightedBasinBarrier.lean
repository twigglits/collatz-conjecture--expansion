/-
  Backward-closed populations with a single exit, entirely in the basin of 1.
  These obstruct a uniform aggregate contraction based on backward closure
  alone. They are not the actual fixed-floor survivor sets.
  The weighted infinite sums and the fixed-block obstruction are written
  arguments in docs/WEIGHTED-BASIN-BARRIER.md, not formalized analysis here.
-/
import WeightedSurvivors
import CollatzGrowth

namespace WeightedBasinBarrier

set_option maxRecDepth 100000
set_option exponentiation.threshold 10000

open OrdinaryCollatz WeightedSurvivors

def Pull (H : Nat) (S : Nat → Prop) (n : Nat) : Prop := H < n ∧ S (U n)

def Basin (H b n : Nat) : Prop :=
  ∃ k, Survives H k n ∧ shortcutIter k n = b

theorem root_mem (H b : Nat) (hb : H < b) : Basin H b b := by
  refine ⟨0, ?_, rfl⟩
  intro j hj
  have : j = 0 := by omega
  simpa [this, shortcutIter] using hb

theorem pull_into_basin (H b n : Nat) (hn : Pull H (Basin H b) n) :
    Basin H b n := by
  obtain ⟨hn, k, hs, he⟩ := hn
  exact ⟨k + 1, (survives_succ H k n).mpr ⟨hn, hs⟩, he⟩

theorem nonroot_stays (H b n : Nat) (hn : Basin H b n) (hne : n ≠ b) :
    Pull H (Basin H b) n := by
  obtain ⟨k, hs, he⟩ := hn
  cases k with
  | zero => exact False.elim (hne he)
  | succ k =>
    obtain ⟨hn, htail⟩ := (survives_succ H k n).mp hs
    exact ⟨hn, k, htail, he⟩

/-- A nonreturning root is the only exit from its killed ancestor basin. -/
theorem pull_basin_iff (H b n : Nat)
    (hreturn : ∀ k, shortcutIter (k + 1) b ≠ b) :
    Pull H (Basin H b) n ↔ Basin H b n ∧ n ≠ b := by
  constructor
  · intro hn
    refine ⟨pull_into_basin H b n hn, ?_⟩
    intro he
    subst n
    obtain ⟨_, k, _, hk⟩ := hn
    exact hreturn k hk
  · rintro ⟨hn, hne⟩
    exact nonroot_stays H b n hn hne

theorem basin_converges (H b n : Nat) (hb : ReachesOne b) (hn : Basin H b n) :
    ReachesOne n := by
  obtain ⟨k, _, hk⟩ := hn
  obtain ⟨j, _, _, hj⟩ := shortcut_iteration_simulation k n
  exact reaches_of_iterate (n := n) (k := j) (by rwa [hj, hk])

theorem shortcut_add : ∀ k j n,
    shortcutIter (k + j) n = shortcutIter j (shortcutIter k n)
  | 0, _, _ => by simp only [Nat.zero_add, shortcutIter]
  | k + 1, j, n => by
    rw [show k + 1 + j = (k + j) + 1 by omega]
    exact shortcut_add k j (U n)

theorem even_step (n : Nat) : U (2 * n) = n := by unfold U; split <;> omega

theorem power_step (a : Nat) : U (2 ^ (a + 1)) = 2 ^ a := by
  rw [Nat.pow_succ, Nat.mul_comm, even_step]

theorem power_hits (a : Nat) : shortcutIter a (2 ^ a) = 1 := by
  induction a with
  | zero => rfl
  | succ a ih => simpa only [shortcutIter, power_step] using ih

theorem one_two_bound (j : Nat) : shortcutIter j 1 ≤ 2 ∧ shortcutIter j 2 ≤ 2 := by
  induction j with
  | zero => decide
  | succ j ih => exact ⟨ih.2, ih.1⟩

theorem power_orbit_bound (a j : Nat) : shortcutIter j (2 ^ (a + 1)) ≤ 2 ^ (a + 1) := by
  induction a generalizing j with
  | zero => exact (one_two_bound j).2
  | succ a ih =>
    cases j with
    | zero => exact Nat.le_refl _
    | succ j =>
      simp only [shortcutIter, power_step]
      exact Nat.le_trans (ih j) (Nat.pow_le_pow_right (by decide) (by omega))

theorem power_no_return (a j : Nat) :
    shortcutIter (j + 1) (2 ^ (a + 2)) ≠ 2 ^ (a + 2) := by
  have hb := power_orbit_bound a j
  have hp : 0 < 2 ^ (a + 1) := Nat.pow_pos (by decide)
  have he : 2 ^ (a + 2) = 2 ^ (a + 1) * 2 := by rw [Nat.pow_succ]
  simp only [shortcutIter, power_step]
  omega

theorem cubic_factor (p : Nat) :
    (3 * p + 2) ^ 3 + 1 = (3 * p + 3) * (3 * (3 * p * p + 3 * p + 1)) := by
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  simp only [Nat.reduceMul, ← Nat.mul_assoc]
  omega

theorem cubic_lift (k x : Nat) (hx : x % 3 = 2) (hd : 3 ^ k ∣ x + 1) :
    3 ^ (k + 1) ∣ x ^ 3 + 1 := by
  obtain ⟨q, hq⟩ := hd
  have he : x = 3 * (x / 3) + 2 := by omega
  have hp : x ^ 3 + 1 = (x + 1) * (3 * (3 * (x / 3) * (x / 3) + 3 * (x / 3) + 1)) := by
    calc
      x ^ 3 + 1 = (3 * (x / 3) + 2) ^ 3 + 1 := by rw [← he]
      _ = (3 * (x / 3) + 3) * (3 * (3 * (x / 3) * (x / 3) + 3 * (x / 3) + 1)) := cubic_factor _
      _ = _ := by rw [show 3 * (x / 3) + 3 = x + 1 by omega]
  refine ⟨q * (3 * (x / 3) * (x / 3) + 3 * (x / 3) + 1), ?_⟩
  rw [hp, hq, Nat.pow_succ]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- An all-index divisibility construction, not a finite search. -/
theorem power_target_divisibility (k : Nat) : 3 ^ (k + 1) ∣ 2 ^ (3 ^ k) + 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hm : (2 ^ (3 ^ k)) % 3 = 2 := by
      obtain ⟨q, hq⟩ := ih
      have hq' : 2 ^ (3 ^ k) + 1 = 3 * (3 ^ k * q) := by
        simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hq
      omega
    have h := cubic_lift (k + 1) (2 ^ (3 ^ k)) hm ih
    have he : 2 ^ (3 ^ (k + 1)) = (2 ^ (3 ^ k)) ^ 3 := by
      rw [Nat.pow_succ, Nat.pow_mul]
    rw [he]
    exact h

theorem power_target_quotient (k : Nat) :
    ∃ q, 0 < q ∧ 3 ^ (k + 1) * q = 2 ^ (3 ^ k) + 1 := by
  obtain ⟨q, hq⟩ := power_target_divisibility k
  refine ⟨q, ?_, hq.symm⟩
  by_cases hz : q = 0
  · have hq' : 2 ^ (3 ^ k) + 1 = 0 := by simpa only [hz, Nat.mul_zero] using hq
    exact False.elim (Nat.noConfusion hq')
  · omega

theorem growth_bridge : ∀ k n, shortcutIter k n = CollatzGrowth.orbit k n
  | 0, _ => rfl
  | k + 1, n => by
    simpa only [shortcutIter, CollatzGrowth.orbit, U, CollatzGrowth.U]
      using growth_bridge k (U n)

theorem growth_prefix_lower (K j q : Nat) (hq : 0 < q) (hj : j ≤ K) :
    2 ^ K * q - 1 ≤ shortcutIter j (2 ^ K * q - 1) := by
  have he : j + (K - j) = K := by omega
  have hf := CollatzGrowth.growth_formula j (K - j) q hq
  rw [he] at hf
  rw [growth_bridge, hf]
  have hl := Nat.mul_le_mul_right q
    (Nat.mul_le_mul_left (2 ^ (K - j)) (Nat.pow_le_pow_left (by decide : 2 ≤ 3) j))
  have hp : 2 ^ (K - j) * 2 ^ j = 2 ^ K := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hj]
  rw [hp] at hl
  omega

theorem growth_to_power (K a q : Nat) (hq : 0 < q)
    (htarget : 3 ^ K * q = 2 ^ a + 1) :
    shortcutIter K (2 ^ K * q - 1) = 2 ^ a := by
  rw [growth_bridge]
  have hf := CollatzGrowth.growth_formula K 0 q hq
  simpa only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, htarget,
    Nat.add_sub_cancel] using hf

theorem general_growth_in_basin (H K q : Nat) (hq : 0 < q)
    (hH : H < 2 ^ K * q - 1) :
    Basin H (3 ^ K * q - 1) (2 ^ K * q - 1) := by
  refine ⟨K, ?_, ?_⟩
  · intro j hj
    exact Nat.lt_of_lt_of_le hH (growth_prefix_lower K j q hq hj)
  · rw [growth_bridge]
    simpa only [Nat.add_zero, Nat.pow_zero, Nat.one_mul]
      using CollatzGrowth.growth_formula K 0 q hq

theorem growth_in_basin (H K a q : Nat) (hq : 0 < q)
    (htarget : 3 ^ K * q = 2 ^ a + 1) (hH : H < 2 ^ K * q - 1) :
    Basin H (2 ^ a) (2 ^ K * q - 1) := by
  refine ⟨K, ?_, growth_to_power K a q hq htarget⟩
  intro j hj
  exact Nat.lt_of_lt_of_le hH (growth_prefix_lower K j q hq hj)

theorem growth_hits_one (K a q : Nat) (hq : 0 < q)
    (htarget : 3 ^ K * q = 2 ^ a + 1) :
    shortcutIter (K + a) (2 ^ K * q - 1) = 1 := by
  rw [shortcut_add, growth_to_power K a q hq htarget, power_hits]

/-- The source is at most (2/3)^K times its larger, convergent target. -/
theorem growth_ratio (K a q : Nat) (hq : 0 < q)
    (htarget : 3 ^ K * q = 2 ^ a + 1) :
    3 ^ K * (2 ^ K * q - 1) ≤ 2 ^ K * 2 ^ a := by
  have hp : 0 < 2 ^ K * q := Nat.mul_pos (Nat.pow_pos (by decide)) hq
  have he : 3 ^ K * ((2 ^ K * q - 1) + 1) = 2 ^ K * (2 ^ a + 1) := by
    rw [Nat.sub_add_cancel hp, ← htarget]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  simp only [Nat.mul_add, Nat.mul_one] at he
  have hl : 2 ^ K ≤ 3 ^ K := Nat.pow_le_pow_left (by decide) K
  omega

def witnessRoot : Nat := 2 ^ 6561
def witnessQuotient : Nat := (witnessRoot + 1) / 3 ^ 9
def witnessStart : Nat := 2 ^ 9 * witnessQuotient - 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem witness_parameters : 0 < witnessQuotient ∧
    3 ^ 9 * witnessQuotient = 2 ^ 6561 + 1 ∧ 64 < witnessStart := by decide

theorem witness_in_basin : Basin 64 witnessRoot witnessStart :=
  growth_in_basin 64 9 6561 witnessQuotient witness_parameters.1
    witness_parameters.2.1 witness_parameters.2.2

theorem witness_reaches_one : shortcutIter 6570 witnessStart = 1 :=
  growth_hits_one 9 6561 witnessQuotient witness_parameters.1 witness_parameters.2.1

theorem witness_basin_boundary (n : Nat) :
    Pull 64 (Basin 64 witnessRoot) n ↔ Basin 64 witnessRoot n ∧ n ≠ witnessRoot := by
  apply pull_basin_iff
  exact power_no_return 6559

theorem witness_basin_converges (n : Nat) (hn : Basin 64 witnessRoot n) : ReachesOne n :=
  basin_converges 64 witnessRoot n (ordinary_reaches_of_shortcut (power_hits 6561)) hn

theorem witness_ratio : 3 ^ 9 * witnessStart ≤ 2 ^ 9 * witnessRoot :=
  growth_ratio 9 6561 witnessQuotient witness_parameters.1 witness_parameters.2.1

/-- Squaring verifies that (2/3)^(27/2) < 7/1000. -/
theorem boundary_constant : 1000 ^ 2 * 2 ^ 27 < 7 ^ 2 * 3 ^ 27 := by decide

/-- The cofinite extension uses twice the root loss at K=10. -/
theorem cofinite_boundary_constant : 2000 * 2 ^ 15 < 7 * 3 ^ 15 := by decide

def profileSource : Nat := 2 ^ 64 * 66 - 1
def profileTarget : Nat := 3 ^ 64 * 66 - 1

theorem profile_parameters : 64 < profileSource ∧ 64 < profileTarget ∧
    16 * profileSource ^ 9 < profileTarget ^ 6 := by decide

theorem profile_in_basin : Basin 64 profileTarget profileSource :=
  general_growth_in_basin 64 64 66 (by decide) profile_parameters.1

set_option maxHeartbeats 5000000 in
theorem profile_convergence : shortcutIter 560 profileSource = 1 ∧
    shortcutIter 496 profileTarget = 1 := by decide

#print axioms pull_basin_iff
#print axioms basin_converges
#print axioms power_hits
#print axioms power_no_return
#print axioms power_target_divisibility
#print axioms power_target_quotient
#print axioms growth_in_basin
#print axioms general_growth_in_basin
#print axioms growth_hits_one
#print axioms growth_ratio
#print axioms witness_parameters
#print axioms witness_in_basin
#print axioms witness_reaches_one
#print axioms witness_basin_boundary
#print axioms witness_basin_converges
#print axioms witness_ratio
#print axioms boundary_constant
#print axioms cofinite_boundary_constant
#print axioms profile_parameters
#print axioms profile_in_basin
#print axioms profile_convergence

end WeightedBasinBarrier
