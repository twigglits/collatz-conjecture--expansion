/-
  A bounded nonperiodic predecessor in every ternary residue class.
  This extension uses the authenticated external predecessor-density sources
  and Mathlib at Lean 4.30.0-rc2; it is not a standalone Lean 4.33.1 module.
  The source definitions are attributed in docs/PREDECESSOR-DENSITY-REVIEW.md.
  No claim of convergence of the target is made.
-/
import Erdos1135.ND.PositiveDensity.GeneralTargetResidueCoverage

namespace BoundedPredecessorSeed

open Erdos1135.ND.PositiveDensity

/-- Two distinct points with the same image cannot both be periodic. -/
theorem one_of_two_no_return {α : Type*} (f : α → α) (r s : α)
    (hne : r ≠ s) (heq : f r = f s) :
    (∀ k : ℕ, 0 < k → (f^[k]) r ≠ r) ∨
    (∀ k : ℕ, 0 < k → (f^[k]) s ≠ s) := by
  classical
  by_cases hr : ∃ k : ℕ, 0 < k ∧ (f^[k]) r = r
  · right
    intro k hk hs
    obtain ⟨j, hj, hrj⟩ := hr
    have hpr : Function.IsPeriodicPt f j r := hrj
    have hps : Function.IsPeriodicPt f k s := hs
    exact hne (hpr.eq_of_apply_eq hps hj hk heq)
  · left
    intro k hk hrk
    exact hr ⟨k, hk, hrk⟩

theorem bounded_start {a : ℕ} (hthree : ¬ 3 ∣ a) :
    ∃ r e : ℕ, 0 < e ∧ e ≤ 2 ∧ 3 * r + 1 = 2 ^ e * a := by
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt := Nat.mod_lt a (by norm_num : 0 < 3)
    have hn : a % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree
    omega
  rcases hmod with h | h
  · refine ⟨(4 * a) / 3, 2, by norm_num, by norm_num, ?_⟩
    have hm : (4 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega
  · refine ⟨(2 * a) / 3, 1, by norm_num, by norm_num, ?_⟩
    have hm : (2 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega

def bound (a q L : ℕ) : ℕ := 4 ^ ((L + 3) * 3 ^ q) * a

/-- The bound depends on a, the residue modulus and the height, not on any
    unknown period or on deciding whether the target lies on a cycle. -/
theorem exists_bounded_nonreturning_predecessor_in_residue
    {a : ℕ} (ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (q L : ℕ) (y : Fin (3 ^ q)) :
    ∃ R : ℕ, L < R ∧ R < bound a q L ∧ Odd R ∧
      Erdos1135.Reaches R a ∧ R % 3 ^ q = y ∧
      ∀ k : ℕ, 0 < k → (Erdos1135.Tao.syracuse^[k]) R ≠ R := by
  obtain ⟨r, e, he, he2, hstart⟩ := bounded_start hthree
  obtain ⟨m, hm⟩ := generalTargetRoot_residue_surjective r q y
  let k1 := (m : ℕ) + (L + 1) * 3 ^ q
  let k2 := (m : ℕ) + (L + 2) * 3 ^ q
  have hq : 1 ≤ 3 ^ q := by positivity
  have hindices : L < k1 ∧ k1 < k2 ∧ k2 < (L + 3) * 3 ^ q := by
    have hm_lt := m.isLt
    have hmul := Nat.mul_le_mul_left (L + 1) hq
    dsimp only [k1, k2]
    nlinarith
  have hfit (k : ℕ) (hlo : L < k) (hhi : k < (L + 3) * 3 ^ q) :
      L < ndGeneralTargetRoot r k ∧ ndGeneralTargetRoot r k < bound a q L := by
    constructor
    · exact hlo.trans_le (generalTargetRoot_ge_index r k)
    · have hc := generalTargetRoot_cleared r k
      rw [hstart] at hc
      have hepow : 2 ^ e ≤ 4 := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 2) he2
        norm_num at h
        exact h
      have hbpow : 4 ^ (k + 1) ≤ 4 ^ ((L + 3) * 3 ^ q) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hstep : 3 * ndGeneralTargetRoot r k + 1 ≤ 4 ^ (k + 1) * a := by
        rw [hc, pow_succ]
        nlinarith [Nat.mul_le_mul_left (4 ^ k) (Nat.mul_le_mul_right a hepow)]
      have hbound := hstep.trans (Nat.mul_le_mul_right a hbpow)
      unfold bound
      omega
  have hr1 := hfit k1 hindices.1 (hindices.2.1.trans hindices.2.2)
  have hr2 := hfit k2 (hindices.1.trans hindices.2.1) hindices.2.2
  have hmod (t : ℕ) : ndGeneralTargetRoot r ((m : ℕ) + t * 3 ^ q) % 3 ^ q = y := by
    have h := generalTargetRoot_modEq_of_period r q m t
    change ndGeneralTargetRoot r m % 3 ^ q =
      ndGeneralTargetRoot r ((m : ℕ) + t * 3 ^ q) % 3 ^ q at h
    exact h.symm.trans (congrArg Fin.val hm)
  have hneq : ndGeneralTargetRoot r k1 ≠ ndGeneralTargetRoot r k2 := by
    intro h
    have h1 := generalTargetRoot_cleared r k1
    have h2 := generalTargetRoot_cleared r k2
    have hp : 4 ^ k1 < 4 ^ k2 := Nat.pow_lt_pow_right (by decide) hindices.2.1
    have hm := Nat.mul_lt_mul_of_pos_right hp (by omega : 0 < 3 * r + 1)
    rw [h] at h1
    omega
  have himage : Erdos1135.Tao.syracuse (ndGeneralTargetRoot r k1) =
      Erdos1135.Tao.syracuse (ndGeneralTargetRoot r k2) := by
    rw [generalTargetRoot_syracuse, generalTargetRoot_syracuse]
  rcases one_of_two_no_return Erdos1135.Tao.syracuse _ _ hneq himage with hn | hn
  · exact ⟨ndGeneralTargetRoot r k1, hr1.1, hr1.2,
      generalTargetRoot_odd r k1 (by omega), generalTargetRoot_reaches hstart (by omega),
      hmod (L + 1), hn⟩
  · exact ⟨ndGeneralTargetRoot r k2, hr2.1, hr2.2,
      generalTargetRoot_odd r k2 (by omega), generalTargetRoot_reaches hstart (by omega),
      hmod (L + 2), hn⟩

#print axioms one_of_two_no_return
#print axioms bounded_start
#print axioms exists_bounded_nonreturning_predecessor_in_residue

end BoundedPredecessorSeed
