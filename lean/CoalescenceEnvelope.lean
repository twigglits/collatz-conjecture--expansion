/- Exact affine envelopes for two-sided paths from the growing CRT classes.
   This does not prove or disprove Collatz. -/
import CoalescenceDescent

namespace CoalescenceEnvelope
open CollatzAffine CoalescenceDescent

theorem weight_add (c a m : Nat) : wt (c + a) m = wt c m + wt a (orbit c m) := by
  induction c generalizing m with
  | zero => simp [wt, orbit]
  | succ c ih =>
    simp only [Nat.succ_add, wt, orbit]
    rw [ih]
    omega

theorem longer_envelope (a c n m : Nat)
    (hg : 2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1))
    (hd : 3 ^ wt c m ∣ n)
    (he : orbit (c + a) m = orbit a n) :
    (2 ^ c * 3 ^ a) * n ≤ 3 ^ wt (c + a) m * m ∧
    3 ^ wt (c + a) m * (m + 1) ≤ (2 ^ c * 3 ^ a) * (n + 1) := by
  let z := orbit c m
  let i := wt c m
  let h := wt a z
  have he' : orbit a z = orbit a n := by simpa only [orbit_add] using he
  have hh : h ≤ a := weight_le a z
  have hp : 3 ^ a = 3 ^ h * 3 ^ (a - h) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hh]
  have hu := orbit_intercept_upper a z
  rw [he', hg] at hu
  have hs : 3 ^ a * n ≤ 3 ^ h * z := by
    change 3 ^ a * (n + 1) ≤ 3 ^ h * z + 3 ^ a at hu
    rw [Nat.mul_add, Nat.mul_one] at hu
    omega
  rw [hp, Nat.mul_assoc] at hs
  have hbase := Nat.le_of_mul_le_mul_left hs (Nat.pow_pos (by decide))
  obtain ⟨q, hq⟩ := hd
  let T := 3 ^ (a - h) * q
  have ht : 3 ^ i * T ≤ z := by
    simpa [T, hq, i, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
  have hm := orbit_ge_scaled c m T ht
  have hwt : 3 ^ wt (c + a) m = 3 ^ h * 3 ^ i := by
    simp [weight_add, Nat.pow_add, h, i, z, Nat.mul_comm]
  have hid : 3 ^ wt (c + a) m * (2 ^ c * T) = (2 ^ c * 3 ^ a) * n := by
    rw [hwt, hq]
    simp [T, i, hp, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  constructor
  · rw [← hid]
    exact Nat.mul_le_mul_left _ hm
  · have hl1 := Nat.mul_le_mul_left (3 ^ h) (orbit_plus_one_lower c m)
    have hl2 := Nat.mul_le_mul_left (2 ^ c) (orbit_plus_one_lower a z)
    rw [he', hg] at hl2
    rw [hwt]
    apply Nat.le_trans (by simpa [i, z, Nat.mul_assoc] using hl1)
    simpa [h, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hl2

theorem shorter_envelope (a b n m : Nat) (hb : b ≤ a)
    (hg : 2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1))
    (he : orbit b m = orbit a n) :
    3 ^ a * n ≤ (2 ^ (a - b) * 3 ^ wt b m) * m ∧
    (2 ^ (a - b) * 3 ^ wt b m) * (m + 1) ≤ 3 ^ a * (n + 1) := by
  have h2 : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hb]
  have h3 : 3 ^ a = 3 ^ (a - b) * 3 ^ b := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hb]
  have hp : 2 ^ (a - b) * 3 ^ b ≤ 3 ^ a := by
    rw [h3]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by decide) _)
  have hu := Nat.mul_le_mul_left (2 ^ (a - b)) (orbit_intercept_upper b m)
  have hl := Nat.mul_le_mul_left (2 ^ (a - b)) (orbit_plus_one_lower b m)
  rw [he] at hu hl
  simp only [← Nat.mul_assoc] at hu hl
  rw [← h2, hg] at hu hl
  constructor
  · simp only [Nat.mul_add, Nat.mul_one] at hu
    simp only [← Nat.mul_assoc] at hu
    omega
  · simpa only [Nat.mul_assoc] using hl

/-- With Q=B/A, these inequalities are exactly m=Q*n+c with
    Q>=1 and 0<=c<=Q-1. This formulation needs no real arithmetic. -/
theorem crt_envelope (K a b n m : Nat) (ha : a ≤ K) (hb : b ≤ K)
    (h2 : 2 ^ K ∣ n + 1) (h3 : 3 ^ K ∣ n)
    (he : orbit b m = orbit a n) :
    (2 ^ b * 3 ^ a) * n ≤ (2 ^ a * 3 ^ wt b m) * m ∧
    (2 ^ a * 3 ^ wt b m) * (m + 1) ≤ (2 ^ b * 3 ^ a) * (n + 1) := by
  have hg := odd_prefix_growth a n (Nat.dvd_trans (Nat.pow_dvd_pow 2 ha) h2)
  by_cases hba : b ≤ a
  · have ht := shorter_envelope a b n m hba hg he
    have hpow : 2 ^ b * 2 ^ (a - b) = 2 ^ a := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hba]
    constructor
    · have h := Nat.mul_le_mul_left (2 ^ b) ht.1
      simpa [← Nat.mul_assoc, hpow] using h
    · have h := Nat.mul_le_mul_left (2 ^ b) ht.2
      simpa [← Nat.mul_assoc, hpow] using h
  · have hab : a ≤ b := by omega
    have hi : wt (b - a) m ≤ K := Nat.le_trans (weight_le _ _) (by omega)
    have hd := Nat.dvd_trans (Nat.pow_dvd_pow 3 hi) h3
    have ht := longer_envelope a (b - a) n m hg hd
      (by simpa [Nat.sub_add_cancel hab] using he)
    rw [Nat.sub_add_cancel hab] at ht
    have hpow : 2 ^ a * 2 ^ (b - a) = 2 ^ b := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hab]
    constructor
    · have h := Nat.mul_le_mul_left (2 ^ a) ht.1
      simpa [← Nat.mul_assoc, hpow] using h
    · have h := Nat.mul_le_mul_left (2 ^ a) ht.2
      simpa [← Nat.mul_assoc, hpow] using h

theorem slope_ge_one (A B n m : Nat)
    (hl : B * n ≤ A * m) (hu : A * (m + 1) ≤ B * (n + 1)) : A ≤ B := by
  simp only [Nat.mul_add, Nat.mul_one] at hu
  omega

/-- An oriented nonempty segment cannot have multiplicative factor one. -/
theorem two_pow_ne_three_pow (length odds : Nat) (hl : 0 < length) :
    2 ^ length ≠ 3 ^ odds := by
  intro he
  have hd : 2 ∣ 2 ^ length := by
    simpa using Nat.pow_dvd_pow 2 (show 1 ≤ length by omega)
  rw [he] at hd
  have hz := Nat.mod_eq_zero_of_dvd hd
  have ho : 3 ^ odds % 2 = 1 := by simp [Nat.pow_mod]
  omega

def Adjacent (n m : Nat) : Prop := U n = m ∨ U m = n

theorem adjacent_transfer {n m : Nat} (h : Adjacent n m)
    (hm : OrdinaryCollatz.ReachesOne m) : OrdinaryCollatz.ReachesOne n := by
  rcases h with hf | hb
  · apply coalescence_transfer (a := 1) (b := 0) (m := m) _ hm
    simpa only [orbit] using hf
  · apply coalescence_transfer (a := 0) (b := 1) (m := m) _ hm
    simpa only [orbit] using hb.symm

/-- This is a sufficient global proof route, not an assertion that a rank
    satisfying the hypotheses has been found. -/
theorem conjecture_of_graph_rank (R : Nat → Nat) (N : Nat)
    (base : ∀ n, 0 < n → n ≤ N → OrdinaryCollatz.ReachesOne n)
    (progress : ∀ n, N < n → ∃ m, 0 < m ∧ Adjacent n m ∧ R m < R n) :
    OrdinaryCollatz.Conjecture := by
  have main : ∀ k n, R n = k → 0 < n → OrdinaryCollatz.ReachesOne n := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n he hn
      by_cases hsmall : n ≤ N
      · exact base n hn hsmall
      · obtain ⟨m, hm, ha, hr⟩ := progress n (by omega)
        apply adjacent_transfer ha
        exact ih (R m) (by omega) m rfl hm
  intro n hn
  exact main (R n) n rfl hn

#print axioms weight_add
#print axioms longer_envelope
#print axioms shorter_envelope
#print axioms crt_envelope
#print axioms slope_ge_one
#print axioms two_pow_ne_three_pow
#print axioms adjacent_transfer
#print axioms conjecture_of_graph_rank
end CoalescenceEnvelope
