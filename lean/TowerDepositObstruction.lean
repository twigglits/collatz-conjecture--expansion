/-
  Exact unbounded deposits in the post-tower family.
  This audits a finite-modulus premise, not the Collatz conjecture.
  Standalone Lean; kernel proofs only.
-/
namespace TowerDepositObstruction

/-- An elementary special case of lifting the exponent, with an odd quotient. -/
theorem power_three_odd_quotient (s : Nat) :
    ∃ q : Nat, q % 2 = 1 ∧ 3 ^ (2 ^ (s + 1)) = 1 + 2 ^ (s + 3) * q := by
  induction s with
  | zero => exact ⟨1, by decide, by decide⟩
  | succ s ih =>
    obtain ⟨q, hq, he⟩ := ih
    refine ⟨q + 2 ^ (s + 2) * q * q, ?_, ?_⟩
    · have hp : 2 ^ (s + 2) % 2 = 0 := by
        rw [show s + 2 = (s + 1) + 1 by omega, Nat.pow_succ]
        omega
      simp [Nat.add_mod, Nat.mul_mod, hp, hq]
    · have hex : 2 ^ (s + 1 + 1) = 2 ^ (s + 1) + 2 ^ (s + 1) := by
        rw [Nat.pow_succ]
        omega
      have hsquare : 3 ^ (2 ^ (s + 1 + 1)) =
          (1 + 2 ^ (s + 3) * q) * (1 + 2 ^ (s + 3) * q) := by
        rw [hex, Nat.pow_add, he]
      rw [hsquare]
      have hp : 2 ^ (s + 3) = 2 * 2 ^ (s + 2) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hp' : 2 ^ (s + 1 + 3) = 2 * 2 ^ (s + 3) := by
        rw [show s + 1 + 3 = (s + 3) + 1 by omega, Nat.pow_succ]
        ac_rfl
      rw [hp', hp]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.two_mul]
      ac_rfl

/-- For k=2^(s+1)+1 this is the second contracting return from rho(k)
    when s>=1. The identification with that return is a written argument. -/
def postTower (s : Nat) : Nat := (3 ^ (2 ^ (s + 1) - 1) - 1) / 2

theorem post_tower_deposit (s : Nat) :
    ∃ q : Nat, q % 2 = 1 ∧ 3 * postTower s + 1 = 2 ^ (s + 2) * q := by
  obtain ⟨q, hq, he⟩ := power_three_odd_quotient s
  refine ⟨q, hq, ?_⟩
  have hp : 0 < 2 ^ (s + 1) := Nat.pow_pos (by decide)
  have ha : 3 ^ (2 ^ (s + 1) - 1) % 2 = 1 := by
    simp [Nat.pow_mod]
  have hb : 2 * postTower s + 1 = 3 ^ (2 ^ (s + 1) - 1) := by
    unfold postTower
    have hpos : 0 < 3 ^ (2 ^ (s + 1) - 1) := Nat.pow_pos (by decide)
    omega
  have hc : 3 ^ (2 ^ (s + 1)) = 3 * 3 ^ (2 ^ (s + 1) - 1) := by
    have hi : 2 ^ (s + 1) = (2 ^ (s + 1) - 1) + 1 := by omega
    calc
      3 ^ (2 ^ (s + 1)) = 3 ^ ((2 ^ (s + 1) - 1) + 1) := congrArg (3 ^ ·) hi
      _ = 3 * 3 ^ (2 ^ (s + 1) - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hd : 2 ^ (s + 3) * q = 2 * (2 ^ (s + 2) * q) := by
    rw [Nat.pow_succ]
    ac_rfl
  rw [hc, ← hb, hd] at he
  omega

/-- Exact valuation phrased without a valuation library. -/
theorem exact_deposit (s : Nat) :
    2 ^ (s + 2) ∣ 3 * postTower s + 1 ∧
    ¬ 2 ^ (s + 3) ∣ 3 * postTower s + 1 := by
  obtain ⟨q, hq, he⟩ := post_tower_deposit s
  constructor
  · exact ⟨q, he⟩
  · intro hd
    obtain ⟨r, hr⟩ := hd
    have ht : 2 ^ (s + 3) = 2 ^ (s + 2) * 2 := Nat.pow_succ _ _
    rw [he, ht] at hr
    have hr' : q = 2 * r := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (n := s + 2) (by decide : 0 < 2))
      simpa only [Nat.mul_assoc] using hr
    omega

#print axioms power_three_odd_quotient
#print axioms post_tower_deposit
#print axioms exact_deposit

end TowerDepositObstruction
