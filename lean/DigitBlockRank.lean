/- A separated-binary-block rank cannot decrease at every sufficiently large
   shortcut step. The finite-window digit interpretation is a written bridge. -/
import CollatzAffine

namespace DigitBlockRank
open CollatzAffine

def bits (n : Nat) : Nat := n.log2 + 1

theorem four_steps (q : Nat) :
    U (2*q+2) = q+1 ∧
    U (2*q+21) = 3*q+32 ∧
    U (6*q+9) = 9*q+14 ∧
    U (14*q+1) = 21*q+2 := by
  unfold U
  simp only [show (2*q+2)%2 = 0 by omega,
    show (2*q+21)%2 = 1 by omega,
    show (6*q+9)%2 = 1 by omega,
    show (14*q+1)%2 = 1 by omega, reduceIte, Nat.reduceEqDiff]
  omega

/-- These three odd-step differences cannot all be negative when appending
    a zero has positive cost. The polynomial cancellation is exact. -/
theorem cancellation (r3 r7 r21 z : Int) (hz : 0 < z) :
    ¬ (r3-r21+3*z < 0 ∧ r7-r3 < 0 ∧ r21-r7-z < 0) := by omega

/-- The two structural laws are assumptions here. Their interpretation for
    weighted finite-window digit counts is not asserted as a Lean theorem. -/
theorem no_eventual_separated_rank (R : Nat → Int) (z c : Int) (K N : Nat)
    (shift : ∀ n, 0 < n → R (2*n) = R n + z)
    (separate : ∀ a b k, 0 < a → 0 < b → K + bits b ≤ k →
      R (a*2^k+b) = R a + R b + ((k:Int)-(bits b:Int))*z-c)
    (decrease : ∀ n, N < n → R (U n) < R n) : False := by
  let k := N+K+6
  let q := 2^k
  have hk : K+6 ≤ k := by omega
  have hq : N < q := by
    have h : k < 2^k := Nat.lt_two_pow_self
    have : N ≤ k := by omega
    omega
  obtain ⟨e0,e1,e2,e3⟩ := four_steps q
  have d0 := decrease (2*q+2) (by omega)
  have d1 := decrease (2*q+21) (by omega)
  have d2 := decrease (6*q+9) (by omega)
  have d3 := decrease (14*q+1) (by omega)
  rw [e0] at d0
  rw [e1] at d1
  rw [e2] at d2
  rw [e3] at d3
  have hzero := shift (q+1) (by omega)
  have hz : 0 < z := by
    have he : 2*(q+1) = 2*q+2 := by omega
    rw [he] at hzero
    omega
  have r2 := shift 1 (by decide)
  have r4 := shift 2 (by decide)
  have r8 := shift 4 (by decide)
  have r16 := shift 8 (by decide)
  have r32 := shift 16 (by decide)
  have r14 := shift 7 (by decide)
  have b1 : bits 1 = 1 := by decide
  have b2 : bits 2 = 2 := by decide
  have b9 : bits 9 = 4 := by decide
  have b14 : bits 14 = 4 := by decide
  have b21 : bits 21 = 5 := by decide
  have b32 : bits 32 = 6 := by decide
  have s1 := separate 1 21 (k+1) (by decide) (by decide) (by rw [b21]; omega)
  have t1 := separate 3 32 k (by decide) (by decide) (by rw [b32]; omega)
  have s2 := separate 3 9 (k+1) (by decide) (by decide) (by rw [b9]; omega)
  have t2 := separate 9 14 k (by decide) (by decide) (by rw [b14]; omega)
  have s3 := separate 7 1 (k+1) (by decide) (by decide) (by rw [b1]; omega)
  have t3 := separate 21 2 k (by decide) (by decide) (by rw [b2]; omega)
  simp only [b1, b2, b9, b14, b21, b32] at s1 t1 s2 t2 s3 t3
  have hp : 2^(k+1) = 2*q := by simp [q, Nat.pow_succ, Nat.mul_comm]
  rw [hp] at s1 s2 s3
  simp only [show 1*(2*q)+21 = 2*q+21 by omega] at s1
  simp only [show 3*(2*q)+9 = 6*q+9 by omega] at s2
  simp only [show 7*(2*q)+1 = 14*q+1 by omega] at s3
  change R (3*q+32) = _ at t1
  change R (9*q+14) = _ at t2
  change R (21*q+2) = _ at t3
  rw [s1, t1] at d1
  rw [s2, t2] at d2
  rw [s3, t3] at d3
  -- Distribute variable products before Presburger arithmetic eliminates them.
  simp [Int.sub_mul, Int.add_mul] at d1 d2 d3
  simp only [Nat.reduceMul] at r2 r4 r8 r16 r32 r14
  omega

#print axioms four_steps
#print axioms cancellation
#print axioms no_eventual_separated_rank
end DigitBlockRank
