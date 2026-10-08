/- Equal-time, equal-weight inverse fibres persist in every aligned block.
The asymptotic multiplicity lower bound is written, not formalized here. -/
import CollatzAffine
namespace InverseFibreGrowth
open CollatzAffine

/-- The first k parity weights depend only on the residue modulo 2^k. -/
theorem wt_affine : ∀ k q r, wt k (2^k*q+r) = wt k r
  | 0, _, _ => rfl
  | k+1, q, r => by
    have hsplit : 2^(k+1)*q+r = 2*(2^k*q)+r := by
      rw [Nat.pow_succ, Nat.mul_comm (2^k) 2, Nat.mul_assoc]
    by_cases hpar : r%2 = 1
    · have h3m : 2^k*(3*q) = 3*(2^k*q) := Nat.mul_left_comm (2^k) 3 q
      have hU : U (2^(k+1)*q+r) = 2^k*(3*q)+U r := by
        rw [hsplit,h3m]
        unfold U
        rw [if_pos (show (2*(2^k*q)+r)%2 = 1 by omega),if_pos hpar]
        omega
      simp only [wt,hU,wt_affine]
      omega
    · have hU : U (2^(k+1)*q+r) = 2^k*q+U r := by
        rw [hsplit]
        unfold U
        rw [if_neg (show ¬ (2*(2^k*q)+r)%2 = 1 by omega),if_neg hpar]
        omega
      simp only [wt,hU,wt_affine]
      omega

def members : List Nat := [512, 640, 672, 680, 682, 768, 832, 848, 852, 853, 904, 906, 908, 909, 1088, 1104, 1108, 1109, 1120, 1128, 1130, 1137, 1200, 1204, 1205, 1208, 1210, 1408, 1440, 1448, 1450, 1472, 1476, 1477, 1478, 1488, 1492, 1493, 1506, 1507, 1604, 1605, 1606, 1608, 1610, 1611, 1612, 1613]

/-- Fibre partitions at a fixed weight are identical in all aligned blocks. -/
theorem same_weight_fibre_shift (k q r s j : Nat)
    (hr : wt k r = j) (hs : wt k s = j) :
    orbit k (2^k*q+r) = orbit k (2^k*q+s) ↔ orbit k r = orbit k s := by
  rw [affine,affine,hr,hs]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem certificate_checked : members.all (fun n =>
    decide (0<n ∧ n<2^16 ∧ wt 16 n=4 ∧ orbit 16 n=2)) = true := by decide

theorem members_distinct : members.Nodup := by decide

theorem member_count : members.length = 48 := by decide

theorem member_facts (n : Nat) (hn : n ∈ members) :
    0<n ∧ n<2^16 ∧ wt 16 n=4 ∧ orbit 16 n=2 :=
  of_decide_eq_true (List.all_eq_true.mp certificate_checked n hn)

/-- Forty-eight distinct positive starts per aligned block share both
    the 16-step endpoint and the four-odd-step count. -/
theorem lifted_fibre (q n : Nat) (hn : n ∈ members) :
    0 < 2^16*q+n ∧ 2^16*q ≤ 2^16*q+n ∧
    2^16*q+n < 2^16*(q+1) ∧
    wt 16 (2^16*q+n)=4 ∧ orbit 16 (2^16*q+n)=81*q+2 := by
  obtain ⟨hpos,hbound,hw,ho⟩ := member_facts n hn
  refine ⟨by omega,by omega,?_,?_,?_⟩
  · have he : 2^16*(q+1) = 2^16*q+2^16 := by rw [Nat.mul_add,Nat.mul_one]
    omega
  · rw [wt_affine,hw]
  · rw [affine,hw,ho]

theorem lifted_distinct (q n m : Nat)
    (he : 2^16*q+n = 2^16*q+m) : n=m := Nat.add_left_cancel he

#print axioms wt_affine
#print axioms same_weight_fibre_shift
#print axioms certificate_checked
#print axioms members_distinct
#print axioms member_count
#print axioms lifted_fibre
#print axioms lifted_distinct
end InverseFibreGrowth
