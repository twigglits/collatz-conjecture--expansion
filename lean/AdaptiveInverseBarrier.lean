/- Complete bounded-depth inverse-tree transport near the root one.
   This rules out bounded inverse-only descent on a family of unit roots,
   not Collatz convergence or adaptive forward/backward descent. -/
import BasinResidueShadow
import CollatzPacking

namespace AdaptiveInverseBarrier
open CollatzAffine InverseFibreGrowth BasinResidueShadow

private theorem orbit_bridge : ∀ k n, orbit k n = CollatzPacking.orbit k n
  | 0, _ => rfl
  | k+1, n => by
    simpa only [orbit,CollatzPacking.orbit,U,CollatzPacking.U] using orbit_bridge k (U n)

private theorem weight_bridge : ∀ k n, wt k n = CollatzPacking.wt k n
  | 0, _ => rfl
  | k+1, n => by simp only [wt,CollatzPacking.wt,weight_bridge]; rfl

theorem residue_image (k r : Nat) (hr : r < 2^k) : orbit k r < 3^wt k r := by
  rw [orbit_bridge,weight_bridge]
  exact CollatzPacking.residue_image_bound k r hr

theorem positive_orbit : ∀ k n, 0<n → 0<orbit k n
  | 0, _, h => h
  | k+1, n, h => by
    apply positive_orbit k (U n)
    unfold U
    split <;> omega

theorem weight_le : ∀ k n, wt k n ≤ k
  | 0, _ => by simp [wt]
  | k+1, n => by have h := weight_le k (U n); simp only [wt]; omega

theorem positive_residue_image (k r : Nat) (hr : r ≤ 2^k) :
    orbit k r ≤ 3^wt k r := by
  by_cases hs : r < 2^k
  · exact Nat.le_of_lt (residue_image k r hs)
  · have he : r=2^k := by omega
    have ho := dyadic_orbit k 1
    simp only [Nat.mul_one] at ho
    rw [he,ho]
    exact Nat.one_le_pow _ _ (by decide)

/-- Every bounded-depth ancestor of 3^K*q+1 is an explicit affine lift
    of an ancestor of 1, with the same parity weight. -/
theorem inverse_transport (K k q m : Nat) (hk : k ≤ K) (hm : 0<m)
    (he : orbit k m = 3^K*q+1) :
    ∃ r, 0<r ∧ r≤2^k ∧ orbit k r=1 ∧ wt k r=wt k m ∧
      m=2^k*(3^(K-wt k m)*q)+r := by
  let d := 2^k
  let p := (m-1)/d
  let r := (m-1)%d+1
  have hd : 0<d := Nat.pow_pos (by decide)
  have hr : 0<r ∧ r≤d := by
    have h := Nat.mod_lt (m-1) hd
    dsimp [r]; omega
  have hsplit : m=2^k*p+r := by
    have h := Nat.mod_add_div (m-1) d
    dsimp [p,r,d] at *
    omega
  have hw : wt k m=wt k r := by rw [hsplit,wt_affine]
  have hj : wt k r ≤ K := Nat.le_trans (weight_le k r) hk
  have hp3 : 3^K=3^wt k r*3^(K-wt k r) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hj]
  have hf : 3^wt k r*p+orbit k r=3^wt k r*(3^(K-wt k r)*q)+1 := by
    rw [hsplit,affine,hp3] at he
    simpa only [Nat.mul_assoc] using he
  have hlo := positive_orbit k r hr.1
  have hup := positive_residue_image k r hr.2
  have hmod := congrArg (fun x => x % (3^wt k r)) hf
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hmod
  simp only [Nat.mod_mod] at hmod
  have hb : orbit k r=1 := by
    have hp : 0<3^wt k r := Nat.pow_pos (by decide)
    by_cases hM : 3^wt k r=1
    · omega
    · have h1 : 1<3^wt k r := by omega
      rw [Nat.mod_eq_of_lt h1] at hmod
      have hb' : orbit k r<3^wt k r := by
        by_cases hlt : orbit k r<3^wt k r
        · exact hlt
        · have heq : orbit k r=3^wt k r := by omega
          rw [heq,Nat.mod_self] at hmod
          omega
      rwa [Nat.mod_eq_of_lt hb'] at hmod
  rw [hb] at hf
  have hp : p=3^(K-wt k r)*q := Nat.eq_of_mul_eq_mul_left
    (Nat.pow_pos (by decide)) (Nat.add_right_cancel hf)
  refine ⟨r,hr.1,hr.2,hb,hw.symm,?_⟩
  rw [hw,hsplit,hp]

/-- Converse: the transport gives every ancestor at the chosen depth. -/
theorem lifted_ancestor (K k q r : Nat) (hk : k≤K) (hr : orbit k r=1) :
    orbit k (2^k*(3^(K-wt k r)*q)+r)=3^K*q+1 := by
  have hj := Nat.le_trans (weight_le k r) hk
  rw [affine,hr,← Nat.mul_assoc,← Nat.pow_add,Nat.add_sub_of_le hj]

theorem inverse_no_descent (K k q m : Nat) (hk : k≤K) (hm : 0<m)
    (he : orbit k m=3^K*q+1) : 3^K*q+1 ≤ m := by
  obtain ⟨r,hpos,_,ho,hw,hs⟩ := inverse_transport K k q m hk hm he
  have hb := coefficient_lower_bound k r
  rw [ho,Nat.mul_one] at hb
  have hp : 3^wt k r ≤ 2^k := by
    have h := Nat.mul_le_mul_left (3^wt k r) hpos
    simp only [Nat.mul_one] at h
    exact Nat.le_trans h hb
  have hj := Nat.le_trans (weight_le k r) hk
  have hmul := Nat.mul_le_mul_right (3^(K-wt k r)*q) hp
  have hpow : 3^wt k r*(3^(K-wt k r)*q)=3^K*q := by
    rw [← Nat.mul_assoc,← Nat.pow_add,Nat.add_sub_of_le hj]
  rw [hpow] at hmul
  rw [hs,← hw]
  omega

#print axioms inverse_transport
#print axioms lifted_ancestor
#print axioms inverse_no_descent
end AdaptiveInverseBarrier
