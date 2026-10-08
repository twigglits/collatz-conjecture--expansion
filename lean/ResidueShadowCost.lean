/- Quantitative bounds and injectivity for the residue shadow construction.
   Modular existence and sharp asymptotics are written separately. -/
import BasinResidueShadow

namespace ResidueShadowCost
open CollatzAffine InverseFibreGrowth BasinResidueShadow

theorem prefix_endpoint (a n k e b q : Nat)
    (he : 3^(wt k n+b)*q+orbit k n = 2^e*a) :
    orbit k (2^k*(3^b*q)+n) = 2^e*a := by
  rw [affine]
  simpa [Nat.pow_add, Nat.mul_assoc] using he

/-- Exact integer form of the linear upper bound on ancestor size. -/
theorem size_bound (a n k e b q : Nat)
    (he : 3^(wt k n+b)*q+orbit k n = 2^e*a) :
    3^wt k n*(2^k*(3^b*q)+n) ≤ 2^(k+e)*a := by
  have h := coefficient_lower_bound k (2^k*(3^b*q)+n)
  rw [wt_affine, prefix_endpoint a n k e b q he] at h
  simpa [Nat.pow_add, Nat.mul_assoc] using h

theorem bounded_exponent_size (a n k e b q E : Nat) (hE : e ≤ E)
    (he : 3^(wt k n+b)*q+orbit k n = 2^e*a) :
    3^wt k n*(2^k*(3^b*q)+n) ≤ 2^(k+E)*a := by
  apply Nat.le_trans (size_bound a n k e b q he)
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem odd_dyadic_unique (e f a c : Nat) (ha : a%2=1) (hc : c%2=1)
    (he : 2^e*a=2^f*c) : e=f ∧ a=c := by
  induction e generalizing f with
  | zero =>
    cases f with
    | zero => simpa using he
    | succ f =>
      have hf : 2^(f+1)*c = 2*(2^f*c) := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [hf] at he
      simp only [Nat.pow_zero, Nat.one_mul] at he
      omega
  | succ e ih =>
    have hsplit (d x : Nat) : 2^(d+1)*x = 2*(2^d*x) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    cases f with
    | zero =>
      rw [hsplit] at he
      simp only [Nat.pow_zero, Nat.one_mul] at he
      omega
    | succ f =>
      rw [hsplit, hsplit] at he
      have h' : 2^e*a=2^f*c := by omega
      obtain ⟨hf,hac⟩ := ih f h'
      exact ⟨by omega,hac⟩

/-- Fixed-prefix shadows of distinct odd roots cannot collide, even when
    their halving-tail lengths differ. -/
theorem shadow_injective (a c n k e f b q s : Nat)
    (ha : a%2=1) (hc : c%2=1)
    (he : 3^(wt k n+b)*q+orbit k n=2^e*a)
    (hf : 3^(wt k n+b)*s+orbit k n=2^f*c)
    (hs : 2^k*(3^b*q)+n=2^k*(3^b*s)+n) : a=c := by
  have h := congrArg (orbit k) hs
  rw [prefix_endpoint a n k e b q he, prefix_endpoint c n k f b s hf] at h
  exact (odd_dyadic_unique e f a c ha hc h).2

/-- Returning along the prescribed prefix does not descend below the root. -/
theorem prefix_not_below_root (a n k e b q : Nat)
    (he : 3^(wt k n+b)*q+orbit k n=2^e*a) :
    a ≤ orbit k (2^k*(3^b*q)+n) := by
  rw [prefix_endpoint a n k e b q he]
  have hp : 1 ≤ 2^e := Nat.one_le_pow e 2 (by decide)
  have h := Nat.mul_le_mul_right a hp
  simpa using h

#print axioms size_bound
#print axioms bounded_exponent_size
#print axioms odd_dyadic_unique
#print axioms shadow_injective
#print axioms prefix_not_below_root
end ResidueShadowCost
