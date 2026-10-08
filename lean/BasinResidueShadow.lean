/- Arithmetic transport for residue-dense inverse basins.
   Existence of the power congruence is proved in the accompanying written
   argument; it is a hypothesis here, not an admitted theorem. -/
import InverseFibreGrowth

namespace BasinResidueShadow
open CollatzAffine InverseFibreGrowth

theorem unit_step (n : Nat) (hn : n%3 ≠ 0) : (U n)%3 ≠ 0 := by
  unfold U
  split <;> omega

theorem unit_orbit : ∀ k n, n%3 ≠ 0 → (orbit k n)%3 ≠ 0
  | 0, _, hn => hn
  | k+1, n, hn => unit_orbit k (U n) (unit_step n hn)

theorem odd_step_unit (n : Nat) (hn : n%2=1) : (U n)%3 ≠ 0 := by
  unfold U
  rw [if_pos hn]
  omega

/-- Once an odd step has occurred, the endpoint is a unit modulo three. -/
theorem positive_weight_unit : ∀ k n, 0 < wt k n → (orbit k n)%3 ≠ 0
  | 0, _, h => by simp [wt] at h
  | k+1, n, h => by
    by_cases hn : n%2=1
    · exact unit_orbit k (U n) (odd_step_unit n hn)
    · have hw : 0 < wt k (U n) := by simp only [wt] at h; omega
      exact positive_weight_unit k (U n) hw

theorem orbit_add (k t n : Nat) : orbit (k+t) n = orbit t (orbit k n) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih => simpa [Nat.succ_add, orbit] using ih (U n)

theorem dyadic_orbit (e a : Nat) : orbit e (2^e*a) = a := by
  induction e with
  | zero => simp [orbit]
  | succ e ih =>
    have hs : 2^(e+1)*a = 2*(2^e*a) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    have hu (x : Nat) : U (2*x) = x := by unfold U; rw [if_neg (by omega)]; omega
    rw [hs, orbit, hu, ih]

/-- Solving one power congruence gives an ancestor in the prescribed cylinder.
    The equality premise includes nonnegativity of the quotient. -/
theorem shadow (a n k e b q : Nat)
    (he : 3^(wt k n + b)*q + orbit k n = 2^e*a) :
    orbit (k+e) (2^k*(3^b*q)+n) = a ∧
    (2^k*(3^b*q)+n) % (2^k*3^b) = n % (2^k*3^b) ∧
    wt k (2^k*(3^b*q)+n) = wt k n := by
  refine ⟨?_, ?_, wt_affine k _ n⟩
  · rw [orbit_add, affine]
    have he' : 3^wt k n*(3^b*q)+orbit k n = 2^e*a := by
      simpa [Nat.pow_add, Nat.mul_assoc] using he
    rw [he', dyadic_orbit]
  · rw [← Nat.mul_assoc]
    simp

theorem forward_closed_orbit (S : Nat → Prop)
    (hc : ∀ n, S n → S (U n)) : ∀ k n, S n → S (orbit k n)
  | 0, _, h => h
  | k+1, n, h => forward_closed_orbit S hc k (U n) (hc n h)

/-- A full residue class in a forward-closed set captures every root for
    which the displayed arithmetic congruence has been solved. -/
theorem class_captures_root (S : Nat → Prop)
    (hc : ∀ n, S n → S (U n)) (a n k e b q : Nat) (hn : 0<n)
    (he : 3^(wt k n+b)*q+orbit k n = 2^e*a)
    (hclass : ∀ m, 0<m → m%(2^k*3^b)=n%(2^k*3^b) → S m) : S a := by
  have hs := shadow a n k e b q he
  have hm := hclass (2^k*(3^b*q)+n) (by omega) hs.2.1
  have ho := forward_closed_orbit S hc (k+e) _ hm
  rwa [hs.1] at ho

#print axioms positive_weight_unit
#print axioms shadow
#print axioms class_captures_root
end BasinResidueShadow
