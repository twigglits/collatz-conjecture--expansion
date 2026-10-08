/- Exact gap and power-budget criteria at a first coefficient drop.
   No assertion that every start has a drop within the required budget.
   Logarithm estimates used in the written application are not imported. -/
import CoalescenceEnvelope

namespace FirstSlopeBudget
open CollatzAffine CoalescenceDescent CoalescenceEnvelope

/-- All additive contributions are controlled before the multiplier drops
    below one. This is an integer inequality, with no real approximations. -/
theorem prefix_bound (k n : Nat)
    (hp : ∀ t, t<k → 2^t≤3^wt t n) :
    3*2^k*orbit k n ≤ 3^wt k n*(3*n+wt k n) := by
  induction k with
  | zero => simp [wt,orbit]
  | succ k ih =>
    have hi := ih (fun t ht => hp t (by omega))
    have hk := hp k (by omega)
    have ho : orbit (k+1) n=U (orbit k n) := by
      simpa [orbit] using CoalescenceDescent.orbit_add k 1 n
    have hw : wt (k+1) n=wt k n+(orbit k n)%2 := by
      simpa [wt] using weight_add k 1 n
    by_cases hodd : (orbit k n)%2=1
    · rw [hodd] at hw
      have hs : 2*U (orbit k n)=3*orbit k n+1 := by
        unfold U; rw [if_pos hodd]; omega
      calc
        3*2^(k+1)*orbit (k+1) n = (3*2^k)*(2*U (orbit k n)) := by
          rw [ho,Nat.pow_succ]; ac_rfl
        _ = 3*(3*2^k*orbit k n)+3*2^k := by
          rw [hs,Nat.mul_add,Nat.mul_one]; ac_rfl
        _ ≤ 3*(3^wt k n*(3*n+wt k n))+3*3^wt k n :=
          Nat.add_le_add (Nat.mul_le_mul_left 3 hi) (Nat.mul_le_mul_left 3 hk)
        _ = 3^wt (k+1) n*(3*n+wt (k+1) n) := by
          rw [hw,Nat.pow_succ]
          simp [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          omega
    · have hz : (orbit k n)%2=0 := by omega
      rw [hz,Nat.add_zero] at hw
      have hs : 2*U (orbit k n)=orbit k n := by
        unfold U; rw [if_neg hodd]; omega
      calc
        3*2^(k+1)*orbit (k+1) n = (3*2^k)*(2*U (orbit k n)) := by
          rw [ho,Nat.pow_succ]; ac_rfl
        _ = 3*2^k*orbit k n := by rw [hs]
        _ ≤ 3^wt (k+1) n*(3*n+wt (k+1) n) := by rw [hw]; exact hi

/-- A sufficient condition, not the unrestricted first-drop conjecture. -/
theorem descent_of_gap (k n : Nat) (hf : FirstSlopeDrop k n)
    (hg : 3^wt k n*wt k n < 3*n*(2^k-3^wt k n)) : orbit k n<n := by
  have hbound := prefix_bound k n hf.2
  have hcoef := hf.1
  have hsplit : 2^k=3^wt k n+(2^k-3^wt k n) := by omega
  have htotal : 3^wt k n*(3*n+wt k n)<3*2^k*n := by
    calc
      3^wt k n*(3*n+wt k n) =
          3^wt k n*(3*n)+3^wt k n*wt k n := Nat.mul_add _ _ _
      _ < 3^wt k n*(3*n)+3*n*(2^k-3^wt k n) := Nat.add_lt_add_left hg _
      _ = 3*n*(3^wt k n+(2^k-3^wt k n)) := by rw [Nat.mul_add]; ac_rfl
      _ = 3*2^k*n := by rw [← hsplit]; ac_rfl
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt hbound htotal)

/-- A rational power bound for the relative coefficient gap converts to a
    polynomial size budget. The gap estimate is an explicit hypothesis. -/
theorem descent_of_power_gap (k n p q : Nat) (hf : FirstSlopeDrop k n)
    (hg : (3^wt k n)^q < k^p*(2^k-3^wt k n)^q)
    (hb : k^(p+q) ≤ (3*n)^q) : orbit k n<n := by
  have hk : 0<k := by
    have hcoef := hf.1
    by_cases he : k=0
    · subst k; simp [wt] at hcoef
    · omega
  have hw := CoalescenceDescent.weight_le k n
  have hpower : (3^wt k n*wt k n)^q < (3*n*(2^k-3^wt k n))^q := by
    calc
      (3^wt k n*wt k n)^q = (3^wt k n)^q*(wt k n)^q := Nat.mul_pow _ _ _
      _ ≤ (3^wt k n)^q*k^q := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw q)
      _ < (k^p*(2^k-3^wt k n)^q)*k^q :=
        Nat.mul_lt_mul_of_pos_right hg (Nat.pow_pos hk)
      _ = k^(p+q)*(2^k-3^wt k n)^q := by rw [Nat.pow_add]; ac_rfl
      _ ≤ (3*n)^q*(2^k-3^wt k n)^q := Nat.mul_le_mul_right _ hb
      _ = (3*n*(2^k-3^wt k n))^q := (Nat.mul_pow _ _ _).symm
  apply descent_of_gap k n hf
  by_cases h : 3^wt k n*wt k n < 3*n*(2^k-3^wt k n)
  · exact h
  · have hrev := Nat.pow_le_pow_left (show 3*n*(2^k-3^wt k n)≤3^wt k n*wt k n by omega) q
    omega

/-- The integer form of the written lambda>k^(-21/5) application. -/
theorem descent_of_21_5_gap (k n : Nat) (hf : FirstSlopeDrop k n)
    (hg : (3^wt k n)^5 < k^21*(2^k-3^wt k n)^5)
    (hb : k^26≤(3*n)^5) : orbit k n<n :=
  descent_of_power_gap k n 21 5 hf hg hb

theorem gap_certificate7 : FirstSlopeDrop 7 7 ∧
    3^wt 7 7*wt 7 7 < 3*7*(2^7-3^wt 7 7) :=
  ⟨CollatzAffine.example_first_drop.1,by decide⟩

theorem gap_budget_not_necessary27 :
    ¬ 3^wt 59 27*wt 59 27 < 3*27*(2^59-3^wt 59 27) ∧ orbit 59 27<27 := by
  decide

/-- This multiplier is still above one half. Its exact small gap and large
    starting value already certify descent at the first drop. -/
def example65 : Nat := 30913060423816076283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem certificate65 : FirstSlopeDrop 65 example65 ∧
    (3^wt 65 example65)^5 < 65^21*(2^65-3^wt 65 example65)^5 ∧
    65^26≤(3*example65)^5 ∧
    2^65<2*3^wt 65 example65 ∧ wt 65 example65=41 ∧
    orbit 65 example65=30560730293104027237 := by
  have hp : ∀ t : Fin 65, 2^t.val≤3^wt t.val example65 := by decide
  exact ⟨⟨by decide,fun t ht => hp ⟨t,ht⟩⟩,
    by decide,by decide,by decide,by decide,by decide⟩

theorem descent65_via_power_gap : orbit 65 example65<example65 :=
  descent_of_21_5_gap 65 example65 certificate65.1
    certificate65.2.1 certificate65.2.2.1

#print axioms prefix_bound
#print axioms descent_of_gap
#print axioms descent_of_power_gap
#print axioms descent_of_21_5_gap
#print axioms gap_certificate7
#print axioms gap_budget_not_necessary27
#print axioms certificate65
#print axioms descent65_via_power_gap
end FirstSlopeBudget
