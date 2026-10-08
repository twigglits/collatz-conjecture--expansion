/- A robust multiplier margin supplies actual descent with a size-dependent
   time bound. Existence of such a crossing for every start is NOT proved. -/
import CoalescenceEnvelope

namespace HalfSlopeDescent
open CollatzAffine CoalescenceDescent CoalescenceEnvelope

def AboveHalfBefore (k n : Nat) : Prop :=
  ∀ t, t<k → 2^t ≤ 2*3^wt t n

/-- Includes every additive +1 term, without assuming that n has descended. -/
theorem prefix_bound (k n : Nat) (hp : AboveHalfBefore k n) :
    3*2^k*orbit k n ≤ 3^wt k n*(3*n+2*wt k n) := by
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
        _ ≤ 3*(3^wt k n*(3*n+2*wt k n))+3*(2*3^wt k n) :=
          Nat.add_le_add (Nat.mul_le_mul_left 3 hi) (Nat.mul_le_mul_left 3 hk)
        _ = 3^wt (k+1) n*(3*n+2*wt (k+1) n) := by
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
        _ ≤ 3^wt (k+1) n*(3*n+2*wt (k+1) n) := by rw [hw]; exact hi

/-- At a first half-slope crossing, a linear odd-step budget suffices. -/
theorem descent_at_half (k n : Nat) (hp : AboveHalfBefore k n)
    (hc : 2*3^wt k n ≤ 2^k) (hb : 2*wt k n < 3*n) : orbit k n<n := by
  have h1 := prefix_bound k n hp
  have h2 := Nat.mul_lt_mul_of_pos_left (show 3*n+2*wt k n<6*n by omega)
    (Nat.pow_pos (by decide : 0<3) : 0<3^wt k n)
  have h3 : 3^wt k n*(6*n) ≤ (3*2^k)*n := by
    calc
      3^wt k n*(6*n) = (2*3^wt k n)*(3*n) := by
        rw [show (6:Nat)=2*3 by decide]; ac_rfl
      _ ≤ 2^k*(3*n) := Nat.mul_le_mul_right (3*n) hc
      _ = (3*2^k)*n := by ac_rfl
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 (Nat.lt_of_lt_of_le h2 h3))

/-- It suffices to detect any half-slope crossing by time n. An earlier
    crossing is selected if the supplied time is not the first. -/
theorem descent_by_linear_time (n K : Nat) (hn : 0<n) (hK : K≤n)
    (hc : 2*3^wt K n ≤ 2^K) : ∃ k, k≤K ∧ orbit k n<n := by
  revert hK hc
  induction K using Nat.strongRecOn with
  | ind K ih =>
    intro hK hc
    by_cases he : ∃ i, i<K ∧ 2*3^wt i n ≤ 2^i
    · obtain ⟨i,hi,hci⟩ := he
      obtain ⟨t,ht,hd⟩ := ih i hi (by omega) hci
      exact ⟨t,by omega,hd⟩
    · have hp : AboveHalfBefore K n := by
        intro i hi
        have hnot : ¬ 2*3^wt i n ≤ 2^i := by intro h; exact he ⟨i,hi,h⟩
        omega
      have hw := CoalescenceDescent.weight_le K n
      exact ⟨K,Nat.le_refl K,descent_at_half K n hp hc (by omega)⟩

/-- A sufficient global certificate format, not an assertion that its
    universal crossing premise holds. -/
theorem conjecture_of_half_certificate (N : Nat)
    (base : ∀ n, 0<n → n≤N → OrdinaryCollatz.ReachesOne n)
    (crossing : ∀ n, N<n → ∃ K, K≤n ∧ 2*3^wt K n ≤ 2^K) :
    OrdinaryCollatz.Conjecture := by
  apply OrdinaryCollatz.conjecture_iff_shortcut_descent.mpr
  intro n hn
  by_cases hb : n≤N
  · obtain ⟨k,hk⟩ := (OrdinaryCollatz.reaches_iff_shortcut n).mp (base n (by omega) hb)
    exact ⟨k,by omega⟩
  · obtain ⟨K,hK,hc⟩ := crossing n (by omega)
    obtain ⟨k,_,hd⟩ := descent_by_linear_time n K (by omega) hK hc
    exact ⟨k,by simpa only [CoalescenceDescent.orbit_bridge] using hd⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem certificate27 : AboveHalfBefore 65 27 ∧
    2*3^wt 65 27≤2^65 ∧ 2*wt 65 27<3*27 ∧ wt 65 27=40 ∧ orbit 65 27=10 := by
  have hp : ∀ t : Fin 65, 2^t.val≤2*3^wt t.val 27 := by decide
  exact ⟨fun t ht => hp ⟨t,ht⟩,by decide,by decide,by decide,by decide⟩

theorem descent27_via_margin : orbit 65 27<27 :=
  descent_at_half 65 27 certificate27.1 certificate27.2.1 certificate27.2.2.1

theorem cycle_one_budget_failure :
    AboveHalfBefore 6 1 ∧ 2*3^wt 6 1≤2^6 ∧
    ¬ 2*wt 6 1<3*1 ∧ orbit 6 1=1 := by
  have hp : ∀ t : Fin 6, 2^t.val≤2*3^wt t.val 1 := by decide
  exact ⟨fun t ht => hp ⟨t,ht⟩,by decide,by decide,by decide⟩

#print axioms prefix_bound
#print axioms descent_at_half
#print axioms descent_by_linear_time
#print axioms conjecture_of_half_certificate
#print axioms certificate27
#print axioms descent27_via_margin
#print axioms cycle_one_budget_failure
end HalfSlopeDescent
