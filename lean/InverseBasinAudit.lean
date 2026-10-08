/- Distinguishing inverse basins from injective orbit sets in packing arguments.
   Also checks small arithmetic counterexamples to two version-specific
   uniqueness/existence statements in arXiv:2512.13760. No Collatz proof. -/
import CollatzPacking

namespace InverseBasinAudit
open CollatzPacking

def Basin (a n : Nat) : Prop := ∃ k, orbit k n = a

def Component (a n : Nat) : Prop := ∃ i j, orbit i n = orbit j a

theorem branching_pair (q : Nat) :
    U (6*q+4) = 3*q+2 ∧ U (2*q+1) = 3*q+2 := by
  unfold U
  simp only [show (6*q+4)%2 = 0 by omega,
    show (2*q+1)%2 = 1 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem even_step (n : Nat) : U (2*n) = n := by
  unfold U
  rw [if_neg (by omega)]
  omega

theorem predecessor_of_multiple_three (a n : Nat) (ha : 3 ∣ a)
    (he : U n = a) : n = 2*a := by
  obtain ⟨q,rfl⟩ := ha
  unfold U at he
  split at he <;> omega

theorem dyadic_orbit (k a : Nat) : orbit k (2^k*a) = a := by
  induction k with
  | zero => simp [orbit]
  | succ k ih =>
    have he : 2^(k+1)*a = 2*(2^k*a) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [he,orbit,even_step,ih]

/-- Roots divisible by three have precisely a doubling ray as their basin. -/
theorem basin_of_multiple_three (a n : Nat) (ha : 3 ∣ a) :
    Basin a n ↔ ∃ k, n = 2^k*a := by
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_⟩
    induction k generalizing n with
    | zero => simpa only [orbit,Nat.pow_zero,Nat.one_mul] using hk
    | succ k ih =>
      have h := ih (U n) hk
      have hd : 3 ∣ 2^k*a := by
        obtain ⟨q,hq⟩ := ha
        refine ⟨2^k*q,?_⟩
        simp [hq,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
      have hn := predecessor_of_multiple_three (2^k*a) n hd h
      simpa [Nat.pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hn
  · rintro ⟨k,rfl⟩
    exact ⟨k,dyadic_orbit k a⟩

/-- Every root coprime to three has distinct positive basin members with
    equal immediate images; both reach the root within two shortcut steps. -/
theorem basin_collision (a : Nat) (ha : a % 3 ≠ 0) :
    ∃ u v i j, 0 < u ∧ 0 < v ∧ u ≠ v ∧ U u = U v ∧
      i ≤ 2 ∧ j ≤ 2 ∧ orbit i u = a ∧ orbit j v = a := by
  have hc : a%3 = 1 ∨ a%3 = 2 := by omega
  rcases hc with h1 | h2
  · let q := a/3
    have he : a = 3*q+1 := by omega
    obtain ⟨hu,hv⟩ := branching_pair (2*q)
    have hu' : U (12*q+4) = 6*q+2 := by simpa only [← Nat.mul_assoc, Nat.reduceMul] using hu
    have hv' : U (4*q+1) = 6*q+2 := by simpa only [← Nat.mul_assoc, Nat.reduceMul] using hv
    have ht : U (6*q+2) = a := by
      have h := even_step (3*q+1)
      have hm : 2*(3*q+1) = 6*q+2 := by omega
      rw [hm] at h
      omega
    refine ⟨12*q+4,4*q+1,2,2,by omega,by omega,by omega,?_,by decide,by decide,?_,?_⟩
    · rw [hu',hv']
    · simp only [orbit,hu',ht]
    · simp only [orbit,hv',ht]
  · let q := a/3
    have he : a = 3*q+2 := by omega
    obtain ⟨hu,hv⟩ := branching_pair q
    refine ⟨6*q+4,2*q+1,1,1,by omega,by omega,by omega,?_,by decide,by decide,?_,?_⟩
    · rw [hu,hv]
    · simpa only [orbit,hu] using he.symm
    · simpa only [orbit,hv] using he.symm

theorem basin_not_injective (a : Nat) (ha : a%3 ≠ 0) :
    ¬ (∀ u v, Basin a u → Basin a v → U u = U v → u = v) := by
  intro hi
  obtain ⟨u,v,i,j,_,_,hne,he,_,_,hu,hv⟩ := basin_collision a ha
  exact hne (hi u v ⟨i,hu⟩ ⟨j,hv⟩ he)

theorem cancel_meeting (S : Nat → Prop)
    (closed : ∀ n, S n → S (U n))
    (injective : ∀ u v, S u → S v → U u = U v → u = v)
    (u v i j : Nat) (hu : S u) (hv : S v) (hij : i ≤ j)
    (he : orbit i u = orbit j v) : orbit (j-i) v = u := by
  have hv' := orbit_mem_of_forward_closed S closed (j-i) v hv
  apply orbit_injective_on_forward_closed S closed injective i _ _ hv' hu
  rw [← orbit_add]
  have ht : i+(j-i) = j := by omega
  rw [ht]
  exact he.symm

/-- Injective forward-closed subsets of one inverse basin cannot retain
    incomparable branches: any two members lie on a single forward chain. -/
theorem basin_subset_is_chain (S : Nat → Prop) (a : Nat)
    (closed : ∀ n, S n → S (U n))
    (injective : ∀ u v, S u → S v → U u = U v → u = v)
    (inside : ∀ n, S n → Basin a n)
    (u v : Nat) (hu : S u) (hv : S v) :
    (∃ k, orbit k u = v) ∨ (∃ k, orbit k v = u) := by
  obtain ⟨i,hi⟩ := inside u hu
  obtain ⟨j,hj⟩ := inside v hv
  by_cases h : i ≤ j
  · exact Or.inr ⟨j-i,cancel_meeting S closed injective u v i j hu hv h (hi.trans hj.symm)⟩
  · exact Or.inl ⟨i-j,cancel_meeting S closed injective v u j i hv hu (by omega) (hj.trans hi.symm)⟩

/-- The convergent basin illustrates the quantitative mismatch sharply:
    an injective forward-closed subset can contain only the two cycle states. -/
theorem convergent_point_in_injective_region (S : Nat → Prop)
    (closed : ∀ n, S n → S (U n))
    (injective : ∀ u v, S u → S v → U u = U v → u = v)
    (n : Nat) (hn : S n) (hc : Basin 1 n) : n = 1 ∨ n = 2 := by
  obtain ⟨k,hk⟩ := hc
  have hs1 := orbit_mem_of_forward_closed S closed k n hn
  rw [hk] at hs1
  have h12 : U 1 = 2 := by decide
  have h21 : U 2 = 1 := by decide
  have hs2 := closed 1 hs1
  rw [h12] at hs2
  have main : ∀ t m, S m → orbit t m = 1 → m = 1 ∨ m = 2 := by
    intro t
    induction t with
    | zero =>
      intro m _ hm
      exact Or.inl hm
    | succ t ih =>
      intro m hm he
      change orbit t (U m) = 1 at he
      rcases ih (U m) (closed m hm) he with h | h
      · exact Or.inr (injective m 2 hm hs2 (h.trans h21.symm))
      · exact Or.inl (injective m 1 hm hs1 (h.trans h12.symm))
  exact main k n hn hk

/-- For a nonperiodic root its inverse basin is not even forward closed:
    it contains no nonempty forward-closed subset. -/
theorem closed_basin_forces_periodic_root (S : Nat → Prop) (a n : Nat)
    (closed : ∀ m, S m → S (U m))
    (inside : ∀ m, S m → Basin a m) (hn : S n) :
    ∃ k, 0 < k ∧ orbit k a = a := by
  obtain ⟨i,hi⟩ := inside n hn
  have ha := orbit_mem_of_forward_closed S closed i n hn
  rw [hi] at ha
  obtain ⟨k,hk⟩ := inside (U a) (closed a ha)
  exact ⟨k+1,by omega,hk⟩

/-- Passing to the forward-closed coalescence component does not fix the
    injectivity/counting mismatch: injective closed subsets are still chains. -/
theorem component_subset_is_chain (S : Nat → Prop) (a : Nat)
    (closed : ∀ n, S n → S (U n))
    (injective : ∀ u v, S u → S v → U u = U v → u = v)
    (inside : ∀ n, S n → Component a n)
    (u v : Nat) (hu : S u) (hv : S v) :
    (∃ k, orbit k u = v) ∨ (∃ k, orbit k v = u) := by
  obtain ⟨i,j,hi⟩ := inside u hu
  obtain ⟨k,l,hv'⟩ := inside v hv
  have meet : orbit (l+i) u = orbit (j+k) v := by
    rw [orbit_add,orbit_add,hi,hv',← orbit_add,← orbit_add,Nat.add_comm l j]
  by_cases h : l+i ≤ j+k
  · exact Or.inr ⟨j+k-(l+i),cancel_meeting S closed injective u v (l+i) (j+k) hu hv h meet⟩
  · exact Or.inl ⟨l+i-(j+k),cancel_meeting S closed injective v u (j+k) (l+i) hv hu (by omega) meet.symm⟩

/-- v1, Lemma 2.2: the free tuple (3,1) has no allowed exponent tuple. -/
theorem v1_free_tuple_counterexample (v1 v2 : Nat)
    (h1 : (v1+1)/2 = 3) (h2 : (v2+1)/2 = 1) :
    2^(v1+v2)%9 ≠ (2^v2+3)%9 := by
  have h1' : v1=5 ∨ v1=6 := by omega
  have h2' : v2=1 ∨ v2=2 := by omega
  rcases h1' with h | h <;> rcases h2' with g | g <;> subst v1 <;> subst v2 <;> decide

/-- v2, Lemma 3.1: at level one and u1=2, both 8 and 10 meet
    the displayed conditions. This refutes uniqueness, not a density bound. -/
theorem v2_nonunique_pair :
    (8+1)/6 = (2:Nat)-1 ∧ (10+1)/6 = (2:Nat)-1 ∧
    (2:Nat)^8%3 = 1 ∧ (2:Nat)^8%9 ≠ 1 ∧
    (2:Nat)^10%3 = 1 ∧ (2:Nat)^10%9 ≠ 1 ∧
    (8:Nat) ≠ 10 ∧ (2:Nat)%3 ≠ 0 := by decide

#print axioms basin_collision
#print axioms basin_of_multiple_three
#print axioms basin_not_injective
#print axioms cancel_meeting
#print axioms basin_subset_is_chain
#print axioms convergent_point_in_injective_region
#print axioms closed_basin_forces_periodic_root
#print axioms component_subset_is_chain
#print axioms v1_free_tuple_counterexample
#print axioms v2_nonunique_pair
end InverseBasinAudit
