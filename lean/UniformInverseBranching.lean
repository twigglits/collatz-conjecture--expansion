/- Every root coprime to three has a binary tree of synchronized ancestors.
   Kernel proofs only. This does not establish Collatz convergence. -/
import InverseFibreGrowth

namespace UniformInverseBranching
open CollatzAffine InverseFibreGrowth

def child (a : Nat) (b : Bool) : Nat :=
  192 * (a / 9) + match a % 9 with
  | 1 => if b then 20 else 16
  | 2 => if b then 40 else 32
  | 4 => if b then 85 else 80
  | 5 => if b then 106 else 104
  | 7 => if b then 149 else 148
  | 8 => if b then 170 else 160
  | _ => 0

private theorem lift (q d r : Nat) (hw : wt 6 d = 1) (ho : orbit 6 d = r) :
    wt 6 (192*q+d) = 1 ∧ orbit 6 (192*q+d) = 9*q+r := by
  have he : 192*q+d = 2^6*(3*q)+d := by omega
  rw [he, wt_affine, affine, hw, ho]
  constructor
  · rfl
  · omega

theorem child_facts (a : Nat) (ha : a % 3 ≠ 0) (b : Bool) :
    0 < child a b ∧ (child a b)%3 ≠ 0 ∧ a < child a b ∧
    3*child a b < 64*a ∧ wt 6 (child a b) = 1 ∧ orbit 6 (child a b) = a := by
  have hr : a%9=1 ∨ a%9=2 ∨ a%9=4 ∨ a%9=5 ∨ a%9=7 ∨ a%9=8 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals cases b
  all_goals simp only [child, hr, Bool.false_eq_true, ↓reduceIte]
  · have h := lift (a/9) 16 1 (by decide) (by decide); omega
  · have h := lift (a/9) 20 1 (by decide) (by decide); omega
  · have h := lift (a/9) 32 2 (by decide) (by decide); omega
  · have h := lift (a/9) 40 2 (by decide) (by decide); omega
  · have h := lift (a/9) 80 4 (by decide) (by decide); omega
  · have h := lift (a/9) 85 4 (by decide) (by decide); omega
  · have h := lift (a/9) 104 5 (by decide) (by decide); omega
  · have h := lift (a/9) 106 5 (by decide) (by decide); omega
  · have h := lift (a/9) 148 7 (by decide) (by decide); omega
  · have h := lift (a/9) 149 7 (by decide) (by decide); omega
  · have h := lift (a/9) 160 8 (by decide) (by decide); omega
  · have h := lift (a/9) 170 8 (by decide) (by decide); omega

theorem children_distinct (a : Nat) (ha : a%3 ≠ 0) : child a false ≠ child a true := by
  have hr : a%9=1 ∨ a%9=2 ∨ a%9=4 ∨ a%9=5 ∨ a%9=7 ∨ a%9=8 := by omega
  rcases hr with hr | hr | hr | hr | hr | hr
  all_goals simp [child, hr]

private theorem orbit_add (k t n : Nat) : orbit (k+t) n = orbit t (orbit k n) := by
  induction k generalizing n with
  | zero => simp [orbit]
  | succ k ih => simpa only [Nat.succ_add, orbit] using ih (U n)

private theorem weight_add (k t n : Nat) : wt (k+t) n = wt k n + wt t (orbit k n) := by
  induction k generalizing n with
  | zero => simp [wt, orbit]
  | succ k ih => simp only [Nat.succ_add, wt, orbit]; rw [ih]; omega

def leaves : Nat → Nat → List Nat
  | 0, a => [a]
  | h+1, a => leaves h (child a false) ++ leaves h (child a true)

theorem leaf_count (h a : Nat) : (leaves h a).length = 2^h := by
  induction h generalizing a with
  | zero => rfl
  | succ h ih => simp [leaves, ih, Nat.pow_succ, Nat.mul_two]

theorem leaf_facts (h a n : Nat) (ha : a%3 ≠ 0) (hn : n ∈ leaves h a) :
    0<n ∧ n%3 ≠ 0 ∧ wt (6*h) n = h ∧ orbit (6*h) n = a := by
  induction h generalizing a n with
  | zero => simp only [leaves, List.mem_singleton] at hn; subst n; simp [wt, orbit]; omega
  | succ h ih =>
    simp only [leaves, List.mem_append] at hn
    have step (b : Bool) (hb : n ∈ leaves h (child a b)) :
        0<n ∧ n%3 ≠ 0 ∧ wt (6*(h+1)) n = h+1 ∧ orbit (6*(h+1)) n = a := by
      obtain ⟨_,hu,_,_,hw,ho⟩ := child_facts a ha b
      obtain ⟨hp,hn3,hw',ho'⟩ := ih (child a b) n hu hb
      refine ⟨hp, hn3, ?_, ?_⟩
      · rw [Nat.mul_add, Nat.mul_one, weight_add, ho', hw', hw]
      · rw [Nat.mul_add, Nat.mul_one, orbit_add, ho', ho]
    rcases hn with hn | hn
    · exact step false hn
    · exact step true hn

theorem leaves_distinct (h a : Nat) (ha : a%3 ≠ 0) : (leaves h a).Nodup := by
  induction h generalizing a with
  | zero => simp [leaves]
  | succ h ih =>
    have hf := child_facts a ha false
    have ht := child_facts a ha true
    apply List.nodup_append.mpr
    refine ⟨ih _ hf.2.1, ih _ ht.2.1, ?_⟩
    intro n hn m hm he
    have en := (leaf_facts h _ n hf.2.1 hn).2.2.2
    have em := (leaf_facts h _ m ht.2.1 hm).2.2.2
    exact children_distinct a ha (by rw [← en, ← em, he])

/-- All synchronized leaves fit below the same explicit height bound. -/
theorem leaf_bound (h a n : Nat) (ha : a%3 ≠ 0) (hn : n ∈ leaves h a) :
    3^h*n ≤ 64^h*a := by
  induction h generalizing a n with
  | zero => simp only [leaves, List.mem_singleton] at hn; subst n; simp
  | succ h ih =>
    simp only [leaves, List.mem_append] at hn
    have step (b : Bool) (hb : n ∈ leaves h (child a b)) :
        3^(h+1)*n ≤ 64^(h+1)*a := by
      have hc := child_facts a ha b
      have h1 := Nat.mul_le_mul_left 3 (ih _ _ hc.2.1 hb)
      have h2 := Nat.mul_le_mul_left (64^h) (Nat.le_of_lt hc.2.2.2.1)
      calc
        3^(h+1)*n = 3*(3^h*n) := by simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
        _ ≤ 3*(64^h*child a b) := h1
        _ = 64^h*(3*child a b) := by simp [Nat.mul_left_comm]
        _ ≤ 64^h*(64*a) := h2
        _ = 64^(h+1)*a := by simp [Nat.pow_succ, Nat.mul_assoc]
    rcases hn with hn | hn
    · exact step false hn
    · exact step true hn

#print axioms child_facts
#print axioms children_distinct
#print axioms leaf_count
#print axioms leaf_facts
#print axioms leaves_distinct
#print axioms leaf_bound
end UniformInverseBranching
