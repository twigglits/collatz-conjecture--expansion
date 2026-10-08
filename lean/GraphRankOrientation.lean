/- In a functional graph, well-founded local descent outside a forward-closed
   region necessarily follows the forward map. This does not prove Collatz. -/
import GraphRankNecessity
import BuchiArithmetic

namespace GraphRankOrientation

theorem wellFounded_asymmetric {α : Type u} {r : α → α → Prop}
    (wf : WellFounded r) : ∀ x y, r y x → r x y → False := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro y hy hx
    exact ih y hy x hx hy

/-- Generic functional-graph theorem; neither arithmetic nor finiteness of S
    is needed here. The descent relation itself must be well founded. -/
theorem forward_required {α : Type u} (f : α → α) (S : α → Prop)
    (r : α → α → Prop) (wf : WellFounded r)
    (closed : ∀ x, S x → S (f x))
    (progress : ∀ x, ¬ S x → ∃ y, (f x = y ∨ f y = x) ∧ r y x) :
    ∀ x, ¬ S x → r (f x) x := by
  intro x
  induction x using wf.induction with
  | h x ih =>
    intro hx
    obtain ⟨y, he, hr⟩ := progress x hx
    rcases he with hf | hb
    · simpa only [hf] using hr
    · have hy : ¬ S y := by
        intro hs
        exact hx (hb ▸ closed y hs)
      have back := ih y hr hy
      rw [hb] at back
      exact False.elim (wellFounded_asymmetric wf x y hr back)

open CollatzAffine GraphRankNecessity

theorem forward_outside_region (R : Nat → Nat) (N : Nat) (S : Nat → Prop)
    (base : ∀ n, n ≤ N → S n)
    (closed : ∀ n, S n → S (U n))
    (progress : ∀ n, N < n → ∃ m, 0 < m ∧ Adjacent n m ∧ R m < R n) :
    ∀ n, ¬ S n → R (U n) < R n := by
  apply forward_required U S (fun m n => R m < R n)
    (InvImage.wf R Nat.lt_wfRel.wf) closed
  intro n hn
  have hlarge : N < n := by
    by_cases h : n ≤ N
    · exact False.elim (hn (base n h))
    · omega
  obtain ⟨m, _, ha, hr⟩ := progress n hlarge
  exact ⟨m, ha, hr⟩

/-- The concrete 110 family obstructs graph ranks monotone between its
    matching feature endpoints, provided the base has bounded forward closure.
    The modular conditions encode the four valuations (0,2,0,0). -/
theorem no_feature_monotone_graph_rank (R : Nat → Nat) (N B M : Nat)
    (hM : 0 < M) (S : Nat → Prop)
    (base : ∀ n, n ≤ N → S n)
    (closed : ∀ n, S n → S (U n))
    (bounded : ∀ n, S n → n ≤ B)
    (progress : ∀ n, N < n → ∃ m, 0 < m ∧ Adjacent n m ∧ R m < R n)
    (monotone : ∀ n m, n < m → n % 8 = 3 → m % 8 = 3 →
      n % 3 = 1 → m % 3 = 1 → n % M = m % M → R n ≤ R m) : False := by
  let s := M*(B+1)
  have hsB : B < s := by
    have h := Nat.mul_le_mul_right (B+1) (show 1 ≤ M by omega)
    simp only [Nat.one_mul] at h
    omega
  have hs : 0 < s := by omega
  obtain ⟨h1, h2, h3, _, hnm, hn8, hm8, hn3, hm3⟩ :=
    BuchiArithmetic.expanding_same_features s hs
  have hmod := BuchiArithmetic.expanding_same_residue s M hs
    (show M ∣ s from Nat.dvd_mul_right M (B+1))
  have order := monotone _ _ hnm hn8 hm8 hn3 hm3 hmod
  have outside1 : ¬ S (192*s-5) := by
    intro h
    have := bounded _ h
    omega
  have outside2 : ¬ S (288*s-7) := by
    intro h
    have := bounded _ h
    omega
  have outside3 : ¬ S (432*s-10) := by
    intro h
    have := bounded _ h
    omega
  have d1 := forward_outside_region R N S base closed progress _ outside1
  have d2 := forward_outside_region R N S base closed progress _ outside2
  have d3 := forward_outside_region R N S base closed progress _ outside3
  change R (BuchiArithmetic.shortcut _) < _ at d1 d2 d3
  rw [h1] at d1
  rw [h2] at d2
  rw [h3] at d3
  omega

#print axioms wellFounded_asymmetric
#print axioms forward_required
#print axioms forward_outside_region
#print axioms no_feature_monotone_graph_rank
end GraphRankOrientation
