/- Necessary conditions for a natural-valued bidirectional Collatz rank.
   No such global rank is constructed here. -/
import CollatzAffine

namespace GraphRankNecessity
open CollatzAffine

def Adjacent (n m : Nat) : Prop := U n = m ∨ U m = n

theorem even_step (n : Nat) : U (2*n) = n := by
  unfold U
  rw [if_neg (by omega)]
  omega

/-- A multiple of three has no odd predecessor under the shortcut map. -/
theorem predecessor_of_three_divides (n m : Nat) (hd : 3 ∣ n)
    (he : U m = n) : m = 2*n := by
  obtain ⟨k, rfl⟩ := hd
  unfold U at he
  split at he <;> omega

/-- Above the exceptional base, the doubling ray over a multiple of three
    must be strictly increasing in any natural-valued rank with local descent. -/
theorem doubling_increases (R : Nat → Nat) (N : Nat)
    (progress : ∀ n, N < n → ∃ m, 0 < m ∧ Adjacent n m ∧ R m < R n)
    (n : Nat) (hn : N < n) (hd : 3 ∣ n) : R n < R (2*n) := by
  have main : ∀ k n, R (2*n) = k → N < n → 3 ∣ n → R n < R (2*n) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n he hn hd
      by_cases good : R n < R (2*n)
      · exact good
      apply False.elim
      obtain ⟨m, _, ha, hr⟩ := progress (2*n) (by omega)
      rcases ha with hf | hb
      · rw [even_step] at hf
        subst m
        omega
      · have hd2 : 3 ∣ 2*n := by
          obtain ⟨t, ht⟩ := hd
          exact ⟨2*t, by omega⟩
        have hm := predecessor_of_three_divides (2*n) m hd2 hb
        subst m
        have smaller := ih (R (2*(2*n))) (by omega) (2*n) rfl (by omega) hd2
        omega
  exact main (R (2*n)) n rfl hn hd

/-- Bidirectional descent cannot replace forward descent at multiples of three. -/
theorem forward_descent_on_multiples_of_three (R : Nat → Nat) (N : Nat)
    (progress : ∀ n, N < n → ∃ m, 0 < m ∧ Adjacent n m ∧ R m < R n)
    (n : Nat) (hn : N < n) (hd : 3 ∣ n) : R (U n) < R n := by
  obtain ⟨m, _, ha, hr⟩ := progress n hn
  rcases ha with hf | hb
  · simpa only [hf] using hr
  · have hm := predecessor_of_three_divides n m hd hb
    have grow := doubling_increases R N progress n hn hd
    subst m
    omega

#print axioms predecessor_of_three_divides
#print axioms doubling_increases
#print axioms forward_descent_on_multiples_of_three
end GraphRankNecessity
