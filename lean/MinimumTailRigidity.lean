/- Linear minimum-tail budgets have a diagonal rigidity absent below that scale.
   The actual Collatz budget remains unproved. The escaping map is explicitly
   the separate DensityCountermodel, not the ordinary Collatz map. -/
import ClockedMinimum
import DensityCountermodel

namespace MinimumTailRigidity
open OrdinaryCollatz ClockedMinimum

noncomputable def minimumClock (n : Nat) : Nat := Classical.choose (minimum_exists n)
noncomputable def minimum (n : Nat) : Nat := iterate (minimumClock n) n

theorem minimum_attained (n : Nat) : ∃ t, iterate t n = minimum n :=
  ⟨minimumClock n, rfl⟩

theorem minimum_le (n t : Nat) : minimum n ≤ iterate t n := by
  exact Classical.choose_spec (minimum_exists n) t

theorem minimum_positive {n : Nat} (hn : 0 < n) : 0 < minimum n :=
  iterate_positive (minimumClock n) n hn

theorem minimum_idempotent (n : Nat) : minimum (minimum n) = minimum n := by
  have h1 := minimum_le (minimum n) 0
  have h2 := minimum_le n (minimumClock n + minimumClock (minimum n))
  rw [iterate_add] at h2
  change minimum (minimum n) ≤ minimum n at h1
  change minimum n ≤ minimum (minimum n) at h2
  omega

def sumPos (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumPos f n + f (n + 1)

def tailTerm (m : Nat → Nat) (h n : Nat) : Nat := if h < m n then m n else 0
def tailSum (m : Nat → Nat) (h n : Nat) : Nat := sumPos (tailTerm m h) n

theorem term_le_sum (f : Nat → Nat) {j n : Nat} (hj : 0 < j) (hjn : j ≤ n) :
    f j ≤ sumPos f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j = n + 1
    · subst j; simp only [sumPos]; omega
    · have hl := ih (by omega)
      simp only [sumPos]
      omega

theorem sum_mono (f g : Nat → Nat) (n : Nat)
    (h : ∀ j, 0 < j → j ≤ n → f j ≤ g j) : sumPos f n ≤ sumPos g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hl := ih (by intro j hj hjn; exact h j hj (by omega))
    have hr := h (n + 1) (by omega) (by omega)
    simp only [sumPos]
    omega

theorem diagonal_tail_lower (m : Nat → Nat) (h n : Nat)
    (hp : 0 < m n) (hi : m (m n) = m n) (hh : h < m n) :
    m n ≤ tailSum m h (m n) := by
  have ht := term_le_sum (tailTerm m h) hp (Nat.le_refl (m n))
  simpa only [tailTerm, hi, if_pos hh, tailSum] using ht

theorem tail_budget_rigidity (m : Nat → Nat) (h : Nat)
    (hp : ∀ n, 0 < n → 0 < m n)
    (hi : ∀ n, 0 < n → m (m n) = m n) :
    (∀ n, 0 < n → tailSum m h n < n) ↔ (∀ n, 0 < n → m n ≤ h) := by
  constructor
  · intro hb n hn
    apply Classical.byContradiction
    intro hno
    have hl := diagonal_tail_lower m h n (hp n hn) (hi n hn) (by omega)
    have hu := hb (m n) (hp n hn)
    omega
  · intro hb n hn
    have hz : ∀ n, tailSum m h n = 0 := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        have hl := hb (n + 1) (by omega)
        simp only [tailSum, sumPos, tailTerm, if_neg (by omega : ¬ h < m (n + 1))] at *
        omega
    rw [hz]
    exact hn

theorem minimum_budget_iff_bounded (h : Nat) :
    (∀ n, 0 < n → tailSum minimum h n < n) ↔
      (∀ n, 0 < n → minimum n ≤ h) :=
  tail_budget_rigidity minimum h (fun _ hn => minimum_positive hn)
    (fun n _ => minimum_idempotent n)

def prefixMinimum : Nat → Nat → Nat
  | 0, n => n
  | t + 1, n => min n (prefixMinimum t (C n))

theorem prefix_lower_bound (b t n : Nat)
    (hb : ∀ j, j ≤ t → b ≤ iterate j n) : b ≤ prefixMinimum t n := by
  induction t generalizing n with
  | zero => exact hb 0 (Nat.le_refl _)
  | succ t ih =>
    have h0 := hb 0 (by omega)
    have hs := ih (C n) (by intro j hj; exact hb (j + 1) (by omega))
    change b ≤ n at h0
    simp only [prefixMinimum]
    omega

theorem minimum_le_prefix (t n : Nat) : minimum n ≤ prefixMinimum t n :=
  prefix_lower_bound (minimum n) t n (fun j _ => minimum_le n j)

theorem tail_term_mono (f g : Nat → Nat) (h n : Nat) (hfg : f n ≤ g n) :
    tailTerm f h n ≤ tailTerm g h n := by
  simp only [tailTerm]
  split <;> split <;> omega

theorem finite_prefix_budget (h : Nat) (clock : Nat → Nat)
    (hb : ∀ n, 0 < n → tailSum (prefixMinimum (clock n)) h n < n) :
    ∀ n, 0 < n → minimum n ≤ h := by
  apply (minimum_budget_iff_bounded h).mp
  intro n hn
  have hl := sum_mono (tailTerm minimum h)
    (tailTerm (prefixMinimum (clock n)) h) n
    (fun j _ _ => tail_term_mono _ _ h j (minimum_le_prefix (clock n) j))
  have hu := hb n hn
  change tailSum minimum h n ≤ tailSum (prefixMinimum (clock n)) h n at hl
  omega

theorem bounded_minimum_verified_floor (h : Nat)
    (hm : ∀ n, 0 < n → minimum n ≤ h)
    (hv : ∀ n, 0 < n → n ≤ h → ReachesOne n) : Conjecture := by
  intro n hn
  exact reaches_of_iterate (hv (minimum n) (minimum_positive hn) (hm n hn))

theorem finite_prefix_verified_floor (h : Nat) (clock : Nat → Nat)
    (hb : ∀ n, 0 < n → tailSum (prefixMinimum (clock n)) h n < n)
    (hv : ∀ n, 0 < n → n ≤ h → ReachesOne n) : Conjecture :=
  bounded_minimum_verified_floor h (finite_prefix_budget h clock hb) hv

theorem comparison_spine_minimum (k t : Nat) :
    DensityCountermodel.spine k ≤ DensityCountermodel.iterate t (DensityCountermodel.spine k) := by
  have hpow : ∀ j, k ≤ j → 2 ^ k ≤ 2 ^ j := by
    intro j hj
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hj
  by_cases he : t % 2 = 0
  · have ht : t = 2 * (t / 2) := by omega
    rw [ht, DensityCountermodel.iterate_even]
    have hp := hpow (k + t / 2) (by omega)
    unfold DensityCountermodel.spine
    omega
  · have ht : t = 2 * (t / 2) + 1 := by omega
    rw [ht, DensityCountermodel.iterate_odd]
    have hp := hpow (k + t / 2 + 1) (by omega)
    have hq := Nat.two_pow_pos k
    unfold DensityCountermodel.spine
    omega

def dyadicBudget : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n + dyadicBudget k (n / 2)

theorem dyadic_budget_bound (k n : Nat) : dyadicBudget k n ≤ 2 * n := by
  induction k generalizing n with
  | zero => simp only [dyadicBudget]; omega
  | succ k ih =>
    have ht := ih (n / 2)
    simp only [dyadicBudget]
    omega

theorem progression_count_weight (v x k : Nat)
    (hx : v + 2 * (v + 1) * k ≤ x) : v * (k + 1) ≤ x := by
  have hm := Nat.mul_le_mul_right k (show v ≤ 2 * (v + 1) by omega)
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem uniform_atom_majorant (v n count : Nat) (hv : 2 ≤ v)
    (hc : v * count ≤ 2 * n) : (v + 1) * count ≤ 3 * n := by
  have hm := Nat.mul_le_mul_right count hv
  rw [Nat.add_mul, Nat.one_mul]
  omega

#print axioms minimum_attained
#print axioms minimum_le
#print axioms minimum_positive
#print axioms minimum_idempotent
#print axioms term_le_sum
#print axioms sum_mono
#print axioms diagonal_tail_lower
#print axioms tail_budget_rigidity
#print axioms minimum_budget_iff_bounded
#print axioms prefix_lower_bound
#print axioms minimum_le_prefix
#print axioms tail_term_mono
#print axioms finite_prefix_budget
#print axioms bounded_minimum_verified_floor
#print axioms finite_prefix_verified_floor
#print axioms comparison_spine_minimum
#print axioms dyadic_budget_bound
#print axioms progression_count_weight
#print axioms uniform_atom_majorant

end MinimumTailRigidity
