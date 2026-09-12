/-
  A multiplicative budget for arbitrary positive halving exponents in a cycle.
  The minimum >=7 is an explicit hypothesis; this file does not prove the
  classification of smaller cycle minima, or the Collatz conjecture.
  Standalone Lean 4; kernel checking only.
  Check: lean CollatzCycleBudget.lean
-/
namespace CollatzCycleBudget

def gain (h : Nat) : Nat := if h = 1 then 5 else 3
def loss (h : Nat) : Nat := if h = 1 then 3 else 2 ^ h

/-- Centering at 1 bounds the expanding step and every contracting step,
    including arbitrarily large halving exponents. -/
theorem step_budget (h n next : Nat) (hh : 1 ≤ h) (hn : 7 ≤ n)
    (hnext : 0 < next) (hs : 2 ^ h * next = 3 * n + 1) :
    loss h * (next - 1) ≤ gain h * (n - 1) := by
  have hn' : n = (n - 1) + 1 := by omega
  have hnext' : next = (next - 1) + 1 := by omega
  have hshift : 2 ^ h * (next - 1) + 2 ^ h = 3 * (n - 1) + 4 := by
    rw [hn', hnext', Nat.mul_add, Nat.mul_add] at hs
    simpa using hs
  by_cases he : h = 1
  · simp [gain, loss, he]
    simp only [he, Nat.pow_one] at hshift
    omega
  · have hp : 4 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ h)
    simp only [gain, loss, if_neg he]
    omega

def gainProduct (h : Nat → Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => gain (h t) * gainProduct h t

def lossProduct (h : Nat → Nat) : Nat → Nat
  | 0 => 1
  | t + 1 => loss (h t) * lossProduct h t

theorem prefix_budget (h n : Nat → Nat) : ∀ k,
    (∀ i, i < k → 1 ≤ h i) →
    (∀ i, i ≤ k → 7 ≤ n i) →
    (∀ i, i < k → 2 ^ h i * n (i + 1) = 3 * n i + 1) →
    lossProduct h k * (n k - 1) ≤ gainProduct h k * (n 0 - 1)
  | 0, _, _, _ => by simp [gainProduct, lossProduct]
  | k + 1, hh, hn, hs => by
    have ih := prefix_budget h n k (fun i hi => hh i (by omega))
      (fun i hi => hn i (by omega)) (fun i hi => hs i (by omega))
    have hi := step_budget (h k) (n k) (n (k + 1)) (hh k (by omega))
      (hn k (by omega)) (by have := hn (k + 1) (by omega); omega) (hs k (by omega))
    have hl := Nat.mul_le_mul_left (lossProduct h k) hi
    have hr := Nat.mul_le_mul_left (gain (h k)) ih
    calc
      lossProduct h (k + 1) * (n (k + 1) - 1) =
          lossProduct h k * (loss (h k) * (n (k + 1) - 1)) := by
        simp [lossProduct, Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ lossProduct h k * (gain (h k) * (n k - 1)) := hl
      _ = gain (h k) * (lossProduct h k * (n k - 1)) := by ac_rfl
      _ ≤ gain (h k) * (gainProduct h k * (n 0 - 1)) := hr
      _ = gainProduct h (k + 1) * (n 0 - 1) := by simp [gainProduct, Nat.mul_assoc]

theorem product_budget (h n : Nat → Nat) (k : Nat)
    (hh : ∀ i, i < k → 1 ≤ h i)
    (hn : ∀ i, i ≤ k → 7 ≤ n i)
    (hs : ∀ i, i < k → 2 ^ h i * n (i + 1) = 3 * n i + 1)
    (hc : n k = n 0) : lossProduct h k ≤ gainProduct h k := by
  have hb := prefix_budget h n k hh hn hs
  rw [hc] at hb
  have hp : 0 < n 0 - 1 := by have := hn 0 (by omega); omega
  exact Nat.le_of_mul_le_mul_right hb hp

def ones (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => ones h t + if h t = 1 then 1 else 0

def others (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => others h t + if h t = 1 then 0 else 1

def excess (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => excess h t + if h t = 1 then 0 else h t - 2

def total (h : Nat → Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => total h t + h t

theorem count_partition (h : Nat → Nat) : ∀ k, ones h k + others h k = k
  | 0 => by simp [ones, others]
  | k + 1 => by
    have ih := count_partition h k
    by_cases he : h k = 1 <;> simp [ones, others, he] <;> omega

theorem total_partition (h : Nat → Nat) : ∀ k,
    (∀ i, i < k → 1 ≤ h i) →
    total h k = ones h k + 2 * others h k + excess h k
  | 0, _ => by simp [total, ones, others, excess]
  | k + 1, hh => by
    have ih := total_partition h k (fun i hi => hh i (by omega))
    have hk := hh k (by omega)
    by_cases he : h k = 1 <;> simp [total, ones, others, excess, he] <;> omega

theorem gain_formula (h : Nat → Nat) : ∀ k,
    gainProduct h k = 5 ^ ones h k * 3 ^ others h k
  | 0 => by simp [gainProduct, ones, others]
  | k + 1 => by
    by_cases he : h k = 1 <;>
      simp [gainProduct, gain, gain_formula h k, ones, others, he, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

theorem loss_formula (h : Nat → Nat) : ∀ k,
    (∀ i, i < k → 1 ≤ h i) →
    lossProduct h k = 3 ^ ones h k * 2 ^ (2 * others h k + excess h k)
  | 0, _ => by simp [lossProduct, ones, others, excess]
  | k + 1, hh => by
    have ih := loss_formula h k (fun i hi => hh i (by omega))
    have hk := hh k (by omega)
    by_cases he : h k = 1
    · simp [lossProduct, loss, ih, ones, others, excess, he, Nat.pow_succ,
        Nat.mul_comm, Nat.mul_left_comm]
    · have hexp : 2 * (others h k + 1) + (excess h k + (h k - 2)) =
          h k + (2 * others h k + excess h k) := by omega
      simp only [lossProduct, loss, if_neg he, ih, ones, others, excess, Nat.add_zero]
      rw [hexp]
      simp only [Nat.pow_add]
      ac_rfl

/-- Joint budget for q one-halving steps, R other steps, and E excess
    halvings beyond two per other step: 3^q 2^(2R+E) ≤ 5^q 3^R. -/
theorem cycle_budget (h n : Nat → Nat) (k : Nat)
    (hh : ∀ i, i < k → 1 ≤ h i)
    (hn : ∀ i, i ≤ k → 7 ≤ n i)
    (hs : ∀ i, i < k → 2 ^ h i * n (i + 1) = 3 * n i + 1)
    (hc : n k = n 0) :
    3 ^ ones h k * 2 ^ (2 * others h k + excess h k) ≤
      5 ^ ones h k * 3 ^ others h k := by
  have hb := product_budget h n k hh hn hs hc
  simpa only [gain_formula, loss_formula h k hh] using hb

#print axioms step_budget
#print axioms prefix_budget
#print axioms count_partition
#print axioms total_partition
#print axioms cycle_budget

end CollatzCycleBudget
