/- Actual floor-survivor implications and finite source-cutoff averaging.
   The auxiliary averaging chain is not a model for an individual orbit.
   Logarithmic potentials, infinite iteration and minimum moments are written. -/
import CensoredProgressionTransport

namespace CutoffDescent
open CensoredProgressionTransport

def walk : Nat → Nat → Nat
  | 0, n => n
  | t + 1, n => walk t (ordinary n)

def NeverBelow (h n : Nat) : Prop := ∀ t, h < walk t n

noncomputable def badCell (h n : Nat) : Rat := by
  classical
  exact if NeverBelow h n then 1 else 0

theorem never_below_even (h n : Nat) : NeverBelow h (2 * n) ↔ NeverBelow h n := by
  constructor
  · intro ha t
    have ht := ha (t + 1)
    simpa only [walk, ordinary_even] using ht
  · intro ha t
    cases t with
    | zero => have ht := ha 0; simp only [walk] at *; omega
    | succ t => simpa only [walk, ordinary_even] using ha t

theorem never_below_odd (h n : Nat) :
    NeverBelow h (2 * n + 1) ↔ h < 2 * n + 1 ∧ NeverBelow h (3 * n + 2) := by
  constructor
  · intro ha
    constructor
    · exact ha 0
    · intro t
      simpa only [walk, ordinary_odd, ordinary_even] using ha (t + 2)
  · intro ha t
    cases t with
    | zero => exact ha.1
    | succ t =>
      cases t with
      | zero => simp only [walk, ordinary_odd]; omega
      | succ t => simpa only [walk, ordinary_odd, ordinary_even] using ha.2 t

theorem below_floor_zero (h n : Nat) (hn : n ≤ h) : badCell h n = 0 := by
  classical
  have hbad : ¬ NeverBelow h n := by
    intro hb
    have ht := hb 0
    simp only [walk] at ht
    omega
  simp [badCell, hbad]

theorem bad_bounds (h n : Nat) : 0 ≤ badCell h n ∧ badCell h n ≤ 1 := by
  classical
  by_cases hb : NeverBelow h n <;> simp [badCell, hb] <;> decide

theorem even_cell (h n : Nat) : badCell h (2 * n) = badCell h n := by
  classical
  simp [badCell, never_below_even]

theorem odd_cell_upper (h n : Nat) : badCell h (2 * n + 1) ≤ badCell h (3 * n + 2) := by
  classical
  by_cases hb : NeverBelow h (2 * n + 1)
  · have ht := (never_below_odd h n).mp hb
    simp [badCell, hb, ht.2]
  · simp only [badCell, if_neg hb]
    exact (bad_bounds h (3 * n + 2)).1

theorem sumPos_mono (x : Nat) (f g : Nat → Rat)
    (h : ∀ n, 0 < n → n ≤ x → f n ≤ g n) : sumPos x f ≤ sumPos x g := by
  induction x with
  | zero => simp [sumPos]
  | succ x ih =>
    have ht := ih (by intro n hn hx; exact h n hn (by omega))
    have hx := h (x + 1) (by omega) (by omega)
    simp only [sumPos]
    grind

theorem population_odd_upper (h x : Nat) (hh : 1 ≤ h) :
    sumPos (2 * x + 1) (badCell h) ≤ sumPos x (badCell h) +
      sumPos x (fun n => badCell h (3 * n + 2)) := by
  have hs := parity_split x (badCell h) (below_floor_zero h 1 hh)
  simp only [even_cell] at hs
  have hm := sumPos_mono x (fun n => badCell h (2 * n + 1))
    (fun n => badCell h (3 * n + 2)) (by intro n _ _; exact odd_cell_upper h n)
  rw [hs]
  grind

theorem population_even_upper (h x : Nat) (hh : 1 ≤ h) :
    sumPos (2 * (x + 1)) (badCell h) ≤ sumPos (x + 1) (badCell h) +
      sumPos x (fun n => badCell h (3 * n + 2)) := by
  have ht := population_odd_upper h x hh
  have he : 2 * (x + 1) = (2 * x + 1) + 1 := by omega
  have hec : badCell h (2 * x + 1 + 1) = badCell h (x + 1) := by
    rw [← he, even_cell]
  have hs : sumPos (2 * (x + 1)) (badCell h) =
      sumPos (2 * x + 1) (badCell h) + badCell h (x + 1) := by
    rw [he, sumPos, hec]
  have hr : sumPos (x + 1) (badCell h) =
      sumPos x (badCell h) + badCell h (x + 1) := rfl
  rw [hs, hr]
  grind

theorem fair_mean_bound (f a b p q delta e : Rat)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) (hq : 0 ≤ q ∧ q ≤ 1 / 2)
    (hd : delta ≤ e) (hf : f ≤ p * a + q * b + q * delta) :
    f ≤ (a + b + e) / 2 := by
  have h1 := Rat.mul_le_mul_of_nonneg_right hp.2 ha
  have h2 := Rat.mul_le_mul_of_nonneg_right hq.2 hb
  have h3 := Rat.mul_le_mul_of_nonneg_left hd hq.1
  have h4 := Rat.mul_le_mul_of_nonneg_right hq.2 he
  grind

def lower (n : Nat) : Nat := n / 2
def upper (n : Nat) : Nat := 3 * ((n - 1) / 2) + 2

theorem cutoffs_even (x : Nat) : lower (2 * (x + 1)) = x + 1 ∧
    upper (2 * (x + 1)) = 3 * x + 2 := by
  simp only [lower, upper]
  omega

theorem cutoffs_odd (x : Nat) : lower (2 * x + 1) = x ∧
    upper (2 * x + 1) = 3 * x + 2 := by
  simp only [lower, upper]
  omega

theorem positive_parity (n : Nat) (hn : 0 < n) :
    (∃ x, n = 2 * (x + 1)) ∨ (∃ x, n = 2 * x + 1) := by
  by_cases h : n % 2 = 0
  · exact Or.inl ⟨n / 2 - 1, by omega⟩
  · exact Or.inr ⟨n / 2, by omega⟩

theorem cutoff_product_bound (n : Nat) (hn : 3 ≤ n) :
    4 * lower n * upper n < 3 * n ^ 2 := by
  rcases positive_parity n (by omega) with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [(cutoffs_even x).1, (cutoffs_even x).2]
    have h : 4 * (x + 1) * (3 * x + 2) + 4 * (x + 1) = 3 * (2 * (x + 1)) ^ 2 := by grind
    omega
  · rw [(cutoffs_odd x).1, (cutoffs_odd x).2]
    have h : 4 * x * (3 * x + 2) + (4 * x + 3) = 3 * (2 * x + 1) ^ 2 := by grind
    omega

theorem reciprocal_cross_bound (n : Nat) (hn : 3 ≤ n) :
    8 * lower n * upper n ≤ 3 * n * (lower n + upper n) := by
  rcases positive_parity n (by omega) with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [(cutoffs_even x).1, (cutoffs_even x).2]
    have h : 8 * (x + 1) * (3 * x + 2) + 2 * (x + 1) =
        3 * (2 * (x + 1)) * ((x + 1) + (3 * x + 2)) := by grind
    omega
  · rw [(cutoffs_odd x).1, (cutoffs_odd x).2]
    have h : 8 * x * (3 * x + 2) + (8 * x + 6) =
        3 * (2 * x + 1) * (x + (3 * x + 2)) := by grind
    omega

theorem boundary_overshoot (h n : Nat) (hh : 3 ≤ h) (hn : h < n) :
    h ≤ 2 * lower n ∧ h ≤ 2 * upper n ∧ n < upper n := by
  simp only [lower, upper]
  omega

def terminal (h : Nat) : Nat → (Nat → Rat) → Nat → Rat
  | 0, f, n => f n
  | k + 1, f, n => if n ≤ h then f n else
      (terminal h k f (lower n) + terminal h k f (upper n)) / 2

def occupation (h : Nat) : Nat → (Nat → Rat) → Nat → Rat
  | 0, _, _ => 0
  | k + 1, g, n => if n ≤ h then 0 else g n +
      (occupation h k g (lower n) + occupation h k g (upper n)) / 2

theorem finite_unroll (h k : Nat) (f e : Nat → Rat)
    (hf : ∀ n, h < n → f n ≤ (f (lower n) + f (upper n)) / 2 + e n) :
    ∀ n, f n ≤ terminal h k f n + occupation h k e n := by
  induction k with
  | zero => intro n; simp only [terminal, occupation]; grind
  | succ k ih =>
    intro n
    by_cases hn : n ≤ h
    · simp only [terminal, occupation, if_pos hn]; grind
    · have hs := hf n (by omega)
      have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [terminal, occupation, if_neg hn]
      grind

theorem finite_potential_budget (h k : Nat) (v g : Nat → Rat) (c : Rat)
    (hv : ∀ n, h < n → c * g n ≤ (v (lower n) + v (upper n)) / 2 - v n) :
    ∀ n, c * occupation h k g n ≤ terminal h k v n - v n := by
  induction k with
  | zero => intro n; simp only [terminal, occupation]; grind
  | succ k ih =>
    intro n
    by_cases hn : n ≤ h
    · simp only [terminal, occupation, if_pos hn]; grind
    · have hs := hv n (by omega)
      have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [terminal, occupation, if_neg hn]
      grind

theorem terminal_upper (h k : Nat) (v : Nat → Rat) (cap : Rat)
    (hv : ∀ n, v n ≤ cap) : ∀ n, terminal h k v n ≤ cap := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    intro n
    by_cases hn : n ≤ h
    · simpa only [terminal, if_pos hn] using hv n
    · have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [terminal, if_neg hn]
      grind

theorem terminal_mono (h k : Nat) (v w : Nat → Rat)
    (hv : ∀ n, v n ≤ w n) : ∀ n, terminal h k v n ≤ terminal h k w n := by
  induction k with
  | zero => exact hv
  | succ k ih =>
    intro n
    by_cases hn : n ≤ h
    · simpa only [terminal, if_pos hn] using hv n
    · have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [terminal, if_neg hn]
      grind

theorem stopped_comparison (h k : Nat) (f e v : Nat → Rat) (c cap : Rat)
    (hc : 0 ≤ c)
    (hf : ∀ n, h < n → f n ≤ (f (lower n) + f (upper n)) / 2 + e n)
    (hv : ∀ n, h < n → c * e n ≤ (v (lower n) + v (upper n)) / 2 - v n)
    (hcap : ∀ n, v n ≤ cap) :
    ∀ n, c * f n ≤ c * terminal h k f n + cap - v n := by
  intro n
  have hf1 := finite_unroll h k f e hf n
  have hp := finite_potential_budget h k v e c hv n
  have hb := terminal_upper h k v cap hcap n
  have hm := Rat.mul_le_mul_of_nonneg_left hf1 hc
  grind

theorem tangent_drift (v vl vu l ll lu slope drift : Rat)
    (hs : 0 ≤ slope) (hl : drift ≤ l - (ll + lu) / 2)
    (hvl : v + slope * (l - ll) ≤ vl)
    (hvu : v + slope * (l - lu) ≤ vu) :
    slope * drift ≤ (vl + vu) / 2 - v := by
  have hm := Rat.mul_le_mul_of_nonneg_left hl hs
  grind

#print axioms never_below_even
#print axioms never_below_odd
#print axioms below_floor_zero
#print axioms odd_cell_upper
#print axioms population_odd_upper
#print axioms population_even_upper
#print axioms fair_mean_bound
#print axioms cutoff_product_bound
#print axioms reciprocal_cross_bound
#print axioms boundary_overshoot
#print axioms finite_unroll
#print axioms finite_potential_budget
#print axioms terminal_upper
#print axioms terminal_mono
#print axioms stopped_comparison
#print axioms tangent_drift

end CutoffDescent
