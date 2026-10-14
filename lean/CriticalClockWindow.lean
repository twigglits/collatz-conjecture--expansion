/- Finite actual-cell transport and clocked cutoff-tree identities.
   The Gaussian limit, logarithmic estimates and boundary limits are written.
   This module does not prove an asymptotic zero limit or Collatz. -/
import CutoffDescent

namespace CriticalClockWindow
open CensoredProgressionTransport CutoffDescent

def alive : Nat → Nat → Rat
  | 0, n => if n = 1 then 0 else 1
  | t + 1, n => if n = 1 then 0 else alive t (ordinary n)

def cellFrom : Nat → Nat → Rat → Rat
  | 0, n, p => if n = 1 then 0 else 1 - p
  | t + 1, n, p => if n = 1 then 0 else cellFrom t (ordinary n) (p * factor n)

def cell (t n : Nat) : Rat := cellFrom t n 1

theorem cell_bounds (t n : Nat) (p : Rat) (hp : 0 ≤ p ∧ p ≤ 1) :
    0 ≤ cellFrom t n p ∧ cellFrom t n p ≤ alive t n ∧ alive t n ≤ 1 := by
  induction t generalizing n p with
  | zero => simp only [cellFrom, alive]; split <;> grind
  | succ t ih =>
    by_cases hn : n = 1
    · simp [cellFrom, alive, hn]; decide
    · have hf := factor_bounds n
      have hl := Rat.mul_nonneg hp.1 hf.1
      have hu := Rat.mul_le_mul_of_nonneg_right hp.2 hf.1
      have ht := ih (ordinary n) (p * factor n) ⟨hl, by grind⟩
      simpa only [cellFrom, alive, if_neg hn] using ht

theorem cell_increment (t n : Nat) (p : Rat) :
    deficitFrom (t + 1) n p - deficitFrom t n p = cellFrom t n p := by
  induction t generalizing n p with
  | zero => simp only [deficitFrom, cellFrom]; split <;> grind
  | succ t ih =>
    by_cases hn : n = 1
    · simp [deficitFrom, cellFrom, hn]; grind
    · have ht := ih (ordinary n) (p * factor n)
      simp only [deficitFrom, cellFrom, if_neg hn] at ht ⊢
      grind

theorem scaled_cell (t n : Nat) (p : Rat) :
    cellFrom t n p = p * cell t n + (1 - p) * alive t n := by
  induction t generalizing n p with
  | zero => simp only [cell, cellFrom, alive]; split <;> grind
  | succ t ih =>
    by_cases hn : n = 1
    · simp [cell, cellFrom, alive, hn]; grind
    · have ht := ih (ordinary n) (p * factor n)
      have h1 := ih (ordinary n) (factor n)
      simp only [cell, cellFrom, alive, if_neg hn, Rat.one_mul] at *
      grind

theorem even_cell_transport (t n : Nat) : cell (t + 1) (2 * n) = cell t n := by
  have hn : 2 * n ≠ 1 := by omega
  simp [cell, cellFrom, hn, ordinary_even, factor_even]

theorem odd_cell_transport (t n : Nat) (hn : 0 < n) :
    cell (t + 2) (2 * n + 1) =
      factor (2 * n + 1) * cell t (3 * n + 2) +
        (1 - factor (2 * n + 1)) * alive t (3 * n + 2) := by
  have h1 : 2 * n + 1 ≠ 1 := by omega
  have h2 : 2 * (3 * n + 2) ≠ 1 := by omega
  have hs := scaled_cell t (3 * n + 2) (factor (2 * n + 1))
  simpa only [cell, cellFrom, if_neg h1, ordinary_odd, if_neg h2,
    ordinary_even, factor_even, Rat.one_mul, Rat.mul_one] using hs

theorem odd_cell_correction_bounds (t n : Nat) (hn : 0 < n) :
    0 ≤ cell (t + 2) (2 * n + 1) - cell t (3 * n + 2) ∧
      2 * ((3 * n + 2 : Nat) : Rat) *
        (cell (t + 2) (2 * n + 1) - cell t (3 * n + 2)) ≤ 1 := by
  have ht := odd_cell_transport t n hn
  have hb := cell_bounds t (3 * n + 2) 1 (by decide)
  have hf := factor_bounds (2 * n + 1)
  have he := odd_loss_identity n
  have hp := Rat.mul_nonneg (by grind : 0 ≤ 1 - factor (2 * n + 1))
    (by grind : 0 ≤ alive t (3 * n + 2) - cellFrom t (3 * n + 2) 1)
  simp only [cell] at *
  have hd : cellFrom (t + 2) (2 * n + 1) 1 - cellFrom t (3 * n + 2) 1 =
      (1 - factor (2 * n + 1)) *
        (alive t (3 * n + 2) - cellFrom t (3 * n + 2) 1) := by grind
  rw [hd]
  constructor
  · exact hp
  · rw [← Rat.mul_assoc, he, Rat.one_mul]
    grind

theorem even_population_transport (t x : Nat) :
    sumPos (2 * (x + 1)) (deficit (t + 2)) =
      sumPos (x + 1) (deficit (t + 1)) + sumPos x (fun n => deficit t (3 * n + 2)) +
        sumPos x (fun n => correction t (3 * n + 2)) := by
  have ht := population_transport t x
  have hn : 2 * (x + 1) = (2 * x + 1) + 1 := by omega
  have hs : sumPos (2 * (x + 1)) (deficit (t + 2)) =
      sumPos (2 * x + 1) (deficit (t + 2)) + deficit (t + 1) (x + 1) := by
    rw [hn, sumPos, ← hn, even_transport (t + 1)]
  have hr : sumPos (x + 1) (deficit (t + 1)) =
      sumPos x (deficit (t + 1)) + deficit (t + 1) (x + 1) := rfl
  rw [hs, hr]
  grind

theorem fair_residual_bound (f a b p q delta correction cap e c : Rat)
    (ha : 0 ≤ a ∧ a ≤ cap) (hb : 0 ≤ b ∧ b ≤ cap)
    (hp : 0 ≤ p ∧ p ≤ 1 / 2) (hq : 0 ≤ q ∧ q ≤ 1 / 2)
    (hd : -e ≤ delta ∧ delta ≤ e) (he : 0 ≤ e)
    (hc : 0 ≤ correction ∧ correction ≤ c)
    (hf : f = p * a + q * b + q * delta + correction) :
    -(e / 2 + c + cap * (1 - p - q)) ≤ f - (a + b) / 2 ∧
      f - (a + b) / 2 ≤ e / 2 + c + cap * (1 - p - q) := by
  have hp0 : 0 ≤ 1 / 2 - p := by grind
  have hq0 : 0 ≤ 1 / 2 - q := by grind
  have hl1 := Rat.mul_nonneg hp0 ha.1
  have hl2 := Rat.mul_nonneg hq0 hb.1
  have hu1 := Rat.mul_le_mul_of_nonneg_left ha.2 hp0
  have hu2 := Rat.mul_le_mul_of_nonneg_left hb.2 hq0
  have hd1 := Rat.mul_le_mul_of_nonneg_left hd.1 hq.1
  have hd2 := Rat.mul_le_mul_of_nonneg_left hd.2 hq.1
  have hd3 := Rat.mul_le_mul_of_nonneg_right hq.2 he
  have hcap : 0 ≤ cap := by grind
  have hg := Rat.mul_nonneg hcap (show 0 ≤ 1 - p - q by grind)
  grind

def timedTerminal (h : Nat) : Nat → (Nat → Nat → Rat) → Nat → Nat → Rat
  | 0, f, t, n => f t n
  | k + 1, f, t, n => if n ≤ h then f t n else
      (timedTerminal h k f (t - 1) (lower n) + timedTerminal h k f (t - 2) (upper n)) / 2

def timedOccupation (h : Nat) : Nat → (Nat → Nat → Rat) → Nat → Nat → Rat
  | 0, _, _, _ => 0
  | k + 1, e, t, n => if n ≤ h then 0 else e t n +
      (timedOccupation h k e (t - 1) (lower n) + timedOccupation h k e (t - 2) (upper n)) / 2

theorem timed_upper_unroll (h k : Nat) (f e : Nat → Nat → Rat)
    (hf : ∀ t n, h < n → f t n ≤
      (f (t - 1) (lower n) + f (t - 2) (upper n)) / 2 + e t n) :
    ∀ t n, f t n ≤ timedTerminal h k f t n + timedOccupation h k e t n := by
  induction k with
  | zero => intro t n; simp only [timedTerminal, timedOccupation]; grind
  | succ k ih =>
    intro t n
    by_cases hn : n ≤ h
    · simp only [timedTerminal, timedOccupation, if_pos hn]; grind
    · have hs := hf t n (by omega)
      have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      simp only [timedTerminal, timedOccupation, if_neg hn]
      grind

theorem timed_lower_unroll (h k : Nat) (f e : Nat → Nat → Rat)
    (hf : ∀ t n, h < n →
      (f (t - 1) (lower n) + f (t - 2) (upper n)) / 2 - e t n ≤ f t n) :
    ∀ t n, timedTerminal h k f t n - timedOccupation h k e t n ≤ f t n := by
  induction k with
  | zero => intro t n; simp only [timedTerminal, timedOccupation]; grind
  | succ k ih =>
    intro t n
    by_cases hn : n ≤ h
    · simp only [timedTerminal, timedOccupation, if_pos hn]; grind
    · have hs := hf t n (by omega)
      have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      simp only [timedTerminal, timedOccupation, if_neg hn]
      grind

theorem timed_cost_majorant (h k t : Nat) (e : Nat → Nat → Rat) (g : Nat → Rat) (cap : Rat)
    (he : ∀ s n, s ≤ t → h < n → e s n ≤ cap * g n) :
    ∀ s n, s ≤ t → timedOccupation h k e s n ≤ cap * occupation h k g n := by
  induction k with
  | zero => intro s n _; simp only [timedOccupation, occupation]; grind
  | succ k ih =>
    intro s n hst
    by_cases hn : n ≤ h
    · simp only [timedOccupation, occupation, if_pos hn]; grind
    · have hs := he s n hst (by omega)
      have hl := ih (s - 1) (lower n) (by omega)
      have hu := ih (s - 2) (upper n) (by omega)
      simp only [timedOccupation, occupation, if_neg hn]
      grind

theorem remaining_clock_composition (t j c : Nat) : (t - j) - c = t - (j + c) := by omega

theorem ideal_clock_balance (l2 l3 : Rat) :
    -l2 + (2 * l2 - l3) / 3 = -(l2 + l3) / 3 ∧
      (l3 - l2) + 2 * ((2 * l2 - l3) / 3) = (l2 + l3) / 3 := by grind

def signMean (h : Nat) : Nat → Nat → Rat → Rat
  | 0, _, s => s
  | k + 1, n, s => if n ≤ h then s else
      (signMean h k (lower n) (s - 1) + signMean h k (upper n) (s + 1)) / 2

def signSecond (h : Nat) : Nat → Nat → Rat → Rat
  | 0, _, s => s ^ 2
  | k + 1, n, s => if n ≤ h then s ^ 2 else
      (signSecond h k (lower n) (s - 1) + signSecond h k (upper n) (s + 1)) / 2

theorem stopped_sign_mean (h k n : Nat) (s : Rat) : signMean h k n s = s := by
  induction k generalizing n s with
  | zero => rfl
  | succ k ih =>
    simp only [signMean]
    split
    · rfl
    · rw [ih, ih]
      grind

theorem stopped_sign_second (h k n : Nat) (s : Rat) :
    signSecond h k n s = s ^ 2 + occupation h k (fun _ => 1) n := by
  induction k generalizing n s with
  | zero => simp only [signSecond, occupation]; grind
  | succ k ih =>
    by_cases hn : n ≤ h
    · simp only [signSecond, occupation, if_pos hn]; grind
    · simp only [signSecond, occupation, if_neg hn]
      rw [ih, ih]
      grind

#print axioms cell_bounds
#print axioms cell_increment
#print axioms scaled_cell
#print axioms even_cell_transport
#print axioms odd_cell_transport
#print axioms odd_cell_correction_bounds
#print axioms even_population_transport
#print axioms fair_residual_bound
#print axioms timed_upper_unroll
#print axioms timed_lower_unroll
#print axioms timed_cost_majorant
#print axioms remaining_clock_composition
#print axioms ideal_clock_balance
#print axioms stopped_sign_mean
#print axioms stopped_sign_second

end CriticalClockWindow
