/- Finite transport for the actual ordinary Collatz map, stopped at one.
   No assertion here concerns an infinite orbit, a density limit, or Collatz. -/
import Std

namespace CensoredProgressionTransport

def ordinary (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def factor (n : Nat) : Rat :=
  if n % 2 = 0 then 1 else (3 * (n : Rat)) / (3 * (n : Rat) + 1)

def liveTime : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => if n = 1 then 0 else 1 + liveTime t (ordinary n)

def deficitFrom : Nat → Nat → Rat → Rat
  | 0, _, _ => 0
  | t + 1, n, p => if n = 1 then 0 else
      (1 - p) + deficitFrom t (ordinary n) (p * factor n)

def deficit (t n : Nat) : Rat := deficitFrom t n 1

theorem scaled_deficit (t n : Nat) (p : Rat) :
    deficitFrom t n p = p * deficit t n + (1 - p) * (liveTime t n : Rat) := by
  induction t generalizing n p with
  | zero => simp [deficitFrom, deficit, liveTime]; grind
  | succ t ih =>
    by_cases hn : n = 1
    · simp [deficitFrom, deficit, liveTime, hn]; grind
    · have hp := ih (ordinary n) (p * factor n)
      have h1 := ih (ordinary n) (factor n)
      simp only [deficit, deficitFrom, liveTime, if_neg hn, Rat.natCast_add] at *
      grind

theorem ordinary_even (n : Nat) : ordinary (2 * n) = n := by
  have h : (2 * n) % 2 = 0 := by omega
  simp [ordinary, h]

theorem factor_even (n : Nat) : factor (2 * n) = 1 := by
  have h : (2 * n) % 2 = 0 := by omega
  simp [factor, h]

theorem ordinary_odd (n : Nat) : ordinary (2 * n + 1) = 2 * (3 * n + 2) := by
  have h : (2 * n + 1) % 2 ≠ 0 := by omega
  simp only [ordinary, if_neg h]
  omega

theorem even_transport (t n : Nat) : deficit (t + 1) (2 * n) = deficit t n := by
  have h : 2 * n ≠ 1 := by omega
  simp [deficit, deficitFrom, h, ordinary_even, factor_even]
  grind

theorem odd_transport (t n : Nat) (hn : 0 < n) :
    deficit (t + 2) (2 * n + 1) =
      factor (2 * n + 1) * deficit t (3 * n + 2) +
        (1 - factor (2 * n + 1)) * (1 + (liveTime t (3 * n + 2) : Rat)) := by
  have h1 : 2 * n + 1 ≠ 1 := by omega
  have h2 : 2 * (3 * n + 2) ≠ 1 := by omega
  have hs := scaled_deficit t (3 * n + 2) (factor (2 * n + 1))
  simp only [deficit, deficitFrom, if_neg h1, ordinary_odd, if_neg h2,
    ordinary_even, factor_even, Rat.one_mul, Rat.mul_one] at *
  grind

theorem odd_loss_identity (n : Nat) :
    (2 * ((3 * n + 2 : Nat) : Rat)) * (1 - factor (2 * n + 1)) = 1 := by
  have h : (2 * n + 1) % 2 ≠ 0 := by omega
  have hp : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hd : 3 * ((2 * n + 1 : Nat) : Rat) + 1 ≠ 0 := by
    simp only [Rat.natCast_add, Rat.natCast_mul]
    grind
  have hc := Rat.div_mul_cancel (a := 3 * ((2 * n + 1 : Nat) : Rat)) hd
  simp only [factor, if_neg h, Rat.natCast_add, Rat.natCast_mul] at *
  grind

def correction (t n : Nat) : Rat :=
  (1 + (liveTime t n : Rat) - deficit t n) / (2 * (n : Rat))

theorem odd_correction_identity (t n : Nat) (hn : 0 < n) :
    deficit (t + 2) (2 * n + 1) = deficit t (3 * n + 2) + correction t (3 * n + 2) := by
  have ht := odd_transport t n hn
  have hl := odd_loss_identity n
  have hp : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hd : 2 * ((3 * n + 2 : Nat) : Rat) ≠ 0 := by
    simp only [Rat.natCast_add, Rat.natCast_mul]
    grind
  have hc := Rat.div_mul_cancel
    (a := 1 + (liveTime t (3 * n + 2) : Rat) - deficit t (3 * n + 2)) hd
  simp only [correction]
  grind

theorem factor_bounds (n : Nat) : 0 ≤ factor n ∧ factor n ≤ 1 := by
  by_cases h : n % 2 = 0
  · simp [factor, h]; decide
  · have hp : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
    have hd : 0 < 3 * (n : Rat) + 1 := by grind
    have hc := Rat.div_mul_cancel (a := 3 * (n : Rat)) (show 3 * (n : Rat) + 1 ≠ 0 by grind)
    have hlo := Rat.le_of_mul_le_mul_right
      (show (0 : Rat) * (3 * (n : Rat) + 1) ≤
        (3 * (n : Rat) / (3 * (n : Rat) + 1)) * (3 * (n : Rat) + 1) by grind) hd
    have hhi := Rat.le_of_mul_le_mul_right
      (show (3 * (n : Rat) / (3 * (n : Rat) + 1)) * (3 * (n : Rat) + 1) ≤
        1 * (3 * (n : Rat) + 1) by grind) hd
    simp only [factor, if_neg h]
    exact ⟨hlo, hhi⟩

theorem liveTime_le (t n : Nat) : liveTime t n ≤ t := by
  induction t generalizing n with
  | zero => simp [liveTime]
  | succ t ih =>
    have h := ih (ordinary n)
    simp only [liveTime]
    split <;> omega

theorem deficit_bounds (t n : Nat) (p : Rat) (hp : 0 ≤ p ∧ p ≤ 1) :
    0 ≤ deficitFrom t n p ∧ deficitFrom t n p ≤ (liveTime t n : Rat) := by
  induction t generalizing n p with
  | zero => simp [deficitFrom, liveTime]
  | succ t ih =>
    by_cases hn : n = 1
    · simp [deficitFrom, liveTime, hn]
    · have hr := factor_bounds n
      have hlo := Rat.mul_nonneg hp.1 hr.1
      have hhi := Rat.mul_le_mul_of_nonneg_right hp.2 hr.1
      have ht := ih (ordinary n) (p * factor n) ⟨hlo, by grind⟩
      simp only [deficitFrom, liveTime, if_neg hn, Rat.natCast_add]
      grind

theorem correction_bounds (t n : Nat) :
    1 ≤ (2 * ((3 * n + 2 : Nat) : Rat)) * correction t (3 * n + 2) ∧
      (2 * ((3 * n + 2 : Nat) : Rat)) * correction t (3 * n + 2) ≤ (t : Rat) + 1 := by
  have hb := deficit_bounds t (3 * n + 2) 1 (by decide)
  have ht := Rat.natCast_le_natCast.mpr (liveTime_le t (3 * n + 2))
  have hp : (0 : Rat) ≤ (n : Rat) := Rat.natCast_nonneg
  have hd : 2 * ((3 * n + 2 : Nat) : Rat) ≠ 0 := by
    simp only [Rat.natCast_add, Rat.natCast_mul]
    grind
  have hc := Rat.div_mul_cancel
    (a := 1 + (liveTime t (3 * n + 2) : Rat) - deficit t (3 * n + 2)) hd
  simp only [deficit] at *
  simp only [correction, deficit]
  grind

def sumPos : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | x + 1, f => sumPos x f + f (x + 1)

theorem parity_split (x : Nat) (f : Nat → Rat) (hf : f 1 = 0) :
    sumPos (2 * x + 1) f = sumPos x (fun n => f (2 * n)) + sumPos x (fun n => f (2 * n + 1)) := by
  induction x with
  | zero => simp [sumPos, hf]
  | succ x ih =>
    have hx : 2 * (x + 1) + 1 = (2 * x + 1) + 1 + 1 := by omega
    rw [hx, sumPos, sumPos, ih]
    simp only [sumPos]
    have h1 : 2 * x + 1 + 1 = 2 * (x + 1) := by omega
    rw [h1]
    grind

theorem population_transport (t x : Nat) :
    sumPos (2 * x + 1) (deficit (t + 2)) =
      sumPos x (deficit (t + 1)) + sumPos x (fun n => deficit t (3 * n + 2)) +
        sumPos x (fun n => correction t (3 * n + 2)) := by
  have hs := parity_split x (deficit (t + 2)) (by simp [deficit, deficitFrom])
  rw [hs]
  clear hs
  induction x with
  | zero => simp [sumPos]; grind
  | succ x ih =>
    simp only [sumPos, even_transport, odd_correction_identity t (x + 1) (by omega)] at *
    grind

#print axioms scaled_deficit
#print axioms even_transport
#print axioms odd_transport
#print axioms odd_loss_identity
#print axioms odd_correction_identity
#print axioms deficit_bounds
#print axioms correction_bounds
#print axioms population_transport

end CensoredProgressionTransport
