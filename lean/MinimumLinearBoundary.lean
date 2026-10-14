/- The fair source-cutoff chain has a small occupation time but retains a
   large linear terminal contribution. This is an auxiliary averaging chain,
   not an individual Collatz orbit. No uniform Collatz tail bound is proved. -/
import MinimumCapTransport
import CutoffDescent

namespace MinimumLinearBoundary
open MinimumTailRigidity MinimumCapTransport CutoffDescent

def bits (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

theorem bits_le_iff (n k : Nat) : bits n ≤ k ↔ n < 2 ^ k := by
  by_cases hn : n = 0
  · subst n
    change 0 ≤ k ↔ 0 < 2 ^ k
    have hp := Nat.two_pow_pos k
    omega
  · simp only [bits, if_neg hn]
    have he := Nat.log2_lt (n := n) (k := k) hn
    omega

theorem below_bits_power (n : Nat) : n < 2 ^ bits n :=
  (bits_le_iff n (bits n)).mp (Nat.le_refl _)

theorem bits_mono {n m : Nat} (hnm : n ≤ m) : bits n ≤ bits m :=
  (bits_le_iff n (bits m)).mpr (Nat.lt_of_le_of_lt hnm (below_bits_power m))

theorem bits_lower (n : Nat) (hn : 0 < n) : bits (lower n) + 1 = bits n := by
  by_cases h1 : n = 1
  · subst n; decide
  · have hn2 : 2 ≤ n := by omega
    have hl : n / 2 ≠ 0 := by omega
    have he := Nat.log2_def n
    simp only [if_pos hn2] at he
    simp only [lower]
    simp only [bits, if_neg (by omega : n ≠ 0), if_neg hl]
    omega

theorem bits_upper (n : Nat) (hn : 0 < n) : bits (upper n) ≤ bits n + 1 := by
  have hu : upper n ≤ 2 * n := by unfold upper; omega
  have hp := below_bits_power n
  apply (bits_le_iff _ _).mpr
  rw [Nat.pow_succ]
  omega

theorem cutoff_sum (n : Nat) (hn : 0 < n) :
    lower n + upper n + (if n % 2 = 0 then 1 else 0) = 2 * n := by
  unfold lower upper
  split <;> omega

theorem cutoff_positive (n : Nat) (hn : 2 ≤ n) : 0 < lower n ∧ 0 < upper n := by
  unfold lower upper
  omega

def branchSum : Nat → (Nat → Nat) → Nat → Nat
  | 0, f, n => f n
  | k + 1, f, n => branchSum k f (lower n) + branchSum k f (upper n)

theorem branch_sum_mono (k : Nat) (f : Nat → Nat)
    (hf : ∀ n m, n ≤ m → f n ≤ f m) {n m : Nat} (hnm : n ≤ m) :
    branchSum k f n ≤ branchSum k f m := by
  induction k generalizing n m with
  | zero => exact hf n m hnm
  | succ k ih =>
    have hl : lower n ≤ lower m := by unfold lower; omega
    have hu : upper n ≤ upper m := by unfold upper; omega
    have h1 := ih hl
    have h2 := ih hu
    simp only [branchSum]
    omega

theorem three_branch_endpoints (p : Nat) (hp : 0 < p) :
    branchSum 3 bits (8 * p - 1) = bits (p - 1) + 3 * bits (3 * p - 1) +
      3 * bits (9 * p - 1) + bits (27 * p - 1) := by
  simp only [branchSum, lower, upper]
  grind

theorem three_branch_dyadic_bound (k : Nat) :
    branchSum 3 bits (2 ^ (k + 3) - 1) ≤ 8 * k + 23 := by
  have hp := Nat.two_pow_pos k
  have he : 2 ^ (k + 3) = 8 * 2 ^ k := by
    rw [Nat.pow_add]
    omega
  rw [he, three_branch_endpoints (2 ^ k) hp]
  have h0 : bits (2 ^ k - 1) ≤ k := (bits_le_iff _ _).mpr (by omega)
  have h1 : bits (3 * 2 ^ k - 1) ≤ k + 2 := by
    apply (bits_le_iff _ _).mpr
    rw [Nat.pow_add]
    omega
  have h2 : bits (9 * 2 ^ k - 1) ≤ k + 4 := by
    apply (bits_le_iff _ _).mpr
    rw [Nat.pow_add]
    omega
  have h3 : bits (27 * 2 ^ k - 1) ≤ k + 5 := by
    apply (bits_le_iff _ _).mpr
    rw [Nat.pow_add]
    omega
  omega

theorem three_step_bits_drift (n : Nat) (hn : 4 ≤ n) :
    branchSum 3 bits n + 1 ≤ 8 * bits n := by
  have hl : 2 ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega)
  have hb : 3 ≤ bits n := by simp only [bits, if_neg (by omega : n ≠ 0)]; omega
  have hp := below_bits_power n
  have hm := branch_sum_mono 3 bits (fun _ _ h => bits_mono h)
    (show n ≤ 2 ^ bits n - 1 by omega)
  have he : bits n - 3 + 3 = bits n := by omega
  have ht := three_branch_dyadic_bound (bits n - 3)
  rw [he] at ht
  omega

def average (f : Nat → Rat) (n : Nat) : Rat := (f (lower n) + f (upper n)) / 2
def rank (n : Nat) : Rat := (bits n : Rat)
def potential (n : Nat) : Rat := rank n + average rank n + average (average rank) n
def parityLoss (n : Nat) : Rat := if n % 2 = 0 then 1 / 2 else 0

theorem average_rank_le (n : Nat) (hn : 0 < n) : average rank n ≤ rank n := by
  have hl := bits_lower n hn
  have hu := bits_upper n hn
  have hcast := Rat.natCast_le_natCast.mpr (show bits (lower n) + bits (upper n) ≤ 2 * bits n by omega)
  simp only [Rat.natCast_add, Rat.natCast_mul] at hcast
  unfold average rank
  grind

theorem potential_nonnegative (n : Nat) : 0 ≤ potential n := by
  have h0 := Rat.natCast_nonneg (a := bits n)
  have h1 := Rat.natCast_nonneg (a := bits (lower n))
  have h2 := Rat.natCast_nonneg (a := bits (upper n))
  have h3 := Rat.natCast_nonneg (a := bits (lower (lower n)))
  have h4 := Rat.natCast_nonneg (a := bits (upper (lower n)))
  have h5 := Rat.natCast_nonneg (a := bits (lower (upper n)))
  have h6 := Rat.natCast_nonneg (a := bits (upper (upper n)))
  unfold potential average rank
  grind

theorem potential_upper (n : Nat) (hn : 2 ≤ n) : potential n ≤ 3 * rank n := by
  have hp := cutoff_positive n hn
  have h0 := average_rank_le n (by omega)
  have h1 := average_rank_le (lower n) hp.1
  have h2 := average_rank_le (upper n) hp.2
  unfold potential average at *
  grind

theorem potential_drift (n : Nat) (hn : 4 ≤ n) :
    average potential n + 1 / 8 ≤ potential n := by
  have ht := Rat.natCast_le_natCast.mpr (three_step_bits_drift n hn)
  simp only [branchSum, Rat.natCast_add, Rat.natCast_mul] at ht
  unfold potential average rank
  grind

theorem size_drift (n : Nat) (hn : 0 < n) :
    average (fun n => (n : Rat)) n + parityLoss n = n := by
  have ht := cutoff_sum n hn
  by_cases he : n % 2 = 0
  · simp only [if_pos he] at ht
    have hc := congrArg (fun x : Nat => (x : Rat)) ht
    simp only [Rat.natCast_add, Rat.natCast_mul] at hc
    simp only [average, parityLoss, if_pos he]
    grind
  · simp only [if_neg he, Nat.add_zero] at ht
    have hc := congrArg (fun x : Nat => (x : Rat)) ht
    simp only [Rat.natCast_add, Rat.natCast_mul] at hc
    simp only [average, parityLoss, if_neg he]
    grind

def clockTerminal (h : Nat) : Nat → (Nat → Nat → Rat) → Nat → Nat → Rat
  | 0, f, t, n => f t n
  | k + 1, f, t, n => if n ≤ h ∨ t ≤ 1 then f t n else
      (clockTerminal h k f (t - 1) (lower n) +
       clockTerminal h k f (t - 2) (upper n)) / 2

def clockOccupation (h : Nat) : Nat → (Nat → Nat → Rat) → Nat → Nat → Rat
  | 0, _, _, _ => 0
  | k + 1, e, t, n => if n ≤ h ∨ t ≤ 1 then 0 else e t n +
      (clockOccupation h k e (t - 1) (lower n) +
       clockOccupation h k e (t - 2) (upper n)) / 2

def residual (f : Nat → Nat → Rat) (t n : Nat) : Rat :=
  f t n - (f (t - 1) (lower n) + f (t - 2) (upper n)) / 2

theorem clocked_exact_unroll (h k : Nat) (f : Nat → Nat → Rat) (t n : Nat) :
    clockTerminal h k f t n + clockOccupation h k (residual f) t n = f t n := by
  induction k generalizing t n with
  | zero => simp only [clockTerminal, clockOccupation]; grind
  | succ k ih =>
    by_cases hs : n ≤ h ∨ t ≤ 1
    · simp only [clockTerminal, clockOccupation, if_pos hs]; grind
    · have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      simp only [clockTerminal, clockOccupation, if_neg hs, residual]
      grind

theorem clock_terminal_nonnegative (h k : Nat) (f : Nat → Nat → Rat)
    (hf : ∀ t n, 0 ≤ f t n) (t n : Nat) : 0 ≤ clockTerminal h k f t n := by
  induction k generalizing t n with
  | zero => exact hf t n
  | succ k ih =>
    by_cases hs : n ≤ h ∨ t ≤ 1
    · simpa only [clockTerminal, if_pos hs] using hf t n
    · have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      simp only [clockTerminal, if_neg hs]
      grind

theorem duration_potential_budget (h k t n : Nat) (hh : 3 ≤ h) :
    clockOccupation h k (fun _ _ => 1) t n ≤ 8 *
      (potential n - clockTerminal h k (fun _ n => potential n) t n) := by
  induction k generalizing t n with
  | zero => simp only [clockTerminal, clockOccupation]; grind
  | succ k ih =>
    by_cases hs : n ≤ h ∨ t ≤ 1
    · simp only [clockTerminal, clockOccupation, if_pos hs]; grind
    · have hd := potential_drift n (by omega)
      have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      simp only [clockTerminal, clockOccupation, if_neg hs, average] at *
      grind

theorem duration_dyadic_bound (h k t n : Nat) (hh : 3 ≤ h) (hn : 2 ≤ n) :
    clockOccupation h k (fun _ _ => 1) t n ≤ 24 * rank n := by
  have hp := duration_potential_budget h k t n hh
  have hz := clock_terminal_nonnegative h k (fun _ n => potential n)
    (fun _ n => potential_nonnegative n) t n
  have hu := potential_upper n hn
  grind

theorem stopped_size_balance (h k t n : Nat) (hh : 1 ≤ h) (hn : 0 < n) :
    clockTerminal h k (fun _ n => (n : Rat)) t n +
      clockOccupation h k (fun _ n => parityLoss n) t n = n := by
  induction k generalizing t n with
  | zero => simp only [clockTerminal, clockOccupation]; grind
  | succ k ih =>
    by_cases hs : n ≤ h ∨ t ≤ 1
    · simp only [clockTerminal, clockOccupation, if_pos hs]; grind
    · have hp := cutoff_positive n (by omega)
      have hl := ih (t - 1) (lower n) hp.1
      have hu := ih (t - 2) (upper n) hp.2
      have hd := size_drift n hn
      simp only [clockTerminal, clockOccupation, if_neg hs, average] at *
      grind

theorem rounding_loss_le_duration (h k t n : Nat) :
    2 * clockOccupation h k (fun _ n => parityLoss n) t n ≤
      clockOccupation h k (fun _ _ => 1) t n := by
  induction k generalizing t n with
  | zero => simp only [clockOccupation]; grind
  | succ k ih =>
    by_cases hs : n ≤ h ∨ t ≤ 1
    · simp only [clockOccupation, if_pos hs]; grind
    · have hl := ih (t - 1) (lower n)
      have hu := ih (t - 2) (upper n)
      have hd : 2 * parityLoss n ≤ 1 := by unfold parityLoss; split <;> grind
      simp only [clockOccupation, if_neg hs]
      grind

theorem retained_size_lower (h k t n : Nat) (hh : 3 ≤ h) (hn : 2 ≤ n) :
    (n : Rat) - 12 * rank n ≤ clockTerminal h k (fun _ n => (n : Rat)) t n := by
  have hb := stopped_size_balance h k t n (by omega) (by omega)
  have hl := rounding_loss_le_duration h k t n
  have hd := duration_dyadic_bound h k t n hh hn
  grind

theorem short_boundary_lower (h k : Nat) (f : Nat → Nat → Rat)
    (hf : ∀ t n, 0 < n → 0 ≤ f t n)
    (hs : ∀ t n : Nat, t ≤ 1 → 0 < n → 3 * (n : Rat) / 8 - h ≤ f t n)
    (hh : 1 ≤ h) (t n : Nat) (ht : t ≤ k) (hn : 0 < n) :
    3 * clockTerminal h k (fun _ n => (n : Rat)) t n / 8 - h ≤
      clockTerminal h k f t n := by
  induction k generalizing t n with
  | zero =>
    simp only [clockTerminal]
    exact hs t n (by omega) hn
  | succ k ih =>
    by_cases hb : n ≤ h ∨ t ≤ 1
    · simp only [clockTerminal, if_pos hb]
      rcases hb with hnh | hts
      · have hcast := Rat.natCast_le_natCast.mpr hnh
        have hz := Rat.natCast_nonneg (a := h)
        have hp := hf t n hn
        grind
      · exact hs t n hts hn
    · have hp := cutoff_positive n (by omega)
      have hl := ih (t - 1) (lower n) (by omega) hp.1
      have hu := ih (t - 2) (upper n) (by omega) hp.2
      simp only [clockTerminal, if_neg hb]
      grind

theorem linear_boundary_lower (h k : Nat) (f : Nat → Nat → Rat)
    (hf : ∀ t n, 0 < n → 0 ≤ f t n)
    (hs : ∀ t n : Nat, t ≤ 1 → 0 < n → 3 * (n : Rat) / 8 - h ≤ f t n)
    (hh : 3 ≤ h) (t n : Nat) (ht : t ≤ k) (hn : 2 ≤ n) :
    3 * (n : Rat) / 8 - 9 * rank n / 2 - h ≤ clockTerminal h k f t n := by
  have hb := short_boundary_lower h k f hf hs (by omega) t n ht (by omega)
  have hz := retained_size_lower h k t n hh hn
  grind

theorem signed_cancellation_bound (h k : Nat) (f : Nat → Nat → Rat)
    (hf : ∀ t n, 0 < n → 0 ≤ f t n)
    (hs : ∀ t n : Nat, t ≤ 1 → 0 < n → 3 * (n : Rat) / 8 - h ≤ f t n)
    (hh : 3 ≤ h) (t n : Nat) (ht : t ≤ k) (hn : 2 ≤ n) :
    clockOccupation h k (residual f) t n ≤
      f t n - 3 * (n : Rat) / 8 + 9 * rank n / 2 + h := by
  have hb := linear_boundary_lower h k f hf hs hh t n ht hn
  have he := clocked_exact_unroll h k f t n
  grind

theorem one_step_odd_minimum (n : Nat) : prefixMinimum 1 (2 * n + 1) = 2 * n + 1 := by
  simp only [prefixMinimum, OrdinaryCollatz.C]
  split <;> omega

theorem one_step_even_sum (n : Nat) :
    2 * sumPos (prefixMinimum 1) (2 * n) = 3 * n * n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he := even_minimum_transport 0 (n + 1)
    have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hn] at he
    change prefixMinimum 1 (2 * n + 1 + 1) = n + 1 at he
    rw [hn, sumPos, sumPos, one_step_odd_minimum, he]
    grind

theorem one_step_odd_sum (n : Nat) :
    2 * sumPos (prefixMinimum 1) (2 * n + 1) = 3 * n * n + 5 * n + 2 := by
  have he := one_step_even_sum n
  simp only [sumPos, one_step_odd_minimum]
  grind

theorem one_step_sum_lower (n : Nat) :
    3 * n * n ≤ 8 * sumPos (prefixMinimum 1) n := by
  by_cases hn : n = 0
  · subst n; decide
  · rcases positive_parity n (by omega) with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · have he := one_step_even_sum (x + 1)
      grind
    · have ho := one_step_odd_sum x
      grind

theorem raw_sum_le_tail_plus_floor (h t n : Nat) :
    sumPos (prefixMinimum t) n ≤ tailSum (prefixMinimum t) h n + h * n := by
  induction n with
  | zero => simp only [sumPos, tailSum]; omega
  | succ n ih =>
    have hs : prefixMinimum t (n + 1) ≤ tailTerm (prefixMinimum t) h (n + 1) + h := by
      simp only [tailTerm]
      split <;> omega
    simp only [tailSum, sumPos] at *
    grind

theorem short_tail_sum_lower (h t n : Nat) (ht : t ≤ 1) :
    3 * n * n ≤ 8 * tailSum (prefixMinimum t) h n + 8 * h * n := by
  have h1 := one_step_sum_lower n
  have h2 := sum_mono (prefixMinimum 1) (prefixMinimum t) n
    (fun j _ _ => prefix_clock_mono ht j)
  have h3 := raw_sum_le_tail_plus_floor h t n
  have h4 := Nat.mul_le_mul_left 8 h2
  have h5 := Nat.mul_le_mul_left 8 h3
  grind

def tailMean (h t n : Nat) : Rat := (tailSum (prefixMinimum t) h n : Rat) / n

theorem tail_mean_nonnegative (h t n : Nat) (hn : 0 < n) : 0 ≤ tailMean h t n := by
  have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  have hz := Rat.natCast_nonneg (a := tailSum (prefixMinimum t) h n)
  have he := Rat.div_mul_cancel (a := (tailSum (prefixMinimum t) h n : Rat))
    (show (n : Rat) ≠ 0 by grind)
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hp
  unfold tailMean
  grind

theorem tail_mean_short_lower (h t n : Nat) (ht : t ≤ 1) (hn : 0 < n) :
    3 * (n : Rat) / 8 - h ≤ tailMean h t n := by
  have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  have hc := Rat.natCast_le_natCast.mpr (short_tail_sum_lower h t n ht)
  simp only [Rat.natCast_add, Rat.natCast_mul] at hc
  have he := Rat.div_mul_cancel (a := (tailSum (prefixMinimum t) h n : Rat))
    (show (n : Rat) ≠ 0 by grind)
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hp
  unfold tailMean
  grind

theorem tail_mean_below_floor (h t n : Nat) (hn : n ≤ h) : tailMean h t n = 0 := by
  have hz : tailSum (prefixMinimum t) h n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hl := prefix_le_source t (n + 1)
      have hi := ih (by omega)
      simp only [tailSum, sumPos] at hi ⊢
      simp only [hi, tailTerm, if_neg (by omega : ¬ h < prefixMinimum t (n + 1)), Nat.add_zero]
  simp only [tailMean, hz]
  change (0 : Rat) * (n : Rat)⁻¹ = 0
  exact Rat.zero_mul _

theorem actual_linear_boundary (h t n : Nat) (hh : 3 ≤ h) (hn : 2 ≤ n) :
    3 * (n : Rat) / 8 - 9 * rank n / 2 - h ≤
      clockTerminal h t (tailMean h) t n :=
  linear_boundary_lower h t (tailMean h) (tail_mean_nonnegative h)
    (tail_mean_short_lower h) hh t n (Nat.le_refl t) hn

theorem every_clock_boundary_256 (t : Nat) :
    (103 : Rat) / 2 ≤ clockTerminal 4 t (tailMean 4) t 256 := by
  have hb := actual_linear_boundary 4 t 256 (by decide) (by decide)
  have hr : bits 256 = 9 := by decide
  simp only [rank, hr] at hb
  grind

def checksFloorPath (h : Nat) : Nat → Nat → List Nat → Bool
  | _, n, [] => decide (n ≤ h)
  | 0, _, _ :: _ => false
  | t + 1, n, v :: vs => decide (OrdinaryCollatz.C n = v) && checksFloorPath h t v vs

def checksFloorRange (h t : Nat) : Nat → List (List Nat) → Bool
  | 0, [] => true
  | n + 1, path :: paths => checksFloorPath h t (n + 1) path && checksFloorRange h t n paths
  | _, _ => false

theorem checks_floor_path_sound (h t n : Nat) (path : List Nat)
    (hc : checksFloorPath h t n path = true) : prefixMinimum t n ≤ h := by
  induction t generalizing n path with
  | zero =>
    cases path with
    | nil => simpa only [checksFloorPath, decide_eq_true_eq, prefixMinimum] using hc
    | cons v vs => simp only [checksFloorPath, Bool.false_eq_true] at hc
  | succ t ih =>
    cases path with
    | nil =>
      have hn : n ≤ h := by simpa only [checksFloorPath, decide_eq_true_eq] using hc
      have hl := prefix_le_source (t + 1) n
      omega
    | cons v vs =>
      simp only [checksFloorPath, Bool.and_eq_true, decide_eq_true_eq] at hc
      have hl := ih v vs hc.2
      simp only [prefixMinimum, hc.1]
      omega

theorem checks_floor_range_sound (h t n : Nat) (paths : List (List Nat))
    (hc : checksFloorRange h t n paths = true) :
    tailSum (prefixMinimum t) h n = 0 := by
  induction n generalizing paths with
  | zero => rfl
  | succ n ih =>
    cases paths with
    | nil => simp only [checksFloorRange, Bool.false_eq_true] at hc
    | cons path paths =>
      simp only [checksFloorRange, Bool.and_eq_true] at hc
      have hl := checks_floor_path_sound h t (n + 1) path hc.1
      have hi := ih paths hc.2
      simp only [tailSum, sumPos] at hi ⊢
      simp only [hi, tailTerm, if_neg (by omega : ¬ h < prefixMinimum t (n + 1)), Nat.add_zero]

#print axioms three_step_bits_drift
#print axioms potential_nonnegative
#print axioms potential_upper
#print axioms potential_drift
#print axioms size_drift
#print axioms clocked_exact_unroll
#print axioms clock_terminal_nonnegative
#print axioms duration_potential_budget
#print axioms duration_dyadic_bound
#print axioms stopped_size_balance
#print axioms rounding_loss_le_duration
#print axioms retained_size_lower
#print axioms short_boundary_lower
#print axioms linear_boundary_lower
#print axioms signed_cancellation_bound
#print axioms one_step_even_sum
#print axioms one_step_odd_sum
#print axioms one_step_sum_lower
#print axioms raw_sum_le_tail_plus_floor
#print axioms short_tail_sum_lower
#print axioms tail_mean_nonnegative
#print axioms tail_mean_short_lower
#print axioms tail_mean_below_floor
#print axioms actual_linear_boundary
#print axioms every_clock_boundary_256
#print axioms checks_floor_path_sound
#print axioms checks_floor_range_sound

end MinimumLinearBoundary
