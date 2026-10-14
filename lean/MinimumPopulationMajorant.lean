/- Exact all-population bounds for actual Collatz prefix and global minima.
   A full-period affine-correction mean improves the previous written bound.
   The resulting majorant is sublinear but does not prove Collatz. -/
import MinimumClockBarrier
import BinaryImageEnergy

namespace MinimumPopulationMajorant
open CollatzAffine CoalescenceTail MinimumTailRigidity MinimumCapTransport
open MinimumClockBarrier MinimumLinearBoundary MinimumGreenKernel

def wordWeight (k n : Nat) : Nat := 85 ^ (k - wt k n) * 147 ^ wt k n

theorem word_weight_positive (k n : Nat) : 0 < wordWeight k n :=
  Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))

theorem word_weight_lift (k q n : Nat) :
    wordWeight k (2 ^ k * q + n) = wordWeight k n := by
  simp only [wordWeight, weight_lift]

theorem word_weight_snoc (k n : Nat) :
    wordWeight (k + 1) n =
      (if orbit k n % 2 = 1 then 147 else 85) * wordWeight k n := by
  have hw := weight_le_length k n
  by_cases hp : orbit k n % 2 = 1
  · have he : k + 1 - (wt k n + 1) = k - wt k n := by omega
    simp only [wordWeight, weight_snoc, hp, if_pos, he, Nat.pow_succ]
    grind
  · have he : orbit k n % 2 = 0 := by omega
    have hk : k + 1 - wt k n = (k - wt k n) + 1 := by omega
    simp only [wordWeight, weight_snoc, he, if_neg (by decide : ¬ (0 : Nat) = 1),
      Nat.add_zero, hk, Nat.pow_succ]
    grind

theorem word_weight_children (k n : Nat) :
    wordWeight (k + 1) n + wordWeight (k + 1) (2 ^ k + n) =
      232 * wordWeight k n := by
  have hl := word_weight_lift k 1 n
  simp only [Nat.mul_one] at hl
  rw [word_weight_snoc, word_weight_snoc, hl, endpoint_parity_flip]
  have hp : orbit k n % 2 = 0 ∨ orbit k n % 2 = 1 := by omega
  rcases hp with hp | hp <;> simp [hp] <;> omega

theorem word_weight_mass (k : Nat) :
    total (2 ^ k) (wordWeight k) = 232 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    have he := total_ext (2 ^ k)
      (fun r => wordWeight (k + 1) r + wordWeight (k + 1) (2 ^ k + r))
      (fun r => 232 * wordWeight k r) (fun r _ => word_weight_children k r)
    rw [he, total_mul, ih, Nat.pow_succ]
    omega

theorem word_weight_square (k n : Nat) :
    3 ^ wt k n * 120 ^ (2 * k) ≤ 2 ^ k * (wordWeight k n) ^ 2 := by
  induction k with
  | zero => simp [wordWeight, wt]
  | succ k ih =>
    have hp : 3 ^ (orbit k n % 2) * 120 ^ 2 ≤
        2 * (if orbit k n % 2 = 1 then 147 else 85) ^ 2 := by
      have he : orbit k n % 2 = 0 ∨ orbit k n % 2 = 1 := by omega
      rcases he with he | he <;> rw [he] <;> decide
    have hm := Nat.mul_le_mul ih hp
    rw [weight_snoc, Nat.pow_add, show 2 * (k + 1) = 2 * k + 2 by omega,
      Nat.pow_add, Nat.pow_succ 2, word_weight_snoc]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at hm ⊢
    grind

theorem square_to_minimum (m q a w b n z : Nat) (hq : 0 < q)
    (hz : z ≤ n) (he : m * z ≤ a * n + b) (hs : a * q * q ≤ m * w * w) :
    m * q * z ≤ m * n * w + q * b := by
  by_cases hw : q ≤ w
  · have h1 := Nat.mul_le_mul_left (m * q) hz
    have h2 := Nat.mul_le_mul_left (m * n) hw
    grind
  · have h1 := Nat.mul_le_mul_left (m * w) (show w ≤ q by omega)
    have h2 := Nat.le_trans hs h1
    have ha := Nat.le_of_mul_le_mul_right h2 hq
    have h3 := Nat.mul_le_mul_right n ha
    have h4 := Nat.mul_le_mul_left q he
    grind

theorem shortcut_orbit_eq (k n : Nat) : OrdinaryCollatz.shortcutIter k n = orbit k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => exact ih (U n)

theorem prefix_le_shortcut (k t n : Nat) (ht : 2 * k ≤ t) :
    prefixMinimum t n ≤ orbit k n := by
  obtain ⟨j, _, hj, he⟩ := OrdinaryCollatz.shortcut_iteration_simulation k n
  rw [shortcut_orbit_eq] at he
  have hm := prefix_clock_mono (show j ≤ t by omega) n
  have hu := prefix_le_endpoint j n
  omega

theorem prefix_word_majorant (k t n : Nat) (ht : 2 * k ≤ t) :
    2 ^ k * 120 ^ k * prefixMinimum t n ≤
      2 ^ k * n * wordWeight k n + 120 ^ k * numerator k n := by
  have he := orbit_equation k n
  have hl := Nat.mul_le_mul_left (2 ^ k) (prefix_le_shortcut k t n ht)
  have hs := word_weight_square k n
  have hq : 120 ^ (2 * k) = 120 ^ k * 120 ^ k := by
    rw [show 2 * k = k + k by omega, Nat.pow_add]
  rw [hq] at hs
  simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] at hs
  apply square_to_minimum (2 ^ k) (120 ^ k) (3 ^ wt k n) (wordWeight k n)
    (numerator k n) n (prefixMinimum t n) (Nat.pow_pos (by decide))
    (prefix_le_source t n) (by omega)
  grind

theorem sum_pos_total (f : Nat → Nat) (n : Nat) :
    MinimumTailRigidity.sumPos f n = total n (fun r => f (r + 1)) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [MinimumTailRigidity.sumPos, total, ih]

theorem total_shift (f : Nat → Nat) (n : Nat) :
    total n (fun r => f (r + 1)) + f 0 = total n f + f n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total]; omega

theorem periodic_positive_mass (m : Nat) (f : Nat → Nat)
    (hf : ∀ n, f (m + n) = f n) :
    MinimumTailRigidity.sumPos f m = total m f ∧
    MinimumTailRigidity.sumPos f (2 * m) = 2 * total m f := by
  have hs := total_shift f m
  have h0 := hf 0
  simp only [Nat.add_zero] at h0
  have hfirst : MinimumTailRigidity.sumPos f m = total m f := by
    rw [sum_pos_total]
    omega
  refine ⟨hfirst, ?_⟩
  rw [sum_pos_total, show 2 * m = m + m by omega, total_add]
  have he := total_ext m (fun r => f (m + r + 1)) (fun r => f (r + 1))
    (by intro r _; rw [Nat.add_assoc, hf])
  rw [he, ← sum_pos_total, hfirst]
  omega

theorem two_period_weight_bound (k n : Nat) (hn : n ≤ 2 ^ (k + 1)) :
    MinimumTailRigidity.sumPos (wordWeight k) n ≤ 2 * 232 ^ k := by
  have hp := periodic_positive_mass (2 ^ k) (wordWeight k)
    (by intro n; simpa only [Nat.mul_one] using word_weight_lift k 1 n)
  have ht := sum_length_mono (wordWeight k) hn
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ]; omega, hp.2,
    word_weight_mass] at ht
  exact ht

theorem two_period_numerator_bound (k n : Nat) (hn : n ≤ 2 ^ (k + 1)) :
    2 * MinimumTailRigidity.sumPos (numerator k) n ≤ k * (2 ^ k) * (2 ^ k) := by
  have hp := periodic_positive_mass (2 ^ k) (numerator k)
    (by intro n; simpa only [Nat.mul_one] using ReturnCorrectionMoments.numerator_lift k 1 n)
  have ht := sum_length_mono (numerator k) hn
  rw [show 2 ^ (k + 1) = 2 * 2 ^ k by rw [Nat.pow_succ]; omega, hp.2] at ht
  have hm := BinaryImageEnergy.numerator_mass k
  rw [ReturnCorrectionMoments.four_pow] at hm
  grind

theorem prefix_sum_word (h k t n : Nat) (ht : 2 * k ≤ t) :
    2 ^ k * 120 ^ k * tailSum (prefixMinimum t) h n ≤
      2 ^ k * n * MinimumTailRigidity.sumPos (wordWeight k) n +
        120 ^ k * MinimumTailRigidity.sumPos (numerator k) n := by
  induction n with
  | zero => simp [tailSum, MinimumTailRigidity.sumPos]
  | succ n ih =>
    have hv : tailTerm (prefixMinimum t) h (n + 1) ≤ prefixMinimum t (n + 1) := by
      simp only [tailTerm]
      split <;> omega
    have hs := Nat.le_trans (Nat.mul_le_mul_left (2 ^ k * 120 ^ k) hv)
      (prefix_word_majorant k t (n + 1) ht)
    have hg := Nat.mul_le_mul_right (MinimumTailRigidity.sumPos (wordWeight k) n)
      (Nat.mul_le_mul_left (2 ^ k) (show n ≤ n + 1 by omega))
    simp only [tailSum, MinimumTailRigidity.sumPos] at ih ⊢
    grind

theorem prefix_population_integer (h k t n : Nat) (ht : 2 * k ≤ t)
    (hn : n ≤ 2 ^ (k + 1)) :
    2 * 120 ^ k * tailSum (prefixMinimum t) h n ≤
      4 * n * 232 ^ k + 120 ^ k * k * 2 ^ k := by
  have hsum := Nat.mul_le_mul_left 2 (prefix_sum_word h k t n ht)
  have hw := Nat.mul_le_mul_left (2 * 2 ^ k * n) (two_period_weight_bound k n hn)
  have hb := Nat.mul_le_mul_left (120 ^ k) (two_period_numerator_bound k n hn)
  have he : 2 ^ k * (2 * 120 ^ k * tailSum (prefixMinimum t) h n) ≤
      2 ^ k * (4 * n * 232 ^ k + 120 ^ k * k * 2 ^ k) := by grind
  exact Nat.le_of_mul_le_mul_left he (Nat.two_pow_pos k)

theorem dyadic_population_integer (h k t : Nat) (ht : 2 * k ≤ t) :
    4 * 120 ^ k * tailSum (prefixMinimum t) h (2 ^ k) ≤
      4 * 2 ^ k * 232 ^ k + 120 ^ k * k * 2 ^ k := by
  have hw := (periodic_positive_mass (2 ^ k) (wordWeight k)
    (by intro n; simpa only [Nat.mul_one] using word_weight_lift k 1 n)).1
  rw [word_weight_mass] at hw
  have hb := (periodic_positive_mass (2 ^ k) (numerator k)
    (by intro n; simpa only [Nat.mul_one] using ReturnCorrectionMoments.numerator_lift k 1 n)).1
  have hn := BinaryImageEnergy.numerator_mass k
  rw [← hb, ReturnCorrectionMoments.four_pow] at hn
  have hsum := Nat.mul_le_mul_left 4 (prefix_sum_word h k t (2 ^ k) ht)
  rw [hw] at hsum
  have he : 2 ^ k * (4 * 120 ^ k * tailSum (prefixMinimum t) h (2 ^ k)) ≤
      2 ^ k * (4 * 2 ^ k * 232 ^ k + 120 ^ k * k * 2 ^ k) := by
    calc
      _ = 4 * (2 ^ k * 120 ^ k * tailSum (prefixMinimum t) h (2 ^ k)) := by ac_rfl
      _ ≤ 4 * (2 ^ k * 2 ^ k * 232 ^ k +
          120 ^ k * MinimumTailRigidity.sumPos (numerator k) (2 ^ k)) := hsum
      _ = _ := by
        rw [Nat.mul_add, show 4 * (120 ^ k * MinimumTailRigidity.sumPos (numerator k) (2 ^ k)) =
          120 ^ k * (4 * MinimumTailRigidity.sumPos (numerator k) (2 ^ k)) by ac_rfl, hn]
        simp only [Nat.mul_add]
        congr 1 <;> ac_rfl
  exact Nat.le_of_mul_le_mul_left he (Nat.two_pow_pos k)

def rate : Rat := 29 / 15

theorem scale_rate_identity (k : Nat) :
    (120 ^ k : Nat) * rate ^ k = (232 ^ k : Nat) := by
  induction k with
  | zero => simp only [Nat.pow_zero, Rat.pow_zero]; grind
  | succ k ih =>
    simp only [Nat.pow_succ, Rat.pow_succ, Rat.natCast_mul]
    unfold rate at *
    grind

theorem rate_dyadic_identity (k : Nat) :
    rate ^ k = q ^ k * (2 ^ k : Nat) := by
  induction k with
  | zero => simp only [Rat.pow_zero, Nat.pow_zero]; grind
  | succ k ih =>
    simp only [Nat.pow_succ, Rat.pow_succ, Rat.natCast_mul, ih]
    unfold rate q
    grind

theorem linear_correction_bound (k : Nat) : (k + 2) * 120 ^ k ≤ 2 * 232 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hc : 120 * (k + 3) ≤ 232 * (k + 2) := by omega
    have hm := Nat.mul_le_mul_right (120 ^ k) hc
    have hs := Nat.mul_le_mul_left 232 ih
    simp only [Nat.pow_succ]
    grind

theorem correction_absorbed (k : Nat) : (k : Rat) / 2 + 1 ≤ rate ^ k := by
  have hi := Rat.natCast_le_natCast.mpr (linear_correction_bound k)
  simp only [Rat.natCast_mul, Rat.natCast_add] at hi
  have he := scale_rate_identity k
  have hp : (0 : Rat) < (120 ^ k : Nat) := Rat.natCast_lt_natCast.mpr (Nat.pow_pos (by decide))
  apply Rat.le_of_mul_le_mul_right (c := ((120 ^ k : Nat) : Rat)) _ hp
  grind

theorem scaled_mean_bound (s n q p k d c : Nat) (hn : 0 < n) (hq : 0 < q) (hd : 0 < d)
    (hb : d * q * s ≤ n * (d * c * p + q * k)) (r : Rat)
    (he : (q : Rat) * r = (p : Rat)) :
    (s : Rat) / n ≤ (c : Rat) * r + (k : Rat) / d := by
  have hc := Rat.natCast_le_natCast.mpr hb
  simp only [Rat.natCast_mul, Rat.natCast_add] at hc
  have hn' : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn
  have hq' : (0 : Rat) < (q : Rat) := Rat.natCast_lt_natCast.mpr hq
  have hd' : (0 : Rat) < (d : Rat) := Rat.natCast_lt_natCast.mpr hd
  have hs := Rat.div_mul_cancel (a := (s : Rat)) (show (n : Rat) ≠ 0 by grind)
  have hk := Rat.div_mul_cancel (a := (k : Rat)) (show (d : Rat) ≠ 0 by grind)
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hn'
  apply Rat.le_of_mul_le_mul_right (c := (q : Rat)) _ hq'
  apply Rat.le_of_mul_le_mul_right (c := (d : Rat)) _ hd'
  have hr : ((c : Rat) * r + (k : Rat) / d) * n * q * d =
      (n : Rat) * ((d : Rat) * c * p + (q : Rat) * k) := by
    calc
      _ = ((c : Rat) * n * d) * ((q : Rat) * r) +
          ((n : Rat) * q) * (((k : Rat) / d) * d) := by
        rw [Rat.add_mul, Rat.add_mul, Rat.add_mul]
        congr 1 <;> grind only
      _ = _ := by
        rw [he, hk, Rat.mul_add]
        congr 1 <;> grind only
  rw [hs, hr]
  calc
    (s : Rat) * q * d = (d : Rat) * q * s := by grind only
    _ ≤ _ := hc

theorem prefix_population_bound (h k t n : Nat) (ht : 2 * k ≤ t)
    (hl : 2 ^ k ≤ n) (hu : n ≤ 2 ^ (k + 1)) :
    tailMean h t n ≤ 2 * rate ^ k + (k : Rat) / 2 := by
  have hi := prefix_population_integer h k t n ht hu
  have hk := Nat.mul_le_mul_left (120 ^ k * k) hl
  have hall : 2 * 120 ^ k * tailSum (prefixMinimum t) h n ≤
      4 * n * 232 ^ k + 120 ^ k * k * n := by omega
  have hnp := Nat.two_pow_pos k
  apply scaled_mean_bound (tailSum (prefixMinimum t) h n) n (120 ^ k) (232 ^ k) k 2 2
    (by omega) (Nat.pow_pos (by decide)) (by decide) _ (rate ^ k) (scale_rate_identity k)
  have he : 4 * n * 232 ^ k + 120 ^ k * k * n = n * (2 * 2 * 232 ^ k + 120 ^ k * k) := by
    grind
  rwa [← he]

theorem dyadic_population_bound (h k t : Nat) (ht : 2 * k ≤ t) :
    tailMean h t (2 ^ k) ≤ rate ^ k + (k : Rat) / 4 := by
  have hb := dyadic_population_integer h k t ht
  have he : 4 * 2 ^ k * 232 ^ k + 120 ^ k * k * 2 ^ k =
      2 ^ k * (4 * 1 * 232 ^ k + 120 ^ k * k) := by grind
  rw [he] at hb
  have hm := scaled_mean_bound (tailSum (prefixMinimum t) h (2 ^ k)) (2 ^ k)
    (120 ^ k) (232 ^ k) k 4 1 (Nat.two_pow_pos k) (Nat.pow_pos (by decide))
    (by decide) hb (rate ^ k) (scale_rate_identity k)
  simpa only [Rat.natCast_ofNat, Rat.one_mul, tailMean] using hm

theorem gauge_rate_lower (n : Nat) (hn : 0 < n) : rate ^ n.log2 ≤ gauge n := by
  have hl := Nat.log2_self_le (by omega : n ≠ 0)
  have hc := Rat.natCast_le_natCast.mpr hl
  have hq := Rat.pow_nonneg (n := n.log2) (Rat.le_of_lt constants.1)
  have hm := Rat.mul_le_mul_of_nonneg_left hc hq
  rw [rate_dyadic_identity]
  simp only [gauge, if_neg (by omega : n ≠ 0), cell]
  grind

theorem prefix_mean_majorant (h t n : Nat) (ht : 2 * n.log2 ≤ t) :
    tailMean h t n ≤ 3 * gauge n := by
  by_cases hn : n = 0
  · subst n
    rw [tail_mean_below_floor h t 0 (Nat.zero_le _)]
    have hg := gauge_nonnegative 0
    grind
  · have hl := Nat.log2_self_le hn
    have hu := Nat.lt_log2_self (n := n)
    have hb := prefix_population_bound h n.log2 t n ht hl (by omega)
    have hg := gauge_rate_lower n (by omega)
    have hc := correction_absorbed n.log2
    grind

theorem global_le_prefix_mean (h t n : Nat) : globalMean h n ≤ tailMean h t n := by
  by_cases hn : n = 0
  · subst n
    rw [global_mean_below_floor h 0 (Nat.zero_le _), tail_mean_below_floor h t 0 (Nat.zero_le _)]
    exact Rat.le_refl
  · have hl := MinimumTailRigidity.sum_mono (tailTerm minimum h)
      (tailTerm (prefixMinimum t) h) n
      (fun i _ _ => tail_term_mono _ _ h i (minimum_le_prefix t i))
    have hc := Rat.natCast_le_natCast.mpr hl
    change (tailSum minimum h n : Rat) ≤ (tailSum (prefixMinimum t) h n : Rat) at hc
    have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr (show 0 < n by omega)
    have hd1 := Rat.div_mul_cancel (a := (tailSum minimum h n : Rat)) (show (n : Rat) ≠ 0 by grind)
    have hd2 := Rat.div_mul_cancel (a := (tailSum (prefixMinimum t) h n : Rat)) (show (n : Rat) ≠ 0 by grind)
    apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hp
    simp only [globalMean, tailMean]
    grind

theorem global_mean_majorant (h n : Nat) :
    0 ≤ globalMean h n ∧ globalMean h n ≤ 3 * gauge n := by
  refine ⟨global_mean_nonnegative h n, ?_⟩
  exact Rat.le_trans (global_le_prefix_mean h (2 * n.log2) n)
    (prefix_mean_majorant h (2 * n.log2) n (Nat.le_refl _))

theorem global_population_bound (h n : Nat) (hn : 0 < n) :
    globalMean h n ≤ 2 * rate ^ n.log2 + (n.log2 : Rat) / 2 := by
  have hl := Nat.log2_self_le (by omega : n ≠ 0)
  have hu := Nat.lt_log2_self (n := n)
  exact Rat.le_trans (global_le_prefix_mean h (2 * n.log2) n)
    (prefix_population_bound h n.log2 (2 * n.log2) n (Nat.le_refl _) hl (by omega))

theorem global_dyadic_bound (h k : Nat) :
    globalMean h (2 ^ k) ≤ rate ^ k + (k : Rat) / 4 :=
  Rat.le_trans (global_le_prefix_mean h (2 * k) (2 ^ k))
    (dyadic_population_bound h k (2 * k) (Nat.le_refl _))

theorem adaptive_mean_majorant (h l n : Nat) : adaptiveMean h l n ≤ 3 * gauge n := by
  apply prefix_mean_majorant h (adaptiveClock l n) n
  simp only [adaptiveClock]
  omega

theorem adaptive_occupation_lower (h l j depth : Nat) (hh : 1 ≤ h) (hj : 0 < j)
    (hfloor : h < 2 ^ (4 * j + 2 * l) - 1) :
    (2 ^ j : Nat) / (2 : Rat) - 3 * rho ^ depth * gauge (2 ^ (5 * j + 2 * l)) ≤
      CutoffDescent.occupation h depth (localResidual (adaptiveMean h l)) (2 ^ (5 * j + 2 * l)) :=
  adaptive_residual_lower h l j depth hh hj hfloor (adaptive_mean_majorant h l)

theorem actual_residual_truncation (h k n : Nat) (hh : 1 ≤ h) :
    0 ≤ globalMean h n - CutoffDescent.occupation h k (localResidual (globalMean h)) n ∧
    globalMean h n - CutoffDescent.occupation h k (localResidual (globalMean h)) n ≤
      3 * rho ^ k * gauge n :=
  residual_truncation_bound h k hh (globalMean h) (global_mean_majorant h)
    (global_mean_below_floor h) n

theorem actual_absolute_tail (h j k n : Nat) (hh : 1 ≤ h) :
    0 ≤ CutoffDescent.occupation h (j + k)
        (fun m => magnitude (localResidual (globalMean h) m)) n -
      CutoffDescent.occupation h j (fun m => magnitude (localResidual (globalMean h) m)) n ∧
    CutoffDescent.occupation h (j + k)
        (fun m => magnitude (localResidual (globalMean h) m)) n -
      CutoffDescent.occupation h j (fun m => magnitude (localResidual (globalMean h) m)) n ≤
      (5133 / 7) * rho ^ j * gauge n :=
  absolute_tail_bound h j k hh (globalMean h) (global_mean_majorant h) n

theorem actual_least_residual_diagnostic {a : Nat} (ha : OrdinaryCollatz.LeastCounterexample a)
    (k : Nat) (eta : Rat) (heta : 0 ≤ eta)
    (hr : ∀ n, a - 1 < n → localResidual (globalMean (a - 1)) n ≤ eta * gauge n) :
    1 ≤ (3 * rho ^ k + eta * geometric k) * gauge a :=
  least_counterexample_residual_diagnostic ha k eta heta
    (fun n => (global_mean_majorant (a - 1) n).2) hr

#print axioms word_weight_positive
#print axioms word_weight_lift
#print axioms word_weight_snoc
#print axioms word_weight_children
#print axioms word_weight_mass
#print axioms word_weight_square
#print axioms square_to_minimum
#print axioms shortcut_orbit_eq
#print axioms prefix_le_shortcut
#print axioms prefix_word_majorant
#print axioms sum_pos_total
#print axioms total_shift
#print axioms periodic_positive_mass
#print axioms two_period_weight_bound
#print axioms two_period_numerator_bound
#print axioms prefix_sum_word
#print axioms prefix_population_integer
#print axioms dyadic_population_integer
#print axioms scale_rate_identity
#print axioms rate_dyadic_identity
#print axioms linear_correction_bound
#print axioms correction_absorbed
#print axioms scaled_mean_bound
#print axioms prefix_population_bound
#print axioms dyadic_population_bound
#print axioms gauge_rate_lower
#print axioms prefix_mean_majorant
#print axioms global_le_prefix_mean
#print axioms global_mean_majorant
#print axioms global_population_bound
#print axioms global_dyadic_bound
#print axioms adaptive_mean_majorant
#print axioms adaptive_occupation_lower
#print axioms actual_residual_truncation
#print axioms actual_absolute_tail
#print axioms actual_least_residual_diagnostic

end MinimumPopulationMajorant
