/- A rational sublinear gauge contracts under the fair cutoff average.
   Finite Green-kernel bounds are kernel checked; infinite expectation and
   the elementary Collatz population majorant are assembled in the note.
   No uniform subunit Collatz tail budget is proved. -/
import MinimumLinearBoundary

namespace MinimumGreenKernel
open CutoffDescent MinimumLinearBoundary MinimumTailRigidity OrdinaryCollatz

def q : Rat := 29 / 30
def rho : Rat := 1704 / 1711
def cell (k n : Nat) : Rat := q ^ k * ((2 ^ k : Nat) + 14 * (n : Rat)) / 15
def gauge (n : Nat) : Rat := if n = 0 then 0 else cell n.log2 n

theorem constants : 0 < q ∧ q < 1 ∧ 0 < rho ∧ rho < 1 ∧
    1 - rho = 7 / 1711 ∧ 3 / (1 - rho) = 5133 / 7 := by
  unfold q rho
  grind

theorem gauge_block (k n : Nat) (hl : 2 ^ k ≤ n) (hu : n < 2 ^ (k + 1)) :
    gauge n = cell k n := by
  have hp := Nat.two_pow_pos k
  have hn : n ≠ 0 := by omega
  have he : n.log2 = k := (Nat.log2_eq_iff hn).mpr ⟨hl, hu⟩
  simp only [gauge, if_neg hn, he]

theorem gauge_nonnegative (n : Nat) : 0 ≤ gauge n := by
  by_cases hn : n = 0
  · simp only [gauge, if_pos hn]; exact Rat.le_refl
  · have hp := Rat.pow_nonneg (n := n.log2) (Rat.le_of_lt constants.1)
    have h2 := Rat.natCast_nonneg (a := 2 ^ n.log2)
    have hn0 := Rat.natCast_nonneg (a := n)
    have hsum : 0 ≤ ((2 ^ n.log2 : Nat) : Rat) + 14 * (n : Rat) := by grind
    have hm := Rat.mul_nonneg hp hsum
    simp only [gauge, if_neg hn, cell]
    grind

theorem low_cell_arithmetic (p n : Nat) (hn : 0 < n)
    (hb : upper n ≤ 4 * p) :
    295 * (88 * p + 420 * lower n + 406 * upper n) ≤
      17040 * (2 * p + 14 * n) := by
  unfold lower upper at *
  omega

theorem high_cell_arithmetic (p n : Nat) (hn : 0 < n)
    (hb : 4 * p ≤ upper n) :
    295 * (2132 * p + 6300 * lower n + 5887 * upper n) ≤
      255600 * (2 * p + 14 * n) := by
  rcases positive_parity n hn with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · rw [(cutoffs_even x).1, (cutoffs_even x).2] at *
    omega
  · rw [(cutoffs_odd x).1, (cutoffs_odd x).2] at *
    omega

theorem block_contraction (k n : Nat) (hl : 2 ^ (k + 1) ≤ n)
    (hu : n < 2 ^ (k + 2)) : average gauge n ≤ rho * gauge n := by
  have hp := Nat.two_pow_pos k
  have hp1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hp2 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_add]; omega
  have hp3 : 2 ^ (k + 3) = 8 * 2 ^ k := by rw [Nat.pow_add]; omega
  have ha : 2 ^ k ≤ lower n ∧ lower n < 2 ^ (k + 1) := by
    unfold lower; omega
  have hb : 2 ^ (k + 1) ≤ upper n ∧ upper n < 2 ^ (k + 3) := by
    unfold upper; omega
  have hq := Rat.pow_nonneg (n := k) (Rat.le_of_lt constants.1)
  rw [average, gauge_block (k + 1) n hl hu, gauge_block k (lower n) ha.1 ha.2]
  by_cases ht : upper n < 2 ^ (k + 2)
  · rw [gauge_block (k + 1) (upper n) hb.1 ht]
    have hc := Rat.natCast_le_natCast.mpr
      (low_cell_arithmetic (2 ^ k) n (by omega) (by omega))
    simp only [Rat.natCast_add, Rat.natCast_mul] at hc
    have hm := Rat.mul_le_mul_of_nonneg_left hc hq
    simp only [cell, Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ]
    unfold q rho at *
    grind
  · rw [gauge_block (k + 2) (upper n) (by omega) hb.2]
    have hc := Rat.natCast_le_natCast.mpr
      (high_cell_arithmetic (2 ^ k) n (by omega) (by omega))
    simp only [Rat.natCast_add, Rat.natCast_mul] at hc
    have hm := Rat.mul_le_mul_of_nonneg_left hc hq
    simp only [cell, Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ]
    unfold q rho at *
    grind

theorem gauge_contraction (n : Nat) (hn : 2 ≤ n) :
    average gauge n ≤ rho * gauge n := by
  have hlog : 1 ≤ n.log2 := (Nat.le_log2 (by omega : n ≠ 0)).mpr (by omega)
  have he : n.log2 - 1 + 1 = n.log2 := by omega
  have hl := Nat.log2_self_le (by omega : n ≠ 0)
  have hu := Nat.lt_log2_self (n := n)
  apply block_contraction (n.log2 - 1) n
  · simpa only [he] using hl
  · have he2 : n.log2 - 1 + 2 = n.log2 + 1 := by omega
    simpa only [he2] using hu

theorem parity_majorant_to_gauge (n : Nat) (hn : 0 < n) :
    q ^ n.log2 * ((n : Rat) + 2 * (2 ^ n.log2 : Nat)) ≤ 3 * gauge n := by
  have hp := Nat.log2_self_le (by omega : n ≠ 0)
  have hc := Rat.natCast_le_natCast.mpr hp
  have hq := Rat.pow_nonneg (n := n.log2) (Rat.le_of_lt constants.1)
  have hm := Rat.mul_le_mul_of_nonneg_left hc hq
  simp only [gauge, if_neg (by omega : n ≠ 0), cell]
  grind

theorem gauge_sublinear_envelope (n : Nat) (hn : 0 < n) :
    gauge n ≤ q ^ n.log2 * (n : Rat) := by
  have hp := Nat.log2_self_le (by omega : n ≠ 0)
  have hc := Rat.natCast_le_natCast.mpr hp
  have hq := Rat.pow_nonneg (n := n.log2) (Rat.le_of_lt constants.1)
  have hm := Rat.mul_le_mul_of_nonneg_left hc hq
  simp only [gauge, if_neg (by omega : n ≠ 0), cell]
  grind

theorem gauge_at_least_one (n : Nat) (hn : 0 < n) : 1 ≤ gauge n := by
  have hb : ∀ k : Nat, 1 ≤ q ^ k * ((2 ^ k : Nat) : Rat) := by
    intro k
    induction k with
    | zero => simp only [Nat.pow_zero, Rat.pow_zero]; grind
    | succ k ih =>
      simp only [Nat.pow_succ, Rat.natCast_mul, Rat.pow_succ]
      unfold q at *
      grind
  have hp := Nat.log2_self_le (by omega : n ≠ 0)
  have hc := Rat.natCast_le_natCast.mpr hp
  have hq := Rat.pow_nonneg (n := n.log2) (Rat.le_of_lt constants.1)
  have hm := Rat.mul_le_mul_of_nonneg_left hc hq
  have hd := hb n.log2
  simp only [gauge, if_neg (by omega : n ≠ 0), cell]
  grind

def killedPower (h : Nat) : Nat → (Nat → Rat) → Nat → Rat
  | 0, f, n => if n ≤ h then 0 else f n
  | k + 1, f, n => if n ≤ h then 0 else
      (killedPower h k f (lower n) + killedPower h k f (upper n)) / 2

def geometric : Nat → Rat
  | 0 => 0
  | k + 1 => 1 + rho * geometric k

private theorem rho_nonnegative : 0 ≤ rho := Rat.le_of_lt constants.2.2.1

theorem geometric_nonnegative (k : Nat) : 0 ≤ geometric k := by
  induction k with
  | zero => exact Rat.le_refl
  | succ k ih =>
    have hm := Rat.mul_nonneg rho_nonnegative ih
    simp only [geometric]
    grind

theorem geometric_identity (k : Nat) :
    (1 - rho) * geometric k = 1 - rho ^ k := by
  induction k with
  | zero => simp only [geometric, Rat.pow_zero]; grind
  | succ k ih => simp only [geometric, Rat.pow_succ]; grind

theorem geometric_upper (k : Nat) : geometric k ≤ 1711 / 7 := by
  have hi := geometric_identity k
  have hp := Rat.pow_nonneg (n := k) rho_nonnegative
  unfold rho at *
  grind

theorem killed_nonnegative (h k : Nat) (f : Nat → Rat)
    (hf : ∀ n, h < n → 0 ≤ f n) (n : Nat) : 0 ≤ killedPower h k f n := by
  induction k generalizing n with
  | zero =>
    by_cases hs : n ≤ h
    · simp only [killedPower, if_pos hs]; exact Rat.le_refl
    · simpa only [killedPower, if_neg hs] using hf n (by omega)
  | succ k ih =>
    by_cases hs : n ≤ h
    · simp only [killedPower, if_pos hs]; exact Rat.le_refl
    · have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [killedPower, if_neg hs]
      grind

theorem killed_gauge_bound (h k : Nat) (hh : 1 ≤ h) (f : Nat → Rat) (c : Rat)
    (hc : 0 ≤ c) (hf : ∀ n, h < n → f n ≤ c * gauge n) (n : Nat) :
    killedPower h k f n ≤ c * rho ^ k * gauge n := by
  have hp := Rat.pow_nonneg (n := k) rho_nonnegative
  have hv := gauge_nonnegative n
  induction k generalizing n with
  | zero =>
    have hm := Rat.mul_nonneg hc hv
    by_cases hs : n ≤ h
    · simp only [killedPower, if_pos hs, Rat.pow_zero]; grind
    · have ht := hf n (by omega)
      simp only [killedPower, if_neg hs, Rat.pow_zero]
      grind
  | succ k ih =>
    by_cases hs : n ≤ h
    · have hm := Rat.mul_nonneg (Rat.mul_nonneg hc hp) hv
      simpa only [killedPower, if_pos hs] using hm
    · have hk := Rat.pow_nonneg (n := k) rho_nonnegative
      have hl := ih (lower n) hk (gauge_nonnegative _)
      have hu := ih (upper n) hk (gauge_nonnegative _)
      have hd := Rat.mul_le_mul_of_nonneg_left (gauge_contraction n (by omega))
        (Rat.mul_nonneg hc hk)
      simp only [killedPower, if_neg hs, average, Rat.pow_succ] at *
      grind

theorem survival_bound (h k n : Nat) (hh : 1 ≤ h) :
    killedPower h k (fun _ => 1) n ≤ rho ^ k * gauge n := by
  have ht := killed_gauge_bound h k hh (fun _ => 1) 1 (by grind)
    (by intro m hm; have hv := gauge_at_least_one m (by omega); grind) n
  grind

theorem occupation_gauge_bound (h k : Nat) (hh : 1 ≤ h) (f : Nat → Rat) (c : Rat)
    (hc : 0 ≤ c) (hf : ∀ n, h < n → f n ≤ c * gauge n) (n : Nat) :
    occupation h k f n ≤ c * geometric k * gauge n := by
  induction k generalizing n with
  | zero => simp only [occupation, geometric]; grind
  | succ k ih =>
    by_cases hs : n ≤ h
    · have hm := Rat.mul_nonneg (Rat.mul_nonneg hc (geometric_nonnegative (k + 1)))
        (gauge_nonnegative n)
      simpa only [occupation, if_pos hs] using hm
    · have hl := ih (lower n)
      have hu := ih (upper n)
      have ht := hf n (by omega)
      have hd := Rat.mul_le_mul_of_nonneg_left (gauge_contraction n (by omega))
        (Rat.mul_nonneg hc (geometric_nonnegative k))
      simp only [occupation, if_neg hs, average, geometric] at *
      grind

def localResidual (f : Nat → Rat) (n : Nat) : Rat := f n - average f n
def magnitude (x : Rat) : Rat := if 0 ≤ x then x else -x

theorem residual_magnitude_bound (f : Nat → Rat) (c : Rat) (hc : 0 ≤ c)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ c * gauge n) (n : Nat) (hn : 2 ≤ n) :
    magnitude (localResidual f n) ≤ c * gauge n := by
  have h0 := hf n
  have hl := hf (lower n)
  have hu := hf (upper n)
  have hd := Rat.mul_le_mul_of_nonneg_left (gauge_contraction n hn) hc
  have hm := Rat.mul_le_mul_of_nonneg_right (Rat.le_of_lt constants.2.2.2.1)
    (Rat.mul_nonneg hc (gauge_nonnegative n))
  simp only [localResidual, average, magnitude] at *
  grind

theorem magnitude_nonnegative (x : Rat) : 0 ≤ magnitude x := by
  unfold magnitude
  split <;> grind

theorem terminal_eq_killed (h k : Nat) (f : Nat → Rat)
    (hf : ∀ n, n ≤ h → f n = 0) (n : Nat) :
    terminal h k f n = killedPower h k f n := by
  induction k generalizing n with
  | zero =>
    by_cases hs : n ≤ h
    · simp only [terminal, killedPower, if_pos hs, hf n hs]
    · simp only [terminal, killedPower, if_neg hs]
  | succ k ih =>
    by_cases hs : n ≤ h
    · simp only [terminal, killedPower, if_pos hs, hf n hs]
    · simp only [terminal, killedPower, if_neg hs, ih]

theorem clockless_exact_unroll (h k : Nat) (f : Nat → Rat) (n : Nat) :
    terminal h k f n + occupation h k (localResidual f) n = f n := by
  induction k generalizing n with
  | zero => simp only [terminal, occupation]; grind
  | succ k ih =>
    by_cases hs : n ≤ h
    · simp only [terminal, occupation, if_pos hs]; grind
    · have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [terminal, occupation, if_neg hs, localResidual, average]
      grind

theorem residual_truncation_bound (h k : Nat) (hh : 1 ≤ h) (f : Nat → Rat)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 3 * gauge n)
    (hz : ∀ n, n ≤ h → f n = 0) (n : Nat) :
    0 ≤ f n - occupation h k (localResidual f) n ∧
      f n - occupation h k (localResidual f) n ≤ 3 * rho ^ k * gauge n := by
  have he := clockless_exact_unroll h k f n
  rw [terminal_eq_killed h k f hz n] at he
  have hl := killed_nonnegative h k f (fun n _ => (hf n).1) n
  have hu := killed_gauge_bound h k hh f 3 (by grind) (fun n _ => (hf n).2) n
  grind

theorem occupation_below_floor (h k : Nat) (f : Nat → Rat) (n : Nat) (hn : n ≤ h) :
    occupation h k f n = 0 := by
  cases k <;> simp only [occupation, if_pos hn]

theorem occupation_nonnegative (h k : Nat) (f : Nat → Rat)
    (hf : ∀ n, h < n → 0 ≤ f n) (n : Nat) : 0 ≤ occupation h k f n := by
  induction k generalizing n with
  | zero => exact Rat.le_refl
  | succ k ih =>
    by_cases hs : n ≤ h
    · simp only [occupation, if_pos hs]; exact Rat.le_refl
    · have ht := hf n (by omega)
      have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [occupation, if_neg hs]
      grind

theorem occupation_split (h j k : Nat) (f : Nat → Rat) (n : Nat) :
    occupation h (j + k) f n = occupation h j f n +
      killedPower h j (fun m => occupation h k f m) n := by
  induction j generalizing n with
  | zero =>
    by_cases hs : n ≤ h
    · simp only [Nat.zero_add, occupation_below_floor h k f n hs,
        occupation, killedPower, if_pos hs]
      grind
    · simp only [Nat.zero_add, occupation, killedPower, if_neg hs]
      grind
  | succ j ih =>
    by_cases hs : n ≤ h
    · simp only [Nat.succ_add, occupation, killedPower, if_pos hs]
      grind
    · have hl := ih (lower n)
      have hu := ih (upper n)
      simp only [Nat.succ_add, occupation, killedPower, if_neg hs]
      grind

theorem absolute_tail_bound (h j k : Nat) (hh : 1 ≤ h) (f : Nat → Rat)
    (hf : ∀ n, 0 ≤ f n ∧ f n ≤ 3 * gauge n) (n : Nat) :
    0 ≤ occupation h (j + k) (fun m => magnitude (localResidual f m)) n -
        occupation h j (fun m => magnitude (localResidual f m)) n ∧
    occupation h (j + k) (fun m => magnitude (localResidual f m)) n -
        occupation h j (fun m => magnitude (localResidual f m)) n ≤
      (5133 / 7) * rho ^ j * gauge n := by
  let r := fun m => magnitude (localResidual f m)
  have hr : ∀ m, h < m → r m ≤ 3 * gauge m := by
    intro m hm
    exact residual_magnitude_bound f 3 (by grind) hf m (by omega)
  have ho : ∀ m, occupation h k r m ≤ (5133 / 7) * gauge m := by
    intro m
    have ht := occupation_gauge_bound h k hh r 3 (by grind) hr m
    have hg := Rat.mul_le_mul_of_nonneg_right (geometric_upper k) (gauge_nonnegative m)
    grind
  have he := occupation_split h j k r n
  have hl := killed_nonnegative h j (fun m => occupation h k r m)
    (fun m _ => occupation_nonnegative h k r (fun m _ => magnitude_nonnegative _) m) n
  have hu := killed_gauge_bound h j hh (fun m => occupation h k r m)
    (5133 / 7) (by grind) (fun m _ => ho m) n
  change 0 ≤ occupation h (j + k) r n - occupation h j r n ∧
    occupation h (j + k) r n - occupation h j r n ≤ _
  grind

noncomputable def globalMean (h n : Nat) : Rat := (tailSum minimum h n : Rat) / n

theorem global_mean_below_floor (h n : Nat) (hn : n ≤ h) : globalMean h n = 0 := by
  have hz : tailSum minimum h n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hl := minimum_le (n + 1) 0
      change minimum (n + 1) ≤ n + 1 at hl
      have hi := ih (by omega)
      simp only [tailSum, MinimumTailRigidity.sumPos] at hi ⊢
      simp only [hi, tailTerm, if_neg (by omega : ¬ h < minimum (n + 1)), Nat.add_zero]
  simp only [globalMean, hz]
  change (0 : Rat) * (n : Rat)⁻¹ = 0
  exact Rat.zero_mul _

theorem global_mean_nonnegative (h n : Nat) : 0 ≤ globalMean h n := by
  by_cases hn : n = 0
  · subst n
    rw [global_mean_below_floor h 0 (Nat.zero_le _)]
    exact Rat.le_refl
  · have hn0 : 0 < n := by omega
    have hp : (0 : Rat) < (n : Rat) := Rat.natCast_lt_natCast.mpr hn0
    have hz := Rat.natCast_nonneg (a := tailSum minimum h n)
    have he := Rat.div_mul_cancel (a := (tailSum minimum h n : Rat))
      (show (n : Rat) ≠ 0 by grind)
    apply Rat.le_of_mul_le_mul_right (c := (n : Rat)) _ hp
    unfold globalMean
    grind

theorem minimum_of_reaches {n : Nat} (hn : 0 < n) (hr : ReachesOne n) : minimum n = 1 := by
  obtain ⟨t, ht⟩ := hr
  have hl := minimum_positive hn
  have hu := minimum_le n t
  rw [ht] at hu
  omega

theorem least_minimum {a : Nat} (ha : LeastCounterexample a) : minimum a = a := by
  have hl := least_orbit_lower_bound ha (minimumClock a)
  have hu := minimum_le a 0
  change a ≤ minimum a at hl
  change minimum a ≤ a at hu
  omega

theorem least_diagonal_tail {a : Nat} (ha : LeastCounterexample a) :
    tailSum minimum (a - 1) a = a := by
  have ha1 := least_gt_one ha
  have hs : ∀ n, n < a → tailSum minimum (a - 1) n = 0 := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hi := ih (by omega)
      have hm := minimum_of_reaches (by omega : 0 < n + 1) (ha.2.2 (n + 1) (by omega) hn)
      simp only [tailSum, MinimumTailRigidity.sumPos] at hi ⊢
      simp only [hi, tailTerm, hm, if_neg (by omega : ¬ a - 1 < 1), Nat.add_zero]
  have he : tailSum minimum (a - 1) (a - 1 + 1) =
      tailSum minimum (a - 1) (a - 1) + tailTerm minimum (a - 1) (a - 1 + 1) := rfl
  have he1 : a - 1 + 1 = a := by omega
  rw [he1, hs (a - 1) (by omega), tailTerm, least_minimum ha,
    if_pos (by omega : a - 1 < a), Nat.zero_add] at he
  exact he

theorem least_diagonal_mean {a : Nat} (ha : LeastCounterexample a) :
    globalMean (a - 1) a = 1 := by
  have hp : (0 : Rat) < (a : Rat) := Rat.natCast_lt_natCast.mpr ha.1
  have he := Rat.div_mul_cancel (a := (a : Rat)) (show (a : Rat) ≠ 0 by grind)
  rw [globalMean, least_diagonal_tail ha]
  grind

theorem finite_positive_residual_diagnostic (h k n : Nat) (hh : 1 ≤ h)
    (f : Nat → Rat) (eta : Rat) (heta : 0 ≤ eta)
    (hf : ∀ m, 0 ≤ f m ∧ f m ≤ 3 * gauge m)
    (hz : ∀ m, m ≤ h → f m = 0) (hone : f n = 1)
    (hr : ∀ m, h < m → localResidual f m ≤ eta * gauge m) :
    1 ≤ (3 * rho ^ k + eta * geometric k) * gauge n := by
  have ht := (residual_truncation_bound h k hh f hf hz n).2
  have ho := occupation_gauge_bound h k hh (localResidual f) eta heta hr n
  rw [hone] at ht
  grind

theorem least_counterexample_residual_diagnostic {a : Nat} (ha : LeastCounterexample a)
    (k : Nat) (eta : Rat) (heta : 0 ≤ eta)
    (hbound : ∀ n, globalMean (a - 1) n ≤ 3 * gauge n)
    (hr : ∀ n, a - 1 < n → localResidual (globalMean (a - 1)) n ≤ eta * gauge n) :
    1 ≤ (3 * rho ^ k + eta * geometric k) * gauge a := by
  have ha1 := least_gt_one ha
  exact finite_positive_residual_diagnostic (a - 1) k a (by omega)
    (globalMean (a - 1)) eta heta
    (fun n => ⟨global_mean_nonnegative (a - 1) n, hbound n⟩)
    (global_mean_below_floor (a - 1)) (least_diagonal_mean ha) hr

#print axioms constants
#print axioms gauge_block
#print axioms gauge_nonnegative
#print axioms low_cell_arithmetic
#print axioms high_cell_arithmetic
#print axioms block_contraction
#print axioms gauge_contraction
#print axioms parity_majorant_to_gauge
#print axioms gauge_sublinear_envelope
#print axioms gauge_at_least_one
#print axioms geometric_nonnegative
#print axioms geometric_identity
#print axioms geometric_upper
#print axioms killed_nonnegative
#print axioms killed_gauge_bound
#print axioms survival_bound
#print axioms occupation_gauge_bound
#print axioms residual_magnitude_bound
#print axioms magnitude_nonnegative
#print axioms terminal_eq_killed
#print axioms clockless_exact_unroll
#print axioms residual_truncation_bound
#print axioms occupation_below_floor
#print axioms occupation_nonnegative
#print axioms occupation_split
#print axioms absolute_tail_bound
#print axioms global_mean_below_floor
#print axioms global_mean_nonnegative
#print axioms minimum_of_reaches
#print axioms least_minimum
#print axioms least_diagonal_tail
#print axioms least_diagonal_mean
#print axioms finite_positive_residual_diagnostic
#print axioms least_counterexample_residual_diagnostic

end MinimumGreenKernel
