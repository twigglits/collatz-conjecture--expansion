/- Attained global minima, their actual-orbit successor, and cap budgets.
   Bounded cap accumulation characterizes eventual repetition, not arrival
   at one. No nontrivial cycle or divergent orbit is excluded here. -/
import MinimumPopulationMajorant

namespace MinimumRootSpine
open OrdinaryCollatz MinimumTailRigidity MinimumCapTransport
open MinimumClockBarrier MinimumGreenKernel MinimumPopulationMajorant

def Periodic (n : Nat) : Prop := ∃ p, 0 < p ∧ iterate p n = n
def EventuallyPeriodic (n : Nat) : Prop :=
  ∃ s p, 0 < p ∧ iterate (s + p) n = iterate s n

theorem minimum_le_source (n : Nat) : minimum n ≤ n := minimum_le n 0

theorem minimum_suffix (n t : Nat) : minimum n ≤ minimum (iterate t n) := by
  have h := minimum_le n (t + minimumClock (iterate t n))
  rw [iterate_add] at h
  exact h

theorem minimum_bellman (n : Nat) : minimum n = min n (minimum (C n)) := by
  have hs := minimum_le_source n
  have ht := minimum_suffix n 1
  change minimum n ≤ minimum (C n) at ht
  obtain ⟨t, he⟩ := minimum_attained n
  cases t with
  | zero => change n = minimum n at he; omega
  | succ t =>
    have hl := minimum_le (C n) t
    change iterate t (C n) = minimum n at he
    omega

theorem minimum_self_iff (n : Nat) :
    minimum n = n ↔ ∀ t, n ≤ iterate t n := by
  constructor
  · intro hn t
    have h := minimum_le n t
    rwa [hn] at h
  · intro hn
    have hl := hn (minimumClock n)
    have hu := minimum_le_source n
    change n ≤ minimum n at hl
    omega

theorem minimum_even (n : Nat) : minimum (2 * n) = minimum n := by
  have hc : C (2 * n) = n := by unfold C; split <;> omega
  have hl := minimum_le_source n
  rw [minimum_bellman (2 * n), hc]
  omega

theorem minimum_odd (n : Nat) :
    minimum (2 * n + 1) = min (2 * n + 1) (minimum (3 * n + 2)) := by
  have hc : C (2 * n + 1) = 2 * (3 * n + 2) := by unfold C; split <;> omega
  rw [minimum_bellman (2 * n + 1), hc, minimum_even]

theorem global_odd_cap (h n : Nat) :
    tailValue h (minimum (2 * n + 1)) + cap h (2 * n + 1) (minimum (3 * n + 2)) =
      tailValue h (minimum (3 * n + 2)) := by
  rw [minimum_odd]
  exact cap_add_identity h (2 * n + 1) (minimum (3 * n + 2))

theorem self_minimum_odd {n : Nat} (hn : 0 < n) (hm : minimum n = n) :
    n % 2 = 1 := by
  have hl := (minimum_self_iff n).mp hm 1
  by_cases he : n % 2 = 0
  · have hd := even_descent hn he
    omega
  · omega

theorem self_minimum_mod16 {n : Nat} (hn : 1 < n) (hm : minimum n = n) :
    n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15 := by
  have ho := self_minimum_odd (by omega) hm
  have h4 : n % 4 ≠ 1 := by
    intro he
    have hd := mod4_descent hn he
    have hl := (minimum_self_iff n).mp hm 3
    omega
  have h16 : n % 16 ≠ 3 := by
    intro he
    have hd := mod16_descent he
    have hl := (minimum_self_iff n).mp hm 6
    omega
  omega

noncomputable def nextRoot (n : Nat) : Nat := minimum (C n)

theorem next_root_self (n : Nat) : minimum (nextRoot n) = nextRoot n :=
  minimum_idempotent (C n)

theorem next_root_ge {n : Nat} (hm : minimum n = n) : n ≤ nextRoot n := by
  have h := minimum_suffix n 1
  change minimum n ≤ nextRoot n at h
  rwa [hm] at h

theorem next_root_upper {n : Nat} (hn : 0 < n) (hm : minimum n = n) :
    2 * nextRoot n ≤ 3 * n + 1 := by
  have ho := self_minimum_odd hn hm
  have hc : C n = 2 * (3 * (n / 2) + 2) := by unfold C; rw [if_pos ho]; omega
  have hu := minimum_le_source (3 * (n / 2) + 2)
  simp only [nextRoot, hc, minimum_even]
  omega

theorem next_root_fixed_iff {n : Nat} (hm : minimum n = n) :
    nextRoot n = n ↔ Periodic n := by
  constructor
  · intro he
    refine ⟨minimumClock (C n) + 1, by omega, ?_⟩
    exact he
  · rintro ⟨p, hp, he⟩
    cases p with
    | zero => omega
    | succ p =>
      have hu := minimum_le (C n) p
      have hl := next_root_ge hm
      change iterate p (C n) = n at he
      change nextRoot n ≤ iterate p (C n) at hu
      omega

theorem step_not_zero_mod3 {n : Nat} (hn : n % 3 ≠ 0) : C n % 3 ≠ 0 := by
  unfold C
  split <;> omega

theorem iterate_not_zero_mod3 {n : Nat} (hn : n % 3 ≠ 0) (t : Nat) :
    iterate t n % 3 ≠ 0 := by
  induction t generalizing n with
  | zero => exact hn
  | succ t ih => exact ih (step_not_zero_mod3 hn)

theorem next_root_not_zero_mod3 {n : Nat} (hn : 0 < n) (hm : minimum n = n) :
    nextRoot n % 3 ≠ 0 := by
  have ho := self_minimum_odd hn hm
  have hc : C n % 3 ≠ 0 := by unfold C; rw [if_pos ho]; omega
  exact iterate_not_zero_mod3 hc (minimumClock (C n))

noncomputable def stepCap (n : Nat) : Nat := minimum (C n) - minimum n
noncomputable def orbitCaps : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => stepCap n + orbitCaps t (C n)

theorem step_cap_add (n : Nat) : minimum n + stepCap n = minimum (C n) := by
  have h := minimum_suffix n 1
  change minimum n ≤ minimum (C n) at h
  unfold stepCap
  omega

theorem step_cap_positive_iff (n : Nat) :
    0 < stepCap n ↔ minimum n = n ∧ ¬ Periodic n := by
  have hb := minimum_bellman n
  have hs := step_cap_add n
  constructor
  · intro hp
    have hm : minimum n = n := by omega
    refine ⟨hm, ?_⟩
    intro hr
    have he := (next_root_fixed_iff hm).mpr hr
    change minimum (C n) = n at he
    omega
  · rintro ⟨hm, hnp⟩
    have he : nextRoot n ≠ n := by
      intro hf
      exact hnp ((next_root_fixed_iff hm).mp hf)
    change minimum (C n) ≠ n at he
    omega

theorem step_cap_even (n : Nat) : stepCap (2 * n) = 0 := by
  have hc : C (2 * n) = n := by unfold C; split <;> omega
  simp only [stepCap, hc, minimum_even, Nat.sub_self]

theorem orbit_caps_telescope (t n : Nat) :
    minimum n + orbitCaps t n = minimum (iterate t n) := by
  induction t generalizing n with
  | zero => simp only [orbitCaps, iterate, Nat.add_zero]
  | succ t ih =>
    have hs := step_cap_add n
    have ht := ih (C n)
    simp only [orbitCaps, iterate]
    omega

noncomputable def root : Nat → Nat → Nat
  | 0, n => minimum n
  | k + 1, n => nextRoot (root k n)

noncomputable def rootClock : Nat → Nat → Nat
  | 0, n => minimumClock n
  | k + 1, n => rootClock k n + (minimumClock (C (root k n)) + 1)

theorem root_self (k n : Nat) : minimum (root k n) = root k n := by
  cases k with
  | zero => exact minimum_idempotent n
  | succ k => exact next_root_self (root k n)

theorem root_positive (k n : Nat) (hn : 0 < n) : 0 < root k n := by
  induction k with
  | zero => exact minimum_positive hn
  | succ k ih => exact minimum_positive (C_positive ih)

theorem root_clock_attained (k n : Nat) : iterate (rootClock k n) n = root k n := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rootClock, iterate_add, ih]
    rfl

theorem root_clock_strict (k n : Nat) : rootClock k n < rootClock (k + 1) n := by
  simp only [rootClock]
  omega

theorem root_monotone (k n : Nat) : root k n ≤ root (k + 1) n :=
  next_root_ge (root_self k n)

theorem root_fixed_eventual {k n : Nat} (he : root (k + 1) n = root k n) :
    EventuallyPeriodic n := by
  obtain ⟨p, hp, hr⟩ := (next_root_fixed_iff (root_self k n)).mp he
  refine ⟨rootClock k n, p, hp, ?_⟩
  rw [iterate_add, root_clock_attained, hr]

theorem root_strict {n : Nat} (hn : ¬ EventuallyPeriodic n) (k : Nat) :
    root k n < root (k + 1) n := by
  have hl := root_monotone k n
  have hne : root (k + 1) n ≠ root k n := fun he => hn (root_fixed_eventual he)
  omega

theorem root_lower {n : Nat} (hn : ¬ EventuallyPeriodic n) (k : Nat) :
    minimum n + k ≤ root k n := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => have hs := root_strict hn k; omega

theorem bounded_tail_iff_eventual (n : Nat) :
    (∃ b, ∀ t, minimum (iterate t n) ≤ b) ↔ EventuallyPeriodic n := by
  constructor
  · rintro ⟨b, hb⟩
    apply Classical.byContradiction
    intro hnp
    have hl := root_lower hnp (b + 1)
    have hu := hb (rootClock (b + 1) n)
    rw [root_clock_attained, root_self] at hu
    omega
  · rintro ⟨s, p, hp, he⟩
    have hr : iterate p (iterate s n) = iterate s n := by
      rwa [iterate_add] at he
    have hm : ∀ k, iterate (k * p) (iterate s n) = iterate s n := by
      intro k
      induction k with
      | zero => simp only [Nat.zero_mul, iterate]
      | succ k ih => rw [Nat.succ_mul, iterate_add, ih, hr]
    refine ⟨minimum (iterate s n), ?_⟩
    intro t
    have ht : t ≤ s + (t + 1) * p := by
      have hl := Nat.mul_le_mul_left (t + 1) hp
      omega
    have hl := minimum_suffix (iterate t n) (s + (t + 1) * p - t)
    rw [← iterate_add, Nat.add_sub_of_le ht, iterate_add, hm] at hl
    exact hl

theorem bounded_caps_iff_eventual (n : Nat) :
    (∃ b, ∀ t, orbitCaps t n ≤ b) ↔ EventuallyPeriodic n := by
  rw [← bounded_tail_iff_eventual]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨minimum n + b, ?_⟩
    intro t
    have he := orbit_caps_telescope t n
    have ht := hb t
    omega
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    intro t
    have he := orbit_caps_telescope t n
    have ht := hb t
    omega

theorem root_gt_one {n : Nat} (hn : 0 < n) (hnp : ¬ EventuallyPeriodic n) (k : Nat) :
    1 < root k n := by
  have hp := root_positive k n hn
  have hne : root k n ≠ 1 := by
    intro he
    have hperiod : Periodic (root k n) := by
      rw [he]
      exact ⟨3, by decide, by decide⟩
    have hf := (next_root_fixed_iff (root_self k n)).mpr hperiod
    exact hnp (root_fixed_eventual hf)
  omega

theorem root_spacing {n : Nat} (hn : 0 < n) (hnp : ¬ EventuallyPeriodic n) (k : Nat) :
    root k n + 4 ≤ root (k + 1) n := by
  have h0 := self_minimum_mod16 (root_gt_one hn hnp k) (root_self k n)
  have h1 := self_minimum_mod16 (root_gt_one hn hnp (k + 1)) (root_self (k + 1) n)
  have hs := root_strict hnp k
  omega

theorem root_growth {n : Nat} (hn : 0 < n) (hnp : ¬ EventuallyPeriodic n) (k : Nat) :
    minimum n + 4 * k ≤ root k n := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => have hs := root_spacing hn hnp k; omega

theorem root_upper (k n : Nat) (hn : 0 < n) :
    2 ^ k * (root k n + 1) ≤ 3 ^ k * (minimum n + 1) := by
  induction k with
  | zero => simp only [root, Nat.pow_zero, Nat.one_mul]; exact Nat.le_refl _
  | succ k ih =>
    have hs := next_root_upper (root_positive k n hn) (root_self k n)
    change 2 * root (k + 1) n ≤ 3 * root k n + 1 at hs
    have ht : 2 * (root (k + 1) n + 1) ≤ 3 * (root k n + 1) := by omega
    have hm := Nat.mul_le_mul_left (2 ^ k) ht
    have hi := Nat.mul_le_mul_left 3 ih
    simp only [Nat.pow_succ]
    calc
      2 ^ k * 2 * (root (k + 1) n + 1) = 2 ^ k * (2 * (root (k + 1) n + 1)) := by grind
      _ ≤ 2 ^ k * (3 * (root k n + 1)) := hm
      _ = 3 * (2 ^ k * (root k n + 1)) := by grind
      _ ≤ 3 * (3 ^ k * (minimum n + 1)) := hi
      _ = 3 ^ k * 3 * (minimum n + 1) := by grind

theorem root_successor_mod48 {n : Nat} (hn : 0 < n) (hnp : ¬ EventuallyPeriodic n)
    (k : Nat) :
    root (k + 1) n % 48 = 7 ∨ root (k + 1) n % 48 = 11 ∨
      root (k + 1) n % 48 = 23 ∨ root (k + 1) n % 48 = 31 ∨
      root (k + 1) n % 48 = 43 ∨ root (k + 1) n % 48 = 47 := by
  have h16 := self_minimum_mod16 (root_gt_one hn hnp (k + 1)) (root_self (k + 1) n)
  have h3 := next_root_not_zero_mod3 (root_positive k n hn) (root_self k n)
  change root (k + 1) n % 3 ≠ 0 at h3
  omega

theorem aperiodic_caps_unbounded {n : Nat} (hnp : ¬ EventuallyPeriodic n) (b : Nat) :
    ∃ t, b < orbitCaps t n := by
  apply Classical.byContradiction
  intro hno
  apply hnp
  apply (bounded_caps_iff_eventual n).mp
  refine ⟨b, ?_⟩
  intro t
  have ht : ¬ b < orbitCaps t n := fun he => hno ⟨t, he⟩
  omega

theorem convergent_caps_zero {n : Nat} (hn : 0 < n) (hr : ReachesOne n) (t : Nat) :
    orbitCaps t n = 0 := by
  have h0 := minimum_of_reaches hn hr
  have ht := minimum_of_reaches (iterate_positive t n hn) (reaches_after_iterate t n hr)
  have he := orbit_caps_telescope t n
  omega

def finiteOrbitCaps : Nat → Nat → Nat
  | 0, _ => 0
  | t + 1, n => (prefixMinimum t (C n) - prefixMinimum (t + 1) n) +
      finiteOrbitCaps t (C n)

theorem finite_caps_telescope (t n : Nat) :
    prefixMinimum t n + finiteOrbitCaps t n = iterate t n := by
  induction t generalizing n with
  | zero => simp only [prefixMinimum, finiteOrbitCaps, iterate, Nat.add_zero]
  | succ t ih =>
    have ht := ih (C n)
    have hs : prefixMinimum (t + 1) n ≤ prefixMinimum t (C n) := by
      simp only [prefixMinimum]
      omega
    change prefixMinimum (t + 1) n +
      ((prefixMinimum t (C n) - prefixMinimum (t + 1) n) + finiteOrbitCaps t (C n)) = _
    change prefixMinimum t (C n) + finiteOrbitCaps t (C n) = iterate (t + 1) n at ht
    omega

theorem finite_caps_one : finiteOrbitCaps 1 1 = 3 := by decide

theorem global_caps_one (t : Nat) : orbitCaps t 1 = 0 :=
  convergent_caps_zero (by decide) reaches_one t

theorem one_cycle_iterate (k : Nat) : iterate (3 * k) 1 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.mul_succ, iterate_add, ih]; rfl

theorem finite_caps_cycle (k : Nat) :
    finiteOrbitCaps (3 * k) 1 = 0 ∧ finiteOrbitCaps (3 * k + 1) 1 = 3 ∧
      finiteOrbitCaps (3 * k + 2) 1 = 1 := by
  have hm : ∀ t, prefixMinimum t 1 = 1 := by
    intro t
    have hl := minimum_le_prefix t 1
    have hu := prefix_le_source t 1
    rw [minimum_of_reaches (by decide : 0 < 1) reaches_one] at hl
    omega
  have h0 := finite_caps_telescope (3 * k) 1
  have h1 := finite_caps_telescope (3 * k + 1) 1
  have h2 := finite_caps_telescope (3 * k + 2) 1
  rw [hm, one_cycle_iterate] at h0
  rw [hm, iterate_add, one_cycle_iterate] at h1 h2
  have e1 : iterate 1 1 = 4 := rfl
  have e2 : iterate 2 1 = 2 := rfl
  rw [e1] at h1
  rw [e2] at h2
  omega

def highSelfCount (m : Nat → Nat) (b n : Nat) : Nat :=
  sumPos (fun j => if b < j ∧ m j = j then 1 else 0) n

noncomputable def rootShell (k : Nat) : Nat :=
  highSelfCount minimum (2 ^ k) (2 ^ (k + 1))

def prefixRootShell (k t : Nat) : Nat :=
  highSelfCount (prefixMinimum t) (2 ^ k) (2 ^ (k + 1))

theorem high_self_count_weighted (m : Nat → Nat) (b n : Nat) :
    b * highSelfCount m b n ≤ tailSum m 0 n := by
  induction n with
  | zero => simp only [highSelfCount, tailSum, sumPos, Nat.mul_zero]; omega
  | succ n ih =>
    by_cases he : b < n + 1 ∧ m (n + 1) = n + 1
    · simp only [highSelfCount, tailSum, sumPos, if_pos he] at *
      have ht : tailTerm m 0 (n + 1) = n + 1 := by
        simp only [tailTerm, he.2, if_pos (by omega : 0 < n + 1)]
      rw [ht, Nat.mul_add, Nat.mul_one]
      omega
    · simp only [highSelfCount, tailSum, sumPos, if_neg he, Nat.add_zero] at *
      omega

theorem root_shell_le_prefix (k t : Nat) : rootShell k ≤ prefixRootShell k t := by
  apply MinimumTailRigidity.sum_mono
  intro j _ _
  by_cases he : 2 ^ k < j ∧ minimum j = j
  · have hl := minimum_le_prefix t j
    have hu := prefix_le_source t j
    have hp : 2 ^ k < j ∧ prefixMinimum t j = j := by omega
    simp only [if_pos he, if_pos hp]
    exact Nat.le_refl _
  · simp only [if_neg he]
    exact Nat.zero_le _

theorem prefix_root_shell_integer (k t : Nat) (ht : 2 * (k + 1) ≤ t) :
    2 * 120 ^ (k + 1) * prefixRootShell k t ≤
      4 * 232 ^ (k + 1) + 120 ^ (k + 1) * (k + 1) := by
  have hw := high_self_count_weighted (prefixMinimum t) (2 ^ k) (2 ^ (k + 1))
  change 2 ^ k * prefixRootShell k t ≤ tailSum (prefixMinimum t) 0 (2 ^ (k + 1)) at hw
  have hp := dyadic_population_integer 0 (k + 1) t ht
  have hm := Nat.mul_le_mul_left (4 * 120 ^ (k + 1)) hw
  have hc : (2 * 2 ^ k) * (2 * 120 ^ (k + 1) * prefixRootShell k t) ≤
      (2 * 2 ^ k) * (4 * 232 ^ (k + 1) + 120 ^ (k + 1) * (k + 1)) := by
    calc
      _ = 4 * 120 ^ (k + 1) * (2 ^ k * prefixRootShell k t) := by grind
      _ ≤ 4 * 120 ^ (k + 1) * tailSum (prefixMinimum t) 0 (2 ^ (k + 1)) := hm
      _ ≤ 4 * 2 ^ (k + 1) * 232 ^ (k + 1) +
          120 ^ (k + 1) * (k + 1) * 2 ^ (k + 1) := hp
      _ = _ := by rw [Nat.pow_succ]; grind
  exact Nat.le_of_mul_le_mul_left hc (Nat.mul_pos (by decide) (Nat.two_pow_pos k))

theorem prefix_root_shell_bound (k t : Nat) (ht : 2 * (k + 1) ≤ t) :
    (prefixRootShell k t : Rat) ≤ 2 * rate ^ (k + 1) + (k + 1 : Nat) / (2 : Rat) := by
  have hb := prefix_root_shell_integer k t ht
  have h := scaled_mean_bound (prefixRootShell k t) 1 (120 ^ (k + 1)) (232 ^ (k + 1))
    (k + 1) 2 2 (by decide) (Nat.pow_pos (by decide)) (by decide)
    (by simpa only [Nat.one_mul, Nat.reduceMul] using hb)
    (rate ^ (k + 1)) (scale_rate_identity (k + 1))
  have he : (prefixRootShell k t : Rat) / 1 = prefixRootShell k t := by
    have hd := Rat.div_mul_cancel (a := (prefixRootShell k t : Rat)) (b := 1) (by decide)
    simpa only [Rat.mul_one] using hd
  simpa only [Rat.natCast_ofNat, he] using h

theorem root_shell_bound (k : Nat) :
    (rootShell k : Rat) ≤ 2 * rate ^ (k + 1) + (k + 1 : Nat) / (2 : Rat) :=
  Rat.le_trans (Rat.natCast_le_natCast.mpr (root_shell_le_prefix k (2 * (k + 1))))
    (prefix_root_shell_bound k (2 * (k + 1)) (Nat.le_refl _))

noncomputable def shellHarmonic : Nat → Rat
  | 0 => 0
  | k + 1 => shellHarmonic k + (rootShell k : Rat) * (1 / 2) ^ k

def shellTail (k : Nat) : Rat := 116 * q ^ k + ((k : Rat) + 2) * (1 / 2) ^ k

theorem rate_half_identity (k : Nat) : rate ^ k * (1 / 2) ^ k = q ^ k := by
  induction k with
  | zero => simp only [Rat.pow_zero, Rat.one_mul]
  | succ k ih =>
    simp only [Rat.pow_succ]
    calc
      rate ^ k * rate * ((1 / 2) ^ k * (1 / 2)) =
          (rate ^ k * (1 / 2) ^ k) * (rate * (1 / 2)) := by grind only
      _ = q ^ k * q := by
        have hc : rate * (1 / 2) = q := by decide +kernel
        rw [ih, hc]

theorem shell_tail_identity (k : Nat) :
    (2 * rate ^ (k + 1) + (k + 1 : Nat) / (2 : Rat)) * (1 / 2) ^ k +
      shellTail (k + 1) = shellTail k := by
  have hm := rate_half_identity k
  have hd := Rat.div_mul_cancel (a := ((k + 1 : Nat) : Rat)) (b := 2) (by decide)
  have he : 2 * rate ^ (k + 1) * (1 / 2) ^ k = (58 / 15) * q ^ k := by
    rw [Rat.pow_succ]
    calc
      2 * (rate ^ k * rate) * (1 / 2) ^ k = (2 * rate) * (rate ^ k * (1 / 2) ^ k) := by grind only
      _ = (58 / 15) * q ^ k := by
        have hc : 2 * rate = 58 / 15 := by decide +kernel
        rw [hm, hc]
  rw [Rat.add_mul, he]
  simp only [shellTail, Rat.pow_succ, Rat.natCast_add, Rat.natCast_ofNat] at hd ⊢
  unfold q
  grind

theorem shell_tail_nonnegative (k : Nat) : 0 ≤ shellTail k := by
  have hq := Rat.pow_nonneg (n := k) (show (0 : Rat) ≤ q by decide +kernel)
  have hh := Rat.pow_nonneg (n := k) (show (0 : Rat) ≤ 1 / 2 by decide +kernel)
  have hk := Rat.natCast_nonneg (a := k)
  have hp := Rat.mul_nonneg (show (0 : Rat) ≤ (k : Rat) + 2 by grind) hh
  unfold shellTail
  grind

theorem shell_harmonic_with_tail (k : Nat) : shellHarmonic k + shellTail k ≤ 118 := by
  induction k with
  | zero =>
    simp only [shellHarmonic, shellTail, Rat.pow_zero, Rat.natCast_ofNat]
    decide +kernel
  | succ k ih =>
    have hh := Rat.pow_nonneg (n := k) (show (0 : Rat) ≤ 1 / 2 by decide +kernel)
    have hb := Rat.mul_le_mul_of_nonneg_right (root_shell_bound k) hh
    have he := shell_tail_identity k
    simp only [shellHarmonic]
    grind

theorem shell_harmonic_bound (k : Nat) : shellHarmonic k ≤ 118 := by
  have ht := shell_tail_nonnegative k
  have hb := shell_harmonic_with_tail k
  grind

#print axioms minimum_le_source
#print axioms minimum_suffix
#print axioms minimum_bellman
#print axioms minimum_self_iff
#print axioms minimum_even
#print axioms minimum_odd
#print axioms global_odd_cap
#print axioms self_minimum_odd
#print axioms self_minimum_mod16
#print axioms next_root_self
#print axioms next_root_ge
#print axioms next_root_upper
#print axioms next_root_fixed_iff
#print axioms step_not_zero_mod3
#print axioms iterate_not_zero_mod3
#print axioms next_root_not_zero_mod3
#print axioms step_cap_add
#print axioms step_cap_positive_iff
#print axioms step_cap_even
#print axioms orbit_caps_telescope
#print axioms root_self
#print axioms root_positive
#print axioms root_clock_attained
#print axioms root_clock_strict
#print axioms root_monotone
#print axioms root_fixed_eventual
#print axioms root_strict
#print axioms root_lower
#print axioms bounded_tail_iff_eventual
#print axioms bounded_caps_iff_eventual
#print axioms root_gt_one
#print axioms root_spacing
#print axioms root_growth
#print axioms root_upper
#print axioms root_successor_mod48
#print axioms aperiodic_caps_unbounded
#print axioms convergent_caps_zero
#print axioms finite_caps_telescope
#print axioms finite_caps_one
#print axioms global_caps_one
#print axioms one_cycle_iterate
#print axioms finite_caps_cycle
#print axioms high_self_count_weighted
#print axioms root_shell_le_prefix
#print axioms prefix_root_shell_integer
#print axioms prefix_root_shell_bound
#print axioms root_shell_bound
#print axioms rate_half_identity
#print axioms shell_tail_identity
#print axioms shell_tail_nonnegative
#print axioms shell_harmonic_with_tail
#print axioms shell_harmonic_bound

end MinimumRootSpine
