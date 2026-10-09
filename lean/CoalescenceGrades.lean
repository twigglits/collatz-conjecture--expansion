/-
  Arrival grades, exact minima, and a conditional odd/even-credit rank.
  Standalone Lean 4. No universal credit bound or Collatz proof is asserted.
-/
import EqualWeightFibres
import CollatzContradiction

namespace CollatzPacking

theorem grade_orbit_positive : ∀ k n, 0 < n → 0 < orbit k n
  | 0, _, h => h
  | k + 1, n, h => by
    apply grade_orbit_positive k (U n)
    unfold U
    split <;> omega

theorem grade_ordinary_bridge : ∀ k n,
    orbit k n = OrdinaryCollatz.shortcutIter k n
  | 0, _ => rfl
  | k + 1, n => by
    simpa only [orbit, OrdinaryCollatz.shortcutIter, U, OrdinaryCollatz.U]
      using grade_ordinary_bridge k (U n)

theorem grade_reaches_bridge (n : Nat) :
    OrdinaryCollatz.ReachesOne n ↔ ∃ k, orbit k n = 1 := by
  rw [OrdinaryCollatz.reaches_iff_shortcut]
  simp only [grade_ordinary_bridge]

/-- The dyadic envelope is valid even after arrival at the standard cycle. -/
theorem dyadic_envelope : ∀ k n, 0 < n →
    2 ^ k * orbit k n ≤ 2 ^ (2 * wt k n) * n
  | 0, n, _ => by simp [orbit, wt]
  | k + 1, n, hn => by
    have h := Nat.mul_le_mul_left 2
      (dyadic_envelope k (U n) (grade_orbit_positive 1 n hn))
    by_cases ho : n % 2 = 1
    · have hu : 2 * U n ≤ 4 * n := by simp only [U, if_pos ho]; omega
      have he : 2 * (2 ^ (2 * wt k (U n)) * U n) =
          2 ^ (2 * wt k (U n)) * (2 * U n) := by ac_rfl
      rw [he] at h
      have hc := Nat.le_trans h (Nat.mul_le_mul_left (2 ^ (2 * wt k (U n))) hu)
      have four : 4 = 2 * 2 := rfl
      rw [four] at hc
      simpa only [orbit, wt, ho, Nat.mul_add, Nat.add_mul, Nat.pow_add, Nat.pow_succ,
        Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hc
    · have hz : n % 2 = 0 := by omega
      have hu : 2 * U n = n := by simp only [U, if_neg ho]; omega
      have he : 2 * (2 ^ (2 * wt k (U n)) * U n) =
          2 ^ (2 * wt k (U n)) * (2 * U n) := by ac_rfl
      rw [he, hu] at h
      simpa only [orbit, wt, hz, Nat.zero_add, Nat.pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem core_balance : ∀ k n, StandardCore n →
    k + orbit k n = 2 * wt k n + n
  | 0, n, _ => by simp [orbit, wt]
  | k + 1, n, hn => by
    have h := core_balance k (U n) (core_closed n hn)
    have hs : 1 + U n = 2 * (n % 2) + n := by
      rcases hn with h | h <;> subst n <;> decide
    simp only [orbit, wt]
    omega

theorem core_path (k n : Nat) (hn : StandardCore n) : StandardCore (orbit k n) :=
  orbit_mem_of_forward_closed StandardCore core_closed k n hn

theorem arrival_extension {n T : Nat} (hT : orbit T n = 1) (s : Nat) :
    StandardCore (orbit (T + s) n) ∧
    T + s + orbit (T + s) n + 2 * wt T n = T + 1 + 2 * wt (T + s) n := by
  have hc := core_path s 1 (Or.inl rfl)
  have hb := core_balance s 1 (Or.inl rfl)
  rw [Nat.add_comm T s, orbit_add, weight_add_right, hT]
  exact ⟨hc, by omega⟩

/-- Integer arrival-grade equality is written without truncated subtraction. -/
theorem equal_weight_iff_arrival_grade {n m T S : Nat}
    (hT : orbit T n = 1) (hS : orbit S m = 1) :
    (∃ k, EqualWeightMate k n m) ↔ T + 2 * wt S m = S + 2 * wt T n := by
  have hn := arrival_extension hT S
  have hm := arrival_extension hS T
  have hm' : StandardCore (orbit (T + S) m) ∧
      T + S + orbit (T + S) m + 2 * wt S m = S + 1 + 2 * wt (T + S) m := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  constructor
  · rintro ⟨k, hk⟩
    have hp := mate_persists hk (T + S)
    have he : EqualWeightMate (T + S) n m :=
      (mate_after_core_iff hn.1 hm'.1 k).mp (by simpa [Nat.add_comm] using hp)
    have hs := he.1
    have hw := he.2
    omega
  · intro hg
    refine ⟨T + S, ?_⟩
    have hc1 := hn.1
    have hc2 := hm'.1
    unfold StandardCore at hc1 hc2
    constructor <;> omega

/-- The clock/odd-count imbalance of any physical meeting determines the grade gap. -/
theorem meeting_grade_balance {n m T S a b : Nat}
    (hT : orbit T n = 1) (hS : orbit S m = 1)
    (hmeet : orbit a n = orbit b m) :
    T + b + 2 * wt a n + 2 * wt S m = S + a + 2 * wt b m + 2 * wt T n := by
  have hn := arrival_extension hT (a + S)
  have hm := arrival_extension hS (b + T)
  have hen : T + (a + S) = (T + S) + a := by omega
  have hem : S + (b + T) = (T + S) + b := by omega
  rw [hen, orbit_add, weight_add_right, hmeet] at hn
  rw [hem, orbit_add, weight_add_right] at hm
  omega

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem nonnegative_grades_below27 : ∀ m : Fin 27, 0 < m.val →
    ∃ t : Fin 73, orbit t.val m.val = 1 ∧ 2 * wt t.val m.val ≤ t.val := by decide

theorem common_clock_27_needs_six {m k : Nat} (hm : 0 < m) (hlt : m < 27)
    (hmeet : orbit k 27 = orbit k m) : wt k m + 6 ≤ wt k 27 := by
  obtain ⟨t, ht, hw⟩ := nonnegative_grades_below27 ⟨m, hlt⟩ hm
  change 2 * wt t.val m ≤ t.val at hw
  have h := meeting_grade_balance (n := 27) (m := m) convergent_27 ht hmeet
  have hj : wt 70 27 = 41 := by decide
  rw [hj] at h
  omega

theorem equal_weight_27_needs_twelve {m a b : Nat} (hm : 0 < m) (hlt : m < 27)
    (hmeet : orbit a 27 = orbit b m) (hweight : wt a 27 = wt b m) : a + 12 ≤ b := by
  obtain ⟨t, ht, hw⟩ := nonnegative_grades_below27 ⟨m, hlt⟩ hm
  change 2 * wt t.val m ≤ t.val at hw
  have h := meeting_grade_balance (n := 27) (m := m) convergent_27 ht hmeet
  have hj : wt 70 27 = 41 := by decide
  rw [hj, hweight] at h
  omega

set_option maxRecDepth 10000 in
theorem sharp_27_meetings :
    (orbit 70 27 = orbit 70 1 ∧ wt 70 27 = wt 70 1 + 6) ∧
    (orbit 70 27 = orbit 82 1 ∧ wt 70 27 = wt 82 1) := by decide

theorem grade_even_step (n : Nat) : U (2 * n) = n := by
  simp only [U]
  have h : (2 * n) % 2 ≠ 1 := by omega
  rw [if_neg h]
  omega

theorem power_two_path : ∀ a n,
    orbit a (2 ^ a * n) = n ∧ wt a (2 ^ a * n) = 0
  | 0, n => by simp [orbit, wt]
  | a + 1, n => by
    have he : 2 ^ (a + 1) * n = 2 * (2 ^ a * n) := by
      rw [Nat.pow_succ]
      ac_rfl
    have hp : (2 * (2 ^ a * n)) % 2 = 0 := by omega
    simp only [he, orbit, wt, grade_even_step, hp, Nat.zero_add]
    exact power_two_path a n

theorem core_pairs : ∀ t, orbit (2 * t) 1 = 1 ∧ wt (2 * t) 1 = t
  | 0 => by decide
  | t + 1 => by
    have he : 2 * (t + 1) = 2 * t + 2 := by omega
    rw [he, orbit_add, weight_add_right]
    have h : orbit 2 1 = 1 ∧ wt 2 1 = 1 := by decide
    rw [h.1, h.2, (core_pairs t).1, (core_pairs t).2]
    omega

/-- Every source of nonnegative arrival grade a is at least 2^a. -/
theorem arrival_grade_minimum {n T a : Nat} (hn : 0 < n)
    (hT : orbit T n = 1) (hg : T = 2 * wt T n + a) : 2 ^ a ≤ n := by
  have h := dyadic_envelope T n hn
  rw [hT, Nat.mul_one] at h
  have hp : 2 ^ T = 2 ^ (2 * wt T n) * 2 ^ a := by
    calc
      2 ^ T = 2 ^ (2 * wt T n + a) := congrArg (fun z => 2 ^ z) hg
      _ = _ := Nat.pow_add _ _ _
  rw [hp] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.pow_pos (by decide))

/-- The unbounded minimal representatives are explicitly the powers of two. -/
theorem power_two_mate_minimum {a k m : Nat} (hm : 0 < m)
    (h : EqualWeightMate k (2 ^ a) m) : 2 ^ a ≤ m := by
  have hp := mate_persists h (a + k)
  have ht : k + (a + k) = 2 * k + a := by omega
  rw [ht] at hp
  have ha : orbit a (2 ^ a) = 1 ∧ wt a (2 ^ a) = 0 := by
    simpa only [Nat.mul_one] using power_two_path a 1
  have hc : orbit (2 * k + a) (2 ^ a) = 1 ∧
      wt (2 * k + a) (2 ^ a) = k := by
    rw [orbit_add, weight_add_right, ha.1, ha.2, Nat.zero_add]
    exact core_pairs k
  have hreach : orbit (2 * k + a) m = 1 := hp.1.trans hc.1
  have hweight : wt (2 * k + a) m = k := hp.2.trans hc.2
  exact arrival_grade_minimum hm hreach (by rw [hweight])

def CreditBound (A k n : Nat) : Prop := ∀ i, i ≤ k → 2 * wt i n ≤ i + A

def creditRank (n g : Nat) : Nat := 2 ^ (g + 1) * (n - 1) + g

theorem credit_even_decreases {n g : Nat} (hn : 1 < n) (he : n % 2 = 0) :
    creditRank (U n) (g + 1) < creditRank n g := by
  have ho : n % 2 ≠ 1 := by omega
  have hu : 2 * U n = n := by simp only [U, if_neg ho]; omega
  have hs : n - 1 = 2 * (U n - 1) + 1 := by omega
  have hp : 0 < 2 ^ (g + 1) := Nat.pow_pos (by decide)
  simp only [creditRank, Nat.pow_succ] at hp ⊢
  rw [hs]
  simp only [Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  omega

theorem credit_odd_decreases {n g : Nat} (hn : 1 < n) (ho : n % 2 = 1) :
    creditRank (U n) g < creditRank n (g + 1) := by
  have hu : U n - 1 ≤ 2 * (n - 1) := by simp only [U, ho, ↓reduceIte]; omega
  have h := Nat.mul_le_mul_left (2 ^ (g + 1)) hu
  simp only [creditRank, Nat.pow_succ, Nat.mul_assoc] at h ⊢
  omega

/-- A prefix avoiding one cannot outlast its available integer rank. -/
theorem credit_avoiding_length : ∀ k n A, 0 < n → CreditBound A k n →
    (∀ i, i < k → orbit i n ≠ 1) → k ≤ creditRank n A
  | 0, _, _, _, _, _ => Nat.zero_le _
  | k + 1, n, A, hn, hc, hno => by
    have hn1 : 1 < n := by have := hno 0 (by omega); simp only [orbit] at this; omega
    have hpos : 0 < U n := grade_orbit_positive 1 n hn
    have ht : ∀ i, i < k → orbit i (U n) ≠ 1 := by
      intro i hi
      exact hno (i + 1) (by omega)
    by_cases ho : n % 2 = 1
    · have ha : 0 < A := by
        have h := hc 1 (by omega)
        simp only [wt, ho] at h
        omega
      have htail : CreditBound (A - 1) k (U n) := by
        intro i hi
        have h := hc (i + 1) (by omega)
        simp only [wt, ho] at h
        omega
      have ih := credit_avoiding_length k (U n) (A - 1) hpos htail ht
      have hr := credit_odd_decreases (g := A - 1) hn1 ho
      have he : A - 1 + 1 = A := by omega
      rw [he] at hr
      omega
    · have hz : n % 2 = 0 := by omega
      have htail : CreditBound (A + 1) k (U n) := by
        intro i hi
        have h := hc (i + 1) (by omega)
        simp only [wt, hz] at h
        omega
      have ih := credit_avoiding_length k (U n) (A + 1) hpos htail ht
      have hr := credit_even_decreases (g := A) hn1 hz
      omega

theorem bounded_credit_reaches {n A : Nat} (hn : 0 < n)
    (hc : ∀ k, 2 * wt k n ≤ k + A) :
    ∃ t, t ≤ creditRank n A ∧ orbit t n = 1 := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ i, i < creditRank n A + 1 → orbit i n ≠ 1 := by
    intro i hi he
    exact h ⟨i, by omega, he⟩
  have hb := credit_avoiding_length (creditRank n A + 1) n A hn
    (fun i _ => hc i) hno
  omega

theorem finite_credit_reaches {n A : Nat} (hn : 0 < n)
    (hc : CreditBound A (creditRank n A + 1) n) :
    ∃ t, t ≤ creditRank n A ∧ orbit t n = 1 := by
  apply Classical.byContradiction
  intro h
  have hno : ∀ i, i < creditRank n A + 1 → orbit i n ≠ 1 := by
    intro i hi he
    exact h ⟨i, by omega, he⟩
  have hb := credit_avoiding_length (creditRank n A + 1) n A hn hc hno
  omega

/-- A nonconvergent source would exceed each proposed credit by a bounded time. -/
theorem nonconvergent_credit_witness {n : Nat} (hn : 0 < n)
    (hbad : ¬ OrdinaryCollatz.ReachesOne n) (A : Nat) :
    ∃ k, k ≤ creditRank n A + 1 ∧ k + A < 2 * wt k n := by
  apply Classical.byContradiction
  intro h
  have hc : CreditBound A (creditRank n A + 1) n := by
    intro k hk
    by_cases hw : 2 * wt k n ≤ k + A
    · exact hw
    · exact False.elim (h ⟨k, hk, by omega⟩)
  obtain ⟨t, _, ht⟩ := finite_credit_reaches hn hc
  exact hbad ((grade_reaches_bridge n).mpr ⟨t, ht⟩)

theorem grade_all_odd_prefix : ∀ k q, 0 < q →
    orbit k (2 ^ k * q - 1) = 3 ^ k * q - 1 ∧
    wt k (2 ^ k * q - 1) = k
  | 0, q, _ => by simp [orbit, wt]
  | k + 1, q, hq => by
    have hp : 0 < 2 ^ k * q := Nat.mul_pos (Nat.pow_pos (by decide)) hq
    have he : 2 ^ (k + 1) * q = 2 * (2 ^ k * q) := by
      rw [Nat.pow_succ]
      ac_rfl
    have ho : (2 ^ (k + 1) * q - 1) % 2 = 1 := by rw [he]; omega
    have hu : U (2 ^ (k + 1) * q - 1) = 2 ^ k * (3 * q) - 1 := by
      simp only [U, if_pos ho]
      rw [he]
      have hm : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by ac_rfl
      rw [hm]
      omega
    have ih := grade_all_odd_prefix k (3 * q) (by omega)
    simp only [orbit, wt, ho, hu, ih.1, ih.2]
    constructor
    · rw [Nat.pow_succ]
      simp only [Nat.mul_assoc]
    · omega

theorem all_odd_credit_lower {k q A : Nat} (hq : 0 < q)
    (hc : CreditBound A k (2 ^ k * q - 1)) : k ≤ A := by
  have h := hc k (Nat.le_refl k)
  rw [(grade_all_odd_prefix k q hq).2] at h
  omega

theorem arrival_credit_bound {n T : Nat} (hT : orbit T n = 1) :
    ∀ k, 2 * wt k n ≤ k + (T + 1) := by
  intro k
  by_cases hk : k ≤ T
  · have := weight_le_length k n
    omega
  · have hkt : T ≤ k := by omega
    have h := arrival_extension hT (k - T)
    have hw := weight_le_length T n
    have he : T + (k - T) = k := Nat.add_sub_of_le hkt
    rw [he] at h
    have hc := h.1
    unfold StandardCore at hc
    omega

/-- This is an equivalence, not an assertion of the unproved bound on the right. -/
theorem reaches_iff_bounded_credit {n : Nat} (hn : 0 < n) :
    OrdinaryCollatz.ReachesOne n ↔ ∃ A, ∀ k, 2 * wt k n ≤ k + A := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := (grade_reaches_bridge n).mp h
    exact ⟨T + 1, arrival_credit_bound hT⟩
  · rintro ⟨A, hA⟩
    obtain ⟨t, _, ht⟩ := bounded_credit_reaches hn hA
    exact (grade_reaches_bridge n).mpr ⟨t, ht⟩

theorem conjecture_iff_bounded_credit : OrdinaryCollatz.Conjecture ↔
    ∀ n, 0 < n → ∃ A, ∀ k, 2 * wt k n ≤ k + A := by
  constructor
  · intro h n hn
    exact (reaches_iff_bounded_credit hn).mp (h n hn)
  · intro h n hn
    exact (reaches_iff_bounded_credit hn).mpr (h n hn)

theorem grade_coalescence_transfer {n m a b : Nat}
    (h : orbit a n = orbit b m) (hm : OrdinaryCollatz.ReachesOne m) :
    OrdinaryCollatz.ReachesOne n := by
  rw [grade_ordinary_bridge, grade_ordinary_bridge] at h
  obtain ⟨i, _, _, hi⟩ := OrdinaryCollatz.shortcut_iteration_simulation a n
  obtain ⟨j, _, _, hj⟩ := OrdinaryCollatz.shortcut_iteration_simulation b m
  have hc := OrdinaryCollatz.reaches_after_iterate j m hm
  rw [hj, ← h, ← hi] at hc
  exact OrdinaryCollatz.reaches_of_iterate hc

theorem core_phase_pair : ∀ k,
    (orbit k 1 = 1 ∧ orbit k 2 = 2) ∨ (orbit k 1 = 2 ∧ orbit k 2 = 1)
  | 0 => by decide
  | k + 1 => by
    have h1 : U 1 = 2 := rfl
    have h2 : U 2 = 1 := rfl
    simp only [orbit, h1, h2]
    rcases core_phase_pair k with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

/-- Keeping a common clock but allowing unequal odd counts loses no generality. -/
theorem conjecture_iff_same_clock_descent : OrdinaryCollatz.Conjecture ↔
    ∀ n, 2 < n → ∃ m, 0 < m ∧ m < n ∧ ∃ k, orbit k n = orbit k m := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := (grade_reaches_bridge n).mp (hc n (by omega))
    rcases core_phase_pair k with h | h
    · exact ⟨1, by omega, by omega, k, hk.trans h.1.symm⟩
    · exact ⟨2, by omega, by omega, k, hk.trans h.2.symm⟩
  · intro hd n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · subst n
        exact OrdinaryCollatz.reaches_one
      by_cases h2 : n = 2
      · subst n
        exact (grade_reaches_bridge 2).mpr ⟨1, by decide⟩
      obtain ⟨m, hm, hmn, k, hk⟩ := hd n (by omega)
      exact grade_coalescence_transfer hk (ih m hmn hm)

/-- Alternatively, keep equal odd counts and allow the two clocks to differ. -/
theorem conjecture_iff_equal_weight_descent : OrdinaryCollatz.Conjecture ↔
    ∀ n, 1 < n → ∃ m, 0 < m ∧ m < n ∧ ∃ a b,
      orbit a n = orbit b m ∧ wt a n = wt b m := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := (grade_reaches_bridge n).mp (hc n (by omega))
    have hp := core_pairs (wt k n)
    exact ⟨1, by omega, hn, k, 2 * wt k n, hk.trans hp.1.symm, hp.2.symm⟩
  · intro hd n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · subst n
        exact OrdinaryCollatz.reaches_one
      obtain ⟨m, hm, hmn, a, b, hab, _⟩ := hd n (by omega)
      exact grade_coalescence_transfer hab (ih m hmn hm)

#print axioms dyadic_envelope
#print axioms equal_weight_iff_arrival_grade
#print axioms meeting_grade_balance
#print axioms common_clock_27_needs_six
#print axioms equal_weight_27_needs_twelve
#print axioms sharp_27_meetings
#print axioms arrival_grade_minimum
#print axioms power_two_mate_minimum
#print axioms credit_even_decreases
#print axioms credit_odd_decreases
#print axioms bounded_credit_reaches
#print axioms finite_credit_reaches
#print axioms nonconvergent_credit_witness
#print axioms all_odd_credit_lower
#print axioms reaches_iff_bounded_credit
#print axioms conjecture_iff_bounded_credit
#print axioms conjecture_iff_same_clock_descent
#print axioms conjecture_iff_equal_weight_descent

end CollatzPacking
