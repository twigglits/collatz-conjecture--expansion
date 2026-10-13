/-
  Dyadic balanced refinements inside the known Collatz basin.
  Integer grade transport, strict odd-step contraction before one,
  and injective finite parity coding. No universal convergence claim.
-/
import CoalescenceGrades

namespace DyadicCoalescenceDefects
open CollatzPacking

def HasGrade (n : Nat) (g : Int) : Prop :=
  ∃ t, orbit t n = 1 ∧ (t : Int) - 2 * (wt t n : Int) = g

def SafeChild (n m : Nat) : Prop :=
  m = 2 * n ∨ (m = 2 * n + 1 ∧ ∃ t, EqualWeightMate t (2 * n) (2 * n + 1))

theorem grade_unique {n : Nat} {g h : Int} (hg : HasGrade n g) (hh : HasGrade n h) : g = h := by
  obtain ⟨t, ht, htg⟩ := hg
  obtain ⟨s, hs, hsg⟩ := hh
  have hb := (equal_weight_iff_arrival_grade ht hs).mp ⟨0, ⟨rfl, rfl⟩⟩
  omega

theorem grade_one : HasGrade 1 0 := by exact ⟨0, rfl, rfl⟩

theorem grade_double {n : Nat} {g : Int} (h : HasGrade n g) : HasGrade (2 * n) (g + 1) := by
  obtain ⟨t, ht, hg⟩ := h
  refine ⟨t + 1, ?_, ?_⟩
  · simpa only [orbit, grade_even_step] using ht
  · have he : 2 * n % 2 = 0 := by omega
    simp only [wt, he, Nat.zero_add, grade_even_step]
    omega

theorem grade_transfer {n m : Nat} {g : Int} (h : HasGrade n g)
    (hm : ∃ t, EqualWeightMate t n m) : HasGrade m g := by
  obtain ⟨t, ht, hg⟩ := h
  obtain ⟨k, hk⟩ := hm
  have hr : OrdinaryCollatz.ReachesOne n := (grade_reaches_bridge n).mpr ⟨t, ht⟩
  have hs := grade_coalescence_transfer hk.1 hr
  obtain ⟨s, hs⟩ := (grade_reaches_bridge m).mp hs
  have hb := (equal_weight_iff_arrival_grade ht hs).mp ⟨k, hk⟩
  exact ⟨s, hs, by omega⟩

theorem safe_child_grade {n m : Nat} {g : Int} (h : HasGrade n g) (hs : SafeChild n m) :
    HasGrade m (g + 1) := by
  rcases hs with he | ⟨he, hm⟩
  · subst m
    exact grade_double h
  · subst m
    exact grade_transfer (grade_double h) hm

theorem safe_chain_grade (v : Nat → Nat) (g : Int) (h0 : HasGrade (v 0) g)
    (k : Nat) (hs : ∀ j, j < k → SafeChild (v j) (v (j + 1))) :
    HasGrade (v k) (g + k) := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have h := safe_child_grade (ih (fun j hj => hs j (by omega))) (hs k (by omega))
    simpa only [Int.natCast_add, Int.natCast_one, Int.add_assoc] using h

def AvoidOne (t n : Nat) : Prop := ∀ j, j < t → orbit j n ≠ 1

theorem avoid_one_tail {t n : Nat} (h : AvoidOne (t + 1) n) : AvoidOne t (U n) := by
  intro j hj
  exact h (j + 1) (by omega)

/-- Every odd input before the first visit to one is at least three. -/
theorem strict_odd_step {n : Nat} (_hn : 0 < n) (h1 : n ≠ 1) (ho : n % 2 = 1) :
    3 * U n ≤ 5 * n := by
  simp only [U, if_pos ho]
  omega

/-- A rational contraction, valid only before the first visit to one. -/
theorem strict_prefix_envelope : ∀ t n, 0 < n → AvoidOne t n →
    3 ^ wt t n * 2 ^ t * orbit t n ≤ 10 ^ wt t n * n
  | 0, n, _, _ => by simp [wt, orbit]
  | t + 1, n, hn, ha => by
    have ih := strict_prefix_envelope t (U n) (grade_orbit_positive 1 n hn) (avoid_one_tail ha)
    have h1 : n ≠ 1 := ha 0 (by omega)
    by_cases ho : n % 2 = 1
    · have hu := strict_odd_step hn h1 ho
      have hu' : 6 * U n ≤ 10 * n := by omega
      calc
        3 ^ wt (t + 1) n * 2 ^ (t + 1) * orbit (t + 1) n =
            6 * (3 ^ wt t (U n) * 2 ^ t * orbit t (U n)) := by
          simp only [wt, orbit, ho, Nat.pow_add, Nat.pow_succ]
          rw [show 6 = 3 * 2 from rfl]
          ac_rfl
        _ ≤ 6 * (10 ^ wt t (U n) * U n) := Nat.mul_le_mul_left 6 ih
        _ = 10 ^ wt t (U n) * (6 * U n) := by ac_rfl
        _ ≤ 10 ^ wt t (U n) * (10 * n) := Nat.mul_le_mul_left _ hu'
        _ = 10 ^ wt (t + 1) n * n := by
          simp only [wt, ho, Nat.pow_add, Nat.pow_one]
          ac_rfl
    · have he : n % 2 = 0 := by omega
      have hu : 2 * U n = n := by simp only [U, if_neg ho]; omega
      calc
        3 ^ wt (t + 1) n * 2 ^ (t + 1) * orbit (t + 1) n =
            2 * (3 ^ wt t (U n) * 2 ^ t * orbit t (U n)) := by
          simp only [wt, orbit, he, Nat.zero_add, Nat.pow_succ]
          ac_rfl
        _ ≤ 2 * (10 ^ wt t (U n) * U n) := Nat.mul_le_mul_left 2 ih
        _ = 10 ^ wt (t + 1) n * n := by
          simp only [wt, he, Nat.zero_add]
          calc
            _ = 10 ^ wt t (U n) * (2 * U n) := by ac_rfl
            _ = _ := by rw [hu]

theorem first_arrival_contraction {t n : Nat} (hn : 0 < n) (ha : AvoidOne t n)
    (ht : orbit t n = 1) : 3 ^ wt t n * 2 ^ t ≤ 10 ^ wt t n * n := by
  simpa only [ht, Nat.mul_one] using strict_prefix_envelope t n hn ha

/-- Bounded source size and odd count give a finite word-length bound. -/
theorem arrival_length_bound {t n L K : Nat} (hn : 0 < n) (hN : n ≤ 2 ^ L)
    (ht : orbit t n = 1) (hw : wt t n ≤ K) : t ≤ L + 2 * K := by
  have h := dyadic_envelope t n hn
  rw [ht, Nat.mul_one] at h
  have h' := Nat.le_trans h (Nat.mul_le_mul_left (2 ^ (2 * wt t n)) hN)
  have he : 2 ^ (2 * wt t n) * 2 ^ L = 2 ^ (L + 2 * wt t n) := by
    rw [← Nat.pow_add, Nat.add_comm]
  rw [he] at h'
  have ht' := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp h'
  omega

def parityWord : Nat → Nat → List Nat
  | 0, _ => []
  | t + 1, n => n % 2 :: parityWord t (U n)

theorem parity_word_length : ∀ t n, (parityWord t n).length = t
  | 0, _ => rfl
  | t + 1, n => by simp [parityWord, parity_word_length]

theorem parity_word_sum : ∀ t n, (parityWord t n).sum = wt t n
  | 0, _ => rfl
  | t + 1, n => by simp [parityWord, wt, parity_word_sum]

theorem parity_word_binary : ∀ t n b, b ∈ parityWord t n → b = 0 ∨ b = 1
  | 0, _, _, h => by simp [parityWord] at h
  | t + 1, n, b, h => by
    simp only [parityWord, List.mem_cons] at h
    rcases h with h | h
    · omega
    · exact parity_word_binary t (U n) b h

theorem same_parity_step_injective {n m : Nat} (hp : n % 2 = m % 2) (hu : U n = U m) : n = m := by
  unfold U at hu
  by_cases h : n % 2 = 1
  · rw [if_pos h, if_pos (by omega)] at hu
    omega
  · rw [if_neg h, if_neg (by omega)] at hu
    omega

/-- An endpoint and its full finite parity word determine its source. -/
theorem parity_word_endpoint_injective : ∀ t n m,
    parityWord t n = parityWord t m → orbit t n = orbit t m → n = m
  | 0, _, _, _, h => h
  | t + 1, n, m, hw, he => by
    simp only [parityWord, List.cons.injEq] at hw
    have hu := parity_word_endpoint_injective t (U n) (U m) hw.2 he
    exact same_parity_step_injective hw.1 hu

theorem two_five_le_six (a : Nat) (ha : 4 ≤ a) : 2 * 5 ^ a ≤ 6 ^ a := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  have hp := Nat.pow_le_pow_left (by decide : 5 ≤ 6) b
  have h := Nat.mul_le_mul (by decide : 1250 ≤ 1296) hp
  rw [Nat.pow_add, Nat.pow_add]
  change 2 * (625 * 5 ^ b) ≤ 1296 * 6 ^ b
  rw [← Nat.mul_assoc]
  exact h

/-- A first arrival with the largest possible nonnegative binary grade
    uses at most three odd inputs. This includes every safe descendant of 1. -/
theorem leading_grade_odd_bound {t n k : Nat} (hn : 0 < n) (hN : n < 2 ^ (k + 1))
    (ht : orbit t n = 1) (ha : AvoidOne t n)
    (hg : (t : Int) - 2 * (wt t n : Int) = k) : wt t n ≤ 3 := by
  let a := wt t n
  have ht' : t = k + 2 * a := by dsimp [a]; omega
  have hc := first_arrival_contraction hn ha ht
  change 3 ^ a * 2 ^ t ≤ 10 ^ a * n at hc
  have hm := Nat.mul_lt_mul_of_pos_left hN (Nat.pow_pos (by decide : 0 < 10) (n := a))
  have hlt := Nat.lt_of_le_of_lt hc hm
  have hleft : 3 ^ a * 2 ^ t = 6 ^ a * 2 ^ (k + a) := by
    rw [ht', show 2 * a = a + a by omega, show 6 = 3 * 2 from rfl, Nat.mul_pow]
    simp only [Nat.pow_add]
    ac_rfl
  have hright : 10 ^ a * 2 ^ (k + 1) = (2 * 5 ^ a) * 2 ^ (k + a) := by
    rw [show 10 = 5 * 2 from rfl, Nat.mul_pow]
    simp only [Nat.pow_add, Nat.pow_one]
    ac_rfl
  rw [hleft, hright] at hlt
  have hsmall := Nat.lt_of_mul_lt_mul_right hlt
  by_cases hbig : 4 ≤ a
  · have h := two_five_le_six a hbig
    omega
  · change a ≤ 3
    omega

#print axioms grade_unique
#print axioms grade_one
#print axioms grade_double
#print axioms grade_transfer
#print axioms safe_child_grade
#print axioms safe_chain_grade
#print axioms avoid_one_tail
#print axioms strict_odd_step
#print axioms strict_prefix_envelope
#print axioms first_arrival_contraction
#print axioms arrival_length_bound
#print axioms parity_word_length
#print axioms parity_word_sum
#print axioms parity_word_binary
#print axioms same_parity_step_injective
#print axioms parity_word_endpoint_injective
#print axioms two_five_le_six
#print axioms leading_grade_odd_bound
end DyadicCoalescenceDefects
