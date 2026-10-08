/-
  Arithmetic certificates for pumping a Collatz parity block backward.
  The finite automaton and its language are not formalized in this file.
  Import CollatzPeriodic through a temporary LEAN_PATH.
-/
import CollatzPeriodic

namespace BuchiArithmetic

def defect (A D : Nat) (B x : Int) : Int := ((D : Int) - A) * x - B

/-- r inverse steps of the affine block (A*x+B)/D, all over integers.
    No parity assumptions: every genuine block prehistory satisfies this. -/
def Backwards (A D : Nat) (B : Int) : Nat → Int → Int → Prop
  | 0, m, n => n = m
  | r + 1, m, n => ∃ z, (A : Int) * z = (D : Int) * m - B ∧
      Backwards A D B r z n

theorem defect_step {A D : Nat} {B x y : Int}
    (h : (A : Int) * y = (D : Int) * x - B) :
    (A : Int) * defect A D B y = (D : Int) * defect A D B x := by
  unfold defect
  grind

theorem backward_transport {A D : Nat} {B : Int} : ∀ r m n,
    Backwards A D B r m n →
    (A : Int) ^ r * defect A D B n = (D : Int) ^ r * defect A D B m
  | 0, m, n, h => by simpa [Backwards] using congrArg (defect A D B) h
  | r + 1, m, n, h => by
    obtain ⟨z, hz, hzn⟩ := h
    have ih := backward_transport r z n hzn
    have hs := defect_step hz
    simp only [Int.pow_succ]
    grind

/-- The number of repeatable inverse blocks consumes exact powers of A. -/
theorem backward_divisibility {A D r : Nat} {B m n : Int}
    (hcop : Nat.gcd A D = 1) (h : Backwards A D B r m n) :
    A ^ r ∣ (defect A D B m).natAbs := by
  have heq := congrArg Int.natAbs (backward_transport r m n h)
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at heq
  have hd : A ^ r ∣ D ^ r * (defect A D B m).natAbs := by
    rw [← heq]
    exact Nat.dvd_mul_right _ _
  have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
  rw [Nat.pow_gcd_pow_of_gcd_eq_one hcop, Nat.one_mul] at hc
  exact hc

/-- A finite cutoff suffices: beyond it the endpoint must be a fixed point. -/
theorem backward_cutoff {A D r : Nat} {B m n : Int}
    (hcop : Nat.gcd A D = 1) (h : Backwards A D B r m n)
    (hlarge : (defect A D B m).natAbs < A ^ r) :
    (D : Int) * m = (A : Int) * m + B := by
  have hd := backward_divisibility hcop h
  have hz : (defect A D B m).natAbs = 0 := by
    by_cases hn : (defect A D B m).natAbs = 0
    · exact hn
    · have := Nat.le_of_dvd (by omega : 0 < (defect A D B m).natAbs) hd
      omega
  have he := Int.natAbs_eq_zero.mp hz
  unfold defect at he
  grind

/-- The prehistories need not be chosen consistently across lengths. -/
theorem arbitrary_pumping_fixed {A D : Nat} {B m : Int}
    (hA : 1 < A) (hcop : Nat.gcd A D = 1)
    (h : ∀ r, ∃ n, Backwards A D B r m n) :
    (D : Int) * m = (A : Int) * m + B := by
  have hd : ∀ r, A ^ r ∣ (defect A D B m).natAbs := by
    intro r
    obtain ⟨n, hn⟩ := h r
    exact backward_divisibility hcop hn
  have hz := CollatzPeriodic.zero_of_all_powers_dvd hA hd
  have he := Int.natAbs_eq_zero.mp hz
  unfold defect at he
  grind

theorem collatz_pumping_fixed {j ell : Nat} {B m : Int} (hj : 0 < j)
    (h : ∀ r, ∃ n, Backwards (3 ^ j) (2 ^ ell) B r m n) :
    ((2 ^ ell : Nat) : Int) * m = ((3 ^ j : Nat) : Int) * m + B := by
  exact arbitrary_pumping_fixed (Nat.one_lt_pow (by omega) (by decide))
    (Nat.pow_gcd_pow_of_gcd_eq_one (by decide : Nat.gcd 3 2 = 1)) h

/-- Forward iteration is backward iteration with A,D swapped and B negated.
    The finite forward obstruction consumes denominator powers instead. -/
theorem forward_divisibility {A D r : Nat} {B m n : Int}
    (hcop : Nat.gcd D A = 1) (h : Backwards D A (-B) r m n) :
    D ^ r ∣ (defect A D B m).natAbs := by
  have hd := backward_divisibility hcop h
  have he : defect D A (-B) m = -defect A D B m := by
    unfold defect
    grind
  simpa only [he, Int.natAbs_neg] using hd

/-- The tail after k odd steps from 2^k-1 permits no additional odd step
    prepended to the same complete odd prefix, even over arbitrary integers. -/
theorem no_extra_odd_predecessors {k r : Nat} {n : Int} (hkr : k < r) :
    ¬ Backwards 3 2 1 r ((3 : Int) ^ k - 1) n := by
  intro h
  have hd := backward_divisibility (by decide : Nat.gcd 3 2 = 1) h
  have he : defect 3 2 1 ((3 : Int) ^ k - 1) = -(3 : Int) ^ k := by
    unfold defect
    grind
  rw [he] at hd
  simp only [Int.natAbs_neg, Int.natAbs_pow] at hd
  have hl : (3 : Nat) ^ r ≤ 3 ^ k := Nat.le_of_dvd (Nat.pow_pos (by decide)) hd
  have hh : (3 : Nat) ^ k < 3 ^ r := Nat.pow_lt_pow_right (by decide) hkr
  omega

/-- After one even step, the valuation attached to the odd-block defect
    can be arbitrarily large although the even-block valuation was one.
    The valuation interpretation is written; these exact identities are
    sufficient to establish it without numerical logarithms. -/
theorem unbounded_counter_reset (k : Nat) :
    let x := 2 ^ (k + 1) - 1
    0 < x ∧ x % 2 = 1 ∧ (2 * x) % 4 = 2 ∧
      (2 * x) / 2 = x ∧ x + 1 = 2 ^ (k + 1) := by
  have hp : 0 < (2 : Nat) ^ k := Nat.pow_pos (by decide)
  have he : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
    rw [Nat.pow_succ, Nat.mul_comm]
  dsimp
  rw [he]
  omega

def shortcut (n : Nat) : Nat :=
  if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

/-- A positive expanding 110 block whose endpoint valuations of n and n+1
    at 2 and 3 coincide. The residue assertions encode the exact valuations. -/
theorem expanding_same_features (s : Nat) (hs : 0 < s) :
    let n := 192 * s - 5
    let m := 216 * s - 5
    shortcut n = 288 * s - 7 ∧
    shortcut (288 * s - 7) = 432 * s - 10 ∧
    shortcut (432 * s - 10) = m ∧
    2 < n ∧ n < m ∧ n % 8 = 3 ∧ m % 8 = 3 ∧
    n % 3 = 1 ∧ m % 3 = 1 := by
  dsimp
  have h1 : (192 * s - 5) % 2 = 1 := by omega
  have h2 : (288 * s - 7) % 2 = 1 := by omega
  have h3 : (432 * s - 10) % 2 ≠ 1 := by omega
  simp only [shortcut, if_pos h1, if_pos h2, if_neg h3]
  omega

/-- Taking the family parameter divisible by M defeats any additional
    correction depending only on the residue modulo that fixed M. -/
theorem expanding_same_residue (s M : Nat) (hs : 0 < s) (hM : M ∣ s) :
    (192 * s - 5) % M = (216 * s - 5) % M := by
  have he : 216 * s - 5 = (192 * s - 5) + 24 * s := by omega
  obtain ⟨t, ht⟩ := hM
  rw [he, Nat.add_mod, ht]
  simp [Nat.mul_mod]

/-- Any proposed integer rank which is no smaller at the larger endpoint
    must fail strict descent on at least one of these three real steps. -/
theorem rank_failure_on_expanding_block (s : Nat) (hs : 0 < s)
    (rank : Nat → Int)
    (hsize : rank (192 * s - 5) ≤ rank (216 * s - 5)) :
    ¬ (rank (shortcut (192 * s - 5)) < rank (192 * s - 5) ∧
       rank (shortcut (288 * s - 7)) < rank (288 * s - 7) ∧
       rank (shortcut (432 * s - 10)) < rank (432 * s - 10)) := by
  obtain ⟨h1, h2, h3, _⟩ := expanding_same_features s hs
  rw [h1, h2, h3]
  omega

#print axioms backward_transport
#print axioms backward_divisibility
#print axioms backward_cutoff
#print axioms arbitrary_pumping_fixed
#print axioms collatz_pumping_fixed
#print axioms forward_divisibility
#print axioms no_extra_odd_predecessors
#print axioms unbounded_counter_reset
#print axioms expanding_same_features
#print axioms expanding_same_residue
#print axioms rank_failure_on_expanding_block

end BuchiArithmetic
