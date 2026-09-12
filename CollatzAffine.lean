/-
  Exact affine thresholds for ordinary Collatz shortcut residue classes.
  Standalone Lean 4: no Mathlib, admitted proofs, or native evaluation.
  Check: lean CollatzAffine.lean
-/
namespace CollatzAffine

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbit k (U n)

def wt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + wt k (U n)

/-- Exact residue-class formula; the same identity as CollatzFrontier.U_affine. -/
theorem affine : ∀ (k q s : Nat),
    orbit k (2 ^ k * q + s) = 3 ^ wt k s * q + orbit k s
  | 0, _, _ => rfl
  | k + 1, q, s => by
    have hsplit : 2 ^ (k + 1) * q + s = 2 * (2 ^ k * q) + s := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    by_cases hpar : s % 2 = 1
    · -- odd residue: U(2^{k+1} q + s) = 2^k·(3q) + U s, weight gains 1
      have hw : wt (k + 1) s = 1 + wt k (U s) := by
        show s % 2 + wt k (U s) = 1 + wt k (U s)
        omega
      have h3m : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := Nat.mul_left_comm (2 ^ k) 3 q
      have hU1 : U (2 ^ (k + 1) * q + s) = 2 ^ k * (3 * q) + U s := by
        rw [hsplit, h3m]
        unfold U
        rw [if_pos (show (2 * (2 ^ k * q) + s) % 2 = 1 by omega), if_pos hpar]
        omega
      show orbit k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + orbit k (U s)
      rw [hU1, affine k (3 * q) (U s), hw, Nat.pow_add, Nat.pow_one,
          Nat.mul_left_comm (3 ^ wt k (U s)) 3 q,
          Nat.mul_assoc 3 (3 ^ wt k (U s)) q]
    · -- even residue: U(2^{k+1} q + s) = 2^k·q + U s, weight unchanged
      have hw : wt (k + 1) s = wt k (U s) := by
        show s % 2 + wt k (U s) = wt k (U s)
        omega
      have hU1 : U (2 ^ (k + 1) * q + s) = 2 ^ k * q + U s := by
        rw [hsplit]
        unfold U
        rw [if_neg (show ¬(2 * (2 ^ k * q) + s) % 2 = 1 by omega), if_neg hpar]
        omega
      show orbit k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + orbit k (U s)
      rw [hU1, affine k q (U s), hw]

/-- Nonnegative additive corrections ensure the linear coefficient is a lower bound. -/
theorem coefficient_lower_bound : ∀ k n, 3 ^ wt k n * n ≤ 2 ^ k * orbit k n
  | 0, n => by simp [wt, orbit]
  | k + 1, n => by
    have ih := coefficient_lower_bound k (U n)
    have hstep : 3 ^ (n % 2) * n ≤ 2 * U n := by
      by_cases hn : n % 2 = 1
      · unfold U
        rw [if_pos hn, hn, Nat.pow_one]
        omega
      · have he : n % 2 = 0 := by omega
        unfold U
        rw [if_neg hn, he, Nat.pow_zero, Nat.one_mul]
        omega
    have hmul := Nat.mul_le_mul_left (3 ^ wt k (U n)) hstep
    have htail := Nat.mul_le_mul_left 2 ih
    show 3 ^ (n % 2 + wt k (U n)) * n ≤ 2 ^ (k + 1) * orbit k (U n)
    rw [Nat.pow_add, Nat.pow_succ]
    have he0 : 3 ^ (n % 2) * 3 ^ wt k (U n) * n =
        3 ^ wt k (U n) * (3 ^ (n % 2) * n) := by
      rw [Nat.mul_comm (3 ^ (n % 2)), Nat.mul_assoc]
    have he1 : 3 ^ wt k (U n) * (2 * U n) = 2 * (3 ^ wt k (U n) * U n) :=
      Nat.mul_left_comm _ _ _
    have he2 : 2 ^ k * 2 * orbit k (U n) = 2 * (2 ^ k * orbit k (U n)) := by
      rw [Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    rw [he0, he2]
    rw [he1] at hmul
    exact Nat.le_trans hmul htail

/-- Actual descent is impossible while the multiplicative coefficient is at least 1. -/
theorem descent_requires_slope_drop {k n : Nat} (hd : orbit k n < n) :
    3 ^ wt k n < 2 ^ k := by
  have hm := Nat.mul_lt_mul_of_pos_left (k := 2 ^ k) hd (Nat.pow_pos (by decide : 0 < 2))
  have hl := coefficient_lower_bound k n
  exact Nat.lt_of_mul_lt_mul_right (Nat.lt_of_le_of_lt hl hm)

/-- Integer additive numerator in U^k(n)=(3^wt*n+numerator)/2^k.
    coefficient_lower_bound guarantees subtraction here does not truncate. -/
def numerator (k n : Nat) : Nat := 2 ^ k * orbit k n - 3 ^ wt k n * n

theorem orbit_equation (k n : Nat) :
    2 ^ k * orbit k n = 3 ^ wt k n * n + numerator k n := by
  unfold numerator
  have := Nat.sub_add_cancel (coefficient_lower_bound k n)
  omega

/-- The additive numerator is constant over a residue class. This form is
    scaled by 2^k and uses the residue's coefficient, avoiding division. -/
theorem affine_numerator (k r q : Nat) :
    2 ^ k * orbit k (2 ^ k * q + r) =
      3 ^ wt k r * (2 ^ k * q + r) + numerator k r := by
  rw [affine, Nat.mul_add, orbit_equation, Nat.mul_add]
  have heq : 2 ^ k * (3 ^ wt k r * q) = 3 ^ wt k r * (2 ^ k * q) :=
    Nat.mul_left_comm _ _ _
  rw [heq]
  omega

/-- Sharp n-threshold in integer form, under an exact affine equation. -/
theorem scaled_descent_iff {A M B n y : Nat} (hM : 0 < M) (hAM : A ≤ M)
    (heq : M * y = A * n + B) : y < n ↔ B < (M - A) * n := by
  have hmul := Nat.mul_lt_mul_left (a := M) (b := y) (c := n) hM
  have hsplit : M * n = A * n + (M - A) * n := by
    rw [← Nat.add_mul, Nat.add_comm A, Nat.sub_add_cancel hAM]
  rw [heq, hsplit] at hmul
  omega

/-- Equivalently n must exceed floor(B/(M-A)); equality does not descend. -/
theorem scaled_threshold_iff {A M B n y : Nat} (hAM : A < M)
    (heq : M * y = A * n + B) : y < n ↔ B / (M - A) < n := by
  rw [scaled_descent_iff (by omega) (Nat.le_of_lt hAM) heq]
  have hdiv := Nat.div_lt_iff_lt_mul (x := B) (y := n) (by omega : 0 < M - A)
  rw [Nat.mul_comm n (M - A)] at hdiv
  exact hdiv.symm

/-- Sharp actual-orbit test for every n with a contracting coefficient. -/
theorem orbit_threshold_iff {k n : Nat} (hslope : 3 ^ wt k n < 2 ^ k) :
    orbit k n < n ↔ numerator k n / (2 ^ k - 3 ^ wt k n) < n :=
  scaled_threshold_iff hslope (orbit_equation k n)

/-- The sharp start-value threshold for an entire contracting residue class. -/
theorem residue_start_threshold_iff {k r q : Nat} (hslope : 3 ^ wt k r < 2 ^ k) :
    orbit k (2 ^ k * q + r) < 2 ^ k * q + r ↔
      numerator k r / (2 ^ k - 3 ^ wt k r) < 2 ^ k * q + r :=
  scaled_threshold_iff hslope (affine_numerator k r q)

/-- Exact subtraction-free descent test for an affine residue-class image. -/
theorem affine_descent_iff {A M b r q : Nat} (hAM : A ≤ M) :
    A * q + b < M * q + r ↔ b < (M - A) * q + r := by
  have heq : M * q = (M - A) * q + A * q := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hAM]
  rw [heq]
  omega

/-- One endpoint check covers the entire tail of a residue class. -/
theorem affine_descent_mono {A M b r q0 q : Nat}
    (hAM : A ≤ M) (hbase : A * q0 + b < M * q0 + r) (hq : q0 ≤ q) :
    A * q + b < M * q + r := by
  have heq : q = q0 + (q - q0) := by omega
  have hmul := Nat.mul_le_mul_right (q - q0) hAM
  rw [heq, Nat.mul_add, Nat.mul_add]
  omega

/-- Sharp first admissible q when A<M. The b<r branch avoids truncated
    subtraction turning an already-descending q=0 into the false threshold 1. -/
def threshold (A M b r : Nat) : Nat :=
  if b < r then 0 else (b - r) / (M - A) + 1

/-- Exact threshold characterization, including every exceptional small q. -/
theorem threshold_iff {A M b r q : Nat} (hAM : A < M) :
    A * q + b < M * q + r ↔ threshold A M b r ≤ q := by
  rw [affine_descent_iff (Nat.le_of_lt hAM)]
  unfold threshold
  by_cases hbr : b < r
  · rw [if_pos hbr]
    omega
  · rw [if_neg hbr]
    have hd : 0 < M - A := by omega
    have hi := Nat.div_lt_iff_lt_mul (x := b - r) (y := q) hd
    rw [Nat.mul_comm q (M - A)] at hi
    omega

/-- Direct all-integer application of an endpoint certificate. -/
theorem residue_descent {k r q0 q : Nat}
    (hslope : 3 ^ wt k r ≤ 2 ^ k)
    (hbase : 3 ^ wt k r * q0 + orbit k r < 2 ^ k * q0 + r)
    (hq : q0 ≤ q) : orbit k (2 ^ k * q + r) < 2 ^ k * q + r := by
  rw [affine]
  exact affine_descent_mono hslope hbase hq

/-- The computed threshold is necessary and sufficient within the entire class. -/
theorem residue_threshold_iff {k r q : Nat} (hslope : 3 ^ wt k r < 2 ^ k) :
    orbit k (2 ^ k * q + r) < 2 ^ k * q + r ↔
      threshold (3 ^ wt k r) (2 ^ k) (orbit k r) r ≤ q := by
  rw [affine]
  exact threshold_iff hslope

/-- Certificate format for symbolic class tails; all supplied quantities are
    recomputed in Lean instead of trusting a sieve's A or b fields. -/
structure ClassCertificate where
  k : Nat
  r : Nat
  q0 : Nat

def checkClass (c : ClassCertificate) : Bool :=
  decide (c.r < 2 ^ c.k ∧ 3 ^ wt c.k c.r ≤ 2 ^ c.k ∧
    3 ^ wt c.k c.r * c.q0 + orbit c.k c.r < 2 ^ c.k * c.q0 + c.r)

/-- A true finite checker result proves infinitely many actual descents. -/
theorem checkClass_sound (c : ClassCertificate) (hc : checkClass c = true) :
    ∀ q, c.q0 ≤ q → orbit c.k (2 ^ c.k * q + c.r) < 2 ^ c.k * q + c.r := by
  have h := of_decide_eq_true hc
  intro q hq
  exact residue_descent h.2.1 h.2.2 hq

/-- A certificate covering every class member greater than 1 may omit q=0
    exactly when its residue is 0 or 1. No finite trajectory check is needed. -/
def checkWholeClass (c : ClassCertificate) : Bool :=
  checkClass c && decide (c.q0 = 0 ∨ (c.q0 = 1 ∧ c.r ≤ 1))

theorem checkWholeClass_sound (c : ClassCertificate) (hc : checkWholeClass c = true) :
    ∀ q, 1 < 2 ^ c.k * q + c.r →
      orbit c.k (2 ^ c.k * q + c.r) < 2 ^ c.k * q + c.r := by
  have h := Bool.and_eq_true_iff.mp hc
  have hq0 := of_decide_eq_true h.2
  intro q hn
  apply checkClass_sound c h.1 q
  have hq : q = 0 ∨ 1 ≤ q := by omega
  rcases hq with he | he
  · rw [he, Nat.mul_zero, Nat.zero_add] at hn
    omega
  · omega

def Descends (n : Nat) : Prop := ∃ j, orbit j n < n

/-- For a contracting residue class, proving descent for all its n>1 is
    equivalent to checking only the finitely many q below the sharp threshold. -/
theorem class_descent_iff_finite_exceptions {k r : Nat}
    (hslope : 3 ^ wt k r < 2 ^ k) :
    (∀ q, 1 < 2 ^ k * q + r → Descends (2 ^ k * q + r)) ↔
    (∀ q, q < threshold (3 ^ wt k r) (2 ^ k) (orbit k r) r →
      1 < 2 ^ k * q + r → Descends (2 ^ k * q + r)) := by
  constructor
  · intro h q _ hn
    exact h q hn
  · intro h q hn
    by_cases hq : q < threshold (3 ^ wt k r) (2 ^ k) (orbit k r) r
    · exact h q hq hn
    · exact ⟨k, residue_threshold_iff hslope |>.mpr (by omega)⟩

/-- Bounded checker for the finite exceptional set q<q0. It checks descent
    itself, and treats only starts 0 and 1 as outside the n>1 obligation. -/
def checkExceptions (c : ClassCertificate) (fuel : Nat) : Bool :=
  (List.range c.q0).all fun q =>
    let n := 2 ^ c.k * q + c.r
    decide (n ≤ 1) || (List.range (fuel + 1)).any (fun j => decide (orbit j n < n))

def checkCompleteClass (c : ClassCertificate) (fuel : Nat) : Bool :=
  checkClass c && checkExceptions c fuel

/-- A finite exceptional-set check plus one symbolic tail certificate proves
    descent for every n>1 in a complete infinite residue class. -/
theorem checkCompleteClass_sound (c : ClassCertificate) (fuel : Nat)
    (hc : checkCompleteClass c fuel = true) :
    ∀ q, 1 < 2 ^ c.k * q + c.r → Descends (2 ^ c.k * q + c.r) := by
  have h := Bool.and_eq_true_iff.mp hc
  intro q hn
  by_cases hq : q < c.q0
  · have he := h.2
    unfold checkExceptions at he
    have hp := List.all_eq_true.mp he q (List.mem_range.mpr hq)
    have hor := Bool.or_eq_true_iff.mp hp
    rcases hor with hlo | hdesc
    · have hlo' := of_decide_eq_true hlo
      omega
    · obtain ⟨j, _, hj⟩ := List.any_eq_true.mp hdesc
      exact ⟨j, of_decide_eq_true hj⟩
  · exact ⟨c.k, checkClass_sound c h.1 q (by omega)⟩

/-- First crossing of the multiplicative slope below 1. -/
def FirstSlopeDrop (k n : Nat) : Prop :=
  3 ^ wt k n < 2 ^ k ∧ ∀ j, j < k → 2 ^ j ≤ 3 ^ wt j n

/-- The first-crossing claim is Terras' coefficient stopping-time conjecture.
    It is recorded as a proposition, not asserted as a theorem or assumption
    of any result in this file. -/
def CoefficientStoppingTimeClaim : Prop :=
  ∀ n k, 1 < n → FirstSlopeDrop k n → orbit k n < n

/-- For 7 the first slope drop really occurs at 7, before the later growth. -/
theorem example_first_drop : FirstSlopeDrop 7 7 ∧ orbit 7 7 = 5 := by
  have hp : ∀ j : Fin 7, 2 ^ j.val ≤ 3 ^ wt j.val 7 := by decide
  exact ⟨⟨by decide, fun j hj => hp ⟨j, hj⟩⟩, by decide⟩

/-- The n>1 restriction in the coefficient stopping-time claim is essential. -/
theorem one_first_drop_exception : FirstSlopeDrop 2 1 ∧ orbit 2 1 = 1 := by
  have hp : ∀ j : Fin 2, 2 ^ j.val ≤ 3 ^ wt j.val 1 := by decide
  exact ⟨⟨by decide, fun j hj => hp ⟨j, hj⟩⟩, by decide⟩

/-- A negative example to the shortcut 'slope<1 implies actual descent'.
    This is NOT a first-slope-drop counterexample: 7 has already descended
    to 5 at step 7, then grows to 8 at step 8. -/
theorem slope_only_counterexample :
    3 ^ wt 8 7 < 2 ^ 8 ∧ orbit 8 7 = 8 ∧ ¬ orbit 8 7 < 7 := by decide

/-- Its exact class threshold: only q=0 fails descent at this particular step. -/
theorem example_threshold : threshold (3 ^ wt 8 7) (2 ^ 8) (orbit 8 7) 7 = 1 := by decide

theorem example_infinite_class (q : Nat) (hq : 1 ≤ q) :
    orbit 8 (256 * q + 7) < 256 * q + 7 :=
  checkClass_sound ⟨8, 7, 1⟩ (by decide) q hq

/-- The exceptional representative 7 descends at step 7; all higher members
    of its class descend at step 8. Both parts are checked finitely here. -/
theorem example_complete_class (q : Nat) : Descends (256 * q + 7) := by
  exact checkCompleteClass_sound ⟨8, 7, 1⟩ 7 (by decide) q (by change 1 < 256 * q + 7; omega)

#print axioms affine
#print axioms descent_requires_slope_drop
#print axioms orbit_equation
#print axioms residue_start_threshold_iff
#print axioms orbit_threshold_iff
#print axioms affine_descent_mono
#print axioms threshold_iff
#print axioms checkClass_sound
#print axioms checkWholeClass_sound
#print axioms checkCompleteClass_sound
#print axioms class_descent_iff_finite_exceptions
#print axioms example_first_drop
#print axioms one_first_drop_exception
#print axioms slope_only_counterexample
#print axioms example_infinite_class
#print axioms example_complete_class

end CollatzAffine
