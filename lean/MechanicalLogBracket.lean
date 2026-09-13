/-
  Exact rational comparisons used by the written mechanical-word argument.
  Standalone Lean 4; no Mathlib.
  Check: lean lean/MechanicalLogBracket.lean

  Only finite rational arithmetic is certified here. No logarithm, infinite
  series, analytic remainder bound, Farey theorem, or Matveev theorem is
  defined or claimed proved by this file. The finite sum has 64 terms.
-/
namespace MechanicalLogBracket

/-- An unreduced nonnegative fraction. Every denominator used in the final
    certificate is explicitly checked positive. -/
structure Fraction where
  num : Nat
  den : Nat
deriving DecidableEq, Repr

def add (x y : Fraction) : Fraction :=
  ⟨x.num * y.den + y.num * x.den, x.den * y.den⟩

def divide (x y : Fraction) : Fraction := ⟨x.num * y.den, x.den * y.num⟩

def Less (x y : Fraction) : Prop := x.num * y.den < y.num * x.den

instance (x y : Fraction) : Decidable (Less x y) := inferInstanceAs
  (Decidable (x.num * y.den < y.num * x.den))

/-- S_q(n) = 2 sum_{j<n} 1/((2j+1) q^(2j+1)); q denotes 1/z. -/
def partialSum (q : Nat) : Nat → Fraction
  | 0 => ⟨0, 1⟩
  | n + 1 => add (partialSum q n) ⟨2, (2 * n + 1) * q ^ (2 * n + 1)⟩

/-- At n=64, the rational expression 2 z^129/(129(1-z^2)),
    evaluated at z=1/q, equals 2/(129(q^2-1)q^127). -/
def remainder (q : Nat) : Fraction := ⟨2, 129 * (q ^ 2 - 1) * q ^ 127⟩

def S3 : Fraction := partialSum 3 64
def S2 : Fraction := partialSum 2 64
def R3 : Fraction := remainder 3
def R2 : Fraction := remainder 2

def L : Fraction := divide S3 (add S2 R2)
def U : Fraction := divide (add S3 R3) S2

def largeLower : Fraction := ⟨137528045312, 217976794617⟩
def largeUpper : Fraction := ⟨753110839881, 1193652440098⟩
def tinyLower : Fraction := ⟨147, 233⟩
def tinyUpper : Fraction := ⟨53, 84⟩

def ExactComparisons : Prop :=
  0 < S3.den ∧ 0 < S2.den ∧ 0 < R3.den ∧ 0 < R2.den ∧
  0 < L.den ∧ 0 < U.den ∧
  0 < largeLower.den ∧ 0 < largeUpper.den ∧
  0 < tinyLower.den ∧ 0 < tinyUpper.den ∧
  Less (add largeLower ⟨1, 2 ^ 98⟩) L ∧ Less U largeUpper ∧
  Less (add tinyLower ⟨1, 36000⟩) L ∧ Less U tinyUpper

instance : Decidable ExactComparisons := inferInstanceAs (Decidable
  (0 < S3.den ∧ 0 < S2.den ∧ 0 < R3.den ∧ 0 < R2.den ∧
   0 < L.den ∧ 0 < U.den ∧
   0 < largeLower.den ∧ 0 < largeUpper.den ∧
   0 < tinyLower.den ∧ 0 < tinyUpper.den ∧
   Less (add largeLower ⟨1, 2 ^ 98⟩) L ∧ Less U largeUpper ∧
   Less (add tinyLower ⟨1, 36000⟩) L ∧ Less U tinyUpper))

def rationalCheck : Bool := decide ExactComparisons

theorem rationalCheck_sound (hc : rationalCheck = true) : ExactComparisons :=
  of_decide_eq_true hc

theorem rationalCheck_verified : rationalCheck = true := by native_decide

theorem exact_comparisons : ExactComparisons := rationalCheck_sound rationalCheck_verified

/-- Addition form fixes the sign of each determinant without Nat subtraction. -/
theorem large_farey_arithmetic :
    753110839881 * 217976794617 = 137528045312 * 1193652440098 + 1 ∧
    10 ^ 12 < 217976794617 + 1193652440098 := by decide

theorem tiny_farey_arithmetic : 53 * 233 = 147 * 84 + 1 ∧ 255 < 233 + 84 := by decide

theorem matveev_numeric_inputs : 2 ^ 9 < 23 ^ 2 ∧ 602494200 < 10 ^ 9 := by decide

/-- A second neighboring pair supports the larger distance-budget reduction. -/
def extendedLower : Fraction := ⟨5409303924479, 8573543875303⟩
def extendedUpper : Fraction := ⟨6162414764360, 9767196315401⟩

def ExtendedComparisons : Prop :=
  0 < extendedLower.den ∧ 0 < extendedUpper.den ∧
  Less (add extendedLower ⟨1, 2 ^ 98⟩) L ∧ Less U extendedUpper

instance : Decidable ExtendedComparisons := inferInstanceAs (Decidable
  (0 < extendedLower.den ∧ 0 < extendedUpper.den ∧
   Less (add extendedLower ⟨1, 2 ^ 98⟩) L ∧ Less U extendedUpper))

theorem extended_comparisons : ExtendedComparisons := by native_decide

theorem extended_farey_arithmetic :
    6162414764360 * 8573543875303 = 5409303924479 * 9767196315401 + 1 ∧
    10 ^ 13 < 8573543875303 + 9767196315401 := by decide

#print axioms extended_comparisons
#print axioms extended_farey_arithmetic

#print axioms rationalCheck_sound
#print axioms rationalCheck_verified
#print axioms exact_comparisons
#print axioms large_farey_arithmetic
#print axioms tiny_farey_arithmetic
#print axioms matveev_numeric_inputs

end MechanicalLogBracket
