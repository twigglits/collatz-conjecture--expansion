/-
  Finite arithmetic for docs/EXPLICIT-LOG-GAP.md. Standalone Lean 4.
  Polynomial identities and interval coefficients use kernel proofs.
  The dyadic logarithm sums use native evaluation, explicitly printed below.
  Integrals, real logarithms, and the all-index denominator argument are written.
-/
namespace ExplicitLogConstants

set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

structure Cubic where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int

def firstUpper : Cubic := ⟨238599375, -49389550, 2960159, -40000⟩
def secondUpper : Cubic := ⟨583743125, 121546950, -7399611, 100000⟩
def firstLower : Cubic := ⟨-595748125, 123472650, -7400397, 100000⟩

theorem integrand_polynomial_identities (t : Int) :
    159*(1225-t)^2-40000*t*(t-25)*(t-49) =
      238599375-49389550*t+2960159*t^2-40000*t^3 ∧
    389*(1225-t)^2+100000*t*(t-25)*(t-49) =
      583743125+121546950*t-7399611*t^2+100000*t^3 ∧
    100000*t*(t-25)*(t-49)-397*(1225-t)^2 =
      -595748125+123472650*t-7400397*t^2+100000*t^3 := by grind

/-- Three times the Bernstein coefficients after t=(a+(b-a)s)/q,
    with the positive denominator q^3 cleared. -/
def bernsteinPositive (p : Cubic) (q a b : Int) : Bool :=
  let h := b-a
  let c0 := p.c0*q^3 + p.c1*a*q^2 + p.c2*a^2*q + p.c3*a^3
  let c1 := h*(p.c1*q^2 + 2*p.c2*a*q + 3*p.c3*a^2)
  let c2 := h^2*(p.c2*q + 3*p.c3*a)
  let c3 := p.c3*h^3
  decide (0 < q ∧ a < b ∧ 0 < 3*c0 ∧ 0 < 3*c0+c1 ∧
    0 < 3*c0+2*c1+c2 ∧ 0 < 3*(c0+c1+c2+c3))

/-- Adjacent entries cover the complete interval between the two endpoints. -/
def checkIntervals (p : Cubic) (q : Int) : List Int → Bool
  | a :: b :: rest => bernsteinPositive p q a b && checkIntervals p q (b :: rest)
  | _ => true

theorem integral_interval_constants :
    checkIntervals firstUpper 64 [0,400,600,650,675,700,800,1600] = true ∧
    checkIntervals secondUpper 2 [50,74,77,80,86,98] = true ∧
    checkIntervals firstLower 400 [4225,4356] = true ∧
    (6*24500 : Nat)*389^300 < 588*397^300 := by decide

theorem bernstein_identity (a b c d s t : Int) :
    3*a*t^3 + 3*(3*a+b)*s*t^2 + 3*(3*a+2*b+c)*s^2*t +
      3*(a+b+c+d)*s^3 =
    3*(a*(s+t)^3 + b*s*(s+t)^2 + c*s^2*(s+t) + d*s^3) := by grind

theorem cubic_substitution (p0 p1 p2 p3 a h q s : Int) :
    p0*q^3 + p1*q^2*(a+h*s) + p2*q*(a+h*s)^2 + p3*(a+h*s)^3 =
    (p0*q^3+p1*a*q^2+p2*a^2*q+p3*a^3) +
      h*(p1*q^2+2*p2*a*q+3*p3*a^2)*s +
      h^2*(p2*q+3*p3*a)*s^2 + p3*h^3*s^3 := by grind

theorem numerator_factorization (u : Int) :
    (u-1)^2*(2*u-3)*(3*u-2)*(3*u-4)*(4*u-3) =
    72-450*u+1153*u^2-1550*u^3+1153*u^4-450*u^5+72*u^6 := by grind

theorem centered_factorization (w : Int) :
    (w-2)^2*(2*w-5)*(3*w-5)*(3*w-7)*(4*w-7) =
    4900-14700*w+18301*w^2-12102*w^3+4483*w^4-882*w^5+72*w^6 := by grind

def numeratorCoefficients : List Int := [72,-450,1153,-1550,1153,-450,72]
def centeredCoefficients : List Int := [4900,-14700,18301,-12102,4483,-882,72]

def weightedDivisible (cs : List Int) (p : Int) (e v : Nat) : Bool :=
  (List.range cs.length).all fun j => decide (p^v ∣ p^(e*j)*cs[j]!)

theorem seed_divisibilities :
    weightedDivisible numeratorCoefficients 2 2 3 = true ∧
    weightedDivisible numeratorCoefficients 2 1 2 = true ∧
    weightedDivisible numeratorCoefficients 3 1 2 = true ∧
    weightedDivisible centeredCoefficients 2 1 2 = true ∧
    weightedDivisible centeredCoefficients 5 1 2 = true ∧
    weightedDivisible centeredCoefficients 7 1 2 = true := by decide

theorem coefficient_and_prime_constants :
    (72*3+450*2+1153 : Nat) = 2269 ∧
    73122192 < 8103*9025 ∧
    2*159^2 < 40000^2*2269^2 ∧
    80^2 = 6400 ∧ 14262 < 180*80 ∧
    101624000+14262 < 101800000 := by decide

theorem coefficient_rational_identity :
    (24^2*(6*19^2+13*5*19+6*5^2)*(12*19^2+25*5*19+12*5^2) : Nat)*9025 =
    73122192*(19^2*14^2*5^2) := by decide

def logFloor (p q : Nat) : Nat := Id.run do
  let mut total := 0
  let mut pn := p
  let mut qn := q
  for j in [:64] do
    total := total + 2^129*pn/((2*j+1)*qn)
    pn := pn*p*p
    qn := qn*q*q
  return total

def tailSmall (p q : Nat) : Prop :=
  0 < p ∧ p < q ∧ 2^129*p^129 < 129*(q^2-p^2)*q^127

instance (p q : Nat) : Decidable (tailSmall p q) := inferInstanceAs
  (Decidable (0 < p ∧ p < q ∧ 2^129*p^129 < 129*(q^2-p^2)*q^127))

def two : Nat := logFloor 1 3
def ratioA : Nat := logFloor 4007 12199
def ratioB : Nat := logFloor 307 943
def ratioC : Nat := logFloor 1 9
def scale : Nat := 2^128
def sigmaUpper : Nat := 250*(13*(two+65)+ratioA+65)+509*scale
def tauLower : Nat := 250*(6*two+ratioB)-509*scale
def tauUpper : Nat := 250*(6*(two+65)+ratioB+65)-509*scale

def LogConstants : Prop :=
  tailSmall 1 3 ∧ tailSmall 4007 12199 ∧ tailSmall 307 943 ∧ tailSmall 1 9 ∧
  509*scale < 250*(6*two+ratioB) ∧ 0 < tauLower ∧ tauUpper < 700*scale ∧
  sigmaUpper < 3000*scale ∧ 125*sigmaUpper < 524*tauLower ∧
  two+65 < scale ∧ scale < 2*two ∧ 9*scale < 4*(3*two+ratioC)

instance : Decidable LogConstants := inferInstanceAs (Decidable
  (tailSmall 1 3 ∧ tailSmall 4007 12199 ∧ tailSmall 307 943 ∧ tailSmall 1 9 ∧
   509*scale < 250*(6*two+ratioB) ∧ 0 < tauLower ∧ tauUpper < 700*scale ∧
   sigmaUpper < 3000*scale ∧ 125*sigmaUpper < 524*tauLower ∧
   two+65 < scale ∧ scale < 2*two ∧ 9*scale < 4*(3*two+ratioC)))

theorem logarithm_constants : LogConstants := by native_decide

theorem cutoff_constants :
    (4000*9 : Nat) = 4*9000 ∧ 14*3200 < 5*9000 ∧ 6524 < 9000 ∧
    19*26 = 500-6 ∧ 2304*12000 < 2^121 ∧ 121*250 < 3*12000 ∧
    500 < 3*12000 ∧ 2*3014 < 10^4000 ∧ 10^4000 < 2^16384 := by decide

theorem covered_denominator_le_product (N b d : Nat) (hb : 0 < b) (hd : 0 < d)
    (hN : N < b+d) : N ≤ b*d := by
  have he : b-1+1 = b := by omega
  have hm : b-1 ≤ (b-1)*d := Nat.le_mul_of_pos_right _ hd
  have hp : b*d = (b-1)*d+d := calc
    b*d = (b-1+1)*d := congrArg (fun x => x*d) he.symm
    _ = (b-1)*d+d := by rw [Nat.add_mul, Nat.one_mul]
  omega

theorem covered_window_large (N m : Nat) (hN : 2^21 ≤ N) (hm : 4*N < 2^m) :
    24 ≤ m := by
  by_cases h : 24 ≤ m
  · exact h
  · have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show m ≤ 23 by omega)
    have he : (2 : Nat)^23 = 4*2^21 := by decide
    omega

theorem sparse_catalog_exponent (m : Nat) (hm : 24 ≤ m) :
    (m+1)+18 < 9*(21*(m+1)/80) := by omega

#print axioms integral_interval_constants
#print axioms integrand_polynomial_identities
#print axioms bernstein_identity
#print axioms cubic_substitution
#print axioms numerator_factorization
#print axioms centered_factorization
#print axioms seed_divisibilities
#print axioms coefficient_and_prime_constants
#print axioms coefficient_rational_identity
#print axioms logarithm_constants
#print axioms cutoff_constants
#print axioms covered_denominator_le_product
#print axioms covered_window_large
#print axioms sparse_catalog_exponent
end ExplicitLogConstants
