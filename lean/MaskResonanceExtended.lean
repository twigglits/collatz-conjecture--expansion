import MaskResonance

/-
  Extend the exact full-mask denominator cover to 10^4000.
  Reuse the existing kernel checker, not the old finite certificate.
  The real logarithm enclosure and cycle application remain written.

  lean -o /tmp/collatz-explicit-log/MaskResonance.olean lean/MaskResonance.lean
  LEAN_PATH=/tmp/collatz-explicit-log lean lean/MaskResonanceExtended.lean
-/
namespace MaskResonanceExtended
open MaskResonance

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def extendedBits : Nat := 32768
def extendedTerms : Nat := 16384
def logTwo : Nat := dyadicSum 3 extendedTerms extendedBits
def logThree : Nat := dyadicSum 2 extendedTerms extendedBits
def extendedLower : Fraction := ⟨logTwo, logThree+extendedTerms+1⟩
def extendedUpper : Fraction := ⟨logTwo+extendedTerms+1, logThree⟩
def extendedCandidates : List Bracket :=
  brackets ((commonCF 20000 extendedLower extendedUpper).drop 1) false ⟨0,1,1,0⟩

def ExtendedLogArithmetic : Prop :=
  0 < logTwo ∧ 0 < logThree ∧
  extendedLower.num*extendedUpper.den < extendedUpper.num*extendedLower.den ∧
  2^(extendedBits+1) < (2*extendedTerms+1)*(2^2-1)*2^(2*extendedTerms-1) ∧
  2^(extendedBits+1) < (2*extendedTerms+1)*(3^2-1)*3^(2*extendedTerms-1)

instance : Decidable ExtendedLogArithmetic := inferInstanceAs (Decidable
  (0 < logTwo ∧ 0 < logThree ∧
   extendedLower.num*extendedUpper.den < extendedUpper.num*extendedLower.den ∧
   2^(extendedBits+1) < (2*extendedTerms+1)*(2^2-1)*2^(2*extendedTerms-1) ∧
   2^(extendedBits+1) < (2*extendedTerms+1)*(3^2-1)*3^(2*extendedTerms-1)))

theorem extended_log_arithmetic : ExtendedLogArithmetic := by native_decide

theorem extended_cover_verified :
    coverCheck extendedLower extendedUpper (10^4000+1) (2^21) extendedCandidates = true := by
  native_decide

theorem extended_denominator_cover (N : Nat) (hlo : 2^21 ≤ N) (hhi : N ≤ 10^4000) :
    ∃ f s m, s ≤ N ∧ N < f.b+f.d ∧ Good extendedLower extendedUpper s m f :=
  coverCheck_sound extendedLower extendedUpper (10^4000+1) (2^21)
    extendedCandidates extended_cover_verified N hlo (by omega)

#print axioms extended_log_arithmetic
#print axioms extended_cover_verified
#print axioms extended_denominator_cover
end MaskResonanceExtended
