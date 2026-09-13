import MaskSubsetDecoder

/-
  Finite certificates excluding EVERY independent 21-to-12 subset of the
  explicitly constructed mechanical halving words below. The decoder's
  completeness and the integer-target reduction are imported kernel proofs.
  Only the displayed finite conjunctions use native_decide.

  Build the dependency as described in MaskSubsetDecoder.lean, then run:
    LEAN_PATH=/tmp/collatz-mask-lean lean -o /tmp/collatz-mask-lean/MaskSubsetDecoder.olean lean/MaskSubsetDecoder.lean
    LEAN_PATH=/tmp/collatz-mask-lean lean lean/MaskSubsetFinite.lean

  Mechanical words use lower-floor increments and are cut at their first 2.
  Reconstruction, both counts, the exact quotient interval, positivity, and
  rejection of every quotient target are all checked. No integer-cycle
  classification, minimum-height claim, or full Collatz conclusion is asserted.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace MaskSubsetFinite

open MechanicalMaskArithmetic MaskSubsetDecoder

def mechanical (k N : Nat) : List Nat :=
  (List.range k).map fun i => (i + 1) * N / k - i * N / k

def cut (k N : Nat) : Nat := (mechanical k N).findIdx (· == 2)

def rotated (k N : Nat) : List Nat :=
  (mechanical k N).drop (cut k N) ++ (mechanical k N).take (cut k N)

/-- Reject malformed token decompositions, rather than silently skipping a
    symbol. The separate reconstruction check also guards the chosen cut. -/
def tokenize : List Nat → Option (List Bool)
  | [] => some []
  | 2 :: 1 :: rest => (tokenize rest).map (true :: ·)
  | 2 :: rest => (tokenize rest).map (false :: ·)
  | _ => none

def family (k N : Nat) : List Bool := (tokenize (rotated k N)).getD []

def quotientLow (bs : List Bool) : Nat :=
  3 * totalCoefficients (unselected bs) / denominator (unselected bs)

def quotientHigh (bs : List Bool) : Nat :=
  4 * totalCoefficients (unselected bs) / denominator (unselected bs)

/-- Both chosen totals are the smallest integers above k log2(3), as
    expressed without logarithms. Coprime counts also preclude a nontrivial
    repetition of either finite halving word. -/
theorem critical_counts :
    2 ^ 305 < 3 ^ 193 ∧ 3 ^ 193 < 2 ^ 306 ∧
    2 ^ 4700 < 3 ^ 2966 ∧ 3 ^ 2966 < 2 ^ 4701 ∧
    Nat.gcd 193 306 = 1 ∧ Nat.gcd 2966 4701 = 1 := by native_decide

theorem checked_193 :
    cut 193 306 = 1 ∧
    tokenize (rotated 193 306) = some (family 193 306) ∧
    base (unselected (family 193 306)) = rotated 193 306 ∧
    (base (unselected (family 193 306))).length = 193 ∧
    (base (unselected (family 193 306))).sum = 306 ∧
    ((family 193 306).filter id).length = 80 ∧
    quotientLow (family 193 306) = 737 ∧
    quotientHigh (family 193 306) = 983 ∧
    0 < denominator (unselected (family 193 306)) ∧
    excludes (family 193 306) = true := by native_decide

/-- Every one of the 80 independent pair choices is quantified through its
    skeleton. The conclusion covers all masks, including the unedited word. -/
theorem all_193_masks_nonintegral (ts : List Token)
    (hs : skeleton ts = family 193 306) :
    ¬ denominator ts ∣ weight (mask ts) :=
  excludes_sound _ checked_193.2.2.2.2.2.2.2.2.1
    checked_193.2.2.2.2.2.2.2.2.2 ts hs

theorem checked_2966 :
    cut 2966 4701 = 1 ∧
    tokenize (rotated 2966 4701) = some (family 2966 4701) ∧
    base (unselected (family 2966 4701)) = rotated 2966 4701 ∧
    (base (unselected (family 2966 4701))).length = 2966 ∧
    (base (unselected (family 2966 4701))).sum = 4701 ∧
    ((family 2966 4701).filter id).length = 1231 ∧
    quotientLow (family 2966 4701) = 946661 ∧
    quotientHigh (family 2966 4701) = 1262215 ∧
    0 < denominator (unselected (family 2966 4701)) ∧
    excludes (family 2966 4701) = true := by native_decide

theorem all_2966_masks_nonintegral (ts : List Token)
    (hs : skeleton ts = family 2966 4701) :
    ¬ denominator ts ∣ weight (mask ts) :=
  excludes_sound _ checked_2966.2.2.2.2.2.2.2.2.1
    checked_2966.2.2.2.2.2.2.2.2.2 ts hs

#print axioms checked_193
#print axioms critical_counts
#print axioms all_193_masks_nonintegral
#print axioms checked_2966
#print axioms all_2966_masks_nonintegral

end MaskSubsetFinite
