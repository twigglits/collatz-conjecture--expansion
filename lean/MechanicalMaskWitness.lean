/-
  An explicit rational-cycle word beyond half-Hamming distance 31 from every
  matching mechanical phase. Standalone Lean 4.33.1; no Mathlib.
  Check: lean lean/MechanicalMaskWitness.lean

  Construction: start with the lower mechanical halving word of length 193 and
  total 306. Swap the cyclic 21 pairs at the zero-based starts listed below.
  The list has 43 entries, including the boundary pair starting at 192.

  Discovery provenance only: enumerate all 80 cyclic 21 starts in increasing
  order. SHAKE256 of the UTF-8 string
    collatz-rational-mask/v1/193/shake_subset_21_to_12
  gives first ten bytes 092faffdec155f05d8b0. Select candidate t when bit t%8
  of byte t/8 is one, with bits numbered least-significant first. The explicit
  list is the certificate input; no theorem trusts or invokes this generator.

  The concrete arithmetic and finite catalog checks use native_decide. The
  generic extraction of universal statements and nondivisibility is kernel
  proved. Printed axioms expose the native checks. The file certifies its exact
  finite definitions, including the positive affine numerator and denominator;
  it does not formalize the general rational-cycle correspondence, mechanical
  phase classification, cyclic-prefix consequence, or integer-cycle exclusion.
  In fact the numerator is NOT divisible by the denominator.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace MechanicalMaskWitness

/-- Exact supporting inequalities for the written general-family estimates. -/
theorem mask_family_arithmetic : 3 ^ 17 < 2 ^ 27 ∧ (17 : Nat) ^ 8 < 2 ^ 33 := by
  decide

def k : Nat := 193
def N : Nat := 306

/-- Zero-based starts of the selected cyclic 21 pairs. -/
def selected : List Nat :=
  [1, 8, 20, 23, 25, 27, 32, 40, 42, 44, 47, 52, 56, 59, 64, 66,
   68, 71, 73, 76, 83, 85, 90, 93, 95, 97, 102, 107, 117, 119, 122,
   124, 126, 131, 136, 141, 163, 165, 170, 172, 184, 187, 192]

def baseHalf (i : Nat) : Nat := (i + 1) * N / k - i * N / k

def editedHalf (i : Nat) : Nat :=
  if selected.contains i then 1
  else if selected.contains ((i + k - 1) % k) then 2 else baseHalf i

def baseHalves : List Nat := (List.range k).map baseHalf
def halves : List Nat := (List.range k).map editedHalf

/-- A halving exponent h expands into one true bit followed by h-1 false bits. -/
def word : List Bool := halves.flatMap fun h => true :: List.replicate (h - 1) false
def wordArray : Array Bool := word.toArray

def mechanicalBit (i : Nat) : Bool := decide (i * k / N < (i + 1) * k / N)
/-- Here a is a cyclic rotation index, not an intercept in the floor formula. -/
def mechanicalPhase (a : Nat) : List Bool :=
  (List.range N).map fun i => mechanicalBit ((i + a) % N)

def hamming (a : Nat) : Nat :=
  ((List.range N).filter fun i =>
    wordArray[i]! != mechanicalBit ((i + a) % N)).length

def distance (a : Nat) : Nat := hamming a / 2

/-- Actual Boolean factors are compared, so no hash or numeric encoding is trusted. -/
def factor (a : Nat) : List Bool :=
  (List.range 32).map fun i => wordArray[(a + i) % N]!

def factorCount : Nat := ((List.range N).map factor).eraseDups.length

def prefixDifference (i : Nat) : Int :=
  ((halves.take i).sum : Int) - ((baseHalves.take i).sum : Int)

def prefixBandCheck : Bool := (List.range (k + 1)).all fun i =>
  decide (0 ≤ prefixDifference i ∧ prefixDifference i ≤ 1)

/-- The shortcut affine numerator together with 3 to the number of true bits. -/
def affine : List Bool → Nat × Nat
  | [] => (0, 1)
  | bit :: tail =>
    let rest := affine tail
    ((if bit then rest.2 else 0) + 2 * rest.1,
      if bit then 3 * rest.2 else rest.2)

def W : Nat := (affine word).1
def D : Nat := 2 ^ N - 3 ^ k

theorem critical_counts :
    2 ^ 305 < 3 ^ k ∧ 3 ^ k < 2 ^ N ∧ Nat.gcd k N = 1 := by native_decide

theorem selected_valid : selected.length = 43 ∧ selected.Nodup ∧
    selected.all (fun j => decide
      (j < k ∧ baseHalf j = 2 ∧ baseHalf ((j + 1) % k) = 1)) = true := by
  native_decide

theorem word_counts :
    halves.length = k ∧ halves.sum = N ∧ word.length = N ∧ word.count true = k := by
  native_decide

theorem matching_phase_check :
    (List.range N).all (fun a => decide ((mechanicalPhase a).count true = k)) = true := by
  native_decide

theorem every_phase_matches (a : Nat) (ha : a < N) :
    (mechanicalPhase a).count true = k := by
  exact of_decide_eq_true
    (List.all_eq_true.mp matching_phase_check a (List.mem_range.mpr ha))

theorem all_phase_check :
    (List.range N).all (fun a => decide (70 ≤ hamming a)) = true := by native_decide

theorem every_phase_far (a : Nat) (ha : a < N) : 35 ≤ distance a := by
  have hr : 70 ≤ hamming a := of_decide_eq_true
    (List.all_eq_true.mp all_phase_check a (List.mem_range.mpr ha))
  unfold distance
  omega

theorem attaining_rotation : hamming 104 = 70 ∧ distance 104 = 35 := by native_decide

theorem factor_count_32 : factorCount = 289 := by native_decide

theorem band_check : prefixBandCheck = true := by native_decide

theorem prefix_band (i : Nat) (hi : i ≤ k) :
    0 ≤ prefixDifference i ∧ prefixDifference i ≤ 1 := by
  exact of_decide_eq_true
    (List.all_eq_true.mp band_check i (List.mem_range.mpr (by omega)))

theorem band_is_exact :
    prefixDifference 0 = 0 ∧ prefixDifference 1 = 1 ∧ prefixDifference k = 0 := by
  native_decide

theorem denominator_positive : 0 < D := by native_decide
theorem numerator_positive : 0 < W := by native_decide
theorem numerator_remainder : W % D ≠ 0 := by native_decide

theorem not_integral : ¬ D ∣ W := by
  intro hd
  exact numerator_remainder (Nat.mod_eq_zero_of_dvd hd)

#print axioms critical_counts
#print axioms mask_family_arithmetic
#print axioms selected_valid
#print axioms word_counts
#print axioms every_phase_matches
#print axioms every_phase_far
#print axioms attaining_rotation
#print axioms factor_count_32
#print axioms prefix_band
#print axioms band_is_exact
#print axioms denominator_positive
#print axioms numerator_positive
#print axioms not_integral

end MechanicalMaskWitness
