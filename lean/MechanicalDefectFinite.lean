/-
  Finite arithmetic certificates for one adjacent swap of phase-zero lower
  mechanical binary words. Standalone Lean 4; no Mathlib.
  Check: lean lean/MechanicalDefectFinite.lean

  The generic Boolean-checker soundness is kernel proved. The two concrete
  finite ranges use native_decide. The statements concern exactly the scalar
  inequality and numerator remainders defined below. The analytic height bound,
  factor-complexity estimate, primitivity, rotation coverage, and their Collatz
  application are not imported or claimed proved by this finite file.
-/
namespace MechanicalDefectFinite

def denominator (N p : Nat) : Nat := 2 ^ N - 3 ^ p

def eligible (N p : Nat) : Prop := 0 < p ∧ p < N ∧ 0 < denominator N p

instance (N p : Nat) : Decidable (eligible N p) := inferInstanceAs
  (Decidable (0 < p ∧ p < N ∧ 0 < denominator N p))

/-- Lower mechanical bits at phase zero; finite checks only use 0 < p < N. -/
def mechanicalBit (N p i : Nat) : Bool := decide (i * p / N < (i + 1) * p / N)

def mechanicalWord (N p : Nat) : List Bool := (List.range N).map (mechanicalBit N p)

/-- Returns the affine numerator and 3 raised to the number of true bits. -/
def affine : List Bool → Nat × Nat
  | [] => (0, 1)
  | bit :: tail =>
    let rest := affine tail
    ((if bit then rest.2 else 0) + 2 * rest.1,
      if bit then 3 * rest.2 else rest.2)

def numerator (word : List Bool) : Nat := (affine word).1

/-- Swaps sites j and (j+1) mod length, including the cyclic boundary. -/
def adjacentSwap (word : List Bool) (j : Nat) : List Bool :=
  let next := (j + 1) % word.length
  (List.range word.length).map fun i =>
    if i = j then word[next]! else if i = next then word[j]! else word[i]!

def ScalarExcluded (N p : Nat) : Prop :=
  3 * p * 2 ^ N ≤ denominator N p * 2 ^ ((N - 3) / 2)

instance (N p : Nat) : Decidable (ScalarExcluded N p) := inferInstanceAs
  (Decidable (3 * p * 2 ^ N ≤ denominator N p * 2 ^ ((N - 3) / 2)))

def scalarCheck (N p : Nat) : Bool := decide (ScalarExcluded N p)

def SwapExcluded (N p j : Nat) : Prop :=
  let word := mechanicalWord N p
  word[j]! = word[(j + 1) % N]! ∨
    numerator (adjacentSwap word j) % denominator N p ≠ 0

instance (N p j : Nat) : Decidable (SwapExcluded N p j) := inferInstanceAs
  (Decidable ((mechanicalWord N p)[j]! = (mechanicalWord N p)[(j + 1) % N]! ∨
    numerator (adjacentSwap (mechanicalWord N p) j) % denominator N p ≠ 0))

def SwapsExcluded (N p : Nat) : Prop := ∀ j, j < N → SwapExcluded N p j

def swapsCheck (N p : Nat) : Bool :=
  (List.range N).all fun j => decide (SwapExcluded N p j)

theorem swapsCheck_sound (N p : Nat) (hc : swapsCheck N p = true) : SwapsExcluded N p := by
  intro j hj
  exact of_decide_eq_true (List.all_eq_true.mp hc j (List.mem_range.mpr hj))

theorem excluded_swap_not_divisible (N p j : Nat) (hs : SwapsExcluded N p)
    (hj : j < N)
    (hdiff : (mechanicalWord N p)[j]! ≠ (mechanicalWord N p)[(j + 1) % N]!) :
    ¬ denominator N p ∣ numerator (adjacentSwap (mechanicalWord N p) j) := by
  intro hd
  rcases hs j hj with heq | hmod
  · exact hdiff heq
  · exact hmod (Nat.mod_eq_zero_of_dvd hd)

/-- A range is start ≤ N < start+count; each row checks every 0 ≤ p < N.
    Ineligible p (including zero or nonpositive denominator) are skipped. -/
def checkedRange (start count : Nat) (check : Nat → Nat → Bool) : Bool :=
  (List.range count).all fun offset =>
    let N := start + offset
    (List.range N).all fun p => if eligible N p then check N p else true

theorem checkedRange_sound (start count : Nat) (check : Nat → Nat → Bool)
    (hc : checkedRange start count check = true)
    (N p : Nat) (hlo : start ≤ N) (hhi : N < start + count)
    (he : eligible N p) : check N p = true := by
  have hoffset : N - start ∈ List.range count := List.mem_range.mpr (by omega)
  have hrow := List.all_eq_true.mp hc (N - start) hoffset
  have hsum : start + (N - start) = N := by omega
  simp only [hsum] at hrow
  have hp : p < N := he.2.1
  have hcell := List.all_eq_true.mp hrow p (List.mem_range.mpr hp)
  simpa only [if_pos he] using hcell

/-- All positive-denominator count pairs for N=32,...,255 satisfy the
    exact scalar exclusion inequality. -/
theorem scalar_32_255 : checkedRange 32 224 scalarCheck = true := by native_decide

/-- Every cyclic adjacent unequal-bit swap for N=3,...,31 has nonzero
    numerator remainder, for every positive-denominator count pair. -/
theorem swaps_3_31 : checkedRange 3 29 swapsCheck = true := by native_decide

/-- The final arithmetic disjunction, covering all N=3,...,255 and 0<p<N
    with positive denominator. It does not assert the external mathematical
    implications of either branch. -/
theorem arithmetic_exclusion_3_255 (N p : Nat) (hlo : 3 ≤ N) (hhi : N ≤ 255)
    (he : eligible N p) : ScalarExcluded N p ∨ SwapsExcluded N p := by
  by_cases hsmall : N < 32
  · right
    apply swapsCheck_sound
    exact checkedRange_sound 3 29 swapsCheck swaps_3_31 N p hlo (by omega) he
  · left
    apply of_decide_eq_true
    exact checkedRange_sound 32 224 scalarCheck scalar_32_255 N p (by omega) (by omega) he

theorem scalar_or_no_integral_swap (N p : Nat) (hlo : 3 ≤ N) (hhi : N < 256)
    (he : eligible N p) :
    ScalarExcluded N p ∨ ∀ j, j < N →
      (mechanicalWord N p)[j]! ≠ (mechanicalWord N p)[(j + 1) % N]! →
      ¬ denominator N p ∣ numerator (adjacentSwap (mechanicalWord N p) j) := by
  rcases arithmetic_exclusion_3_255 N p hlo (by omega) he with hs | he
  · exact Or.inl hs
  · exact Or.inr (fun j hj hdiff => excluded_swap_not_divisible N p j he hj hdiff)

#print axioms swapsCheck_sound
#print axioms checkedRange_sound
#print axioms scalar_32_255
#print axioms swaps_3_31
#print axioms arithmetic_exclusion_3_255
#print axioms scalar_or_no_integral_swap

end MechanicalDefectFinite
