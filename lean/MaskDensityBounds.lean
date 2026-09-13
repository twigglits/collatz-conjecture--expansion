/-
  Kernel-checked finite inputs to docs/MASK-DENSITY.md.
  The entropy and window-count arguments remain written proofs.
  Requires MaskTransitionBounds.olean on LEAN_PATH.
-/
import MaskTransitionBounds

namespace MaskDensityBounds

set_option exponentiation.threshold 10000
set_option maxRecDepth 20000

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (words n).flatMap fun bs => [false :: bs, true :: bs]

def count (n j : Nat) : Nat :=
  ((words n).filter fun bs => MaskTransitionBounds.rises bs == j).length

theorem block_distributions :
    count 2 0 = 3 ∧ count 2 1 = 1 ∧ (words 2).length = 4 ∧
    count 3 0 = 4 ∧ count 3 1 = 4 ∧ (words 3).length = 8 := by decide

theorem generating_function_input : (513 : Nat) ^ 256 < 2 ^ 2305 := by decide

theorem density_arithmetic :
    3 * 8192 = 4 * 6144 ∧
    (9 * 2048 + 6144) * 512 = 6144 * 2048 ∧
    19 * 128 + 25 = 2457 ∧ 26 * 2457 < 5 * 12800 ∧
    21 * 2457 + 2 * 12800 < 7 * 12800 ∧
    4 * 2457 < 12800 ∧ 26 * 2457 = 2 * 31941 ∧
    32000 - 31941 = 59 := by decide

theorem density_cutoff :
    30 * 32000 < 59 * 16384 ∧ 9216 * 16384 < (2 : Nat) ^ 30 ∧
    64000 < 59 * 16384 := by decide

#print axioms block_distributions
#print axioms generating_function_input
#print axioms density_arithmetic
#print axioms density_cutoff
end MaskDensityBounds
