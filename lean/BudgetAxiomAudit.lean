/-
  Refutation of the added `odd_steps_certificate` axiom in the public
  CollatzLayerA v8.1 source, inspected on 2026-10-08:
  https://github.com/AIDoctrine/CollatzLayerA/blob/main/CollatzLayerA_v8_1_FINAL.lean

  This file does not import that source or its axioms. Its ordinary map
  and odd-step count use the same defining equations. Finite evaluations
  use `decide`, checked by the kernel, rather than native evaluation.

  The witness refutes the bounded-budget axiom, NOT Collatz: it reaches 1.
  Check with standalone Lean 4.33.1: lean lean/BudgetAxiomAudit.lean
-/

namespace BudgetAxiomAudit

def step (n : Nat) : Nat := if n % 2 = 0 then n / 2 else 3 * n + 1

def iterate : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => iterate k (step n)

def oddSteps : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 1 then 1 else 0) + oddSteps k (step n)

def ClaimedCertificate : Prop :=
  ∀ n : Nat, n ≥ 2 ^ 71 → n % 2 = 1 → n % 4 = 3 →
    ∃ k : Nat, 0 < k ∧ k ≤ 200 ∧ oddSteps k n ≤ 44 ∧
      71 ≤ k - oddSteps k n

def witness : Nat := 2 ^ 111 - 1

theorem witness_large : 2 ^ 109 ≤ witness := by decide

theorem witness_eligible : 2 ^ 71 ≤ witness ∧ witness % 2 = 1 ∧
    witness % 4 = 3 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem witness_counts : ∀ k : Fin 201,
    oddSteps k.val witness = (k.val + 1) / 2 := by decide

theorem no_budget_at_witness (k : Nat) (hk : k ≤ 200) :
    ¬ (oddSteps k witness ≤ 44 ∧ 71 ≤ k - oddSteps k witness) := by
  have h := witness_counts ⟨k, by omega⟩
  simp only at h
  omega

theorem claimed_certificate_false : ¬ ClaimedCertificate := by
  intro h
  obtain ⟨k, _, hk, ho, he⟩ := h witness witness_eligible.1
    witness_eligible.2.1 witness_eligible.2.2
  exact no_budget_at_witness k hk ⟨ho, he⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem witness_reaches_one : iterate 1476 witness = 1 := by decide

#print axioms witness_large
#print axioms witness_eligible
#print axioms witness_counts
#print axioms no_budget_at_witness
#print axioms claimed_certificate_false
#print axioms witness_reaches_one

end BudgetAxiomAudit
