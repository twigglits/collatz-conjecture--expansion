import MechanicalMaskArithmetic

/-
  Complete decoder for every subset of disjoint 21-to-12 edits.
  Lean 4, kernel proofs only. Temporary build products keep source directories
  clean. From the repository root, run:
    mkdir -p /tmp/collatz-mask-lean
    lean -o /tmp/collatz-mask-lean/MechanicalMaskArithmetic.olean lean/MechanicalMaskArithmetic.lean
    LEAN_PATH=/tmp/collatz-mask-lean lean lean/MaskSubsetDecoder.lean

  A false skeleton token is the single symbol 2; true is an editable pair 21.
  The decoder tests one integer target, without enumerating its subsets.
  The final finite checker enumerates every possible integer quotient in the
  exact normal form. No mechanical-word classification is assumed.
-/

namespace MaskSubsetDecoder

open MechanicalMaskArithmetic

def skeleton : List Token → List Bool
  | [] => []
  | none :: ts => false :: skeleton ts
  | some _ :: ts => true :: skeleton ts

def unselected : List Bool → List Token
  | [] => []
  | false :: bs => none :: unselected bs
  | true :: bs => some false :: unselected bs

theorem skeleton_unselected (bs : List Bool) : skeleton (unselected bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [unselected, skeleton, ih]

theorem base_skeleton (ts : List Token) :
    base ts = base (unselected (skeleton ts)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [base, unselected, skeleton, ih]

theorem flipped_skeleton (ts : List Token) :
    flipped ts = flipped (unselected (skeleton ts)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => cases t <;> simp [flipped, unselected, skeleton, ih]

theorem C_skeleton (ts : List Token) : C ts = C (unselected (skeleton ts)) := by
  unfold C
  rw [base_skeleton ts, flipped_skeleton ts]

theorem denominator_skeleton (ts : List Token) :
    denominator ts = denominator (unselected (skeleton ts)) := by
  unfold denominator
  rw [base_skeleton ts]

/-- Preparation caches each pair's coefficient before the target scan. -/
def prepare : List Bool → List (Bool × Nat)
  | [] => []
  | b :: bs => (b, 2 * 3 ^ (base (unselected bs)).length) :: prepare bs

/-- At a single token a target must be 4 times the remaining target. At a
    pair it must be either 8 times the remainder, or c plus 8 times it.
    Both residue tests are explicit and short-circuit; c is 2 modulo 4,
    so at most one of the pair branches can pass its residue test. -/
def decode : List (Bool × Nat) → Nat → Bool
  | [], x => x == 0
  | (false, _) :: rest, x => x % 4 == 0 && decode rest (x / 4)
  | (true, c) :: rest, x =>
      (x % 8 == 0 && decode rest (x / 8)) ||
      (decide (c ≤ x) && (x - c) % 8 == 0 && decode rest ((x - c) / 8))

theorem pair_residues_disjoint (n x : Nat) :
    ¬ (x % 8 = 0 ∧ (x - 2 * 3 ^ n) % 8 = 0 ∧ 2 * 3 ^ n ≤ x) := by
  have hp : 3 ^ n % 2 = 1 := by simp [Nat.pow_mod]
  omega

/-- Every accepted target, and only an accepted target, is the exact selected
    coefficient sum of a mask having the specified skeleton. -/
theorem decode_iff (bs : List Bool) (x : Nat) :
    decode (prepare bs) x = true ↔
      ∃ ts, skeleton ts = bs ∧ selectedCoefficients ts = x := by
  induction bs generalizing x with
  | nil =>
    simp only [prepare, decode, beq_iff_eq]
    constructor
    · intro hx
      exact ⟨[], rfl, hx.symm⟩
    · rintro ⟨ts, hs, hx⟩
      cases ts with
      | nil => exact hx.symm
      | cons t ts => cases t <;> simp [skeleton] at hs
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [prepare, decode, Bool.and_eq_true, beq_iff_eq, ih]
      constructor
      · rintro ⟨hm, ts, hs, hx⟩
        refine ⟨none :: ts, by simp [skeleton, hs], ?_⟩
        simp only [selectedCoefficients, hx]
        omega
      · rintro ⟨ts, hs, hx⟩
        cases ts with
        | nil => simp [skeleton] at hs
        | cons t ts =>
          cases t with
          | some b => simp [skeleton] at hs
          | none =>
            simp only [skeleton, List.cons.injEq, true_and] at hs
            simp only [selectedCoefficients] at hx
            exact ⟨by omega, ts, hs, by omega⟩
    | true =>
      simp only [prepare, decode, Bool.or_eq_true, Bool.and_eq_true,
        beq_iff_eq, decide_eq_true_eq, ih]
      constructor
      · intro h
        rcases h with ⟨hm, ts, hs, hx⟩ | ⟨⟨hc, hm⟩, ts, hs, hx⟩
        · refine ⟨some false :: ts, by simp [skeleton, hs], ?_⟩
          simp only [selectedCoefficients, hx]
          omega
        · have hb : base ts = base (unselected bs) := by rw [base_skeleton ts, hs]
          refine ⟨some true :: ts, by simp [skeleton, hs], ?_⟩
          simp only [selectedCoefficients, hb, hx]
          omega
      · rintro ⟨ts, hs, hx⟩
        cases ts with
        | nil => simp [skeleton] at hs
        | cons t ts =>
          cases t with
          | none => simp [skeleton] at hs
          | some b =>
            simp only [skeleton, List.cons.injEq, true_and] at hs
            have hb : base ts = base (unselected bs) := by rw [base_skeleton ts, hs]
            cases b with
            | false =>
              simp only [selectedCoefficients] at hx
              exact Or.inl ⟨by omega, ts, hs, by omega⟩
            | true =>
              simp only [selectedCoefficients, hb] at hx
              exact Or.inr ⟨⟨by omega, by omega⟩, ts, hs, by omega⟩

/-- Tail-recursive scan of a finite interval of quotient candidates. -/
def checkFrom (plan : List (Bool × Nat)) (D top : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | q, count + 1 => !decode plan (top - q * D) && checkFrom plan D top (q + 1) count

theorem checkFrom_at (plan : List (Bool × Nat)) (D top q count r : Nat)
    (hc : checkFrom plan D top q count = true)
    (hlo : q ≤ r) (hhi : r < q + count) : decode plan (top - r * D) = false := by
  induction count generalizing q with
  | zero => omega
  | succ count ih =>
    simp only [checkFrom, Bool.and_eq_true] at hc
    by_cases he : r = q
    · subst r; simpa using hc.1
    · exact ih (q + 1) hc.2 (by omega) (by omega)

/-- A mask can be integral only if its selected sum is 4C-qD, with
    3C≤qD≤4C. The scan starts at floor(3C/D), possibly including one harmless
    extra target larger than C, and ends at floor(4C/D). -/
def excludes (bs : List Bool) : Bool :=
  let ts := unselected bs
  let D := denominator ts
  let c := totalCoefficients ts
  let lo := 3 * c / D
  checkFrom (prepare bs) D (4 * c) lo (4 * c / D - lo + 1)

/-- A successful finite target scan excludes every subset of the specified
    skeleton, using the imported exact numerator normal form. -/
theorem excludes_sound (bs : List Bool)
    (hD : 0 < denominator (unselected bs)) (hc : excludes bs = true)
    (ts : List Token) (hs : skeleton ts = bs) :
    ¬ denominator ts ∣ weight (mask ts) := by
  let D := denominator (unselected bs)
  let c := totalCoefficients (unselected bs)
  have hden : denominator ts = D := by rw [denominator_skeleton ts, hs]
  have hC : C ts = c := by rw [C_skeleton ts, hs, C_eq_total]
  have hsmall : selectedCoefficients ts ≤ c := by
    have hh := (X_bounds ts).2
    rwa [X_eq_selected, hC] at hh
  have hsign : 3 ^ (base ts).length ≤ 2 ^ (base ts).sum := by
    have hp : 0 < denominator ts := by rw [hden]; exact hD
    unfold denominator at hp
    omega
  intro hd
  have ht := (mask_divisibility_iff ts hsign).mp hd
  rw [hden, hC, X_eq_selected] at ht
  obtain ⟨q, hq⟩ := ht
  have hq' : 4 * c - selectedCoefficients ts = q * D := by
    simpa [Nat.mul_comm] using hq
  have hlow : 3 * c ≤ q * D := by omega
  have hupp : q * D ≤ 4 * c := by omega
  have hlo : 3 * c / D ≤ q := by
    have hh := Nat.div_le_div_right (c := D) hlow
    simpa [Nat.mul_div_cancel q (show 0 < D from hD)] using hh
  have hhi : q ≤ 4 * c / D := (Nat.le_div_iff_mul_le hD).mpr hupp
  have htarget : 4 * c - q * D = selectedCoefficients ts := by omega
  have hy : decode (prepare bs) (4 * c - q * D) = true := by
    rw [htarget]
    exact (decode_iff bs _).mpr ⟨ts, hs, rfl⟩
  have hn : decode (prepare bs) (4 * c - q * D) = false :=
    checkFrom_at (prepare bs) D (4 * c) (3 * c / D)
      (4 * c / D - 3 * c / D + 1) q hc hlo (by omega)
  rw [hy] at hn
  contradiction

#print axioms pair_residues_disjoint
#print axioms decode_iff
#print axioms excludes_sound

end MaskSubsetDecoder
