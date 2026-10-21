/-
  Period3Certs.lean — machine-checked window certificate for period-3 (and
  period-4) universal families (CollatzTheory.lean §7; paper §6.3).

  A period-3 universal family through c requires, with m₁ = oddPart(a+1) > 1
  and m₂ = oddPart(a·m₁+1) > 1, that a·m₂+1 be a power of two
  (`period3_universal_criterion`); period 4 continues one leg further.

  This file certifies by exhaustive exact big-integer check (`native_decide`)
  that for EVERY odd a < 2^24:
    • the period-3 closure never fires  (no non-degenerate 1 → m₁ → m₂ → 1),
    • the period-4 closure never fires  (no 1 → m₁ → m₂ → m₃ → 1).
  Degenerate skips are exactly the classified strata: m₁ = 1 (Mersenne,
  period 1, Theorem 4b) and m₂ = 1 (period 2 — only a = 5, Theorem 6).
  Unlike the u64 GPU catalog window, these checks are EXACT: no value
  window, so verdicts are complete for a < 2^24.

  Check with:  lean Period3Certs.lean    (Lean 4.31.0)
-/

def oddPartC (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then oddPartC (n / 2) else n
termination_by n
decreasing_by omega

def isPow2 (n : Nat) : Bool := n != 0 && (n &&& (n - 1)) == 0

/-- No period-3 and no period-4 closure at a = 2i+1. -/
def ok34 (i : Nat) : Bool :=
  let a := 2 * i + 1
  let m1 := oddPartC (a + 1)
  if m1 == 1 then true                     -- Mersenne: period 1 (Thm 4b)
  else
    let t2 := a * m1 + 1
    let m2 := oddPartC t2
    if m2 == 1 then true                   -- period 2: only a = 5 (Thm 6)
    else
      let t3 := a * m2 + 1
      if isPow2 t3 then false              -- period-3 closure: must not fire
      else
        let m3 := oddPartC t3
        !(isPow2 (a * m3 + 1))             -- period-4 closure: must not fire

def scanUpTo (f : Nat → Bool) : Nat → Bool
  | 0 => true
  | i + 1 => f i && scanUpTo f i

/-- Window certificate: no period-3 or period-4 universal family through c
    exists for any odd a < 2^24. -/
theorem period34_window_certificate : scanUpTo ok34 (2 ^ 23) = true := by
  native_decide

/- Detection sanity: the component predicates must fire on known positives
   (so a broken helper cannot silently weaken the certificate). -/
example : oddPartC 6 = 3 := by native_decide
example : oddPartC (2 ^ 60 * 12347) = 12347 := by native_decide
example : isPow2 (2 ^ 100) = true := by native_decide
example : isPow2 (2 ^ 100 + 2) = false := by native_decide
example : isPow2 (5 * 3 + 1) = true := by native_decide          -- a=5 period-2 leg
example : isPow2 (11 * 93 + 1) = true := by native_decide        -- 1024: d ∣ c instance
-- a synthetic period-3-shaped closure the checker must catch: with a = 7,
-- m = 9 (NOT the orbit of 1), 7*9+1 = 64 fires isPow2 — the detection path.
example : isPow2 (7 * 9 + 1) = true := by native_decide

#print axioms period34_window_certificate
