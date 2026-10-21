/-
  Period2Certs.lean — machine-checked window certificate for the period-2
  Diophantine reduction (CollatzTheory.lean §6; paper §6.2).

  A period-2 universal family through c with multiplier a, a+1 = 2^j·m
  (m = oddPart(a+1) ≥ 3), forces  x² + (2^(j+2) − 1) = 2^N  with
  x = 2^(j+1)·m − 1  (kernel theorem `period2_ramanujan_nagell`).

  This file certifies, by exhaustive big-integer check (`native_decide`,
  exact Nat arithmetic), that for ALL 1 ≤ j ≤ 64 and N ≤ 2048 the only
  solutions x of  x² = 2^N − (2^(j+2) − 1)  are:
    • x = 1              (spurious branch: not of the form 2^(j+1)m − 1, m odd,
                          for j ≥ 1)
    • x = 2^(j+1) − 1    (m = 1: the Mersenne degenerate, period 1)
    • j = 1 only: x ∈ {3, 5, 11, 181}  (Nagell's x²+7 = 2^n; on the branch
      x ≡ 3 mod 4 only x = 3 (m=1) and x = 11 (m=3 → a = 5) survive)
  Consequence: no non-Mersenne multiplier a with ν₂(a+1) ≤ 64 and
  a·m+1 ≤ 2^2046 has a period-2 universal family, except a = 5.
  (Within the window this also independently re-verifies the Apéry–Beukers
  two-solution classification for D = 2^ℓ − 1, 4 ≤ ℓ ≤ 66.)

  Check with:  lean Period2Certs.lean    (Lean 4.31.0)
-/

/-- Bit length: bits 0 = 0, bits n = ⌊log₂ n⌋ + 1 for n ≥ 1. -/
def bits (n : Nat) : Nat :=
  if h : n = 0 then 0 else bits (n / 2) + 1
termination_by n
decreasing_by omega

/-- Integer square root by Newton iteration, seeded above √n; the sequence
    decreases strictly until it reaches ⌊√n⌋ (quadratic convergence, so fuel
    64 is far beyond what 2048-bit inputs need). Detection correctness is
    exercised by the `sq detection` examples below. -/
def isqrt (n : Nat) : Nat := go 64 (2 ^ (bits n / 2 + 1))
where
  go : Nat → Nat → Nat
    | 0, x => x
    | f + 1, x =>
      if x = 0 then 0
      else
        let x' := (x + n / x) / 2
        if x' < x then go f x' else x

/-- The solution of x² = 2^N − (2^(j+2) − 1), if one exists. -/
def solAt (j N : Nat) : Option Nat :=
  let D := 2 ^ (j + 2) - 1
  if 2 ^ N ≤ D then none
  else
    let y := 2 ^ N - D
    let x := isqrt y
    if x * x == y then some x else none

/-- Any solution at (j, N) lies in the known list. -/
def okJN (j N : Nat) : Bool :=
  match solAt j N with
  | none => true
  | some x =>
      x == 1 || x == 2 ^ (j + 1) - 1
        || (j == 1 && (x == 3 || x == 5 || x == 11 || x == 181))

def okWindow (jmax Nmax : Nat) : Bool :=
  (List.range jmax).all fun j0 =>
    (List.range (Nmax + 1)).all fun N => okJN (j0 + 1) N

/-- Window certificate: j ∈ [1,64], N ∈ [0,2048] — only the known solutions. -/
theorem period2_window_certificate : okWindow 64 2048 = true := by native_decide

/- sq detection sanity: isqrt must FIND these squares (validates the engine,
   so a broken isqrt cannot silently weaken the certificate). -/
example : solAt 1 3 = some 1 := by native_decide     -- 1 + 7 = 2^3
example : solAt 1 4 = some 3 := by native_decide     -- 9 + 7 = 2^4
example : solAt 1 5 = some 5 := by native_decide     -- 25 + 7 = 2^5
example : solAt 1 7 = some 11 := by native_decide    -- 121 + 7 = 2^7
example : solAt 1 15 = some 181 := by native_decide  -- 32761 + 7 = 2^15
example : solAt 2 6 = some 7 := by native_decide     -- 49 + 15 = 2^6
example : solAt 3 8 = some 15 := by native_decide    -- 225 + 31 = 2^8
example : solAt 5 12 = some 63 := by native_decide   -- 3969 + 127 = 2^12
example : isqrt ((2 ^ 1000 + 12345) ^ 2) = 2 ^ 1000 + 12345 := by native_decide
example : isqrt ((2 ^ 1000 + 12345) ^ 2 + 1) = 2 ^ 1000 + 12345 := by native_decide

#print axioms period2_window_certificate
