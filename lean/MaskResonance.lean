/-
  Finite rational separation for unrestricted mechanical masks.
  Standalone Lean 4.33.1; no Mathlib.

  The dyadic logarithm enclosure and the application to all mask cycles
  are written in docs/MASK-RESONANCE.md. This file checks finite integer
  arithmetic, proves the Farey denominator lemma and cover extraction,
  and independently validates every generated bracket.
  Only the finite certificate uses native_decide.
-/
namespace MaskResonance
set_option maxRecDepth 16384
set_option exponentiation.threshold 16384

structure Fraction where
  num : Nat
  den : Nat
deriving Repr

structure Bracket where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
deriving Repr

/-- Scaled lower sum of the logarithm series. Each division rounds down.
    The mathematical relation to logarithms is a written argument. -/
def dyadicSum (q terms bits : Nat) : Nat := Id.run do
  let scale := 2 ^ (bits + 1)
  let mut total := 0
  let mut power := q
  for j in [:terms] do
    total := total + scale / ((2 * j + 1) * power)
    power := power * q * q
  return total

def bits : Nat := 8192
def terms : Nat := 4096
def logTwoFloor : Nat := dyadicSum 3 terms bits
def logThreeFloor : Nat := dyadicSum 2 terms bits
def lower : Fraction := ⟨logTwoFloor, logThreeFloor + terms + 1⟩
def upper : Fraction := ⟨logTwoFloor + terms + 1, logThreeFloor⟩

/-- An untrusted candidate generator. An incorrect prefix cannot make a
    false bracket pass the separate arithmetic checks below. -/
def commonCF : Nat → Fraction → Fraction → List Nat
  | 0, _, _ => []
  | fuel + 1, l, u =>
      let q := l.num / l.den
      if l.den = 0 ∨ u.den = 0 ∨ q ≠ u.num / u.den then []
      else q :: commonCF fuel
        ⟨u.den, u.num - q * u.den⟩
        ⟨l.den, l.num - q * l.den⟩

def advance (changeLower : Bool) (q : Nat) (f : Bracket) : Bracket :=
  if changeLower then ⟨f.a + q * f.c, f.b + q * f.d, f.c, f.d⟩
  else ⟨f.a, f.b, f.c + q * f.a, f.d + q * f.b⟩

def brackets : List Nat → Bool → Bracket → List Bracket
  | [], _, _ => []
  | q :: qs, side, f =>
      let next := advance side q f
      next :: brackets qs (!side) next

def candidates : List Bracket :=
  brackets ((commonCF 5000 lower upper).drop 1) false ⟨0, 1, 1, 0⟩

/-- A uniform catalog bound for every independent 21-to-12 mask.
    The combinatorial derivation is written; this is its exact integer form. -/
def catalog (m : Nat) : Nat :=
  (m + 4) * 2 ^ (21 * (m + 1) / 80 + 3)

/-- An untrusted choice of window length. Every chosen length is checked
    against the catalog bound before its row is accepted. -/
def window (start : Nat) : Nat := Id.run do
  let mut lo := 0
  let mut hi := 4 * start.log2 + 16
  for _ in [:64] do
    if lo + 1 < hi then
      let mid := (lo + hi) / 2
      if catalog mid < start then lo := mid else hi := mid
  return lo

/-- A row's gap is checked at the smallest denominator it covers.
    The sign is checked before natural subtraction is used. -/
def Good (l u : Fraction) (start m : Nat) (f : Bracket) : Prop :=
  catalog m < start ∧ 0 < f.b ∧ 0 < f.d ∧
  f.b * f.c = f.a * f.d + 1 ∧
  u.num * f.d < f.c * u.den ∧
  f.a * l.den < l.num * f.b ∧
  4 * l.den * f.b <
    (l.num * f.b - f.a * l.den) * 2 ^ m

instance (l u : Fraction) (start m : Nat) (f : Bracket) :
    Decidable (Good l u start m f) := inferInstanceAs (Decidable
      (catalog m < start ∧ 0 < f.b ∧ 0 < f.d ∧
       f.b * f.c = f.a * f.d + 1 ∧
       u.num * f.d < f.c * u.den ∧
       f.a * l.den < l.num * f.b ∧
       4 * l.den * f.b <
         (l.num * f.b - f.a * l.den) * 2 ^ m))

/-- Skipped brackets extend no coverage. Accepted brackets cover exactly
    the next interval, ending before b+d. An exhausted list must already
    have reached the requested final endpoint. -/
def coverCheck (l u : Fraction) (stop : Nat) :
    Nat → List Bracket → Bool
  | start, [] => decide (stop ≤ start)
  | start, f :: fs =>
      if stop ≤ start then true
      else if f.b + f.d ≤ start then coverCheck l u stop start fs
      else decide (Good l u start (window start) f) &&
        coverCheck l u stop (min stop (f.b + f.d)) fs

/-- Every denominator in an accepted cover has an independently checked
    bracket. This does not assume correctness of either generator. -/
theorem coverCheck_sound (l u : Fraction) (stop start : Nat)
    (fs : List Bracket) (hc : coverCheck l u stop start fs = true)
    (N : Nat) (hlo : start ≤ N) (hhi : N < stop) :
    ∃ f s m, s ≤ N ∧ N < f.b + f.d ∧ Good l u s m f := by
  induction fs generalizing start with
  | nil =>
      simp only [coverCheck, decide_eq_true_eq] at hc
      omega
  | cons f fs ih =>
      have hs : ¬ stop ≤ start := by omega
      simp only [coverCheck, if_neg hs] at hc
      by_cases hf : f.b + f.d ≤ start
      · simp only [if_pos hf] at hc
        exact ih start hc hlo
      · simp only [if_neg hf, Bool.and_eq_true, decide_eq_true_eq] at hc
        by_cases hn : N < f.b + f.d
        · exact ⟨f, start, window start, hlo, hn, hc.1⟩
        · exact ih (min stop (f.b + f.d)) hc.2 (by omega)

/-- A rational strictly between Farey neighbors has denominator at least
    the sum of their denominators, including unreduced rationals. -/
theorem farey_denominator {a b c d p N : Nat}
    (hdet : b * c = a * d + 1)
    (hlo : a * N < p * b) (hhi : p * d < c * N) :
    b + d ≤ N := by
  have h1 : c * N - p * d + p * d = c * N := Nat.sub_add_cancel (by omega)
  have h2 : p * b - a * N + a * N = p * b := Nat.sub_add_cancel (by omega)
  have hid : b * (c * N - p * d) + d * (p * b - a * N) = N := by
    have he : (b * c) * N = (a * d + 1) * N := congrArg (fun x => x * N) hdet
    grind
  have hb : b ≤ b * (c * N - p * d) :=
    Nat.le_mul_of_pos_right b (by omega)
  have hd : d ≤ d * (p * b - a * N) :=
    Nat.le_mul_of_pos_right d (by omega)
  omega

theorem below_farey_lower {a b c d p N : Nat}
    (hdet : b * c = a * d + 1)
    (hupper : p * d < c * N) (hsmall : N < b + d) :
    p * b ≤ a * N := by
  by_cases hh : p * b ≤ a * N
  · exact hh
  · have := farey_denominator hdet (by omega) hupper
    omega

/-- Finite tail and positivity checks for the written series enclosure. -/
def LogArithmetic : Prop :=
  0 < logTwoFloor ∧ 0 < logThreeFloor ∧
  lower.num * upper.den < upper.num * lower.den ∧
  2 ^ (bits + 1) < (2 * terms + 1) * (2 ^ 2 - 1) * 2 ^ (2 * terms - 1) ∧
  2 ^ (bits + 1) < (2 * terms + 1) * (3 ^ 2 - 1) * 3 ^ (2 * terms - 1)

instance : Decidable LogArithmetic := inferInstanceAs (Decidable
  (0 < logTwoFloor ∧ 0 < logThreeFloor ∧
   lower.num * upper.den < upper.num * lower.den ∧
   2 ^ (bits + 1) < (2 * terms + 1) * (2 ^ 2 - 1) * 2 ^ (2 * terms - 1) ∧
   2 ^ (bits + 1) < (2 * terms + 1) * (3 ^ 2 - 1) * 3 ^ (2 * terms - 1)))

theorem log_arithmetic : LogArithmetic := by native_decide

theorem cover_verified :
    coverCheck lower upper (10 ^ 1000 + 1) (2 ^ 21) candidates = true := by
  native_decide

theorem denominator_cover (N : Nat) (hlo : 2 ^ 21 ≤ N)
    (hhi : N ≤ 10 ^ 1000) :
    ∃ f s m, s ≤ N ∧ N < f.b + f.d ∧ Good lower upper s m f :=
  coverCheck_sound lower upper (10 ^ 1000 + 1) (2 ^ 21)
    candidates cover_verified N hlo (by omega)

/-- Exact comparisons used in the written all-mask catalog bound. -/
theorem catalog_constants :
    2 ^ 160 < 3 ^ 101 ∧
    (32 * (3 * 64 + 7)) ^ 80 < 2 ^ (17 * 64) ∧
    17 ^ 80 < 2 ^ 337 := by decide

theorem catalog_power_bound (t : Nat) (ht : 64 ≤ t) :
    (32 * (3 * t + 7)) ^ 80 < 2 ^ (17 * t) := by
  have step : ∀ t, 64 ≤ t →
      (32 * (3 * t + 7)) ^ 80 < 2 ^ (17 * t) →
      (32 * (3 * (t + 1) + 7)) ^ 80 < 2 ^ (17 * (t + 1)) := by
      intro t ht ih
      have hlinear : 16 * (32 * (3 * (t + 1) + 7)) ≤
          17 * (32 * (3 * t + 7)) := by omega
      have hpow := Nat.pow_le_pow_left hlinear 80
      rw [Nat.mul_pow 16 _ 80, Nat.mul_pow 17 _ 80] at hpow
      have hprod : 17 ^ 80 * (32 * (3 * t + 7)) ^ 80 <
          2 ^ 337 * 2 ^ (17 * t) := by
        exact Nat.lt_trans
          (Nat.mul_lt_mul_of_pos_left ih (by decide))
          (Nat.mul_lt_mul_of_pos_right catalog_constants.2.2
            (Nat.pow_pos (by decide)))
      have hh := Nat.lt_of_le_of_lt hpow hprod
      have he : 2 ^ 337 * 2 ^ (17 * t) =
          16 ^ 80 * 2 ^ (17 * (t + 1)) := by
        have h16 : 16 = 2 ^ 4 := by decide
        rw [h16, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
        congr 1
        omega
      rw [he] at hh
      exact (Nat.mul_lt_mul_left (by decide : 0 < 16 ^ 80)).mp hh
  obtain ⟨j, rfl⟩ : ∃ j, t = 64 + j := ⟨t - 64, by omega⟩
  induction j with
  | zero => exact catalog_constants.2.1
  | succ j ih => exact step (64 + j) (by omega) (ih (by omega))

#print axioms farey_denominator
#print axioms below_farey_lower
#print axioms coverCheck_sound
#print axioms catalog_constants
#print axioms catalog_power_bound
#print axioms log_arithmetic
#print axioms cover_verified
#print axioms denominator_cover
end MaskResonance
