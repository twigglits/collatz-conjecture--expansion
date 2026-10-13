/-
  Integer inputs for returned-endpoint sampling bounds.
  Haar integration, logarithmic moments, and probability consequences
  remain written in docs/RETURN-IMAGE-BOUNDS.md.
-/
import ReversalPersistence

namespace ReturnImageBounds
open CollatzAffine CoalescenceTail EscapeWeightRefinements ReversalPersistence

theorem cubic_children (t n : Nat) :
    3 ^ wt (t + 1) n + 3 ^ wt (t + 1) (2 ^ t + n) = 4 * 3 ^ wt t n := by
  rw [weight_snoc, weight_snoc, endpoint_parity_flip]
  have hl := weight_lift t 1 n
  simp only [Nat.mul_one] at hl
  rw [hl]
  have hp : orbit t n % 2 = 0 ∨ orbit t n % 2 = 1 := by omega
  rcases hp with hp | hp <;> simp [hp, Nat.pow_succ] <;> omega

theorem cubic_mass (t : Nat) :
    total (2 ^ t) (fun n => 3 ^ wt t n) = 4 ^ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Nat.pow_succ 2, Nat.mul_two, total_add, ← total_sum]
    have he := total_ext (2 ^ t)
      (fun n => 3 ^ wt (t + 1) n + 3 ^ wt (t + 1) (2 ^ t + n))
      (fun n => 4 * 3 ^ wt t n) (fun n _ => cubic_children t n)
    rw [he, total_mul, ih, Nat.pow_succ 4]
    ac_rfl

inductive PrefixTree where
  | empty
  | stop
  | split (even odd : PrefixTree)

def columnNumerator : Nat → PrefixTree → Nat
  | _, .empty => 0
  | h, .stop => 2 ^ h
  | 0, .split _ _ => 0
  | h + 1, .split even odd => columnNumerator h even + 3 * columnNumerator h odd

def tiltedNumerator : Nat → PrefixTree → Nat
  | _, .empty => 0
  | h, .stop => 4 ^ h
  | 0, .split _ _ => 0
  | h + 1, .split even odd => tiltedNumerator h even + 3 * tiltedNumerator h odd

def binaryNumerator : Nat → PrefixTree → Nat
  | _, .empty => 0
  | h, .stop => 2 ^ h
  | 0, .split _ _ => 0
  | h + 1, .split even odd => binaryNumerator h even + binaryNumerator h odd

theorem column_le_tilted (h : Nat) (tree : PrefixTree) :
    columnNumerator h tree ≤ tiltedNumerator h tree := by
  induction h generalizing tree with
  | zero => cases tree <;> simp [columnNumerator, tiltedNumerator]
  | succ h ih =>
    cases tree with
    | empty => simp [columnNumerator, tiltedNumerator]
    | stop =>
      simp only [columnNumerator, tiltedNumerator]
      exact Nat.pow_le_pow_left (show 2 ≤ 4 by decide) (h + 1)
    | split even odd =>
      have he := ih even
      have ho := ih odd
      simp only [columnNumerator, tiltedNumerator]
      omega

theorem tilted_kraft (h : Nat) (tree : PrefixTree) :
    tiltedNumerator h tree ≤ 4 ^ h := by
  induction h generalizing tree with
  | zero => cases tree <;> simp [tiltedNumerator]
  | succ h ih =>
    cases tree with
    | empty => simp [tiltedNumerator]
    | stop => simp [tiltedNumerator]
    | split even odd =>
      have he := ih even
      have ho := ih odd
      simp only [tiltedNumerator, Nat.pow_succ]
      omega

theorem column_numerator_bound (h : Nat) (tree : PrefixTree) :
    columnNumerator h tree ≤ 4 ^ h :=
  Nat.le_trans (column_le_tilted h tree) (tilted_kraft h tree)

theorem binary_kraft (h : Nat) (tree : PrefixTree) :
    binaryNumerator h tree ≤ 2 ^ h := by
  induction h generalizing tree with
  | zero => cases tree <;> simp [binaryNumerator]
  | succ h ih =>
    cases tree with
    | empty => simp [binaryNumerator]
    | stop => simp [binaryNumerator]
    | split even odd =>
      have he := ih even
      have ho := ih odd
      simp only [binaryNumerator, Nat.pow_succ]
      omega

theorem prefix_endpoint_bound (t r : Nat) (hr : r < 2 ^ t) :
    orbit t r < 2 * 3 ^ wt t r := by
  have hh : 2 ^ t * (orbit t r + 1) ≤ 2 ^ t * (2 * 3 ^ wt t r) := by
    calc
      2 ^ t * (orbit t r + 1) ≤ 3 ^ wt t r * (r + 2 ^ t) := shifted_retention t r
      _ ≤ 3 ^ wt t r * (2 * 2 ^ t) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 ^ t * (2 * 3 ^ wt t r) := by ac_rfl
  have hp : 0 < 2 ^ t := Nat.pow_pos (by decide)
  have hc := Nat.le_of_mul_le_mul_left hh hp
  omega

theorem equal_count_distance_bound (t r a : Nat) (hr : r + 1 < 2 ^ t)
    (ha : wt t r = a) (hb : wt t (r + 1) = a) :
    (orbit t r - orbit t (r + 1)) + (orbit t (r + 1) - orbit t r) < 2 * 3 ^ a := by
  have hx := prefix_endpoint_bound t r (by omega)
  have hy := prefix_endpoint_bound t (r + 1) hr
  rw [ha] at hx
  rw [hb] at hy
  omega

theorem image_lift (t r a q : Nat) (ha : wt t r = a) :
    orbit t (2 ^ t * q + r) = 3 ^ a * q + orbit t r := by
  rw [affine, ha]

def residueCount (start length period residue : Nat) : Nat :=
  (start + length + (period - 1 - residue)) / period -
    (start + (period - 1 - residue)) / period

theorem residue_count_zero (start period residue : Nat) :
    residueCount start 0 period residue = 0 := by simp [residueCount]

/-- Integer interval discrepancy; the floor counter's counting interpretation is written. -/
theorem residue_count_discrepancy (start length period residue : Nat) (hp : 0 < period) :
    period * residueCount start length period residue < length + period ∧
    length < period * residueCount start length period residue + period := by
  let lo := start + (period - 1 - residue)
  let hi := lo + length
  have he : start + length + (period - 1 - residue) = hi := by dsimp [hi, lo]; omega
  have hl := Nat.mod_add_div lo period
  have hh := Nat.mod_add_div hi period
  have hml := Nat.mod_lt lo hp
  have hmh := Nat.mod_lt hi hp
  have hdiv : lo / period ≤ hi / period := Nat.div_le_div_right (by dsimp [hi]; omega)
  unfold residueCount
  rw [he]
  change period * (hi / period - lo / period) < length + period ∧
    length < period * (hi / period - lo / period) + period
  rw [Nat.mul_sub_left_distrib]
  have heq : hi = lo + length := rfl
  omega

theorem residue_count_full_period (start period residue : Nat) (hp : 0 < period) :
    residueCount start period period residue = 1 := by
  unfold residueCount
  rw [show start + period + (period - 1 - residue) =
    start + (period - 1 - residue) + period by omega, Nat.add_div_right _ hp]
  omega

#print axioms cubic_children
#print axioms cubic_mass
#print axioms column_le_tilted
#print axioms tilted_kraft
#print axioms column_numerator_bound
#print axioms binary_kraft
#print axioms prefix_endpoint_bound
#print axioms equal_count_distance_bound
#print axioms image_lift
#print axioms residue_count_zero
#print axioms residue_count_discrepancy
#print axioms residue_count_full_period

end ReturnImageBounds
