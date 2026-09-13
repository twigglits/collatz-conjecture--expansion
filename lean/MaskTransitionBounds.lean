/-
  Exact arithmetic and local repairs for docs/MASK-TRANSITIONS.md.
  Kernel evaluation only. The catalog and logarithm arguments are written.
  Check: lean lean/MaskTransitionBounds.lean
-/
namespace MaskTransitionBounds

set_option exponentiation.threshold 10000

theorem slope_and_entropy_inputs :
    (3 : Nat) ^ 7 > 2 ^ 11 ∧ 3 ^ 147 < 2 ^ 233 ∧
    65 * 147 = 233 * 41 + 2 ∧ 6027 < 2 * 3014 ∧
    1814 * 100 < 19 * 9555 ∧ 21 * 19 + 200 < 600 ∧
    4 * 19 < 100 ∧ 26 * 19 = 494 ∧ 150 < 19 * 8 := by decide

theorem large_period_cutoff :
    24 * 250 < 3 * 2048 ∧ 2304 * 2048 < (2 : Nat) ^ 24 ∧
    500 < 3 * 2048 ∧ 2 * 3014 < 2 ^ 13 ∧ 13 ≤ 2048 := by decide

def rises : List Bool → Nat
  | a :: b :: tail => (if !a && b then 1 else 0) + rises (b :: tail)
  | _ => 0

def repair : List Bool → List Bool
  | [false, true] => [false, false]
  | [false, false, true] => [false, false, false]
  | [false, true, false] => [false, false, false]
  | [false, true, true] => [true, true, true]
  | [true, false, true] => [true, false, false]
  | bs => bs

def hamming : List Bool → List Bool → Nat
  | [], bs => bs.length
  | bs, [] => bs.length
  | a :: as, b :: bs => (if a == b then 0 else 1) + hamming as bs

def encoded (bs : List Bool) : List Bool :=
  bs.flatMap fun selected => if selected then [true, true, false] else [true, false, true]

def repairClaim (bs : List Bool) : Prop :=
  (repair bs).length = bs.length ∧ rises (repair bs) = 0 ∧
  hamming (encoded bs) (encoded (repair bs)) = 2 * rises bs ∧ rises bs ≤ 1

theorem two_pair_repair : ∀ a b : Bool, repairClaim [a, b] := by
  unfold repairClaim
  decide

theorem three_pair_repair : ∀ a b c : Bool, repairClaim [a, b, c] := by
  unfold repairClaim
  decide

#print axioms slope_and_entropy_inputs
#print axioms large_period_cutoff
#print axioms two_pair_repair
#print axioms three_pair_repair
end MaskTransitionBounds
