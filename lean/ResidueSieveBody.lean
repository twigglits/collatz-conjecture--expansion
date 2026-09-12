/-
  Symbolic residue sieve. Append this file after CollatzAffine.lean.
  Universal soundness uses only kernel proofs. Any generated numeric count
  using native_decide separately trusts Lean's compiler and native runtime.
-/
namespace CollatzResidue

open CollatzAffine

def certificate (k r : Nat) : ClassCertificate :=
  ⟨k, r, threshold (3 ^ wt k r) (2 ^ k) (orbit k r) r⟩

def closes (k r : Nat) : Bool := checkWholeClass (certificate k r)

/-- Follow the next low bit of q only while the symbolic class remains open. -/
def covered : Nat → Nat → Nat → Nat → Bool
  | 0, k, r, _ => closes k r
  | fuel + 1, k, r, q =>
      if closes k r then true
      else if q % 2 = 0 then covered fuel (k + 1) r (q / 2)
      else covered fuel (k + 1) (r + 2 ^ k) (q / 2)

/-- The even child represents precisely the even q members of its parent. -/
theorem even_child (k r q : Nat) (hq : q % 2 = 0) :
    2 ^ (k + 1) * (q / 2) + r = 2 ^ k * q + r := by
  have heq : 2 * (q / 2) = q := by omega
  rw [Nat.pow_succ, Nat.mul_assoc, heq]

/-- The odd child represents precisely the odd q members of its parent. -/
theorem odd_child (k r q : Nat) (hq : q % 2 ≠ 0) :
    2 ^ (k + 1) * (q / 2) + (r + 2 ^ k) = 2 ^ k * q + r := by
  have heq : q = 2 * (q / 2) + 1 := by omega
  have heq' : 2 ^ k * q = 2 ^ k * (2 * (q / 2)) + 2 ^ k := by
    have hm := congrArg (fun x => 2 ^ k * x) heq
    simpa only [Nat.mul_add, Nat.mul_one] using hm
  rw [heq', Nat.pow_succ, Nat.mul_assoc]
  omega

theorem closes_sound {k r : Nat} (hc : closes k r = true) (q : Nat)
    (hn : 1 < 2 ^ k * q + r) : orbit k (2 ^ k * q + r) < 2 ^ k * q + r :=
  checkWholeClass_sound (certificate k r) hc q hn

/-- Every accepted positive start descends, with a depth-dependent step bound. -/
theorem covered_sound : ∀ fuel k r q, covered fuel k r q = true →
    1 < 2 ^ k * q + r →
    ∃ j, j ≤ k + fuel ∧ orbit j (2 ^ k * q + r) < 2 ^ k * q + r
  | 0, k, r, q, hc, hn => ⟨k, by omega, closes_sound hc q hn⟩
  | fuel + 1, k, r, q, hc, hn => by
    by_cases hclose : closes k r = true
    · exact ⟨k, by omega, closes_sound hclose q hn⟩
    · have hfalse : closes k r = false := by cases he : closes k r <;> simp_all
      simp only [covered, hfalse, Bool.false_eq_true, if_false] at hc
      by_cases hq : q % 2 = 0
      · rw [if_pos hq] at hc
        have he := even_child k r q hq
        obtain ⟨j, hj, hd⟩ := covered_sound fuel (k + 1) r (q / 2) hc (by rw [he]; exact hn)
        exact ⟨j, by omega, by rw [he] at hd; exact hd⟩
      · rw [if_neg hq] at hc
        have he := odd_child k r q hq
        obtain ⟨j, hj, hd⟩ := covered_sound fuel (k + 1) (r + 2 ^ k) (q / 2) hc
          (by rw [he]; exact hn)
        exact ⟨j, by omega, by rw [he] at hd; exact hd⟩

/-- The decision reads at most fuel low bits of q. All higher bits may vary. -/
theorem covered_periodic : ∀ fuel k r t q,
    covered fuel k r (2 ^ fuel * t + q) = covered fuel k r q
  | 0, _, _, _, _ => rfl
  | fuel + 1, k, r, t, q => by
    by_cases hc : closes k r = true
    · simp [covered, hc]
    · have hf : closes k r = false := by cases he : closes k r <;> simp_all
      have hsplit : 2 ^ (fuel + 1) * t + q = 2 * (2 ^ fuel * t) + q := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ fuel) 2, Nat.mul_assoc]
      have hpar : (2 ^ (fuel + 1) * t + q) % 2 = q % 2 := by rw [hsplit]; omega
      have hdiv : (2 ^ (fuel + 1) * t + q) / 2 = 2 ^ fuel * t + q / 2 := by
        rw [hsplit]; omega
      simp only [covered, hf, Bool.false_eq_true, if_false, hpar, hdiv]
      by_cases hq : q % 2 = 0
      · rw [if_pos hq, if_pos hq]
        exact covered_periodic fuel (k + 1) r t (q / 2)
      · rw [if_neg hq, if_neg hq]
        exact covered_periodic fuel (k + 1) (r + 2 ^ k) t (q / 2)

/-- A closed node accounts for every one of its 2^fuel refinements. -/
def countCovered : Nat → Nat → Nat → Nat
  | 0, k, r => if closes k r then 1 else 0
  | fuel + 1, k, r =>
      if closes k r then 2 ^ (fuel + 1)
      else countCovered fuel (k + 1) r + countCovered fuel (k + 1) (r + 2 ^ k)

/-- A simple semantic count of a Boolean predicate on the interval [0,n). -/
def countWhere (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => countWhere p n + if p n then 1 else 0

theorem countWhere_congr {p q : Nat → Bool} (h : ∀ n, p n = q n) :
    ∀ n, countWhere p n = countWhere q n
  | 0 => rfl
  | n + 1 => by simp only [countWhere, h, countWhere_congr h n]

theorem countWhere_true : ∀ n, countWhere (fun _ => true) n = n
  | 0 => rfl
  | n + 1 => by simp [countWhere, countWhere_true n]

/-- Counting even and odd indices separately is an exact partition. -/
theorem countWhere_even_odd (p : Nat → Bool) : ∀ n,
    countWhere p (2 * n) = countWhere (fun q => p (2 * q)) n +
      countWhere (fun q => p (2 * q + 1)) n
  | 0 => rfl
  | n + 1 => by
    have heq : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [heq, countWhere, countWhere, countWhere_even_odd p n, countWhere, countWhere]
    omega

/-- The fast tree counter equals the exact number of accepted residues.
    This proof does not evaluate all residues when computing countCovered. -/
theorem countCovered_eq_countWhere : ∀ fuel k r,
    countCovered fuel k r = countWhere (covered fuel k r) (2 ^ fuel)
  | 0, k, r => by simp [countCovered, countWhere, covered]
  | fuel + 1, k, r => by
    by_cases hc : closes k r = true
    · have hall : ∀ q, covered (fuel + 1) k r q = true := by intro q; simp [covered, hc]
      rw [countWhere_congr hall, countWhere_true]
      simp [countCovered, hc]
    · have hf : closes k r = false := by cases he : closes k r <;> simp_all
      have heven : ∀ q, covered (fuel + 1) k r (2 * q) = covered fuel (k + 1) r q := by
        intro q
        simp [covered, hf]
      have hodd : ∀ q, covered (fuel + 1) k r (2 * q + 1) =
          covered fuel (k + 1) (r + 2 ^ k) q := by
        intro q
        simp [covered, hf, Nat.add_div]
      rw [show 2 ^ (fuel + 1) = 2 * 2 ^ fuel by rw [Nat.pow_succ, Nat.mul_comm]]
      rw [countWhere_even_odd, countWhere_congr heven, countWhere_congr hodd]
      simp only [countCovered, hf, Bool.false_eq_true, if_false, countCovered_eq_countWhere]

theorem countWhere_le (p : Nat → Bool) : ∀ n, countWhere p n ≤ n
  | 0 => by simp [countWhere]
  | n + 1 => by
    have ih := countWhere_le p n
    simp only [countWhere]
    split <;> omega

theorem countCovered_le (fuel k r : Nat) : countCovered fuel k r ≤ 2 ^ fuel := by
  rw [countCovered_eq_countWhere]
  exact countWhere_le _ _

def countOpen (fuel k r : Nat) : Nat := 2 ^ fuel - countCovered fuel k r

/-- Accepted and open residue masses partition every finite level exactly. -/
theorem mass_partition (fuel k r : Nat) :
    countCovered fuel k r + countOpen fuel k r = 2 ^ fuel := by
  have := Nat.sub_add_cancel (countCovered_le fuel k r)
  unfold countOpen
  omega

/-- The root predicate is interpreted directly on the original integer. -/
def good (depth n : Nat) : Bool := covered depth 0 0 n

theorem good_sound (depth n : Nat) (hg : good depth n = true) (hn : 1 < n) :
    ∃ j, j ≤ depth ∧ orbit j n < n := by
  simpa using covered_sound depth 0 0 n hg (by simpa using hn)

/-- The certified count applies in every aligned block, not just the first one.
    For descent itself, good_sound excludes only the starts 0 and 1. -/
theorem count_each_block (depth t : Nat) :
    countWhere (fun r => good depth (2 ^ depth * t + r)) (2 ^ depth) =
      countCovered depth 0 0 := by
  have h : ∀ r, good depth (2 ^ depth * t + r) = good depth r :=
    fun r => covered_periodic depth 0 0 t r
  rw [countWhere_congr h]
  exact (countCovered_eq_countWhere depth 0 0).symm

#print axioms covered_sound
#print axioms covered_periodic
#print axioms countCovered_eq_countWhere
#print axioms good_sound
#print axioms count_each_block
#print axioms mass_partition

end CollatzResidue
