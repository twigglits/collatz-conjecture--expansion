/-
  A rotation with bounded cumulative sums for every periodic integer word.
  This is the finite rotation ingredient of CYCLE-EXTREMA.md. It does not
  formalize the weighted numerator extrema or characterize Collatz cycles.
  Standalone Lean 4.31, checked without added axioms or native evaluation.
-/
namespace CollatzCycleExtrema

/-- Every nonempty finite range has an index at which an integer function
    attains its maximum. -/
theorem finite_maximum (f : Nat → Int) : ∀ k, ∃ a, a ≤ k ∧
    ∀ t, t ≤ k → f t ≤ f a
  | 0 => by
    refine ⟨0, by omega, ?_⟩
    intro t ht
    have he : t = 0 := by omega
    simp [he]
  | k + 1 => by
    obtain ⟨a, ha, hm⟩ := finite_maximum f k
    by_cases hnew : f (k + 1) ≤ f a
    · refine ⟨a, by omega, ?_⟩
      intro t ht
      by_cases htk : t ≤ k
      · exact hm t htk
      · have : t = k + 1 := by omega
        simpa [this] using hnew
    · refine ⟨k + 1, by omega, ?_⟩
      intro t ht
      by_cases htk : t ≤ k
      · have := hm t htk
        omega
      · have : t = k + 1 := by omega
        simp [this]

/-- Periodicity reduces every position to one finite period. -/
theorem periodic_reduce (f : Nat → Int) (k : Nat) (hk : 0 < k)
    (hp : ∀ t, f (t + k) = f t) (n : Nat) : f n = f (n % k) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn : n < k
    · simp [Nat.mod_eq_of_lt hn]
    · have he : n = n - k + k := by omega
      have hmod := congrArg (fun t => t % k) he
      simp only [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod] at hmod
      calc
        f n = f (n - k + k) := congrArg f he
        _ = f (n - k) := hp (n - k)
        _ = f ((n - k) % k) := ih (n - k) (by omega)
        _ = f (n % k) := congrArg f hmod.symm

def discrepancy (S : Nat → Int) (k : Nat) (H : Int) (t : Nat) : Int :=
  (k : Int) * S t - (t : Int) * H

theorem discrepancy_periodic (S : Nat → Int) (k : Nat) (H : Int)
    (hs : ∀ t, S (t + k) = S t + H) (t : Nat) :
    discrepancy S k H (t + k) = discrepancy S k H t := by
  simp only [discrepancy, hs, Int.natCast_add, Int.mul_add, Int.add_mul]
  omega

theorem discrepancy_comparison {S : Nat → Int} {k a j : Nat} {H : Int}
    (hd : discrepancy S k H (a + j) ≤ discrepancy S k H a) :
    (k : Int) * (S (a + j) - S a) ≤ (j : Int) * H := by
  simp only [discrepancy, Int.natCast_add, Int.add_mul] at hd
  rw [Int.mul_sub]
  omega

/-- Rotating at a maximum discrepancy bounds every cumulative sum by its
    proportional share of the full period, including prefixes spanning wraps. -/
theorem bounded_rotation (S : Nat → Int) (k : Nat) (H : Int) (hk : 0 < k)
    (hs : ∀ t, S (t + k) = S t + H) :
    ∃ a, a < k ∧ ∀ j, (k : Int) * (S (a + j) - S a) ≤ (j : Int) * H := by
  obtain ⟨a, ha, hm⟩ := finite_maximum (discrepancy S k H) (k - 1)
  refine ⟨a, by omega, ?_⟩
  intro j
  apply discrepancy_comparison
  rw [periodic_reduce (discrepancy S k H) k hk
    (discrepancy_periodic S k H hs) (a + j)]
  apply hm
  have := Nat.mod_lt (a + j) hk
  omega

/-- The corresponding natural-number floor bound for nondecreasing
    cumulative halving counts. -/
theorem floor_bounded_rotation (S : Nat → Nat) (k H : Nat) (hk : 0 < k)
    (hs : ∀ t, S (t + k) = S t + H)
    (hm : ∀ a b, a ≤ b → S a ≤ S b) :
    ∃ a, a < k ∧ ∀ j, S (a + j) - S a ≤ j * H / k := by
  have hsi : ∀ t, (S (t + k) : Int) = (S t : Int) + (H : Int) := by
    intro t
    rw [hs]
    simp
  obtain ⟨a, ha, hb⟩ := bounded_rotation (fun t => (S t : Int)) k (H : Int) hk hsi
  refine ⟨a, ha, ?_⟩
  intro j
  have hle := hm a (a + j) (by omega)
  have hi := hb j
  have hcast : ((S (a + j) - S a : Nat) : Int) = (S (a + j) : Int) - (S a : Int) := by
    omega
  rw [← hcast] at hi
  have hnat : k * (S (a + j) - S a) ≤ j * H := by
    omega
  exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hnat)

#print axioms finite_maximum
#print axioms bounded_rotation
#print axioms floor_bounded_rotation

end CollatzCycleExtrema
