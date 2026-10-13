/-
  Stopped odd-count gaps for actual adjacent shortcut Collatz trajectories.
  Their exact complete-period mean gives a harmonic noncoalescence tail.
  This does not decide convergence of any unresolved positive start.
-/
import CollatzAffine

namespace CoalescenceTail
open CollatzAffine

theorem weight_lift : ∀ k q s,
    wt k (2 ^ k * q + s) = wt k s
  | 0, _, _ => rfl
  | k + 1, q, s => by
    have hs : 2 ^ (k + 1) * q + s = 2 * (2 ^ k * q) + s := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have hp : (2 ^ (k + 1) * q + s) % 2 = s % 2 := by rw [hs]; omega
    by_cases h : s % 2 = 1
    · have hu : U (2 ^ (k + 1) * q + s) = 2 ^ k * (3 * q) + U s := by
        rw [hs]
        unfold U
        rw [if_pos (by omega), if_pos h]
        have hm : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := Nat.mul_left_comm _ _ _
        rw [hm]
        omega
      simp only [wt, hp, hu, weight_lift]
    · have hu : U (2 ^ (k + 1) * q + s) = 2 ^ k * q + U s := by
        rw [hs]
        unfold U
        rw [if_neg (by omega), if_neg h]
        omega
      simp only [wt, hp, hu, weight_lift]

theorem weight_snoc : ∀ k n, wt (k + 1) n = wt k n + orbit k n % 2
  | 0, n => by simp [wt, orbit]
  | k + 1, n => by
    change n % 2 + wt (k + 1) (U n) = n % 2 + wt k (U n) + orbit k (U n) % 2
    rw [weight_snoc]
    omega

theorem weight_le_length : ∀ k n, wt k n ≤ k
  | 0, _ => by simp [wt]
  | k + 1, n => by
    have h := weight_le_length k (U n)
    simp only [wt]
    omega

def gap (k n : Nat) : Int := (wt k n : Int) - (wt k (n + 1) : Int)

def alive : Nat → Nat → Bool
  | 0, _ => true
  | k + 1, n => alive k n && decide (gap (k + 1) n ≠ 0)

def stopped (k n : Nat) : Nat := if alive k n then (gap k n).natAbs else 0

theorem gap_lift (k q r : Nat) : gap k (2 ^ k * q + r) = gap k r := by
  unfold gap
  rw [weight_lift, Nat.add_assoc, weight_lift]

theorem alive_lift : ∀ k q r, alive k (2 ^ k * q + r) = alive k r
  | 0, _, _ => rfl
  | k + 1, q, r => by
    have hs : 2 ^ (k + 1) * q + r = 2 ^ k * (2 * q) + r := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    simp only [alive, gap_lift]
    rw [hs, alive_lift]

theorem alive_gap_ne {k n : Nat} (hk : 0 < k) (h : alive k n = true) : gap k n ≠ 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hh : alive k n = true ∧ gap (k + 1) n ≠ 0 := by simpa [alive] using h
    exact hh.2

theorem stopped_of_alive {k n : Nat} (h : alive k n = true) :
    stopped (k + 1) n = (gap (k + 1) n).natAbs := by
  by_cases hz : gap (k + 1) n = 0 <;> simp [stopped, alive, h, hz]

theorem stopped_of_dead {k n : Nat} (h : alive k n = false) : stopped (k + 1) n = 0 := by
  simp [stopped, alive, h]

theorem endpoint_parity_flip (k n : Nat) :
    orbit k (2 ^ k + n) % 2 = 1 - orbit k n % 2 := by
  have ha := affine k 1 n
  simp only [Nat.mul_one] at ha
  have hp : 3 ^ wt k n % 2 = 1 := by simp [Nat.pow_mod]
  rw [ha, Nat.add_mod, hp]
  omega

theorem gap_snoc (k n : Nat) : gap (k + 1) n =
    gap k n + (orbit k n % 2 : Nat) - (orbit k (n + 1) % 2 : Nat) := by
  unfold gap
  rw [weight_snoc, weight_snoc]
  omega

theorem gap_snoc_lift (k n : Nat) : gap (k + 1) (2 ^ k + n) =
    gap k n + (1 - orbit k n % 2 : Nat) - (1 - orbit k (n + 1) % 2 : Nat) := by
  rw [gap_snoc]
  have hg := gap_lift k 1 n
  simp only [Nat.mul_one] at hg
  rw [hg, endpoint_parity_flip, Nat.add_assoc, endpoint_parity_flip]

theorem absolute_pair (d : Int) (a b : Nat) (hd : d ≠ 0) (ha : a ≤ 1) (hb : b ≤ 1) :
    (d + a - b).natAbs + (d + (1 - a : Nat) - (1 - b : Nat)).natAbs = 2 * d.natAbs := by
  by_cases hp : 0 ≤ d
  · have h0 := Int.natAbs_of_nonneg hp
    have h1 := Int.natAbs_of_nonneg (show 0 ≤ d + a - b by omega)
    have h2 := Int.natAbs_of_nonneg (show 0 ≤ d + (1 - a : Nat) - (1 - b : Nat) by omega)
    omega
  · have h0 := Int.ofNat_natAbs_of_nonpos (show d ≤ 0 by omega)
    have h1 := Int.ofNat_natAbs_of_nonpos (show d + a - b ≤ 0 by omega)
    have h2 := Int.ofNat_natAbs_of_nonpos (show d + (1 - a : Nat) - (1 - b : Nat) ≤ 0 by omega)
    omega

/-- The two next-bit children preserve the stopped absolute gap on average. -/
theorem stopped_children (k n : Nat) (hk : 0 < k) :
    stopped (k + 1) n + stopped (k + 1) (2 ^ k + n) = 2 * stopped k n := by
  have hl := alive_lift k 1 n
  simp only [Nat.mul_one] at hl
  cases h : alive k n with
  | false => rw [stopped_of_dead h, stopped_of_dead (hl.trans h)]; simp [stopped, h]
  | true =>
    rw [stopped_of_alive h, stopped_of_alive (hl.trans h), gap_snoc, gap_snoc_lift]
    simp only [stopped, h, ↓reduceIte]
    exact absolute_pair _ _ _ (alive_gap_ne hk h) (by omega) (by omega)

theorem stopped_bound (k n : Nat) : stopped k n ≤ k := by
  have h0 := weight_le_length k n
  have h1 := weight_le_length k (n + 1)
  have hb : (gap k n).natAbs ≤ k := by
    by_cases hp : 0 ≤ gap k n
    · have ha := Int.natAbs_of_nonneg hp
      unfold gap at *
      omega
    · have ha := Int.ofNat_natAbs_of_nonpos (show gap k n ≤ 0 by omega)
      unfold gap at *
      omega
  unfold stopped
  split <;> omega

def balanced (k n : Nat) : Bool :=
  decide (orbit k n = orbit k (n + 1) ∧ wt k n = wt k (n + 1))

def unmerged (k n : Nat) : Nat := if balanced k n then 0 else 1

theorem balanced_lift (k q r : Nat) : balanced k (2 ^ k * q + r) = balanced k r := by
  have hs : 2 ^ k * q + r + 1 = 2 ^ k * q + (r + 1) := Nat.add_assoc _ _ _
  unfold balanced
  rw [hs, weight_lift, weight_lift, affine, affine]
  by_cases hw : wt k r = wt k (r + 1)
  · simp [hw]
  · simp [hw]

theorem orbit_snoc : ∀ k n, orbit (k + 1) n = U (orbit k n)
  | 0, _ => rfl
  | k + 1, n => orbit_snoc k (U n)

theorem balanced_persists {k n : Nat} (h : balanced k n = true) : balanced (k + 1) n = true := by
  have hh := of_decide_eq_true h
  unfold balanced
  apply decide_eq_true
  constructor
  · rw [orbit_snoc, orbit_snoc, hh.1]
  · rw [weight_snoc, weight_snoc, hh.1, hh.2]

theorem stopped_zero_of_equal_weight {k n : Nat} (h : wt k n = wt k (n + 1)) :
    stopped k n = 0 := by simp [stopped, gap, h]

theorem stopped_bound_unmerged (k n : Nat) : stopped k n ≤ k * unmerged k n := by
  cases h : balanced k n with
  | false => simpa [unmerged, h] using stopped_bound k n
  | true =>
    have hw : wt k n = wt k (n + 1) := (of_decide_eq_true h).2
    rw [stopped_zero_of_equal_weight hw]
    omega

def total : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k + 1, f => total k f + f k

theorem total_add (a b : Nat) (f : Nat → Nat) :
    total (a + b) f = total a f + total b (fun r => f (a + r)) := by
  induction b with
  | zero => simp [total]
  | succ b ih =>
    change total (a + b) f + f (a + b) =
      total a f + (total b (fun r => f (a + r)) + f (a + b))
    rw [ih]
    omega

theorem total_sum (a : Nat) (f g : Nat → Nat) :
    total a (fun r => f r + g r) = total a f + total a g := by
  induction a with
  | zero => rfl
  | succ a ih => simp only [total, ih]; omega

theorem total_mul (a c : Nat) (f : Nat → Nat) :
    total a (fun r => c * f r) = c * total a f := by
  induction a with
  | zero => simp [total]
  | succ a ih => simp only [total, ih, Nat.mul_add]

theorem total_ext (a : Nat) (f g : Nat → Nat) (h : ∀ r, r < a → f r = g r) :
    total a f = total a g := by
  induction a with
  | zero => rfl
  | succ a ih => rw [total, total, ih (fun r hr => h r (by omega)), h a (by omega)]

theorem total_le (a : Nat) (f g : Nat → Nat) (h : ∀ r, r < a → f r ≤ g r) :
    total a f ≤ total a g := by
  induction a with
  | zero => exact Nat.le_refl 0
  | succ a ih =>
    have hx := ih (fun r hr => h r (by omega))
    have hy := h a (by omega)
    simp only [total]
    omega

/-- Exact all-depth mass, not a finite enumeration. -/
theorem stopped_mass (k : Nat) : total (2 ^ (k + 1)) (stopped (k + 1)) = 2 ^ (k + 1) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    have he := total_ext (2 ^ (k + 1))
      (fun r => stopped (k + 1 + 1) r + stopped (k + 1 + 1) (2 ^ (k + 1) + r))
      (fun r => 2 * stopped (k + 1) r)
      (fun r _ => stopped_children (k + 1) r (by omega))
    rw [he, total_mul, ih]
    omega

/-- At least a 1/k fraction of the full period is not balanced-coalescent. -/
theorem harmonic_tail (k : Nat) (hk : 0 < k) :
    2 ^ k ≤ k * total (2 ^ k) (unmerged k) := by
  have hm : total (2 ^ k) (stopped k) = 2 ^ k := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact stopped_mass j
  have h := total_le (2 ^ k) (stopped k) (fun r => k * unmerged k r)
    (fun r _ => stopped_bound_unmerged k r)
  rw [hm, total_mul] at h
  exact h

/-- Conditioning on either initial parity preserves the same unit mean. -/
theorem stopped_parity_mass (k e : Nat) (he : e < 2) :
    total (2 ^ k) (fun r => stopped (k + 1) (2 * r + e)) = 2 ^ k := by
  induction k with
  | zero =>
    have h : e = 0 ∨ e = 1 := by omega
    rcases h with h | h <;> subst e <;> decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_two, total_add, ← total_sum]
    have hh := total_ext (2 ^ k)
      (fun r => stopped (k + 1 + 1) (2 * r + e) +
        stopped (k + 1 + 1) (2 * (2 ^ k + r) + e))
      (fun r => 2 * stopped (k + 1) (2 * r + e)) (by
        intro r _
        have hs : 2 * (2 ^ k + r) + e = 2 ^ (k + 1) + (2 * r + e) := by
          rw [Nat.mul_add, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.add_assoc]
        rw [hs]
        exact stopped_children (k + 1) (2 * r + e) (by omega))
    rw [hh, total_mul, ih]
    omega

theorem parity_harmonic_tail (k e : Nat) (he : e < 2) :
    2 ^ k ≤ (k + 1) * total (2 ^ k) (fun r => unmerged (k + 1) (2 * r + e)) := by
  have h := total_le (2 ^ k) (fun r => stopped (k + 1) (2 * r + e))
    (fun r => (k + 1) * unmerged (k + 1) (2 * r + e))
    (fun r _ => stopped_bound_unmerged (k + 1) (2 * r + e))
  rw [stopped_parity_mass k e he, total_mul] at h
  exact h

#print axioms weight_lift
#print axioms weight_snoc
#print axioms weight_le_length
#print axioms gap_lift
#print axioms alive_lift
#print axioms alive_gap_ne
#print axioms stopped_of_alive
#print axioms stopped_of_dead
#print axioms endpoint_parity_flip
#print axioms gap_snoc
#print axioms gap_snoc_lift
#print axioms absolute_pair
#print axioms stopped_children
#print axioms stopped_bound
#print axioms balanced_lift
#print axioms orbit_snoc
#print axioms balanced_persists
#print axioms stopped_zero_of_equal_weight
#print axioms stopped_bound_unmerged
#print axioms stopped_mass
#print axioms harmonic_tail
#print axioms stopped_parity_mass
#print axioms parity_harmonic_tail
end CoalescenceTail
