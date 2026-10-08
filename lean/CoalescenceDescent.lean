/- Exact induction through a smaller coalescing start.
   This file does not prove the Collatz conjecture.
   Build CollatzAffine, CollatzContradiction, and CollatzGrowth into LEAN_PATH first. -/
import CollatzAffine
import CollatzContradiction
import CollatzGrowth

namespace CoalescenceDescent
open CollatzAffine

def WeakDescent (n : Nat) : Prop :=
  ∃ m, 0 < m ∧ m < n ∧ ∃ a b, orbit a n = orbit b m

theorem orbit_bridge : ∀ k n, orbit k n = OrdinaryCollatz.shortcutIter k n
  | 0, _ => rfl
  | k + 1, n => by
    simpa only [orbit, OrdinaryCollatz.shortcutIter, U, OrdinaryCollatz.U]
      using orbit_bridge k (U n)

theorem orbit_positive : ∀ k n, 0 < n → 0 < orbit k n
  | 0, _, h => h
  | k + 1, n, h => by
    apply orbit_positive k (U n)
    unfold U
    split <;> omega

theorem coalescence_transfer {n m a b : Nat} (h : orbit a n = orbit b m)
    (hm : OrdinaryCollatz.ReachesOne m) : OrdinaryCollatz.ReachesOne n := by
  rw [orbit_bridge, orbit_bridge] at h
  obtain ⟨i, _, _, hi⟩ := OrdinaryCollatz.shortcut_iteration_simulation a n
  obtain ⟨j, _, _, hj⟩ := OrdinaryCollatz.shortcut_iteration_simulation b m
  have hc := OrdinaryCollatz.reaches_after_iterate j m hm
  rw [hj, ← h, ← hi] at hc
  exact OrdinaryCollatz.reaches_of_iterate hc

/-- Meeting a smaller orbit is enough; the meeting point need not be small. -/
theorem conjecture_iff_weak_descent : OrdinaryCollatz.Conjecture ↔
    ∀ n, 1 < n → WeakDescent n := by
  constructor
  · intro hc n hn
    obtain ⟨k, hk⟩ := OrdinaryCollatz.shortcut_reaches_of_ordinary (hc n (by omega))
    exact ⟨1, by omega, hn, k, 0,
      by simpa [orbit_bridge, OrdinaryCollatz.shortcutIter] using hk⟩
  · intro hw n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      by_cases h1 : n = 1
      · rw [h1]; exact OrdinaryCollatz.reaches_one
      · obtain ⟨m, hm, hmn, a, b, hab⟩ := hw n (by omega)
        exact coalescence_transfer hab (ih m hmn hm)

theorem shorter_affine (k t r q : Nat) (ht : t ≤ k) :
    orbit t (2 ^ k * q + r) =
      (3 ^ wt t r * 2 ^ (k - t)) * q + orbit t r := by
  have he : 2 ^ k = 2 ^ t * 2 ^ (k - t) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le ht]
  rw [he, Nat.mul_assoc, affine]
  simp only [Nat.mul_assoc]

structure Certificate where
  r : Nat
  t : Nat
  merge : Bool
  target : Nat
  deriving DecidableEq, Repr

def baseQuotient (r : Nat) : Nat := if r ≤ 1 then 1 else 0

def check (k : Nat) (c : Certificate) : Bool :=
  decide (c.t ≤ k ∧ c.r < 2 ^ k) &&
  if c.merge then
    decide (0 < c.target ∧ c.target < c.r ∧
      wt c.t c.r = wt c.t c.target ∧ orbit c.t c.r = orbit c.t c.target)
  else
    let A := 3 ^ wt c.t c.r * 2 ^ (k - c.t)
    decide (A ≤ 2 ^ k ∧ A * baseQuotient c.r + orbit c.t c.r <
      2 ^ k * baseQuotient c.r + c.r)

theorem check_sound (k : Nat) (c : Certificate) (hc : check k c = true)
    (q : Nat) (hn : 1 < 2 ^ k * q + c.r) :
    WeakDescent (2 ^ k * q + c.r) := by
  have h := Bool.and_eq_true_iff.mp hc
  have hkt := (of_decide_eq_true h.1).1
  by_cases hm : c.merge = true
  · have hd := h.2
    simp only [hm, ↓reduceIte] at hd
    obtain ⟨hpos, hlt, hw, ho⟩ := of_decide_eq_true hd
    refine ⟨2 ^ k * q + c.target, by omega, by omega, c.t, c.t, ?_⟩
    rw [shorter_affine k c.t c.r q hkt, shorter_affine k c.t c.target q hkt, hw, ho]
  · have hf : c.merge = false := by cases he : c.merge <;> simp_all
    have hd := h.2
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hd
    obtain ⟨hslope, hbase⟩ := of_decide_eq_true hd
    have hq : baseQuotient c.r ≤ q := by
      unfold baseQuotient
      split
      · by_cases hz : q = 0
        · simp only [hz, Nat.mul_zero, Nat.zero_add] at hn
          omega
        · omega
      · omega
    have hl := affine_descent_mono hslope hbase hq
    rw [← shorter_affine k c.t c.r q hkt] at hl
    exact ⟨orbit c.t (2 ^ k * q + c.r), orbit_positive _ _ (by omega),
      hl, c.t, 0, rfl⟩

/-- Three classes not covered by direct descent within eight steps. -/
theorem new_merge_classes (q : Nat) :
    WeakDescent (256 * q + 63) ∧
    WeakDescent (256 * q + 207) ∧
    WeakDescent (256 * q + 223) := by
  exact ⟨check_sound 8 ⟨63, 8, true, 62⟩ (by decide) q (by dsimp; omega),
    check_sound 8 ⟨207, 6, true, 206⟩ (by decide) q (by dsimp; omega),
    check_sound 8 ⟨223, 7, true, 222⟩ (by decide) q (by dsimp; omega)⟩

#print axioms conjecture_iff_weak_descent
#print axioms shorter_affine
#print axioms check_sound
#print axioms new_merge_classes

def remaining8 : List Nat :=
  [27, 31, 47, 71, 91, 103, 111, 127, 155, 159, 167, 191, 231, 239, 251, 255]

/-- Search only direct certificates; three explicit merges supplement them. -/
def candidate8 (r : Nat) : Certificate :=
  if r = 63 then ⟨r, 8, true, 62⟩
  else if r = 207 then ⟨r, 6, true, 206⟩
  else if r = 223 then ⟨r, 7, true, 222⟩
  else ⟨r, ((List.range 9).find? (fun t => check 8 ⟨r, t, false, 0⟩)).getD 0,
    false, 0⟩

theorem candidate8_residue (r : Nat) : (candidate8 r).r = r := by
  unfold candidate8
  split <;> (try rfl)
  split <;> (try rfl)
  split <;> rfl

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem table8_valid : ∀ r : Fin 256,
    r.val ∉ remaining8 → check 8 (candidate8 r.val) = true := by decide

theorem outside_remaining8 (n : Nat) (hn : 1 < n)
    (hr : n % 256 ∉ remaining8) : WeakDescent n := by
  have hc := table8_valid ⟨n % 256, Nat.mod_lt _ (by decide)⟩ hr
  have he : 2 ^ 8 * (n / 256) + (candidate8 (n % 256)).r = n := by
    rw [candidate8_residue]
    exact Nat.div_add_mod n 256
  have hw := check_sound 8 (candidate8 (n % 256)) hc (n / 256) (by omega)
  rwa [he] at hw

theorem least_remaining8 {n : Nat} (hn : OrdinaryCollatz.LeastCounterexample n) :
    n % 256 ∈ remaining8 := by
  apply Classical.byContradiction
  intro hr
  obtain ⟨m, hm, hmn, a, b, hab⟩ := outside_remaining8 n
    (OrdinaryCollatz.least_gt_one hn) hr
  exact hn.2.1 (coalescence_transfer hab (hn.2.2 m hm hmn))

/-- The outstanding universal claim, not an assertion that it holds. -/
theorem conjecture_iff_remaining8 : OrdinaryCollatz.Conjecture ↔
    ∀ n, 1 < n → n % 256 ∈ remaining8 → WeakDescent n := by
  rw [conjecture_iff_weak_descent]
  constructor
  · intro h n hn _; exact h n hn
  · intro h n hn
    by_cases hr : n % 256 ∈ remaining8
    · exact h n hn hr
    · exact outside_remaining8 n hn hr

#print axioms table8_valid
#print axioms outside_remaining8
#print axioms least_remaining8
#print axioms conjecture_iff_remaining8

/-- A discrete bound useful for pulling a lower bound back through an orbit. -/
theorem orbit_lt_scaled : ∀ k n q : Nat,
    n < 2 ^ k * q → orbit k n < 3 ^ wt k n * q
  | 0, n, q, hn => by simpa [orbit, wt] using hn
  | k + 1, n, q, hn => by
    have hh : n < 2 * (2 ^ k * q) := by
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn
    by_cases hp : n % 2 = 1
    · have hu : U n < 2 ^ k * (3 * q) := by
        have he : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := by
          simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        rw [he]
        unfold U
        rw [if_pos hp]
        omega
      have ht := orbit_lt_scaled k (U n) (3 * q) hu
      simpa [orbit, wt, hp, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using ht
    · have hz : n % 2 = 0 := by omega
      have hu : U n < 2 ^ k * q := by
        unfold U
        rw [if_neg hp]
        omega
      have ht := orbit_lt_scaled k (U n) q hu
      simpa [orbit, wt, hz] using ht

theorem orbit_ge_scaled (k n q : Nat) (h : 3 ^ wt k n * q ≤ orbit k n) :
    2 ^ k * q ≤ n := by
  by_cases hn : n < 2 ^ k * q
  · have := orbit_lt_scaled k n q hn; omega
  · omega

theorem weight_le : ∀ k n, wt k n ≤ k
  | 0, _ => by simp [wt]
  | k + 1, n => by
    have := weight_le k (U n)
    simp only [wt]
    omega

/-- This includes a sharp lower bound on the affine additive numerator. -/
theorem orbit_plus_one_lower : ∀ k n,
    3 ^ wt k n * (n + 1) ≤ 2 ^ k * (orbit k n + 1)
  | 0, _ => by simp [wt, orbit]
  | k + 1, n => by
    have ht := orbit_plus_one_lower k (U n)
    have hs : 3 ^ (n % 2) * (n + 1) ≤ 2 * (U n + 1) := by
      by_cases hp : n % 2 = 1
      · simp only [hp, Nat.pow_one, U, if_pos]
        omega
      · have hz : n % 2 = 0 := by omega
        simp only [U, if_neg hp]
        simp only [hz, Nat.pow_zero, Nat.one_mul]
        omega
    have h1 := Nat.mul_le_mul_left (3 ^ wt k (U n)) hs
    have h2 := Nat.mul_le_mul_left 2 ht
    simp only [orbit, wt, Nat.pow_add, Nat.pow_succ]
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
      Nat.le_trans h1 (by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2)

/-- Every branch word's additive numerator is at most that of all odd steps. -/
theorem orbit_intercept_upper : ∀ k n,
    2 ^ k * (orbit k n + 1) ≤ 3 ^ wt k n * n + 3 ^ k
  | 0, _ => by simp [wt, orbit]
  | k + 1, n => by
    have ht := Nat.mul_le_mul_left 2 (orbit_intercept_upper k (U n))
    have hw : 3 ^ wt k (U n) ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by decide) (weight_le k (U n))
    by_cases hp : n % 2 = 1
    · have hs : 2 * U n = 3 * n + 1 := by
        simp only [U, if_pos hp]; omega
      have he : 2 * (3 ^ wt k (U n) * U n) =
          3 * (3 ^ wt k (U n) * n) + 3 ^ wt k (U n) := by
        calc
          _ = 3 ^ wt k (U n) * (2 * U n) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = _ := by rw [hs]; simp [Nat.add_mul, Nat.mul_assoc,
            Nat.mul_comm, Nat.mul_left_comm]
      rw [Nat.mul_add 2 (3 ^ wt k (U n) * U n) (3 ^ k)] at ht
      rw [he] at ht
      have hg : 2 * (2 ^ k * (orbit k (U n) + 1)) ≤
          3 * (3 ^ wt k (U n) * n) + 3 * 3 ^ k := by omega
      simpa [orbit, wt, hp, Nat.pow_add, Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hg
    · have hz : n % 2 = 0 := by omega
      have hs : 2 * U n = n := by simp only [U, if_neg hp]; omega
      have he : 2 * (3 ^ wt k (U n) * U n) = 3 ^ wt k (U n) * n := by
        calc
          _ = 3 ^ wt k (U n) * (2 * U n) := by
            simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          _ = _ := by rw [hs]
      rw [Nat.mul_add 2 (3 ^ wt k (U n) * U n) (3 ^ k)] at ht
      rw [he] at ht
      have hg : 2 * (2 ^ k * (orbit k (U n) + 1)) ≤
          3 ^ wt k (U n) * n + 3 * 3 ^ k := by omega
      simpa [orbit, wt, hz, Nat.pow_succ, Nat.mul_assoc,
        Nat.mul_comm, Nat.mul_left_comm] using hg

theorem orbit_add (c a m : Nat) : orbit (c + a) m = orbit a (orbit c m) := by
  induction c generalizing m with
  | zero => simp [orbit]
  | succ c ih => simpa [Nat.succ_add, orbit] using ih (U m)

/-- Pulling back a maximally growing orbit cannot help at a divisible start. -/
theorem coalescence_divisible_bound (a c n m : Nat)
    (hgrowth : 2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1))
    (hdiv : 3 ^ wt c m ∣ n)
    (hmeet : orbit (c + a) m = orbit a n) : n ≤ m := by
  let z := orbit c m
  let i := wt c m
  let h := wt a z
  have hmeet' : orbit a z = orbit a n := by
    simpa only [orbit_add] using hmeet
  have hh : h ≤ a := weight_le a z
  have hp : 3 ^ a = 3 ^ h * 3 ^ (a - h) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hh]
  have hupper := orbit_intercept_upper a z
  rw [hmeet', hgrowth] at hupper
  have hscaled : 3 ^ a * n ≤ 3 ^ h * z := by
    change 3 ^ a * (n + 1) ≤ 3 ^ h * z + 3 ^ a at hupper
    rw [Nat.mul_add, Nat.mul_one] at hupper
    omega
  rw [hp, Nat.mul_assoc] at hscaled
  have hbase : 3 ^ (a - h) * n ≤ z :=
    Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by decide))
  obtain ⟨q, hq⟩ := hdiv
  let T := 3 ^ (a - h) * q
  have hT : 3 ^ i * T ≤ z := by
    simpa [T, hq, i, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hbase
  have hm : 2 ^ c * T ≤ m := orbit_ge_scaled c m T hT
  let A := 3 ^ h * 3 ^ i
  let B := 2 ^ c * 3 ^ a
  have hidentity : A * (2 ^ c * T) = B * n := by
    rw [hq]
    simp [A, B, T, i, hp, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have hAm : B * n ≤ A * m := by
    rw [← hidentity]
    exact Nat.mul_le_mul_left A hm
  have hl1 := Nat.mul_le_mul_left (3 ^ h) (orbit_plus_one_lower c m)
  have hl2 := Nat.mul_le_mul_left (2 ^ c) (orbit_plus_one_lower a z)
  rw [hmeet', hgrowth] at hl2
  have hAB : A * (m + 1) ≤ B * (n + 1) := by
    apply Nat.le_trans (by simpa [A, i, z, Nat.mul_assoc] using hl1)
    simpa [B, h, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hl2
  have hAB' : A ≤ B := by
    simp only [Nat.mul_add, Nat.mul_one] at hAB
    omega
  have hAn : A * n ≤ A * m := Nat.le_trans (Nat.mul_le_mul_right n hAB') hAm
  exact Nat.le_of_mul_le_mul_left hAn
    (Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide)))

theorem shorter_meeting_bound (a b n m : Nat) (hb : b ≤ a)
    (hgrowth : 2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1))
    (hmeet : orbit b m = orbit a n) : n ≤ m := by
  have h2 : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hb]
  have h3 : 3 ^ a = 3 ^ (a - b) * 3 ^ b := by
    rw [← Nat.pow_add, Nat.sub_add_cancel hb]
  have hp : 2 ^ (a - b) ≤ 3 ^ (a - b) := Nat.pow_le_pow_left (by decide) _
  have hlo := Nat.mul_le_mul_right (3 ^ b * (n + 1)) hp
  rw [h2, h3, Nat.mul_assoc, Nat.mul_assoc] at hgrowth
  rw [← hgrowth] at hlo
  have hlow := Nat.le_of_mul_le_mul_left hlo (Nat.pow_pos (by decide))
  have hu := orbit_intercept_upper b m
  have hw : 3 ^ wt b m ≤ 3 ^ b :=
    Nat.pow_le_pow_right (by decide) (weight_le b m)
  have hm := Nat.mul_le_mul_right m hw
  rw [hmeet] at hu
  have hf : 3 ^ b * (n + 1) ≤ 3 ^ b * (m + 1) := by
    calc
      _ ≤ 2 ^ b * (orbit a n + 1) := hlow
      _ ≤ 3 ^ wt b m * m + 3 ^ b := hu
      _ ≤ 3 ^ b * m + 3 ^ b := Nat.add_le_add_right hm _
      _ = _ := by rw [Nat.mul_add, Nat.mul_one]
  have := Nat.le_of_mul_le_mul_left hf (Nat.pow_pos (by decide))
  omega

/-- Universal arithmetic obstruction, conditional only on the stated start data. -/
theorem bounded_meeting_bound (K a b n m : Nat) (hb : b ≤ K)
    (hdiv : 3 ^ K ∣ n)
    (hgrowth : 2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1))
    (hmeet : orbit b m = orbit a n) : n ≤ m := by
  by_cases hab : b ≤ a
  · exact shorter_meeting_bound a b n m hab hgrowth hmeet
  · have ha : a ≤ b := by omega
    have hi : wt (b - a) m ≤ K := Nat.le_trans (weight_le _ _) (by omega)
    have hd : 3 ^ wt (b - a) m ∣ 3 ^ K := by
      refine ⟨3 ^ (K - wt (b - a) m), ?_⟩
      rw [← Nat.pow_add, Nat.add_sub_of_le hi]
    apply coalescence_divisible_bound a (b - a) n m hgrowth (Nat.dvd_trans hd hdiv)
    simpa [Nat.sub_add_cancel ha] using hmeet

theorem growth_orbit_bridge : ∀ k n, orbit k n = CollatzGrowth.orbit k n
  | 0, _ => rfl
  | k + 1, n => by
    simpa only [orbit, CollatzGrowth.orbit, U, CollatzGrowth.U]
      using growth_orbit_bridge k (U n)

theorem odd_prefix_growth (a n : Nat) (hdiv : 2 ^ a ∣ n + 1) :
    2 ^ a * (orbit a n + 1) = 3 ^ a * (n + 1) := by
  obtain ⟨q, hq⟩ := hdiv
  have hpos : 0 < q := by
    by_cases hz : q = 0
    · simp only [hz, Nat.mul_zero] at hq; omega
    · omega
  have hn : n = 2 ^ (a + 0) * q - 1 := by simp only [Nat.add_zero]; omega
  have hf := CollatzGrowth.growth_formula a 0 q hpos
  have hp : 0 < 3 ^ a * q := Nat.mul_pos (Nat.pow_pos (by decide)) hpos
  have he : orbit a n = 3 ^ a * q - 1 := by
    rw [growth_orbit_bridge, hn, hf]
    simp only [Nat.pow_zero, Nat.one_mul]
  rw [he, Nat.sub_add_cancel hp, hq]
  simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- No meeting with a smaller start within either bounded time on the CRT class. -/
theorem crt_class_meeting_bound (K a b n m : Nat) (ha : a ≤ K) (hb : b ≤ K)
    (h2 : 2 ^ K ∣ n + 1) (h3 : 3 ^ K ∣ n)
    (hmeet : orbit b m = orbit a n) : n ≤ m := by
  apply bounded_meeting_bound K a b n m hb h3
  · exact odd_prefix_growth a n (Nat.dvd_trans (Nat.pow_dvd_pow 2 ha) h2)
  · exact hmeet

/-- A constructive alternative to invoking the Chinese remainder theorem. -/
theorem growing_divisible_starts : ∀ K : Nat, ∃ n : Nat,
    1 < n ∧ 2 ^ (K + 1) ∣ n + 1 ∧ 3 ^ (K + 1) ∣ n
  | 0 => ⟨3, by decide, by decide, by decide⟩
  | K + 1 => by
    obtain ⟨n, hn, h2, h3⟩ := growing_divisible_starts K
    let N := n * (n * n + 3 * n + 3)
    have hN : 1 < N := by
      have hh : n ≤ N := Nat.le_mul_of_pos_right n (by omega)
      omega
    have he : N + 1 = (n + 1) * (n + 1) * (n + 1) := by
      dsimp [N]
      grind
    have ht : 2 ∣ n + 1 := Nat.dvd_trans
      (by simpa using Nat.pow_dvd_pow 2 (show 1 ≤ K + 1 by omega)) h2
    have h2N : 2 ^ (K + 1 + 1) ∣ N + 1 := by
      rw [he, Nat.pow_succ]
      exact Nat.dvd_trans (Nat.mul_dvd_mul h2 ht) (Nat.dvd_mul_right _ _)
    have hthree : 3 ∣ n := Nat.dvd_trans
      (by simpa using Nat.pow_dvd_pow 3 (show 1 ≤ K + 1 by omega)) h3
    have hfactor : 3 ∣ n * n + 3 * n + 3 := by
      obtain ⟨s, hs⟩ := hthree
      refine ⟨s * n + n + 1, ?_⟩
      rw [hs]
      grind
    have h3N : 3 ^ (K + 1 + 1) ∣ N := by
      rw [Nat.pow_succ]
      exact Nat.mul_dvd_mul h3 hfactor
    exact ⟨N, hN, h2N, h3N⟩

/-- Even allowing different times and arbitrary smaller starts leaves no
    uniform finite meeting horizon. This is not a divergent orbit. -/
theorem no_uniform_coalescence_horizon (K : Nat) : ∃ n : Nat, 1 < n ∧
    ∀ m a b : Nat, m < n → a ≤ K → b ≤ K → orbit a n ≠ orbit b m := by
  obtain ⟨n, hn, h2, h3⟩ := growing_divisible_starts K
  refine ⟨n, hn, ?_⟩
  intro m a b hm ha hb he
  have hl := crt_class_meeting_bound (K + 1) a b n m
    (by omega) (by omega) h2 h3 he.symm
  omega

#print axioms orbit_lt_scaled
#print axioms orbit_ge_scaled
#print axioms orbit_plus_one_lower
#print axioms orbit_intercept_upper
#print axioms coalescence_divisible_bound
#print axioms shorter_meeting_bound
#print axioms bounded_meeting_bound
#print axioms odd_prefix_growth
#print axioms crt_class_meeting_bound
#print axioms growing_divisible_starts
#print axioms no_uniform_coalescence_horizon
end CoalescenceDescent
