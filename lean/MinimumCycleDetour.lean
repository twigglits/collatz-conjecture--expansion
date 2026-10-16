/- Positive inverse lifts of the negative seventeen cycle.
   Parameterized coalescence and strict source reductions, not convergence. -/
import MinimumInverseEscape

namespace MinimumCycleDetour
open OrdinaryCollatz MinimumTailRigidity MinimumClockBarrier
open MinimumRootPredecessors MinimumReturnLadder MinimumInverseEscape

theorem cycle_block (q : Nat) (hq : 0 < q) :
    Backtrack 4 7 (2187 * q - 17) (2048 * q - 17) := by
  have h0 := Backtrack.nil (2187 * q - 17)
  have h1 := Backtrack.even h0
  have h2 := Backtrack.even h1
  have h3 := Backtrack.even h2
  have h4 := Backtrack.odd h3
    (show 3 * (11664 * q - 91) + 1 = 2 * (2 * (2 * (2 * (2187 * q - 17)))) by omega)
  have h5 := Backtrack.odd h4
    (show 3 * (7776 * q - 61) + 1 = 2 * (11664 * q - 91) by omega)
  have h6 := Backtrack.odd h5
    (show 3 * (5184 * q - 41) + 1 = 2 * (7776 * q - 61) by omega)
  have h7 := Backtrack.even h6
  have h8 := Backtrack.odd h7
    (show 3 * (6912 * q - 55) + 1 = 2 * (2 * (5184 * q - 41)) by omega)
  have h9 := Backtrack.odd h8
    (show 3 * (4608 * q - 37) + 1 = 2 * (6912 * q - 55) by omega)
  have h10 := Backtrack.odd h9
    (show 3 * (3072 * q - 25) + 1 = 2 * (4608 * q - 37) by omega)
  exact Backtrack.odd h10 (by omega)

theorem cycle_inverse (k q : Nat) (hq : 0 < q) :
    Backtrack (4 * k) (7 * k) (3 ^ (7 * k) * q - 17) (2 ^ (11 * k) * q - 17) := by
  induction k generalizing q with
  | zero => simpa using Backtrack.nil (q - 17)
  | succ k ih =>
    have hq3 := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 3) (n := 7 * k)) hq
    have hb := cycle_block (3 ^ (7 * k) * q) hq3
    have hp := ih (2048 * q) (by omega)
    have hmid : 3 ^ (7 * k) * (2048 * q) = 2048 * (3 ^ (7 * k) * q) := by ac_rfl
    rw [hmid] at hp
    have hc := backtrack_append hb hp
    have h3 : 3 ^ (7 * (k + 1)) * q = 2187 * (3 ^ (7 * k) * q) := by
      have he : 7 * (k + 1) = 7 * k + 7 := by omega
      rw [he, Nat.pow_add]
      change (3 ^ (7 * k) * 2187) * q = _
      ac_rfl
    have h2 : 2 ^ (11 * (k + 1)) * q = 2 ^ (11 * k) * (2048 * q) := by
      have he : 11 * (k + 1) = 11 * k + 11 := by omega
      rw [he, Nat.pow_add]
      change (2 ^ (11 * k) * 2048) * q = _
      ac_rfl
    rw [h3, h2]
    have he : 4 * (k + 1) = 4 + 4 * k := by omega
    have ho : 7 * (k + 1) = 7 + 7 * k := by omega
    rw [he, ho]
    exact hc

theorem cycle_clock (k q : Nat) (hq : 0 < q) :
    iterate (18 * k) (2 ^ (11 * k) * q - 17) = 3 ^ (7 * k) * q - 17 := by
  have hh := backtrack_actual (cycle_inverse k q hq)
  have ht : 4 * k + 2 * (7 * k) = 18 * k := by omega
  rw [ht] at hh
  exact hh

theorem detour_lift (n k q : Nat) (hk : 0 < k)
    (he : 3 ^ (7 * k - 1) * q = n + 6) : 3 ^ (7 * k) * q - 17 = 3 * n + 1 := by
  have ht : 7 * k = (7 * k - 1) + 1 := by omega
  have hpow : 3 ^ (7 * k) = 3 ^ (7 * k - 1) * 3 := by
    calc
      _ = 3 ^ ((7 * k - 1) + 1) := congrArg (fun t => 3 ^ t) ht
      _ = _ := Nat.pow_succ _ _
  have hm : 3 ^ (7 * k) * q = 3 * (3 ^ (7 * k - 1) * q) := by
    rw [hpow]
    ac_rfl
  rw [hm, he]
  omega

theorem cycle_detour (n k q : Nat) (hn : n % 2 = 1) (hk : 0 < k) (hq : 0 < q)
    (he : 3 ^ (7 * k - 1) * q = n + 6) :
    Backtrack (4 * k + 1) (7 * k) (iterate 2 n) (2 ^ (11 * k) * q - 17) := by
  have hb := Backtrack.even (Backtrack.nil (iterate 2 n))
  have hm := odd_meeting n hn
  rw [hm] at hb
  have hc := cycle_inverse k q hq
  rw [detour_lift n k q hk he] at hc
  have hh := backtrack_append hb hc
  simpa only [Nat.zero_add, Nat.add_comm] using hh

theorem detour_meeting (n k q : Nat) (hn : n % 2 = 1) (hk : 0 < k) (hq : 0 < q)
    (he : 3 ^ (7 * k - 1) * q = n + 6) :
    iterate (18 * k) (2 ^ (11 * k) * q - 17) = iterate 1 n := by
  rw [cycle_clock k q hq, detour_lift n k q hk he]
  change _ = C n
  unfold C
  rw [if_pos hn]

theorem seventeen_gain (k : Nat) (hk : 17 ≤ k) : 2 ^ (11 * k) < 3 ^ (7 * k - 1) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hbase : 2 ^ 187 < 3 ^ 118 := by decide +kernel
  have hs : 2048 ^ a ≤ 2187 ^ a := Nat.pow_le_pow_left (by decide) a
  have hp := Nat.pow_pos (by decide : 0 < 2048) (n := a)
  have he2 : 11 * (17 + a) = 187 + 11 * a := by omega
  have he3 : 7 * (17 + a) - 1 = 118 + 7 * a := by omega
  rw [he2, he3, Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul]
  exact Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hbase hp)
    (Nat.mul_le_mul_left _ hs)

theorem detour_smaller (n k q : Nat) (hk : 17 ≤ k) (hq : 0 < q)
    (he : 3 ^ (7 * k - 1) * q = n + 6) :
    0 < 2 ^ (11 * k) * q - 17 ∧ 2 ^ (11 * k) * q - 17 < n := by
  have hg := Nat.mul_lt_mul_of_pos_right (seventeen_gain k hk) hq
  have hp : 32 ≤ 2 ^ (11 * k) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 11 * k by omega)
  have hpos := Nat.mul_le_mul_left (2 ^ (11 * k)) hq
  rw [he] at hg
  omega

theorem least_cycle_exclusion {n : Nat} (hn : LeastCounterexample n) (k : Nat) (hk : 17 ≤ k) :
    ¬ 3 ^ (7 * k - 1) ∣ n + 6 := by
  intro hd
  obtain ⟨q, hq⟩ := hd
  have he : 3 ^ (7 * k - 1) * q = n + 6 := hq.symm
  have hqp : 0 < q := by
    by_cases h : q = 0
    · rw [h, Nat.mul_zero] at he
      omega
    · omega
  have hs := detour_smaller n k q hk hqp he
  have ho : n % 2 = 1 := by have hh := least_mod4 hn; omega
  have hc := least_coalescing_predecessor hn hs.1
    (detour_meeting n k q ho (by omega) hqp he)
  omega

theorem odd_power_factor (x h : Nat) (hx : 0 < x) : x + 1 ∣ x ^ (2 * h + 1) + 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    obtain ⟨q, hq⟩ := ih
    have hqp : 0 < q := by
      by_cases hz : q = 0
      · rw [hz, Nat.mul_zero] at hq
        omega
      · omega
    have hxx : x ≤ x * x := by have hh := Nat.mul_le_mul_left x hx; omega
    have hbig : x ≤ x * x * q := by
      have hh := Nat.mul_le_mul_left (x * x) hqp
      omega
    refine ⟨x * x * q - x + 1, ?_⟩
    have ht : 2 * (h + 1) + 1 = (2 * h + 1) + 2 := by omega
    have hsub := Nat.sub_add_cancel hbig
    have hp2 : x ^ 2 = x * x := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    rw [ht, Nat.pow_add, hp2]
    grind only

theorem cube_lift (a x : Nat) (hd : 3 ^ (a + 2) ∣ x + 1) :
    3 ^ (a + 3) ∣ x ^ 3 + 1 := by
  have h3 : 3 ∣ x + 1 := Nat.dvd_trans
    (Nat.pow_dvd_pow 3 (show 1 ≤ a + 2 by omega)) hd
  have hr : x % 3 = 2 := by omega
  have hx : 0 < x := by omega
  have hxx : x ≤ x * x := by have hh := Nat.mul_le_mul_left x hx; omega
  have hres : (x * x) % 3 = 1 := by rw [Nat.mul_mod, hr]
  have hfactor : 3 ∣ x * x - x + 1 := by omega
  have hc := Nat.mul_dvd_mul hd hfactor
  have hsub := Nat.sub_add_cancel hxx
  have hp : (x + 1) * (x * x - x + 1) = x ^ 3 + 1 := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    grind only
  have he : a + 3 = (a + 2) + 1 := by omega
  rw [hp, ← Nat.pow_succ] at hc
  change 3 ^ ((a + 2) + 1) ∣ x ^ 3 + 1 at hc
  rw [← he] at hc
  exact hc

theorem ternary_lift (a : Nat) : 3 ^ (a + 2) ∣ 8 ^ (3 ^ a) + 1 := by
  induction a with
  | zero => decide
  | succ a ih =>
    have hc := cube_lift a (8 ^ (3 ^ a)) ih
    have ht : 8 ^ (3 ^ (a + 1)) = (8 ^ (3 ^ a)) ^ 3 := by
      rw [Nat.pow_succ, Nat.pow_mul]
    rw [ht]
    simpa only [Nat.add_assoc] using hc

theorem ladder_divisibility (a h : Nat) :
    3 ^ (a + 2) ∣ 8 ^ (3 ^ a * (2 * h + 1)) + 1 := by
  have hf := odd_power_factor (8 ^ (3 ^ a)) h (Nat.pow_pos (by decide : 0 < 8))
  have hd := Nat.dvd_trans (ternary_lift a) hf
  simpa only [Nat.pow_mul] using hd

def ladderExponent (k h : Nat) : Nat := 3 ^ (7 * k - 3) * (2 * h + 1)
def ladderSource (k h : Nat) : Nat := 8 ^ ladderExponent k h - 5
def ladderQuotient (k h : Nat) : Nat := (8 ^ ladderExponent k h + 1) / 3 ^ (7 * k - 1)
def ladderPredecessor (k h : Nat) : Nat := 2 ^ (11 * k) * ladderQuotient k h - 17

theorem ladder_parameters (k h : Nat) (hk : 0 < k) :
    3 ≤ ladderExponent k h ∧ ladderExponent k h % 2 = 1 ∧
    ladderSource k h = blockValue (ladderExponent k h) 0 ∧ ladderSource k h % 2 = 1 := by
  have hp : 3 ≤ 3 ^ (7 * k - 3) :=
    Nat.pow_le_pow_right (by decide : 0 < 3) (show 1 ≤ 7 * k - 3 by omega)
  have hh := Nat.mul_le_mul_left (3 ^ (7 * k - 3)) (show 1 ≤ 2 * h + 1 by omega)
  have hR : 3 ≤ ladderExponent k h := by unfold ladderExponent; omega
  have ho : ladderExponent k h % 2 = 1 := by
    unfold ladderExponent
    rw [Nat.mul_mod, Nat.pow_mod]
    simp
  have hv : 8 ≤ 8 ^ ladderExponent k h :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ ladderExponent k h by omega)
  have he : ladderExponent k h = (ladderExponent k h - 1) + 1 := by omega
  have hr : 8 ^ ladderExponent k h % 2 = 0 := by rw [he, Nat.pow_succ, Nat.mul_mod]; simp
  refine ⟨hR, ho, ?_, ?_⟩
  · simp only [ladderSource, blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero,
      Nat.pow_zero, Nat.mul_one, Nat.pow_mul]
  · unfold ladderSource
    omega

theorem ladder_lift (k h : Nat) (hk : 0 < k) :
    0 < ladderQuotient k h ∧ 3 ^ (7 * k - 1) * ladderQuotient k h = ladderSource k h + 6 := by
  have hd := ladder_divisibility (7 * k - 3) h
  have ht : 7 * k - 3 + 2 = 7 * k - 1 := by omega
  rw [ht] at hd
  change 3 ^ (7 * k - 1) ∣ 8 ^ ladderExponent k h + 1 at hd
  have he := Nat.mul_div_cancel' hd
  have hv : 8 ≤ 8 ^ ladderExponent k h := Nat.pow_le_pow_right (by decide : 0 < 8)
    (show 1 ≤ ladderExponent k h by have hh := (ladder_parameters k h hk).1; omega)
  change 3 ^ (7 * k - 1) * ladderQuotient k h = 8 ^ ladderExponent k h + 1 at he
  constructor
  · by_cases hz : ladderQuotient k h = 0
    · rw [hz, Nat.mul_zero] at he
      omega
    · omega
  · unfold ladderSource
    omega

theorem ladder_smaller (k h : Nat) (hk : 17 ≤ k) :
    0 < ladderPredecessor k h ∧ ladderPredecessor k h < ladderSource k h := by
  have hl := ladder_lift k h (by omega)
  exact detour_smaller _ k _ hk hl.1 hl.2

theorem ladder_meeting (k h : Nat) (hk : 0 < k) :
    iterate (18 * k) (ladderPredecessor k h) = iterate 1 (ladderSource k h) := by
  have hl := ladder_lift k h hk
  exact detour_meeting _ k _ (ladder_parameters k h hk).2.2.2 hk hl.1 hl.2

theorem ladder_later_inverse (k h i : Nat) (hk : 0 < k) (hi : i < ladderExponent k h) :
    Backtrack (i + 4 * k + 1) (2 * i + 7 * k)
      (hitValue (ladderExponent k h) i) (ladderPredecessor k h) := by
  have hl := ladder_lift k h hk
  have hc := cycle_detour _ k _ (ladder_parameters k h hk).2.2.2 hk hl.1 hl.2
  have hm : iterate 2 (ladderSource k h) = hitValue (ladderExponent k h) 0 := by
    rw [(ladder_parameters k h hk).2.2.1]
    exact hit_clock _ 0 (by omega)
  rw [hm] at hc
  have hb := backtrack_append (hit_to_initial _ i hi) hc
  simpa only [Nat.add_assoc, ladderPredecessor] using hb

theorem ladder_later_clock (k h i : Nat) (hk : 0 < k) (hi : i < ladderExponent k h) :
    iterate (5 * i + 18 * k + 1) (ladderPredecessor k h) = hitValue (ladderExponent k h) i := by
  have hh := backtrack_actual (ladder_later_inverse k h i hk hi)
  have ht : i + 4 * k + 1 + 2 * (2 * i + 7 * k) = 5 * i + 18 * k + 1 := by omega
  rw [ht] at hh
  exact hh

theorem ladder_not_least (k h : Nat) (hk : 17 ≤ k) : ¬ LeastCounterexample (ladderSource k h) := by
  intro ha
  have hs := ladder_smaller k h hk
  have hp := least_coalescing_predecessor ha hs.1 (ladder_meeting k h (by omega))
  omega

theorem amplified_gain (g : Nat) :
    3 ^ g * 2 ^ (11 * (17 * (g + 1))) < 3 ^ (7 * (17 * (g + 1)) - 1) := by
  have hb : 3 * 2 ^ 187 < 3 ^ 119 := by decide +kernel
  have hp := Nat.pow_lt_pow_left hb (show g + 1 ≠ 0 by omega)
  rw [Nat.mul_pow, ← Nat.pow_mul, ← Nat.pow_mul] at hp
  have h2 : 187 * (g + 1) = 11 * (17 * (g + 1)) := by omega
  have h3 : 119 * (g + 1) = 7 * (17 * (g + 1)) := by omega
  rw [h2, h3, Nat.pow_succ] at hp
  have ht : 7 * (17 * (g + 1)) = (7 * (17 * (g + 1)) - 1) + 1 := by omega
  have hpow : 3 ^ (7 * (17 * (g + 1))) = 3 ^ (7 * (17 * (g + 1)) - 1) * 3 := by
    calc
      _ = 3 ^ ((7 * (17 * (g + 1)) - 1) + 1) := congrArg (fun t => 3 ^ t) ht
      _ = _ := Nat.pow_succ _ _
  rw [hpow] at hp
  have hm : (3 ^ g * 3) * 2 ^ (11 * (17 * (g + 1))) =
      (3 ^ g * 2 ^ (11 * (17 * (g + 1)))) * 3 :=
    Nat.mul_right_comm _ _ _
  rw [hm] at hp
  omega

theorem amplified_detour (g n q : Nat) (hq : 0 < q)
    (he : 3 ^ (7 * (17 * (g + 1)) - 1) * q = n + 6) :
    3 ^ g * (2 ^ (11 * (17 * (g + 1))) * q - 17) < n := by
  have hp := Nat.mul_lt_mul_of_pos_right (amplified_gain g) hq
  have h2 : 32 ≤ 2 ^ (11 * (17 * (g + 1))) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 11 * (17 * (g + 1)) by omega)
  have hq2 := Nat.mul_le_mul_left (2 ^ (11 * (17 * (g + 1)))) hq
  have hs : 2 ^ (11 * (17 * (g + 1))) * q - 17 + 17 =
      2 ^ (11 * (17 * (g + 1))) * q := by omega
  have hh := congrArg (fun x => 3 ^ g * x) hs
  rw [Nat.mul_add] at hh
  have hg : 1 ≤ 3 ^ g := Nat.pow_pos (by decide : 0 < 3)
  rw [Nat.mul_assoc, he] at hp
  omega

theorem ladder_arbitrary_gain (g h : Nat) :
    0 < ladderPredecessor (17 * (g + 1)) h ∧
    3 ^ g * ladderPredecessor (17 * (g + 1)) h < ladderSource (17 * (g + 1)) h ∧
    iterate (306 * (g + 1)) (ladderPredecessor (17 * (g + 1)) h) =
      iterate 1 (ladderSource (17 * (g + 1)) h) := by
  have hk : 17 ≤ 17 * (g + 1) := by omega
  have hl := ladder_lift (17 * (g + 1)) h (by omega)
  have hs := ladder_smaller (17 * (g + 1)) h hk
  have hc := ladder_meeting (17 * (g + 1)) h (by omega)
  have ht : 18 * (17 * (g + 1)) = 306 * (g + 1) := by omega
  rw [ht] at hc
  exact ⟨hs.1, amplified_detour g _ _ hl.1 hl.2, hc⟩

theorem ladder_growth (k h : Nat) (hk : 0 < k) : h < ladderSource k h := by
  have hr := ladder_parameters k h hk
  have hg := MinimumReturnLadder.source_growth (ladderExponent k h) hr.1
  rw [← hr.2.2.1] at hg
  have hp : 1 ≤ 3 ^ (7 * k - 3) := Nat.pow_pos (by decide : 0 < 3)
  have hm := Nat.mul_le_mul_right (2 * h + 1) hp
  unfold ladderExponent at hg
  omega

theorem least_orbit_cycle_bound {A n t q : Nat} (g : Nat) (ha : LeastCounterexample A)
    (ht : iterate t A = n) (hn : n % 2 = 1) (hq : 0 < q)
    (he : 3 ^ (7 * (17 * (g + 1)) - 1) * q = n + 6) : 3 ^ g * A < n := by
  have hk : 17 ≤ 17 * (g + 1) := by omega
  have hs := detour_smaller n _ q hk hq he
  have hm : iterate (18 * (17 * (g + 1))) (2 ^ (11 * (17 * (g + 1))) * q - 17) =
      iterate (t + 1) A := by
    calc
      _ = iterate 1 n := detour_meeting n _ q hn (by omega) hq he
      _ = _ := by rw [iterate_add, ht]
  have hp := least_coalescing_predecessor ha hs.1 hm
  have hh := Nat.mul_le_mul_left (3 ^ g) hp
  exact Nat.lt_of_le_of_lt hh (amplified_detour g n q hq he)

theorem ladder_old_detour_residue (k h : Nat) (hk : 17 ≤ k) :
    (8 * ladderSource k h + 3) % 27 = 9 := by
  have hl := (ladder_lift k h (by omega)).2
  have he : 7 * k - 1 = (7 * k - 4) + 3 := by omega
  have hr : 3 ^ (7 * k - 1) % 27 = 0 := by rw [he, Nat.pow_add, Nat.mul_mod]; simp
  have hm : (ladderSource k h + 6) % 27 = 0 := by
    rw [← hl, Nat.mul_mod, hr]
    simp
  omega

theorem arbitrarily_strong_ladder_detours (g B : Nat) :
    ∃ R p, R % 2 = 1 ∧ B < blockValue R 0 ∧
      prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      0 < p ∧ 3 ^ g * p < blockValue R 0 ∧
      ∀ i, i < R → Backtrack (i + 68 * (g + 1) + 1) (2 * i + 119 * (g + 1)) (hitValue R i) p := by
  let k := 17 * (g + 1)
  let h := B + 1
  have hk : 0 < k := by unfold k; omega
  have hr := ladder_parameters k h hk
  have hs := ladder_arbitrary_gain g h
  have hg := ladder_growth k h hk
  change 0 < ladderPredecessor k h ∧
    3 ^ g * ladderPredecessor k h < ladderSource k h ∧ _ at hs
  refine ⟨ladderExponent k h, ladderPredecessor k h, hr.2.1, ?_,
    (block_prefix _ _ (Nat.le_refl _)).2, hs.1, ?_, ?_⟩
  · rw [← hr.2.2.1]
    exact Nat.lt_trans (show B < h by unfold h; omega) hg
  · rw [← hr.2.2.1]
    exact hs.2.1
  · intro i hi
    have hp := ladder_later_inverse k h i hk hi
    have h4 : 4 * k = 68 * (g + 1) := by unfold k; omega
    have h7 : 7 * k = 119 * (g + 1) := by unfold k; omega
    rw [h4, h7] at hp
    exact hp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finite_cycle_witness :
    0 < 9 * 2 ^ 187 - 17 ∧ 9 * 2 ^ 187 - 17 < 3 ^ 120 - 6 ∧
    iterate 306 (9 * 2 ^ 187 - 17) = iterate 1 (3 ^ 120 - 6) ∧
    ReachesOne (3 ^ 120 - 6) ∧ ReachesOne (9 * 2 ^ 187 - 17) := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨1413, by decide +kernel⟩, ⟨1718, by decide +kernel⟩⟩

end MinimumCycleDetour

#print axioms MinimumCycleDetour.cycle_block
#print axioms MinimumCycleDetour.cycle_inverse
#print axioms MinimumCycleDetour.cycle_clock
#print axioms MinimumCycleDetour.detour_lift
#print axioms MinimumCycleDetour.cycle_detour
#print axioms MinimumCycleDetour.detour_meeting
#print axioms MinimumCycleDetour.seventeen_gain
#print axioms MinimumCycleDetour.detour_smaller
#print axioms MinimumCycleDetour.least_cycle_exclusion
#print axioms MinimumCycleDetour.odd_power_factor
#print axioms MinimumCycleDetour.cube_lift
#print axioms MinimumCycleDetour.ternary_lift
#print axioms MinimumCycleDetour.ladder_divisibility
#print axioms MinimumCycleDetour.ladder_parameters
#print axioms MinimumCycleDetour.ladder_lift
#print axioms MinimumCycleDetour.ladder_smaller
#print axioms MinimumCycleDetour.ladder_meeting
#print axioms MinimumCycleDetour.ladder_later_inverse
#print axioms MinimumCycleDetour.ladder_later_clock
#print axioms MinimumCycleDetour.ladder_not_least
#print axioms MinimumCycleDetour.amplified_gain
#print axioms MinimumCycleDetour.amplified_detour
#print axioms MinimumCycleDetour.ladder_arbitrary_gain
#print axioms MinimumCycleDetour.ladder_growth
#print axioms MinimumCycleDetour.least_orbit_cycle_bound
#print axioms MinimumCycleDetour.ladder_old_detour_residue
#print axioms MinimumCycleDetour.arbitrarily_strong_ladder_detours
#print axioms MinimumCycleDetour.finite_cycle_witness
