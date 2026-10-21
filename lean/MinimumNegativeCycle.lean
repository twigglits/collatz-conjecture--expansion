/- Positive inverse paths lifted from the magnitude-17 negative cycle.
   These are coalescing-source exclusions, not universal convergence. -/
import MinimumInverseEscape

namespace MinimumNegativeCycle
open OrdinaryCollatz MinimumTailRigidity MinimumRootPredecessors
open MinimumReturnLadder MinimumInverseEscape

-- Avoid expanding hundreds of symbolic Collatz steps while matching clocks.
attribute [local irreducible] OrdinaryCollatz.iterate

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
  exact Backtrack.odd h10
    (show 3 * (2048 * q - 17) + 1 = 2 * (3072 * q - 25) by omega)

theorem cycle_repeated (k q : Nat) (hq : 0 < q) :
    Backtrack (4 * k) (7 * k) (2187 ^ k * q - 17) (2048 ^ k * q - 17) := by
  induction k generalizing q with
  | zero => simpa using Backtrack.nil (q - 17)
  | succ k ih =>
    have h1 := ih (2187 * q) (by omega)
    have h2 := cycle_block (2048 ^ k * q)
      (Nat.mul_pos (Nat.pow_pos (by decide : 0 < 2048)) hq)
    have hm : 2048 ^ k * (2187 * q) = 2187 * (2048 ^ k * q) := by ac_rfl
    rw [hm] at h1
    have hh := backtrack_append h1 h2
    simpa only [Nat.pow_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

theorem cycle_clock (k q : Nat) (hq : 0 < q) :
    iterate (18 * k) (2048 ^ k * q - 17) = 2187 ^ k * q - 17 := by
  have hh := backtrack_actual (cycle_repeated k q hq)
  have hc : 4 * k + 2 * (7 * k) = 18 * k := by omega
  rwa [hc] at hh

theorem meeting_inverse (n k q : Nat) (hn : n % 2 = 1) (hq : 0 < q)
    (hl : 2187 ^ k * q = 3 * n + 18) :
    Backtrack (4 * k + 1) (7 * k) (iterate 2 n) (2048 ^ k * q - 17) := by
  have hm := odd_meeting n hn
  have he : 2 * iterate 2 n = 2187 ^ k * q - 17 := by omega
  have hh := Backtrack.even (Backtrack.nil (iterate 2 n))
  rw [he] at hh
  have hp := backtrack_append hh (cycle_repeated k q hq)
  simpa only [Nat.zero_add, Nat.add_comm] using hp

theorem meeting_clock (n k q : Nat) (hn : n % 2 = 1) (hq : 0 < q)
    (hl : 2187 ^ k * q = 3 * n + 18) :
    iterate (18 * k + 1) (2048 ^ k * q - 17) = iterate 2 n := by
  have hh := backtrack_actual (meeting_inverse n k q hn hq hl)
  have hc : 4 * k + 1 + 2 * (7 * k) = 18 * k + 1 := by omega
  rwa [hc] at hh

theorem seventeen_gain : 3 * 2048 ^ 17 < 2187 ^ 17 := by decide +kernel

theorem power_gain (k : Nat) (hk : 17 ≤ k) : 3 * 2048 ^ k < 2187 ^ k := by
  have he : k = 17 + (k - 17) := by omega
  have hp := Nat.pow_le_pow_left (by decide : 2048 ≤ 2187) (k - 17)
  have hpos := Nat.pow_pos (by decide : 0 < 2048) (n := k - 17)
  have hs := seventeen_gain
  rw [he, Nat.pow_add, Nat.pow_add]
  have h1 := Nat.mul_lt_mul_of_pos_right hs hpos
  have h2 := Nat.mul_le_mul_left (2187 ^ 17) hp
  omega

theorem meeting_smaller (n k q : Nat) (hk : 17 ≤ k) (hq : 0 < q)
    (hl : 2187 ^ k * q = 3 * n + 18) :
    0 < 2048 ^ k * q - 17 ∧ 2048 ^ k * q - 17 < n := by
  have hg := Nat.mul_lt_mul_of_pos_right (power_gain k hk) hq
  have hm : 3 * 2048 ^ k * q = 3 * (2048 ^ k * q) := by ac_rfl
  rw [hm, hl] at hg
  have hp : 2048 ≤ 2048 ^ k :=
    Nat.pow_le_pow_right (by decide : 0 < 2048) (show 1 ≤ k by omega)
  have hq' := Nat.mul_le_mul_left (2048 ^ k) hq
  omega

theorem least_no_lift {n : Nat} (hn : LeastCounterexample n)
    (k q : Nat) (hk : 17 ≤ k) (hq : 0 < q) : 2187 ^ k * q ≠ 3 * n + 18 := by
  intro hl
  have ho : n % 2 = 1 := by have hh := least_mod4 hn; omega
  have hs := meeting_smaller n k q hk hq hl
  have hp := least_coalescing_predecessor hn hs.1 (meeting_clock n k q ho hq hl)
  exact Nat.not_lt_of_ge hp hs.2

theorem least_residue_exclusion {n : Nat} (hn : LeastCounterexample n) :
    (n + 6) % 3 ^ 118 ≠ 0 := by
  intro hz
  obtain ⟨q, hd⟩ := Nat.dvd_of_mod_eq_zero hz
  have hl : 2187 ^ 17 * q = 3 * n + 18 := by
    have hc : 2187 ^ 17 = 3 * 3 ^ 118 := by decide +kernel
    rw [hc, Nat.mul_assoc, ← hd]
    omega
  have hq : 0 < q := Nat.pos_of_mul_pos_left (hd ▸ (show 0 < n + 6 by omega))
  exact least_no_lift hn 17 q (by decide) hq hl

theorem finite_gain_threshold :
    (∀ k : Fin 17, 0 < k.val → 2187 ^ k.val + 33 < 3 * 2048 ^ k.val) ∧
    3 * 2048 ^ 17 < 2187 ^ 17 := by decide +kernel

theorem earlier_cycles_larger (n k q : Nat) (hk : k < 17)
    (hq : 0 < q) (hl : 2187 ^ k * q = 3 * n + 18) :
    n < 2048 ^ k * q - 17 := by
  by_cases hz : k = 0
  · simp only [hz, Nat.pow_zero, Nat.one_mul] at *
    omega
  · have hg := finite_gain_threshold.1 ⟨k, hk⟩ (show 0 < k from Nat.pos_of_ne_zero hz)
    have hm := Nat.mul_lt_mul_of_pos_right hg hq
    have ha : (2187 ^ k + 33) * q = 2187 ^ k * q + 33 * q := by rw [Nat.add_mul]
    have hb : 3 * 2048 ^ k * q = 3 * (2048 ^ k * q) := by ac_rfl
    rw [ha, hb, hl] at hm
    omega

theorem repeated_gain (h : Nat) :
    3 ^ h * 2048 ^ (17 * h) ≤ 2187 ^ (17 * h) := by
  have hp := Nat.pow_le_pow_left (Nat.le_of_lt seventeen_gain) h
  simpa only [Nat.mul_pow, ← Nat.pow_mul] using hp

theorem meeting_improvement (n h q : Nat)
    (hl : 2187 ^ (17 * (h + 1)) * q = 3 * n + 18) :
    3 ^ h * (2048 ^ (17 * (h + 1)) * q) ≤ n + 6 := by
  have hp := Nat.mul_le_mul_right q (repeated_gain (h + 1))
  rw [hl, Nat.pow_succ] at hp
  have he (a b c : Nat) : a * 3 * b * c = 3 * (a * (b * c)) := by ac_rfl
  rw [he] at hp
  omega

theorem meeting_factor_smaller (n h q : Nat) (hq : 0 < q)
    (hl : 2187 ^ (17 * (h + 1)) * q = 3 * n + 18) :
    3 ^ h * (2048 ^ (17 * (h + 1)) * q - 17) < n := by
  have hs := meeting_smaller n (17 * (h + 1)) q (by omega) hq hl
  have hp := meeting_improvement n h q hl
  have he : 2048 ^ (17 * (h + 1)) * q =
      (2048 ^ (17 * (h + 1)) * q - 17) + 17 := by omega
  rw [he, Nat.mul_add] at hp
  have h3 := Nat.pow_pos (by decide : 0 < 3) (n := h)
  omega

theorem cube_divisibility (d x : Nat) (hd : 3 ∣ d) (hx : d ∣ x + 1) :
    d * 3 ∣ x ^ 3 + 1 := by
  have h3 := Nat.dvd_trans hd hx
  have hprod := Nat.mul_dvd_mul hx h3
  have hcube := Nat.dvd_mul_right_of_dvd hprod (x + 1)
  have hterm : d * 3 ∣ 3 * x * (x + 1) := by
    obtain ⟨q, hq⟩ := hx
    refine ⟨x * q, ?_⟩
    rw [hq]
    ac_rfl
  have he : x ^ 3 + 1 + 3 * x * (x + 1) = (x + 1) * (x + 1) * (x + 1) := by
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    grind
  exact (Nat.dvd_add_iff_left hterm).mpr (he ▸ hcube)

theorem ternary_lift (s : Nat) : 3 ^ (s + 2) ∣ 8 ^ (3 ^ s) + 1 := by
  induction s with
  | zero => exact ⟨1, by decide⟩
  | succ s ih =>
    have hd : 3 ∣ 3 ^ (s + 2) := by
      rw [show s + 2 = (s + 1) + 1 by omega, Nat.pow_succ]
      exact Nat.dvd_mul_left 3 _
    have hh := cube_divisibility (3 ^ (s + 2)) (8 ^ (3 ^ s)) hd ih
    change 3 ^ ((s + 2) + 1) ∣ 8 ^ (3 ^ (s + 1)) + 1
    rw [Nat.pow_succ 3 (s + 2), Nat.pow_succ 3 s, Nat.pow_mul]
    exact hh

theorem odd_power_divisibility (d x h : Nat) (hx : 0 < x) (hd : d ∣ x + 1) :
    d ∣ x ^ (2 * h + 1) + 1 := by
  induction h with
  | zero => simpa using hd
  | succ h ih =>
    have hterm := Nat.dvd_mul_left_of_dvd hd (x - 1)
    have hmain := Nat.dvd_mul_left_of_dvd ih (x * x)
    have hp : 2 * (h + 1) + 1 = (2 * h + 1) + 2 := by omega
    have he : x ^ (2 * (h + 1) + 1) + 1 + (x - 1) * (x + 1) =
        x * x * (x ^ (2 * h + 1) + 1) := by
      rw [hp, Nat.pow_add]
      have htwo : x ^ 2 = x * x := by simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      rw [htwo]
      have halg (a b c : Nat) (ha : a = c + 1) :
          b * (a * a) + 1 + c * (a + 1) = a * a * (b + 1) := by
        rw [ha]
        grind
      exact halg x (x ^ (2 * h + 1)) (x - 1) (by omega)
    exact (Nat.dvd_add_iff_left hterm).mpr (he ▸ hmain)

-- Keep the enormous exponent symbolic during elaboration; unfold only for
-- its arithmetic properties, never to evaluate the corresponding source.
@[irreducible] def ladderExponent (h : Nat) : Nat := 3 ^ 116 * (2 * h + 1)

theorem ladder_exponent (h : Nat) : ladderExponent h % 2 = 1 ∧ 3 ≤ ladderExponent h := by
  have hc : 3 ^ 116 % 2 = 1 := by decide +kernel
  have hb : 3 ≤ 3 ^ 116 := by decide +kernel
  have hm := Nat.mul_le_mul_left (3 ^ 116) (show 1 ≤ 2 * h + 1 by omega)
  constructor
  · unfold ladderExponent
    rw [Nat.mul_mod, hc]
    omega
  · unfold ladderExponent
    omega

theorem ladder_divisibility (h : Nat) :
    3 ^ 118 ∣ 8 ^ ladderExponent h + 1 := by
  have hp := odd_power_divisibility (3 ^ 118) (8 ^ (3 ^ 116)) h
    (Nat.pow_pos (by decide : 0 < 8)) (ternary_lift 116)
  simpa only [← Nat.pow_mul, ladderExponent] using hp

theorem ladder_source_lift (h : Nat) :
    blockValue (ladderExponent h) 0 + 6 = 8 ^ ladderExponent h + 1 := by
  have hb : 8 ≤ 8 ^ ladderExponent h :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ ladderExponent h from
      Nat.le_trans (by decide) (ladder_exponent h).2)
  have he : 2 ^ (3 * ladderExponent h) = 8 ^ ladderExponent h := by rw [Nat.pow_mul]
  simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero,
    Nat.pow_zero, Nat.mul_one, he]
  omega

theorem residue_detour (n : Nat) (hn : n % 2 = 1) (hdv : 3 ^ 118 ∣ n + 6) :
    ∃ p, 0 < p ∧ p < n ∧ Backtrack 69 119 (iterate 2 n) p ∧
      iterate 307 p = iterate 2 n := by
  obtain ⟨q, hd⟩ := hdv
  have hpos : 0 < n + 6 := Nat.zero_lt_succ (n + 5)
  have hq : 0 < q := Nat.pos_of_mul_pos_left (hd ▸ hpos)
  have hl : 2187 ^ 17 * q = 3 * n + 18 := by
    have hc : 2187 ^ 17 = 3 * 3 ^ 118 := by decide +kernel
    rw [hc, Nat.mul_assoc, ← hd]
    exact Nat.mul_add 3 n 6
  have hs := meeting_smaller n 17 q (by decide) hq hl
  have hc := meeting_clock n 17 q hn hq hl
  rw [show 18 * 17 + 1 = 307 by decide] at hc
  exact ⟨2048 ^ 17 * q - 17, hs.1, hs.2,
    meeting_inverse n 17 q hn hq hl, hc⟩

private theorem return_clock_identity (i : Nat) :
    i + 69 + 2 * (2 * i + 119) = 5 * i + 307 := by omega

theorem ladder_escape (h : Nat) :
    ∃ p, 0 < p ∧ p < blockValue (ladderExponent h) 0 ∧
      iterate 307 p = iterate 2 (blockValue (ladderExponent h) 0) ∧
      ∀ i, i < ladderExponent h →
        Backtrack (i + 69) (2 * i + 119) (hitValue (ladderExponent h) i) p ∧
        iterate (5 * i + 307) p = hitValue (ladderExponent h) i := by
  have hi0 : 0 < ladderExponent h :=
    Nat.lt_of_lt_of_le (show 0 < 3 by decide) (ladder_exponent h).2
  obtain ⟨u, hu, _, _⟩ := block_coordinates (ladderExponent h) 0 hi0
  have hn : blockValue (ladderExponent h) 0 % 2 = 1 := by
    rw [hu, Nat.add_mod, Nat.mul_mod]
    simp
  have hd : 3 ^ 118 ∣ blockValue (ladderExponent h) 0 + 6 := by
    rw [ladder_source_lift]
    exact ladder_divisibility h
  obtain ⟨p, hp, hs, hb, hc⟩ := residue_detour (blockValue (ladderExponent h) 0) hn hd
  refine ⟨p, hp, hs, hc, ?_⟩
  intro i hi
  rw [hit_clock (ladderExponent h) 0 hi0] at hb
  have ht := backtrack_append (hit_to_initial (ladderExponent h) i hi) hb
  have htclock := backtrack_actual ht
  rw [return_clock_identity] at htclock
  exact ⟨ht, htclock⟩

theorem ladder_not_least (h : Nat) : ¬ LeastCounterexample (blockValue (ladderExponent h) 0) := by
  intro hn
  obtain ⟨p, hp, hs, hm, _⟩ := ladder_escape h
  have hl := least_coalescing_predecessor hn hp hm
  exact Nat.not_lt_of_ge hl hs

theorem ladder_growth (h : Nat) : h < blockValue (ladderExponent h) 0 := by
  have hr := ladder_exponent h
  have hs := source_growth (ladderExponent h) hr.2
  have hb : 1 ≤ 3 ^ 116 := by decide +kernel
  have hm := Nat.mul_le_mul_right (2 * h + 1) hb
  have hh : h < 2 * h + 1 := Nat.lt_succ_of_le
    (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right h (show 1 ≤ 2 by decide))
  have he : 2 * h + 1 ≤ ladderExponent h := by
    simpa only [Nat.one_mul, ladderExponent] using hm
  exact Nat.lt_trans (Nat.lt_of_lt_of_le hh he) hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem finite_positive_witness :
    2 ^ 187 - 17 < 3 ^ 118 - 6 ∧
    iterate 307 (2 ^ 187 - 17) = iterate 2 (3 ^ 118 - 6) ∧
    ReachesOne (3 ^ 118 - 6) ∧ ReachesOne (2 ^ 187 - 17) := by
  exact ⟨by decide +kernel, by decide +kernel,
    ⟨1247, by decide +kernel⟩, ⟨1552, by decide +kernel⟩⟩

end MinimumNegativeCycle

#print axioms MinimumNegativeCycle.cycle_block
#print axioms MinimumNegativeCycle.cycle_repeated
#print axioms MinimumNegativeCycle.cycle_clock
#print axioms MinimumNegativeCycle.meeting_inverse
#print axioms MinimumNegativeCycle.meeting_clock
#print axioms MinimumNegativeCycle.seventeen_gain
#print axioms MinimumNegativeCycle.power_gain
#print axioms MinimumNegativeCycle.meeting_smaller
#print axioms MinimumNegativeCycle.least_no_lift
#print axioms MinimumNegativeCycle.least_residue_exclusion
#print axioms MinimumNegativeCycle.finite_gain_threshold
#print axioms MinimumNegativeCycle.earlier_cycles_larger
#print axioms MinimumNegativeCycle.repeated_gain
#print axioms MinimumNegativeCycle.meeting_improvement
#print axioms MinimumNegativeCycle.meeting_factor_smaller
#print axioms MinimumNegativeCycle.cube_divisibility
#print axioms MinimumNegativeCycle.ternary_lift
#print axioms MinimumNegativeCycle.odd_power_divisibility
#print axioms MinimumNegativeCycle.ladder_exponent
#print axioms MinimumNegativeCycle.ladder_divisibility
#print axioms MinimumNegativeCycle.ladder_source_lift
#print axioms MinimumNegativeCycle.residue_detour
#print axioms MinimumNegativeCycle.ladder_escape
#print axioms MinimumNegativeCycle.ladder_not_least
#print axioms MinimumNegativeCycle.ladder_growth
#print axioms MinimumNegativeCycle.finite_positive_witness
