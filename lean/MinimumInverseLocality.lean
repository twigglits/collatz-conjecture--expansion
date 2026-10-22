/- Finite inverse budgets are locally constant in a ternary residue class.
   An exact anchor at 857 gives arbitrarily large first-target obstructions. -/
import MinimumNegativeCycle

namespace MinimumInverseLocality
open OrdinaryCollatz MinimumReturnLadder

theorem backtrack_positive {e o b p : Nat} (h : Backtrack e o b p)
    (hb : 0 < b) : 0 < p := by
  induction h with
  | nil => exact hb
  | even h ih => omega
  | odd h hp ih => omega

theorem backtrack_size {e o b p : Nat} (h : Backtrack e o b p) :
    3 ^ o * (p + 1) ≤ 2 ^ (e + o) * (b + 1) := by
  induction h with
  | nil => simp
  | @even e o b x h ih =>
    have hh := Nat.mul_le_mul_left 2 ih
    have ht : e + 1 + o = (e + o) + 1 := by omega
    rw [ht, Nat.pow_succ]
    calc
      _ ≤ 3 ^ o * (2 * (x + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = 2 * (3 ^ o * (x + 1)) := by ac_rfl
      _ ≤ 2 * (2 ^ (e + o) * (b + 1)) := hh
      _ = _ := by ac_rfl
  | @odd e o b x p h hp ih =>
    have hh := Nat.mul_le_mul_left 2 ih
    have ht : e + (o + 1) = (e + o) + 1 := by omega
    rw [ht, Nat.pow_succ, Nat.pow_succ]
    have he : 3 ^ o * 3 * (p + 1) = 2 * (3 ^ o * (x + 1)) := by
      calc
        _ = 3 ^ o * (3 * p + 3) := by grind
        _ = 3 ^ o * (2 * (x + 1)) := by congr 1; omega
        _ = _ := by ac_rfl
    rw [he]
    calc
      _ ≤ 2 * (2 ^ (e + o) * (b + 1)) := hh
      _ = _ := by ac_rfl

theorem odd_count_bound {e o b p : Nat} (h : Backtrack e o b p)
    (hb : 0 < b) (d : Nat) (hd : b + 1 ≤ 2 ^ d) : o < 2 * (e + d) := by
  have hp := backtrack_positive h hb
  have hs := backtrack_size h
  have hu := Nat.mul_le_mul_left (2 ^ (e + o)) hd
  have hlow := Nat.mul_le_mul_left (3 ^ o) (show 2 ≤ p + 1 by omega)
  apply Classical.byContradiction
  intro hn
  have ho : o = 2 * (e + d) + (o - 2 * (e + d)) := by omega
  have ha := Nat.pow_le_pow_left (by decide : 8 ≤ 9) (e + d)
  have ht := Nat.pow_le_pow_left (by decide : 2 ≤ 3) (o - 2 * (e + d))
  have hm := Nat.mul_le_mul ha ht
  have hex : 2 ^ (e + o + d) ≤ 3 ^ o := by
    calc
      _ = 8 ^ (e + d) * 2 ^ (o - 2 * (e + d)) := by
        rw [show 8 = 2 ^ 3 by decide, ← Nat.pow_mul, ← Nat.pow_add]
        congr 1
        omega
      _ ≤ 9 ^ (e + d) * 3 ^ (o - 2 * (e + d)) := hm
      _ = 3 ^ o := by
        rw [show 9 = 3 ^ 2 by decide, ← Nat.pow_mul, ← Nat.pow_add, ← ho]
  rw [← Nat.pow_add] at hu
  have hpos := Nat.pow_pos (by decide : 0 < 3) (n := o)
  omega

theorem inverse_locality {e o B P : Nat} (h : Backtrack e o B P)
    (b d r K q : Nat) (hb : 0 < b) (hd : b + 1 ≤ 2 ^ d)
    (hK : 2 * (r + d) ≤ K) (he : e ≤ r) (hB : B = b + 3 ^ K * q) :
    ∃ p, Backtrack e o b p ∧ o < K ∧
      P = p + 2 ^ (e + o) * 3 ^ (K - o) * q := by
  induction h with
  | nil B =>
    have hdpos : 0 < d := by
      by_cases hz : d = 0
      · simp only [hz, Nat.pow_zero] at hd
        omega
      · omega
    exact ⟨b, Backtrack.nil b, by omega, by simpa using hB⟩
  | @even e o B x h ih =>
    obtain ⟨p, hp, ho, hx⟩ := ih (by omega) hB
    refine ⟨2 * p, Backtrack.even hp, ho, ?_⟩
    have ht : e + 1 + o = (e + o) + 1 := by omega
    rw [hx, ht, Nat.pow_succ]
    grind
  | @odd e o B x P h hP ih =>
    obtain ⟨p, hp, ho, hx⟩ := ih he hB
    have hk : K - o = (K - (o + 1)) + 1 := by omega
    let z := 2 ^ (e + o) * 3 ^ (K - (o + 1)) * q
    have hxz : x = p + 3 * z := by
      rw [hx, hk, Nat.pow_succ]
      dsimp [z]
      congr 1
      ac_rfl
    have hg : 3 * ((2 * p - 1) / 3) + 1 = 2 * p := by
      have hpos := backtrack_positive hp hb
      omega
    have hnext := Backtrack.odd hp hg
    have hcount := odd_count_bound hnext hb d hd
    refine ⟨(2 * p - 1) / 3, hnext, by omega, ?_⟩
    have ht : e + (o + 1) = (e + o) + 1 := by omega
    have hterm : 2 ^ (e + (o + 1)) * 3 ^ (K - (o + 1)) * q = 2 * z := by
      rw [ht, Nat.pow_succ]
      dsimp [z]
      ac_rfl
    rw [hterm]
    omega

theorem inverse_lift {e o b p : Nat} (h : Backtrack e o b p)
    (K q : Nat) (ho : o ≤ K) :
    Backtrack e o (b + 3 ^ K * q)
      (p + 2 ^ (e + o) * 3 ^ (K - o) * q) := by
  induction h with
  | nil b => simpa using Backtrack.nil (b + 3 ^ K * q)
  | @even e o b x h ih =>
    have hh := Backtrack.even (ih ho)
    have ht : e + 1 + o = (e + o) + 1 := by omega
    have he : 2 * (x + 2 ^ (e + o) * 3 ^ (K - o) * q) =
        2 * x + 2 ^ (e + 1 + o) * 3 ^ (K - o) * q := by
      rw [ht, Nat.pow_succ]
      grind
    rw [he] at hh
    exact hh
  | @odd e o b x p h hp ih =>
    apply Backtrack.odd (ih (by omega))
    have hk : K - o = (K - (o + 1)) + 1 := by omega
    have ht : e + (o + 1) = (e + o) + 1 := by omega
    rw [hk, ht, Nat.pow_succ, Nat.pow_succ]
    grind

def avoids857 : Nat → Nat → Bool
  | 0, n => n == 1 || n == 2 || n == 4
  | k + 1, n => (n != 857) && avoids857 k (C n)

theorem cycle_avoids (t n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) :
    iterate t n ≠ 857 := by
  induction t generalizing n with
  | zero => rcases hn with h | h | h <;> simp [iterate, h]
  | succ t ih =>
    apply ih
    rcases hn with h | h | h <;> simp [C, h]

theorem avoids_sound (k n : Nat) (h : avoids857 k n = true) :
    ∀ t, iterate t n ≠ 857 := by
  induction k generalizing n with
  | zero =>
    have hn : n = 1 ∨ n = 2 ∨ n = 4 := by simpa [avoids857, or_assoc] using h
    exact fun t => cycle_avoids t n hn
  | succ k ih =>
    have hh : n ≠ 857 ∧ avoids857 k (C n) = true := by simpa [avoids857] using h
    intro t
    cases t with
    | zero => exact hh.1
    | succ t => exact ih (C n) hh.2 t

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem finite_anchor :
    (∀ p : Fin 507, 0 < p.val → avoids857 200 p.val = true) ∧
    avoids857 200 (iterate 8 507) = true ∧
    (∀ t : Fin 8, iterate t.val 507 = 857 ↔ t.val = 7) := by
  decide +kernel

theorem anchor_only_hit (p t : Nat) (hp : 0 < p) (hple : p ≤ 507)
    (hit : iterate t p = 857) : p = 507 ∧ t = 7 := by
  have hp507 : p = 507 := by
    apply Classical.byContradiction
    intro hn
    have hf := avoids_sound 200 p (finite_anchor.1 ⟨p, by omega⟩ hp) t
    exact hf hit
  subst p
  have ht : t < 8 := by
    apply Classical.byContradiction
    intro hn
    have hf := avoids_sound 200 (iterate 8 507) finite_anchor.2.1 (t - 8)
    have he : t = 8 + (t - 8) := by omega
    rw [he, iterate_add] at hit
    exact hf hit
  exact ⟨rfl, (finite_anchor.2.2 ⟨t, ht⟩).mp hit⟩

theorem anchor_minimum {e o p : Nat} (h : Backtrack e o 857 p) : 507 ≤ p := by
  apply Classical.byContradiction
  intro hn
  have hp := backtrack_positive h (by decide)
  have hh := anchor_only_hit p (e + 2 * o) hp (by omega) (backtrack_actual h)
  omega

theorem anchor_slope {e o p : Nat} (h : Backtrack e o 857 p) :
    16 * 3 ^ o ≤ 27 * 2 ^ (e + o) := by
  apply Classical.byContradiction
  intro hn
  have hs := backtrack_size h
  have hstrict : 27 * 2 ^ (e + o) < 16 * 3 ^ o := by omega
  have ha := Nat.mul_le_mul_left 27 hs
  have hb := Nat.mul_lt_mul_of_pos_right hstrict (by decide : 0 < 858)
  have hbound : 3 ^ o * (27 * (p + 1)) < 3 ^ o * (16 * 858) := by
    calc
      _ = 27 * (3 ^ o * (p + 1)) := by ac_rfl
      _ ≤ 27 * (2 ^ (e + o) * 858) := ha
      _ = (27 * 2 ^ (e + o)) * 858 := by ac_rfl
      _ < (16 * 3 ^ o) * 858 := hb
      _ = _ := by ac_rfl
  have hnum := Nat.lt_of_mul_lt_mul_left hbound
  have hp : p ≤ 507 := by omega
  obtain ⟨_, ht⟩ := anchor_only_hit p (e + 2 * o)
    (backtrack_positive h (by decide)) hp (backtrack_actual h)
  have ho : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
  rcases ho with ho | ho | ho | ho
  · subst o
    have he : e = 7 := by omega
    subst e
    contradiction
  · subst o
    have he : e = 5 := by omega
    subst e
    contradiction
  · subst o
    have he : e = 3 := by omega
    subst e
    contradiction
  · subst o
    have he : e = 1 := by omega
    subst e
    contradiction

@[irreducible] def precision (r : Nat) : Nat := 2 * (r + 10)
def source (r q : Nat) : Nat := 507 + 16 * 3 ^ (precision r - 3) * q
def target (r q : Nat) : Nat := 857 + 3 ^ precision r * q

theorem precision_factor (r : Nat) : 3 ^ precision r = 27 * 3 ^ (precision r - 3) := by
  have he : precision r = 3 + (precision r - 3) := by unfold precision; omega
  calc
    _ = 3 ^ (3 + (precision r - 3)) := by rw [← he]
    _ = _ := by rw [Nat.pow_add]

theorem canonical_inverse (v : Nat) : Backtrack 1 3 (857 + 27 * v) (507 + 16 * v) := by
  have h1 := Backtrack.odd (Backtrack.nil (857 + 27 * v))
    (show 3 * (571 + 18 * v) + 1 = 2 * (857 + 27 * v) by omega)
  have h2 := Backtrack.even h1
  have h3 := Backtrack.odd h2
    (show 3 * (761 + 24 * v) + 1 = 2 * (2 * (571 + 18 * v)) by omega)
  exact Backtrack.odd h3
    (show 3 * (507 + 16 * v) + 1 = 2 * (761 + 24 * v) by omega)

theorem family_attainment (r q : Nat) : Backtrack 1 3 (target r q) (source r q) := by
  have hh := canonical_inverse (3 ^ (precision r - 3) * q)
  simpa only [target, source, precision_factor, Nat.mul_assoc] using hh

theorem family_lower {e o p : Nat} (r q : Nat)
    (h : Backtrack e o (target r q) p) (he : e ≤ r) : source r q ≤ p := by
  obtain ⟨a, ha, ho, hl⟩ := inverse_locality h 857 10 r (precision r) q
    (by decide) (by decide) (by unfold precision; omega) he rfl
  have hmin := anchor_minimum ha
  have hslope := anchor_slope ha
  have hmul := Nat.mul_le_mul_right (3 ^ (precision r - 3) * q) hslope
  have hterm : 3 ^ o * (16 * 3 ^ (precision r - 3) * q) ≤
      2 ^ (e + o) * 3 ^ precision r * q := by
    calc
      _ = (16 * 3 ^ o) * (3 ^ (precision r - 3) * q) := by ac_rfl
      _ ≤ (27 * 2 ^ (e + o)) * (3 ^ (precision r - 3) * q) := hmul
      _ = _ := by rw [precision_factor]; ac_rfl
  have hc : 3 ^ o * 3 ^ (precision r - o) = 3 ^ precision r := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hid : 3 ^ o * p = 3 ^ o * a + 2 ^ (e + o) * 3 ^ precision r * q := by
    rw [hl, Nat.mul_add]
    congr 1
    calc
      _ = 2 ^ (e + o) * (3 ^ o * 3 ^ (precision r - o)) * q := by ac_rfl
      _ = _ := by rw [hc]
  have hbase := Nat.mul_le_mul_left (3 ^ o) hmin
  have hh : 3 ^ o * source r q ≤ 3 ^ o * p := by
    rw [source, Nat.mul_add, hid]
    exact Nat.add_le_add hbase hterm
  exact Nat.le_of_mul_le_mul_left hh (Nat.pow_pos (by decide : 0 < 3))

theorem family_exact_minimum (r q : Nat) (hr : 1 ≤ r) :
    (∃ e o, e ≤ r ∧ Backtrack e o (target r q) (source r q)) ∧
    ∀ e o p, e ≤ r → Backtrack e o (target r q) p → source r q ≤ p := by
  exact ⟨⟨1, 3, hr, family_attainment r q⟩,
    fun _ _ _ he h => family_lower r q h he⟩

theorem seven_step_profile (v : Nat) :
    iterate 7 (507 + 16 * v) = 857 + 27 * v ∧
    (∀ t, t ≤ 7 → 507 + 16 * v ≤ iterate t (507 + 16 * v)) ∧
    (v % 27 = 0 → ∀ t, t ≤ 7 →
      ((iterate t (507 + 16 * v)) % 27 = 20 ↔ t = 7)) := by
  have h0 : C (507 + 16 * v) = 1522 + 48 * v := by unfold C; split <;> omega
  have h1 : C (1522 + 48 * v) = 761 + 24 * v := by unfold C; split <;> omega
  have h2 : C (761 + 24 * v) = 2284 + 72 * v := by unfold C; split <;> omega
  have h3 : C (2284 + 72 * v) = 1142 + 36 * v := by unfold C; split <;> omega
  have h4 : C (1142 + 36 * v) = 571 + 18 * v := by unfold C; split <;> omega
  have h5 : C (571 + 18 * v) = 1714 + 54 * v := by unfold C; split <;> omega
  have h6 : C (1714 + 54 * v) = 857 + 27 * v := by unfold C; split <;> omega
  refine ⟨by simp only [iterate, h0, h1, h2, h3, h4, h5, h6], ?_, ?_⟩
  · intro t ht
    have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
    rcases hc with ht | ht | ht | ht | ht | ht | ht | ht <;> subst t
    all_goals simp only [iterate, h0, h1, h2, h3, h4, h5, h6]
    all_goals omega
  · intro hv t ht
    have hc : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 := by omega
    rcases hc with ht | ht | ht | ht | ht | ht | ht | ht <;> subst t
    all_goals simp only [iterate, h0, h1, h2, h3, h4, h5, h6]
    all_goals constructor <;> intro hh <;> first | trivial | omega

theorem family_first_target (r q : Nat) :
    iterate 7 (source r q) = target r q ∧
    (∀ t, t ≤ 7 → source r q ≤ iterate t (source r q)) ∧
    (∀ t, t ≤ 7 → ((iterate t (source r q)) % 27 = 20 ↔ t = 7)) := by
  let v := 3 ^ (precision r - 3) * q
  have hv : v % 27 = 0 := by
    have he : precision r - 3 = 3 + (precision r - 6) := by unfold precision; omega
    dsimp [v]
    rw [he, Nat.pow_add]
    change (27 * 3 ^ (precision r - 6) * q) % 27 = 0
    rw [Nat.mul_assoc]
    omega
  have hh := seven_step_profile v
  have hsource : source r q = 507 + 16 * v := by dsimp [source, v]; ac_rfl
  have htarget : target r q = 857 + 27 * v := by
    dsimp [target, v]
    rw [precision_factor]
    ac_rfl
  rw [hsource, htarget]
  exact ⟨hh.1, hh.2.1, hh.2.2 hv⟩

theorem unbounded_first_target_obstruction (r bound : Nat) (hr : 1 ≤ r) :
    ∃ n b, bound < n ∧ iterate 7 n = b ∧
      (∀ t, t ≤ 7 → ((iterate t n) % 27 = 20 ↔ t = 7)) ∧
      Backtrack 1 3 b n ∧
      ∀ e o p, e ≤ r → Backtrack e o b p → n ≤ p := by
  let q := bound + 1
  have hp := Nat.pow_pos (by decide : 0 < 3) (n := precision r - 3)
  have hm := Nat.mul_le_mul_right q (show 1 ≤ 16 * 3 ^ (precision r - 3) by omega)
  have hlarge : bound < source r q := by dsimp [source, q] at *; omega
  exact ⟨source r q, target r q, hlarge, (family_first_target r q).1,
    (family_first_target r q).2.2, family_attainment r q,
    (family_exact_minimum r q hr).2⟩

theorem one_residue_powers (M x q h : Nat) (hx : x = 1 + M * q) :
    ∃ z, x ^ h = 1 + M * z := by
  induction h with
  | zero => exact ⟨0, by simp⟩
  | succ h ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨z + q + M * z * q, ?_⟩
    rw [Nat.pow_succ, hz, hx]
    grind

theorem eight_period (K h : Nat) :
    ∃ z, 8 ^ (2 * 3 ^ K * h) = 1 + 3 ^ K * z := by
  have hd := Nat.dvd_trans (Nat.pow_dvd_pow 3 (show K ≤ K + 2 by omega))
    (MinimumNegativeCycle.ternary_lift K)
  obtain ⟨q, hq⟩ := hd
  have hx := Nat.pow_pos (by decide : 0 < 8) (n := 3 ^ K)
  have he : 8 ^ (2 * 3 ^ K) = 1 + 3 ^ K * (q * (8 ^ (3 ^ K) - 1)) := by
    rw [Nat.mul_comm 2, Nat.pow_mul]
    have ha : 8 ^ (3 ^ K) = (8 ^ (3 ^ K) - 1) + 1 := by omega
    have hp : 3 ^ K * (q * (8 ^ (3 ^ K) - 1)) =
        (8 ^ (3 ^ K) + 1) * (8 ^ (3 ^ K) - 1) := by
      rw [← Nat.mul_assoc, ← hq]
    rw [hp]
    generalize 8 ^ (3 ^ K) - 1 = a at *
    rw [ha]
    simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
    grind
  have hh := one_residue_powers (3 ^ K) (8 ^ (2 * 3 ^ K))
    (q * (8 ^ (3 ^ K) - 1)) h he
  simpa only [← Nat.pow_mul] using hh

@[irreducible] def ladderExponent (r h : Nat) : Nat := 3 + 2 * 3 ^ precision r * h

theorem ladder_exponent (r h : Nat) :
    3 ≤ ladderExponent r h ∧ ladderExponent r h % 2 = 1 := by
  unfold ladderExponent
  rw [Nat.mul_assoc]
  constructor <;> omega

theorem ladder_in_family (r h : Nat) :
    ∃ q, blockValue (ladderExponent r h) 0 = source r q ∧
      hitValue (ladderExponent r h) 1 = target r q := by
  obtain ⟨z, hz⟩ := eight_period (precision r) h
  let t := 2 * 3 ^ precision r * h
  have hR : ladderExponent r h = 3 + t := by unfold ladderExponent; rfl
  have hN : 2 ^ (3 * ladderExponent r h) = 512 * (1 + 3 ^ precision r * z) := by
    rw [Nat.pow_mul]
    change 8 ^ ladderExponent r h = _
    rw [hR, Nat.pow_add]
    change 512 * 8 ^ t = _
    rw [hz]
  have hB : 2 ^ (3 * (ladderExponent r h - 1) - 1) =
      32 * (1 + 3 ^ precision r * z) := by
    have he : 3 * (ladderExponent r h - 1) - 1 = 5 + 3 * t := by omega
    rw [he, Nat.pow_add, Nat.pow_mul]
    change 32 * 8 ^ t = _
    rw [hz]
  refine ⟨864 * z, ?_, ?_⟩
  · simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero,
      Nat.mul_one, hN, source]
    rw [precision_factor]
    have he : 512 * (1 + 27 * 3 ^ (precision r - 3) * z) =
        512 + 16 * 3 ^ (precision r - 3) * (864 * z) := by grind
    rw [he]
    omega
  · simp only [hitValue, hB, target]
    have he : 32 * (1 + 3 ^ precision r * z) * 3 ^ (2 * 1 + 1) =
        864 + 3 ^ precision r * (864 * z) := by
      change 32 * (1 + 3 ^ precision r * z) * 27 = _
      grind
    rw [he]
    omega

theorem ladder_first_target_minimum (r h : Nat) (hr : 1 ≤ r) :
    let R := ladderExponent r h
    (∃ e o, e ≤ r ∧ Backtrack e o (hitValue R 1) (blockValue R 0)) ∧
    (∀ e o p, e ≤ r → Backtrack e o (hitValue R 1) p → blockValue R 0 ≤ p) ∧
    iterate 7 (blockValue R 0) = hitValue R 1 ∧
    (∀ t, t ≤ 7 → ((iterate t (blockValue R 0)) % 27 = 20 ↔ t = 7)) := by
  obtain ⟨q, hN, hB⟩ := ladder_in_family r h
  dsimp only
  rw [hN, hB]
  exact ⟨(family_exact_minimum r q hr).1, (family_exact_minimum r q hr).2,
    (family_first_target r q).1, (family_first_target r q).2.2⟩

theorem ladder_growth (r h : Nat) : h < blockValue (ladderExponent r h) 0 := by
  let t := 2 * 3 ^ precision r * h
  have hp := Nat.pow_pos (by decide : 0 < 3) (n := precision r)
  have ht : h ≤ t := by
    have hh := Nat.mul_le_mul_right h (show 1 ≤ 2 * 3 ^ precision r by omega)
    simpa only [Nat.one_mul] using hh
  have hx : t < 8 ^ t := Nat.lt_pow_self (by decide)
  have he : blockValue (ladderExponent r h) 0 = 512 * 8 ^ t - 5 := by
    simp only [blockValue, blockProduct, Nat.sub_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
    rw [Nat.pow_mul]
    change 8 ^ ladderExponent r h - 5 = _
    rw [show ladderExponent r h = 3 + t by unfold ladderExponent; rfl, Nat.pow_add]
  rw [he]
  omega

theorem unbounded_ladder_obstruction (s bound : Nat) :
    ∃ R, 3 ≤ R ∧ R % 2 = 1 ∧ bound < blockValue R 0 ∧
      Backtrack 1 3 (hitValue R 1) (blockValue R 0) ∧
      ∀ e o p, e ≤ 1 + s → Backtrack e o (hitValue R 1) p → blockValue R 0 ≤ p := by
  let R := ladderExponent (1 + s) (bound + 1)
  have hR := ladder_exponent (1 + s) (bound + 1)
  have hg := ladder_growth (1 + s) (bound + 1)
  obtain ⟨q, hN, hB⟩ := ladder_in_family (1 + s) (bound + 1)
  refine ⟨R, hR.1, hR.2, by dsimp [R]; omega, ?_, ?_⟩
  · dsimp [R]
    rw [hN, hB]
    exact family_attainment (1 + s) q
  · dsimp [R]
    rw [hN, hB]
    exact (family_exact_minimum (1 + s) q (by omega)).2

#print axioms backtrack_positive
#print axioms backtrack_size
#print axioms odd_count_bound
#print axioms inverse_locality
#print axioms inverse_lift
#print axioms cycle_avoids
#print axioms avoids_sound
#print axioms finite_anchor
#print axioms anchor_only_hit
#print axioms anchor_minimum
#print axioms anchor_slope
#print axioms precision_factor
#print axioms canonical_inverse
#print axioms family_attainment
#print axioms family_lower
#print axioms family_exact_minimum
#print axioms seven_step_profile
#print axioms family_first_target
#print axioms unbounded_first_target_obstruction
#print axioms one_residue_powers
#print axioms eight_period
#print axioms ladder_exponent
#print axioms ladder_in_family
#print axioms ladder_first_target_minimum
#print axioms ladder_growth
#print axioms unbounded_ladder_obstruction

end MinimumInverseLocality
