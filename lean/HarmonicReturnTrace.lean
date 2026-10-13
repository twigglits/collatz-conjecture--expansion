/-
  Finite integer inputs for a uniform harmonic nonfusion trace bound.
  The square-root fusion tail and harmonic/real summations remain written.
  No external analytic theorem or compiled external library is imported.
-/
import IntegerReturnCesaro

namespace HarmonicReturnTrace
open CollatzAffine CoalescenceTail IntegerReturnCesaro

theorem shifted_step_growth (n : Nat) : 2 * (U n + 1) ≤ 3 * (n + 1) := by
  unfold U
  split <;> omega

/-- A hit at any clock up to H has the same shifted lower source bound. -/
theorem bounded_hit_growth (H t m n : Nat) (ht : t ≤ H)
    (hh : orbit t m = n) : 2 ^ H * (n + 1) ≤ 3 ^ H * (m + 1) := by
  induction H generalizing t m n with
  | zero =>
    have hz : t = 0 := by omega
    subst t
    have he : m = n := hh
    subst n
    simp [orbit]
  | succ H ih =>
    cases t with
    | zero =>
      have he : m = n := hh
      subst n
      exact Nat.mul_le_mul_right (m + 1) (Nat.pow_le_pow_left (by decide) (H + 1))
    | succ t =>
      have hi := ih t (U m) n (by omega) hh
      have h0 := Nat.mul_le_mul_left 2 hi
      have h1 := Nat.mul_le_mul_left (3 ^ H) (shifted_step_growth m)
      calc
        2 ^ (H + 1) * (n + 1) = 2 * (2 ^ H * (n + 1)) := by
          rw [Nat.pow_succ]; ac_rfl
        _ ≤ 2 * (3 ^ H * (U m + 1)) := h0
        _ = 3 ^ H * (2 * (U m + 1)) := by ac_rfl
        _ ≤ 3 ^ H * (3 * (m + 1)) := h1
        _ = 3 ^ (H + 1) * (m + 1) := by rw [Nat.pow_succ]; ac_rfl

/-- The ratio of any two sources reaching one target through H is bounded
independently of that target. -/
theorem hitting_source_span {H s t u v n : Nat} (hu : 0 < u)
    (hs : s ≤ H) (ht : t ≤ H) (huv : orbit s u = n) (hvv : orbit t v = n) :
    v ≤ 2 * 3 ^ H * u := by
  have hv := bounded_hit_source ht hvv
  have hg := bounded_hit_growth H s u n hs huv
  have hn := Nat.mul_le_mul_left (2 ^ H) (show n ≤ n + 1 by omega)
  have hm := Nat.mul_le_mul_left (3 ^ H) (show u + 1 ≤ 2 * u by omega)
  calc
    v ≤ 2 ^ H * n := hv
    _ ≤ 2 ^ H * (n + 1) := hn
    _ ≤ 3 ^ H * (u + 1) := hg
    _ ≤ 3 ^ H * (2 * u) := hm
    _ = 2 * 3 ^ H * u := by ac_rfl

/-- An interval with this source span meets at most 2H+2 binary bands. -/
theorem dyadic_band_span {H a b j k : Nat} (ha : a < 2 ^ (j + 1))
    (hb : 2 ^ k ≤ b) (hspan : b ≤ 2 * 3 ^ H * a) : k < j + 2 * H + 2 := by
  have h34 : 3 ^ H ≤ 4 ^ H := Nat.pow_le_pow_left (by decide) H
  have hpos : 0 < 2 * 4 ^ H := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have hm := Nat.mul_le_mul_right a (Nat.mul_le_mul_left 2 h34)
  have hl := Nat.mul_lt_mul_of_pos_left (k := 2 * 4 ^ H) ha hpos
  have hp : 2 * 4 ^ H * 2 ^ (j + 1) = 2 ^ (j + 2 * H + 2) := by
    have h4 : 4 ^ H = 2 ^ (2 * H) := by rw [Nat.pow_mul]
    rw [h4]
    change 2 ^ 1 * 2 ^ (2 * H) * 2 ^ (j + 1) = _
    rw [← Nat.pow_add, ← Nat.pow_add]
    congr 1
    omega
  rw [hp] at hl
  have hh : 2 ^ k < 2 ^ (j + 2 * H + 2) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hb (Nat.le_trans hspan hm)) hl
  by_cases hk : k < j + 2 * H + 2
  · exact hk
  · have he := Nat.pow_le_pow_right (n := 2) (by decide)
      (show j + 2 * H + 2 ≤ k by omega)
    omega

theorem nonfusion_antitone {L T n : Nat} (h : L ≤ T) :
    unmerged T n ≤ unmerged L n := by
  cases hl : balanced L n with
  | false => simp [unmerged, hl]; split <;> omega
  | true =>
    have ht := balanced_persists_le h hl
    simp [unmerged, hl, ht]

theorem mask_repeated_periods (L q : Nat) :
    total (2 ^ L * q) (unmerged L) = q * total (2 ^ L) (unmerged L) := by
  induction q with
  | zero => simp [total]
  | succ q ih =>
    rw [Nat.mul_succ, total_add, ih]
    have h := total_ext (2 ^ L)
      (fun r => unmerged L (2 ^ L * q + r)) (unmerged L)
      (fun r _ => nonfused_mask_lift L q r)
    rw [h, Nat.succ_mul]

/-- Exact population of an earlier mask on any later full binary band. -/
theorem earlier_mask_band (L j : Nat) (h : L ≤ j) :
    total (2 ^ j) (fun r => unmerged L (2 ^ j + r)) =
      2 ^ (j - L) * total (2 ^ L) (unmerged L) := by
  have hp : 2 ^ j = 2 ^ L * 2 ^ (j - L) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le h]
  have he := total_ext (2 ^ j)
    (fun r => unmerged L (2 ^ j + r)) (unmerged L) (by
      intro r _
      rw [hp]
      exact nonfused_mask_lift L (2 ^ (j - L)) r)
  rw [he, hp, mask_repeated_periods]

/-- At mask clock T and source band j, use the earlier of the two clocks. -/
theorem nested_mask_band (T j : Nat) :
    total (2 ^ j) (fun r => unmerged T (2 ^ j + r)) ≤
      2 ^ (j - min T j) * total (2 ^ (min T j)) (unmerged (min T j)) := by
  have hm : min T j ≤ T := Nat.min_le_left _ _
  have hj : min T j ≤ j := Nat.min_le_right _ _
  have he := earlier_mask_band (min T j) j hj
  rw [← he]
  exact total_le (2 ^ j) _ _ (fun r _ => nonfusion_antitone hm)

theorem zero_count_identity (t n : Nat) (h : wt t n = 0) :
    2 ^ t * orbit t n = n := by
  induction t generalizing n with
  | zero => simp [orbit]
  | succ t ih =>
    have he : n % 2 = 0 := by simp only [wt] at h; omega
    have hw : wt t (U n) = 0 := by simp only [wt, he] at h; omega
    have hi := ih (U n) hw
    have hu : 2 * U n = n := by simp only [U, he, Nat.zero_ne_one, if_false]; omega
    calc
      2 ^ (t + 1) * orbit (t + 1) n = 2 * (2 ^ t * orbit t (U n)) := by
        rw [Nat.pow_succ, orbit]; ac_rfl
      _ = 2 * U n := by rw [hi]
      _ = n := hu

theorem cycle_count_positive {R n : Nat} (hR : 0 < R) (hn : 0 < n)
    (hh : orbit R n = n) : 0 < wt R n := by
  by_cases hw : wt R n = 0
  · have hi := zero_count_identity R n hw
    rw [hh] at hi
    have hp : 2 ≤ 2 ^ R := by
      simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ R by omega)
    have hm := Nat.mul_le_mul_right n hp
    omega
  · omega

/-- One actual odd step supplies a definite affine correction. -/
theorem positive_count_coefficient (t n : Nat) (h : 0 < wt t n) :
    3 ^ wt t n * (3 * n + 1) ≤ 3 * 2 ^ t * orbit t n := by
  induction t generalizing n with
  | zero => simp [wt] at h
  | succ t ih =>
    by_cases ho : n % 2 = 1
    · have hu : 2 * U n = 3 * n + 1 := by
        simp only [U, ho, if_true]; omega
      have hi := Nat.mul_le_mul_left 6 (coefficient_lower_bound t (U n))
      simp only [wt, ho, Nat.pow_add, orbit, Nat.pow_succ]
      calc
        3 * 3 ^ wt t (U n) * (3 * n + 1) = 6 * (3 ^ wt t (U n) * U n) := by
          rw [← hu]
          change 3 * 3 ^ wt t (U n) * (2 * U n) = (3 * 2) * (3 ^ wt t (U n) * U n)
          ac_rfl
        _ ≤ 6 * (2 ^ t * orbit t (U n)) := hi
        _ = 3 * (2 ^ t * 2) * orbit t (U n) := by
          change (3 * 2) * (2 ^ t * orbit t (U n)) = _
          ac_rfl
    · have he : n % 2 = 0 := by omega
      have hu : 2 * U n = n := by
        simp only [U, he, Nat.zero_ne_one, if_false]; omega
      have hw : 0 < wt t (U n) := by simp only [wt, he, Nat.zero_add] at h; exact h
      have hi := Nat.mul_le_mul_left 2 (ih (U n) hw)
      have hs := Nat.mul_le_mul_left (3 ^ wt t (U n))
        (show 3 * n + 1 ≤ 2 * (3 * U n + 1) by omega)
      simp only [wt, he, Nat.zero_add, orbit, Nat.pow_succ]
      calc
        3 ^ wt t (U n) * (3 * n + 1) ≤ 3 ^ wt t (U n) * (2 * (3 * U n + 1)) := hs
        _ = 2 * (3 ^ wt t (U n) * (3 * U n + 1)) := by ac_rfl
        _ ≤ 2 * (3 * 2 ^ t * orbit t (U n)) := hi
        _ = 3 * (2 ^ t * 2) * orbit t (U n) := by ac_rfl

/-- For any positive cycle, rho <= 3n/(3n+1), hence its Green factor
is at most 3n+1. This does not assert existence of any unknown cycle. -/
theorem cycle_ratio_cap {R n : Nat} (hR : 0 < R) (hn : 0 < n)
    (hh : orbit R n = n) : (3 * n + 1) * 3 ^ wt R n ≤ 3 * n * 2 ^ R := by
  have hi := positive_count_coefficient R n (cycle_count_positive hR hn hh)
  rw [hh] at hi
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hi

#print axioms bounded_hit_growth
#print axioms hitting_source_span
#print axioms dyadic_band_span
#print axioms nonfusion_antitone
#print axioms mask_repeated_periods
#print axioms earlier_mask_band
#print axioms nested_mask_band
#print axioms cycle_count_positive
#print axioms positive_count_coefficient
#print axioms cycle_ratio_cap

end HarmonicReturnTrace
