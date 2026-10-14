/-
  Affine clones for the written prearrival-deficit transfer.
  The boundedness equivalence, real limits and lifetime deficits remain written.
  No universal convergence or unknown-orbit arrival is assumed or concluded.
-/
import SignedArrivalWindows
import ReversalPersistence

namespace PrearrivalDeficitTransfer
open CollatzAffine CoalescenceTail EscapeWeightRefinements IntegerReturnCesaro
  GradientClockObstruction SignedArrivalWindows ReversalPersistence

theorem lifted_one_multiple (a v : Nat) :
    orbit (2 * a) (2 ^ (2 * a) * v + 1) = 3 ^ a * v + 1 ∧
    wt (2 * a) (2 ^ (2 * a) * v + 1) = a := by
  have he := affine (2 * a) v 1
  have hw := weight_lift (2 * a) v 1
  simpa [(cycle_one a).1, (cycle_one a).2] using And.intro he hw

theorem clone_common_clock {a u v : Nat}
    (h : 9 * u + 1 = 4 * (2 ^ (2 * a) * v)) :
    orbit (2 * a + 5) (8 * u) = 3 ^ a * v + 1 ∧
    wt (2 * a + 5) (8 * u) = a + 2 ∧
    orbit (2 * a + 5) (24 * u + 2) = v ∧
    wt (2 * a + 5) (24 * u + 2) = 1 := by
  have hp := family_first_five h
  have hq := family_target_two h
  have hb : 8 * (2 ^ (2 * a) * v) = 2 ^ (2 * a + 3) * v := by
    simp only [Nat.pow_add]
    change 8 * (2 ^ (2 * a) * v) = (2 ^ (2 * a) * 8) * v
    ac_rfl
  constructor
  · rw [show 2 * a + 5 = 5 + 2 * a by omega, orbit_add, hp.1,
      (lifted_one_multiple a v).1]
  constructor
  · rw [show 2 * a + 5 = 5 + 2 * a by omega, weight_add, hp.1, hp.2,
      (lifted_one_multiple a v).2]
    omega
  constructor
  · rw [show 2 * a + 5 = 2 + (2 * a + 3) by omega, orbit_add, hq.1,
      hb, (halving_data (2 * a + 3) v).1]
  · rw [show 2 * a + 5 = 2 + (2 * a + 3) by omega, weight_add,
      hq.1, hq.2, hb, (halving_data (2 * a + 3) v).2]

def cloneSeed (j v : Nat) : Nat := (64 ^ (j + 1) * v - 1) / 9

theorem clone_seed_equation (j v : Nat) (hv : v % 9 = 1) :
    9 * cloneSeed j v + 1 = 4 * (2 ^ (2 * (3 * j + 2)) * v) := by
  have hp : 0 < v := by omega
  have hm : (64 ^ (j + 1) * v) % 9 = 1 := by
    simp [Nat.mul_mod, Nat.pow_mod, hv]
  have hd := Nat.mod_add_div (64 ^ (j + 1) * v) 9
  have hpos : 0 < 64 ^ (j + 1) * v := Nat.mul_pos (Nat.pow_pos (by decide)) hp
  have he : (64 ^ (j + 1) * v - 1) / 9 = (64 ^ (j + 1) * v) / 9 := by omega
  have hb : 64 ^ (j + 1) = 4 * 2 ^ (2 * (3 * j + 2)) := by
    rw [show 64 = 2 ^ 6 from rfl, ← Nat.pow_mul]
    rw [show 6 * (j + 1) = 2 + 2 * (3 * j + 2) by omega, Nat.pow_add]
  unfold cloneSeed
  calc
    9 * ((64 ^ (j + 1) * v - 1) / 9) + 1 = 64 ^ (j + 1) * v := by omega
    _ = 4 * (2 ^ (2 * (3 * j + 2)) * v) := by rw [hb, Nat.mul_assoc]

theorem clone_shell {k u : Nat}
    (hl : 9 * 2 ^ k ≤ 8 * (9 * u + 1))
    (hu : 8 * (9 * u + 1) < 9 * 2 ^ (k + 1)) :
    2 ^ k ≤ 8 * u ∧ 8 * u < 2 ^ (k + 1) := by omega

theorem clone_current_reversal {a u v h : Nat}
    (hc : 9 * u + 1 = 4 * (2 ^ (2 * a) * v)) (hh : h < a) :
    1 + wt (2 * a + 5 + h) (24 * u + 2) <
      wt (2 * a + 5 + h) (8 * u) := by
  have he := clone_common_clock hc
  rw [weight_add (2 * a + 5) h (24 * u + 2),
    weight_add (2 * a + 5) h (8 * u), he.2.1, he.1, he.2.2.2, he.2.2.1]
  have hw := weight_le_length h v
  omega

theorem large_endpoint_no_arrival {H X h : Nat}
    (hX : 2 ^ H < X) (hh : h ≤ H) : orbit h X ≠ 1 := by
  intro he
  have hs := source_bound h X
  rw [he, Nat.mul_one] at hs
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
  omega

theorem unit_doubling_to_one {v : Nat} (hv : v % 3 ≠ 0) :
    ∃ e ≤ 5, (2 ^ e * v) % 9 = 1 := by
  have hr : v % 9 = 1 ∨ v % 9 = 2 ∨ v % 9 = 4 ∨
      v % 9 = 5 ∨ v % 9 = 7 ∨ v % 9 = 8 := by omega
  rcases hr with h | h | h | h | h | h
  · refine ⟨0, by decide, ?_⟩; simpa using h
  · refine ⟨5, by decide, ?_⟩; rw [Nat.mul_mod, h]
  · refine ⟨4, by decide, ?_⟩; rw [Nat.mul_mod, h]
  · refine ⟨1, by decide, ?_⟩; rw [Nat.mul_mod, h]
  · refine ⟨2, by decide, ?_⟩; rw [Nat.mul_mod, h]
  · refine ⟨3, by decide, ?_⟩; rw [Nat.mul_mod, h]

theorem first_arrival_ten : FirstArrival 10 5 := by
  constructor
  · decide
  · intro t ht
    have hs : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl <;> decide

theorem ten_window {h : Nat} (hl : 2 ≤ h) (hu : h ≤ 4) :
    2 ^ h * orbit h 10 = 32 ∧ wt h 10 = 1 := by
  have hs : h = 2 ∨ h = 3 ∨ h = 4 := by omega
  rcases hs with rfl | rfl | rfl <;> decide

theorem clone_retained_seven_eighths {h R : Nat} (hR : 21 ≤ R) (hh : h ≤ 4) :
    7 * (2 ^ h * orbit h (10 * R + 1)) ≤
      72 * R * 3 ^ wt h (10 * R + 1) := by
  have hp : 2 ^ h ≤ 16 := Nat.pow_le_pow_right (by decide) hh
  have hr := reciprocal_retention h (10 * R + 1)
  have hs := Nat.mul_le_mul_left (3 ^ wt h (10 * R + 1)) hp
  have hm := Nat.mul_le_mul_left (3 ^ wt h (10 * R + 1)) hR
  simp only [Nat.mul_add, Nat.mul_one] at hr
  have he : 3 ^ wt h (10 * R + 1) * (3 * (10 * R)) =
      30 * (R * 3 ^ wt h (10 * R + 1)) := by grind
  have hm' : 21 * 3 ^ wt h (10 * R + 1) ≤ R * 3 ^ wt h (10 * R + 1) := by
    simpa only [Nat.mul_comm] using hm
  have hs' : 3 ^ wt h (10 * R + 1) * 2 ^ h ≤ 16 * 3 ^ wt h (10 * R + 1) := by
    simpa only [Nat.mul_comm] using hs
  rw [he] at hr
  rw [Nat.mul_assoc]
  omega

theorem halving_clock_bound (h : Nat) : h + 1 ≤ 2 ^ h := by
  induction h with
  | zero => decide
  | succ h ih =>
    rw [Nat.pow_succ]
    have hp : 1 ≤ 2 ^ h := Nat.one_le_pow h 2 (by decide)
    omega

theorem odd_output_unit {n : Nat} (hn : n % 2 = 1) : U n % 3 = 2 := by
  unfold U
  rw [if_pos hn]
  omega

/-- Reaching the unit classes needs only removal of the initial even run
    and, if necessary, one odd step. This is not convergence to one. -/
theorem positive_hits_unit (n : Nat) : 0 < n → ∃ t, orbit t n % 3 ≠ 0 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    by_cases hu : n % 3 ≠ 0
    · exact ⟨0, hu⟩
    · by_cases ho : n % 2 = 1
      · refine ⟨1, ?_⟩
        change U n % 3 ≠ 0
        rw [odd_output_unit ho]
        decide
      · have he : n % 2 = 0 := by omega
        have hs : U n = n / 2 := by simp [U, ho]
        have hp : 0 < U n := by rw [hs]; omega
        have hl : U n < n := by rw [hs]; omega
        obtain ⟨t, ht⟩ := ih (U n) hl hp
        exact ⟨t + 1, ht⟩

#print axioms lifted_one_multiple
#print axioms clone_common_clock
#print axioms clone_seed_equation
#print axioms clone_shell
#print axioms clone_current_reversal
#print axioms large_endpoint_no_arrival
#print axioms unit_doubling_to_one
#print axioms first_arrival_ten
#print axioms ten_window
#print axioms clone_retained_seven_eighths
#print axioms halving_clock_bound
#print axioms odd_output_unit
#print axioms positive_hits_unit

end PrearrivalDeficitTransfer
