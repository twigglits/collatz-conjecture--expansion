/- A smaller weighted ladder handles the complementary post-ladder exit.
   The remaining exponent condition is necessary, not a convergence proof. -/
import MinimumLadderBlockExit

namespace MinimumLadderComplement
open OrdinaryCollatz MinimumReturnLadder MinimumInverseEscape MinimumInverseLocality
open MinimumLadderExit MinimumLadderBlockExit MinimumFirstTarget MinimumRootPredecessors
open MinimumClockBarrier

theorem weighted_step (q : Nat) (hq : 0 < q) :
    Backtrack 1 2 (9 * q - 5) (8 * q - 5) := by
  have h0 := Backtrack.even (Backtrack.nil (9 * q - 5))
  have h1 := Backtrack.odd h0
    (show 3 * (12 * q - 7) + 1 = 2 * (2 * (9 * q - 5)) by omega)
  exact Backtrack.odd h1
    (show 3 * (8 * q - 5) + 1 = 2 * (12 * q - 7) by omega)

theorem weighted_ladder (r q : Nat) (hq : 0 < q) :
    Backtrack r (2 * r) (9 ^ r * q - 5) (8 ^ r * q - 5) := by
  induction r generalizing q with
  | zero => simpa using Backtrack.nil (q - 5)
  | succ r ih =>
    have hq' := Nat.mul_pos (Nat.pow_pos (by decide : 0 < 8) (n := r)) hq
    have h0 := weighted_step (8 ^ r * q) hq'
    have h1 := ih (9 * q) (by omega)
    have hm : 8 ^ r * (9 * q) = 9 * (8 ^ r * q) := by ac_rfl
    rw [hm] at h1
    have h2 := backtrack_append h1 h0
    simpa only [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm,
      show 2 * (r + 1) = 2 * r + 2 by omega] using h2

def smallerSource (R : Nat) : Nat := 6 * 8 ^ (R - 1) - 5

theorem smaller_source_bounds (R : Nat) (hR : 3 ≤ R) :
    0 < smallerSource R ∧ smallerSource R < blockValue R 0 ∧
      4 * (smallerSource R + 5) = 3 * (blockValue R 0 + 5) := by
  have hp : 64 ≤ 8 ^ (R - 1) :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 2 ≤ R - 1 by omega)
  have he : 8 ^ R = 8 * 8 ^ (R - 1) := by
    calc
      _ = 8 ^ ((R - 1) + 1) := congrArg (fun j => 8 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  rw [source_identity, he]
  unfold smallerSource
  omega

theorem complementary_bridge (u : Nat) :
    Backtrack 2 3 (27 * u + 2) (32 * u + 1) := by
  have h0 := Backtrack.odd (Backtrack.nil (27 * u + 2))
    (show 3 * (18 * u + 1) + 1 = 2 * (27 * u + 2) by omega)
  have h1 := Backtrack.even h0
  have h2 := Backtrack.odd h1
    (show 3 * (24 * u + 1) + 1 = 2 * (2 * (18 * u + 1)) by omega)
  have h3 := Backtrack.even h2
  exact Backtrack.odd h3
    (show 3 * (32 * u + 1) + 1 = 2 * (2 * (24 * u + 1)) by omega)

theorem complementary_profile (u k q : Nat) (hk : 2 ≤ k) (hq : 0 < q)
    (hd : 2 ^ k * q = 9 * u + 2) (hg : (3 ^ k * q) % 4 = 1) :
    ∃ b, 4 * b + 1 = 3 ^ k * q ∧
      iterate (2 * k + 7) (48 * u + 4) = b ∧
      Backtrack 5 (k + 2) b (32 * u + 1) := by
  let a := 3 ^ (k - 2) * (3 * q)
  have ha : 3 ^ k * q = 3 * a := by
    rw [show k = (k - 2) + 2 by omega, Nat.pow_add]
    dsimp [a]
    grind
  have ha4 : a % 4 = 3 := by rw [ha] at hg; omega
  let v := a / 4
  have hv : a = 4 * v + 3 := by dsimp [v]; omega
  have hz : 3 ^ k * q - 1 = 4 * (3 * v + 2) := by rw [ha, hv]; omega
  have hblock := (odd_block k 0 q hq).1
  simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at hblock
  have hbridge : iterate 5 (48 * u + 4) = 2 ^ k * q - 1 := by
    have he : 48 * u + 4 = 16 * (3 * u) + 4 := by omega
    rw [he, (bridge_profile (3 * u)).1]
    omega
  have hforward : iterate (2 * k + 7) (48 * u + 4) = 3 * v + 2 := by
    rw [show 2 * k + 7 = 5 + (2 * k + 2) by omega, iterate_add, hbridge,
      iterate_add, hblock, hz]
    have he : 4 * (3 * v + 2) = 2 * (2 * (3 * v + 2)) := by omega
    simp only [he, iterate, even_step]
  have h0 := Backtrack.odd (Backtrack.nil (3 * v + 2))
    (show 3 * (2 * v + 1) + 1 = 2 * (3 * v + 2) by omega)
  have h1 := Backtrack.even h0
  have hp := pure_inverse (k - 2) (3 * q) (by omega)
  have hpa : 3 ^ (k - 2) * (3 * q) - 1 = 2 * (2 * v + 1) := by
    change a - 1 = _
    omega
  rw [hpa] at hp
  have h2 := backtrack_append h1 hp
  have h3 := Backtrack.even (Backtrack.even h2)
  have htwo : 2 ^ k * q = 4 * (2 ^ (k - 2) * q) := by
    rw [show k = (k - 2) + 2 by omega, Nat.pow_add]
    grind
  have hpos := Nat.mul_pos (Nat.two_pow_pos (k - 2)) hq
  have hpb : 2 * (2 * (2 ^ (k - 2) * (3 * q) - 1)) = 27 * u + 2 := by
    have he : 2 ^ (k - 2) * (3 * q) = 3 * (2 ^ (k - 2) * q) := by ac_rfl
    rw [he]
    omega
  rw [hpb] at h3
  have h4 := backtrack_append h3 (complementary_bridge u)
  refine ⟨3 * v + 2, by rw [ha, hv]; omega, hforward, ?_⟩
  simpa only [Nat.add_zero, Nat.zero_add,
    show 1 + (k - 2) + 3 = k + 2 by omega] using h4

theorem complementary_coordinates (R : Nat) (hR : R % 2 = 1) :
    ∃ u, 9 ^ R = 48 * u + 9 ∧ 6 * 9 ^ (R - 1) = 32 * u + 6 := by
  have hr : 9 ^ (R - 1) % 8 = 1 := by rw [Nat.pow_mod]; simp
  let u := 9 ^ (R - 1) / 8
  have hx : 9 ^ (R - 1) = 8 * u + 1 := by dsimp [u]; omega
  have h9 : 9 ^ R = 9 * 9 ^ (R - 1) := by
    calc
      _ = 9 ^ ((R - 1) + 1) := congrArg (fun j => 9 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  have h16 := nine_odd_residue R hR
  rw [h9, hx] at h16
  have hu : u % 2 = 0 := by omega
  refine ⟨3 * (u / 2), ?_, ?_⟩
  · rw [h9, hx]
    omega
  · rw [hx]
    omega

theorem complementary_escape (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hk : 2 ≤ k) (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hg : (3 ^ k * q) % 4 = 1) :
    0 < smallerSource R ∧ smallerSource R < blockValue R 0 ∧
      4 * iterate (5 * R + 2 * k + 7) (blockValue R 0) + 1 = 3 ^ k * q ∧
      Backtrack (R + 4) (2 * R + k)
        (iterate (5 * R + 2 * k + 7) (blockValue R 0)) (smallerSource R) ∧
      iterate (5 * R + 2 * k + 4) (smallerSource R) =
        iterate (5 * R + 2 * k + 7) (blockValue R 0) := by
  obtain ⟨u, hx, hy⟩ := complementary_coordinates R hR
  have hd : 2 ^ k * q = 9 * u + 2 := by
    rw [Nat.pow_add, hx] at hX
    have he : 2 ^ k * 16 * q = 16 * (2 ^ k * q) := by ac_rfl
    change 3 * (48 * u + 9) + 5 = 2 ^ k * 16 * q at hX
    rw [he] at hX
    omega
  obtain ⟨b, hb, hforward, hback⟩ := complementary_profile u k q hk hq hd hg
  have hn : iterate (5 * R + 2 * k + 7) (blockValue R 0) = b := by
    rw [show 5 * R + 2 * k + 7 = 5 * R + (2 * k + 7) by omega,
      iterate_add, endpoint_clock, hx]
    have he : 48 * u + 9 - 5 = 48 * u + 4 := by omega
    rw [he, hforward]
  have hp := weighted_ladder (R - 1) 6 (by decide)
  have hp0 : 9 ^ (R - 1) * 6 - 5 = 32 * u + 1 := by omega
  have hp1 : 8 ^ (R - 1) * 6 - 5 = smallerSource R := by unfold smallerSource; omega
  rw [hp0, hp1] at hp
  have hall := backtrack_append hback hp
  have hback' : Backtrack (R + 4) (2 * R + k) b (smallerSource R) := by
    simpa only [show 5 + (R - 1) = R + 4 by omega,
      show k + 2 + 2 * (R - 1) = 2 * R + k by omega] using hall
  have hactual := backtrack_actual hback'
  rw [show R + 4 + 2 * (2 * R + k) = 5 * R + 2 * k + 4 by omega] at hactual
  rw [hn]
  exact ⟨(smaller_source_bounds R hR3).1, (smaller_source_bounds R hR3).2.1,
    hb, hback', hactual⟩

theorem complementary_not_least (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hk : 2 ≤ k) (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hg : (3 ^ k * q) % 4 = 1) : ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  have he := complementary_escape R k q hR3 hR hk hq hX hg
  have hl := least_coalescing_predecessor hn he.1 he.2.2.2.2
  omega

theorem finite_residue_injection :
    ∀ r : Fin 16, (9 : Nat) ^ r.val % 128 = 73 → r.val = 9 := by
  decide +kernel

theorem least_exponent_nine (R : Nat) (hR3 : 3 ≤ R)
    (hn : LeastCounterexample (blockValue R 0)) :
    R % 16 = 9 ∧ ∃ q, 0 < q ∧ q % 4 = 3 ∧ 3 * 9 ^ R + 5 = 32 * q := by
  obtain ⟨hR4, k, q, hk, hq, _, hX, hg⟩ := least_exit_constraint R hR3 hn
  have hR : R % 2 = 1 := by omega
  have hk1 : k = 1 := by
    by_cases htwo : 2 ≤ k
    · exact False.elim (complementary_not_least R k q hR3 hR htwo hq hX hg hn)
    · omega
  subst k
  have hq4 : q % 4 = 3 := by simp only [Nat.pow_one] at hg; omega
  have hx : 3 * 9 ^ R + 5 = 32 * q := by simpa using hX
  have hr : 9 ^ R % 128 = 73 := by omega
  have he : R = 16 * (R / 16) + R % 16 := by omega
  have hp : 9 ^ R % 128 = 9 ^ (R % 16) % 128 := by
    calc
      _ = 9 ^ (16 * (R / 16) + R % 16) % 128 :=
        congrArg (fun j => 9 ^ j % 128) he
      _ = _ := by
        rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
          finite_exit_periods.2.2.2.2]
        simp
  have hi := finite_residue_injection ⟨R % 16, by omega⟩ (by simpa only using hp ▸ hr)
  exact ⟨hi, q, hq, hq4, hx⟩

theorem outside_nine_not_least (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 ≠ 9) :
    ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  exact hR (least_exponent_nine R hR3 hn).1

theorem complementary_first_target (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hk : 3 ≤ k) (hq : 0 < q) (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q)
    (hg : (3 ^ k * q) % 4 = 1) :
    iterate (5 * R + 2 * k + 7) (blockValue R 0) % 27 = 20 ∧
      ∀ t, 5 * R ≤ t → t < 5 * R + 2 * k + 7 →
        iterate t (blockValue R 0) % 27 ≠ 20 := by
  let u := 9 ^ R / 16
  have hr := nine_odd_residue R hR
  have hx : 9 ^ R = 16 * u + 9 := by dsimp [u]; omega
  have hx27 : 9 ^ R % 27 = 0 := by
    have he : R = 3 + (R - 3) := by omega
    rw [he, Nat.pow_add, Nat.mul_mod]
    simp
  have hu : (16 * u + 9) % 27 = 0 := by rw [← hx]; exact hx27
  have hd : 2 ^ k * q = 3 * u + 2 := by
    rw [Nat.pow_add, hx] at hX
    have he : 2 ^ k * 16 * q = 16 * (2 ^ k * q) := by ac_rfl
    change 3 * (16 * u + 9) + 5 = 2 ^ k * 16 * q at hX
    rw [he] at hX
    omega
  have hd' : 2 ^ k * q - 1 = 3 * u + 1 := by omega
  let b := (3 ^ k * q) / 4
  have hb : 3 ^ k * q = 4 * b + 1 := by dsimp [b]; omega
  have hq27 : (3 ^ k * q) % 27 = 0 := by
    have he : k = 3 + (k - 3) := by omega
    rw [he, Nat.pow_add]
    change (27 * 3 ^ (k - 3) * q) % 27 = 0
    rw [Nat.mul_assoc]
    omega
  have hb27 : b % 27 = 20 := by omega
  have hB : iterate (5 * R) (blockValue R 0) = 16 * u + 4 := by
    rw [endpoint_clock, hx]
    omega
  have hA : iterate (5 * R + 5) (blockValue R 0) = 2 ^ k * q - 1 := by
    rw [iterate_add, hB, (bridge_profile u).1, hd']
  have hgood : GoodResidue (2 ^ k * q - 1) := by
    apply Or.inl
    rw [hd', ← (bridge_profile u).1]
    exact (bridge_residues u hu).1
  have hZ : iterate ((5 * R + 5) + 2 * k) (blockValue R 0) = 4 * b := by
    rw [iterate_add, hA]
    have ho := (odd_block k 0 q hq).1
    simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul] at ho
    rw [ho, hb]
    omega
  have hc0 : C (4 * b) = 2 * b := by
    have he : 4 * b = 2 * (2 * b) := by omega
    rw [he, even_step]
  have hlast : ∀ t, t < 2 → iterate t (4 * b) % 27 ≠ 20 := by
    intro t ht
    have hh : t = 0 ∨ t = 1 := by omega
    rcases hh with hh | hh <;> subst t
    all_goals simp only [iterate, hc0]
    all_goals omega
  constructor
  · have ht : 5 * R + 2 * k + 7 = ((5 * R + 5) + 2 * k) + 2 := by omega
    rw [ht, iterate_add _ 2, hZ]
    simpa only [iterate, hc0, even_step] using hb27
  · intro t ht hupper
    by_cases hfirst : t < 5 * R + 5
    · have he : t = 5 * R + (t - 5 * R) := by omega
      rw [he, iterate_add, hB]
      exact (bridge_residues u hu).2 _ (by omega)
    · by_cases hmiddle : t ≤ (5 * R + 5) + 2 * k
      · have he : t = (5 * R + 5) + (t - (5 * R + 5)) := by omega
        rw [he, iterate_add, hA]
        exact odd_block_avoids k q hq hgood _ (by omega)
      · have he : t = ((5 * R + 5) + 2 * k) + (t - ((5 * R + 5) + 2 * k)) := by omega
        rw [he, iterate_add, hZ]
        exact hlast _ (by omega)

theorem all_long_blocks_have_target (R k q : Nat) (hR3 : 3 ≤ R) (hR : R % 2 = 1)
    (hk : 3 ≤ k) (hq : 0 < q) (hqo : q % 2 = 1)
    (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q) :
    ∃ P t s e o, 0 < P ∧ P < blockValue R 0 ∧
      (t = 5 * R + 2 * k + 7 ∨ t = 5 * R + 2 * k + 8) ∧
      iterate t (blockValue R 0) % 27 = 20 ∧
      (∀ j, 5 * R ≤ j → j < t → iterate j (blockValue R 0) % 27 ≠ 20) ∧
      Backtrack e o (iterate t (blockValue R 0)) P ∧ e ≤ R + 4 ∧
      iterate s P = iterate t (blockValue R 0) := by
  have ho : (3 ^ k * q) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hqo]
    simp
  have hc : (3 ^ k * q) % 4 = 1 ∨ (3 ^ k * q) % 4 = 3 := by omega
  rcases hc with hc | hc
  · have he := complementary_escape R k q hR3 hR (by omega) hq hX hc
    have ht := complementary_first_target R k q hR3 hR hk hq hX hc
    exact ⟨smallerSource R, 5 * R + 2 * k + 7, 5 * R + 2 * k + 4,
      R + 4, 2 * R + k, he.1, he.2.1, Or.inl rfl, ht.1, ht.2,
      he.2.2.2.1, by omega, he.2.2.2.2⟩
  · have he := block_escape R k q hR3 hR hq hX hc
    have ht := first_late_target R k q hR3 hR (by omega) hq hX hc
    exact ⟨2 ^ (2 * R + 1) - 1, 5 * R + 2 * k + 8, 4 * R + 2 * k + 9,
      5, 2 * R + k + 2, he.1, he.2.1, Or.inr rfl, ht.1, ht.2,
      he.2.2.1, by omega, he.2.2.2⟩

theorem old_progression_resolved (h : Nat) :
    let R := 512 * h + 5
    0 < smallerSource R ∧ smallerSource R < blockValue R 0 ∧
      Backtrack (R + 4) (2 * R + 6)
        (iterate (5 * R + 19) (blockValue R 0)) (smallerSource R) ∧
      iterate (5 * R + 16) (smallerSource R) = iterate (5 * R + 19) (blockValue R 0) ∧
      iterate (5 * R + 19) (blockValue R 0) % 27 = 20 ∧
      (∀ t, 5 * R ≤ t → t < 5 * R + 19 → iterate t (blockValue R 0) % 27 ≠ 20) ∧
      ¬ LeastCounterexample (blockValue R 0) := by
  dsimp only
  obtain ⟨hR3, hR4, _, q, hq, _, hX, hg⟩ := surviving_progression h
  have ho : (512 * h + 5) % 2 = 1 := by omega
  have he := complementary_escape (512 * h + 5) 6 q hR3 ho (by decide) hq hX hg
  have ht := complementary_first_target (512 * h + 5) 6 q hR3 ho (by decide) hq hX hg
  have hn := complementary_not_least (512 * h + 5) 6 q hR3 ho (by decide) hq hX hg
  exact ⟨he.1, he.2.1, by simpa only [Nat.add_assoc] using he.2.2.2.1,
    by simpa only [Nat.add_assoc] using he.2.2.2.2,
    by simpa only [Nat.add_assoc] using ht.1,
    by simpa only [Nat.add_assoc] using ht.2, hn⟩

theorem remaining_progression (h : Nat) :
    let R := 16 * h + 9
    3 ≤ R ∧ h < R ∧ R % 16 = 9 ∧
      ∃ q, 0 < q ∧ q % 4 = 3 ∧ 3 * 9 ^ R + 5 = 32 * q := by
  dsimp only
  have hx : 9 ^ (16 * h + 9) % 128 = 73 := by
    rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
      finite_exit_periods.2.2.2.2]
    simp
  let u := 9 ^ (16 * h + 9) / 128
  have he : 9 ^ (16 * h + 9) = 128 * u + 73 := by dsimp [u]; omega
  refine ⟨by omega, by omega, by omega, 12 * u + 7, by omega, by omega, ?_⟩
  omega

theorem remaining_profile (u : Nat) :
    iterate 9 (384 * u + 196) = 27 * u + 14 ∧
      iterate 9 (256 * u + 129) = 108 * u + 55 := by
  have n0 : C (384 * u + 196) = 192 * u + 98 := by unfold C; split <;> omega
  have n1 : C (192 * u + 98) = 96 * u + 49 := by unfold C; split <;> omega
  have n2 : C (96 * u + 49) = 288 * u + 148 := by unfold C; split <;> omega
  have n3 : C (288 * u + 148) = 144 * u + 74 := by unfold C; split <;> omega
  have n4 : C (144 * u + 74) = 72 * u + 37 := by unfold C; split <;> omega
  have n5 : C (72 * u + 37) = 216 * u + 112 := by unfold C; split <;> omega
  have n6 : C (216 * u + 112) = 108 * u + 56 := by unfold C; split <;> omega
  have n7 : C (108 * u + 56) = 54 * u + 28 := by unfold C; split <;> omega
  have n8 : C (54 * u + 28) = 27 * u + 14 := by unfold C; split <;> omega
  have p0 : C (256 * u + 129) = 768 * u + 388 := by unfold C; split <;> omega
  have p1 : C (768 * u + 388) = 384 * u + 194 := by unfold C; split <;> omega
  have p2 : C (384 * u + 194) = 192 * u + 97 := by unfold C; split <;> omega
  have p3 : C (192 * u + 97) = 576 * u + 292 := by unfold C; split <;> omega
  have p4 : C (576 * u + 292) = 288 * u + 146 := by unfold C; split <;> omega
  have p5 : C (288 * u + 146) = 144 * u + 73 := by unfold C; split <;> omega
  have p6 : C (144 * u + 73) = 432 * u + 220 := by unfold C; split <;> omega
  have p7 : C (432 * u + 220) = 216 * u + 110 := by unfold C; split <;> omega
  have p8 : C (216 * u + 110) = 108 * u + 55 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, n0, n1, n2, n3, n4, n5, n6, n7, n8],
    by simp only [iterate, p0, p1, p2, p3, p4, p5, p6, p7, p8]⟩

theorem remaining_pair (R : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 9) :
    ∃ b, 128 * b + 17 = 9 * 9 ^ R ∧ b % 27 = 14 ∧
      iterate (5 * R + 9) (blockValue R 0) = b ∧
      iterate (5 * R + 4) (smallerSource R) = 4 * b - 1 := by
  have hdecomp : R = 16 * (R / 16) + 9 := by omega
  have hx : 9 ^ R % 128 = 73 := by
    rw [hdecomp, Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod,
      finite_exit_periods.2.2.2.2]
    simp
  have hpow : 9 ^ R = 9 * 9 ^ (R - 1) := by
    calc
      _ = 9 ^ ((R - 1) + 1) := congrArg (fun j => 9 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_succ]; omega
  let u := 9 ^ R / 384
  have hX : 9 ^ R = 384 * u + 201 := by dsimp [u]; omega
  have hY : 6 * 9 ^ (R - 1) = 256 * u + 134 := by omega
  have hN : iterate (5 * R + 9) (blockValue R 0) = 27 * u + 14 := by
    rw [iterate_add, endpoint_clock, hX]
    have he : 384 * u + 201 - 5 = 384 * u + 196 := by omega
    rw [he, (remaining_profile u).1]
  have hP0 := backtrack_actual (weighted_ladder (R - 1) 6 (by decide))
  have hc : R - 1 + 2 * (2 * (R - 1)) = 5 * (R - 1) := by omega
  have hs : 8 ^ (R - 1) * 6 - 5 = smallerSource R := by unfold smallerSource; omega
  have ht : 9 ^ (R - 1) * 6 - 5 = 256 * u + 129 := by omega
  rw [hc, hs, ht] at hP0
  have hP : iterate (5 * R + 4) (smallerSource R) = 108 * u + 55 := by
    rw [show 5 * R + 4 = 5 * (R - 1) + 9 by omega, iterate_add, hP0,
      (remaining_profile u).2]
  exact ⟨27 * u + 14, by omega, by omega, hN, by rw [hP]; omega⟩

theorem remaining_merge_suffices (R s t : Nat) (hR3 : 3 ≤ R) (hR : R % 16 = 9)
    (hmerge : iterate s (iterate (5 * R + 9) (blockValue R 0)) =
      iterate t (4 * iterate (5 * R + 9) (blockValue R 0) - 1)) :
    ¬ LeastCounterexample (blockValue R 0) := by
  intro hn
  obtain ⟨b, _, _, hN, hP⟩ := remaining_pair R hR3 hR
  have he : iterate ((5 * R + 4) + t) (smallerSource R) =
      iterate ((5 * R + 9) + s) (blockValue R 0) := by
    rw [iterate_add (5 * R + 4) t, iterate_add (5 * R + 9) s, hN, hP]
    rw [hN] at hmerge
    exact hmerge.symm
  have hl := least_coalescing_predecessor hn (smaller_source_bounds R hR3).1 he
  have hs := (smaller_source_bounds R hR3).2.1
  omega

theorem half_period_flip (R k q : Nat) (hq : 0 < q) (hqo : q % 2 = 1)
    (hX : 3 * 9 ^ R + 5 = 2 ^ (k + 4) * q) (hg : (3 ^ k * q) % 4 = 3) :
    ∃ Q, 0 < Q ∧ Q % 2 = 1 ∧
      3 * 9 ^ (R + 2 ^ (k + 2)) + 5 = 2 ^ (k + 4) * Q ∧
      (3 ^ k * Q) % 4 = 1 := by
  obtain ⟨c, hc⟩ := MinimumCriticalClockLift.nine_power_top_bit (k + 2)
  have hpow : 2 ^ (k + 2 + 3) = 2 * 2 ^ (k + 4) := by
    rw [show k + 2 + 3 = (k + 4) + 1 by omega, Nat.pow_succ]
    omega
  rw [hpow] at hc
  let delta := 3 * 9 ^ R * (2 * c + 1)
  have hd : delta % 2 = 1 := by
    dsimp [delta]
    simp [Nat.mul_mod, Nat.pow_mod]
  have hodd : (3 ^ k * delta) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod, hd]
    simp
  let Q := q + 2 * delta
  have hnew : 3 * 9 ^ (R + 2 ^ (k + 2)) + 5 = 2 ^ (k + 4) * Q := by
    rw [Nat.pow_add, hc]
    dsimp [Q, delta]
    grind
  have he : 3 ^ k * Q = 3 ^ k * q + 2 * (3 ^ k * delta) := by
    dsimp [Q]
    grind
  refine ⟨Q, by dsimp [Q]; omega, by dsimp [Q]; omega, hnew, ?_⟩
  rw [he]
  omega

theorem unbounded_complementary_lifts (k B : Nat) :
    ∃ R q, B < R ∧ 3 ≤ R ∧ R % 2 = 1 ∧ 0 < q ∧ q % 2 = 1 ∧
      3 * 9 ^ R + 5 = 2 ^ (k + 4) * q ∧ (3 ^ k * q) % 4 = 1 := by
  obtain ⟨R, q, hB, hR3, _, hq, hqo, hX, hg⟩ := unbounded_block_lifts k B
  obtain ⟨Q, hQ, hQo, hnew, hbad⟩ := half_period_flip R k q hq hqo hX hg
  have hpositive := Nat.two_pow_pos (k + 2)
  exact ⟨R + 2 ^ (k + 2), Q, by omega, by omega,
    block_lift_odd _ k Q hnew, hQ, hQo, hnew, hbad⟩

theorem unbounded_complementary_first_targets (k B : Nat) (hk : 3 ≤ k) :
    ∃ R P, 3 ≤ R ∧ R % 2 = 1 ∧ B < blockValue R 0 ∧
      MinimumTailRigidity.prefixMinimum (5 * R) (blockValue R 0) = blockValue R 0 ∧
      0 < P ∧ P < blockValue R 0 ∧
      iterate (5 * R + 2 * k + 7) (blockValue R 0) % 27 = 20 ∧
      (∀ t, 5 * R ≤ t → t < 5 * R + 2 * k + 7 → iterate t (blockValue R 0) % 27 ≠ 20) ∧
      Backtrack (R + 4) (2 * R + k)
        (iterate (5 * R + 2 * k + 7) (blockValue R 0)) P ∧
      iterate (5 * R + 2 * k + 4) P = iterate (5 * R + 2 * k + 7) (blockValue R 0) ∧
      ¬ LeastCounterexample (blockValue R 0) := by
  obtain ⟨R, q, hB, hR3, hRo, hq, _, hX, hg⟩ := unbounded_complementary_lifts k B
  have he := complementary_escape R k q hR3 hRo (by omega) hq hX hg
  have ht := complementary_first_target R k q hR3 hRo hk hq hX hg
  have hs := MinimumReturnLadder.source_growth R hR3
  exact ⟨R, smallerSource R, hR3, hRo, by omega,
    (block_prefix R R (by omega)).2, he.1, he.2.1, ht.1, ht.2,
    he.2.2.2.1, he.2.2.2.2,
    complementary_not_least R k q hR3 hRo (by omega) hq hX hg⟩

#print axioms weighted_step
#print axioms weighted_ladder
#print axioms smaller_source_bounds
#print axioms complementary_bridge
#print axioms complementary_profile
#print axioms complementary_coordinates
#print axioms complementary_escape
#print axioms complementary_not_least
#print axioms finite_residue_injection
#print axioms least_exponent_nine
#print axioms outside_nine_not_least
#print axioms complementary_first_target
#print axioms all_long_blocks_have_target
#print axioms old_progression_resolved
#print axioms remaining_progression
#print axioms remaining_profile
#print axioms remaining_pair
#print axioms remaining_merge_suffices
#print axioms half_period_flip
#print axioms unbounded_complementary_lifts
#print axioms unbounded_complementary_first_targets

end MinimumLadderComplement
