import CollatzCycleCriterion

/-
  Exact finite local lifts of rational Collatz cycles.
  No divisibility of the cycle numerator by its denominator is assumed.
  The graph conclusion is a closed walk of residue classes, not an
  actual positive integer cycle. All proofs use the Lean kernel.
-/
namespace CycleLocalLifts

open CollatzCycleCriterion

/-- A signed Bezout identity, proved by the Euclidean algorithm. -/
theorem bezout (a b : Nat) :
    ∃ x y : Int, (a : Int) * x + (b : Int) * y = (Nat.gcd a b : Nat) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
      by_cases ha : a = 0
      · subst a
        exact ⟨0, 1, by simp⟩
      · obtain ⟨x, y, he⟩ := ih (b % a) (Nat.mod_lt b (by omega)) a
        refine ⟨y - (b / a : Nat) * x, x, ?_⟩
        have hd := congrArg (fun n : Nat => (n : Int)) (Nat.mod_add_div b a)
        simp only [Int.natCast_add, Int.natCast_mul] at hd
        rw [← Nat.gcd_rec a b] at he
        grind

theorem smooth_coprime (D a b : Nat)
    (h2 : Nat.gcd D 2 = 1) (h3 : Nat.gcd D 3 = 1) :
    Nat.gcd D (2^a * 3^b) = 1 := by
  rw [Nat.gcd_mul_right_right_of_gcd_eq_one (Nat.gcd_pow_right_of_gcd_eq_one h2)]
  exact Nat.gcd_pow_right_of_gcd_eq_one h3

def lift (L : Nat) (z : Int) (W : Nat) : Nat :=
  (z * (W : Int) % (L : Int)).toNat

theorem cast_lift (L : Nat) (hL : 0 < L) (z : Int) (W : Nat) :
    (lift L z W : Int) = z * (W : Int) % (L : Int) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

theorem lift_bound (L : Nat) (hL : 0 < L) (z : Int) (W : Nat) :
    lift L z W < L := by
  have he := cast_lift L hL z W
  have hh := Int.emod_lt_of_pos (z * (W : Int)) (show (0 : Int) < L by omega)
  omega

theorem lift_denominator_congruence (L D : Nat) (hL : 0 < L)
    (z v : Int) (hbez : (D : Int) * z + (L : Int) * v = 1) (W : Nat) :
    (D * lift L z W) % L = W % L := by
  have he := Int.emod_add_mul_ediv (z * (W : Int)) (L : Int)
  rw [← cast_lift L hL z W] at he
  have hd : (L : Int) ∣ (D : Int) * (lift L z W : Int) - (W : Int) := by
    refine ⟨-v * (W : Int) - (D : Int) * (z * (W : Int) / (L : Int)), ?_⟩
    grind
  apply Int.ofNat.inj
  change ((D : Int) * (lift L z W : Int)) % (L : Int) = (W : Int) % (L : Int)
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)

theorem reduce_congruence (L Q a b : Nat) (hQ : Q ∣ L)
    (he : a % L = b % L) : a % Q = b % Q := by
  have hh := congrArg (fun n => n % Q) he
  simpa only [Nat.mod_mod_of_dvd _ hQ] using hh

theorem lift_odd (L D : Nat) (hL : 0 < L) (hL2 : 2 ∣ L)
    (hD2 : D % 2 = 1) (z v : Int)
    (hbez : (D : Int) * z + (L : Int) * v = 1)
    (W : Nat) (hW : W % 2 = 1) : lift L z W % 2 = 1 := by
  have hh := reduce_congruence L 2 (D * lift L z W) W hL2
    (lift_denominator_congruence L D hL z v hbez W)
  simpa [Nat.mul_mod, hD2, hW] using hh

/-- The affine edge is preserved at the full lifted precision L. -/
theorem lift_edge (L D A B P : Nat) (hL : 0 < L)
    (z v : Int) (hbez : (D : Int) * z + (L : Int) * v = 1)
    (he : P * B = 3 * A + D) :
    (P * lift L z B) % L = (3 * lift L z A + 1) % L := by
  have ha := Int.emod_add_mul_ediv (z * (A : Int)) (L : Int)
  have hb := Int.emod_add_mul_ediv (z * (B : Int)) (L : Int)
  rw [← cast_lift L hL z A] at ha
  rw [← cast_lift L hL z B] at hb
  have he' := congrArg (fun n : Nat => (n : Int)) he
  simp only [Int.natCast_add, Int.natCast_mul] at he'
  have hd : (L : Int) ∣ (P : Int) * (lift L z B : Int) -
      (3 * (lift L z A : Int) + 1) := by
    refine ⟨3 * (z * (A : Int) / (L : Int)) -
      (P : Int) * (z * (B : Int) / (L : Int)) - v, ?_⟩
    grind
  apply Int.ofNat.inj
  change ((P : Int) * (lift L z B : Int)) % (L : Int) =
    (3 * (lift L z A : Int) + 1) % (L : Int)
  exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)

/-- Division loses h bits of precision. Keeping the modulus 2^h*M
    proves both the exact valuation and the successor residue modulo M. -/
theorem branch_of_congruence (h x y M : Nat) (hM2 : 2 ∣ M)
    (hy : y % 2 = 1)
    (he : (2^h * y) % (2^h * M) = (3*x+1) % (2^h * M)) :
    F x % M = y % M ∧ v2 (3*x+1) = h := by
  have hP : 0 < 2^h := Nat.pow_pos (by decide)
  have hd := reduce_congruence (2^h * M) (2^h) (2^h * y) (3*x+1)
    (Nat.dvd_mul_right _ _) he
  have hz : (3*x+1) % (2^h) = 0 := by simpa using hd.symm
  have hf : 2^h * ((3*x+1) / 2^h) = 3*x+1 :=
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hz)
  have hq := congrArg (fun n => n / 2^h) he
  rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self,
    Nat.mul_div_cancel_left y hP] at hq
  have ho := reduce_congruence M 2 y ((3*x+1) / 2^h) hM2 hq
  have hqo : ((3*x+1) / 2^h) % 2 = 1 := by omega
  have ha := actual_step h x ((3*x+1) / 2^h) hqo hf
  exact ⟨by rw [ha.1]; exact hq.symm, ha.2⟩

/-- Every cyclic numerator system has exact integer edge witnesses modulo M
    whenever D is invertible at a sufficiently fine even precision L. -/
theorem cyclic_local_lifts (k D M L : Nat) (h W : Nat → Nat)
    (hL : 0 < L) (hL2 : 2 ∣ L) (hM2 : 2 ∣ M)
    (hD2 : D % 2 = 1) (hg : Nat.gcd D L = 1)
    (hprec : ∀ i, i < k → 2^(h i) * M ∣ L)
    (hodd : ∀ i, i ≤ k → W i % 2 = 1)
    (hrot : ∀ i, i < k → 2^(h i) * W (i+1) = 3 * W i + D)
    (hclose : W k = W 0) :
    ∃ x : Nat → Nat,
      (∀ i, i ≤ k → 0 < x i ∧ x i < L ∧ x i % 2 = 1) ∧
      x k = x 0 ∧
      (∀ i, i < k → F (x i) % M = x (i+1) % M ∧
        v2 (3 * x i + 1) = h i) := by
  obtain ⟨z, v, hb⟩ := bezout D L
  rw [hg] at hb
  refine ⟨fun i => lift L z (W i), ?_, ?_, ?_⟩
  · intro i hi
    dsimp only
    have ho := lift_odd L D hL hL2 hD2 z v hb (W i) (hodd i hi)
    exact ⟨by omega, lift_bound L hL z (W i), ho⟩
  · change lift L z (W k) = lift L z (W 0)
    rw [hclose]
  · intro i hi
    have he := lift_edge L D (W i) (W (i+1)) (2^(h i)) hL z v hb (hrot i hi)
    have hh := reduce_congruence L (2^(h i) * M) _ _ (hprec i hi) he
    exact branch_of_congruence (h i) _ _ M hM2
      (lift_odd L D hL hL2 hD2 z v hb (W (i+1)) (hodd (i+1) (by omega))) hh

theorem head_le_sum (word : List Nat) : word.headD 0 ≤ word.sum := by
  cases word <;> simp

theorem word_coprime_three (word : List Nat) (hne : word ≠ [])
    (hD : 0 < denominator word) : Nat.gcd 3 (denominator word) = 1 := by
  have hl : 0 < word.length := List.length_pos_iff.mpr hne
  have hle : 3^word.length ≤ 2^word.sum := by unfold denominator at hD; omega
  have hd : 3 ∣ 3^word.length := by
    have hh := Nat.pow_dvd_pow 3 (show 1 ≤ word.length by omega)
    simpa using hh
  unfold denominator
  rw [Nat.gcd_sub_right_right_of_dvd 3 hle hd]
  exact Nat.gcd_pow_right_of_gcd_eq_one (by decide)

theorem precision_divides (a b H h : Nat) (hh : h ≤ H) :
    2^h * (2^a * 3^b) ∣ 2^(a+H) * 3^b := by
  refine ⟨2^(H-h), ?_⟩
  have he : a+H = (h+a)+(H-h) := by omega
  rw [he, Nat.pow_add, Nat.pow_add]
  ac_rfl

/-- Every positive-denominator positive halving word has a closed walk in
    the exact residue graph modulo 2^a*3^b, at every finite a>0 and b.
    Each edge is witnessed by an actual positive odd integer with exactly
    the prescribed valuation. The witnesses need not form an integer cycle. -/
theorem every_word_has_smooth_local_lifts (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h) (hD : 0 < denominator word)
    (a b : Nat) (ha : 0 < a) :
    ∃ x : Nat → Nat,
      (∀ i, i ≤ word.length →
        0 < x i ∧ x i < 2^(a+word.sum)*3^b ∧ x i % 2 = 1) ∧
      x word.length = x 0 ∧
      (∀ i (hi : i < word.length),
        F (x i) % (2^a*3^b) = x (i+1) % (2^a*3^b) ∧
        v2 (3*x i+1) = word[i]) := by
  have hk : 0 < word.length := List.length_pos_iff.mpr hne
  have hnr : ∀ i, rotate word i ≠ [] := by
    intro i he
    have hl := rotate_length word i
    rw [he] at hl
    simp only [List.length_nil] at hl
    omega
  have hdr : ∀ i, denominator (rotate word i) = denominator word := by
    intro i
    simp only [denominator, rotate_sum, rotate_length]
  have hg2 := denominator_coprime_two word hne hp hD
  have hg3 := word_coprime_three word hne hD
  have hoddD : denominator word % 2 = 1 := by
    have hh := hg2
    rw [Nat.gcd_rec] at hh
    by_cases hz : denominator word % 2 = 0
    · simp [hz] at hh
    · omega
  have hM2 : 2 ∣ 2^a*3^b := by
    have hh := Nat.pow_dvd_pow 2 (show 1 ≤ a by omega)
    have h2a : 2 ∣ 2^a := by simpa using hh
    exact Nat.dvd_trans h2a (Nat.dvd_mul_right _ _)
  have hML : 2^a*3^b ∣ 2^(a+word.sum)*3^b := by
    simpa using precision_divides a b word.sum 0 (by omega)
  have hL : 0 < 2^(a+word.sum)*3^b :=
    Nat.mul_pos (Nat.pow_pos (by decide)) (Nat.pow_pos (by decide))
  have hrot : ∀ i, i < word.length →
      2^((rotate word i).headD 0) * weight (rotate word (i+1)) =
        3 * weight (rotate word i) + denominator word := by
    intro i _
    have he := rotation_identity (rotate word i) (hnr i) (by rw [hdr]; exact hD)
    simpa only [rotate, hdr] using he
  have hprec : ∀ i, i < word.length →
      2^((rotate word i).headD 0) * (2^a*3^b) ∣ 2^(a+word.sum)*3^b := by
    intro i _
    apply precision_divides
    have hh := head_le_sum (rotate word i)
    simpa only [rotate_sum] using hh
  obtain ⟨x, hx, hclose, he⟩ := cyclic_local_lifts word.length (denominator word)
    (2^a*3^b) (2^(a+word.sum)*3^b)
    (fun i => (rotate word i).headD 0) (fun i => weight (rotate word i))
    hL (Nat.dvd_trans hM2 hML) hM2 hoddD
    (smooth_coprime _ _ _ (by simpa [Nat.gcd_comm] using hg2)
      (by simpa [Nat.gcd_comm] using hg3))
    hprec
    (fun i _ => weight_odd _ (hnr i) (rotate_positive word i hp))
    hrot (by rw [rotate_full, rotate])
  refine ⟨x, hx, hclose, ?_⟩
  intro i hi
  have hh := he i hi
  rw [rotate_head word i hi] at hh
  exact hh

/-- A fixed size bound changes the conclusion: once both sides are below
    the modulus, a residue equality is an exact integer equality. -/
theorem bounded_lift_forces_divisibility (D W B L x : Nat)
    (hx : x ≤ B) (hDB : D*B < L) (hW : W < L)
    (he : (D*x) % L = W % L) : D ∣ W := by
  have hDx : D*x < L := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left D hx) hDB
  rw [Nat.mod_eq_of_lt hDx, Nat.mod_eq_of_lt hW] at he
  exact ⟨x, he.symm⟩

theorem concrete_rational_cycle :
    weight [1,2,2] = 23 ∧ denominator [1,2,2] = 5 ∧
    weight [2,2,1] = 37 ∧ weight [2,1,2] = 29 ∧
    ¬ 5 ∣ weight [1,2,2] := by decide

theorem graph_mod64_witness :
    F 107 % 64 = 161 % 64 ∧ F 161 % 64 = 57 % 64 ∧
    F 57 % 64 = 107 % 64 ∧
    v2 (3*107+1) = 1 ∧ v2 (3*161+1) = 2 ∧ v2 (3*57+1) = 2 ∧
    107 % 64 = 43 ∧ 161 % 64 = 33 ∧ 57 % 64 = 57 ∧
    F 57 ≠ 107 := by
  have h1 := actual_step 1 107 161 (by decide) (by decide)
  have h2 := actual_step 2 161 121 (by decide) (by decide)
  have h3 := actual_step 2 57 43 (by decide) (by decide)
  simp only [h1.1, h2.1, h3.1, h1.2, h2.2, h3.2]
  decide

/-- Primitive binary word disproving the size inequality asserted as
    Theorem 6.2 in the external preprint discussed in the written note. -/
theorem external_size_claim_counterexample :
    weight [1,2,2,2,2,1,2,2] = 23413 ∧
    denominator [1,2,2,2,2,1,2,2] = 9823 ∧
    2^14 ≥ 2*3^8 ∧
    weight [1,2,2,2,2,1,2,2] - denominator [1,2,2,2,2,1,2,2] >
      denominator [1,2,2,2,2,1,2,2] := by decide

#print axioms bezout
#print axioms smooth_coprime
#print axioms lift_denominator_congruence
#print axioms lift_odd
#print axioms lift_edge
#print axioms branch_of_congruence
#print axioms cyclic_local_lifts
#print axioms every_word_has_smooth_local_lifts
#print axioms bounded_lift_forces_divisibility
#print axioms concrete_rational_cycle
#print axioms graph_mod64_witness
#print axioms external_size_claim_counterexample
end CycleLocalLifts
