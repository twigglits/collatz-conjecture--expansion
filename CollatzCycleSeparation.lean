/-
  Adjacent halving transfers cannot both pass the positive cycle test.
  Standalone Lean 4; kernel proofs only, no Mathlib or native evaluation.
  The weight and denominator definitions and append formula are identical
  to those in CollatzCycleCriterion.lean, in a separate namespace.
  Check: lean CollatzCycleSeparation.lean
-/
namespace CollatzCycleSeparation

def weight : List Nat → Nat
  | [] => 0
  | h :: tail => 3 ^ tail.length + 2 ^ h * weight tail

def denominator (word : List Nat) : Nat := 2 ^ word.sum - 3 ^ word.length

def leftWord (pre post : List Nat) (a b : Nat) : List Nat :=
  pre ++ [a + 1, b] ++ post

def rightWord (pre post : List Nat) (a b : Nat) : List Nat :=
  pre ++ [a, b + 1] ++ post

theorem weight_append (a b : List Nat) :
    weight (a ++ b) = 3 ^ b.length * weight a + 2 ^ a.sum * weight b := by
  induction a with
  | nil => simp [weight]
  | cons h a ih =>
    simp only [List.cons_append, weight, List.length_append, List.sum_cons,
      Nat.pow_add, ih]
    grind

/-- The dependence on a replaced block separates into two common terms and
    a positive monomial times that block's numerator. -/
theorem weight_context (pre block post : List Nat) :
    weight (pre ++ block ++ post) =
      3 ^ (block.length + post.length) * weight pre +
      2 ^ pre.sum * 3 ^ post.length * weight block +
      2 ^ (pre.sum + block.sum) * weight post := by
  simp only [weight_append, List.sum_append, Nat.pow_add]
  grind

/-- Natural subtraction is intentional: this equality holds in both orders,
    including the order in which both differences truncate to zero. -/
theorem replacement_difference (pre post u v : List Nat)
    (hl : u.length = v.length) (hs : u.sum = v.sum) :
    weight (pre ++ u ++ post) - weight (pre ++ v ++ post) =
      (2 ^ pre.sum * 3 ^ post.length) * (weight u - weight v) := by
  rw [weight_context, weight_context, hl, hs, Nat.mul_sub]
  omega

theorem transfer_length (pre post : List Nat) (a b : Nat) :
    (leftWord pre post a b).length = (rightWord pre post a b).length := by
  simp [leftWord, rightWord]

theorem transfer_sum (pre post : List Nat) (a b : Nat) :
    (leftWord pre post a b).sum = (rightWord pre post a b).sum := by
  simp [leftWord, rightWord, List.sum_append, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

theorem transfer_denominator (pre post : List Nat) (a b : Nat) :
    denominator (leftWord pre post a b) =
      denominator (rightWord pre post a b) := by
  unfold denominator
  rw [transfer_length, transfer_sum]

/-- Moving one halving from the second selected position to the first raises
    the numerator by exactly one monomial. No positivity assumptions are used. -/
theorem transfer_weight (pre post : List Nat) (a b : Nat) :
    weight (leftWord pre post a b) = weight (rightWord pre post a b) +
      2 ^ (pre.sum + a) * 3 ^ post.length := by
  simp only [leftWord, rightWord, weight_append, List.length_cons, List.length_nil,
    weight, Nat.pow_add, Nat.pow_succ]
  grind

/-- A number coprime to both 2 and 3 can divide a 2-3 monomial only if it is 1. -/
theorem divisor_of_monomial (D A B : Nat)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hd : D ∣ 2 ^ A * 3 ^ B) : D = 1 := by
  have hc := Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr hd
  rw [Nat.gcd_comm D (2 ^ A), Nat.gcd_comm D (3 ^ B),
    Nat.gcd_pow_left_of_gcd_eq_one h2, Nat.gcd_pow_left_of_gcd_eq_one h3] at hc
  exact Nat.eq_one_of_dvd_one (by simpa using hc)

theorem cancel_monomial (D A B C : Nat)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hd : D ∣ (2 ^ A * 3 ^ B) * C) : D ∣ C := by
  rw [Nat.mul_assoc] at hd
  have hc := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hd
  rw [Nat.gcd_comm D (2 ^ A), Nat.gcd_pow_left_of_gcd_eq_one h2,
    Nat.one_mul] at hc
  have hc' := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hc
  rwa [Nat.gcd_comm D (3 ^ B), Nat.gcd_pow_left_of_gcd_eq_one h3,
    Nat.one_mul] at hc'

/-- Any common divisor coprime to 6 survives cancellation of the unchanged
    context. Swapping u and v gives the opposite natural difference. -/
theorem replacement_divides_difference (pre post u v : List Nat) (D : Nat)
    (hl : u.length = v.length) (hs : u.sum = v.sum)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hu : D ∣ weight (pre ++ u ++ post))
    (hv : D ∣ weight (pre ++ v ++ post)) :
    D ∣ weight u - weight v := by
  have hd := Nat.dvd_sub hu hv
  rw [replacement_difference pre post u v hl hs] at hd
  exact cancel_monomial D pre.sum post.length _ h2 h3 hd

/-- The sum of the two natural differences is the absolute numerator
    difference, so no ordering hypothesis or truncated conclusion is needed. -/
theorem replacement_divides_distance (pre post u v : List Nat) (D : Nat)
    (hl : u.length = v.length) (hs : u.sum = v.sum)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hu : D ∣ weight (pre ++ u ++ post))
    (hv : D ∣ weight (pre ++ v ++ post)) :
    D ∣ (weight u - weight v) + (weight v - weight u) :=
  Nat.dvd_add
    (replacement_divides_difference pre post u v D hl hs h2 h3 hu hv)
    (replacement_divides_difference pre post v u D hl.symm hs.symm h2 h3 hv hu)

/-- Below one denominator of separation, simultaneous divisibility forces
    equal local numerators. This does not yet assert equality of the blocks. -/
theorem replacement_equal_weight (pre post u v : List Nat) (D : Nat)
    (hl : u.length = v.length) (hs : u.sum = v.sum)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hu : D ∣ weight (pre ++ u ++ post))
    (hv : D ∣ weight (pre ++ v ++ post))
    (hbound : (weight u - weight v) + (weight v - weight u) < D) :
    weight u = weight v := by
  have hd := replacement_divides_distance pre post u v D hl hs h2 h3 hu hv
  by_cases he : weight u = weight v
  · exact he
  · have hp : 0 < (weight u - weight v) + (weight v - weight u) := by omega
    have := Nat.le_of_dvd hp hd
    omega

theorem weight_odd (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h) : weight word % 2 = 1 := by
  cases word with
  | nil => contradiction
  | cons h tail =>
    have hh : 0 < h := hp h (by simp)
    obtain ⟨r, rfl⟩ : ∃ r, h = r + 1 := ⟨h - 1, by omega⟩
    simp [weight, Nat.pow_succ, Nat.add_mod, Nat.mul_mod, Nat.pow_mod]

/-- Uniqueness of a power of two times an odd factor. -/
theorem odd_factors_unique (a b x y : Nat) (hx : x % 2 = 1) (hy : y % 2 = 1)
    (he : 2 ^ a * x = 2 ^ b * y) : a = b ∧ x = y := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => simpa using he
    | succ b =>
      have hm := congrArg (fun n => n % 2) he
      simp [Nat.pow_succ, Nat.mul_mod, hx] at hm
  | succ a ih =>
    cases b with
    | zero =>
      have hm := congrArg (fun n => n % 2) he
      simp [Nat.pow_succ, Nat.mul_mod, hy] at hm
    | succ b =>
      have hc : 2 ^ a * x = 2 ^ b * y := by
        simp only [Nat.pow_succ] at he
        grind
      obtain ⟨hab, hxy⟩ := ih b hc
      exact ⟨by omega, hxy⟩

/-- Positivity of the symbols makes every nonempty tail numerator odd. The
    numerator then determines each head until the final symbol, which is fixed
    by the total sum. Both the length and sum assumptions are essential. -/
theorem weight_injective (u v : List Nat)
    (hu : ∀ h ∈ u, 0 < h) (hv : ∀ h ∈ v, 0 < h)
    (hl : u.length = v.length) (hs : u.sum = v.sum)
    (hw : weight u = weight v) : u = v := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => rfl
    | cons b v => simp at hl
  | cons a u ih =>
    cases v with
    | nil => simp at hl
    | cons b v =>
      have hlen : u.length = v.length := by simpa using hl
      have hpu : ∀ h ∈ u, 0 < h := by
        intro h hh
        exact hu h (List.mem_cons_of_mem a hh)
      have hpv : ∀ h ∈ v, 0 < h := by
        intro h hh
        exact hv h (List.mem_cons_of_mem b hh)
      by_cases he : u = []
      · subst u
        have hev : v = [] := by simpa using hlen.symm
        subst v
        simpa using hs
      · have hev : v ≠ [] := by
          intro hvnil
          simp [hvnil] at hlen
          exact he hlen
        have heq : 2 ^ a * weight u = 2 ^ b * weight v := by
          simp only [weight, hlen] at hw
          omega
        obtain ⟨hab, hweight⟩ := odd_factors_unique a b _ _
          (weight_odd u he hpu) (weight_odd v hev hpv) heq
        have hsum : u.sum = v.sum := by
          simp only [List.sum_cons] at hs
          omega
        have ht := ih v hpu hpv hlen hsum hweight
        simp [hab, ht]

theorem positive_length_le_sum (word : List Nat) (hp : ∀ h ∈ word, 0 < h) :
    word.length ≤ word.sum := by
  induction word with
  | nil => simp
  | cons h tail ih =>
    have hh := hp h (by simp)
    have ht := ih (fun x hx => hp x (List.mem_cons_of_mem h hx))
    simp only [List.length_cons, List.sum_cons]
    omega

theorem two_pow_add_one_le_three_pow (h : Nat) (hp : 0 < h) : 2 ^ h + 1 ≤ 3 ^ h := by
  cases h with
  | zero => omega
  | succ r =>
    induction r with
    | zero => decide
    | succ r ih =>
      simp only [Nat.pow_succ] at ih ⊢
      omega

/-- A coarse numerator bound depending only on the total halving count. -/
theorem weight_lt_three_pow_sum (word : List Nat) (hp : ∀ h ∈ word, 0 < h) :
    weight word < 3 ^ word.sum := by
  induction word with
  | nil => simp [weight]
  | cons h tail ih =>
    have hh := hp h (by simp)
    have ht : ∀ x ∈ tail, 0 < x := fun x hx => hp x (List.mem_cons_of_mem h hx)
    have hw := ih ht
    have hlen := Nat.pow_le_pow_right (show 0 < 3 by decide)
      (positive_length_le_sum tail ht)
    have hpow := two_pow_add_one_le_three_pow h hh
    have hmul := Nat.mul_lt_mul_of_pos_left (k := 2 ^ h) hw
      (Nat.pow_pos (show 0 < 2 by decide))
    have hprod := Nat.mul_le_mul_right (3 ^ tail.sum) hpow
    simp only [weight, List.sum_cons, Nat.pow_add]
    grind

theorem replacement_equal_word (pre post u v : List Nat) (D : Nat)
    (hu : ∀ h ∈ u, 0 < h) (hv : ∀ h ∈ v, 0 < h)
    (hl : u.length = v.length) (hs : u.sum = v.sum)
    (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1)
    (hdu : D ∣ weight (pre ++ u ++ post))
    (hdv : D ∣ weight (pre ++ v ++ post))
    (hbound : (weight u - weight v) + (weight v - weight u) < D) : u = v := by
  exact weight_injective u v hu hv hl hs
    (replacement_equal_weight pre post u v D hl hs h2 h3 hdu hdv hbound)

theorem transfer_divisibility_exclusion (pre post : List Nat) (a b D : Nat)
    (hD : 1 < D) (h2 : Nat.gcd 2 D = 1) (h3 : Nat.gcd 3 D = 1) :
    ¬ (D ∣ weight (leftWord pre post a b) ∧
       D ∣ weight (rightWord pre post a b)) := by
  rintro ⟨hl, hr⟩
  rw [transfer_weight] at hl
  have hm := (Nat.dvd_add_iff_right hr).mpr hl
  have he := divisor_of_monomial D (pre.sum + a) post.length h2 h3 hm
  omega

/-- A divisor of the denominator and the original numerator excludes either
    sign of a monomial perturbation. The original word need not pass the cycle
    test: only this shared factor is required. -/
theorem shared_factor_excludes_monomial_perturbation
    (F D original mutated A B : Nat)
    (hF : 1 < F) (h2 : Nat.gcd 2 F = 1) (h3 : Nat.gcd 3 F = 1)
    (hFD : F ∣ D) (hFW : F ∣ original)
    (hdelta : mutated = original + 2 ^ A * 3 ^ B ∨
      original = mutated + 2 ^ A * 3 ^ B) : ¬ D ∣ mutated := by
  intro hd
  have hmut := Nat.dvd_trans hFD hd
  have hm : F ∣ 2 ^ A * 3 ^ B := by
    rcases hdelta with hl | hr
    · rw [hl] at hmut
      exact (Nat.dvd_add_iff_right hFW).mpr hmut
    · rw [hr] at hFW
      exact (Nat.dvd_add_iff_right hmut).mpr hFW
  have he := divisor_of_monomial F A B h2 h3 hm
  omega

theorem transfer_left_excluded_by_shared_factor (pre post : List Nat) (a b F : Nat)
    (hF : 1 < F) (h2 : Nat.gcd 2 F = 1) (h3 : Nat.gcd 3 F = 1)
    (hFD : F ∣ denominator (rightWord pre post a b))
    (hFW : F ∣ weight (rightWord pre post a b)) :
    ¬ denominator (leftWord pre post a b) ∣ weight (leftWord pre post a b) := by
  rw [transfer_denominator]
  exact shared_factor_excludes_monomial_perturbation F _ _ _ _ _
    hF h2 h3 hFD hFW (Or.inl (transfer_weight pre post a b))

theorem transfer_right_excluded_by_shared_factor (pre post : List Nat) (a b F : Nat)
    (hF : 1 < F) (h2 : Nat.gcd 2 F = 1) (h3 : Nat.gcd 3 F = 1)
    (hFD : F ∣ denominator (leftWord pre post a b))
    (hFW : F ∣ weight (leftWord pre post a b)) :
    ¬ denominator (rightWord pre post a b) ∣ weight (rightWord pre post a b) := by
  rw [← transfer_denominator]
  exact shared_factor_excludes_monomial_perturbation F _ _ _ _ _
    hF h2 h3 hFD hFW (Or.inr (transfer_weight pre post a b))

theorem denominator_coprime_two (word : List Nat)
    (hs : 0 < word.sum) (hD : 0 < denominator word) :
    Nat.gcd 2 (denominator word) = 1 := by
  have hle : 3 ^ word.length ≤ 2 ^ word.sum := by
    unfold denominator at hD
    omega
  have hd : 2 ∣ 2 ^ word.sum := by
    have h := Nat.pow_dvd_pow 2 (show 1 ≤ word.sum by omega)
    simpa using h
  unfold denominator
  rw [Nat.gcd_sub_left_right_of_dvd 2 hle hd]
  exact Nat.gcd_pow_right_of_gcd_eq_one (by decide)

theorem denominator_coprime_three (word : List Nat)
    (hl : 0 < word.length) (hD : 0 < denominator word) :
    Nat.gcd 3 (denominator word) = 1 := by
  have hle : 3 ^ word.length ≤ 2 ^ word.sum := by
    unfold denominator at hD
    omega
  have hd : 3 ∣ 3 ^ word.length := by
    have h := Nat.pow_dvd_pow 3 (show 1 ≤ word.length by omega)
    simpa using h
  unfold denominator
  rw [Nat.gcd_sub_right_right_of_dvd 3 hle hd]
  exact Nat.gcd_pow_right_of_gcd_eq_one (by decide)

/-- Full-word exclusion at the words' common actual denominator. -/
theorem transfer_cycle_test_exclusion (pre post : List Nat) (a b : Nat)
    (hD : 1 < denominator (leftWord pre post a b)) :
    ¬ (denominator (leftWord pre post a b) ∣
         weight (leftWord pre post a b) ∧
       denominator (rightWord pre post a b) ∣
         weight (rightWord pre post a b)) := by
  have hs : 0 < (leftWord pre post a b).sum := by
    simp only [leftWord, List.sum_append, List.sum_cons, List.sum_nil]
    omega
  have hl : 0 < (leftWord pre post a b).length := by
    simp only [leftWord, List.length_append, List.length_cons, List.length_nil]
    omega
  have hpos : 0 < denominator (leftWord pre post a b) := by omega
  have he := transfer_divisibility_exclusion pre post a b
    (denominator (leftWord pre post a b)) hD
    (denominator_coprime_two _ hs hpos) (denominator_coprime_three _ hl hpos)
  rwa [transfer_denominator] at he ⊢

/-- The geometric factor shared by the numerator and denominator of a
    repeated block. This recurrence equals the usual finite geometric sum. -/
def geometric (A B : Nat) : Nat → Nat
  | 0 => 0
  | g + 1 => B ^ g + A * geometric A B g

theorem geometric_other_step (A B g : Nat) :
    geometric A B (g + 1) = A ^ g + B * geometric A B g := by
  induction g with
  | zero => simp [geometric]
  | succ g ih =>
    simp only [geometric] at ih ⊢
    simp only [Nat.pow_succ]
    grind

theorem geometric_balance (A B g : Nat) :
    A ^ g + B * geometric A B g = B ^ g + A * geometric A B g := by
  rw [← geometric_other_step, geometric]

theorem geometric_divides_difference (A B g : Nat) :
    geometric A B g ∣ A ^ g - B ^ g := by
  have he := geometric_balance A B g
  have hs : A ^ g - B ^ g = A * geometric A B g - B * geometric A B g := by
    omega
  rw [hs]
  exact Nat.dvd_sub (Nat.dvd_mul_left _ _) (Nat.dvd_mul_left _ _)

def repeatWord (block : List Nat) : Nat → List Nat
  | 0 => []
  | g + 1 => block ++ repeatWord block g

theorem repeatWord_length (block : List Nat) (g : Nat) :
    (repeatWord block g).length = block.length * g := by
  induction g with
  | zero => simp [repeatWord]
  | succ g ih => simp [repeatWord, ih, Nat.mul_succ, Nat.add_comm]

theorem repeatWord_sum (block : List Nat) (g : Nat) :
    (repeatWord block g).sum = block.sum * g := by
  induction g with
  | zero => simp [repeatWord]
  | succ g ih => simp [repeatWord, List.sum_append, ih, Nat.mul_succ, Nat.add_comm]

theorem repeatWord_weight (block : List Nat) (g : Nat) :
    weight (repeatWord block g) = geometric (2 ^ block.sum) (3 ^ block.length) g *
      weight block := by
  induction g with
  | zero => simp [repeatWord, weight, geometric]
  | succ g ih =>
    rw [repeatWord, weight_append, repeatWord_length, ih, Nat.pow_mul, geometric]
    grind

theorem repeatWord_denominator_divisible (block : List Nat) (g : Nat) :
    geometric (2 ^ block.sum) (3 ^ block.length) g ∣ denominator (repeatWord block g) := by
  simp only [denominator, repeatWord_length, repeatWord_sum, Nat.pow_mul]
  exact geometric_divides_difference _ _ _

theorem repeatWord_weight_divisible (block : List Nat) (g : Nat) :
    geometric (2 ^ block.sum) (3 ^ block.length) g ∣ weight (repeatWord block g) := by
  rw [repeatWord_weight]
  exact Nat.dvd_mul_right _ _

theorem repeatFactor_coprime_two (block : List Nat) (g : Nat)
    (hs : 0 < block.sum) (hg : 0 < g) :
    Nat.gcd 2 (geometric (2 ^ block.sum) (3 ^ block.length) g) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 1 := ⟨g - 1, by omega⟩
  have hd : 2 ∣ 2 ^ block.sum := by
    have h := Nat.pow_dvd_pow 2 (show 1 ≤ block.sum by omega)
    simpa using h
  rw [geometric, Nat.gcd_add_right_right_of_dvd ((3 ^ block.length) ^ r)
    (Nat.dvd_mul_right_of_dvd hd _)]
  exact Nat.gcd_pow_right_of_gcd_eq_one
    (Nat.gcd_pow_right_of_gcd_eq_one (by decide))

theorem repeatFactor_coprime_three (block : List Nat) (g : Nat)
    (hl : 0 < block.length) (hg : 0 < g) :
    Nat.gcd 3 (geometric (2 ^ block.sum) (3 ^ block.length) g) = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 1 := ⟨g - 1, by omega⟩
  have hd : 3 ∣ 3 ^ block.length := by
    have h := Nat.pow_dvd_pow 3 (show 1 ≤ block.length by omega)
    simpa using h
  rw [geometric_other_step, Nat.gcd_add_right_right_of_dvd ((2 ^ block.sum) ^ r)
    (Nat.dvd_mul_right_of_dvd hd _)]
  exact Nat.gcd_pow_right_of_gcd_eq_one
    (Nat.gcd_pow_right_of_gcd_eq_one (by decide))

theorem repeatFactor_gt_one (block : List Nat) (g : Nat)
    (hl : 0 < block.length) (hg : 1 < g) :
    1 < geometric (2 ^ block.sum) (3 ^ block.length) g := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 2 := ⟨g - 2, by omega⟩
  have hb : 1 < 3 ^ block.length := by
    obtain ⟨s, hlen⟩ : ∃ s, block.length = s + 1 := ⟨block.length - 1, by omega⟩
    rw [hlen, Nat.pow_succ]
    have hp : 0 < 3 ^ s := Nat.pow_pos (by decide)
    omega
  have hp : 0 < (3 ^ block.length) ^ r := Nat.pow_pos (by omega)
  rw [show r + 2 = (r + 1) + 1 by omega, geometric, Nat.pow_succ]
  have hm : 3 ^ block.length ≤ (3 ^ block.length) ^ r * 3 ^ block.length := by
    exact Nat.le_mul_of_pos_left _ hp
  omega

theorem repeatFactor_gt_power (block : List Nat) (g : Nat) (hg : 0 < g) :
    (2 ^ block.sum) ^ g < geometric (2 ^ block.sum) (3 ^ block.length) (g + 1) := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 1 := ⟨g - 1, by omega⟩
  have hA : 0 < 2 ^ block.sum := Nat.pow_pos (by decide)
  have hB : 0 < 3 ^ block.length := Nat.pow_pos (by decide)
  have hG : 0 < geometric (2 ^ block.sum) (3 ^ block.length) (r + 1) := by
    rw [geometric]
    have hp : 0 < (3 ^ block.length) ^ r := Nat.pow_pos hB
    omega
  rw [geometric_other_step]
  have hm := Nat.mul_pos hB hG
  omega

theorem repeatFactor_gt_local_bound (block : List Nat) (g : Nat) (hg : 2 < g) :
    3 ^ block.sum < geometric (2 ^ block.sum) (3 ^ block.length) g := by
  obtain ⟨r, rfl⟩ : ∃ r, g = r + 3 := ⟨g - 3, by omega⟩
  have hpow := Nat.pow_le_pow_right (Nat.pow_pos (show 0 < 2 by decide))
    (show 2 ≤ r + 2 by omega) (n := 2 ^ block.sum)
  have hbase : 3 ^ block.sum ≤ (2 ^ block.sum) ^ 2 := by
    have h := Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by decide) block.sum
    simpa only [← Nat.pow_mul, Nat.mul_comm] using h
  have hbig := repeatFactor_gt_power block (r + 2) (by omega)
  simp only [Nat.add_assoc] at hbig
  exact Nat.lt_of_le_of_lt (Nat.le_trans hbase hpow) hbig

/-- Every genuine repeated block has a nontrivial common factor coprime to
    6, whether or not that repeated block itself realizes an integer cycle. -/
theorem repeatWord_shared_factor (block : List Nat) (g : Nat)
    (hs : 0 < block.sum) (hl : 0 < block.length) (hg : 1 < g) :
    ∃ F, 1 < F ∧ Nat.gcd 2 F = 1 ∧ Nat.gcd 3 F = 1 ∧
      F ∣ denominator (repeatWord block g) ∧ F ∣ weight (repeatWord block g) := by
  refine ⟨geometric (2 ^ block.sum) (3 ^ block.length) g,
    repeatFactor_gt_one block g hl hg,
    repeatFactor_coprime_two block g hs (by omega),
    repeatFactor_coprime_three block g hl (by omega),
    repeatWord_denominator_divisible block g, repeatWord_weight_divisible block g⟩

/-- A single adjacent one-halving transfer away from an arbitrary repeated
    block fails the integer cycle divisibility test, in either direction. -/
theorem repeated_block_transfer_exclusion (block pre post : List Nat) (a b g : Nat)
    (hs : 0 < block.sum) (hl : 0 < block.length) (hg : 1 < g) :
    (rightWord pre post a b = repeatWord block g →
      ¬ denominator (leftWord pre post a b) ∣ weight (leftWord pre post a b)) ∧
    (leftWord pre post a b = repeatWord block g →
      ¬ denominator (rightWord pre post a b) ∣ weight (rightWord pre post a b)) := by
  obtain ⟨F, hF, h2, h3, hFD, hFW⟩ := repeatWord_shared_factor block g hs hl hg
  constructor
  · intro he
    exact transfer_left_excluded_by_shared_factor pre post a b F hF h2 h3
      (he ▸ hFD) (he ▸ hFW)
  · intro he
    exact transfer_right_excluded_by_shared_factor pre post a b F hF h2 h3
      (he ▸ hFD) (he ▸ hFW)

/-- In at least three repeats of a positive block, replacing one occurrence
    by any different positive block with the same length and sum fails the
    cycle divisibility test. The original repeated word need not be a cycle. -/
theorem repeated_block_replacement_exclusion
    (block replacement pre post : List Nat) (g : Nat)
    (hb : ∀ h ∈ block, 0 < h) (hr : ∀ h ∈ replacement, 0 < h)
    (hne : block ≠ []) (hg : 2 < g)
    (hl : replacement.length = block.length) (hs : replacement.sum = block.sum)
    (hdiff : replacement ≠ block)
    (hcontext : pre ++ block ++ post = repeatWord block g) :
    ¬ denominator (pre ++ replacement ++ post) ∣ weight (pre ++ replacement ++ post) := by
  intro hd
  have hlen : 0 < block.length := by
    cases block with
    | nil => contradiction
    | cons h tail => simp
  have hsum : 0 < block.sum := by
    have ht := positive_length_le_sum block hb
    omega
  let F := geometric (2 ^ block.sum) (3 ^ block.length) g
  have hden : denominator (pre ++ replacement ++ post) =
      denominator (repeatWord block g) := by
    rw [← hcontext]
    simp only [denominator, List.sum_append, List.length_append, hl, hs]
  rw [hden] at hd
  have hfr : F ∣ weight (pre ++ replacement ++ post) :=
    Nat.dvd_trans (repeatWord_denominator_divisible block g) hd
  have hfb : F ∣ weight (pre ++ block ++ post) := by
    rw [hcontext]
    exact repeatWord_weight_divisible block g
  have hbound : (weight block - weight replacement) +
      (weight replacement - weight block) < F := by
    have hbw := weight_lt_three_pow_sum block hb
    have hrw := weight_lt_three_pow_sum replacement hr
    rw [hs] at hrw
    have hgf := repeatFactor_gt_local_bound block g hg
    change 3 ^ block.sum < F at hgf
    omega
  have heq := replacement_equal_word pre post block replacement F hb hr hl.symm hs.symm
    (repeatFactor_coprime_two block g hsum (by omega))
    (repeatFactor_coprime_three block g hlen (by omega)) hfb hfr hbound
  exact hdiff heq.symm

#print axioms transfer_weight
#print axioms replacement_difference
#print axioms replacement_divides_distance
#print axioms replacement_equal_weight
#print axioms weight_injective
#print axioms replacement_equal_word
#print axioms divisor_of_monomial
#print axioms shared_factor_excludes_monomial_perturbation
#print axioms transfer_left_excluded_by_shared_factor
#print axioms transfer_right_excluded_by_shared_factor
#print axioms transfer_cycle_test_exclusion
#print axioms repeatWord_shared_factor
#print axioms repeated_block_transfer_exclusion
#print axioms weight_lt_three_pow_sum
#print axioms repeated_block_replacement_exclusion

end CollatzCycleSeparation
