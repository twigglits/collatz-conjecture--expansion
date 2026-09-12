/-
  From ordered cyclic numerators to actual positive odd Collatz cycles.
  Standalone Lean 4; no Mathlib, admitted proofs, or native evaluation.
  Check: lean CollatzCycleCriterion.lean
-/
namespace CollatzCycleCriterion

def oddPart (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

def v2 (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then v2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

def F (n : Nat) : Nat := oddPart (3 * n + 1)

def iterate : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => F (iterate k n)

/-- Factoring a power of two times an odd integer gives the exact exponent. -/
theorem odd_factor_exact (h y : Nat) (hy : y % 2 = 1) :
    oddPart (2 ^ h * y) = y ∧ v2 (2 ^ h * y) = h := by
  induction h with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul]
    rw [oddPart.eq_def, dif_neg (by omega), v2.eq_def, dif_neg (by omega)]
    exact ⟨rfl, rfl⟩
  | succ h ih =>
    have hp : 0 < 2 ^ h * y := Nat.mul_pos (Nat.pow_pos (by decide)) (by omega)
    have he : 2 ^ (h + 1) * y = 2 * (2 ^ h * y) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [he, oddPart.eq_def, dif_pos (by omega), v2.eq_def, dif_pos (by omega)]
    simpa using ih

/-- An odd terminal factor turns a prescribed step equation into the actual map. -/
theorem actual_step (h x y : Nat) (hy : y % 2 = 1)
    (he : 2 ^ h * y = 3 * x + 1) : F x = y ∧ v2 (3 * x + 1) = h := by
  unfold F
  rw [← he]
  exact odd_factor_exact h y hy

/-- Coprimality with two permits divisibility to propagate to the next rotation. -/
theorem rotate_divisibility (D h A B : Nat) (hg : Nat.gcd 2 D = 1)
    (ha : D ∣ A) (he : 2 ^ h * B = 3 * A + D) : D ∣ B := by
  have hright : D ∣ 3 * A + D := Nat.dvd_add (Nat.dvd_mul_left_of_dvd ha 3) (Nat.dvd_refl D)
  rw [← he] at hright
  have hcancel := Nat.dvd_gcd_mul_iff_dvd_mul.mpr hright
  rw [Nat.gcd_comm D (2 ^ h), Nat.gcd_pow_left_of_gcd_eq_one hg, Nat.one_mul] at hcancel
  exact hcancel

/-- An integral quotient of an odd numerator is again odd and positive. -/
theorem odd_quotient (D W : Nat) (hd : D ∣ W) (hw : W % 2 = 1) :
    (W / D) % 2 = 1 ∧ 0 < W / D := by
  have he : D * (W / D) = W := Nat.mul_div_cancel' hd
  have hm := congrArg (fun n => n % 2) he
  rw [Nat.mul_mod, hw] at hm
  have hn : (W / D) % 2 ≠ 0 := by
    intro hz
    simp only [hz, Nat.mul_zero, Nat.zero_mod] at hm
    contradiction
  have ho : (W / D) % 2 = 1 := by omega
  refine ⟨ho, Nat.pos_of_ne_zero ?_⟩
  intro hz
  rw [hz] at ho
  contradiction

theorem quotient_step (D h A B : Nat) (hD : 0 < D)
    (ha : D ∣ A) (hb : D ∣ B) (he : 2 ^ h * B = 3 * A + D) :
    2 ^ h * (B / D) = 3 * (A / D) + 1 := by
  have hea : D * (A / D) = A := Nat.mul_div_cancel' ha
  have heb : D * (B / D) = B := Nat.mul_div_cancel' hb
  apply Nat.eq_of_mul_eq_mul_left hD
  calc
    D * (2 ^ h * (B / D)) = 2 ^ h * B := by
      rw [Nat.mul_left_comm D, heb]
    _ = 3 * A + D := he
    _ = D * (3 * (A / D) + 1) := by
      rw [Nat.mul_add, Nat.mul_left_comm D, hea, Nat.mul_one]

/-- The complete bridge for any finite cyclic numerator sequence. The oddness
    and rotation equations are explicit premises, not facts inferred from a
    supplied label or an unchecked list of purported cycle members. -/
theorem cyclic_numerators_realize (k D : Nat) (h W : Nat → Nat)
    (hk : 0 < k) (hD : 0 < D) (hg : Nat.gcd 2 D = 1)
    (hodd : ∀ i, i ≤ k → W i % 2 = 1)
    (hrot : ∀ i, i < k → 2 ^ h i * W (i + 1) = 3 * W i + D)
    (hclose : W k = W 0) (hdiv : D ∣ W 0) :
    0 < W 0 / D ∧ (W 0 / D) % 2 = 1 ∧
    iterate k (W 0 / D) = W 0 / D ∧
    (∀ i, i ≤ k → iterate i (W 0 / D) = W i / D) ∧
    (∀ i, i < k → v2 (3 * iterate i (W 0 / D) + 1) = h i) := by
  have hall : ∀ i, i ≤ k → D ∣ W i := by
    intro i
    induction i with
    | zero => intro _; exact hdiv
    | succ i ih =>
      intro hi
      exact rotate_divisibility D (h i) (W i) (W (i + 1)) hg
        (ih (by omega)) (hrot i (by omega))
  have hq : ∀ i, i ≤ k → (W i / D) % 2 = 1 ∧ 0 < W i / D := by
    intro i hi
    exact odd_quotient D (W i) (hall i hi) (hodd i hi)
  have hs : ∀ i, i < k →
      F (W i / D) = W (i + 1) / D ∧ v2 (3 * (W i / D) + 1) = h i := by
    intro i hi
    exact actual_step (h i) (W i / D) (W (i + 1) / D)
      (hq (i + 1) (by omega)).1
      (quotient_step D (h i) (W i) (W (i + 1)) hD
        (hall i (by omega)) (hall (i + 1) (by omega)) (hrot i hi))
  have hit : ∀ i, i ≤ k → iterate i (W 0 / D) = W i / D := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [iterate, ih (by omega)]
      exact (hs i (by omega)).1
  refine ⟨(hq 0 (by omega)).2, (hq 0 (by omega)).1, ?_, hit, ?_⟩
  · rw [hit k (by omega), hclose]
  · intro i hi
    rw [hit i (by omega)]
    exact (hs i hi).2

def weight : List Nat → Nat
  | [] => 0
  | h :: tail => 3 ^ tail.length + 2 ^ h * weight tail

def denominator (word : List Nat) : Nat := 2 ^ word.sum - 3 ^ word.length

def rotateOnce : List Nat → List Nat
  | [] => []
  | h :: tail => tail ++ [h]

def rotate (word : List Nat) : Nat → List Nat
  | 0 => word
  | i + 1 => rotateOnce (rotate word i)

theorem rotate_succ_head (word : List Nat) (i : Nat) :
    rotate word (i + 1) = rotate (rotateOnce word) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change rotateOnce (rotate word (i + 1)) = rotateOnce (rotate (rotateOnce word) i)
    rw [ih]

theorem rotate_prefix (a b : List Nat) : rotate (a ++ b) a.length = b ++ a := by
  induction a generalizing b with
  | nil => simp [rotate]
  | cons h a ih =>
    simp only [List.cons_append, List.length_cons, rotate_succ_head, rotateOnce]
    rw [List.append_assoc, ih]
    simp only [List.append_assoc, List.singleton_append]

theorem rotate_full (word : List Nat) : rotate word word.length = word := by
  simpa using rotate_prefix word []

theorem rotate_split (word : List Nat) (i : Nat) (hi : i ≤ word.length) :
    rotate word i = word.drop i ++ word.take i := by
  have he := rotate_prefix (word.take i) (word.drop i)
  simpa [List.take_append_drop, List.length_take, Nat.min_eq_left hi] using he

theorem rotate_head (word : List Nat) (i : Nat) (hi : i < word.length) :
    (rotate word i).headD 0 = word[i] := by
  rw [rotate_split word i (by omega), List.drop_eq_getElem_cons hi]
  rfl

theorem rotate_length (word : List Nat) (i : Nat) : (rotate word i).length = word.length := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [rotate]
    have he : ∀ w : List Nat, (rotateOnce w).length = w.length := by
      intro w
      cases w <;> simp [rotateOnce]
    rw [he, ih]

theorem rotate_sum (word : List Nat) (i : Nat) : (rotate word i).sum = word.sum := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [rotate]
    have he : ∀ w : List Nat, (rotateOnce w).sum = w.sum := by
      intro w
      cases w <;> simp [rotateOnce, List.sum_append, Nat.add_comm]
    rw [he, ih]

theorem rotate_positive (word : List Nat) (i : Nat)
    (hp : ∀ h ∈ word, 0 < h) : ∀ h ∈ rotate word i, 0 < h := by
  induction i with
  | zero => exact hp
  | succ i ih =>
    rw [rotate]
    cases he : rotate word i with
    | nil => simp [rotateOnce]
    | cons h tail =>
      simp only [he, List.mem_cons] at ih
      simpa [rotateOnce, List.mem_append, List.mem_singleton, or_comm] using ih

theorem weight_append (a b : List Nat) :
    weight (a ++ b) = 3 ^ b.length * weight a + 2 ^ a.sum * weight b := by
  induction a with
  | nil => simp [weight]
  | cons h a ih =>
    simp only [List.cons_append, weight, List.length_append, List.sum_cons,
      Nat.pow_add, ih]
    grind

theorem weight_pos (word : List Nat) (hne : word ≠ []) : 0 < weight word := by
  cases word with
  | nil => contradiction
  | cons h tail =>
    have hp : 0 < 3 ^ tail.length := Nat.pow_pos (by decide)
    simp only [weight]
    omega

theorem pow_two_even (h : Nat) (hp : 0 < h) : (2 ^ h) % 2 = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, h = r + 1 := ⟨h - 1, by omega⟩
  rw [Nat.pow_succ, Nat.mul_mod]
  simp

theorem weight_odd (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h) : weight word % 2 = 1 := by
  cases word with
  | nil => contradiction
  | cons h tail =>
    have hh : 0 < h := hp h (by simp)
    have h3 : (3 ^ tail.length) % 2 = 1 := by simp [Nat.pow_mod]
    rw [weight, Nat.add_mod, Nat.mul_mod, pow_two_even h hh, h3]
    simp

theorem denominator_add (word : List Nat) (hD : 0 < denominator word) :
    denominator word + 3 ^ word.length = 2 ^ word.sum := by
  unfold denominator at *
  omega

theorem denominator_coprime_two (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h) (hD : 0 < denominator word) :
    Nat.gcd 2 (denominator word) = 1 := by
  have hsum : 0 < word.sum := by
    cases word with
    | nil => contradiction
    | cons h tail =>
      have hh := hp h (by simp)
      simp only [List.sum_cons]
      omega
  have h2 := pow_two_even word.sum hsum
  have h3 : (3 ^ word.length) % 2 = 1 := by simp [Nat.pow_mod]
  have hadd := denominator_add word hD
  have hodd : denominator word % 2 = 1 := by omega
  rw [Nat.gcd_rec, hodd]
  decide

/-- Rotation identity before subtraction, valid without a sign assumption. -/
theorem rotation_balance (word : List Nat) (hne : word ≠ []) :
    2 ^ word.headD 0 * weight (rotateOnce word) + 3 ^ word.length =
      3 * weight word + 2 ^ word.sum := by
  cases word with
  | nil => contradiction
  | cons h tail =>
    simp [rotateOnce, weight_append, weight, Nat.pow_succ, Nat.pow_add,
      Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_assoc, Nat.add_comm]

theorem rotation_identity (word : List Nat) (hne : word ≠ [])
    (hD : 0 < denominator word) :
    2 ^ word.headD 0 * weight (rotateOnce word) = 3 * weight word + denominator word := by
  have hr := rotation_balance word hne
  have hd := denominator_add word hD
  omega

/-- A genuine accelerated cycle, with the exponent at each position equal to
    the corresponding symbol of the supplied ordered word. Primitivity is
    deliberately not required. -/
def RealizesWord (word : List Nat) (n : Nat) : Prop :=
  0 < n ∧ n % 2 = 1 ∧ iterate word.length n = n ∧
    ∀ i (hi : i < word.length), v2 (3 * iterate i n + 1) = word[i]

/-- Divisibility and a positive denominator suffice for an actual integer
    cycle, with every intermediate integrality and parity fact discharged. -/
theorem word_sufficiency (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h)
    (hD : 0 < denominator word) (hdiv : denominator word ∣ weight word) :
    RealizesWord word (weight word / denominator word) := by
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
  have hrot : ∀ i, i < word.length →
      2 ^ (rotate word i).headD 0 * weight (rotate word (i + 1)) =
        3 * weight (rotate word i) + denominator word := by
    intro i _
    have he := rotation_identity (rotate word i) (hnr i) (by rw [hdr]; exact hD)
    simpa only [rotate, hdr] using he
  have hall := cyclic_numerators_realize word.length (denominator word)
    (fun i => (rotate word i).headD 0) (fun i => weight (rotate word i)) hk hD
    (denominator_coprime_two word hne hp hD)
    (fun i _ => weight_odd (rotate word i) (hnr i) (rotate_positive word i hp))
    hrot (by rw [rotate_full, rotate]) (by simpa only [rotate] using hdiv)
  simp only [rotate] at hall
  refine ⟨hall.1, hall.2.1, hall.2.2.1, ?_⟩
  intro i hi
  have he := hall.2.2.2.2 i hi
  rw [rotate_head word i hi] at he
  exact he

/-- Fundamental factorization for the actual odd-part and valuation functions. -/
theorem actual_factorization (n : Nat) (hn : 0 < n) :
    2 ^ v2 n * oddPart n = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hp : n % 2 = 0
    · have hne : n ≠ 0 := by omega
      have hsmall : n / 2 < n := by omega
      have hpos : 0 < n / 2 := by omega
      have htail := ih (n / 2) hsmall hpos
      rw [oddPart.eq_def, dif_pos ⟨hp, hne⟩, v2.eq_def, dif_pos ⟨hp, hne⟩]
      rw [Nat.pow_succ]
      calc
        2 ^ v2 (n / 2) * 2 * oddPart (n / 2) =
            2 * (2 ^ v2 (n / 2) * oddPart (n / 2)) := by ac_rfl
        _ = 2 * (n / 2) := by rw [htail]
        _ = n := by omega
    · rw [oddPart.eq_def, dif_neg (by omega), v2.eq_def, dif_neg (by omega)]
      simp

/-- Affine composition for any finite sequence satisfying the prescribed
    step equations; no integrality of a hypothetical rational orbit is assumed. -/
theorem word_equation (word : List Nat) (x : Nat → Nat)
    (hs : ∀ i (hi : i < word.length), 2 ^ word[i] * x (i + 1) = 3 * x i + 1) :
    2 ^ word.sum * x word.length = 3 ^ word.length * x 0 + weight word := by
  induction word generalizing x with
  | nil => simp [weight]
  | cons h tail ih =>
    have hh : 2 ^ h * x 1 = 3 * x 0 + 1 := hs 0 (by simp)
    have ht : ∀ i (hi : i < tail.length),
        2 ^ tail[i] * x ((i + 1) + 1) = 3 * x (i + 1) + 1 := by
      intro i hi
      exact hs (i + 1) (by simpa using hi)
    have he := ih (fun i => x (i + 1)) ht
    simp only [List.sum_cons, List.length_cons, weight, Nat.pow_add, Nat.pow_succ]
    calc
      2 ^ h * 2 ^ tail.sum * x (tail.length + 1) =
          2 ^ h * (2 ^ tail.sum * x (tail.length + 1)) := Nat.mul_assoc _ _ _
      _ = 2 ^ h * (3 ^ tail.length * x 1 + weight tail) := by rw [he]
      _ = 3 ^ tail.length * (2 ^ h * x 1) + 2 ^ h * weight tail := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = 3 ^ tail.length * (3 * x 0 + 1) + 2 ^ h * weight tail := by rw [hh]
      _ = 3 ^ tail.length * 3 * x 0 + (3 ^ tail.length + 2 ^ h * weight tail) := by
        simp [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Every actual nonempty cycle has the positive denominator and divisibility
    appearing in the ordered word test. -/
theorem word_necessity (word : List Nat) (hne : word ≠ []) (n : Nat)
    (hc : RealizesWord word n) :
    0 < denominator word ∧ denominator word ∣ weight word := by
  have hs : ∀ i (hi : i < word.length),
      2 ^ word[i] * iterate (i + 1) n = 3 * iterate i n + 1 := by
    intro i hi
    have he := actual_factorization (3 * iterate i n + 1) (by omega)
    rw [hc.2.2.2 i hi] at he
    exact he
  have he := word_equation word (fun i => iterate i n) hs
  rw [hc.2.2.1] at he
  change 2 ^ word.sum * n = 3 ^ word.length * n + weight word at he
  have hW := weight_pos word hne
  have hlt : 3 ^ word.length < 2 ^ word.sum :=
    Nat.lt_of_mul_lt_mul_right (show 3 ^ word.length * n < 2 ^ word.sum * n by omega)
  have hD : 0 < denominator word := by unfold denominator; omega
  have hd : denominator word * n = weight word := by
    unfold denominator
    rw [Nat.sub_mul, he]
    omega
  exact ⟨hD, ⟨n, hd.symm⟩⟩

/-- Complete ordered cycle test for every nonempty positive halving word. -/
theorem word_cycle_iff (word : List Nat) (hne : word ≠ [])
    (hp : ∀ h ∈ word, 0 < h) :
    (∃ n, RealizesWord word n) ↔
      0 < denominator word ∧ denominator word ∣ weight word := by
  constructor
  · rintro ⟨n, hn⟩
    exact word_necessity word hne n hn
  · rintro ⟨hD, hd⟩
    exact ⟨weight word / denominator word, word_sufficiency word hne hp hD hd⟩

#print axioms odd_factor_exact
#print axioms quotient_step
#print axioms cyclic_numerators_realize
#print axioms rotation_balance
#print axioms word_sufficiency
#print axioms word_necessity
#print axioms word_cycle_iff

end CollatzCycleCriterion
