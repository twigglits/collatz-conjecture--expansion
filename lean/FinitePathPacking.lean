/-
  Finite simple trajectories and exact first-entry transport.
  Standalone Lean 4; no Mathlib, native evaluation, or admitted proofs.
  The entropy induction and reciprocal-product estimates remain written.
-/
import FirstPassagePacking

namespace CollatzPacking

/-- All positions through N are distinct; no claim is made about later time. -/
def SimplePrefix (N n : Nat) : Prop :=
  ∀ i, i ≤ N → ∀ j, j ≤ N → orbit i n = orbit j n → i = j

def PrefixValues (N n x : Nat) : Prop :=
  ∃ i, i ≤ N ∧ x = orbit i n

def FirstEntry (H h n : Nat) : Prop :=
  orbit h n ≤ H ∧ ∀ t, t < h → H < orbit t n

theorem first_entry_simple {H h n : Nat} (hf : FirstEntry H h n) :
    SimplePrefix h n := by
  have impossible : ∀ i j, i < j → j ≤ h → orbit i n = orbit j n → False := by
    intro i j hij hj he
    have he' := congrArg (orbit (h - j)) he
    rw [← orbit_add, ← orbit_add, Nat.sub_add_cancel hj] at he'
    have hi : h - j + i < h := by omega
    have ha := hf.2 (h - j + i) hi
    have hb := hf.1
    omega
  intro i hi j hj he
  by_cases hij : i = j
  · exact hij
  · have ho : i < j ∨ j < i := by omega
    rcases ho with ho | ho
    · exact False.elim (impossible i j ho hj he)
    · exact False.elim (impossible j i ho hi he.symm)

theorem prefix_fixed_injective {N n k i j : Nat}
    (hs : SimplePrefix N n) (hi : i + k ≤ N) (hj : j + k ≤ N)
    (he : orbit k (orbit i n) = orbit k (orbit j n)) : i = j := by
  rw [← orbit_add, ← orbit_add] at he
  have h := hs (k + i) (by omega) (k + j) (by omega) he
  omega

theorem prefix_image_mem {N n k i : Nat} (hi : i + k ≤ N) :
    PrefixValues N n (orbit k (orbit i n)) := by
  exact ⟨k + i, by omega, (orbit_add k i n).symm⟩

/-- At most k selected positions lack the k-step continuation in this prefix. -/
theorem terminal_positions_bound (N k : Nat) (times : List Nat)
    (hd : times.Nodup)
    (ht : ∀ t ∈ times, t ≤ N ∧ N < t + k) : times.length ≤ k := by
  apply finite_image_packing times (fun t => N - t) k hd
  · intro i hi j hj he
    have h1 := ht i hi
    have h2 := ht j hj
    omega
  · intro i hi
    have h := ht i hi
    omega

/-- The same local packing transfer works on a finite path after deleting
    its final k positions. Only the image-length bound is assumed. -/
theorem finite_prefix_local_packing (N n k q j M : Nat) (times : List Nat)
    (hs : SimplePrefix N n) (hd : times.Nodup)
    (ht : ∀ t ∈ times, t + k ≤ N)
    (hpack : ∀ a (ys : List Nat), ys.Nodup →
      (∀ y ∈ ys, PrefixValues N n y ∧ a ≤ y ∧ y < a + 3 ^ j) →
      ys.length ≤ M)
    (hblock : ∀ t ∈ times,
      2 ^ k * q ≤ orbit t n ∧ orbit t n < 2 ^ k * q + 2 ^ k)
    (hweight : ∀ t ∈ times, wt k (orbit t n - 2 ^ k * q) = j) :
    times.length ≤ M := by
  let f := fun t => orbit k (orbit t n)
  have hm : (times.map f).Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp_of_mem
      (fun hi hj hne he => hne (prefix_fixed_injective hs (ht _ hi) (ht _ hj) he)) hd
  have hb : ∀ y ∈ times.map f,
      PrefixValues N n y ∧ 3 ^ j * q ≤ y ∧ y < 3 ^ j * q + 3 ^ j := by
    intro y hy
    obtain ⟨t, ht', rfl⟩ := List.mem_map.mp hy
    exact ⟨prefix_image_mem (ht t ht'),
      fixed_weight_image_interval k q j (orbit t n) (hblock t ht') (hweight t ht')⟩
  simpa only [List.length_map] using hpack (3 ^ j * q) (times.map f) hm hb

theorem orbit_succ_right (t n : Nat) : orbit (t + 1) n = U (orbit t n) := by
  have h := orbit_add 1 t n
  simpa only [Nat.add_comm 1 t, orbit] using h

theorem entry_step_even {H x y : Nat} (ha : H < x) (hb : y ≤ H)
    (hu : y = U x) : x % 2 = 0 ∧ x = 2 * y ∧ H < 2 * y := by
  have hp : x % 2 = 0 := by
    by_cases ho : x % 2 = 1
    · simp only [U, if_pos ho] at hu
      omega
    · omega
  simp only [U, hp, Nat.zero_ne_one, if_false] at hu
  exact ⟨hp, by omega, by omega⟩

/-- The first step into a floor from above is even, and lands above H/2. -/
theorem first_entry_landing {H h n : Nat} (hh : 0 < h)
    (hf : FirstEntry H h n) :
    ∃ t, h = t + 1 ∧ (orbit t n) % 2 = 0 ∧
      orbit t n = 2 * orbit h n ∧ H < 2 * orbit h n := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : h ≠ 0)
  have hb := hf.1
  have ha := hf.2 t (by omega)
  exact ⟨t, rfl, entry_step_even ha hb (orbit_succ_right t n)⟩

/-- Integer form of the unique odd count in a dyadic source shell when
    the reverse product is at least 2/3. A is the common value 2^h*y. -/
theorem shell_weight_unique (X A n m j k : Nat)
    (hn : X ≤ n ∧ n < 2 * X) (hm : X ≤ m ∧ m < 2 * X)
    (hnlo : 2 * A ≤ 3 * (3 ^ j * n)) (hnhi : 3 ^ j * n ≤ A)
    (hmlo : 2 * A ≤ 3 * (3 ^ k * m)) (hmhi : 3 ^ k * m ≤ A) :
    j = k := by
  have impossible : ∀ u v a b, u < v →
      X ≤ a → b < 2 * X →
      3 ^ v * a ≤ A → 2 * A ≤ 3 * (3 ^ u * b) → False := by
    intro u v a b huv ha hb hahi hblo
    have hp : 3 * 3 ^ u ≤ 3 ^ v := by
      have h := Nat.pow_le_pow_right (by decide : 0 < 3) (show u + 1 ≤ v by omega)
      simpa only [Nat.pow_succ, Nat.mul_comm] using h
    have hmul := Nat.mul_le_mul_right a hp
    have hbound : (3 * 3 ^ u) * (2 * a) ≤ (3 * 3 ^ u) * b := by
      calc
        (3 * 3 ^ u) * (2 * a) = 2 * ((3 * 3 ^ u) * a) := by ac_rfl
        _ ≤ 2 * A := Nat.mul_le_mul_left 2 (Nat.le_trans hmul hahi)
        _ ≤ 3 * (3 ^ u * b) := hblo
        _ = (3 * 3 ^ u) * b := by ac_rfl
    have hpos : 0 < 3 * 3 ^ u := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    have hab : 2 * a ≤ b := Nat.le_of_mul_le_mul_left hbound hpos
    omega
  by_cases he : j = k
  · exact he
  · have ho : j < k ∨ k < j := by omega
    rcases ho with ho | ho
    · exact False.elim (impossible j k m n ho hm.1 hn.2 hmhi hnlo)
    · exact False.elim (impossible k j n m ho hn.1 hm.2 hnhi hmlo)

/-- Supports the written reciprocal bound with exponent 1/20. -/
theorem reciprocal_constant : (32 : Nat) ^ 20 < 2 * 31 ^ 20 := by decide

#print axioms first_entry_simple
#print axioms prefix_fixed_injective
#print axioms prefix_image_mem
#print axioms terminal_positions_bound
#print axioms finite_prefix_local_packing
#print axioms first_entry_landing
#print axioms shell_weight_unique
#print axioms reciprocal_constant

end CollatzPacking
