/-
  Finite ingredients of the orbit-packing argument in APERIODIC-ATTEMPT.md.
  Standalone Lean 4: no Mathlib, admitted proofs, or native evaluation.
  U/orbit/wt are the ordinary Collatz shortcut definitions used in CollatzAffine.
  This file does not prove reciprocal summability or the Collatz conjecture.
  Check: lean CollatzPacking.lean
-/
namespace CollatzPacking

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

def orbit : Nat → Nat → Nat
  | 0, n => n
  | k + 1, n => orbit k (U n)

def wt : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => n % 2 + wt k (U n)

/-- Exact residue-class formula; the same identity as CollatzFrontier.U_affine. -/
theorem affine : ∀ (k q s : Nat),
    orbit k (2 ^ k * q + s) = 3 ^ wt k s * q + orbit k s
  | 0, _, _ => rfl
  | k + 1, q, s => by
    have hsplit : 2 ^ (k + 1) * q + s = 2 * (2 ^ k * q) + s := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    by_cases hpar : s % 2 = 1
    · -- odd residue: U(2^{k+1} q + s) = 2^k·(3q) + U s, weight gains 1
      have hw : wt (k + 1) s = 1 + wt k (U s) := by
        show s % 2 + wt k (U s) = 1 + wt k (U s)
        omega
      have h3m : 2 ^ k * (3 * q) = 3 * (2 ^ k * q) := Nat.mul_left_comm (2 ^ k) 3 q
      have hU1 : U (2 ^ (k + 1) * q + s) = 2 ^ k * (3 * q) + U s := by
        rw [hsplit, h3m]
        unfold U
        rw [if_pos (show (2 * (2 ^ k * q) + s) % 2 = 1 by omega), if_pos hpar]
        omega
      show orbit k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + orbit k (U s)
      rw [hU1, affine k (3 * q) (U s), hw, Nat.pow_add, Nat.pow_one,
          Nat.mul_left_comm (3 ^ wt k (U s)) 3 q,
          Nat.mul_assoc 3 (3 ^ wt k (U s)) q]
    · -- even residue: U(2^{k+1} q + s) = 2^k·q + U s, weight unchanged
      have hw : wt (k + 1) s = wt k (U s) := by
        show s % 2 + wt k (U s) = wt k (U s)
        omega
      have hU1 : U (2 ^ (k + 1) * q + s) = 2 ^ k * q + U s := by
        rw [hsplit]
        unfold U
        rw [if_neg (show ¬(2 * (2 ^ k * q) + s) % 2 = 1 by omega), if_neg hpar]
        omega
      show orbit k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + orbit k (U s)
      rw [hU1, affine k q (U s), hw]

/-- A bound for every start, with integral scaling to avoid real arithmetic. -/
theorem scaled_image_bound : ∀ k n,
    2 ^ k * orbit k n < 3 ^ wt k n * (n + 2 ^ k)
  | 0, n => by simp [orbit, wt]
  | k + 1, n => by
    have ih := scaled_image_bound k (U n)
    have hp : 0 < 2 ^ k := Nat.pow_pos (by decide)
    have hstep : 2 * (U n + 2 ^ k) ≤
        3 ^ (n % 2) * (n + 2 ^ (k + 1)) := by
      by_cases hn : n % 2 = 1
      · simp only [U, hn, if_true, Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
        omega
      · have he : n % 2 = 0 := by omega
        simp only [U, he, Nat.zero_ne_one, if_false, Nat.pow_zero, Nat.one_mul, Nat.pow_succ]
        omega
    have hm := Nat.mul_le_mul_left (3 ^ wt k (U n)) hstep
    have hl := Nat.mul_lt_mul_of_pos_left (k := 2) ih (by decide)
    calc
      2 ^ (k + 1) * orbit (k + 1) n = 2 * (2 ^ k * orbit k (U n)) := by
        simp [orbit, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      _ < 2 * (3 ^ wt k (U n) * (U n + 2 ^ k)) := hl
      _ = 3 ^ wt k (U n) * (2 * (U n + 2 ^ k)) := Nat.mul_left_comm _ _ _
      _ ≤ 3 ^ wt k (U n) * (3 ^ (n % 2) * (n + 2 ^ (k + 1))) := hm
      _ = 3 ^ wt (k + 1) n * (n + 2 ^ (k + 1)) := by
        simp [wt, Nat.pow_add, Nat.mul_comm, Nat.mul_left_comm]

/-- Integral block bounds propagate exactly; no additive-error estimate is needed. -/
theorem block_image_bound : ∀ k p n, n < p * 2 ^ k →
    orbit k n < p * 3 ^ wt k n
  | 0, p, n, hn => by simpa [orbit, wt] using hn
  | k + 1, p, n, hn => by
    have hm : p * 2 ^ (k + 1) = 2 * (p * 2 ^ k) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [hm] at hn
    by_cases hp : n % 2 = 1
    · have hu : U n < (3 * p) * 2 ^ k := by
        simp only [U, if_pos hp, Nat.mul_assoc]
        omega
      have hi := block_image_bound k (3 * p) (U n) hu
      simpa [orbit, wt, hp, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hi
    · have he : n % 2 = 0 := by omega
      have hu : U n < p * 2 ^ k := by
        simp only [U, if_neg hp]
        omega
      simpa [orbit, wt, he] using block_image_bound k p (U n) hu

/-- Sharper residue image bound, using integrality of each shortcut step. -/
theorem residue_image_bound (k r : Nat) (hr : r < 2 ^ k) :
    orbit k r < 3 ^ wt k r := by
  simpa using block_image_bound k 1 r (by simpa using hr)

/-- The looser constant used in the original written packing argument. -/
theorem residue_image_bound_two (k r : Nat) (hr : r < 2 ^ k) :
    orbit k r < 2 * 3 ^ wt k r := by
  have hi := scaled_image_bound k r
  have hm := Nat.mul_le_mul_left (3 ^ wt k r)
    (show r + 2 ^ k ≤ 2 * 2 ^ k by omega)
  have he : 3 ^ wt k r * (2 * 2 ^ k) = 2 ^ k * (2 * 3 ^ wt k r) := by
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [he] at hm
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_lt_of_le hi hm)

/-- Iterates compose by addition of times. -/
theorem orbit_add : ∀ k t n, orbit (k + t) n = orbit k (orbit t n)
  | k, 0, n => by simp [orbit]
  | k, t + 1, n => by
    simpa [orbit, Nat.add_assoc] using orbit_add k t (U n)

/-- Distinct positions remain distinct after applying any fixed iterate. -/
theorem fixed_iterate_injective (n k : Nat)
    (hinj : Function.Injective (fun t => orbit t n)) :
    Function.Injective (fun t => orbit k (orbit t n)) := by
  intro i j h
  change orbit k (orbit i n) = orbit k (orbit j n) at h
  rw [← orbit_add, ← orbit_add] at h
  have he := hinj h
  omega

/-- The map is injective on the set of values of a nonrepeating orbit. -/
theorem fixed_iterate_on_orbit (n k x y : Nat)
    (hinj : Function.Injective (fun t => orbit t n))
    (hx : ∃ i, x = orbit i n) (hy : ∃ j, y = orbit j n)
    (he : orbit k x = orbit k y) : x = y := by
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨j, rfl⟩ := hy
  have hij := fixed_iterate_injective n k hinj he
  rw [hij]

/-- Elementary finite cardinality comparison, with no finiteness library. -/
theorem nodup_length_le_of_subset {xs ys : List Nat} (hd : xs.Nodup)
    (hs : ∀ x ∈ xs, x ∈ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons a xs ih =>
    have ha : a ∈ ys := hs a (by simp)
    obtain ⟨hna, hdx⟩ := List.nodup_cons.mp hd
    have hsub : ∀ x ∈ xs, x ∈ ys.erase a := by
      intro x hx
      have hne : x ≠ a := by intro h; subst x; exact hna hx
      exact (List.mem_erase_of_ne hne).mpr (hs x (by simp [hx]))
    have hlen := ih hdx hsub
    have he := List.length_erase_of_mem ha
    have hpos : 0 < ys.length := List.length_pos_iff.mpr (by intro h; simp [h] at ha)
    simp only [List.length_cons]
    omega

/-- Distinct objects injecting into the interval [0,M) number at most M. -/
theorem finite_image_packing (xs : List Nat) (f : Nat → Nat) (M : Nat)
    (hd : xs.Nodup)
    (hi : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y)
    (hb : ∀ x ∈ xs, f x < M) : xs.length ≤ M := by
  have hmap : (xs.map f).Nodup := by
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp_of_mem (fun hx hy hne he => hne (hi _ hx _ hy he)) hd
  have hs : ∀ y ∈ xs.map f, y ∈ List.range M := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact List.mem_range.mpr (hb x hx)
  simpa using nodup_length_le_of_subset hmap hs

/-- A selected finite list of positions in one aligned block, all of one
    parity weight, has at most 3^j members on a nonrepeating orbit.
    The subtraction is the block offset; its nontruncation follows from hblock. -/
theorem fixed_weight_packing (n k q j : Nat) (times : List Nat)
    (hinj : Function.Injective (fun t => orbit t n))
    (hd : times.Nodup)
    (hblock : ∀ t ∈ times,
      2 ^ k * q ≤ orbit t n ∧ orbit t n < 2 ^ k * q + 2 ^ k)
    (hweight : ∀ t ∈ times, wt k (orbit t n - 2 ^ k * q) = j) :
    times.length ≤ 3 ^ j := by
  let image := fun t => orbit k (orbit t n - 2 ^ k * q)
  have htranslate : ∀ t ∈ times, orbit k (orbit t n) = 3 ^ j * q + image t := by
    intro t ht
    have hlo := (hblock t ht).1
    have he : orbit t n = 2 ^ k * q + (orbit t n - 2 ^ k * q) := by omega
    calc
      orbit k (orbit t n) = orbit k (2 ^ k * q + (orbit t n - 2 ^ k * q)) :=
        congrArg (orbit k) he
      _ = 3 ^ j * q + image t := by rw [affine, hweight t ht]
  apply finite_image_packing times image (3 ^ j) hd
  · intro s hs t ht he
    apply fixed_iterate_injective n k hinj
    change orbit k (orbit s n) = orbit k (orbit t n)
    rw [htranslate s hs, htranslate t ht, he]
  · intro t ht
    have hr : orbit t n - 2 ^ k * q < 2 ^ k := by
      have := hblock t ht
      omega
    have hb := residue_image_bound k (orbit t n - 2 ^ k * q) hr
    simpa only [hweight t ht] using hb

#print axioms scaled_image_bound
#print axioms block_image_bound
#print axioms residue_image_bound
#print axioms fixed_iterate_injective
#print axioms finite_image_packing
#print axioms fixed_weight_packing

end CollatzPacking
