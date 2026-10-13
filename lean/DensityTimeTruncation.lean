/-
  Ordinary Collatz inverse fibres and a uniform finite-clock bound.
  Only finite arithmetic and cardinality are formalized here.
  Density limits, the spectrum at infinity, and time-limit exchanges
  are written arguments, not conclusions of this module.
-/
import CollatzContradiction

namespace DensityTimeTruncation
open OrdinaryCollatz

def parentsTwo (a : Nat) : List Nat :=
  [4 * a] ++
    if a % 3 = 2 then [(2 * a - 1) / 3]
    else if a % 6 = 4 then [2 * ((a - 1) / 3)] else []

theorem two_step_predecessor_iff (n a : Nat) :
    iterate 2 n = a ↔ n = 4 * a ∨
      (a % 3 = 2 ∧ n = (2 * a - 1) / 3) ∨
      (a % 6 = 4 ∧ n = 2 * ((a - 1) / 3)) := by
  simp only [iterate]
  unfold C
  split <;> split <;> omega

theorem mem_parentsTwo (n a : Nat) :
    n ∈ parentsTwo a ↔ iterate 2 n = a := by
  rw [two_step_predecessor_iff]
  by_cases h3 : a % 3 = 2 <;> by_cases h6 : a % 6 = 4 <;>
    simp_all [parentsTwo] <;> omega

theorem parentsTwo_length (a : Nat) : (parentsTwo a).length ≤ 2 := by
  unfold parentsTwo
  split <;> simp_all <;> split <;> simp_all

def fibre : Nat → Nat → List Nat
  | 0, a => [a]
  | k + 1, a => (parentsTwo a).flatMap (fibre k)

def count : Nat → Nat → Nat
  | 0, _ => 1
  | k + 1, a => count k (4 * a) +
      if a % 3 = 2 then count k ((2 * a - 1) / 3)
      else if a % 6 = 4 then count k (2 * ((a - 1) / 3)) else 0

theorem mem_fibre (k n a : Nat) :
    n ∈ fibre k a ↔ iterate (2 * k) n = a := by
  induction k generalizing a with
  | zero => simp [fibre, iterate]
  | succ k ih =>
    simp only [fibre, List.mem_flatMap]
    constructor
    · rintro ⟨p, hp, hn⟩
      have he := (ih p).mp hn
      have ht := (mem_parentsTwo p a).mp hp
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, iterate_add, he, ht]
    · intro he
      refine ⟨iterate (2 * k) n, ?_, (ih _).mpr rfl⟩
      apply (mem_parentsTwo _ a).mpr
      simpa only [show 2 * (k + 1) = 2 * k + 2 by omega, iterate_add] using he

theorem fibre_length (k a : Nat) : (fibre k a).length = count k a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [fibre, parentsTwo, count]
    split <;> simp_all <;> split <;> simp_all

theorem count_binary_bound (k a : Nat) : count k a ≤ 2 ^ k := by
  induction k generalizing a with
  | zero => simp [count]
  | succ k ih =>
    have h0 := ih (4 * a)
    have h1 := ih ((2 * a - 1) / 3)
    have h2 := ih (2 * ((a - 1) / 3))
    simp only [count, Nat.pow_succ]
    split <;> (try split) <;> omega

theorem count_shift (k a q : Nat) :
    count k (a + 2 * 3 ^ k * q) = count k a := by
  induction k generalizing a q with
  | zero => rfl
  | succ k ih =>
    have hp : 2 * 3 ^ (k + 1) * q = 6 * (3 ^ k * q) := by
      rw [Nat.pow_succ]
      calc
        2 * (3 ^ k * 3) * q = (2 * 3) * (3 ^ k * q) := by ac_rfl
        _ = 6 * (3 ^ k * q) := rfl
    have hmod3 : (a + 2 * 3 ^ (k + 1) * q) % 3 = a % 3 := by rw [hp]; omega
    have hmod6 : (a + 2 * 3 ^ (k + 1) * q) % 6 = a % 6 := by rw [hp]; omega
    have hmain : 4 * (a + 2 * 3 ^ (k + 1) * q) = 4 * a + 2 * 3 ^ k * (12 * q) := by
      have hm : 2 * 3 ^ k * (12 * q) = 24 * (3 ^ k * q) := by
        calc
          2 * 3 ^ k * (12 * q) = (2 * 12) * (3 ^ k * q) := by ac_rfl
          _ = 24 * (3 ^ k * q) := rfl
      rw [hp, hm]
      omega
    simp only [count, hmod3, hmod6, hmain, ih]
    split
    · rename_i h
      have hs : (2 * (a + 2 * 3 ^ (k + 1) * q) - 1) / 3 =
          (2 * a - 1) / 3 + 2 * 3 ^ k * (2 * q) := by
        rw [hp]
        have hmul : 2 * 3 ^ k * (2 * q) = 4 * (3 ^ k * q) := by
          calc
            2 * 3 ^ k * (2 * q) = (2 * 2) * (3 ^ k * q) := by ac_rfl
            _ = 4 * (3 ^ k * q) := rfl
        rw [hmul]
        omega
      rw [hs, ih]
    · split
      · rename_i h
        have hs : 2 * ((a + 2 * 3 ^ (k + 1) * q - 1) / 3) =
            2 * ((a - 1) / 3) + 2 * 3 ^ k * (2 * q) := by
          rw [hp]
          have hmul : 2 * 3 ^ k * (2 * q) = 4 * (3 ^ k * q) := by
            calc
              2 * 3 ^ k * (2 * q) = (2 * 2) * (3 ^ k * q) := by ac_rfl
              _ = 4 * (3 ^ k * q) := rfl
          rw [hmul]
          omega
        rw [hs, ih]
      · rfl

theorem count_residue (k a : Nat) :
    count k a = count k (a % (2 * 3 ^ k)) := by
  have he := count_shift k (a % (2 * 3 ^ k)) (a / (2 * 3 ^ k))
  simpa only [Nat.mod_add_div] using he

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem twelve_step_residue_bound :
    (List.range 1458).all (fun a => decide (count 6 a ≤ 38)) = true := by
  decide

theorem twelve_step_bound (a : Nat) : count 6 a ≤ 38 := by
  rw [count_residue]
  have h := List.all_eq_true.mp twelve_step_residue_bound (a % 1458)
    (List.mem_range.mpr (Nat.mod_lt _ (by decide)))
  exact of_decide_eq_true h

theorem twelve_step_witness : count 6 364 = 38 := by decide

theorem twelve_step_witness_nodup : (fibre 6 364).Nodup := by decide

theorem count_composition_bound (k j B : Nat)
    (hb : ∀ a, count k a ≤ B) (a : Nat) :
    count (k + j) a ≤ B * count j a := by
  induction j generalizing a with
  | zero => simpa [count] using hb a
  | succ j ih =>
    have h0 := ih (4 * a)
    have h1 := ih ((2 * a - 1) / 3)
    have h2 := ih (2 * ((a - 1) / 3))
    change count ((k + j) + 1) a ≤ B * count (j + 1) a
    simp only [count]
    split <;> (try split) <;> simp only [Nat.mul_add, Nat.mul_zero] <;> omega

theorem repeated_block_bound (q a : Nat) : count (6 * q) a ≤ 38 ^ q := by
  induction q generalizing a with
  | zero => simp [count]
  | succ q ih =>
    have hc := count_composition_bound 6 (6 * q) 38 twelve_step_bound a
    have hi := Nat.mul_le_mul_left 38 (ih a)
    have he : 6 * (q + 1) = 6 + 6 * q := by omega
    rw [he]
    rw [Nat.pow_succ]
    simpa only [Nat.mul_comm] using Nat.le_trans hc hi

theorem all_depth_bound (k a : Nat) :
    count k a ≤ 2 ^ (k % 6) * 38 ^ (k / 6) := by
  have hc := count_composition_bound (k % 6) (6 * (k / 6)) (2 ^ (k % 6))
    (count_binary_bound (k % 6)) a
  have hi := Nat.mul_le_mul_left (2 ^ (k % 6)) (repeated_block_bound (k / 6) a)
  have he : k % 6 + 6 * (k / 6) = k := Nat.mod_add_div k 6
  rw [he] at hc
  exact Nat.le_trans hc hi

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

theorem distinct_fibre_bound (k a : Nat) (xs : List Nat) (hd : xs.Nodup)
    (hh : ∀ n ∈ xs, iterate (2 * k) n = a) :
    xs.length ≤ 2 ^ (k % 6) * 38 ^ (k / 6) := by
  have hs : ∀ n ∈ xs, n ∈ fibre k a := by
    intro n hn
    exact (mem_fibre k n a).mpr (hh n hn)
  have hl := nodup_length_le_of_subset hd hs
  rw [fibre_length] at hl
  exact Nat.le_trans hl (all_depth_bound k a)

#print axioms two_step_predecessor_iff
#print axioms mem_parentsTwo
#print axioms parentsTwo_length
#print axioms mem_fibre
#print axioms fibre_length
#print axioms count_binary_bound
#print axioms count_shift
#print axioms count_residue
#print axioms twelve_step_residue_bound
#print axioms twelve_step_bound
#print axioms twelve_step_witness
#print axioms twelve_step_witness_nodup
#print axioms count_composition_bound
#print axioms repeated_block_bound
#print axioms all_depth_bound
#print axioms nodup_length_le_of_subset
#print axioms distinct_fibre_bound
end DensityTimeTruncation
