/-
  Checked small starts converge; cycles visiting them are trivial.
  Standalone Lean 4; no Mathlib.
  Check: lean lean/BoundedStandardCycle.lean

  The strongest theorem uses direct_range_1000000, which checks convergence
  of every start from 1 through 1000000 with fuel 200000 and NO escape branch.
  It implies shortcut_cycle_small_start_is_trivial without any global state
  bound. Finite computations use native_decide; soundness is kernel proved.

  The earlier numerical theorem range_a3_c1 recomputes the standard 3x+1 range
  check from CollatzCerts.lean: starts 1 through 100000, fuel 200000, and
  window threshold 2^62. It uses native_decide, whose generated native
  evaluation axiom is an explicit dependency of the final hitting theorems.

  Checker soundness, periodic reduction, and the bound on intermediate
  ordinary states are kernel proofs. A shortcut cycle bound over one
  complete period is extended to every iterate before ruling out escape.
  No bound on every positive Collatz orbit is asserted.
-/

namespace CollatzBoundedCycle

def T (a c n : Nat) : Nat := if n % 2 = 1 then a * n + c else n / 2

def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0, x => x
  | k + 1, x => iterN f k (f x)

def orbHits (f : Nat → Nat) (mins : List Nat) (tau : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | n, k + 1 =>
    if mins.contains n then true
    else if tau < n then true
    else orbHits f mins tau (f n) k

def checkFrom (f : Nat → Nat) (mins : List Nat) (tau fuel : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | i, left + 1 =>
    if orbHits f mins tau i fuel then checkFrom f mins tau fuel (i + 1) left
    else false

theorem checkFrom_at (f : Nat → Nat) (mins : List Nat) (tau fuel count start n : Nat)
    (hc : checkFrom f mins tau fuel start count = true)
    (hlo : start ≤ n) (hhi : n < start + count) :
    orbHits f mins tau n fuel = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    simp only [checkFrom] at hc
    split at hc
    · rename_i hhead
      by_cases he : n = start
      · simpa only [he] using hhead
      · exact ih (start + 1) hc (by omega) (by omega)
    · contradiction

theorem orbHits_sound (f : Nat → Nat) (mins : List Nat) (tau fuel n : Nat)
    (hc : orbHits f mins tau n fuel = true) :
    ∃ t, t < fuel ∧ (iterN f t n ∈ mins ∨ tau < iterN f t n) := by
  induction fuel generalizing n with
  | zero => simp [orbHits] at hc
  | succ fuel ih =>
    simp only [orbHits] at hc
    split at hc
    · rename_i hm
      exact ⟨0, by omega, Or.inl (by simpa [iterN] using hm)⟩
    · split at hc
      · rename_i ht
        exact ⟨0, by omega, Or.inr ht⟩
      · obtain ⟨t, ht, hhit⟩ := ih (f n) hc
        exact ⟨t + 1, by omega, hhit⟩

theorem noescape_forces_hit (f : Nat → Nat) (mins : List Nat) (tau fuel n : Nat)
    (hc : orbHits f mins tau n fuel = true)
    (hb : ∀ t, t < fuel → iterN f t n ≤ tau) :
    ∃ t, t < fuel ∧ iterN f t n ∈ mins := by
  obtain ⟨t, ht, hm | he⟩ := orbHits_sound f mins tau fuel n hc
  · exact ⟨t, ht, hm⟩
  · have := hb t ht
    omega

theorem iterN_add (f : Nat → Nat) (a b n : Nat) :
    iterN f (a + b) n = iterN f b (iterN f a n) := by
  induction a generalizing n with
  | zero => simp [iterN]
  | succ a ih => simpa only [Nat.succ_add, iterN] using ih (f n)

theorem cycle_reduce (f : Nat → Nat) (N n : Nat) (hN : 0 < N)
    (hcycle : iterN f N n = n) (t : Nat) :
    ∃ r, r < N ∧ iterN f t n = iterN f r n := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    by_cases ht : t < N
    · exact ⟨t, ht, rfl⟩
    · obtain ⟨r, hr, he⟩ := ih (t - N) (by omega)
      refine ⟨r, hr, ?_⟩
      have hsum : t = N + (t - N) := by omega
      rw [hsum, iterN_add, hcycle]
      exact he

theorem cycle_uniform_bound (f : Nat → Nat) (N n B : Nat) (hN : 0 < N)
    (hcycle : iterN f N n = n)
    (hb : ∀ r, r < N → iterN f r n ≤ B) :
    ∀ t, iterN f t n ≤ B := by
  intro t
  obtain ⟨r, hr, he⟩ := cycle_reduce f N n hN hcycle t
  rw [he]
  exact hb r hr

theorem range_a3_c1 :
    checkFrom (T 3 1) [1] 4611686018427387904 200000 1 100000 = true := by native_decide

theorem bounded_start_hits_one (n : Nat) (hn : 0 < n) (hsmall : n ≤ 100000)
    (hb : ∀ t, t < 200000 → iterN (T 3 1) t n ≤ 4611686018427387904) :
    ∃ t, t < 200000 ∧ iterN (T 3 1) t n = 1 := by
  have hc := checkFrom_at (T 3 1) [1] 4611686018427387904 200000 100000 1 n
    range_a3_c1 (by omega) (by omega)
  obtain ⟨t, ht, hm⟩ := noescape_forces_hit (T 3 1) [1] _ _ n hc hb
  exact ⟨t, ht, by simpa using hm⟩

theorem ordinary_cycle_hits_one (N n : Nat) (hn : 0 < n) (hN : 0 < N)
    (hcycle : iterN (T 3 1) N n = n)
    (hb : ∀ r, r < N → iterN (T 3 1) r n ≤ 100000) :
    ∃ r, r < N ∧ iterN (T 3 1) r n = 1 := by
  have hsmall := hb 0 hN
  change n ≤ 100000 at hsmall
  have hall := cycle_uniform_bound (T 3 1) N n 100000 hN hcycle hb
  obtain ⟨t, _, ht⟩ := bounded_start_hits_one n hn hsmall (fun t _ => by
    have := hall t
    omega)
  obtain ⟨r, hr, he⟩ := cycle_reduce (T 3 1) N n hN hcycle t
  exact ⟨r, hr, by omega⟩

def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

theorem ordinary_bound_from_shortcut (B t : Nat) :
    ∀ n, (∀ k, iterN U k n ≤ B) → iterN (T 3 1) t n ≤ 3 * B + 1 := by
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro n hb
    have hn : n ≤ B := hb 0
    have hnext : ∀ k, iterN U k (U n) ≤ B := fun k => hb (k + 1)
    cases t with
    | zero => simpa only [iterN] using (show n ≤ 3 * B + 1 by omega)
    | succ t =>
      by_cases hnodd : n % 2 = 1
      · cases t with
        | zero =>
          change T 3 1 n ≤ 3 * B + 1
          simp only [T, if_pos hnodd]
          omega
        | succ s =>
          have heven : (3 * n + 1) % 2 ≠ 1 := by omega
          have hstep : T 3 1 (T 3 1 n) = U n := by
            simp only [T, U, if_pos hnodd, if_neg heven]
          change iterN (T 3 1) s (T 3 1 (T 3 1 n)) ≤ 3 * B + 1
          rw [hstep]
          exact ih s (by omega) (U n) hnext
      · have hstep : T 3 1 n = U n := by simp only [T, U, if_neg hnodd]
        change iterN (T 3 1) t (T 3 1 n) ≤ 3 * B + 1
        rw [hstep]
        exact ih t (by omega) (U n) hnext

theorem ordinary_hit_implies_shortcut (k : Nat) :
    ∀ n, iterN (T 3 1) k n = 1 → ∃ j, iterN U j n = 1 := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro n hk
    cases k with
    | zero => exact ⟨0, hk⟩
    | succ k =>
      by_cases hn : n % 2 = 1
      · cases k with
        | zero =>
          have hc : T 3 1 n = 3 * n + 1 := by simp only [T, if_pos hn]
          change T 3 1 n = 1 at hk
          omega
        | succ l =>
          have he : (3 * n + 1) % 2 ≠ 1 := by omega
          have hstep : T 3 1 (T 3 1 n) = U n := by
            simp only [T, U, if_pos hn, if_neg he]
          change iterN (T 3 1) l (T 3 1 (T 3 1 n)) = 1 at hk
          rw [hstep] at hk
          obtain ⟨j, hj⟩ := ih l (by omega) (U n) hk
          exact ⟨j + 1, hj⟩
      · have hstep : T 3 1 n = U n := by simp only [T, U, if_neg hn]
        change iterN (T 3 1) k (T 3 1 n) = 1 at hk
        rw [hstep] at hk
        obtain ⟨j, hj⟩ := ih k (by omega) (U n) hk
        exact ⟨j + 1, hj⟩

theorem shortcut_cycle_with_small_start_hits_one (N n B : Nat)
    (hn : 0 < n) (hsmall : n ≤ 100000) (hN : 0 < N)
    (hcycle : iterN U N n = n)
    (hb : ∀ r, r < N → iterN U r n ≤ B)
    (hwindow : 3 * B + 1 ≤ 4611686018427387904) :
    ∃ r, r < N ∧ iterN U r n = 1 := by
  have hall := cycle_uniform_bound U N n B hN hcycle hb
  obtain ⟨t, _, ht⟩ := bounded_start_hits_one n hn hsmall (fun t _ =>
    Nat.le_trans (ordinary_bound_from_shortcut B t n hall) hwindow)
  obtain ⟨s, hs⟩ := ordinary_hit_implies_shortcut t n ht
  obtain ⟨r, hr, he⟩ := cycle_reduce U N n hN hcycle s
  exact ⟨r, hr, by omega⟩

theorem shortcut_cycle_hits_one (N n : Nat) (hn : 0 < n) (hN : 0 < N)
    (hcycle : iterN U N n = n)
    (hb : ∀ r, r < N → iterN U r n ≤ 100000) :
    ∃ r, r < N ∧ iterN U r n = 1 := by
  have hsmall : n ≤ 100000 := hb 0 hN
  exact shortcut_cycle_with_small_start_hits_one N n 100000 hn hsmall hN hcycle hb (by decide)

/-- The shortcut map preserves the trivial cycle {1,2}. -/
theorem trivial_cycle_invariant (t n : Nat) (hn : n = 1 ∨ n = 2) :
    iterN U t n = 1 ∨ iterN U t n = 2 := by
  induction t generalizing n with
  | zero => exact hn
  | succ t ih =>
    apply ih (U n)
    rcases hn with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- A nonempty shortcut cycle that visits 1 starts at 1 or 2.
    The hitting time need not lie in the first period. -/
theorem shortcut_cycle_hit_one_is_trivial (N n t : Nat) (hN : 0 < N)
    (hcycle : iterN U N n = n) (hhit : iterN U t n = 1) : n = 1 ∨ n = 2 := by
  obtain ⟨r, hr, he⟩ := cycle_reduce U N n hN hcycle t
  have hrhit : iterN U r n = 1 := by rw [← he]; exact hhit
  have hsum : r + (N - r) = N := by omega
  have hback : iterN U (N - r) 1 = n := by
    rw [← hrhit, ← iterN_add, hsum, hcycle]
  have htrivial := trivial_cycle_invariant (N - r) 1 (Or.inl rfl)
  rwa [hback] at htrivial

/-- Direct exclusion interface: the bounded-cycle hypotheses imply that the
    initial value belongs to the trivial shortcut cycle. -/
theorem shortcut_cycle_with_small_start_is_trivial (N n B : Nat)
    (hn : 0 < n) (hsmall : n ≤ 100000) (hN : 0 < N)
    (hcycle : iterN U N n = n)
    (hb : ∀ r, r < N → iterN U r n ≤ B)
    (hwindow : 3 * B + 1 ≤ 4611686018427387904) : n = 1 ∨ n = 2 := by
  obtain ⟨r, _, hr⟩ :=
    shortcut_cycle_with_small_start_hits_one N n B hn hsmall hN hcycle hb hwindow
  exact shortcut_cycle_hit_one_is_trivial N n r hN hcycle hr

/-- Direct reachability checker: no escape-window alternative. -/
def hitsOne (f : Nat → Nat) : Nat → Nat → Bool
  | _, 0 => false
  | n, fuel + 1 => if n = 1 then true else hitsOne f (f n) fuel

def checkOneFrom (f : Nat → Nat) (fuel : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | start, count + 1 =>
    if hitsOne f start fuel then checkOneFrom f fuel (start + 1) count else false

theorem hitsOne_sound (f : Nat → Nat) (fuel n : Nat)
    (hc : hitsOne f n fuel = true) :
    ∃ t, t < fuel ∧ iterN f t n = 1 := by
  induction fuel generalizing n with
  | zero => simp [hitsOne] at hc
  | succ fuel ih =>
    simp only [hitsOne] at hc
    split at hc
    · rename_i hn
      exact ⟨0, by omega, hn⟩
    · obtain ⟨t, ht, he⟩ := ih (f n) hc
      exact ⟨t + 1, by omega, he⟩

theorem checkOneFrom_at (f : Nat → Nat) (fuel count start n : Nat)
    (hc : checkOneFrom f fuel start count = true)
    (hlo : start ≤ n) (hhi : n < start + count) :
    hitsOne f n fuel = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    simp only [checkOneFrom] at hc
    split at hc
    · rename_i hhead
      by_cases he : n = start
      · simpa only [he] using hhead
      · exact ih (start + 1) hc (by omega) (by omega)
    · contradiction

theorem small_start_hits_one_of_check (B fuel n : Nat)
    (hc : checkOneFrom (T 3 1) fuel 1 B = true)
    (hn : 0 < n) (hsmall : n ≤ B) :
    ∃ t, t < fuel ∧ iterN (T 3 1) t n = 1 := by
  exact hitsOne_sound (T 3 1) fuel n
    (checkOneFrom_at (T 3 1) fuel B 1 n hc (by omega) (by omega))

theorem direct_range_1000000 :
    checkOneFrom (T 3 1) 200000 1 1000000 = true := by native_decide

theorem small_start_hits_one_unconditionally (n : Nat)
    (hn : 0 < n) (hsmall : n ≤ 1000000) :
    ∃ t, t < 200000 ∧ iterN (T 3 1) t n = 1 :=
  small_start_hits_one_of_check 1000000 200000 n direct_range_1000000 hn hsmall

/-- Any positive shortcut cycle with a start at most one million is trivial.
    No bound on its other states is assumed. -/
theorem shortcut_cycle_small_start_is_trivial (N n : Nat)
    (hn : 0 < n) (hsmall : n ≤ 1000000) (hN : 0 < N)
    (hcycle : iterN U N n = n) : n = 1 ∨ n = 2 := by
  obtain ⟨t, _, ht⟩ := small_start_hits_one_unconditionally n hn hsmall
  obtain ⟨s, hs⟩ := ordinary_hit_implies_shortcut t n ht
  exact shortcut_cycle_hit_one_is_trivial N n s hN hcycle hs

#print axioms hitsOne_sound
#print axioms checkOneFrom_at
#print axioms small_start_hits_one_unconditionally
#print axioms shortcut_cycle_small_start_is_trivial
#print axioms trivial_cycle_invariant
#print axioms shortcut_cycle_hit_one_is_trivial
#print axioms shortcut_cycle_with_small_start_is_trivial
#print axioms ordinary_bound_from_shortcut
#print axioms ordinary_hit_implies_shortcut
#print axioms shortcut_cycle_with_small_start_hits_one
#print axioms shortcut_cycle_hits_one

#print axioms checkFrom_at
#print axioms orbHits_sound
#print axioms cycle_reduce
#print axioms ordinary_cycle_hits_one
end CollatzBoundedCycle
