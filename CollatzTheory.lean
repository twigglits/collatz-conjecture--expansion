/-
  CollatzTheory.lean — machine-checked structural theorems for the
  generalized Collatz family   T_{a,c}(n) = a*n + c  (n odd),  n/2  (n even).

  Pure kernel proofs: no Mathlib, no native_decide, no extra axioms.
  Check with:  lean CollatzTheory.lean    (Lean 4.31.0)
-/

/-- One step of the generalized Collatz map. -/
def T (a c n : Nat) : Nat := if n % 2 = 1 then a * n + c else n / 2

/-- `iterN f k x` = k-fold application of `f` to `x`. -/
def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => iterN f k (f x)

/- ====================================================================
   1. PARITY REDUCTION — the family is dynamically interesting only
      for a, c both odd.  Otherwise every odd start diverges monotonically.
   ==================================================================== -/

/-- a odd, c even, c > 0: an odd point maps to a strictly larger odd point. -/
theorem step_growth_evenC {a c n : Nat} (ha : a % 2 = 1) (hc : c % 2 = 0)
    (hc0 : 0 < c) (hn : n % 2 = 1) : (T a c n) % 2 = 1 ∧ n < T a c n := by
  have hmul := Nat.mul_mod a n 2
  rw [ha, hn] at hmul
  have han : n ≤ a * n := Nat.le_mul_of_pos_left n (by omega : 0 < a)
  unfold T
  rw [if_pos hn]
  omega

/-- a even (a ≥ 2), c odd: an odd point maps to a strictly larger odd point. -/
theorem step_growth_evenA {a c n : Nat} (ha : a % 2 = 0) (ha2 : 2 ≤ a)
    (hc : c % 2 = 1) (hn : n % 2 = 1) : (T a c n) % 2 = 1 ∧ n < T a c n := by
  have hmul := Nat.mul_mod a n 2
  rw [ha] at hmul
  have h2n : 2 * n ≤ a * n := Nat.mul_le_mul_right n ha2
  unfold T
  rw [if_pos hn]
  omega

/-- Divergence: with a odd, c even > 0, the whole forward orbit of any odd
    point stays odd and grows at least linearly — no cycles, no convergence. -/
theorem orbit_diverges_evenC {a c : Nat} (ha : a % 2 = 1) (hc : c % 2 = 0)
    (hc0 : 0 < c) :
    ∀ (k n : Nat), n % 2 = 1 →
      (iterN (T a c) k n) % 2 = 1 ∧ n + k ≤ iterN (T a c) k n
  | 0, n, hn => ⟨hn, by show n + 0 ≤ n; omega⟩
  | k + 1, n, hn => by
    have hs := step_growth_evenC ha hc hc0 hn
    have ih := orbit_diverges_evenC ha hc hc0 k (T a c n) hs.1
    show (iterN (T a c) k (T a c n)) % 2 = 1 ∧ n + (k+1) ≤ iterN (T a c) k (T a c n)
    omega

/- ====================================================================
   2. SCALING CONJUGACY — for odd m, the system (a, m*c) restricted to
      multiples of m is exactly m times the system (a, c).
      Hence cycles(a, m*c) ⊇ m * cycles(a, c).
   ==================================================================== -/

theorem scaling_step {a c m n : Nat} (hm : m % 2 = 1) :
    T a (m * c) (m * n) = m * T a c n := by
  have h1 := Nat.mul_mod m n 2
  rw [hm] at h1
  by_cases hn : n % 2 = 1
  · unfold T
    rw [if_pos (by omega : m * n % 2 = 1), if_pos hn]
    rw [Nat.mul_left_comm, ← Nat.mul_add]
  · unfold T
    rw [if_neg (by omega : ¬ m * n % 2 = 1), if_neg hn]
    exact Nat.mul_div_assoc m (Nat.dvd_of_mod_eq_zero (by omega))

theorem scaling_orbit {a c m : Nat} (hm : m % 2 = 1) :
    ∀ (k n : Nat), iterN (T a (m * c)) k (m * n) = m * iterN (T a c) k n
  | 0, _ => rfl
  | k + 1, n => by
    show iterN (T a (m * c)) k (T a (m * c) (m * n)) = m * iterN (T a c) k (T a c n)
    rw [scaling_step hm]
    exact scaling_orbit hm k (T a c n)

/- ====================================================================
   3. PRIME ABSORPTION — if p is an odd prime factor of both a and c,
      every orbit falls into pℤ after one odd step and stays there.
      Combined with scaling this reduces (a,c) to (a, c/p): WLOG
      gcd(a, c) = 1 in the classification.
   ==================================================================== -/

theorem absorb_entry {p a c n : Nat} (hpa : p ∣ a) (hpc : p ∣ c)
    (hn : n % 2 = 1) : p ∣ T a c n := by
  unfold T
  rw [if_pos hn]
  obtain ⟨s, rfl⟩ := hpa
  obtain ⟨t, rfl⟩ := hpc
  exact ⟨s * n + t, by rw [Nat.mul_add, ← Nat.mul_assoc]⟩

theorem absorb_step {p a c n : Nat} (hp : p % 2 = 1) (hpa : p ∣ a) (hpc : p ∣ c)
    (hpn : p ∣ n) : p ∣ T a c n := by
  by_cases hn : n % 2 = 1
  · exact absorb_entry hpa hpc hn
  · unfold T
    rw [if_neg hn]
    obtain ⟨t, rfl⟩ := hpn
    have h1 := Nat.mul_mod p t 2
    rw [hp] at h1
    have ht : t % 2 = 0 := by omega
    rw [Nat.mul_div_assoc p (Nat.dvd_of_mod_eq_zero ht)]
    exact Nat.dvd_mul_right p (t / 2)

theorem absorb_iter {p a c : Nat} (hp : p % 2 = 1) (hpa : p ∣ a) (hpc : p ∣ c) :
    ∀ (k n : Nat), p ∣ n → p ∣ iterN (T a c) k n
  | 0, _, h => h
  | k + 1, n, h => absorb_iter hp hpa hpc k (T a c n) (absorb_step hp hpa hpc h)

/-- After the first odd step, an orbit of (a,c) with p ∣ a, p ∣ c, p odd
    is trapped in pℤ forever. -/
theorem absorb_orbit {p a c n : Nat} (hp : p % 2 = 1) (hpa : p ∣ a) (hpc : p ∣ c)
    (hn : n % 2 = 1) (k : Nat) : p ∣ iterN (T a c) (k + 1) n :=
  absorb_iter hp hpa hpc k (T a c n) (absorb_entry hpa hpc hn)

/- ====================================================================
   4. UNIVERSAL TRIVIAL CYCLE — for a = 2^k − 1 (a = 3, 7, 15, 31, …)
      EVERY system (a, c) with c odd has the cycle through c itself:
      c → (a+1)c = 2^k c → … → c   in exactly k+1 steps.
      This is the general form of the Collatz cycle {1,4,2}.
   ==================================================================== -/

theorem halve_iter (a c : Nat) :
    ∀ (k m : Nat), iterN (T a c) k (2 ^ k * m) = m
  | 0, m => by
    show iterN (T a c) 0 (2 ^ 0 * m) = m
    rw [Nat.pow_zero, Nat.one_mul]
    rfl
  | k + 1, m => by
    have h2 : 2 ^ (k+1) * m = 2 * (2 ^ k * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have ht : T a c (2 * (2 ^ k * m)) = 2 ^ k * m := by
      unfold T
      rw [if_neg (by omega : ¬ 2 * (2 ^ k * m) % 2 = 1)]
      omega
    show iterN (T a c) k (T a c (2 ^ (k+1) * m)) = m
    rw [h2, ht]
    exact halve_iter a c k m

theorem universal_cycle {a c : Nat} (k : Nat) (ha : a + 1 = 2 ^ k)
    (hc : c % 2 = 1) : iterN (T a c) (k + 1) c = c := by
  have h1 : T a c c = 2 ^ k * c := by
    unfold T
    rw [if_pos hc, ← ha, Nat.add_mul, Nat.one_mul]
  show iterN (T a c) k (T a c c) = c
  rw [h1]
  exact halve_iter a c k c

/-- Every 3x+c system (c odd) has the cycle through c:  c → 4c → 2c → c. -/
theorem trivial_cycle_3 (c : Nat) (hc : c % 2 = 1) : iterN (T 3 c) 3 c = c :=
  universal_cycle (a := 3) 2 rfl hc

/-- Every 7x+c system (c odd) has the cycle through c (period 4). -/
theorem trivial_cycle_7 (c : Nat) (hc : c % 2 = 1) : iterN (T 7 c) 4 c = c :=
  universal_cycle (a := 7) 3 rfl hc

/-- Every 15x+c system (c odd) has the cycle through c (period 5). -/
theorem trivial_cycle_15 (c : Nat) (hc : c % 2 = 1) : iterN (T 15 c) 5 c = c :=
  universal_cycle (a := 15) 4 rfl hc

/- Kernel-checked sanity examples (no native code, pure `decide`). -/
example : iterN (T 3 1) 3 1 = 1 := by decide
example : iterN (T 5 1) 10 13 = 13 := by decide  -- 5x+1 cycle {13,33,83}
example : iterN (T 5 1) 10 17 = 17 := by decide  -- 5x+1 cycle {17,43,27}

#print axioms orbit_diverges_evenC
#print axioms scaling_orbit
#print axioms absorb_orbit
#print axioms universal_cycle
#print axioms trivial_cycle_3
