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

/- ====================================================================
   5. THE UNIVERSAL-CYCLE MECHANISM, SHARPENED
      Let F_{a,c}(x) = oddPart(a·x + c) be the accelerated odd→odd map.
      Master identity (c odd):        F_{a,c}(c·y) = c · F_{a,1}(y)
      Formula at the point c:         F_{a,c}(c)   = oddPart(a+1) · c
      Consequences, all proved below for ALL parameters:
        • F_{a,c}(c) = c  ↔  a+1 is a power of 2      (converse of Thm 4:
          the universal fixed point CHARACTERIZES a = 2^k − 1)
        • F_{a,c}(x) = x  ↔  ∃ d k, d·x = c ∧ a+d = 2^k
          (complete law of one-step cycles: fixed points ↔ divisors d of c
           with d + a a power of two)
        • orbit transport:  iterN F_{a,c} n (c·y) = c · iterN F_{a,1} n y,
          and c·y is n-periodic for (a,c)  ↔  y is n-periodic for (a,1):
          every cycle of ax+1 is a UNIVERSAL cycle family of ax+c
          (a=5: {c,3c} for every odd c; a=181: {27c, 611c}).
   ==================================================================== -/

/-- Odd part of n: divide out every factor of 2 (convention oddPart 0 = 0). -/
def oddPart (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

theorem oddPart_zero : oddPart 0 = 0 := by
  rw [oddPart.eq_def, dif_neg (by omega : ¬((0:Nat) % 2 = 0 ∧ (0:Nat) ≠ 0))]

theorem oddPart_odd {n : Nat} (hn : n % 2 = 1) : oddPart n = n := by
  rw [oddPart.eq_def, dif_neg (by omega : ¬(n % 2 = 0 ∧ n ≠ 0))]

theorem oddPart_even {n : Nat} (h0 : n ≠ 0) (he : n % 2 = 0) :
    oddPart n = oddPart (n / 2) := by
  rw [oddPart.eq_def, dif_pos ⟨he, h0⟩]

theorem two_pow_pos : ∀ k : Nat, 0 < 2 ^ k
  | 0 => by decide
  | k + 1 => by rw [Nat.pow_succ]; have := two_pow_pos k; omega

/-- Fundamental factorization: every n ≥ 1 is 2^k times its odd part. -/
theorem oddPart_spec (n : Nat) (hne : n ≠ 0) :
    (oddPart n) % 2 = 1 ∧ ∃ k, n = 2 ^ k * oddPart n := by
  have key : ∀ b m, m ≤ b → m ≠ 0 →
      (oddPart m) % 2 = 1 ∧ ∃ k, m = 2 ^ k * oddPart m := by
    intro b
    induction b with
    | zero => intro m hle hme; exact absurd (Nat.le_zero.mp hle) hme
    | succ b ih =>
      intro m hle hme
      by_cases hpar : m % 2 = 1
      · rw [oddPart_odd hpar]
        exact ⟨hpar, 0, by rw [Nat.pow_zero, Nat.one_mul]⟩
      · have he : m % 2 = 0 := by omega
        have hne2 : m / 2 ≠ 0 := by omega
        have hle2 : m / 2 ≤ b := by omega
        have ihh := ih (m / 2) hle2 hne2
        rw [oddPart_even hme he]
        refine ⟨ihh.1, ?_⟩
        obtain ⟨k, hk⟩ := ihh.2
        refine ⟨k + 1, ?_⟩
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ← hk]
        omega
  exact key n n (Nat.le_refl n) hne

/-- Uniqueness of the 2-power/odd factorization (cancellation form). -/
theorem pow2_mul_odd_cancel : ∀ (k j m m' : Nat), m % 2 = 1 → m' % 2 = 1 →
    2 ^ k * m = 2 ^ j * m' → m = m' := by
  intro k
  induction k with
  | zero =>
    intro j m m' hm hm' heq
    rw [Nat.pow_zero, Nat.one_mul] at heq
    cases j with
    | zero => rw [Nat.pow_zero, Nat.one_mul] at heq; exact heq
    | succ j' =>
      exfalso
      rw [Nat.pow_succ, Nat.mul_assoc] at heq
      -- heq : m = 2^j' * (2 * m'), so m is even: contradiction
      have h1 := Nat.mul_mod (2 ^ j') (2 * m') 2
      rw [← heq] at h1
      have h2 : (2 * m') % 2 = 0 := Nat.mul_mod_right 2 m'
      rw [h2, Nat.mul_zero] at h1
      omega
  | succ k ih =>
    intro j m m' hm hm' heq
    cases j with
    | zero =>
      exfalso
      rw [Nat.pow_zero, Nat.one_mul, Nat.pow_succ, Nat.mul_assoc] at heq
      have h1 := Nat.mul_mod (2 ^ k) (2 * m) 2
      rw [heq] at h1
      have h2 : (2 * m) % 2 = 0 := Nat.mul_mod_right 2 m
      rw [h2, Nat.mul_zero] at h1
      omega
    | succ j' =>
      rw [Nat.pow_succ, Nat.pow_succ] at heq
      have h1 : 2 * (2 ^ k * m) = 2 * (2 ^ j' * m') := by
        rw [← Nat.mul_assoc, ← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ k),
            Nat.mul_comm 2 (2 ^ j')]
        exact heq
      exact ih j' m m' hm hm' (Nat.eq_of_mul_eq_mul_left (by omega) h1)

/-- If n = 2^k · m with m odd then oddPart n = m. -/
theorem oddPart_unique {n m k : Nat} (hm : m % 2 = 1) (hn : n = 2 ^ k * m) :
    oddPart n = m := by
  have hne : n ≠ 0 := by
    have h1 := two_pow_pos k
    have h2 : 0 < m := by omega
    have h3 := Nat.mul_pos h1 h2
    omega
  obtain ⟨hodd, j, hj⟩ := oddPart_spec n hne
  exact pow2_mul_odd_cancel j k (oddPart n) m hodd hm (by rw [← hj]; exact hn)

/-- KEY LEMMA: an odd factor passes through the odd part. -/
theorem oddPart_mul_odd {c : Nat} (hc : c % 2 = 1) (n : Nat) :
    oddPart (c * n) = c * oddPart n := by
  cases Nat.eq_zero_or_pos n with
  | inl h0 => rw [h0, Nat.mul_zero, oddPart_zero, Nat.mul_zero]
  | inr hpos =>
    have hne : n ≠ 0 := by omega
    obtain ⟨hodd, k, hk⟩ := oddPart_spec n hne
    have hm : (c * oddPart n) % 2 = 1 := by
      have h := Nat.mul_mod c (oddPart n) 2
      rw [hc, hodd] at h
      omega
    refine oddPart_unique (k := k) hm ?_
    rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ k) c, Nat.mul_assoc, ← hk]

theorem oddPart_eq_one_iff {n : Nat} (hne : n ≠ 0) :
    oddPart n = 1 ↔ ∃ k, n = 2 ^ k := by
  constructor
  · intro h1
    obtain ⟨_, k, hk⟩ := oddPart_spec n hne
    exact ⟨k, by rw [hk, h1, Nat.mul_one]⟩
  · intro h
    obtain ⟨k, hk⟩ := h
    exact oddPart_unique (by omega : (1:Nat) % 2 = 1) (by rw [hk, Nat.mul_one])

/-- The accelerated odd→odd map: one odd step, then all halvings at once. -/
def F (a c x : Nat) : Nat := oddPart (a * x + c)

/-- MASTER IDENTITY (scaling covariance of the accelerated map): for d odd,
    F_{a, d·e}(d·u) = d · F_{a,e}(u).  With e = 1: the (a,c)-orbit of c·y is
    c times the (a,1)-orbit of y.  Note: only d needs to be odd. -/
theorem F_scaling {d : Nat} (hd : d % 2 = 1) (a e u : Nat) :
    F a (d * e) (d * u) = d * F a e u := by
  unfold F
  rw [show a * (d * u) + d * e = d * (a * u + e) by
        rw [Nat.mul_left_comm a d u, ← Nat.mul_add]]
  exact oddPart_mul_odd hd (a * u + e)

/-- THE FORMULA behind the universal cycle: the accelerated image of the
    point c is always  oddPart(a+1) · c. -/
theorem F_formula {a c : Nat} (hc : c % 2 = 1) :
    F a c c = oddPart (a + 1) * c := by
  unfold F
  rw [show a * c + c = c * (a + 1) by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm c a]]
  rw [oddPart_mul_odd hc (a + 1), Nat.mul_comm c (oddPart (a + 1))]

/-- RIGIDITY (converse of Theorem 4): c is a fixed point of the accelerated
    map  ↔  a + 1 is a power of 2.  Holds for every single odd c, hence the
    fixed point at c is universal exactly for the Mersenne multipliers. -/
theorem universal_fixed_iff {a c : Nat} (hc : c % 2 = 1) :
    F a c c = c ↔ ∃ k, a + 1 = 2 ^ k := by
  rw [F_formula hc]
  constructor
  · intro h
    have h2 : c * oddPart (a + 1) = c * 1 := by
      rw [Nat.mul_comm c (oddPart (a + 1)), Nat.mul_one]
      exact h
    have h1 : oddPart (a + 1) = 1 :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < c) h2
    exact (oddPart_eq_one_iff (by omega : a + 1 ≠ 0)).mp h1
  · intro h
    obtain ⟨k, hk⟩ := h
    rw [(oddPart_eq_one_iff (by omega : a + 1 ≠ 0)).mpr ⟨k, hk⟩, Nat.one_mul]

/-- Sufficiency direction as a named corollary (F-form of Theorem 4). -/
theorem F_universal_cycle {a c k : Nat} (ha : a + 1 = 2 ^ k) (hc : c % 2 = 1) :
    F a c c = c :=
  (universal_fixed_iff hc).mpr ⟨k, ha⟩

/-- ONE-STEP CYCLE LAW: complete classification of fixed points of the
    accelerated map.  x is fixed  ↔  x divides c and a + c/x is a power of 2.
    (Stated multiplicatively: ∃ d k with d·x = c and a + d = 2^k.)
    The universal fixed point x = c is the divisor d = 1 (a Mersenne);
    the classical fixed point x = 1 is the divisor d = c (a + c a 2-power). -/
theorem fix_classification {a c x : Nat} (hc : c % 2 = 1) :
    F a c x = x ↔ ∃ d k, d * x = c ∧ a + d = 2 ^ k := by
  constructor
  · intro hfix
    have hne : a * x + c ≠ 0 := by omega
    obtain ⟨hodd, k, hk⟩ := oddPart_spec (a * x + c) hne
    have hfix' : oddPart (a * x + c) = x := hfix
    rw [hfix'] at hodd hk
    -- hodd : x % 2 = 1,  hk : a * x + c = 2 ^ k * x
    have hxpos : 0 < x := by omega
    have hle : a ≤ 2 ^ k := by
      cases Nat.lt_or_ge a (2 ^ k) with
      | inl h => omega
      | inr hge =>
        have h := Nat.mul_le_mul_right x hge
        omega
    refine ⟨2 ^ k - a, k, ?_, by omega⟩
    rw [Nat.sub_mul]
    omega
  · intro h
    obtain ⟨d, k, hdx, hdk⟩ := h
    have hx : x % 2 = 1 := by
      have hmm := Nat.mul_mod d x 2
      rw [hdx, hc] at hmm
      cases Nat.mod_two_eq_zero_or_one x with
      | inl h0 => rw [h0, Nat.mul_zero] at hmm; omega
      | inr h1 => exact h1
    unfold F
    refine oddPart_unique (k := k) hx ?_
    rw [← hdx, ← Nat.add_mul, hdk]

/-- ORBIT TRANSPORT: the whole (a,c)-orbit of c·y is c times the (a,1)-orbit
    of y — the qx+1 system embeds in every qx+c system, rescaled by c. -/
theorem F_orbit_scaling {c : Nat} (hc : c % 2 = 1) (a : Nat) :
    ∀ (n y : Nat), iterN (F a c) n (c * y) = c * iterN (F a 1) n y
  | 0, _ => rfl
  | n + 1, y => by
    have h := F_scaling hc a 1 y
    rw [Nat.mul_one] at h
    show iterN (F a c) n (F a c (c * y)) = c * iterN (F a 1) n (F a 1 y)
    rw [h]
    exact F_orbit_scaling hc a n (F a 1 y)

/-- PERIODICITY TRANSPORT (both directions): c·y is n-periodic under F_{a,c}
    ↔ y is n-periodic under F_{a,1}.  Every ax+1 cycle is a universal cycle
    family; conversely nothing new appears on the c-divisible sublattice. -/
theorem F_periodic_transport {c : Nat} (hc : c % 2 = 1) (a n y : Nat) :
    iterN (F a c) n (c * y) = c * y ↔ iterN (F a 1) n y = y := by
  rw [F_orbit_scaling hc a n y]
  constructor
  · exact fun h => Nat.eq_of_mul_eq_mul_left (by omega : 0 < c) h
  · intro h; rw [h]

/-- a = 5 (NOT Mersenne): every 5x+c system has the two-cycle {c, 3c}.
    Universal families are not exclusive to a = 2^k − 1 — they come from
    any ax+1 cycle; a = 5 contributes {1,3}. -/
theorem five_universal_two_cycle {c : Nat} (hc : c % 2 = 1) :
    F 5 c c = 3 * c ∧ F 5 c (3 * c) = c := by
  constructor
  · rw [F_formula hc,
        oddPart_unique (m := 3) (k := 1) (by decide) (by decide : (5:Nat) + 1 = 2 ^ 1 * 3)]
  · have h := F_scaling hc 5 1 3
    rw [Nat.mul_one] at h
    rw [Nat.mul_comm 3 c, h,
        show F 5 1 3 = 1 from
          oddPart_unique (by decide) (by decide : (5:Nat) * 3 + 1 = 2 ^ 4 * 1),
        Nat.mul_one]

/-- a = 181: every 181x+c system has the two-cycle {27c, 611c} — the
    classical 181x+1 cycle {27, 611}, transported to all odd c. -/
theorem oneEightyOne_universal_two_cycle {c : Nat} (hc : c % 2 = 1) :
    F 181 c (27 * c) = 611 * c ∧ F 181 c (611 * c) = 27 * c := by
  have h1 := F_scaling hc 181 1 27
  have h2 := F_scaling hc 181 1 611
  rw [Nat.mul_one] at h1 h2
  constructor
  · rw [Nat.mul_comm 27 c, h1,
        show F 181 1 27 = 611 from
          oddPart_unique (by decide) (by decide : (181:Nat) * 27 + 1 = 2 ^ 3 * 611),
        Nat.mul_comm c 611]
  · rw [Nat.mul_comm 611 c, h2,
        show F 181 1 611 = 27 from
          oddPart_unique (by decide) (by decide : (181:Nat) * 611 + 1 = 2 ^ 12 * 27),
        Nat.mul_comm c 27]

/-- T-form of the master formula: writing a+1 = 2^k·m (m odd), the raw
    T-orbit of c reaches m·c in exactly k+1 steps.  Theorem 4 is m = 1. -/
theorem generalized_universal_step {a c m : Nat} (k : Nat)
    (ha : a + 1 = 2 ^ k * m) (hc : c % 2 = 1) :
    iterN (T a c) (k + 1) c = m * c := by
  have h1 : T a c c = 2 ^ k * (m * c) := by
    unfold T
    rw [if_pos hc, show a * c + c = (a + 1) * c by rw [Nat.add_mul, Nat.one_mul],
        ha, Nat.mul_assoc]
  show iterN (T a c) k (T a c c) = m * c
  rw [h1]
  exact halve_iter a c k (m * c)

/-- Fixed points of F are genuine T-cycles: a·x + c = 2^k·x with x odd gives
    a (k+1)-step cycle of the raw map through x. -/
theorem F_fix_realizes_T {a c x k : Nat} (hx : x % 2 = 1)
    (hk : a * x + c = 2 ^ k * x) : iterN (T a c) (k + 1) x = x := by
  have h1 : T a c x = 2 ^ k * x := by unfold T; rw [if_pos hx]; exact hk
  show iterN (T a c) k (T a c x) = x
  rw [h1]
  exact halve_iter a c k x

/- Kernel-checked instances of the transported cycles (raw T map, `decide`). -/
example : iterN (T 5 7) 7 7 = 7 := by decide        -- {c,3c} family, c=7
example : iterN (T 5 9) 7 9 = 9 := by decide        -- {c,3c} family, c=9
example : iterN (T 181 1) 17 27 = 27 := by decide   -- 181x+1 cycle {27,611}
example : iterN (T 181 7) 17 189 = 189 := by decide -- transported: {189,4277}

#print axioms F_formula
#print axioms universal_fixed_iff
#print axioms fix_classification
#print axioms F_orbit_scaling
#print axioms F_periodic_transport
#print axioms five_universal_two_cycle
#print axioms oneEightyOne_universal_two_cycle
#print axioms generalized_universal_step
