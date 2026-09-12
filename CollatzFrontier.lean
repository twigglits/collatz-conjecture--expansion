/-
  CollatzFrontier.lean — new machine-checked angles on the generalized
  Collatz family   T_{a,c}(n) = a*n + c  (n odd),  n/2  (n even),
  accelerated map  F_{a,c}(x) = oddPart (a*x + c).

  Four angles, each proved for ALL parameters with kernel-only proofs
  (no Mathlib, no extra axioms) — except the counting certificates
  marked `native_decide`, which trust Lean's compiler exactly as the
  range certificates of CollatzCerts.lean do:

  §1  BÖHM–SONTACCHI, PROVED.  The paper's Proposition 5 was verified on
      the 89 discovered cycles; here it becomes a theorem for every cycle
      of every (a,c): the orbit formula
          F^n(x) * 2^(S n x) = a^n * x + c * (W n x),
      the cycle equation (additive and subtractive forms), and the
      corollary that every cycle lives above the drift line: 2^H > a^k.

  §2  REPULSION (dual of CollatzTheory's absorption): if p ∣ a and p ∤ c,
      then after the first odd step NO iterate is divisible by p.
      Collatz instance: no T_{3,1}-iterate is a multiple of 3.

  §3  COSET CONFINEMENT: every value of the accelerated map lies in the
      coset c·⟨2⟩ (mod a).  For a = 7 the orbit occupies only the
      index-2 subgroup {1,2,4} of (ℤ/7)ˣ — a constraint on every orbit
      tail and every cycle inventory of every 7x+c system.

  §4  FINITE TERRAS DESCENT (density angle — the first statement in this
      repository about a positive fraction of ALL integers).  The
      shortcut map U(n) = (3n+1)/2 (n odd), n/2 (n even) satisfies the
      affine decomposition  U^k(2^k q + s) = 3^(wt k s) * q + U^k(s),
      so the first k steps depend only on n mod 2^k.  Call a residue s
      GOOD at level k if 3^(wt k s) < 2^k.  Then every n ≥ 8^k in a good
      class satisfies U^k(n) < n — descent below the start within k
      shortcut steps.  Certified counts of good residues:
        219/256 at k = 8,   58651/65536 at k = 16,
        910596/1048576 (86.84 %) at k = 20.
      (Terras 1976 in the limit k → ∞; each finite level is a theorem
      about all n ≥ 8^k at once, not a finite check.)

  Check with:  lean CollatzFrontier.lean    (Lean 4.31.0, no dependencies)
-/

set_option maxRecDepth 100000

/-- One step of the generalized Collatz map. -/
def T (a c n : Nat) : Nat := if n % 2 = 1 then a * n + c else n / 2

/-- `iterN f k x` = k-fold application of `f` to `x`. -/
def iterN (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     x => x
  | k + 1, x => iterN f k (f x)

/-- Odd part of n (convention oddPart 0 = 0). -/
def oddPart (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then oddPart (n / 2) else n
termination_by n
decreasing_by omega

/-- 2-adic valuation of n (convention v2 0 = 0). -/
def v2 (n : Nat) : Nat :=
  if h : n % 2 = 0 ∧ n ≠ 0 then v2 (n / 2) + 1 else 0
termination_by n
decreasing_by omega

/-- The accelerated odd→odd map: one odd step, then all halvings at once. -/
def F (a c x : Nat) : Nat := oddPart (a * x + c)

/- ==== small self-contained arithmetic helpers (no Mathlib) ==== -/

theorem pow_pos' {a : Nat} (ha : 0 < a) : ∀ n : Nat, 0 < a ^ n
  | 0 => by rw [Nat.pow_zero]; omega
  | n + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow_pos' ha n) ha

theorem mul_pow' (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => by rw [Nat.pow_zero, Nat.pow_zero, Nat.pow_zero, Nat.mul_one]
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow' a b n,
        Nat.mul_assoc, Nat.mul_assoc, Nat.mul_left_comm (b ^ n) a b]

theorem oddPart_odd {n : Nat} (hn : n % 2 = 1) : oddPart n = n := by
  rw [oddPart.eq_def, dif_neg (by omega : ¬(n % 2 = 0 ∧ n ≠ 0))]

theorem oddPart_even {n : Nat} (h0 : n ≠ 0) (he : n % 2 = 0) :
    oddPart n = oddPart (n / 2) := by
  rw [oddPart.eq_def, dif_pos ⟨he, h0⟩]

theorem v2_odd {n : Nat} (hn : n % 2 = 1) : v2 n = 0 := by
  rw [v2.eq_def, dif_neg (by omega : ¬(n % 2 = 0 ∧ n ≠ 0))]

theorem v2_even {n : Nat} (h0 : n ≠ 0) (he : n % 2 = 0) :
    v2 n = v2 (n / 2) + 1 := by
  rw [v2.eq_def, dif_pos ⟨he, h0⟩]

/-- Fundamental factorization with the explicit exponent: 2^(v2 n) · oddPart n = n. -/
theorem pow_v2_oddPart (n : Nat) (hne : n ≠ 0) : 2 ^ v2 n * oddPart n = n := by
  have key : ∀ b m, m ≤ b → m ≠ 0 → 2 ^ v2 m * oddPart m = m := by
    intro b
    induction b with
    | zero => intro m hle hme; exact absurd (Nat.le_zero.mp hle) hme
    | succ b ih =>
      intro m hle hme
      by_cases hpar : m % 2 = 1
      · rw [v2_odd hpar, oddPart_odd hpar, Nat.pow_zero, Nat.one_mul]
      · have he : m % 2 = 0 := by omega
        have hne2 : m / 2 ≠ 0 := by omega
        have hle2 : m / 2 ≤ b := by omega
        have ihh := ih (m / 2) hle2 hne2
        rw [v2_even hme he, oddPart_even hme he, Nat.pow_succ]
        have h2 : 2 ^ v2 (m / 2) * 2 * oddPart (m / 2)
                = 2 * (2 ^ v2 (m / 2) * oddPart (m / 2)) := by
          rw [Nat.mul_comm (2 ^ v2 (m / 2)) 2, Nat.mul_assoc]
        rw [h2, ihh]
        omega
  exact key n n (Nat.le_refl n) hne

/-- One accelerated step, multiplicatively:  2^h · F(x) = a·x + c,  h = v2(ax+c). -/
theorem F_step (a c x : Nat) (hc : 0 < c) :
    2 ^ v2 (a * x + c) * F a c x = a * x + c :=
  pow_v2_oddPart (a * x + c) (by omega)

/- ====================================================================
   1. BÖHM–SONTACCHI FOR ALL PARAMETERS
      S n x = total halvings over the first n accelerated steps from x;
      W n x = the cycle-equation weight (head-recursive form).  The
      orbit formula upgrades the paper's Proposition 5 from an
      89-instance check to a theorem quantified over everything.
   ==================================================================== -/

/-- Total halvings over the first n accelerated steps from x. -/
def S (a c : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, x => v2 (a * x + c) + S a c n (F a c x)

/-- Böhm–Sontacchi weight over the first n accelerated steps from x:
    W(0,x) = 0,  W(n+1,x) = a^n + 2^{h₀}·W(n, F x)  with h₀ = v2(ax+c).
    (Unfolds to  W(k,x) = Σ_{i<k} a^{k-1-i} 2^{h₀+⋯+h_{i-1}}.) -/
def W (a c : Nat) : Nat → Nat → Nat
  | 0,     _ => 0
  | n + 1, x => a ^ n + 2 ^ v2 (a * x + c) * W a c n (F a c x)

/-- ORBIT FORMULA:  F^n(x) · 2^(S n x) = a^n · x + c · (W n x),  for ALL a, x
    (a may be even or zero; only c ≥ 1 is used). -/
theorem orbit_formula {a c : Nat} (hc : 0 < c) :
    ∀ (n x : Nat), iterN (F a c) n x * 2 ^ S a c n x = a ^ n * x + c * W a c n x
  | 0, x => by
    show x * 2 ^ (0:Nat) = a ^ 0 * x + c * 0
    rw [Nat.pow_zero, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_zero,
        Nat.add_zero]
  | n + 1, x => by
    have hstep : 2 ^ v2 (a * x + c) * F a c x = a * x + c := F_step a c x hc
    have ih := orbit_formula (a := a) hc n (F a c x)
    show iterN (F a c) n (F a c x) * 2 ^ (v2 (a * x + c) + S a c n (F a c x))
       = a ^ (n + 1) * x + c * (a ^ n + 2 ^ v2 (a * x + c) * W a c n (F a c x))
    calc iterN (F a c) n (F a c x) * 2 ^ (v2 (a * x + c) + S a c n (F a c x))
        = iterN (F a c) n (F a c x)
            * (2 ^ S a c n (F a c x) * 2 ^ v2 (a * x + c)) := by
          rw [Nat.pow_add,
              Nat.mul_comm (2 ^ v2 (a * x + c)) (2 ^ S a c n (F a c x))]
      _ = iterN (F a c) n (F a c x) * 2 ^ S a c n (F a c x)
            * 2 ^ v2 (a * x + c) := by
          rw [← Nat.mul_assoc]
      _ = (a ^ n * F a c x + c * W a c n (F a c x)) * 2 ^ v2 (a * x + c) := by
          rw [ih]
      _ = a ^ n * F a c x * 2 ^ v2 (a * x + c)
            + c * W a c n (F a c x) * 2 ^ v2 (a * x + c) := by
          rw [Nat.add_mul]
      _ = a ^ n * (2 ^ v2 (a * x + c) * F a c x)
            + c * (2 ^ v2 (a * x + c) * W a c n (F a c x)) := by
          rw [Nat.mul_assoc (a ^ n), Nat.mul_assoc c,
              Nat.mul_comm (F a c x) (2 ^ v2 (a * x + c)),
              Nat.mul_comm (W a c n (F a c x)) (2 ^ v2 (a * x + c))]
      _ = a ^ n * (a * x + c)
            + c * (2 ^ v2 (a * x + c) * W a c n (F a c x)) := by
          rw [hstep]
      _ = a ^ (n + 1) * x
            + c * (a ^ n + 2 ^ v2 (a * x + c) * W a c n (F a c x)) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.pow_succ, ← Nat.mul_assoc,
              Nat.mul_comm (a ^ n) c]
          omega

/-- CYCLE EQUATION (Böhm–Sontacchi 1978), additive (subtraction-free) form,
    now a theorem for every cycle of every (a,c):  a k-cycle through x
    satisfies  x · 2^H = a^k · x + c · W  with H = S k x. -/
theorem cycle_equation {a c x k : Nat} (hc : 0 < c)
    (hcyc : iterN (F a c) k x = x) :
    x * 2 ^ S a c k x = a ^ k * x + c * W a c k x := by
  have h := orbit_formula (a := a) hc k x
  rw [hcyc] at h
  exact h

theorem W_pos {a c : Nat} (ha : 0 < a) (n x : Nat) : 0 < W a c (n + 1) x := by
  show 0 < a ^ n + 2 ^ v2 (a * x + c) * W a c n (F a c x)
  have := pow_pos' ha n
  omega

/-- EVERY CYCLE LIVES ABOVE THE DRIFT LINE:  2^H > a^k.  Halvings must
    strictly outrun the multiplier — the integer form of H/k > log₂ a.
    Previously observed on the 89 discovered cycles; now forced. -/
theorem cycle_expansion {a c x k : Nat} (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < k) (hcyc : iterN (F a c) k x = x) :
    a ^ k < 2 ^ S a c k x := by
  have heq := cycle_equation hc hcyc
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hW : 0 < W a c (m + 1) x := W_pos ha m x
  have hcW : 0 < c * W a c (m + 1) x := Nat.mul_pos hc hW
  have h1 : x * a ^ (m + 1) < x * 2 ^ S a c (m + 1) x := by
    have hcomm : x * a ^ (m + 1) = a ^ (m + 1) * x := Nat.mul_comm x (a ^ (m + 1))
    omega
  exact Nat.lt_of_mul_lt_mul_left h1

/-- Subtractive form — exactly the paper's Proposition 5:
        x · (2^H − a^k) = c · W. -/
theorem cycle_equation_sub {a c x k : Nat} (ha : 0 < a) (hc : 0 < c)
    (hk : 0 < k) (hcyc : iterN (F a c) k x = x) :
    x * (2 ^ S a c k x - a ^ k) = c * W a c k x := by
  have heq := cycle_equation hc hcyc
  have hle : a ^ k ≤ 2 ^ S a c k x :=
    Nat.le_of_lt (cycle_expansion ha hc hk hcyc)
  have h1 : 2 ^ S a c k x - a ^ k + a ^ k = 2 ^ S a c k x :=
    Nat.sub_add_cancel hle
  have h2 : x * (2 ^ S a c k x - a ^ k) + a ^ k * x = x * 2 ^ S a c k x := by
    rw [Nat.mul_comm (a ^ k) x, ← Nat.mul_add, h1]
  omega

/- ====================================================================
   2. REPULSION — dual of CollatzTheory's absorption theorem.
      Absorption: p ∣ a, p ∣ c  ⇒  orbits are trapped in pℤ.
      Repulsion:  p ∣ a, p ∤ c  ⇒  orbits are EXPELLED from pℤ:
      after the first odd step no iterate is divisible by p, ever.
      Together they settle the mod-p fate of every orbit for every p ∣ a.
   ==================================================================== -/

theorem repel_entry {p a c n : Nat} (hpa : p ∣ a) (hpc : ¬ p ∣ c)
    (hn : n % 2 = 1) : ¬ p ∣ T a c n := by
  unfold T
  rw [if_pos hn]
  intro hdvd
  obtain ⟨s, rfl⟩ := hpa
  have h1 : p ∣ p * s * n := ⟨s * n, by rw [Nat.mul_assoc]⟩
  have h2 : p ∣ p * s * n + c - p * s * n := Nat.dvd_sub hdvd h1
  rw [Nat.add_sub_cancel_left] at h2
  exact hpc h2

theorem repel_step {p a c n : Nat} (hpa : p ∣ a) (hpc : ¬ p ∣ c)
    (hn : ¬ p ∣ n) : ¬ p ∣ T a c n := by
  by_cases hpar : n % 2 = 1
  · exact repel_entry hpa hpc hpar
  · unfold T
    rw [if_neg hpar]
    intro hdvd
    obtain ⟨t, ht⟩ := hdvd
    have h2 : n = 2 * (p * t) := by omega
    exact hn ⟨2 * t, by rw [h2, Nat.mul_left_comm]⟩

theorem repel_iter {p a c : Nat} (hpa : p ∣ a) (hpc : ¬ p ∣ c) :
    ∀ (k n : Nat), ¬ p ∣ n → ¬ p ∣ iterN (T a c) k n
  | 0, _, h => h
  | k + 1, n, h => repel_iter hpa hpc k (T a c n) (repel_step hpa hpc h)

/-- REPULSION: if p divides a but not c, then from any odd start the orbit
    leaves pℤ at the first step and never returns. -/
theorem repel_orbit {p a c n : Nat} (hpa : p ∣ a) (hpc : ¬ p ∣ c)
    (hn : n % 2 = 1) (k : Nat) : ¬ p ∣ iterN (T a c) (k + 1) n :=
  repel_iter hpa hpc k (T a c n) (repel_entry hpa hpc hn)

/-- Collatz instance: after the first odd step, no iterate of T_{3,1} is
    divisible by 3 — every orbit lives in the residues {1,2} mod 3. -/
theorem collatz_avoids_3Z {n : Nat} (hn : n % 2 = 1) (k : Nat) :
    ¬ 3 ∣ iterN (T 3 1) (k + 1) n :=
  repel_orbit ⟨1, rfl⟩ (fun ⟨t, ht⟩ => by omega) hn k

/- ====================================================================
   3. COSET CONFINEMENT — a multiplicative constraint mod a.
      2^h · F(x) = a·x + c ≡ c (mod a): every image of the accelerated
      map lies in the coset c·⟨2⟩ of the subgroup generated by 2 in
      (ℤ/a)ˣ.  When ⟨2⟩ is proper (a = 7: ⟨2⟩ = {1,2,4}, index 2), this
      excludes half the unit residues from every orbit tail and every
      cycle inventory — a constraint invisible to parity/divisibility.
   ==================================================================== -/

theorem F_image_coset {a c : Nat} (hc : 0 < c) (x : Nat) :
    F a c x * 2 ^ v2 (a * x + c) % a = c % a := by
  rw [Nat.mul_comm (F a c x) (2 ^ v2 (a * x + c)), F_step a c x hc,
      Nat.add_comm (a * x) c]
  exact Nat.add_mul_mod_self_left c a x

theorem iterN_succ_right (f : Nat → Nat) :
    ∀ (k x : Nat), iterN f (k + 1) x = f (iterN f k x)
  | 0, _ => rfl
  | k + 1, x => iterN_succ_right f k (f x)

/-- Every iterate (≥ 1 accelerated step) lies in c·⟨2⟩ (mod a). -/
theorem orbit_coset {a c : Nat} (hc : 0 < c) (x m : Nat) :
    ∃ j, iterN (F a c) (m + 1) x * 2 ^ j % a = c % a := by
  rw [iterN_succ_right]
  exact ⟨v2 (a * iterN (F a c) m x + c), F_image_coset hc _⟩

theorem two_pow_mod7 : ∀ h : Nat, 2 ^ h % 7 = 1 ∨ 2 ^ h % 7 = 2 ∨ 2 ^ h % 7 = 4
  | 0 => by decide
  | h + 1 => by
    have ih := two_pow_mod7 h
    have hm := Nat.mul_mod (2 ^ h) 2 7
    rw [Nat.pow_succ]
    omega

/-- 7x+1 flavor: every accelerated iterate is ≡ 1, 2, or 4 (mod 7) — orbits
    occupy only the index-2 subgroup ⟨2⟩ ⊆ (ℤ/7)ˣ.  (The committed
    inventories obey this: e.g. the (7,5) minima 3, 5, 27 are ≡ 3, 5, 6
    (mod 7), i.e. 5·{1,2,4}; the (7,11) minima 11, 23 are ≡ 4, 2, i.e.
    11·{1,2,4} = {4,1,2}.) -/
theorem sevenX1_iterates_mod7 (x m : Nat) :
    iterN (F 7 1) (m + 1) x % 7 = 1 ∨ iterN (F 7 1) (m + 1) x % 7 = 2 ∨
    iterN (F 7 1) (m + 1) x % 7 = 4 := by
  obtain ⟨j, hj⟩ := orbit_coset (a := 7) (c := 1) (by omega) x m
  have hmul := Nat.mul_mod (iterN (F 7 1) (m + 1) x) (2 ^ j) 7
  obtain h | h | h := two_pow_mod7 j <;> rw [h] at hmul <;> omega

/- ====================================================================
   4. FINITE TERRAS DESCENT — the density angle.
      U is the shortcut map, wt k s the parity-vector weight of s over k
      steps.  The affine decomposition shows the first k steps see only
      n mod 2^k; good residues force descent for EVERY n ≥ 8^k at once.
      This is the k-th finite level of Terras' theorem ("almost all n
      have finite stopping time"), machine-certified.
   ==================================================================== -/

/-- The shortcut ("Terras") Collatz map. -/
def U (n : Nat) : Nat := if n % 2 = 1 then (3 * n + 1) / 2 else n / 2

/-- Parity-vector weight: number of odd steps among the first k U-steps from s. -/
def wt : Nat → Nat → Nat
  | 0,     _ => 0
  | k + 1, s => s % 2 + wt k (U s)

/-- AFFINE DECOMPOSITION at level k, for ALL q and s (no bounds needed):
        U^k (2^k·q + s) = 3^(wt k s) · q + U^k(s).
    The high part q rides along, tripled once per odd step of s: the
    first k steps of the orbit depend only on the residue s. -/
theorem U_affine : ∀ (k q s : Nat),
    iterN U k (2 ^ k * q + s) = 3 ^ wt k s * q + iterN U k s
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
      show iterN U k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + iterN U k (U s)
      rw [hU1, U_affine k (3 * q) (U s), hw, Nat.pow_add, Nat.pow_one,
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
      show iterN U k (U (2 ^ (k + 1) * q + s)) = 3 ^ wt (k + 1) s * q + iterN U k (U s)
      rw [hU1, U_affine k q (U s), hw]

theorem U_le (n : Nat) : U n ≤ 2 * n := by
  unfold U
  by_cases h : n % 2 = 1
  · rw [if_pos h]; omega
  · rw [if_neg h]; omega

theorem iterN_U_le : ∀ (k s : Nat), iterN U k s ≤ 2 ^ k * s
  | 0, s => by
    show s ≤ 2 ^ (0:Nat) * s
    rw [Nat.pow_zero, Nat.one_mul]
    exact Nat.le_refl s
  | k + 1, s => by
    show iterN U k (U s) ≤ 2 ^ (k + 1) * s
    have h1 := iterN_U_le k (U s)
    have h2 := U_le s
    have h3 : 2 ^ k * U s ≤ 2 ^ k * (2 * s) :=
      Nat.mul_le_mul_left (2 ^ k) h2
    have h4 : 2 ^ (k + 1) * s = 2 ^ k * (2 * s) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    omega

/-- FINITE TERRAS DESCENT: if the residue s is GOOD at level k, i.e.
    3^(wt k s) < 2^k, then EVERY n = 2^k·q + s with q ≥ 4^k satisfies
    U^k(n) < n — one theorem per good residue covers infinitely many n. -/
theorem descent {k s q : Nat} (hs : s < 2 ^ k) (hgood : 3 ^ wt k s < 2 ^ k)
    (hq : 4 ^ k ≤ q) : iterN U k (2 ^ k * q + s) < 2 ^ k * q + s := by
  rw [U_affine]
  have h2pos : 0 < 2 ^ k := pow_pos' (by omega) k
  have hUs : iterN U k s ≤ 2 ^ k * s := iterN_U_le k s
  have h4 : (4:Nat) ^ k = 2 ^ k * 2 ^ k := by
    rw [show (4:Nat) = 2 * 2 from rfl, mul_pow']
  have hmono : 2 ^ k * (s + 1) ≤ 2 ^ k * 2 ^ k :=
    Nat.mul_le_mul_left (2 ^ k) (by omega : s + 1 ≤ 2 ^ k)
  have hdistr : 2 ^ k * (s + 1) = 2 ^ k * s + 2 ^ k := by
    rw [Nat.mul_add, Nat.mul_one]
  have hkey : (3 ^ wt k s + 1) * q ≤ 2 ^ k * q :=
    Nat.mul_le_mul_right q (by omega : 3 ^ wt k s + 1 ≤ 2 ^ k)
  have hexp : (3 ^ wt k s + 1) * q = 3 ^ wt k s * q + q := by
    rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Descent, stated for every large n directly: if n ≥ 8^k and the residue
    n mod 2^k is good at level k, then U^k(n) < n. -/
theorem descent_all {k : Nat} (n : Nat) (h8 : 8 ^ k ≤ n)
    (hgood : 3 ^ wt k (n % 2 ^ k) < 2 ^ k) : iterN U k n < n := by
  have h2pos : 0 < 2 ^ k := pow_pos' (by omega) k
  have hsplit : 2 ^ k * (n / 2 ^ k) + n % 2 ^ k = n := Nat.div_add_mod n (2 ^ k)
  have hs : n % 2 ^ k < 2 ^ k := Nat.mod_lt n h2pos
  have h8' : (8:Nat) ^ k = 2 ^ k * 4 ^ k := by
    rw [show (8:Nat) = 2 * 4 from rfl, mul_pow']
  have hq : 4 ^ k ≤ n / 2 ^ k := by
    have hd : 2 ^ k * (n / 2 ^ k + 1) = 2 ^ k * (n / 2 ^ k) + 2 ^ k := by
      rw [Nat.mul_add, Nat.mul_one]
    have hlt : 2 ^ k * 4 ^ k < 2 ^ k * (n / 2 ^ k + 1) := by omega
    have := Nat.lt_of_mul_lt_mul_left hlt
    omega
  have h := descent hs hgood hq
  rw [hsplit] at h
  exact h

/- ==== counted good-residue certificates ==== -/

/-- Tail-recursive count of good residues below the second argument. -/
def cgAux (k : Nat) : Nat → Nat → Nat
  | acc, 0     => acc
  | acc, s + 1 => cgAux k (if 3 ^ wt k s < 2 ^ k then acc + 1 else acc) s

/-- Number of good residues at level k. -/
def countGood (k : Nat) : Nat := cgAux k 0 (2 ^ k)

/-- 219 of the 256 residue classes mod 2^8 are good (85.5 %): every n ≥ 8^8
    in one of them descends within 8 shortcut steps.  Kernel-checked. -/
theorem countGood_8 : countGood 8 = 219 := by decide

/-- 58651/65536 good classes at level 16 (89.5 %). -/
theorem countGood_16 : countGood 16 = 58651 := by native_decide

/-- 910596/1048576 good classes at level 20 (86.84 %): at least 86.84 % of
    every aligned block of 2^20 consecutive integers ≥ 8^20 descend below
    their start within 20 shortcut steps. -/
theorem countGood_20 : countGood 20 = 910596 := by native_decide

/- Kernel-checked flavor instances. -/
example : (3:Nat) ^ wt 20 1 < 2 ^ 20 := by decide          -- residue 1 is good
example : ¬ (3:Nat) ^ wt 20 27 < 2 ^ 20 := by decide       -- 27 (famously slow) is not
example (q : Nat) (hq : 4 ^ 20 ≤ q) :                       -- descent live, ∀ q
    iterN U 20 (2 ^ 20 * q + 1) < 2 ^ 20 * q + 1 :=
  descent (by decide) (by decide) hq

#print axioms orbit_formula
#print axioms cycle_equation
#print axioms cycle_equation_sub
#print axioms cycle_expansion
#print axioms repel_orbit
#print axioms collatz_avoids_3Z
#print axioms orbit_coset
#print axioms sevenX1_iterates_mod7
#print axioms U_affine
#print axioms descent
#print axioms descent_all
#print axioms countGood_8
#print axioms countGood_20
