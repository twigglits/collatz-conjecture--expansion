/-
  Arithmetic for docs/MASK-SPAN-BOUND.md. Standalone Lean 4.
  Kernel proofs only. Real logarithms, circle-rotation counting, and the
  assembly of the cycle-span theorem remain written arguments.
-/
namespace MaskSpanBounds

set_option exponentiation.threshold 30000
set_option maxRecDepth 60000

theorem span_implies_narrow (m M : Nat) (hm : 2 ≤ m)
    (hspan : 20 * M ≤ 49 * m) : 3 * M + 1 < 8 * m := by omega

/-- The binary phase of an interior odd-step boundary is the complement
    of its halving-rank residue. All divisions are exact natural operations. -/
theorem boundary_phase (k N i : Nat) (hk : 0 < k) (hkN : k < N) (hi : 0 < i)
    (hj : 0 < i * N % k) :
    ((i * N / k) * k) % N = N - i * N % k := by
  have hr := Nat.mod_lt (i * N) hk
  have he := Nat.mod_add_div (i * N) k
  have hi' : i = (i - 1) + 1 := by omega
  have hp : i * N = (i - 1) * N + N := calc
    i * N = ((i - 1) + 1) * N := congrArg (fun j => j * N) hi'
    _ = (i - 1) * N + N := by rw [Nat.add_mul, Nat.one_mul]
  have hform : (i * N / k) * k = (N - i * N % k) + (i - 1) * N := by
    rw [Nat.mul_comm (i * N / k) k]
    omega
  rw [hform, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- Distinct increasing integer grid labels consume at least one unit
    per point, including labels lifted across the circular seam. -/
theorem integer_grid_spacing (s : Nat) (z : Nat → Int)
    (hz : ∀ i, i + 1 < s → z i < z (i + 1))
    (j : Nat) (hj : j < s) : z 0 + (j : Int) ≤ z j := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hp := ih (by omega)
      have hstep := hz j hj
      omega

/-- A lifted grid arc shorter than b grid spacings contains at most b
    points. The real perturbation-to-arc step is written in the note. -/
theorem integer_grid_count (s b : Nat) (z : Nat → Int) (hs : 0 < s)
    (hz : ∀ i, i + 1 < s → z i < z (i + 1))
    (D : Int) (hD : 0 < D)
    (hspan : D * (z (s - 1) - z 0) < D * (b : Int)) : s ≤ b := by
  have hp := integer_grid_spacing s z hz (s - 1) (by omega)
  have hd := (Int.mul_lt_mul_left hD).mp hspan
  omega

def count (a : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => count a start n + if a (start + n) then 1 else 0

theorem count_add (a : Nat → Bool) (start n r : Nat) :
    count a start (n + r) = count a start n + count a (start + n) r := by
  induction r with
  | zero => simp [count]
  | succ r ih =>
      change count a start (n + r) + (if a (start + (n + r)) then 1 else 0) =
        count a start n +
          (count a (start + n) r + (if a ((start + n) + r) then 1 else 0))
      rw [ih]
      simp only [Nat.add_assoc]

theorem count_mono (a : Nat → Bool) (start n r : Nat) (hn : n ≤ r) :
    count a start n ≤ count a start r := by
  have he : r = n + (r - n) := by omega
  rw [he, count_add]
  omega

theorem whole_blocks (a : Nat → Bool) (q cap : Nat)
    (hc : ∀ start, count a start q ≤ cap) (t start : Nat) :
    count a start (q * t) ≤ cap * t := by
  induction t generalizing start with
  | zero => simp [count]
  | succ t ih =>
      rw [Nat.mul_succ, count_add, Nat.mul_succ]
      exact Nat.add_le_add (ih start) (hc (start + q * t))

/-- Any uniform q-window cap extends to every window, including a
    shorter final block. No periodicity of a is assumed. -/
theorem partial_blocks (a : Nat → Bool) (q cap : Nat) (hq : 0 < q)
    (hc : ∀ start, count a start q ≤ cap) (n start : Nat) :
    count a start n ≤ cap * (n / q + 1) := by
  have hn : n = q * (n / q) + n % q := by
    have := Nat.mod_add_div n q
    omega
  have hr := count_mono a (start + q * (n / q)) (n % q) q
    (Nat.le_of_lt (Nat.mod_lt n hq))
  have hb := Nat.le_trans hr (hc (start + q * (n / q)))
  calc
    count a start n = count a start (q * (n / q) + n % q) :=
      congrArg (count a start) hn
    _ = count a start (q * (n / q)) + count a (start + q * (n / q)) (n % q) :=
      count_add a start _ _
    _ ≤ cap * (n / q) + cap :=
      Nat.add_le_add (whole_blocks a q cap hc (n / q) start) hb
    _ = cap * (n / q + 1) := by rw [Nat.mul_add, Nat.mul_one]

theorem logarithm_power_inputs :
    (49 : Nat)^200 < 40^200 * 3^37 ∧
    3^15601 < 2^24727 ∧ 2^1054 < 3^665 ∧
    665 * 24727 = 15601 * 1054 + 1 ∧
    665 * 485 = 306 * 1054 + 1 ∧ Nat.gcd 665 1054 = 1 := by decide

/-- W=185001/10^6, epsilon=1/10^7, q=1054.
    q*W + 2*q^2*epsilon < 196, with denominators cleared. -/
theorem grid_and_density_constants :
    (10^8 : Nat) < 9 * 1054 * 24727 ∧
    1054 * 185001 * 10 + 2 * 1054^2 < 196 * 10^7 ∧
    16 * 196 < 3 * 1054 ∧ 3 * 26 = 39 * 2 ∧
    16 * 196 + 3 * 5 < 16 * 197 := by decide

theorem block_exponent (n : Nat) (hnpos : 0 < n) :
    16 * (196 * (n / 1054 + 1)) < 3 * n + 16 * 196 := by
  have hd := Nat.mod_add_div n 1054
  have hr := Nat.mod_lt n (by decide : 0 < 1054)
  by_cases hn : n < 1054
  · have : n / 1054 = 0 := Nat.div_eq_of_lt hn
    simp only [this, Nat.zero_add, Nat.mul_one]
    omega
  · have hp : 0 < n / 1054 := Nat.div_pos (by omega) (by decide)
    omega

theorem cutoff_constants :
    (72 : Nat) * 12000^2 < 2^34 ∧ 197 + 34 < 300 ∧
    40 * 300 = 12000 ∧ 160 < 12000 ∧ 2^12000 < 10^4000 ∧
    10^8 < 2^64 ∧ 8 * 10^6 < (10^8)^2 := by decide

#print axioms span_implies_narrow
#print axioms boundary_phase
#print axioms integer_grid_spacing
#print axioms integer_grid_count
#print axioms count_add
#print axioms whole_blocks
#print axioms partial_blocks
#print axioms logarithm_power_inputs
#print axioms grid_and_density_constants
#print axioms block_exponent
#print axioms cutoff_constants
end MaskSpanBounds
