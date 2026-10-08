import CycleLocalLifts

/-
  Modular arithmetic for the rank form of critical mechanical masks.
  Kernel proofs only. The mechanical coefficient reindexing is described
  in docs/MASK-RANK-ARITHMETIC.md.
-/
namespace MaskRankArithmetic

def EqMod (D a b : Int) : Prop := D ∣ a-b

theorem eq_refl (D a : Int) : EqMod D a a := by
  exact ⟨0, by omega⟩

theorem eq_of_eq (D : Int) {a b : Int} (h : a=b) : EqMod D a b := by
  subst b
  exact eq_refl D a

theorem eq_symm {D a b : Int} (h : EqMod D a b) : EqMod D b a := by
  obtain ⟨x, hx⟩ := h
  exact ⟨-x, by grind⟩

theorem eq_trans {D a b c : Int} (h : EqMod D a b) (g : EqMod D b c) :
    EqMod D a c := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact ⟨x+y, by grind⟩

theorem eq_add {D a b c d : Int} (h : EqMod D a b) (g : EqMod D c d) :
    EqMod D (a+c) (b+d) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact ⟨x+y, by grind⟩

theorem eq_sub {D a b c d : Int} (h : EqMod D a b) (g : EqMod D c d) :
    EqMod D (a-c) (b-d) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact ⟨x-y, by grind⟩

theorem eq_mul {D a b c d : Int} (h : EqMod D a b) (g : EqMod D c d) :
    EqMod D (a*c) (b*d) := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨y, hy⟩ := g
  exact ⟨x*c+b*y, by grind⟩

theorem eq_pow {D a b : Int} (h : EqMod D a b) (n : Nat) :
    EqMod D (a^n) (b^n) := by
  induction n with
  | zero => simpa only [Int.pow_zero] using eq_refl D 1
  | succ n ih =>
      simpa only [Int.pow_succ] using eq_mul ih h

def UnitMod (D a : Int) : Prop := ∃ b : Int, EqMod D (a*b) 1

theorem unit_of_coprime (D a : Nat) (hg : Nat.gcd a D = 1) :
    UnitMod (D : Int) (a : Int) := by
  obtain ⟨x,y,he⟩ := CycleLocalLifts.bezout a D
  rw [hg] at he
  exact ⟨x, -y, by grind⟩

theorem unit_mul {D a b : Int} (ha : UnitMod D a) (hb : UnitMod D b) :
    UnitMod D (a*b) := by
  obtain ⟨u,hu⟩ := ha
  obtain ⟨v,hv⟩ := hb
  refine ⟨u*v, ?_⟩
  simpa only [Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
    using eq_mul hu hv

theorem unit_pow {D a : Int} (h : UnitMod D a) (n : Nat) :
    UnitMod D (a^n) := by
  induction n with
  | zero => exact ⟨1, by simpa using eq_refl D 1⟩
  | succ n ih =>
      simpa only [Int.pow_succ] using unit_mul ih h

theorem unit_cancel {D u a b : Int} (hu : UnitMod D u)
    (he : EqMod D (u*a) (u*b)) : EqMod D a b := by
  obtain ⟨v,hv⟩ := hu
  have ha : EqMod D ((u*a)*v) a := by
    simpa only [Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      using eq_mul (eq_refl D a) hv
  have hb : EqMod D ((u*b)*v) b := by
    simpa only [Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
      using eq_mul (eq_refl D b) hv
  exact eq_trans (eq_symm ha) (eq_trans (eq_mul he (eq_refl D v)) hb)

theorem unit_congr {D a b : Int} (he : EqMod D a b) (hb : UnitMod D b) :
    UnitMod D a := by
  obtain ⟨v,hv⟩ := hb
  exact ⟨v, eq_trans (eq_mul he (eq_refl D v)) hv⟩

theorem unit_coprime (D C : Nat) (hu : UnitMod (D : Int) (C : Int)) :
    Nat.gcd C D = 1 := by
  apply Nat.gcd_eq_one_iff.mpr
  intro d hdC hdD
  obtain ⟨v,w,hw⟩ := hu
  have hc : (d : Int) ∣ (C : Int)*v :=
    Int.dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdC)
  have hD : (d : Int) ∣ (D : Int)*w :=
    Int.dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdD)
  have he : (C : Int)*v-(D : Int)*w = 1 := by grind
  have hh : (d : Int) ∣ (1 : Int) := by
    rw [← he]
    exact Int.dvd_sub hc hD
  exact Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hh)

/-- Congruence roots are constructed using a genuine modular inverse.
    The two power relations and Bezout determinant remain explicit. -/
theorem count_roots (D z : Int) (k N q t : Nat)
    (h2 : UnitMod D 2) (h3 : UnitMod D 3)
    (hcounts : EqMod D (3^k) (2^N))
    (hbez : q*N = k*t+1) (hz : EqMod D ((3^q)*z) (2^t)) :
    EqMod D (2*z^k) 1 ∧ EqMod D (3*z^N) 1 := by
  have hk := eq_pow hz k
  have hq := eq_pow hcounts q
  have htk : t*k = k*t := Nat.mul_comm t k
  have hkq : k*q = q*k := Nat.mul_comm k q
  have hNq : N*q = k*t+1 := by rw [Nat.mul_comm N q]; exact hbez
  have hk' : EqMod D ((3^k)^q*z^k) (2^(k*t)) := by
    simpa only [Int.mul_pow, ← Int.pow_mul, htk, hkq] using hk
  have hA : EqMod D ((2^(k*t))*(2*z^k)) (2^(k*t)*1) := by
    have hc := eq_mul (eq_symm hq) (eq_refl D (z^k))
    have hh := eq_trans hc hk'
    simpa only [Int.mul_pow, ← Int.pow_mul, htk, hkq, hNq,
      Int.pow_succ, Int.mul_assoc, Int.mul_one] using hh
  have hN := eq_pow hz N
  have ht := eq_pow hcounts t
  have ht' : EqMod D ((2^t)^N) (3^(k*t)) := by
    simpa only [← Int.pow_mul, Nat.mul_comm t N] using eq_symm ht
  have hB : EqMod D ((3^(k*t))*(3*z^N)) (3^(k*t)*1) := by
    have hh := eq_trans hN ht'
    simpa only [Int.mul_pow, ← Int.pow_mul, hbez, Nat.mul_comm t N,
      Int.pow_succ, Int.mul_assoc, Int.mul_one] using hh
  exact ⟨unit_cancel (unit_pow h2 (k*t)) hA,
    unit_cancel (unit_pow h3 (k*t)) hB⟩

theorem monomial_inverse (D z : Int) (k N a b : Nat)
    (hk : EqMod D (2*z^k) 1) (hN : EqMod D (3*z^N) 1) :
    EqMod D ((3^a*2^b)*z^(N*a+k*b)) 1 := by
  have hh := eq_mul (eq_pow hN a) (eq_pow hk b)
  simpa only [Int.mul_pow, ← Int.pow_mul, Int.pow_add, Int.one_pow,
    Int.mul_one, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hh

/-- Monomials with neighboring mechanical ranks differ by a power of z.
    All exponents and their exact rank identity are explicit. -/
theorem monomial_rank (D z : Int) (k N a b a₀ b₀ j : Nat)
    (hk : EqMod D (2*z^k) 1) (hN : EqMod D (3*z^N) 1)
    (he : N*a+k*b+j = N*a₀+k*b₀) :
    EqMod D (3^a*2^b) ((3^a₀*2^b₀)*z^j) := by
  have hi := monomial_inverse D z k N a b hk hN
  have hzero := monomial_inverse D z k N a₀ b₀ hk hN
  have hu : UnitMod D (z^(N*a+k*b)) := by
    exact ⟨3^a*2^b, by simpa only [Int.mul_comm] using hi⟩
  have hz : EqMod D (((3^a₀*2^b₀)*z^j)*z^(N*a+k*b)) 1 := by
    have hid : ((3^a₀*2^b₀)*z^j)*z^(N*a+k*b) =
        (3^a₀*2^b₀)*z^(N*a₀+k*b₀) := by
      rw [Int.mul_assoc, ← Int.pow_add]
      have hj : j+(N*a+k*b) = N*a₀+k*b₀ := by omega
      rw [hj]
    rw [hid]
    exact hzero
  apply unit_cancel hu
  simpa only [Int.mul_comm] using eq_trans hi (eq_symm hz)

/-- For the cut after the first lower-mechanical symbol, rank zero has
    coefficient 2^(N-2). This checks the integer exponent bridge. -/
theorem cut_one_rank_identity (k N i S j a b : Nat)
    (ha : a+i+1 = k) (hb : b+1 = S)
    (hphase : k*S+j+k = N*(i+1)) (hN : 2 ≤ N) :
    N*a+k*b+j = k*(N-2) := by
  have hsub : N-2+2 = N := by omega
  grind

theorem cut_one_coefficient (D z : Int) (k N i S j a b : Nat)
    (hk : EqMod D (2*z^k) 1) (hN : EqMod D (3*z^N) 1)
    (ha : a+i+1 = k) (hb : b+1 = S)
    (hphase : k*S+j+k = N*(i+1)) (hNtwo : 2 ≤ N) :
    EqMod D (3^a*2^b) ((2^(N-2))*z^j) := by
  have he := cut_one_rank_identity k N i S j a b ha hb hphase hNtwo
  have he' : N*a+k*b+j = N*0+k*(N-2) := by omega
  simpa only [Int.pow_zero, Int.one_mul] using
    monomial_rank D z k N a b 0 (N-2) j hk hN he'

def geometric (z : Int) : Nat → Int
  | 0 => 0
  | n+1 => 1+z*geometric z n

theorem geometric_identity (z : Int) (n : Nat) :
    (1-z)*geometric z n = 1-z^n := by
  induction n with
  | zero => simp [geometric]
  | succ n ih =>
      simp only [geometric, Int.pow_succ]
      grind

/-- The eligible interval has length s=2k-N. Its geometric sum is a unit,
    with the explicit inverse 4*(1-z). -/
theorem interval_root (D z : Int) (k N s : Nat)
    (hN : N+s = 2*k) (hk : EqMod D (2*z^k) 1)
    (hbig : EqMod D (3*z^N) 1) :
    EqMod D (4*z^s) 3 := by
  have hsquare := eq_pow hk 2
  have hleft : EqMod D ((4*z^s)*(3*z^N)) (4*z^s) := by
    simpa only [Int.mul_one] using eq_mul (eq_refl D (4*z^s)) hbig
  have hright : EqMod D ((4*z^s)*(3*z^N)) 3 := by
    have hh := eq_mul (eq_refl D 3) hsquare
    have he : (4*z^s)*(3*z^N) = 3*(2*z^k)^2 := by
      have he' : s+N = k*2 := by omega
      calc
        (4*z^s)*(3*z^N) = 12*(z^s*z^N) := by grind
        _ = 12*z^(s+N) := by rw [Int.pow_add]
        _ = 12*z^(k*2) := by rw [he']
        _ = 3*(2*z^k)^2 := by rw [Int.mul_pow, ← Int.pow_mul]; grind
    rw [he]
    simpa using hh
  exact eq_trans (eq_symm hleft) hright

theorem geometric_inverse (D z : Int) (s : Nat)
    (hs : EqMod D (4*z^s) 3) :
    EqMod D (4*(1-z)*geometric z s) 1 := by
  have hh := eq_sub (eq_refl D 4) hs
  have he : 4*(1-z)*geometric z s = 4-4*z^s := by
    have hg := geometric_identity z s
    grind
  rw [he]
  simpa using hh

theorem geometric_unit (D z : Int) (s : Nat)
    (hs : EqMod D (4*z^s) 3) : UnitMod D (geometric z s) := by
  exact ⟨4*(1-z), by simpa only [Int.mul_comm] using geometric_inverse D z s hs⟩

theorem total_coefficient_unit (D z C κ : Int) (s : Nat)
    (hκ : UnitMod D κ) (hs : EqMod D (4*z^s) 3)
    (hC : EqMod D C (κ*geometric z s)) : UnitMod D C := by
  exact unit_congr hC (unit_mul hκ (geometric_unit D z s hs))

def selected (z : Int) : List Bool → Int
  | [] => 0
  | b :: bs => (if b then 1 else 0)+z*selected z bs

def digits (z : Int) : List Bool → Int
  | [] => 0
  | b :: bs => (if b then 3 else 4)+z*digits z bs

theorem digits_balance (z : Int) (bs : List Bool) :
    digits z bs + selected z bs = 4*geometric z bs.length := by
  induction bs with
  | nil => simp [digits, selected, geometric]
  | cons b bs ih =>
      cases b <;> simp only [digits, selected, Bool.false_eq_true, if_false,
        if_true, List.length_cons, geometric] <;> grind

theorem digit_equation_iff (D z : Int) (bs : List Bool)
    (hs : EqMod D (4*z^bs.length) 3) :
    EqMod D (digits z bs) 0 ↔ EqMod D ((1-z)*selected z bs) 1 := by
  have hg := geometric_inverse D z bs.length hs
  have hG : UnitMod D (1-z) := by
    refine ⟨4*geometric z bs.length, ?_⟩
    simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using hg
  have hbalance : EqMod D ((1-z)*digits z bs) (1-(1-z)*selected z bs) := by
    have hh := eq_sub hg (eq_refl D ((1-z)*selected z bs))
    have he : 4*(1-z)*geometric z bs.length - (1-z)*selected z bs =
        (1-z)*digits z bs := by
      have hb := digits_balance z bs
      grind
    rwa [he] at hh
  constructor
  · intro he
    have hzero := eq_mul (eq_refl D (1-z)) he
    have hh := eq_trans (eq_symm hzero) hbalance
    obtain ⟨v,hv⟩ := hh
    exact ⟨v, by grind⟩
  · intro he
    have hh := eq_sub (eq_refl D 1) he
    have hz : EqMod D ((1-z)*digits z bs) ((1-z)*0) := by
      simpa only [Int.sub_self, Int.mul_zero] using eq_trans hbalance hh
    exact unit_cancel hG hz

/-- Once the coefficient reindexing is supplied, the previous 4C-X test
    is equivalent to a binary polynomial with the fixed target one. -/
theorem mask_equation_iff (D z C X κ : Int) (bs : List Bool)
    (hκ : UnitMod D κ) (hs : EqMod D (4*z^bs.length) 3)
    (hC : EqMod D C (κ*geometric z bs.length))
    (hX : EqMod D X (κ*selected z bs)) :
    EqMod D (4*C-X) 0 ↔ EqMod D ((1-z)*selected z bs) 1 := by
  have he : EqMod D (4*C-X) (κ*digits z bs) := by
    have hh := eq_sub (eq_mul (eq_refl D 4) hC) hX
    have hid : 4*(κ*geometric z bs.length)-κ*selected z bs =
        κ*digits z bs := by
      have hb := digits_balance z bs
      grind
    rwa [hid] at hh
  rw [← digit_equation_iff D z bs hs]
  constructor
  · intro hzero
    apply unit_cancel hκ
    simpa only [Int.mul_zero] using eq_trans (eq_symm he) hzero
  · intro hzero
    have hh := eq_mul (eq_refl D κ) hzero
    simpa only [Int.mul_zero] using eq_trans he hh

/-- Large multiplicative order does not make a short positive polynomial
    nonzero modulo a prime. The counts 11,18 have this divisor 11. -/
theorem short_polynomial_can_vanish :
    EqMod 11 (2*(6:Int)^11) 1 ∧ EqMod 11 (3*(6:Int)^18) 1 ∧
    EqMod 11 (digits 6 [false,true,false,true]) 0 ∧
    ¬ EqMod 11 ((6:Int)^1) 1 ∧ ¬ EqMod 11 ((6:Int)^2) 1 ∧
    ¬ EqMod 11 ((6:Int)^5) 1 ∧ EqMod 11 ((6:Int)^10) 1 := by
  unfold EqMod digits
  decide

#print axioms count_roots
#print axioms cut_one_coefficient
#print axioms interval_root
#print axioms geometric_inverse
#print axioms total_coefficient_unit
#print axioms unit_coprime
#print axioms digits_balance
#print axioms digit_equation_iff
#print axioms mask_equation_iff
#print axioms short_polynomial_can_vanish
end MaskRankArithmetic
