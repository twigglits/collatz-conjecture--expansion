/- Arithmetic certificates for a four-feature valuation rank obstruction.
The real logarithm and weighted-inequality interpretation are written bridges.
No assertion here proves or disproves the Collatz conjecture. -/
import CollatzAffine
namespace ValuationGraphRank

def ExactVal (p k n : Nat) : Prop := n % p^k = 0 ∧ n % p^(k+1) ≠ 0

def Features (n a b c d : Nat) : Prop :=
  ExactVal 2 a n ∧ ExactVal 2 b (n+1) ∧
  ExactVal 3 c n ∧ ExactVal 3 d (n+1)

theorem features_131 (q : Nat) :
    Features (432*q+131) 0 2 0 1 ∧
    Features (648*q+197) 0 1 0 2 ∧
    Features (864*q+262) 1 0 0 0 ∧
    Features (288*q+87) 0 3 1 0 := by
  simp only [Features, ExactVal]
  omega

theorem neighbors_131 (q : Nat) :
    CollatzAffine.U (432*q+131) = (648*q+197) ∧
    CollatzAffine.U (864*q+262) = 432*q+131 ∧
    CollatzAffine.U (288*q+87) = 432*q+131 ∧
    (432*q+131) % 3 = 2 := by
  unfold CollatzAffine.U
  simp only [show (432*q+131) % 2 = 1 by omega,
    show (864*q+262) % 2 = 0 by omega,
    show (288*q+87) % 2 = 1 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem features_134 (q : Nat) :
    Features (1296*q+134) 1 0 0 3 ∧
    Features (648*q+67) 0 2 0 0 ∧
    Features (2592*q+268) 2 0 0 0 ∧
    Features (864*q+89) 0 1 0 2 := by
  simp only [Features, ExactVal]
  omega

theorem neighbors_134 (q : Nat) :
    CollatzAffine.U (1296*q+134) = (648*q+67) ∧
    CollatzAffine.U (2592*q+268) = 1296*q+134 ∧
    CollatzAffine.U (864*q+89) = 1296*q+134 ∧
    (1296*q+134) % 3 = 2 := by
  unfold CollatzAffine.U
  simp only [show (1296*q+134) % 2 = 0 by omega,
    show (2592*q+268) % 2 = 0 by omega,
    show (864*q+89) % 2 = 1 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem features_137 (q : Nat) :
    Features (216*q+137) 0 1 0 1 ∧
    Features (324*q+206) 1 0 0 2 ∧
    Features (432*q+274) 1 0 0 0 ∧
    Features (144*q+91) 0 2 0 0 := by
  simp only [Features, ExactVal]
  omega

theorem neighbors_137 (q : Nat) :
    CollatzAffine.U (216*q+137) = (324*q+206) ∧
    CollatzAffine.U (432*q+274) = 216*q+137 ∧
    CollatzAffine.U (144*q+91) = 216*q+137 ∧
    (216*q+137) % 3 = 2 := by
  unfold CollatzAffine.U
  simp only [show (216*q+137) % 2 = 1 by omega,
    show (432*q+274) % 2 = 0 by omega,
    show (144*q+91) % 2 = 1 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem features_142 (q : Nat) :
    Features (864*q+142) 1 0 0 0 ∧
    Features (432*q+71) 0 3 0 2 ∧
    Features (1728*q+284) 2 0 0 1 := by
  simp only [Features, ExactVal]
  omega

theorem neighbors_142 (q : Nat) :
    CollatzAffine.U (864*q+142) = (432*q+71) ∧
    CollatzAffine.U (1728*q+284) = 864*q+142 ∧
    (864*q+142) % 3 = 1 := by
  unfold CollatzAffine.U
  simp only [show (864*q+142) % 2 = 0 by omega,
    show (1728*q+284) % 2 = 0 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem features_147 (q : Nat) :
    Features (72*q+147) 0 2 1 0 ∧
    Features (108*q+221) 0 1 0 1 ∧
    Features (144*q+294) 1 0 1 0 := by
  simp only [Features, ExactVal]
  omega

theorem neighbors_147 (q : Nat) :
    CollatzAffine.U (72*q+147) = (108*q+221) ∧
    CollatzAffine.U (144*q+294) = 72*q+147 ∧
    (72*q+147) % 3 = 0 := by
  unfold CollatzAffine.U
  simp only [show (72*q+147) % 2 = 1 by omega,
    show (144*q+294) % 2 = 0 by omega, reduceIte, Nat.reduceEqDiff]
  omega

theorem log_power_bounds : 2^19 < (3:Nat)^12 ∧ (3:Nat)^5 < 2^8 := by decide

-- Each row denotes coeffs · (C,L,a,b,c,d) ≥ 0 (or > 0 if strict).
abbrev Row := List Int × Bool
def base : List Row := [([1, 0, 0, 0, 0, 0], true),
  ([-7, 12, 0, 0, 0, 0], true),
  ([3, -5, 0, 0, 0, 0], true),
  ([1, 0, 1, 0, 0, 0], false)]

def alternatives : List (List Row) := [
  [([0, -1, 0, 1, 0, -1], true), ([-1, 0, -1, 2, 0, 1], true), ([0, 1, 0, -1, -1, 1], false)],
  [([1, 0, 1, -2, 0, 3], true), ([-1, 0, -1, 0, 0, 3], true), ([0, 1, 1, -1, 0, 1], false)],
  [([0, -1, -1, 1, 0, -1], true), ([-1, 0, -1, 1, 0, 1], true), ([0, 1, 0, -1, 0, 1], false)],
  [([1, 0, 1, -3, 0, -2], true), ([-1, 0, -1, 0, 0, -1], true)],
  [([0, -1, 0, 1, 1, -1], true), ([-1, 0, -1, 2, 0, 0], true)]]

def certificates : List (List Nat × List Nat) := [
  ([0, 0, 0, 0, 0], [19, 13, 0, 0, 84, 60, 72, 12, 0]),
  ([0, 0, 0, 0, 1], [0, 0, 0, 3, 0, 4, 0, 6, 13]),
  ([0, 0, 0, 1, 0], [7, 1, 0, 0, 12, 6, 0, 6, 0]),
  ([0, 0, 0, 1, 1], [0, 0, 0, 3, 0, 1, 0, 3, 1]),
  ([0, 0, 1, 0, 0], [7, 1, 0, 36, 12, 0, 60, 24, 0]),
  ([0, 0, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([0, 0, 1, 1, 0], [0, 0, 0, 6, 0, 1, 2, 5, 0]),
  ([0, 0, 1, 1, 1], [0, 0, 0, 6, 0, 1, 2, 5, 0]),
  ([0, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 0, 2, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 0, 2, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 0, 2, 1, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 1, 0, 0, 0], [21, 3, 0, 8, 36, 20, 0, 12, 0]),
  ([0, 1, 0, 0, 1], [0, 0, 0, 7, 0, 4, 0, 6, 9]),
  ([0, 1, 0, 1, 0], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([0, 1, 0, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([0, 1, 1, 0, 0], [7, 1, 0, 36, 12, 0, 60, 24, 0]),
  ([0, 1, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([0, 1, 1, 1, 0], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([0, 1, 1, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([0, 1, 2, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 1, 2, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 1, 2, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 1, 2, 1, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([0, 2, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([0, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([0, 2, 0, 1, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([0, 2, 1, 0, 0], [43, 1, 0, 0, 48, 36, 60, 24, 0]),
  ([0, 2, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([0, 2, 1, 1, 0], [12, 0, 1, 0, 10, 15, 5, 10, 0]),
  ([0, 2, 1, 1, 1], [12, 0, 1, 0, 10, 15, 5, 10, 0]),
  ([0, 2, 2, 0, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 2, 2, 0, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 2, 2, 1, 0], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([0, 2, 2, 1, 1], [0, 0, 0, 0, 1, 0, 1, 0, 0]),
  ([1, 0, 0, 0, 0], [0, 0, 0, 4, 13, 1, 0, 8, 0]),
  ([1, 0, 0, 0, 1], [0, 0, 0, 4, 13, 1, 0, 8, 0]),
  ([1, 0, 0, 1, 0], [0, 0, 0, 4, 1, 1, 0, 4, 0]),
  ([1, 0, 0, 1, 1], [0, 0, 0, 4, 1, 1, 0, 4, 0]),
  ([1, 0, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 1, 0]),
  ([1, 0, 1, 0, 1], [0, 0, 0, 3, 0, 4, 0, 6, 13]),
  ([1, 0, 1, 1, 0], [0, 0, 0, 6, 0, 1, 2, 5, 0]),
  ([1, 0, 1, 1, 1], [0, 0, 0, 6, 0, 1, 2, 5, 0]),
  ([1, 0, 2, 0, 0], [0, 0, 0, 4, 13, 1, 0, 8, 0]),
  ([1, 0, 2, 0, 1], [0, 0, 0, 4, 13, 1, 0, 8, 0]),
  ([1, 0, 2, 1, 0], [0, 0, 0, 4, 1, 1, 0, 4, 0]),
  ([1, 0, 2, 1, 1], [0, 0, 0, 4, 1, 1, 0, 4, 0]),
  ([1, 1, 0, 0, 0], [0, 0, 0, 4, 9, 1, 0, 6, 0]),
  ([1, 1, 0, 0, 1], [0, 0, 0, 4, 9, 1, 0, 6, 0]),
  ([1, 1, 0, 1, 0], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 1, 0, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 1, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 1, 0]),
  ([1, 1, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([1, 1, 1, 1, 0], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 1, 1, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 1, 2, 0, 0], [0, 0, 0, 4, 9, 1, 0, 6, 0]),
  ([1, 1, 2, 0, 1], [0, 0, 0, 4, 9, 1, 0, 6, 0]),
  ([1, 1, 2, 1, 0], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 1, 2, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([1, 2, 0, 0, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([1, 2, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([1, 2, 0, 1, 0], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([1, 2, 0, 1, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([1, 2, 1, 0, 0], [0, 0, 0, 1, 1, 0, 1, 1, 0]),
  ([1, 2, 1, 0, 1], [0, 0, 0, 1, 1, 0, 1, 1, 0]),
  ([1, 2, 1, 1, 0], [2, 0, 1, 10, 0, 5, 5, 10, 0]),
  ([1, 2, 1, 1, 1], [2, 0, 1, 10, 0, 5, 5, 10, 0]),
  ([1, 2, 2, 0, 0], [2, 0, 1, 5, 25, 5, 0, 15, 0]),
  ([1, 2, 2, 0, 1], [2, 0, 1, 5, 25, 5, 0, 15, 0]),
  ([1, 2, 2, 1, 0], [4, 0, 2, 10, 5, 10, 0, 15, 0]),
  ([1, 2, 2, 1, 1], [4, 0, 2, 10, 5, 10, 0, 15, 0]),
  ([2, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 0, 0, 1], [0, 0, 0, 3, 0, 4, 0, 6, 13]),
  ([2, 0, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 0, 1, 1], [0, 0, 0, 3, 0, 1, 0, 3, 1]),
  ([2, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([2, 0, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 1, 1, 1], [0, 0, 0, 6, 0, 1, 2, 5, 0]),
  ([2, 0, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 2, 0, 1], [0, 0, 0, 3, 0, 4, 0, 6, 13]),
  ([2, 0, 2, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 0, 2, 1, 1], [0, 0, 0, 3, 0, 1, 0, 3, 1]),
  ([2, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 0, 0, 1], [0, 0, 0, 7, 0, 4, 0, 6, 9]),
  ([2, 1, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 0, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([2, 1, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([2, 1, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 1, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([2, 1, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 2, 0, 1], [0, 0, 0, 7, 0, 4, 0, 6, 9]),
  ([2, 1, 2, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 1, 2, 1, 1], [0, 0, 0, 4, 0, 1, 0, 3, 0]),
  ([2, 2, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 0, 0, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([2, 2, 0, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 0, 1, 1], [0, 0, 0, 0, 0, 1, 1, 0, 0]),
  ([2, 2, 1, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 1, 0, 1], [0, 0, 0, 3, 0, 0, 4, 2, 1]),
  ([2, 2, 1, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 1, 1, 1], [2, 0, 1, 10, 0, 5, 5, 10, 0]),
  ([2, 2, 2, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 2, 0, 1], [0, 3, 8, 0, 0, 3, 1, 2, 5]),
  ([2, 2, 2, 1, 0], [0, 0, 0, 0, 1, 0, 0, 0, 1]),
  ([2, 2, 2, 1, 1], [4, 0, 2, 5, 0, 10, 0, 10, 5])]

def selections : List (List Nat) :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
  (List.range 3).flatMap fun c => (List.range 2).flatMap fun d =>
  (List.range 2).map fun e => [a,b,c,d,e]

def selected (choices : List Nat) : List Row :=
  base ++ (alternatives.zip choices).map (fun (rs,i) => rs[i]!)

def validCertificate (cert : List Nat × List Nat) : Bool := Id.run do
  let rows := selected cert.1
  let weights := cert.2
  return rows.length == 9 && weights.length == 9 &&
    rows.all (fun r => r.1.length == 6) &&
    (List.range 6).all (fun j =>
      ((rows.zip weights).map (fun (r,w) => (w:Int) * r.1[j]!)).sum == 0) &&
    ((rows.zip weights).map (fun (r,w) => if r.2 then w else 0)).sum > 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
 theorem certificates_checked : certificates.all validCertificate = true := by decide

theorem selections_exhausted : certificates.map Prod.fst = selections := by decide

theorem certificate_count : certificates.length = 108 := by decide

#print axioms features_131
#print axioms features_134
#print axioms features_137
#print axioms features_142
#print axioms features_147
#print axioms neighbors_131
#print axioms neighbors_134
#print axioms neighbors_137
#print axioms neighbors_142
#print axioms neighbors_147
#print axioms log_power_bounds
#print axioms certificates_checked
#print axioms selections_exhausted
#print axioms certificate_count
end ValuationGraphRank
