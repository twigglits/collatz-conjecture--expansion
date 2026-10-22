/- A positive transition from the magnitude-five ladder into arbitrarily
   many magnitude-seventeen blocks, with two smaller Mersenne sources.
   Two exit units give unconditional least-source exclusions. -/
import MinimumPhaseCover

namespace MinimumSeventeenTransition
open OrdinaryCollatz MinimumLadderCover MinimumReturnLadder
open MinimumRootPredecessors

set_option maxRecDepth 4096

attribute [local irreducible] OrdinaryCollatz.iterate

def mainSource (R w : Nat) : Nat := source R (4 * w)
def firstSource (R w : Nat) : Nat := 2 ^ (2 * R + 5) * w - 1
def secondSource (R w : Nat) : Nat := 2 ^ (2 * R + 15) * w - 1
def scalar (r u : Nat) : Nat := 3 ^ (33 + 7 * r) * u

theorem bridge_33 (q : Nat) (hq : 0 < q) :
    Backtrack 5 7 (2187 * q - 17) (4096 * q - 33) := by
  have h0 := Backtrack.nil (2187 * q - 17)
  have h1 := Backtrack.even h0
  have e1 : 2 * (2187 * q - 17) = 4374 * q - 34 := by omega
  rw [e1] at h1
  clear e1 h0
  have h2 := Backtrack.even h1
  have e2 : 2 * (4374 * q - 34) = 8748 * q - 68 := by omega
  rw [e2] at h2
  clear e2 h1
  have h3 := Backtrack.even h2
  have e3 : 2 * (8748 * q - 68) = 17496 * q - 136 := by omega
  rw [e3] at h3
  clear e3 h2
  have h4 := Backtrack.odd h3
    (show 3 * (11664 * q - 91) + 1 = 2 * (17496 * q - 136) by omega)
  clear h3
  have h5 := Backtrack.odd h4
    (show 3 * (7776 * q - 61) + 1 = 2 * (11664 * q - 91) by omega)
  clear h4
  have h6 := Backtrack.even h5
  have e6 : 2 * (7776 * q - 61) = 15552 * q - 122 := by omega
  rw [e6] at h6
  clear e6 h5
  have h7 := Backtrack.even h6
  have e7 : 2 * (15552 * q - 122) = 31104 * q - 244 := by omega
  rw [e7] at h7
  clear e7 h6
  have h8 := Backtrack.odd h7
    (show 3 * (20736 * q - 163) + 1 = 2 * (31104 * q - 244) by omega)
  clear h7
  have h9 := Backtrack.odd h8
    (show 3 * (13824 * q - 109) + 1 = 2 * (20736 * q - 163) by omega)
  clear h8
  have h10 := Backtrack.odd h9
    (show 3 * (9216 * q - 73) + 1 = 2 * (13824 * q - 109) by omega)
  clear h9
  have h11 := Backtrack.odd h10
    (show 3 * (6144 * q - 49) + 1 = 2 * (9216 * q - 73) by omega)
  clear h10
  have h12 := Backtrack.odd h11
    (show 3 * (4096 * q - 33) + 1 = 2 * (6144 * q - 49) by omega)
  clear h11
  exact h12

theorem bridge_1702 (q : Nat) (hq : 0 < q) :
    Backtrack 13 11 (177147 * q - 17) (16777216 * q - 1702) := by
  have h0 := Backtrack.nil (177147 * q - 17)
  have h1 := Backtrack.even h0
  have e1 : 2 * (177147 * q - 17) = 354294 * q - 34 := by omega
  rw [e1] at h1
  clear e1 h0
  have h2 := Backtrack.even h1
  have e2 : 2 * (354294 * q - 34) = 708588 * q - 68 := by omega
  rw [e2] at h2
  clear e2 h1
  have h3 := Backtrack.even h2
  have e3 : 2 * (708588 * q - 68) = 1417176 * q - 136 := by omega
  rw [e3] at h3
  clear e3 h2
  have h4 := Backtrack.odd h3
    (show 3 * (944784 * q - 91) + 1 = 2 * (1417176 * q - 136) by omega)
  clear h3
  have h5 := Backtrack.odd h4
    (show 3 * (629856 * q - 61) + 1 = 2 * (944784 * q - 91) by omega)
  clear h4
  have h6 := Backtrack.odd h5
    (show 3 * (419904 * q - 41) + 1 = 2 * (629856 * q - 61) by omega)
  clear h5
  have h7 := Backtrack.even h6
  have e7 : 2 * (419904 * q - 41) = 839808 * q - 82 := by omega
  rw [e7] at h7
  clear e7 h6
  have h8 := Backtrack.odd h7
    (show 3 * (559872 * q - 55) + 1 = 2 * (839808 * q - 82) by omega)
  clear h7
  have h9 := Backtrack.odd h8
    (show 3 * (373248 * q - 37) + 1 = 2 * (559872 * q - 55) by omega)
  clear h8
  have h10 := Backtrack.odd h9
    (show 3 * (248832 * q - 25) + 1 = 2 * (373248 * q - 37) by omega)
  clear h9
  have h11 := Backtrack.even h10
  have e11 : 2 * (248832 * q - 25) = 497664 * q - 50 := by omega
  rw [e11] at h11
  clear e11 h10
  have h12 := Backtrack.even h11
  have e12 : 2 * (497664 * q - 50) = 995328 * q - 100 := by omega
  rw [e12] at h12
  clear e12 h11
  have h13 := Backtrack.odd h12
    (show 3 * (663552 * q - 67) + 1 = 2 * (995328 * q - 100) by omega)
  clear h12
  have h14 := Backtrack.even h13
  have e14 : 2 * (663552 * q - 67) = 1327104 * q - 134 := by omega
  rw [e14] at h14
  clear e14 h13
  have h15 := Backtrack.even h14
  have e15 : 2 * (1327104 * q - 134) = 2654208 * q - 268 := by omega
  rw [e15] at h15
  clear e15 h14
  have h16 := Backtrack.odd h15
    (show 3 * (1769472 * q - 179) + 1 = 2 * (2654208 * q - 268) by omega)
  clear h15
  have h17 := Backtrack.even h16
  have e17 : 2 * (1769472 * q - 179) = 3538944 * q - 358 := by omega
  rw [e17] at h17
  clear e17 h16
  have h18 := Backtrack.odd h17
    (show 3 * (2359296 * q - 239) + 1 = 2 * (3538944 * q - 358) by omega)
  clear h17
  have h19 := Backtrack.even h18
  have e19 : 2 * (2359296 * q - 239) = 4718592 * q - 478 := by omega
  rw [e19] at h19
  clear e19 h18
  have h20 := Backtrack.odd h19
    (show 3 * (3145728 * q - 319) + 1 = 2 * (4718592 * q - 478) by omega)
  clear h19
  have h21 := Backtrack.even h20
  have e21 : 2 * (3145728 * q - 319) = 6291456 * q - 638 := by omega
  rw [e21] at h21
  clear e21 h20
  have h22 := Backtrack.even h21
  have e22 : 2 * (6291456 * q - 638) = 12582912 * q - 1276 := by omega
  rw [e22] at h22
  clear e22 h21
  have h23 := Backtrack.odd h22
    (show 3 * (8388608 * q - 851) + 1 = 2 * (12582912 * q - 1276) by omega)
  clear h22
  have h24 := Backtrack.even h23
  have e24 : 2 * (8388608 * q - 851) = 16777216 * q - 1702 := by omega
  rw [e24] at h24
  clear e24 h23
  exact h24

theorem bridge_fifteen (q : Nat) (hq : 0 < q) :
    Backtrack 33 18 (387420489 * q - 17) (2251799813685248 * q - 100442350) := by
  have h0 := Backtrack.nil (387420489 * q - 17)
  have h1 := Backtrack.even h0
  have e1 : 2 * (387420489 * q - 17) = 774840978 * q - 34 := by omega
  rw [e1] at h1
  clear e1 h0
  have h2 := Backtrack.odd h1
    (show 3 * (516560652 * q - 23) + 1 = 2 * (774840978 * q - 34) by omega)
  clear h1
  have h3 := Backtrack.even h2
  have e3 : 2 * (516560652 * q - 23) = 1033121304 * q - 46 := by omega
  rw [e3] at h3
  clear e3 h2
  have h4 := Backtrack.even h3
  have e4 : 2 * (1033121304 * q - 46) = 2066242608 * q - 92 := by omega
  rw [e4] at h4
  clear e4 h3
  have h5 := Backtrack.even h4
  have e5 : 2 * (2066242608 * q - 92) = 4132485216 * q - 184 := by omega
  rw [e5] at h5
  clear e5 h4
  have h6 := Backtrack.even h5
  have e6 : 2 * (4132485216 * q - 184) = 8264970432 * q - 368 := by omega
  rw [e6] at h6
  clear e6 h5
  have h7 := Backtrack.even h6
  have e7 : 2 * (8264970432 * q - 368) = 16529940864 * q - 736 := by omega
  rw [e7] at h7
  clear e7 h6
  have h8 := Backtrack.odd h7
    (show 3 * (11019960576 * q - 491) + 1 = 2 * (16529940864 * q - 736) by omega)
  clear h7
  have h9 := Backtrack.even h8
  have e9 : 2 * (11019960576 * q - 491) = 22039921152 * q - 982 := by omega
  rw [e9] at h9
  clear e9 h8
  have h10 := Backtrack.odd h9
    (show 3 * (14693280768 * q - 655) + 1 = 2 * (22039921152 * q - 982) by omega)
  clear h9
  have h11 := Backtrack.even h10
  have e11 : 2 * (14693280768 * q - 655) = 29386561536 * q - 1310 := by omega
  rw [e11] at h11
  clear e11 h10
  have h12 := Backtrack.even h11
  have e12 : 2 * (29386561536 * q - 1310) = 58773123072 * q - 2620 := by omega
  rw [e12] at h12
  clear e12 h11
  have h13 := Backtrack.odd h12
    (show 3 * (39182082048 * q - 1747) + 1 = 2 * (58773123072 * q - 2620) by omega)
  clear h12
  have h14 := Backtrack.odd h13
    (show 3 * (26121388032 * q - 1165) + 1 = 2 * (39182082048 * q - 1747) by omega)
  clear h13
  have h15 := Backtrack.even h14
  have e15 : 2 * (26121388032 * q - 1165) = 52242776064 * q - 2330 := by omega
  rw [e15] at h15
  clear e15 h14
  have h16 := Backtrack.even h15
  have e16 : 2 * (52242776064 * q - 2330) = 104485552128 * q - 4660 := by omega
  rw [e16] at h16
  clear e16 h15
  have h17 := Backtrack.odd h16
    (show 3 * (69657034752 * q - 3107) + 1 = 2 * (104485552128 * q - 4660) by omega)
  clear h16
  have h18 := Backtrack.even h17
  have e18 : 2 * (69657034752 * q - 3107) = 139314069504 * q - 6214 := by omega
  rw [e18] at h18
  clear e18 h17
  have h19 := Backtrack.even h18
  have e19 : 2 * (139314069504 * q - 6214) = 278628139008 * q - 12428 := by omega
  rw [e19] at h19
  clear e19 h18
  have h20 := Backtrack.even h19
  have e20 : 2 * (278628139008 * q - 12428) = 557256278016 * q - 24856 := by omega
  rw [e20] at h20
  clear e20 h19
  have h21 := Backtrack.odd h20
    (show 3 * (371504185344 * q - 16571) + 1 = 2 * (557256278016 * q - 24856) by omega)
  clear h20
  have h22 := Backtrack.even h21
  have e22 : 2 * (371504185344 * q - 16571) = 743008370688 * q - 33142 := by omega
  rw [e22] at h22
  clear e22 h21
  have h23 := Backtrack.even h22
  have e23 : 2 * (743008370688 * q - 33142) = 1486016741376 * q - 66284 := by omega
  rw [e23] at h23
  clear e23 h22
  have h24 := Backtrack.even h23
  have e24 : 2 * (1486016741376 * q - 66284) = 2972033482752 * q - 132568 := by omega
  rw [e24] at h24
  clear e24 h23
  have h25 := Backtrack.odd h24
    (show 3 * (1981355655168 * q - 88379) + 1 = 2 * (2972033482752 * q - 132568) by omega)
  clear h24
  have h26 := Backtrack.even h25
  have e26 : 2 * (1981355655168 * q - 88379) = 3962711310336 * q - 176758 := by omega
  rw [e26] at h26
  clear e26 h25
  have h27 := Backtrack.even h26
  have e27 : 2 * (3962711310336 * q - 176758) = 7925422620672 * q - 353516 := by omega
  rw [e27] at h27
  clear e27 h26
  have h28 := Backtrack.even h27
  have e28 : 2 * (7925422620672 * q - 353516) = 15850845241344 * q - 707032 := by omega
  rw [e28] at h28
  clear e28 h27
  have h29 := Backtrack.odd h28
    (show 3 * (10567230160896 * q - 471355) + 1 = 2 * (15850845241344 * q - 707032) by omega)
  clear h28
  have h30 := Backtrack.even h29
  have e30 : 2 * (10567230160896 * q - 471355) = 21134460321792 * q - 942710 := by omega
  rw [e30] at h30
  clear e30 h29
  have h31 := Backtrack.even h30
  have e31 : 2 * (21134460321792 * q - 942710) = 42268920643584 * q - 1885420 := by omega
  rw [e31] at h31
  clear e31 h30
  have h32 := Backtrack.odd h31
    (show 3 * (28179280429056 * q - 1256947) + 1 = 2 * (42268920643584 * q - 1885420) by omega)
  clear h31
  have h33 := Backtrack.even h32
  have e33 : 2 * (28179280429056 * q - 1256947) = 56358560858112 * q - 2513894 := by omega
  rw [e33] at h33
  clear e33 h32
  have h34 := Backtrack.even h33
  have e34 : 2 * (56358560858112 * q - 2513894) = 112717121716224 * q - 5027788 := by omega
  rw [e34] at h34
  clear e34 h33
  have h35 := Backtrack.even h34
  have e35 : 2 * (112717121716224 * q - 5027788) = 225434243432448 * q - 10055576 := by omega
  rw [e35] at h35
  clear e35 h34
  have h36 := Backtrack.even h35
  have e36 : 2 * (225434243432448 * q - 10055576) = 450868486864896 * q - 20111152 := by omega
  rw [e36] at h36
  clear e36 h35
  have h37 := Backtrack.even h36
  have e37 : 2 * (450868486864896 * q - 20111152) = 901736973729792 * q - 40222304 := by omega
  rw [e37] at h37
  clear e37 h36
  have h38 := Backtrack.even h37
  have e38 : 2 * (901736973729792 * q - 40222304) = 1803473947459584 * q - 80444608 := by omega
  rw [e38] at h38
  clear e38 h37
  have h39 := Backtrack.odd h38
    (show 3 * (1202315964973056 * q - 53629739) + 1 = 2 * (1803473947459584 * q - 80444608) by omega)
  clear h38
  have h40 := Backtrack.even h39
  have e40 : 2 * (1202315964973056 * q - 53629739) = 2404631929946112 * q - 107259478 := by omega
  rw [e40] at h40
  clear e40 h39
  have h41 := Backtrack.odd h40
    (show 3 * (1603087953297408 * q - 71506319) + 1 = 2 * (2404631929946112 * q - 107259478) by omega)
  clear h40
  have h42 := Backtrack.even h41
  have e42 : 2 * (1603087953297408 * q - 71506319) = 3206175906594816 * q - 143012638 := by omega
  rw [e42] at h42
  clear e42 h41
  have h43 := Backtrack.odd h42
    (show 3 * (2137450604396544 * q - 95341759) + 1 = 2 * (3206175906594816 * q - 143012638) by omega)
  clear h42
  have h44 := Backtrack.odd h43
    (show 3 * (1424967069597696 * q - 63561173) + 1 = 2 * (2137450604396544 * q - 95341759) by omega)
  clear h43
  have h45 := Backtrack.even h44
  have e45 : 2 * (1424967069597696 * q - 63561173) = 2849934139195392 * q - 127122346 := by omega
  rw [e45] at h45
  clear e45 h44
  have h46 := Backtrack.odd h45
    (show 3 * (1899956092796928 * q - 84748231) + 1 = 2 * (2849934139195392 * q - 127122346) by omega)
  clear h45
  have h47 := Backtrack.odd h46
    (show 3 * (1266637395197952 * q - 56498821) + 1 = 2 * (1899956092796928 * q - 84748231) by omega)
  clear h46
  have h48 := Backtrack.odd h47
    (show 3 * (844424930131968 * q - 37665881) + 1 = 2 * (1266637395197952 * q - 56498821) by omega)
  clear h47
  have h49 := Backtrack.even h48
  have e49 : 2 * (844424930131968 * q - 37665881) = 1688849860263936 * q - 75331762 := by omega
  rw [e49] at h49
  clear e49 h48
  have h50 := Backtrack.odd h49
    (show 3 * (1125899906842624 * q - 50221175) + 1 = 2 * (1688849860263936 * q - 75331762) by omega)
  clear h49
  have h51 := Backtrack.even h50
  have e51 : 2 * (1125899906842624 * q - 50221175) = 2251799813685248 * q - 100442350 := by omega
  rw [e51] at h51
  clear e51 h50
  exact h51

theorem bridge_clocks (q : Nat) (hq : 0 < q) :
    iterate 19 (4096 * q - 33) = 2187 * q - 17 ∧
      iterate 35 (2 ^ 24 * q - 1702) = 3 ^ 11 * q - 17 ∧
      iterate 69 (2 ^ 51 * q - 100442350) = 3 ^ 18 * q - 17 := by
  exact ⟨backtrack_actual (bridge_33 q hq),
    backtrack_actual (bridge_1702 q hq), backtrack_actual (bridge_fifteen q hq)⟩

theorem base_profiles (X u : Nat) (hu : 0 < u) (hX : X + 7 = 2 ^ 57 * u) :
    iterate 91 (4 * X - 5) = 72 * (3 ^ 33 * u) - 17 ∧
      iterate 89 (243 * X - 1) = 81 * (3 ^ 33 * u) - 17 ∧
      iterate 69 (14348907 * X - 1) = 64 * (3 ^ 33 * u) - 17 := by
  have hn : 4 * X - 5 = 4096 * (2 ^ 47 * u) - 33 := by omega
  have hnp : 0 < 2 ^ 47 * u := by omega
  have hnc : 2187 * (2 ^ 47 * u) - 17 = 2048 ^ 4 * (8 * 2187 * u) - 17 := by omega
  have hnq : 0 < 8 * 2187 * u := by omega
  have hp : 243 * X - 1 = 2 ^ 24 * (243 * 2 ^ 33 * u) - 1702 := by omega
  have hpp : 0 < 243 * 2 ^ 33 * u := by omega
  have hpc : 3 ^ 11 * (243 * 2 ^ 33 * u) - 17 = 2048 ^ 3 * (3 ^ 16 * u) - 17 := by omega
  have hpq : 0 < 3 ^ 16 * u := by omega
  have hq : 14348907 * X - 1 = 2 ^ 51 * (14348907 * 64 * u) - 100442350 := by omega
  have hqp : 0 < 14348907 * 64 * u := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [show 91 = 19 + 18 * 4 by decide, iterate_add, hn,
      (bridge_clocks _ hnp).1, hnc, MinimumNegativeCycle.cycle_clock 4 _ hnq]
    omega
  · rw [show 89 = 35 + 18 * 3 by decide, iterate_add, hp,
      (bridge_clocks _ hpp).2.1, hpc, MinimumNegativeCycle.cycle_clock 3 _ hpq]
    omega
  · rw [hq, (bridge_clocks _ hqp).2.2]
    omega

theorem source_bounds (R w : Nat) (hR : 14 ≤ R) (hw : 0 < w) :
    (0 < firstSource R w ∧ firstSource R w < mainSource R w) ∧
      (0 < secondSource R w ∧ secondSource R w < mainSource R w) := by
  have h8 : 8 ≤ 8 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < 8) (show 1 ≤ R by omega)
  have hZ := Nat.mul_le_mul h8 (show 1 ≤ w by omega)
  have hfirst : 2 ^ (2 * R + 5) ≤ 2 ^ (2 * R + 15) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hscale : 2 ^ (3 * R + 1) = 2 * 8 ^ R := by
    rw [Nat.pow_succ, Nat.pow_mul]
    change 8 ^ R * 2 = 2 * 8 ^ R
    omega
  have hsecond : 2 ^ (2 * R + 15) ≤ 2 * 8 ^ R := by
    rw [← hscale]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hpos : 32 ≤ 2 ^ (2 * R + 5) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 5 ≤ 2 * R + 5 by omega)
  have hposw := Nat.mul_le_mul hpos (show 1 ≤ w by omega)
  have hfw := Nat.mul_le_mul_right w hfirst
  have hsw := Nat.mul_le_mul_right w hsecond
  have hn : 8 ^ R * (4 * w) = 4 * (8 ^ R * w) := by ac_rfl
  have hs : 2 * 8 ^ R * w = 2 * (8 ^ R * w) := by ac_rfl
  rw [hs] at hsw
  unfold firstSource secondSource mainSource source
  rw [hn]
  omega

theorem source_prefixes (R w : Nat) (hw : 0 < w) :
    iterate (5 * R) (mainSource R w) = 4 * (9 ^ R * w) - 5 ∧
      iterate (4 * R + 10) (firstSource R w) = 243 * (9 ^ R * w) - 1 ∧
      iterate (4 * R + 30) (secondSource R w) = 14348907 * (9 ^ R * w) - 1 := by
  have hn := weighted_clock R (4 * w) (by omega)
  have hnm : 9 ^ R * (4 * w) = 4 * (9 ^ R * w) := by ac_rfl
  have hp := backtrack_actual (MinimumInverseEscape.pure_inverse (2 * R + 5) w hw)
  have hq := backtrack_actual (MinimumInverseEscape.pure_inverse (2 * R + 15) w hw)
  have hpm : 3 ^ (2 * R + 5) * w = 243 * (9 ^ R * w) := by
    rw [Nat.pow_add, Nat.pow_mul]
    ac_rfl
  have hqm : 3 ^ (2 * R + 15) * w = 14348907 * (9 ^ R * w) := by
    rw [Nat.pow_add, Nat.pow_mul]
    ac_rfl
  exact ⟨by simpa only [mainSource, hnm] using hn,
    by simpa only [firstSource, Nat.zero_add, hpm,
      show 2 * (2 * R + 5) = 4 * R + 10 by omega] using hp,
    by simpa only [secondSource, Nat.zero_add, hqm,
      show 2 * (2 * R + 15) = 4 * R + 30 by omega] using hq⟩

theorem base_three_sources (R w u : Nat) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ 57 * u) :
    iterate (5 * R + 91) (mainSource R w) = 72 * (3 ^ 33 * u) - 17 ∧
      iterate (4 * R + 99) (firstSource R w) = 81 * (3 ^ 33 * u) - 17 ∧
      iterate (4 * R + 99) (secondSource R w) = 64 * (3 ^ 33 * u) - 17 := by
  have hp := source_prefixes R w hw
  have hb := base_profiles (9 ^ R * w) u hu hX
  refine ⟨?_, ?_, ?_⟩
  · rw [iterate_add, hp.1, hb.1]
  · rw [show 4 * R + 99 = (4 * R + 10) + 89 by omega, iterate_add, hp.2.1, hb.2.1]
  · rw [show 4 * R + 99 = (4 * R + 30) + 69 by omega, iterate_add, hp.2.2, hb.2.2]

theorem cycle_lift (r u c : Nat) (hu : 0 < u) (hc : 0 < c) :
    iterate (18 * r) (c * (3 ^ 33 * (2048 ^ r * u)) - 17) = c * scalar r u - 17 := by
  have hq : 0 < c * (3 ^ 33 * u) := by
    exact Nat.mul_pos hc (Nat.mul_pos (Nat.pow_pos (by decide)) hu)
  have he : c * (3 ^ 33 * (2048 ^ r * u)) = 2048 ^ r * (c * (3 ^ 33 * u)) := by ac_rfl
  rw [he, MinimumNegativeCycle.cycle_clock r _ hq]
  have hthree : 3 ^ (33 + 7 * r) = 3 ^ 33 * 2187 ^ r := by
    rw [Nat.pow_add, Nat.pow_mul]
  unfold scalar
  rw [hthree]
  congr 1
  ac_rfl

theorem three_sources (R w r u : Nat) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u) :
    iterate (5 * R + 91 + 18 * r) (mainSource R w) = 72 * scalar r u - 17 ∧
      iterate (4 * R + 99 + 18 * r) (firstSource R w) = 81 * scalar r u - 17 ∧
      iterate (4 * R + 99 + 18 * r) (secondSource R w) = 64 * scalar r u - 17 := by
  have hp : 0 < 2048 ^ r * u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hx : 9 ^ R * w + 7 = 2 ^ 57 * (2048 ^ r * u) := by
    rw [Nat.pow_add, Nat.pow_mul] at hX
    simpa only [Nat.mul_assoc] using hX
  have hb := base_three_sources R w (2048 ^ r * u) hw hp hx
  refine ⟨?_, ?_, ?_⟩
  · rw [iterate_add (5 * R + 91) (18 * r), hb.1, cycle_lift r u 72 hu (by decide)]
  · rw [iterate_add (4 * R + 99) (18 * r), hb.2.1, cycle_lift r u 81 hu (by decide)]
  · rw [iterate_add (4 * R + 99) (18 * r), hb.2.2, cycle_lift r u 64 hu (by decide)]


theorem even_exit_profiles (v : Nat) :
    iterate 10 (4608 * v + 919) = 972 * v + 194 ∧
      iterate 4 (5184 * v + 1036) = 1944 * v + 389 := by
  have f0_0 : C (4608 * v + 919) = 13824 * v + 2758 := by unfold C; split <;> omega
  have f0_1 : C (13824 * v + 2758) = 6912 * v + 1379 := by unfold C; split <;> omega
  have f0_2 : C (6912 * v + 1379) = 20736 * v + 4138 := by unfold C; split <;> omega
  have f0_3 : C (20736 * v + 4138) = 10368 * v + 2069 := by unfold C; split <;> omega
  have f0_4 : C (10368 * v + 2069) = 31104 * v + 6208 := by unfold C; split <;> omega
  have f0_5 : C (31104 * v + 6208) = 15552 * v + 3104 := by unfold C; split <;> omega
  have f0_6 : C (15552 * v + 3104) = 7776 * v + 1552 := by unfold C; split <;> omega
  have f0_7 : C (7776 * v + 1552) = 3888 * v + 776 := by unfold C; split <;> omega
  have f0_8 : C (3888 * v + 776) = 1944 * v + 388 := by unfold C; split <;> omega
  have f0_9 : C (1944 * v + 388) = 972 * v + 194 := by unfold C; split <;> omega
  have f1_0 : C (5184 * v + 1036) = 2592 * v + 518 := by unfold C; split <;> omega
  have f1_1 : C (2592 * v + 518) = 1296 * v + 259 := by unfold C; split <;> omega
  have f1_2 : C (1296 * v + 259) = 3888 * v + 778 := by unfold C; split <;> omega
  have f1_3 : C (3888 * v + 778) = 1944 * v + 389 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f0_7, f0_8, f0_9],
    by simp only [iterate, f1_0, f1_1, f1_2, f1_3]⟩

theorem odd_exit_profiles (v : Nat) :
    iterate 12 (4608 * v + 4375) = 1458 * v + 1385 ∧
      iterate 6 (5184 * v + 4924) = 2916 * v + 2771 ∧
      iterate 17 (4096 * v + 3887) = 1458 * v + 1384 := by
  have f0_0 : C (4608 * v + 4375) = 13824 * v + 13126 := by unfold C; split <;> omega
  have f0_1 : C (13824 * v + 13126) = 6912 * v + 6563 := by unfold C; split <;> omega
  have f0_2 : C (6912 * v + 6563) = 20736 * v + 19690 := by unfold C; split <;> omega
  have f0_3 : C (20736 * v + 19690) = 10368 * v + 9845 := by unfold C; split <;> omega
  have f0_4 : C (10368 * v + 9845) = 31104 * v + 29536 := by unfold C; split <;> omega
  have f0_5 : C (31104 * v + 29536) = 15552 * v + 14768 := by unfold C; split <;> omega
  have f0_6 : C (15552 * v + 14768) = 7776 * v + 7384 := by unfold C; split <;> omega
  have f0_7 : C (7776 * v + 7384) = 3888 * v + 3692 := by unfold C; split <;> omega
  have f0_8 : C (3888 * v + 3692) = 1944 * v + 1846 := by unfold C; split <;> omega
  have f0_9 : C (1944 * v + 1846) = 972 * v + 923 := by unfold C; split <;> omega
  have f0_10 : C (972 * v + 923) = 2916 * v + 2770 := by unfold C; split <;> omega
  have f0_11 : C (2916 * v + 2770) = 1458 * v + 1385 := by unfold C; split <;> omega
  have f1_0 : C (5184 * v + 4924) = 2592 * v + 2462 := by unfold C; split <;> omega
  have f1_1 : C (2592 * v + 2462) = 1296 * v + 1231 := by unfold C; split <;> omega
  have f1_2 : C (1296 * v + 1231) = 3888 * v + 3694 := by unfold C; split <;> omega
  have f1_3 : C (3888 * v + 3694) = 1944 * v + 1847 := by unfold C; split <;> omega
  have f1_4 : C (1944 * v + 1847) = 5832 * v + 5542 := by unfold C; split <;> omega
  have f1_5 : C (5832 * v + 5542) = 2916 * v + 2771 := by unfold C; split <;> omega
  have f2_0 : C (4096 * v + 3887) = 12288 * v + 11662 := by unfold C; split <;> omega
  have f2_1 : C (12288 * v + 11662) = 6144 * v + 5831 := by unfold C; split <;> omega
  have f2_2 : C (6144 * v + 5831) = 18432 * v + 17494 := by unfold C; split <;> omega
  have f2_3 : C (18432 * v + 17494) = 9216 * v + 8747 := by unfold C; split <;> omega
  have f2_4 : C (9216 * v + 8747) = 27648 * v + 26242 := by unfold C; split <;> omega
  have f2_5 : C (27648 * v + 26242) = 13824 * v + 13121 := by unfold C; split <;> omega
  have f2_6 : C (13824 * v + 13121) = 41472 * v + 39364 := by unfold C; split <;> omega
  have f2_7 : C (41472 * v + 39364) = 20736 * v + 19682 := by unfold C; split <;> omega
  have f2_8 : C (20736 * v + 19682) = 10368 * v + 9841 := by unfold C; split <;> omega
  have f2_9 : C (10368 * v + 9841) = 31104 * v + 29524 := by unfold C; split <;> omega
  have f2_10 : C (31104 * v + 29524) = 15552 * v + 14762 := by unfold C; split <;> omega
  have f2_11 : C (15552 * v + 14762) = 7776 * v + 7381 := by unfold C; split <;> omega
  have f2_12 : C (7776 * v + 7381) = 23328 * v + 22144 := by unfold C; split <;> omega
  have f2_13 : C (23328 * v + 22144) = 11664 * v + 11072 := by unfold C; split <;> omega
  have f2_14 : C (11664 * v + 11072) = 5832 * v + 5536 := by unfold C; split <;> omega
  have f2_15 : C (5832 * v + 5536) = 2916 * v + 2768 := by unfold C; split <;> omega
  have f2_16 : C (2916 * v + 2768) = 1458 * v + 1384 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f0_7, f0_8, f0_9, f0_10, f0_11],
    by simp only [iterate, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5],
    by simp only [iterate, f2_0, f2_1, f2_2, f2_3, f2_4, f2_5, f2_6, f2_7, f2_8, f2_9, f2_10, f2_11, f2_12, f2_13, f2_14, f2_15, f2_16]⟩

theorem scalar_cover (a : Nat) (ha : a % 64 = 13 ∨ a % 64 = 61) :
    Merges (81 * a - 17) (72 * a - 17) ∨
      Merges (64 * a - 17) (72 * a - 17) := by
  let v := a / 64
  rcases ha with ha | ha
  · have hv : a = 64 * v + 13 := by dsimp [v]; omega
    have hn : 72 * a - 17 = 4608 * v + 919 := by omega
    have hp : 81 * a - 17 = 5184 * v + 1036 := by omega
    have hb := even_exit_profiles v
    have hd := double_partner_even (972 * v + 194) (by omega)
    have he : 2 * (972 * v + 194) + 1 = 1944 * v + 389 := by omega
    rw [he] at hd
    apply Or.inl
    refine ⟨7, 12, ?_⟩
    rw [show 7 = 4 + 3 by decide, iterate_add 4 3,
      show 12 = 10 + 2 by decide, iterate_add 10 2, hn, hp, hb.1, hb.2]
    exact hd
  · have hv : a = 64 * v + 61 := by dsimp [v]; omega
    have hn : 72 * a - 17 = 4608 * v + 4375 := by omega
    have hp : 81 * a - 17 = 5184 * v + 4924 := by omega
    have hq : 64 * a - 17 = 4096 * v + 3887 := by omega
    have hb := odd_exit_profiles v
    have hdouble : 2 * (1458 * v + 1385) + 1 = 2916 * v + 2771 := by omega
    have hadj : 1458 * v + 1385 - 1 = 1458 * v + 1384 := by omega
    rcases odd_two_partner_cover (1458 * v + 1385) (by omega) with hm | hm
    · apply Or.inl
      rw [hdouble] at hm
      exact merger_transport _ _ _ _ 6 12 (by rw [hp, hb.2.1]) (by rw [hn, hb.1]) hm
    · apply Or.inr
      rw [hadj] at hm
      exact merger_transport _ _ _ _ 17 12 (by rw [hq, hb.2.2]) (by rw [hn, hb.1]) hm

theorem weighted_escape (R w r u : Nat) (hR : 14 ≤ R) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (ha : scalar r u % 64 = 13 ∨ scalar r u % 64 = 61) :
    ∃ P, 0 < P ∧ P < mainSource R w ∧ Merges P (mainSource R w) := by
  have hb := source_bounds R w hR hw
  have ht := three_sources R w r u hw hu hX
  rcases scalar_cover (scalar r u) ha with hm | hm
  · exact ⟨firstSource R w, hb.1.1, hb.1.2,
      merger_transport _ _ _ _ _ _ ht.2.1 ht.1 hm⟩
  · exact ⟨secondSource R w, hb.2.1, hb.2.2,
      merger_transport _ _ _ _ _ _ ht.2.2 ht.1 hm⟩

theorem weighted_not_least (R w r u : Nat) (hR : 14 ≤ R) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (ha : scalar r u % 64 = 13 ∨ scalar r u % 64 = 61) :
    ¬ LeastCounterexample (mainSource R w) := by
  intro hn
  obtain ⟨P, hP, hlt, s, t, hmeet⟩ := weighted_escape R w r u hR hw hu hX ha
  have hle := least_coalescing_predecessor hn hP hmeet
  omega

theorem powered_unit (d v h : Nat) :
    ∃ U, (1 + 64 * d * v) ^ h = 1 + 64 * d * U ∧ U % 64 = (h * v) % 64 := by
  induction h with
  | zero => exact ⟨0, by simp⟩
  | succ h ih =>
    obtain ⟨U, he, hm⟩ := ih
    refine ⟨U + v + 64 * d * U * v, ?_, ?_⟩
    · rw [Nat.pow_succ, he]
      grind
    · rw [Nat.succ_mul h v]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
        Nat.zero_mod, Nat.add_zero, Nat.mod_mod, hm]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem finite_odd_targets :
    ∀ c : Fin 64, c.val % 2 = 1 →
      (∃ h : Fin 64, (c.val * h.val) % 64 = 13) ∧
      (∃ h : Fin 64, (c.val * h.val) % 64 = 61) := by
  decide +kernel


theorem lifted_exponents (r B e : Nat) (he : e = 13 ∨ e = 61) :
    ∃ R u, B < R ∧ 14 ≤ R ∧ 0 < u ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧ scalar r u % 64 = e := by
  let m := 57 + 11 * r
  let D := 2 ^ m
  let A := MinimumCriticalClockLift.liftExponent (m + 3)
  let T := 2 ^ (m - 3)
  have hm : 6 ≤ m := by dsimp [m]; omega
  have hD : D = 64 * 2 ^ (m - 6) := by
    dsimp [D]
    calc
      _ = 2 ^ ((m - 6) + 6) := congrArg (fun j => 2 ^ j) (by omega)
      _ = _ := by rw [Nat.pow_add]; omega
  obtain ⟨c, hc⟩ := MinimumCriticalClockLift.nine_power_top_bit (m - 3)
  let v := 2 * c + 1
  have hv : v % 2 = 1 := by dsimp [v]; omega
  have hT : 9 ^ T = 1 + D * v := by
    simpa only [T, D, v, show m - 3 + 3 = m by omega] using hc
  obtain ⟨_, t, ht⟩ := MinimumCriticalClockLift.lift_exponent_spec (m + 3)
  have hA : 9 ^ A + 7 = 64 * D * t := by
    have hs : 2 ^ (m + 3 + 3) = 64 * D := by
      rw [show m + 3 + 3 = m + 6 by omega, Nat.pow_add]
      dsimp [D]
      omega
    simpa only [A, hs] using ht
  have hbase : 9 ^ A % 64 = 57 := by
    have hs : 64 * D * t = 64 * (D * t) := by ac_rfl
    rw [hs] at hA
    omega
  let coeff := 57 * 3 ^ (33 + 7 * r) * v
  have hcodd : coeff % 2 = 1 := by
    change (57 * 3 ^ (33 + 7 * r) * v) % 2 = 1
    rw [Nat.mul_mod (57 * 3 ^ (33 + 7 * r)) v 2,
      Nat.mul_mod 57 (3 ^ (33 + 7 * r)) 2, Nat.pow_mod, hv]
    simp
  have hcf : (coeff % 64) % 2 = 1 := by omega
  have hf := finite_odd_targets ⟨coeff % 64, Nat.mod_lt _ (by decide)⟩ hcf
  have hex : ∃ h : Fin 64, (coeff % 64 * h.val) % 64 = e := by
    rcases he with he | he
    · simpa only [he] using hf.1
    · simpa only [he] using hf.2
  obtain ⟨h0, hh0⟩ := hex
  let h := h0.val + 64 * (B + 14)
  let R := A + T * h
  have hmod : h % 64 = h0.val := by dsimp [h]; omega
  have hbound : B < R ∧ 14 ≤ R := by
    have hp : 1 ≤ T := Nat.two_pow_pos _
    have hph := Nat.mul_le_mul_right h hp
    dsimp [R, h] at *
    omega
  obtain ⟨U, hU, hu⟩ := powered_unit (2 ^ (m - 6)) v h
  have hpow : 9 ^ (T * h) = 1 + D * U := by
    rw [Nat.pow_mul, hT, hD]
    exact hU
  let u := 64 * t + 9 ^ A * U
  have hX : 9 ^ R + 7 = D * u := by
    calc
      _ = 9 ^ A * (1 + D * U) + 7 := by
        change 9 ^ (A + T * h) + 7 = _
        rw [Nat.pow_add, hpow]
      _ = (9 ^ A + 7) + D * (9 ^ A * U) := by
        rw [Nat.mul_add, Nat.mul_one]
        have hs : 9 ^ A * (D * U) = D * (9 ^ A * U) := by ac_rfl
        rw [hs]
        omega
      _ = 64 * D * t + D * (9 ^ A * U) := by rw [hA]
      _ = D * u := by
        change _ = D * (64 * t + 9 ^ A * U)
        rw [Nat.mul_add]
        congr 1
        ac_rfl
  have hunit : scalar r u % 64 = e := by
    have hco : (coeff * h) % 64 = e := by
      rw [Nat.mul_mod, hmod]
      exact hh0
    have hu0 : u % 64 = (57 * (h * v)) % 64 := by
      dsimp [u]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul,
        Nat.zero_mod, Nat.zero_add, Nat.mod_mod, hbase, hu]
    have hfinal : (3 ^ (33 + 7 * r) * (57 * (h * v))) % 64 = e := by
      have heq : 3 ^ (33 + 7 * r) * (57 * (h * v)) = coeff * h := by dsimp [coeff]; ac_rfl
      rw [heq]
      exact hco
    unfold scalar
    rw [Nat.mul_mod, hu0]
    rw [← Nat.mul_mod]
    exact hfinal
  have hupos : 0 < u := by
    have hp : 0 < 9 ^ R := Nat.pow_pos (by decide)
    by_cases hz : u = 0
    · rw [hz, Nat.mul_zero] at hX
      omega
    · omega
  exact ⟨R, u, hbound.1, hbound.2, hupos, hX, hunit⟩

theorem unbounded_pure_escape (r B e : Nat) (he : e = 13 ∨ e = 61) :
    ∃ R u, B < R ∧ 14 ≤ R ∧ 0 < u ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧ scalar r u % 64 = e ∧
      ¬ LeastCounterexample (4 * 8 ^ R - 5) := by
  obtain ⟨R, u, hB, hR, hu, hX, ha⟩ := lifted_exponents r B e he
  refine ⟨R, u, hB, hR, hu, hX, ha, ?_⟩
  have hx : 9 ^ R * 1 + 7 = 2 ^ (57 + 11 * r) * u := by simpa only [Nat.mul_one] using hX
  have ha' : scalar r u % 64 = 13 ∨ scalar r u % 64 = 61 := by omega
  have hn := weighted_not_least R 1 r u hR (by decide) hu hx ha'
  have hs : mainSource R 1 = 4 * 8 ^ R - 5 := by simp [mainSource, source, Nat.mul_comm]
  simpa only [hs] using hn

#print axioms bridge_33
#print axioms bridge_1702
#print axioms bridge_fifteen
#print axioms bridge_clocks
#print axioms base_profiles
#print axioms source_bounds
#print axioms source_prefixes
#print axioms base_three_sources
#print axioms cycle_lift
#print axioms three_sources
#print axioms even_exit_profiles
#print axioms odd_exit_profiles
#print axioms scalar_cover
#print axioms weighted_escape
#print axioms weighted_not_least
#print axioms powered_unit
#print axioms finite_odd_targets
#print axioms lifted_exponents
#print axioms unbounded_pure_escape

end MinimumSeventeenTransition
