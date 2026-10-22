/- A fourth smaller Mersenne source crosses the separated exit family
   after arbitrarily many additional negative-seventeen blocks. -/
import MinimumSeventeenSeparation

namespace MinimumSeventeenFourth
open OrdinaryCollatz MinimumReturnLadder MinimumLadderCover
open MinimumSeventeenTransition MinimumSeventeenSeparation MinimumRootPredecessors

set_option maxRecDepth 8192
attribute [local irreducible] OrdinaryCollatz.iterate

def fourthSource (R w : Nat) : Nat := 2 ^ (2 * R + 13) * w - 1
def secondaryScalar (j q : Nat) : Nat := 3 ^ (6 + 7 * j) * q

theorem bridge_thirteen (q : Nat) (hq : 0 < q) :
    Backtrack 52 56
      (523347633027360537213511521 * q - 17) (324518553658426726783156020576256 * q - 11160262) := by
  have h0 := Backtrack.nil (523347633027360537213511521 * q - 17)
  have h1 := Backtrack.even h0
  have e1 : 2 * (523347633027360537213511521 * q - 17) = 1046695266054721074427023042 * q - 34 := by omega
  rw [e1] at h1
  clear e1 h0
  have h2 := Backtrack.even h1
  have e2 : 2 * (1046695266054721074427023042 * q - 34) = 2093390532109442148854046084 * q - 68 := by omega
  rw [e2] at h2
  clear e2 h1
  have h3 := Backtrack.even h2
  have e3 : 2 * (2093390532109442148854046084 * q - 68) = 4186781064218884297708092168 * q - 136 := by omega
  rw [e3] at h3
  clear e3 h2
  have h4 := Backtrack.odd h3
    (show 3 * (2791187376145922865138728112 * q - 91) + 1 = 2 * (4186781064218884297708092168 * q - 136) by omega)
  clear h3
  have h5 := Backtrack.odd h4
    (show 3 * (1860791584097281910092485408 * q - 61) + 1 = 2 * (2791187376145922865138728112 * q - 91) by omega)
  clear h4
  have h6 := Backtrack.odd h5
    (show 3 * (1240527722731521273394990272 * q - 41) + 1 = 2 * (1860791584097281910092485408 * q - 61) by omega)
  clear h5
  have h7 := Backtrack.even h6
  have e7 : 2 * (1240527722731521273394990272 * q - 41) = 2481055445463042546789980544 * q - 82 := by omega
  rw [e7] at h7
  clear e7 h6
  have h8 := Backtrack.odd h7
    (show 3 * (1654036963642028364526653696 * q - 55) + 1 = 2 * (2481055445463042546789980544 * q - 82) by omega)
  clear h7
  have h9 := Backtrack.odd h8
    (show 3 * (1102691309094685576351102464 * q - 37) + 1 = 2 * (1654036963642028364526653696 * q - 55) by omega)
  clear h8
  have h10 := Backtrack.odd h9
    (show 3 * (735127539396457050900734976 * q - 25) + 1 = 2 * (1102691309094685576351102464 * q - 37) by omega)
  clear h9
  have h11 := Backtrack.even h10
  have e11 : 2 * (735127539396457050900734976 * q - 25) = 1470255078792914101801469952 * q - 50 := by omega
  rw [e11] at h11
  clear e11 h10
  have h12 := Backtrack.even h11
  have e12 : 2 * (1470255078792914101801469952 * q - 50) = 2940510157585828203602939904 * q - 100 := by omega
  rw [e12] at h12
  clear e12 h11
  have h13 := Backtrack.odd h12
    (show 3 * (1960340105057218802401959936 * q - 67) + 1 = 2 * (2940510157585828203602939904 * q - 100) by omega)
  clear h12
  have h14 := Backtrack.even h13
  have e14 : 2 * (1960340105057218802401959936 * q - 67) = 3920680210114437604803919872 * q - 134 := by omega
  rw [e14] at h14
  clear e14 h13
  have h15 := Backtrack.even h14
  have e15 : 2 * (3920680210114437604803919872 * q - 134) = 7841360420228875209607839744 * q - 268 := by omega
  rw [e15] at h15
  clear e15 h14
  have h16 := Backtrack.odd h15
    (show 3 * (5227573613485916806405226496 * q - 179) + 1 = 2 * (7841360420228875209607839744 * q - 268) by omega)
  clear h15
  have h17 := Backtrack.even h16
  have e17 : 2 * (5227573613485916806405226496 * q - 179) = 10455147226971833612810452992 * q - 358 := by omega
  rw [e17] at h17
  clear e17 h16
  have h18 := Backtrack.odd h17
    (show 3 * (6970098151314555741873635328 * q - 239) + 1 = 2 * (10455147226971833612810452992 * q - 358) by omega)
  clear h17
  have h19 := Backtrack.even h18
  have e19 : 2 * (6970098151314555741873635328 * q - 239) = 13940196302629111483747270656 * q - 478 := by omega
  rw [e19] at h19
  clear e19 h18
  have h20 := Backtrack.odd h19
    (show 3 * (9293464201752740989164847104 * q - 319) + 1 = 2 * (13940196302629111483747270656 * q - 478) by omega)
  clear h19
  have h21 := Backtrack.even h20
  have e21 : 2 * (9293464201752740989164847104 * q - 319) = 18586928403505481978329694208 * q - 638 := by omega
  rw [e21] at h21
  clear e21 h20
  have h22 := Backtrack.even h21
  have e22 : 2 * (18586928403505481978329694208 * q - 638) = 37173856807010963956659388416 * q - 1276 := by omega
  rw [e22] at h22
  clear e22 h21
  have h23 := Backtrack.even h22
  have e23 : 2 * (37173856807010963956659388416 * q - 1276) = 74347713614021927913318776832 * q - 2552 := by omega
  rw [e23] at h23
  clear e23 h22
  have h24 := Backtrack.even h23
  have e24 : 2 * (74347713614021927913318776832 * q - 2552) = 148695427228043855826637553664 * q - 5104 := by omega
  rw [e24] at h24
  clear e24 h23
  have h25 := Backtrack.odd h24
    (show 3 * (99130284818695903884425035776 * q - 3403) + 1 = 2 * (148695427228043855826637553664 * q - 5104) by omega)
  clear h24
  have h26 := Backtrack.odd h25
    (show 3 * (66086856545797269256283357184 * q - 2269) + 1 = 2 * (99130284818695903884425035776 * q - 3403) by omega)
  clear h25
  have h27 := Backtrack.odd h26
    (show 3 * (44057904363864846170855571456 * q - 1513) + 1 = 2 * (66086856545797269256283357184 * q - 2269) by omega)
  clear h26
  have h28 := Backtrack.odd h27
    (show 3 * (29371936242576564113903714304 * q - 1009) + 1 = 2 * (44057904363864846170855571456 * q - 1513) by omega)
  clear h27
  have h29 := Backtrack.odd h28
    (show 3 * (19581290828384376075935809536 * q - 673) + 1 = 2 * (29371936242576564113903714304 * q - 1009) by omega)
  clear h28
  have h30 := Backtrack.even h29
  have e30 : 2 * (19581290828384376075935809536 * q - 673) = 39162581656768752151871619072 * q - 1346 := by omega
  rw [e30] at h30
  clear e30 h29
  have h31 := Backtrack.even h30
  have e31 : 2 * (39162581656768752151871619072 * q - 1346) = 78325163313537504303743238144 * q - 2692 := by omega
  rw [e31] at h31
  clear e31 h30
  have h32 := Backtrack.even h31
  have e32 : 2 * (78325163313537504303743238144 * q - 2692) = 156650326627075008607486476288 * q - 5384 := by omega
  rw [e32] at h32
  clear e32 h31
  have h33 := Backtrack.even h32
  have e33 : 2 * (156650326627075008607486476288 * q - 5384) = 313300653254150017214972952576 * q - 10768 := by omega
  rw [e33] at h33
  clear e33 h32
  have h34 := Backtrack.even h33
  have e34 : 2 * (313300653254150017214972952576 * q - 10768) = 626601306508300034429945905152 * q - 21536 := by omega
  rw [e34] at h34
  clear e34 h33
  have h35 := Backtrack.even h34
  have e35 : 2 * (626601306508300034429945905152 * q - 21536) = 1253202613016600068859891810304 * q - 43072 := by omega
  rw [e35] at h35
  clear e35 h34
  have h36 := Backtrack.odd h35
    (show 3 * (835468408677733379239927873536 * q - 28715) + 1 = 2 * (1253202613016600068859891810304 * q - 43072) by omega)
  clear h35
  have h37 := Backtrack.even h36
  have e37 : 2 * (835468408677733379239927873536 * q - 28715) = 1670936817355466758479855747072 * q - 57430 := by omega
  rw [e37] at h37
  clear e37 h36
  have h38 := Backtrack.odd h37
    (show 3 * (1113957878236977838986570498048 * q - 38287) + 1 = 2 * (1670936817355466758479855747072 * q - 57430) by omega)
  clear h37
  have h39 := Backtrack.odd h38
    (show 3 * (742638585491318559324380332032 * q - 25525) + 1 = 2 * (1113957878236977838986570498048 * q - 38287) by omega)
  clear h38
  have h40 := Backtrack.odd h39
    (show 3 * (495092390327545706216253554688 * q - 17017) + 1 = 2 * (742638585491318559324380332032 * q - 25525) by omega)
  clear h39
  have h41 := Backtrack.odd h40
    (show 3 * (330061593551697137477502369792 * q - 11345) + 1 = 2 * (495092390327545706216253554688 * q - 17017) by omega)
  clear h40
  have h42 := Backtrack.even h41
  have e42 : 2 * (330061593551697137477502369792 * q - 11345) = 660123187103394274955004739584 * q - 22690 := by omega
  rw [e42] at h42
  clear e42 h41
  have h43 := Backtrack.odd h42
    (show 3 * (440082124735596183303336493056 * q - 15127) + 1 = 2 * (660123187103394274955004739584 * q - 22690) by omega)
  clear h42
  have h44 := Backtrack.odd h43
    (show 3 * (293388083157064122202224328704 * q - 10085) + 1 = 2 * (440082124735596183303336493056 * q - 15127) by omega)
  clear h43
  have h45 := Backtrack.even h44
  have e45 : 2 * (293388083157064122202224328704 * q - 10085) = 586776166314128244404448657408 * q - 20170 := by omega
  rw [e45] at h45
  clear e45 h44
  have h46 := Backtrack.odd h45
    (show 3 * (391184110876085496269632438272 * q - 13447) + 1 = 2 * (586776166314128244404448657408 * q - 20170) by omega)
  clear h45
  have h47 := Backtrack.odd h46
    (show 3 * (260789407250723664179754958848 * q - 8965) + 1 = 2 * (391184110876085496269632438272 * q - 13447) by omega)
  clear h46
  have h48 := Backtrack.odd h47
    (show 3 * (173859604833815776119836639232 * q - 5977) + 1 = 2 * (260789407250723664179754958848 * q - 8965) by omega)
  clear h47
  have h49 := Backtrack.odd h48
    (show 3 * (115906403222543850746557759488 * q - 3985) + 1 = 2 * (173859604833815776119836639232 * q - 5977) by omega)
  clear h48
  have h50 := Backtrack.even h49
  have e50 : 2 * (115906403222543850746557759488 * q - 3985) = 231812806445087701493115518976 * q - 7970 := by omega
  rw [e50] at h50
  clear e50 h49
  have h51 := Backtrack.even h50
  have e51 : 2 * (231812806445087701493115518976 * q - 7970) = 463625612890175402986231037952 * q - 15940 := by omega
  rw [e51] at h51
  clear e51 h50
  have h52 := Backtrack.odd h51
    (show 3 * (309083741926783601990820691968 * q - 10627) + 1 = 2 * (463625612890175402986231037952 * q - 15940) by omega)
  clear h51
  have h53 := Backtrack.odd h52
    (show 3 * (206055827951189067993880461312 * q - 7085) + 1 = 2 * (309083741926783601990820691968 * q - 10627) by omega)
  clear h52
  have h54 := Backtrack.even h53
  have e54 : 2 * (206055827951189067993880461312 * q - 7085) = 412111655902378135987760922624 * q - 14170 := by omega
  rw [e54] at h54
  clear e54 h53
  have h55 := Backtrack.even h54
  have e55 : 2 * (412111655902378135987760922624 * q - 14170) = 824223311804756271975521845248 * q - 28340 := by omega
  rw [e55] at h55
  clear e55 h54
  have h56 := Backtrack.even h55
  have e56 : 2 * (824223311804756271975521845248 * q - 28340) = 1648446623609512543951043690496 * q - 56680 := by omega
  rw [e56] at h56
  clear e56 h55
  have h57 := Backtrack.odd h56
    (show 3 * (1098964415739675029300695793664 * q - 37787) + 1 = 2 * (1648446623609512543951043690496 * q - 56680) by omega)
  clear h56
  have h58 := Backtrack.even h57
  have e58 : 2 * (1098964415739675029300695793664 * q - 37787) = 2197928831479350058601391587328 * q - 75574 := by omega
  rw [e58] at h58
  clear e58 h57
  have h59 := Backtrack.odd h58
    (show 3 * (1465285887652900039067594391552 * q - 50383) + 1 = 2 * (2197928831479350058601391587328 * q - 75574) by omega)
  clear h58
  have h60 := Backtrack.odd h59
    (show 3 * (976857258435266692711729594368 * q - 33589) + 1 = 2 * (1465285887652900039067594391552 * q - 50383) by omega)
  clear h59
  have h61 := Backtrack.odd h60
    (show 3 * (651238172290177795141153062912 * q - 22393) + 1 = 2 * (976857258435266692711729594368 * q - 33589) by omega)
  clear h60
  have h62 := Backtrack.odd h61
    (show 3 * (434158781526785196760768708608 * q - 14929) + 1 = 2 * (651238172290177795141153062912 * q - 22393) by omega)
  clear h61
  have h63 := Backtrack.odd h62
    (show 3 * (289439187684523464507179139072 * q - 9953) + 1 = 2 * (434158781526785196760768708608 * q - 14929) by omega)
  clear h62
  have h64 := Backtrack.even h63
  have e64 : 2 * (289439187684523464507179139072 * q - 9953) = 578878375369046929014358278144 * q - 19906 := by omega
  rw [e64] at h64
  clear e64 h63
  have h65 := Backtrack.odd h64
    (show 3 * (385918916912697952676238852096 * q - 13271) + 1 = 2 * (578878375369046929014358278144 * q - 19906) by omega)
  clear h64
  have h66 := Backtrack.even h65
  have e66 : 2 * (385918916912697952676238852096 * q - 13271) = 771837833825395905352477704192 * q - 26542 := by omega
  rw [e66] at h66
  clear e66 h65
  have h67 := Backtrack.odd h66
    (show 3 * (514558555883597270234985136128 * q - 17695) + 1 = 2 * (771837833825395905352477704192 * q - 26542) by omega)
  clear h66
  have h68 := Backtrack.odd h67
    (show 3 * (343039037255731513489990090752 * q - 11797) + 1 = 2 * (514558555883597270234985136128 * q - 17695) by omega)
  clear h67
  have h69 := Backtrack.even h68
  have e69 : 2 * (343039037255731513489990090752 * q - 11797) = 686078074511463026979980181504 * q - 23594 := by omega
  rw [e69] at h69
  clear e69 h68
  have h70 := Backtrack.even h69
  have e70 : 2 * (686078074511463026979980181504 * q - 23594) = 1372156149022926053959960363008 * q - 47188 := by omega
  rw [e70] at h70
  clear e70 h69
  have h71 := Backtrack.odd h70
    (show 3 * (914770766015284035973306908672 * q - 31459) + 1 = 2 * (1372156149022926053959960363008 * q - 47188) by omega)
  clear h70
  have h72 := Backtrack.even h71
  have e72 : 2 * (914770766015284035973306908672 * q - 31459) = 1829541532030568071946613817344 * q - 62918 := by omega
  rw [e72] at h72
  clear e72 h71
  have h73 := Backtrack.even h72
  have e73 : 2 * (1829541532030568071946613817344 * q - 62918) = 3659083064061136143893227634688 * q - 125836 := by omega
  rw [e73] at h73
  clear e73 h72
  have h74 := Backtrack.even h73
  have e74 : 2 * (3659083064061136143893227634688 * q - 125836) = 7318166128122272287786455269376 * q - 251672 := by omega
  rw [e74] at h74
  clear e74 h73
  have h75 := Backtrack.even h74
  have e75 : 2 * (7318166128122272287786455269376 * q - 251672) = 14636332256244544575572910538752 * q - 503344 := by omega
  rw [e75] at h75
  clear e75 h74
  have h76 := Backtrack.odd h75
    (show 3 * (9757554837496363050381940359168 * q - 335563) + 1 = 2 * (14636332256244544575572910538752 * q - 503344) by omega)
  clear h75
  have h77 := Backtrack.even h76
  have e77 : 2 * (9757554837496363050381940359168 * q - 335563) = 19515109674992726100763880718336 * q - 671126 := by omega
  rw [e77] at h77
  clear e77 h76
  have h78 := Backtrack.even h77
  have e78 : 2 * (19515109674992726100763880718336 * q - 671126) = 39030219349985452201527761436672 * q - 1342252 := by omega
  rw [e78] at h78
  clear e78 h77
  have h79 := Backtrack.odd h78
    (show 3 * (26020146233323634801018507624448 * q - 894835) + 1 = 2 * (39030219349985452201527761436672 * q - 1342252) by omega)
  clear h78
  have h80 := Backtrack.odd h79
    (show 3 * (17346764155549089867345671749632 * q - 596557) + 1 = 2 * (26020146233323634801018507624448 * q - 894835) by omega)
  clear h79
  have h81 := Backtrack.odd h80
    (show 3 * (11564509437032726578230447833088 * q - 397705) + 1 = 2 * (17346764155549089867345671749632 * q - 596557) by omega)
  clear h80
  have h82 := Backtrack.even h81
  have e82 : 2 * (11564509437032726578230447833088 * q - 397705) = 23129018874065453156460895666176 * q - 795410 := by omega
  rw [e82] at h82
  clear e82 h81
  have h83 := Backtrack.even h82
  have e83 : 2 * (23129018874065453156460895666176 * q - 795410) = 46258037748130906312921791332352 * q - 1590820 := by omega
  rw [e83] at h83
  clear e83 h82
  have h84 := Backtrack.even h83
  have e84 : 2 * (46258037748130906312921791332352 * q - 1590820) = 92516075496261812625843582664704 * q - 3181640 := by omega
  rw [e84] at h84
  clear e84 h83
  have h85 := Backtrack.even h84
  have e85 : 2 * (92516075496261812625843582664704 * q - 3181640) = 185032150992523625251687165329408 * q - 6363280 := by omega
  rw [e85] at h85
  clear e85 h84
  have h86 := Backtrack.odd h85
    (show 3 * (123354767328349083501124776886272 * q - 4242187) + 1 = 2 * (185032150992523625251687165329408 * q - 6363280) by omega)
  clear h85
  have h87 := Backtrack.odd h86
    (show 3 * (82236511552232722334083184590848 * q - 2828125) + 1 = 2 * (123354767328349083501124776886272 * q - 4242187) by omega)
  clear h86
  have h88 := Backtrack.odd h87
    (show 3 * (54824341034821814889388789727232 * q - 1885417) + 1 = 2 * (82236511552232722334083184590848 * q - 2828125) by omega)
  clear h87
  have h89 := Backtrack.odd h88
    (show 3 * (36549560689881209926259193151488 * q - 1256945) + 1 = 2 * (54824341034821814889388789727232 * q - 1885417) by omega)
  clear h88
  have h90 := Backtrack.even h89
  have e90 : 2 * (36549560689881209926259193151488 * q - 1256945) = 73099121379762419852518386302976 * q - 2513890 := by omega
  rw [e90] at h90
  clear e90 h89
  have h91 := Backtrack.odd h90
    (show 3 * (48732747586508279901678924201984 * q - 1675927) + 1 = 2 * (73099121379762419852518386302976 * q - 2513890) by omega)
  clear h90
  have h92 := Backtrack.odd h91
    (show 3 * (32488498391005519934452616134656 * q - 1117285) + 1 = 2 * (48732747586508279901678924201984 * q - 1675927) by omega)
  clear h91
  have h93 := Backtrack.odd h92
    (show 3 * (21658998927337013289635077423104 * q - 744857) + 1 = 2 * (32488498391005519934452616134656 * q - 1117285) by omega)
  clear h92
  have h94 := Backtrack.even h93
  have e94 : 2 * (21658998927337013289635077423104 * q - 744857) = 43317997854674026579270154846208 * q - 1489714 := by omega
  rw [e94] at h94
  clear e94 h93
  have h95 := Backtrack.even h94
  have e95 : 2 * (43317997854674026579270154846208 * q - 1489714) = 86635995709348053158540309692416 * q - 2979428 := by omega
  rw [e95] at h95
  clear e95 h94
  have h96 := Backtrack.even h95
  have e96 : 2 * (86635995709348053158540309692416 * q - 2979428) = 173271991418696106317080619384832 * q - 5958856 := by omega
  rw [e96] at h96
  clear e96 h95
  have h97 := Backtrack.odd h96
    (show 3 * (115514660945797404211387079589888 * q - 3972571) + 1 = 2 * (173271991418696106317080619384832 * q - 5958856) by omega)
  clear h96
  have h98 := Backtrack.odd h97
    (show 3 * (77009773963864936140924719726592 * q - 2648381) + 1 = 2 * (115514660945797404211387079589888 * q - 3972571) by omega)
  clear h97
  have h99 := Backtrack.even h98
  have e99 : 2 * (77009773963864936140924719726592 * q - 2648381) = 154019547927729872281849439453184 * q - 5296762 := by omega
  rw [e99] at h99
  clear e99 h98
  have h100 := Backtrack.odd h99
    (show 3 * (102679698618486581521232959635456 * q - 3531175) + 1 = 2 * (154019547927729872281849439453184 * q - 5296762) by omega)
  clear h99
  have h101 := Backtrack.odd h100
    (show 3 * (68453132412324387680821973090304 * q - 2354117) + 1 = 2 * (102679698618486581521232959635456 * q - 3531175) by omega)
  clear h100
  have h102 := Backtrack.even h101
  have e102 : 2 * (68453132412324387680821973090304 * q - 2354117) = 136906264824648775361643946180608 * q - 4708234 := by omega
  rw [e102] at h102
  clear e102 h101
  have h103 := Backtrack.odd h102
    (show 3 * (91270843216432516907762630787072 * q - 3138823) + 1 = 2 * (136906264824648775361643946180608 * q - 4708234) by omega)
  clear h102
  have h104 := Backtrack.odd h103
    (show 3 * (60847228810955011271841753858048 * q - 2092549) + 1 = 2 * (91270843216432516907762630787072 * q - 3138823) by omega)
  clear h103
  have h105 := Backtrack.even h104
  have e105 : 2 * (60847228810955011271841753858048 * q - 2092549) = 121694457621910022543683507716096 * q - 4185098 := by omega
  rw [e105] at h105
  clear e105 h104
  have h106 := Backtrack.even h105
  have e106 : 2 * (121694457621910022543683507716096 * q - 4185098) = 243388915243820045087367015432192 * q - 8370196 := by omega
  rw [e106] at h106
  clear e106 h105
  have h107 := Backtrack.odd h106
    (show 3 * (162259276829213363391578010288128 * q - 5580131) + 1 = 2 * (243388915243820045087367015432192 * q - 8370196) by omega)
  clear h106
  have h108 := Backtrack.even h107
  have e108 : 2 * (162259276829213363391578010288128 * q - 5580131) = 324518553658426726783156020576256 * q - 11160262 := by omega
  rw [e108] at h108
  clear e108 h107
  exact h108

theorem bridge_thirteen_clock (q : Nat) (hq : 0 < q) :
    iterate 164 (2 ^ 108 * q - 11160262) = 3 ^ 56 * q - 17 :=
  backtrack_actual (bridge_thirteen q hq)

theorem bridge_twentyfive (q : Nat) (hq : 0 < q) :
    Backtrack 4 6
      (2916 * q - 17) (4096 * q - 25) := by
  have h0 := Backtrack.nil (2916 * q - 17)
  have h1 := Backtrack.even h0
  have e1 : 2 * (2916 * q - 17) = 5832 * q - 34 := by omega
  rw [e1] at h1
  clear e1 h0
  have h2 := Backtrack.even h1
  have e2 : 2 * (5832 * q - 34) = 11664 * q - 68 := by omega
  rw [e2] at h2
  clear e2 h1
  have h3 := Backtrack.even h2
  have e3 : 2 * (11664 * q - 68) = 23328 * q - 136 := by omega
  rw [e3] at h3
  clear e3 h2
  have h4 := Backtrack.odd h3
    (show 3 * (15552 * q - 91) + 1 = 2 * (23328 * q - 136) by omega)
  clear h3
  have h5 := Backtrack.odd h4
    (show 3 * (10368 * q - 61) + 1 = 2 * (15552 * q - 91) by omega)
  clear h4
  have h6 := Backtrack.odd h5
    (show 3 * (6912 * q - 41) + 1 = 2 * (10368 * q - 61) by omega)
  clear h5
  have h7 := Backtrack.even h6
  have e7 : 2 * (6912 * q - 41) = 13824 * q - 82 := by omega
  rw [e7] at h7
  clear e7 h6
  have h8 := Backtrack.odd h7
    (show 3 * (9216 * q - 55) + 1 = 2 * (13824 * q - 82) by omega)
  clear h7
  have h9 := Backtrack.odd h8
    (show 3 * (6144 * q - 37) + 1 = 2 * (9216 * q - 55) by omega)
  clear h8
  have h10 := Backtrack.odd h9
    (show 3 * (4096 * q - 25) + 1 = 2 * (6144 * q - 37) by omega)
  clear h9
  exact h10

theorem fourth_bounds (R w : Nat) (hR : 14 ≤ R) (hw : 0 < w) :
    0 < fourthSource R w ∧ fourthSource R w < mainSource R w := by
  have hb := MinimumSeventeenTransition.source_bounds R w hR hw
  have hp : 8192 ≤ 2 ^ (2 * R + 13) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (show 13 ≤ 2 * R + 13 by omega)
  have hwp := Nat.mul_le_mul hp (show 1 ≤ w by omega)
  have hs : 2 ^ (2 * R + 13) ≤ 2 ^ (2 * R + 15) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hws := Nat.mul_le_mul_right w hs
  unfold fourthSource secondSource at *
  omega

theorem fourth_prefix (R w : Nat) (hw : 0 < w) :
    iterate (4 * R + 26) (fourthSource R w) = 1594323 * (9 ^ R * w) - 1 := by
  have h := backtrack_actual (MinimumInverseEscape.pure_inverse (2 * R + 13) w hw)
  have hp : 3 ^ (2 * R + 13) * w = 1594323 * (9 ^ R * w) := by
    rw [Nat.pow_add, Nat.pow_mul]
    ac_rfl
  simpa only [fourthSource, Nat.zero_add,
    show 2 * (2 * R + 13) = 4 * R + 26 by omega, hp] using h

theorem fourth_profile (R w r u : Nat) (hr : 5 ≤ r) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u) :
    iterate (4 * R + 100 + 18 * r) (fourthSource R w) = 48 * scalar r u - 17 := by
  let d := r - 5
  have hd : r = d + 5 := by dsimp [d]; omega
  let q := 16 * 1594323 * (2048 ^ d * u)
  have hq : 0 < q := by
    exact Nat.mul_pos (by decide) (Nat.mul_pos (Nat.pow_pos (by decide)) hu)
  have hpower : 2 ^ (57 + 11 * r) = 2 ^ 112 * 2048 ^ d := by
    rw [hd, show 57 + 11 * (d + 5) = 112 + 11 * d by omega,
      Nat.pow_add, Nat.pow_mul]
  have hstart : 1594323 * (9 ^ R * w) - 1 = 2 ^ 108 * q - 11160262 := by
    rw [hpower] at hX
    dsimp [q]
    have he : 2 ^ 108 * (16 * 1594323 * (2048 ^ d * u)) =
        1594323 * (2 ^ 112 * 2048 ^ d * u) := by
      have hc : 2 ^ 108 * (16 * 1594323) = 1594323 * 2 ^ 112 := by decide
      calc
        _ = (2 ^ 108 * (16 * 1594323)) * (2048 ^ d * u) := by ac_rfl
        _ = _ := by rw [hc]; ac_rfl
    rw [he, ← hX]
    omega
  have hmiddle : 3 ^ 56 * q - 17 = 2048 ^ d * (16 * 3 ^ 69 * u) - 17 := by
    change 3 ^ 56 * (16 * 1594323 * (2048 ^ d * u)) - 17 = _
    congr 1
    have hc : 3 ^ 56 * (16 * 1594323) = 16 * 3 ^ 69 := by decide
    calc
      _ = (3 ^ 56 * (16 * 1594323)) * (2048 ^ d * u) := by ac_rfl
      _ = _ := by rw [hc]; ac_rfl
  have hpos : 0 < 16 * 3 ^ 69 * u := Nat.mul_pos (by decide) hu
  have hfinish : 2187 ^ d * (16 * 3 ^ 69 * u) = 48 * scalar r u := by
    unfold scalar
    rw [hd, show 33 + 7 * (d + 5) = 68 + 7 * d by omega,
      Nat.pow_add, Nat.pow_mul]
    have hc : 16 * 3 ^ 69 = 48 * 3 ^ 68 := by decide
    calc
      _ = (16 * 3 ^ 69) * (2187 ^ d * u) := by ac_rfl
      _ = _ := by rw [hc]; ac_rfl
  have hc : 4 * R + 100 + 18 * r = (4 * R + 26) + (164 + 18 * d) := by omega
  rw [hc, iterate_add, fourth_prefix R w hw, hstart,
    iterate_add 164 (18 * d), bridge_thirteen_clock q hq, hmiddle,
    MinimumNegativeCycle.cycle_clock d _ hpos, hfinish]

theorem secondary_profiles (a j q : Nat) (ha : 0 < a) (hq : 0 < q)
    (hT : 9 * a + 1 = 2 ^ (9 + 11 * j) * q) :
    iterate (16 + 18 * j) (72 * a - 17) = 4 * secondaryScalar j q - 17 ∧
    iterate (21 + 18 * j) (48 * a - 17) = 3 * secondaryScalar j q - 17 := by
  let v := 2048 ^ j * q
  have hv : 0 < v := Nat.mul_pos (Nat.pow_pos (by decide)) hq
  have hpow : 2 ^ (9 + 11 * j) * q = 512 * v := by
    rw [Nat.pow_add, Nat.pow_mul]
    change 512 * 2048 ^ j * q = 512 * (2048 ^ j * q)
    ac_rfl
  rw [hpow] at hT
  have hn : 72 * a - 17 = 4096 * v - 25 := by omega
  have hs0 : C (48 * a - 17) = 144 * a - 50 := by unfold C; split <;> omega
  have hs1 : C (144 * a - 50) = 72 * a - 25 := by unfold C; split <;> omega
  have hs : iterate 2 (48 * a - 17) = 4096 * v - 33 := by
    simp only [iterate, hs0, hs1]
    omega
  have hnclock : iterate 16 (4096 * v - 25) = 2916 * v - 17 :=
    backtrack_actual (bridge_twentyfive v hv)
  have hmidN : 2916 * v - 17 = 2048 ^ j * (2916 * q) - 17 := by
    dsimp [v]; congr 1; ac_rfl
  have hmidS : 2187 * v - 17 = 2048 ^ j * (2187 * q) - 17 := by
    dsimp [v]; congr 1; ac_rfl
  have hqN : 0 < 2916 * q := by omega
  have hqS : 0 < 2187 * q := by omega
  have hp : 3 ^ (6 + 7 * j) = 729 * 2187 ^ j := by rw [Nat.pow_add, Nat.pow_mul]
  refine ⟨?_, ?_⟩
  · rw [iterate_add 16 (18 * j), hn, hnclock, hmidN,
      MinimumNegativeCycle.cycle_clock j _ hqN]
    unfold secondaryScalar
    rw [hp]
    congr 1
    rw [← Nat.mul_assoc 4 (729 * 2187 ^ j) q,
      ← Nat.mul_assoc 4 729 (2187 ^ j)]
    change 2187 ^ j * (2916 * q) = 2916 * 2187 ^ j * q
    ac_rfl
  · rw [show 21 + 18 * j = 2 + (19 + 18 * j) by omega,
      iterate_add 2 (19 + 18 * j), hs, iterate_add 19 (18 * j),
      (MinimumSeventeenTransition.bridge_clocks v hv).1, hmidS,
      MinimumNegativeCycle.cycle_clock j _ hqS]
    unfold secondaryScalar
    rw [hp]
    congr 1
    rw [← Nat.mul_assoc 3 (729 * 2187 ^ j) q,
      ← Nat.mul_assoc 3 729 (2187 ^ j)]
    change 2187 ^ j * (2187 * q) = 2187 * 2187 ^ j * q
    ac_rfl


theorem pair_profiles (v : Nat) :
    iterate 10 (256 * v + 75) = 54 * v + 16 ∧
    iterate 7 (192 * v + 52) = 54 * v + 16 := by
  have f0_0 : C (256 * v + 75) = 768 * v + 226 := by unfold C; split <;> omega
  have f0_1 : C (768 * v + 226) = 384 * v + 113 := by unfold C; split <;> omega
  have f0_2 : C (384 * v + 113) = 1152 * v + 340 := by unfold C; split <;> omega
  have f0_3 : C (1152 * v + 340) = 576 * v + 170 := by unfold C; split <;> omega
  have f0_4 : C (576 * v + 170) = 288 * v + 85 := by unfold C; split <;> omega
  have f0_5 : C (288 * v + 85) = 864 * v + 256 := by unfold C; split <;> omega
  have f0_6 : C (864 * v + 256) = 432 * v + 128 := by unfold C; split <;> omega
  have f0_7 : C (432 * v + 128) = 216 * v + 64 := by unfold C; split <;> omega
  have f0_8 : C (216 * v + 64) = 108 * v + 32 := by unfold C; split <;> omega
  have f0_9 : C (108 * v + 32) = 54 * v + 16 := by unfold C; split <;> omega
  have f1_0 : C (192 * v + 52) = 96 * v + 26 := by unfold C; split <;> omega
  have f1_1 : C (96 * v + 26) = 48 * v + 13 := by unfold C; split <;> omega
  have f1_2 : C (48 * v + 13) = 144 * v + 40 := by unfold C; split <;> omega
  have f1_3 : C (144 * v + 40) = 72 * v + 20 := by unfold C; split <;> omega
  have f1_4 : C (72 * v + 20) = 36 * v + 10 := by unfold C; split <;> omega
  have f1_5 : C (36 * v + 10) = 18 * v + 5 := by unfold C; split <;> omega
  have f1_6 : C (18 * v + 5) = 54 * v + 16 := by unfold C; split <;> omega
  exact ⟨by simp only [iterate, f0_0, f0_1, f0_2, f0_3, f0_4, f0_5, f0_6, f0_7, f0_8, f0_9],
    by simp only [iterate, f1_0, f1_1, f1_2, f1_3, f1_4, f1_5, f1_6]⟩

theorem scalar_pair_meeting (b : Nat) (hb : b % 64 = 23) :
    iterate 7 (3 * b - 17) = iterate 10 (4 * b - 17) := by
  let v := b / 64
  have hv : b = 64 * v + 23 := by dsimp [v]; omega
  have hn : 4 * b - 17 = 256 * v + 75 := by omega
  have hs : 3 * b - 17 = 192 * v + 52 := by omega
  rw [hn, hs, (pair_profiles v).1, (pair_profiles v).2]

theorem nested_meeting (R w r u j q : Nat) (hr : 5 ≤ r) (hw : 0 < w)
    (hu : 0 < u) (hq : 0 < q)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hb : secondaryScalar j q % 64 = 23) :
    iterate (4 * R + 128 + 18 * r + 18 * j) (fourthSource R w) =
      iterate (5 * R + 117 + 18 * r + 18 * j) (mainSource R w) := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hN := (MinimumSeventeenTransition.three_sources R w r u hw hu hX).1
  have hS := fourth_profile R w r u hr hw hu hX
  have hl := secondary_profiles (scalar r u) j q ha hq hT
  have hcS : 4 * R + 128 + 18 * r + 18 * j =
      (4 * R + 100 + 18 * r) + ((21 + 18 * j) + 7) := by omega
  have hcN : 5 * R + 117 + 18 * r + 18 * j =
      (5 * R + 91 + 18 * r) + ((16 + 18 * j) + 10) := by omega
  rw [hcS, hcN, iterate_add (4 * R + 100 + 18 * r),
    iterate_add (5 * R + 91 + 18 * r), hS, hN,
    iterate_add (21 + 18 * j) 7, iterate_add (16 + 18 * j) 10,
    hl.1, hl.2, scalar_pair_meeting _ hb]

theorem nested_not_least (R w r u j q : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r)
    (hw : 0 < w) (hu : 0 < u) (hq : 0 < q)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q)
    (hb : secondaryScalar j q % 64 = 23) : ¬ LeastCounterexample (mainSource R w) := by
  intro hn
  have hbound := fourth_bounds R w hR hw
  have hm := nested_meeting R w r u j q hr hw hu hq hX hT hb
  have hle := least_coalescing_predecessor hn hbound.1 hm
  omega

set_option maxHeartbeats 1000000 in
theorem finite_exit_units :
    ∀ c : Fin 64, c.val % 2 = 1 →
      ∃ e : Fin 64, e.val % 2 = 1 ∧ (c.val * e.val) % 64 = 23 := by
  decide +kernel


theorem pure_nested_lift (r j B : Nat) :
    ∃ R u q, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q % 64 = 23 := by
  let m := 57 + 11 * r
  let K := 9 + 11 * j
  let D := 2 ^ m
  let E := 2 ^ K
  let A := 3 ^ (35 + 7 * r)
  let c := 3 ^ (6 + 7 * j)
  have hcodd : c % 2 = 1 := by dsimp [c]; rw [Nat.pow_mod]; simp
  have hcf : (c % 64) % 2 = 1 := by omega
  obtain ⟨eps, heodd, heunit⟩ :=
    finite_exit_units ⟨c % 64, Nat.mod_lt _ (by decide)⟩ hcf
  have hepos : 0 < eps.val := by omega
  have helt : eps.val < 64 := eps.isLt
  have heunit' : (c * eps.val) % 64 = 23 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt helt]
    exact heunit
  have hA : A % 2 = 1 := by dsimp [A]; rw [Nat.pow_mod]; simp
  have hD : D = 8 * 2 ^ (54 + 11 * r) := by
    dsimp [D, m]
    rw [show 57 + 11 * r = (54 + 11 * r) + 3 by omega, Nat.pow_add]
    omega
  let C := 7 * A + D + (64 - eps.val) * D * E
  have hbase : (A + C) % 8 = 0 := by
    have he : A + C = 8 * (A + 2 ^ (54 + 11 * r) +
        (64 - eps.val) * 2 ^ (54 + 11 * r) * E) := by
      unfold C
      rw [hD]
      grind
    rw [he]
    omega
  obtain ⟨R, Q, hB, hR, hQ⟩ := unbounded_affine_lift (m + K + 3) A C B hA hbase
  have hpow : 2 ^ (m + K + 3 + 3) = 64 * (D * E) := by
    rw [show m + K + 3 + 3 = (m + K) + 6 by omega, Nat.pow_add,
      Nat.pow_add]
    change (D * E) * 64 = 64 * (D * E)
    omega
  rw [hpow] at hQ
  have hDpos : 0 < D := Nat.two_pow_pos m
  have hpositive : 0 < A * 9 ^ R + C := by unfold C; omega
  have hQpos : 0 < Q := Nat.pos_of_mul_pos_left (hQ ▸ hpositive)
  let q := 64 * (Q - 1) + eps.val
  have hqpos : 0 < q := by dsimp [q]; omega
  have hqmod : q % 64 = eps.val := by dsimp [q]; omega
  have hqsum : q + (64 - eps.val) = 64 * Q := by dsimp [q]; omega
  have hpad : D * E * q + (64 - eps.val) * D * E = 64 * (D * E) * Q := by
    calc
      _ = (D * E) * (q + (64 - eps.val)) := by
        rw [Nat.mul_add (D * E) q (64 - eps.val)]
        ac_rfl
      _ = (D * E) * (64 * Q) := congrArg (fun z => (D * E) * z) hqsum
      _ = _ := by ac_rfl
  have hstart : A * (9 ^ R + 7) + D + (64 - eps.val) * D * E =
      64 * (D * E) * Q := by
    rw [Nat.mul_add, show A * 7 = 7 * A by omega]
    simpa only [C, Nat.add_assoc] using hQ
  have hsum : A * (9 ^ R + 7) + D = D * (E * q) := by
    have hh := Nat.add_right_cancel (hstart.trans hpad.symm)
    simpa only [Nat.mul_assoc] using hh
  have hdiv : D ∣ A * (9 ^ R + 7) := by
    apply (Nat.dvd_add_iff_left (Nat.dvd_refl D)).mpr
    exact ⟨E * q, hsum⟩
  obtain ⟨u, hu⟩ := odd_power_cancel m A (9 ^ R + 7) hA hdiv
  have hupositive : 0 < 9 ^ R + 7 := Nat.succ_pos (9 ^ R + 6)
  have hup : 0 < u := Nat.pos_of_mul_pos_left (hu ▸ hupositive)
  have hprod : D * (A * u + 1) = D * (E * q) := by
    have he : D * (A * u + 1) = A * (D * u) + D := by
      rw [Nat.mul_add, Nat.mul_one]
      congr 1
      ac_rfl
    rw [he, ← hu]
    exact hsum
  have hcancel := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos m) hprod
  have hscalar : A * u = 9 * scalar r u := by
    unfold A scalar
    rw [show 35 + 7 * r = (33 + 7 * r) + 2 by omega, Nat.pow_add]
    ac_rfl
  rw [hscalar] at hcancel
  have hguard : secondaryScalar j q % 64 = 23 := by
    change (c * q) % 64 = 23
    rw [Nat.mul_mod, hqmod]
    rw [Nat.mul_mod, Nat.mod_eq_of_lt helt] at heunit'
    exact heunit'
  exact ⟨R, u, q, hB, hR, hup, hqpos, hu, hcancel, hguard⟩

theorem weighted_nested_lift (R r j B : Nat) :
    ∃ w u q, B < w ∧ 0 < u ∧ 0 < q ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q ∧
      secondaryScalar j q % 64 = 23 := by
  obtain ⟨S, u, q, hS, _, hu, hq, hX, hT, hb⟩ := pure_nested_lift r j (R + B + 1)
  refine ⟨9 ^ (S - R), u, q, ?_, hu, hq, ?_, hT, hb⟩
  · exact Nat.lt_trans (show B < S - R by omega) (Nat.lt_pow_self (by decide : 1 < 9))
  · rw [← Nat.pow_add, show R + (S - R) = S by omega]
    exact hX

theorem old_partner_separation (R w r u j q : Nat) (hj : 0 < j)
    (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u)
    (hT : 9 * scalar r u + 1 = 2 ^ (9 + 11 * j) * q) :
    ∀ s t, s ≤ 11 * j - 3 → t ≤ 11 * j - 3 →
      iterate (4 * R + 99 + 18 * r + s) (firstSource R w) ≠
        iterate (5 * R + 91 + 18 * r + t) (mainSource R w) ∧
      iterate (4 * R + 99 + 18 * r + s) (secondSource R w) ≠
        iterate (5 * R + 91 + 18 * r + t) (mainSource R w) := by
  have hd : 2 ^ ((11 * j - 3) + 12) ∣ 9 * scalar r u + 1 := by
    rw [show (11 * j - 3) + 12 = 9 + 11 * j by omega]
    exact ⟨q, hT⟩
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have hs := scalar_separation (11 * j - 3) (scalar r u) ha hd
  have ht := MinimumSeventeenTransition.three_sources R w r u hw hu hX
  intro s t hss htt
  simp only [iterate_add (4 * R + 99 + 18 * r) s,
    iterate_add (5 * R + 91 + 18 * r) t, ht.1, ht.2.1, ht.2.2]
  exact hs s t hss htt

theorem pure_escape_past_window (r H B : Nat) (hr : 5 ≤ r) :
    ∃ R u q, B < R ∧ 14 ≤ R ∧ 0 < u ∧ 0 < q ∧
      9 ^ R + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * (H + 1)) * q ∧
      secondaryScalar (H + 1) q % 64 = 23 ∧
      ¬ LeastCounterexample (mainSource R 1) ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 99 + 18 * r + s) (firstSource R 1) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R 1) ∧
        iterate (4 * R + 99 + 18 * r + s) (secondSource R 1) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R 1) := by
  obtain ⟨R, u, q, hB, hR, hu, hq, hX, hT, hb⟩ := pure_nested_lift r (H + 1) B
  have hx : 9 ^ R * 1 + 7 = 2 ^ (57 + 11 * r) * u := by simpa only [Nat.mul_one] using hX
  have hn := nested_not_least R 1 r u (H + 1) q hR hr (by decide) hu hq hx hT hb
  have hs := old_partner_separation R 1 r u (H + 1) q (by omega) (by decide) hu hx hT
  refine ⟨R, u, q, hB, hR, hu, hq, hX, hT, hb, hn, ?_⟩
  intro s t hss htt
  exact hs s t (by omega) (by omega)

theorem weighted_escape_past_window (R r H B : Nat) (hR : 14 ≤ R) (hr : 5 ≤ r) :
    ∃ w u q, B < w ∧ 0 < u ∧ 0 < q ∧
      9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u ∧
      9 * scalar r u + 1 = 2 ^ (9 + 11 * (H + 1)) * q ∧
      secondaryScalar (H + 1) q % 64 = 23 ∧
      ¬ LeastCounterexample (mainSource R w) ∧
      ∀ s t, s ≤ H → t ≤ H →
        iterate (4 * R + 99 + 18 * r + s) (firstSource R w) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R w) ∧
        iterate (4 * R + 99 + 18 * r + s) (secondSource R w) ≠
          iterate (5 * R + 91 + 18 * r + t) (mainSource R w) := by
  obtain ⟨w, u, q, hwB, hu, hq, hX, hT, hb⟩ := weighted_nested_lift R r (H + 1) B
  have hw : 0 < w := by omega
  have hn := nested_not_least R w r u (H + 1) q hR hr hw hu hq hX hT hb
  have hs := old_partner_separation R w r u (H + 1) q (by omega) hw hu hX hT
  refine ⟨w, u, q, hwB, hu, hq, hX, hT, hb, hn, ?_⟩
  intro s t hss htt
  exact hs s t (by omega) (by omega)


theorem fourth_shifted_profile (R w r u : Nat) (hr : 5 ≤ r) (hw : 0 < w) (hu : 0 < u)
    (hX : 9 ^ R * w + 7 = 2 ^ (57 + 11 * r) * u) :
    iterate (4 * R + 102 + 18 * r) (fourthSource R w) = 72 * scalar r u - 25 := by
  have ha : 0 < scalar r u := Nat.mul_pos (Nat.pow_pos (by decide)) hu
  have h0 : C (48 * scalar r u - 17) = 144 * scalar r u - 50 := by
    unfold C; split <;> omega
  have h1 : C (144 * scalar r u - 50) = 72 * scalar r u - 25 := by
    unfold C; split <;> omega
  rw [show 4 * R + 102 + 18 * r = (4 * R + 100 + 18 * r) + 2 by omega,
    iterate_add, fourth_profile R w r u hr hw hu hX]
  simp only [iterate, h0, h1]

#print axioms bridge_thirteen
#print axioms bridge_thirteen_clock
#print axioms bridge_twentyfive
#print axioms fourth_bounds
#print axioms fourth_prefix
#print axioms fourth_profile
#print axioms secondary_profiles
#print axioms pair_profiles
#print axioms scalar_pair_meeting
#print axioms nested_meeting
#print axioms nested_not_least
#print axioms finite_exit_units
#print axioms pure_nested_lift
#print axioms weighted_nested_lift
#print axioms old_partner_separation
#print axioms pure_escape_past_window
#print axioms weighted_escape_past_window
#print axioms fourth_shifted_profile

end MinimumSeventeenFourth
