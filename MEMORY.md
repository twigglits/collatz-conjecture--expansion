# Collatz project memory

Last updated: 2026-10-26 local time, after the parameter-dependent inverse bounds.

Research remains active with no external blocker. Previous goal turn:
progress (the immediate predecessor and fixed fourteen-even certificate).
Current turn: progress (20 kernel roots giving algebraic inverse bounds,
an exact negative-five minimum, a precision-boundary witness, and a
both-branch obstruction throughout the pure coordinate family).
The positive-integer Collatz conjecture remains unresolved.

LATEST ARTIFACTS:
lean/MinimumFiveInverseCone.lean, docs/MINIMUM-FIVE-INVERSE-CONE.md,
verify_minimum_five_inverse_cone.py, results/minimum-five-inverse-cone/.
All 20 roots passed fresh kernel dependency audits. None is axiom-free;
all use only propext, Quot.sound and, where needed, Classical.choice.
No native reduction, new mathematical axiom or external mathematical premise.

REFERENCE PATHS, KERNEL:
Reference c e o m starts at (0,0,c) and follows
  E inverse: (e,o,m) -> (e+1,o,2m),
  O inverse: (e,o,m) -> (e,o+1,(2m+1)/3), when integral.
For c=2: m>=2,o<=2e, 2^(2e-o)*(m-1)<=2*3^(2e-o).
The only states with m<5 are (0,0,2),(1,0,4),(1,1,3).
For c=5: m>=5,o<=2e, 2^(2e-o)*(m-1)<=4*3^(2e-o).
These are universal induction proofs, not finite graph certificates.

ACTUAL INVERSE LIFT AND MINIMA, KERNEL:
For b+c=3^K*v, e<=B and 2B<K, every Backtrack e o b p has
  p+m=2^(e+o)*3^(K-o)*v
with a reference offset m. No actual odd-count or total-depth bound
is assumed. The invariants supply o<=2e<K at each lifting step.
For c=2: 8^B*3^(K-2B)*v<=p+3 (a lower bound, not an exact minimum).
For c=5 and v>0: the exact minimum is 8^B*3^(K-2B)*v-5.
B inverse EOO blocks attain it, with e=B,o=2B and ordinary clock5B.
The compulsory halving in O is not included in e.

The strict precision condition cannot generally be weakened to 2B<=K.
precision_boundary_witness proves Backtrack 2 5 76 39, with
76+5=3^4 and39<8^2-5=59. Its forward shortcut word is OOOEOOE,
ordinary clock12. It violates both o<=2e and the proposed minimum
at B=2,K=4,v=1. This is a kernel witness, not just scratch evidence.

THIRD ENDPOINT AND BOTH BRANCHES, KERNEL:
Keep the existing coordinates
  X=9^R*w, X+7=2^(57+11r)*u, a=3^(33+7r)*u,
  9a+1=2^(9+11j)*q, b=3^(6+7j)*q,
  b=1+2^(3k+4)*v, d=9^(k+1)*v, N=4*8^R*w-5.
At target3d-5 the exact inverse minimum with e<=k+1 is
  W=3*8^(k+1)*v-5,
attained with e=k+1,o=2(k+1). The rewriting2W+13=3b is
written arithmetic and independently checked, not a separate kernel root.

For H defined by2H+5=3d, all inverse paths with e<=k obey
  9*8^k*v<=p+3.
backtrack_first proves the complete first-edge decomposition:
empty path, inverse O to U=d-2, or inverse E to3d-5.
The U branch uses the c=2 bound. The E branch uses the stronger
p+5>=27*8^k*v. Thus the conclusion covers both branches at H,
not merely inverse paths into U. These are complete shortcut paths.

half_third_profile proves that N reaches H at ordinary clock
  5R+117+18r+18j+5k.
This is one shared halving beyond the earlier immediate merger.
An integral H forces d odd. The inverse minimum at H is NOT determined.

PURE-SOURCE OBSTRUCTION, KERNEL:
For R>=26,r>=5,w>0 and all three coordinate equations,
  N+3 < 9*8^k*v.
Set z=8^k*v and rewrite the third coordinate with k=0, unit z.
The old scaled identity and the new universal comparison
  2*2^(72+11s+3t)<=3^(43+7s+2t) for s>=5,t>=26
imply8*(8^R*w)<=9z. The base coefficient check is (s,t)=(5,26),
then transport by2^11<=3^7 and2^3<=3^2.
Consequently every inverse predecessor of H with e<=k is strictly
larger than N. Every pure source hasR>=36, so this covers the entire
pure coordinate family with r>=5 and positive quotients.
The budget k is unbounded ACROSS instances, bounded WITHIN each instance.
This is an obstruction to a particular smaller-source search, not a
nonconvergence statement. Later mergers with the earlier small S remain
compatible. Budgets e>k, later targets and all-time coalescence stay open.

VERIFICATION 2026-10-26T21:21:55.023886+00:00:
All 102 prior manifest hashes authenticated; all 105 new hashes pass.
The old /tmp compiler and object cache were absent. Restored the public
Lean4.33.1 release using the existing authorized download command, with
no credentials accessed. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Rebuilt all45 dependencies sequentially with16 threads,158.851 seconds
in total. Every rebuilt object exactly matched its prior manifest hash.
The verifier then authenticated and reused those45 objects and freshly
built the new module in3.057 seconds. All46 cached objects now match
the new manifest. Reuse keeps source/log/object/compiler provenance and
copies imports into an isolated directory. Without --cache all46 builds
run sequentially. Do not rerun prior finite replays without a new reason.
Verifier session19000 and final development session47595 exited0.
Dependency rebuild99374, extraction63042 and download93187 also exited0.
All milestone jobs are terminal.

INDEPENDENT FINITE SCOPE:
Reference graphs through e<=24 have228,252 states:37,967 at c=2
(max o26),190,285 at c=5 (max o48). No odd-count or depth cap.
159 complete actual inverse trees match the affine reference formula;
79 certify exact offset-five minima independently. Budgets0..8,12,16,
precision2B+1,2B+2,2B+19 and selectedK4096; units1,2,3,17,2^128+1
as recorded. Largest generic target6621 bits.
33 additional complete half-endpoint trees cover the FULL budget k,
k0..8,12,16 andv1,3,17, including both inverse branches.
50 weighted N/U/W cases replay complete paths including N's growing
prefix. Weighted inverse trees are complete only at min(k,8);36 cases
use the full k budget. Their largest parameters occur in one large case
R4096,r128,j128,k4096, with weight15,175bits,N27,465,H28,878,
v15,890 and Nclock45,685. No enormous pure trajectory is materialized.
Total inverse states replayed116,842, ordinary forward steps3,314,934;
weighted N ordinary steps73,102 are counted separately. The inverse-state
count includes U/W witnesses and the precision-boundary witness.
There are2,340 additional finite coefficient comparisons.

NEXT LEADS, NOT FORMALIZED:
The new proof removes the need merely to increase the old fixed14-edge
certificate. Investigate later endpoints/residual pair9h+2,h, or actual
coordinate information when ternary precision is consumed. The relation
from the earlier handoff remains available:
  T*(U+2)+f=3^(2k+8+7j)*q,
whereT=2^(3k+4),f=9^(k+1), and3 does not divideq.
Also b=1+Tv is divisible by3, so3 does not dividev; v=2mod3 for
k even andv=1mod3 for k odd. These latter observations are written
arithmetic here, not new roots in the current module.

A modest sharpening is visible in two_reference: a nonempty reference
path cannot have o=2e, since then m<=3 and the three exceptional states
leave only the empty path at that equality. This could extend the
c=2 lift to the equality precision in some cases; the c=5 boundary
witness does not transfer automatically to c=2. No such strengthened
actual-path theorem has been compiled or claimed. Increasing a budget
by a constant still would not cover unrestricted ancestors or later merger.

Full family convergence, arbitrary least-source exclusion, nontrivial
cycles, divergence and the full Collatz objective remain open. The goal
is active. ATTEMPT and README include the new result and reproduction.
No agents, staging, commits or Git writes occurred. The index SHA256
remains13d988c0249cc78dd544ef4874e45f6835d3ac269a252b8ed98a609780ead6e0.

The preceding immediate-predecessor handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the immediate-predecessor size boundary.

Research remains active with no external blocker. Previous goal turn:
progress (20 variable odd-exit roots). Current turn: progress (21 kernel
roots for an immediate predecessor, its exact size boundary, unbounded
weighted exclusions, the pure-source obstruction and a bounded inverse
certificate). The positive-integer Collatz conjecture remains unresolved.
Continue with 16 Lean threads per process, sequential heavy checks and
authenticated dependency reuse. No new permission or external-state
change is needed to continue the mathematics.

LATEST ARTIFACTS:
lean/MinimumFivePredecessor.lean, docs/MINIMUM-FIVE-PREDECESSOR.md,
verify_minimum_five_predecessor.py, results/minimum-five-predecessor/.
All 21 roots passed fresh kernel dependency audits. finite_size_boundary
is axiom-free. The other 20 roots use only standard logical axioms.
finite_inverse_certificate uses propext and Quot.sound. No native
reduction, new mathematical axiom or external mathematical premise.

KEY SIMPLIFICATION, KERNEL:
The previous lead U=d-2 does not need a final odd-block condition.
For every k>=0 and positive odd v, d=9^(k+1)*v is odd and >=9,
so U=d-2 is positive and C(U)=3d-5. This is one ordinary odd step.
Keep the three earlier coordinates:
  X=9^R*w, X+7=2^(57+11r)*u, a=3^(33+7r)*u,
  9a+1=2^(9+11j)*q, b=3^(6+7j)*q,
  b=1+2^(3k+4)*v, d=9^(k+1)*v.
N=4*8^R*w-5 reaches 3d-5 at ordinary clock
  5R+116+18r+18j+5k.
Therefore U and N coalesce regardless of d=1 or3 mod4 and regardless
of the later odd-block residue. The merger requires v odd; the size
comparison below and inverse minimum do not require this parity.

EXACT SIZE BOUNDARY, KERNEL:
For R>=14,r>=5,w>0 and the coordinate equations, set s=r+j,t=R+k.
U<N if and only if SmallRegion(s,t), the following staircase:
  s=5 or6: 14<=t<=19;
  s=7 or8: 14<=t<=18;
  s=9 or10:14<=t<=17;
  s=11:   14<=t<=16;
  s=12 or13:14<=t<=15;
  s=14 or15:t=14.
Outside this region, N<U strictly. No equality case. The 39 (s,t)
pairs correspond to 392 admissible (R,r,j,k) quadruples.
This is uniform over every admissible positive weight, not a finite
sample claim. Positive odd v inside the region excludes N as least.
For each fixed quadruple in the region, weights beyond every bound
realize this exclusion. CandidateEscape bundles the positive quotients,
three equations, v odd, positive smaller U, exclusion and meeting.
weighted_candidate_escape uses pure_residue_lift with v=1mod2,
then w=9^(L-R) for a pure exponent L>R+B+1.

PURE SOURCES CANNOT USE THIS U, KERNEL:
If w=1,r>=5,u>0, the first equation implies
9^R+7>=2^112. Since 9^35+7<2^112, R>=36.
Thus every pure source in this coordinate family is outside the size
region and U>N. Do not try to obtain pure-source exclusions from this
immediate candidate alone. Other coalescing sources remain possible.

EXACT ALGEBRA BEHIND THE BOUNDARY:
D=2^(57+11r), E=2^(9+11j), T=2^(3k+4),
L=denominator(r,j,k)=DET=2^(70+11(r+j)+3k),
M=multiplier(r,j,k)=3^(43+7(r+j)+2k),
P=padding(r,j,k)=7M+9^(k+1)*D*(3^(6+7j)-E).
The scaled_coordinates root proves L*d=M*X+P.
For r>=5, D<=3*3^(35+7r) and P<=10M.
Normalize M*9^R=A(s,t)=3^(43+7s+2t) and
L*(4*8^R)=B(s,t)=2^(72+11s+3t).
The axiom-free finite root checks 1000A<=993B inside the region,
B<=A outside on Fin16 x Fin20, and outside boundary points(16,14),(5,20).
Multiplication by 2^11<=3^7 and 2^3<=3^2 transports the outside
bound to arbitrary s,t. Inside, X>=10000 gives1000P<=M*X,
so1000d<=3976*8^R*w. With8^R*w>=512 this absorbs the source offsets.
Outside, L*d>=M*X>=L*(4*8^R*w), giving d>=4*8^R*w and N<U.

INVERSE CERTIFICATE, KERNEL:
Backtrack e o B p uses e EVEN-INPUT SHORTCUT edges and o odd-input
shortcut edges. Its ordinary clock is e+2o. The compulsory halving
inside each odd shortcut is not counted in e.
For B=3^K*v-2, the reference states (e,o,m) start at(0,0,2), with
  even inverse: (e+1,o,2m),
  odd inverse: (e,o+1,(2m+1)/3), if3 divides2m+1.
The 683-entry inverseStates list is kernel checked to be closed for
e<=14, with o<14,m>=2 and
  m+3^14 <= 2+2^(e+o)*3^(14-o).
No odd-count or total-depth bound is assumed on actual inverse paths.
The generic certificate_lift theorem proves, for every K>=14,
  p+m=2^(e+o)*3^(K-o)*v
for all actual paths with e<=14. certificate_lower multiplies the
reference inequality by3^(K-14)*v>=1 to prove B<=p.
The empty path attains B, so this is an exact minimum at that budget.

For U=d-2 set K=2(k+1). If k>=6, every inverse predecessor of U
with e<=14 is >=U. Since R+k>=20, U>N, and all these predecessors
are strictly larger than N. This does NOT cover other branches into
3d-5, all later targets, all coalescing sources or larger inverse budgets.
The earlier successful final exit can still merge N with smaller S
while this inverse obstruction holds at U. No nonconvergence claim.

VERIFICATION 2026-10-22T04:09:43.102255+00:00:
Fresh Lean 4.33.1 build, 28.725 seconds, 16 threads; 44 authenticated
objects reused. Compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 99 prior hashes and 102 current hashes authenticated. All 45 cached
.olean objects, including the new development object, match the manifest.
Verifier session 65653 exited 0; final development session 76525 exited 0.
All jobs are terminal. Reuse authenticates compiler/source/log/object,
copies imports into an isolated directory and retains nested provenance.
The new module is always fresh. Without --cache all 45 builds run sequentially.

INDEPENDENT FINITE SCOPE:
3,060 coefficient comparisons on s5..64,t14..64; exactly39 inside.
1,224 generic odd-unit immediate predecessors;72 even-unit checks
confirm those units are outside the one-step merger hypothesis.
The 683 reference states are reconstructed and compared with the Lean
list, closure, bounds and affine inequalities.
43 complete actual inverse trees,29,369 states,627,800 forward ordinary
steps. Each complete tree matches the affine reference set, has exact
minimum equal to its target and has maximum13 odd edges. The enumeration
has no imposed odd-count or total-depth cap. Generic K=14,16,32,128,4096
use v=1,2,3,17,2^128+1. Eighteen additional trees use actual weighted
coordinates R14,36,128, r5, j0 or1, k6,14,64. Maximum target6621 bits,
maximum unit538 bits, in possibly different cases.

927 complete N/U weighted pairs:784 smaller candidates (all 392 inside
quadruples with offsets0 and1),143 larger candidates. Complete N ordinary
steps626,635 and U steps1,854, total628,489. There are3,708 checkpoints
(three for each N, one for each U). Shortcut and inverse edge totals are
384,403 each, including generic checks. These full shortcuts add one
shared halving to the kernel merger: Nclock5R+117+18r+18j+5k, Uclock2,
common value(3d-5)/2. The kernel meeting itself uses Nclock one less and
Uclock1. Among all 927 cases:460 have d=3mod4;223 have later residue1;
244 have later residue3. No earliest-meeting claim.
Complete maxima occur separately: R16384,r4096,j4096,k4096;
weight45,200 bits,N49,308,U52,090,v52,068;
Nclock including shared halving82,175.
150 pure modular-only lifts, allr>=5,R>=36; maximum exponent6281 bits.
No pure starting value, trajectory or actual U is materialized.
Four larger cases R65536,1048576,r5,(j,k)=(1,6) or(16,128):
maximum N3,146,416 bits,U3,324,615 bits. Only N's three tails and U's
one-step merger replay:724 primary,676 secondary,1376 third and4 U
steps. Full initial growing prefixes and these huge inverse trees
are NOT replayed/enumerated.

ADDITIONAL SCRATCH EVIDENCE, NOT IN THE MANIFEST:
A Python reconstruction of the negative-two reference tree through
30 even edges has 433,148 states,max 34 odd edges. Its minimum affine
slope2^(e+o)/3^o is 1, attained at(0,0,2). This is finite Python evidence,
not a kernel extension of the14-edge certificate or an all-budget theorem.
Do NOT assume o<=e: the state(e,o,m)=(23,24,1029) refutes that proposed
invariant. An earlier partial traversal found(27,28,3345) as another.
A separate finite replay of every start1..59,047 to1 (maximum 339 steps)
found that targets3^K-2 for K=2,4,6,8,10 were first reached from those
targets themselves, not a smaller start. This too is scratch-only;
there is no universal backward-minimality theorem for that family.

NEXT LEADS, NOT FORMALIZED:
Investigate other inverse branches into3d-5 or the residual pair9h+2,h,
rather than treating the immediate U as a universal escape. The proved
pure comparison prevents that. The inverse certificate only concerns U
and a fixed budget; its30-edge scratch extension also found no contracting
reference slope, so simply increasing the fixed budget has limited evidence.

The actual coordinates impose more ternary information than the generic
K=2k+2 inverse certificate uses. Write f=9^(k+1),T=2^(3k+4),c=3^(6+7j).
Since b=cq=1+Tv and U=fv-2,
  T*(U+2)+f = f*c*q = 3^(2k+8+7j)*q.
Also q is not divisible by3, from9a+1=2^(9+11j)q. Thus the last
ternary valuation is exact. This written identity may support a scaled
reference certificate that uses j as well as k. It is not a new theorem
in the current module. For a general scaled reference M*B+c0=3^K*v,
the inverse offset rules would be c0->2c0 and c0->(2c0+M)/3 when
integral. Any such application needs its own proof and size comparison.

Another written candidate is W=3*8^(k+1)*v-5, which reaches3d-5 by
the existing weighted-ladder theorem. In terms of b it is (3b-13)/2,
independent of how its negative-five block is split. This observation
has not been turned into a smaller-original-source result; do not assume
its size helps. The known S has secondary endpoint3b-17, whose first
halving is W-2, linking this lead back to the current residual pair.

Full family convergence, unrestricted least-source exclusion, cap/residual
estimates, nontrivial cycles, divergence and full Collatz remain open.
The full goal is active. ATTEMPT, README and reproduction commands include
the new note. No installations, credentials, agents, staging, commits or
Git writes occurred. HEAD 8dcff74; index SHA256
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing user changes are preserved.

The preceding variable odd-block exit handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the variable odd-block exit.

Research remains active with no external blocker. Previous goal turn:
progress (19 negative-five transition roots). Current turn: progress
(20 kernel roots extending the final merger through arbitrary odd-block
lengths, realizing both exits, bounding the complementary companion,
and identifying the residual pair). The positive-integer Collatz
conjecture remains unresolved. Continue with 16 Lean threads per
process, sequential heavy checks and authenticated dependency reuse.
The user has explicitly authorized increased Lean threading. Current
runners pass both -j 16 and LEAN_NUM_THREADS=16. No new permission
or external-state change is needed to continue the mathematics.

LATEST ARTIFACTS:
lean/MinimumFiveOddExit.lean, docs/MINIMUM-FIVE-ODD-EXIT.md,
verify_minimum_five_odd_exit.py, results/minimum-five-odd-exit/.
Twenty roots passed fresh kernel audits. All use only standard logical
axioms; none is axiom-free. exit_growth_bound uses propext only;
adjacent_bridges, binary_target, companion_above_source, exit_units_odd
and realization_windows use propext and Quot.sound. No native
reduction, new mathematical axiom, unproved merger or external premise.

VARIABLE FINAL ODD BLOCK, KERNEL:
Keep R>=14,r>=5,w,u,q,v>0 and prior coordinates:
  X=9^R*w, X+7=2^(57+11r)*u, a=3^(33+7r)*u,
  9a+1=2^(9+11j)*q, b=3^(6+7j)*q,
  b=1+2^(3k+4)*v, d=thirdScalar(k,v)=9^(k+1)*v.
N=4*8^R*w-5 and S=2^(2R+13)*w-1 have third endpoints
  C^(5R+116+18r+18j+5k)N=3d-5,
  C^(4R+125+18r+18j+5k)S=2d-5.

For l>=1,z>0,d=1+2^(l+1)*z and 3^(l+1)*z=1mod4:
  C^(2l+5)(2d-5)=C^(2l+3)(3d-5).
Let A=2^l*(3z)-1. C(3d-5)=A and C^3(2d-5)=A-1.
MinimumLadderCover.adjacent_odd_block l (3z) supplies the merger.
Full clocks:
  C^(4R+130+18r+18j+5k+2l)S
    =C^(5R+119+18r+18j+5k+2l)N.
Since 0<S<N, N is not a least counterexample. No earliest meeting
or whole-family convergence is claimed. l=1 recovers d=5 mod16,
with one extra shared halving versus the previous kernel equation.
Final shortcut words N:E O^l EE; S:OEE O^(l-1) EO.
Common value (3^(l+1)*z-1)/4. No extra halving in this verifier.

OPPOSITE EXIT, KERNEL:
If instead 3^(l+1)*z=3mod4, T=3d-4=2A+1 merges with the
N endpoint at equal local clocks2l+4:
  C^(2l+4)T=C^(2l+4)(3d-5)
    =C^(5R+120+18r+18j+5k+2l)N.
But T>N throughout the coordinate family with R>=14,r>=5.
The growth lemma proves, for s,t>=0,
  5*2^(167+11s+3t)<=3^(107+7s+2t).
Use 5*2^167<=3^107,2048<=2187,8<=9, then set
s=r-5+j,t=R-14+k. Coordinate cancellation gives
5*8^R*w<=3d and thus N<3d-4. This rules out using THIS
companion as a smaller source, not all other possible predecessors.

More precisely, if 3^l*z=4h+1, then
  C^(2l+4)(3d-5)=9h+2,
  C^(2l+4)(2d-5)=h.
This is a residual pair, not a merger. S's full clock here is
4R+129+18r+18j+5k+2l. Words:
  N:E O^l EO, S:OEE O^(l-1) EE, T:O^(l+1) EE.
Exact odd factorization gives the two exit alternatives for every
d>1,d=1 mod4. A hypothetical least N there must take residue 3.
The d=3 mod4 branch is outside this dichotomy.

Written consequences of the residual formula (not extra audited roots):
h>0,h=2mod3, so9h+2=20 mod27, returning to the earlier critical
first-target class. Also4*(9h+2)+1=3^(l+2)*z. In actual third
coordinates,9 dividesd and d=1+2^(l+1)*z, so3 does not dividez;
the last ternary valuation is exactlyl+2. The note records the
20 mod27 consequence as written arithmetic, not a new kernel theorem.

BOTH RESIDUES HAVE UNBOUNDED REALIZATIONS, KERNEL:
For every r,j,k,l,B and g=1 or3, there exist R>B,R>=14 and
positive u,q,v,z with all four coordinate equations, zodd and
3^(l+1)*z=gmod4. At each fixed initialR, weights w>B also exist.
The lifts allow any r; fourth-source exclusion needsr>=5,R>=14.
The equations forceu,q,vodd. Thus all four exact binary valuations
are57+11r,9+11j,3k+4,l+1 forX+7,9a+1,b-1,d-1.

The reusable pure_residue_lift realizes any 0<eps<2^(h+1) as
v modulo2^(h+1), including even eps. Set
D=2^(57+11r),E=2^(9+11j),T0=2^(3k+4),V=2^(h+1),
A0=3^(35+7r),c=3^(6+7j),F=7cA0+D(c-E)+(V-eps)DET0.
An affine lift at index(57+11r)+(9+11j)+3k+h+2 gives
cA0*9^R+F=VDET0*Q. Putv=V(Q-1)+eps and cancel padding,
then cancel odd coefficients moduloD andE as in the prior proof.
For the final exit chooseV=2^(l+3),z0odd<4 with3^(l+1)z0=gmod4,
and odd eps<V with 9^(k+1)eps=1+2^(l+1)z0modV.
binary_target obtains such residues from odd_binary_inverse.
Thenz=4*(d/V)+z0. Fixed-R weights use w=9^(L-R),L>R+B+1.

BOTH EARLIER WINDOWS:
ExitRealization bundles the coordinates, positives,zodd and final g.
realization_windows preserves FourSeparated and SecondarySeparated
for either g when H+13<=9+11j and H+6<=3k+4.
OddEscape bundles successful g1, least exclusion, both windows and
explicit full merger. pure_odd_escape and weighted_odd_escape allow
arbitrary l>=1. Choosingj=k=H+1 works for every H and l. These windows
are cross-time inequalities inside named clock intervals, not all-time
separation or claims about clocks before those intervals.

VERIFICATION 2026-10-22T03:41:01.051928+00:00:
One fresh Lean 4.33.1 build, 2.978 seconds, 16 threads; 43 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 96 prior hashes and all 99 current hashes authenticated.
All 44 cached .olean objects, including the new development object,
match the manifest. Verifier session 5288 exited 0; final development
session 42252 exited 0. All milestone jobs are terminal. Reuse checks
compiler/source/log/object, copies objects into isolated imports,
retains nested provenance and always rebuilds the new module.
Without --cache all 44 modules build sequentially.

INDEPENDENT FINITE SCOPE:
896 complete four-source cases, 448 per final residue. N,S paths are
complete to the stated common value or residual pair. P,Q prefixes
are complete; opposite larger companions also replay to N's endpoint.
Complete ordinary steps 2,838,448, comprising N 885,160, S 845,496,
P/Q 1,092,000 and companions 15,792. There are 5,376 ordinary
checkpoints at three boundaries for each N,S case. Total shortcut
and inverse edges 2,096,368 each, including generic/tail checks.
Primary and secondary windows each hold in 608 complete cases;
both in 416 complete cases, including both final residues.

Generic 335 bridge pairs, 1,340 ordinary steps; 2,054 successful and
2,054 opposite local pairs. Local N 322,602 steps,S 326,710,
companions 162,328. There are 10,270 comparisons of complete ordinary
and paired paths, plus 341 binary target residue cases.
Primary phase checks 612 pairs, 230,628 states, 229,404 steps, 602 actual sets.
Old three-source checks 612 triples, 345,942 states, 344,106 steps.
Secondary phase checks 612 pairs, 64,200 states, 62,976 steps, 602 actual sets.
The primary main window repeats in old and new checks; summing counts
does not count distinct visits. Exact phase signatures cover all
cross-time comparisons without enumerating every clock pair.

Complete maxima occur separately:R16384,r4096,j4096,k4096,l4096;
primaryH45,052,secondaryH12,286;N49,312bits,S45,244,
weight45,203,a52,090,b52,094,d52,093,z52,076;
Nclock82,185,Sclock74,041. Pure modular-only checks 880, covering
both g residues andr0,5,6, plus larger tuples including
(r,j,k,l)=(5,512,4096,1024) and(5,1,1,8192).
Largest pure exponent 24,739 bits; modulus 19,073 bits. These pure
starting values and complete trajectories are NOT materialized.
Four larger casesR65536,1048576 use(j,k,l,g)=(1,16,128,1)
or(16,128,512,3). Largest N 3,146,930 bits. Tail-only counts:
primary 2,732 steps, secondary 1,372, third 2,932, exit 5,152,
companion 2,056. Full initial growing prefixes are NOT replayed.

NEXT LEAD, WRITTEN AND SCRATCH ONLY:
In the opposite branch there is another, smaller local predecessor
U=d-2=2^(l+1)*z-1. The earlier half_source_meeting lemma at
(k,q,t)=(l+1,z,3h), where3^(l+1)z=12h+3, gives
  C^(2l+5)(d-2)=9h+2=C^(2l+4)(3d-5).
Its shortcut word is O^(l+1) EO. This specific corollary is NOT in
MinimumFiveOddExit or its manifest. An independent scratch replay
checked 1,024 qualifying pairs,l1..32,oddz1..127, with ordinary,
shortcut and inverse operations. Actual weighted sample coordinates
r5,j0,k0,l1,g3 gaveU<N forR14..19 andU>N forR20..24.
These size comparisons are FINITE samples, not universal bounds.
Investigate whether this U or another inverse construction supplies
smaller original sources more broadly. Do not confuse T>N with an
exclusion of U or all other predecessors.

The residual pair9h+2,h and its return to20 mod27 also suggest
reusing the earlier mixed-ancestry/first-target analysis. The known
small S reaches h; no general argument transfers its convergence to
9h+2. Both final residues have unbounded realizations, so residue
incompatibility alone cannot eliminate the opposite branch.

Full family convergence, arbitrary least-counterexample exclusion,
cap/residual estimates, nontrivial cycles, divergence and full Collatz
remain open. The full goal is active.
ATTEMPT, README and reproduction commands include the new note.
Whitespace, note links, hashes and cached objects passed checks.
No installations, credentials, agents, staging, commits or Git writes
occurred. HEAD 8dcff74; index SHA256
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing user changes are preserved.

The preceding negative-five transition handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the negative-five transition.

Research remains active with no external blocker. Previous goal turn:
progress (22 exact phase-obstruction roots). Current turn: progress
(19 kernel roots giving later mergers through an arbitrary negative-five
block, unbounded pure/weighted realizations and simultaneous separated
windows). The positive-integer Collatz conjecture remains unresolved.
Continue with 16 Lean threads per process, sequential heavy checks
and authenticated dependency reuse. No new permission or external-state
change is required to continue the mathematics.

LATEST ARTIFACTS:
docs/MINIMUM-FIVE-TRANSITION.md, lean/MinimumFiveTransition.lean,
verify_minimum_five_transition.py, results/minimum-five-transition/.
All 19 roots passed fresh kernel dependency audits. All use only standard
logical axioms; none is axiom-free. finite_five_units uses propext and
Quot.sound; secondary_scale_bound uses propext. No native reduction,
new mathematical axiom, unproved merger or external premise.

NEW THIRD BLOCK, KERNEL:
Keep the previous coordinates R>=14,r>=5,w,u,q>0:
  X=9^R*w, X+7=2^(57+11r)*u, a=3^(33+7r)*u,
  9a+1=2^(9+11j)*q, b=3^(6+7j)*q.
The main N=4*8^R*w-5 and fourth S=2^(2R+13)*w-1 have
secondary endpoints 4b-17 and 3b-17 at base clocks
  N:5R+107+18r+18j, S:4R+121+18r+18j.
Now assume k>=0,v>0 and
  b=1+2^(3k+4)*v, d=thirdScalar(k,v)=9^(k+1)*v.
Then
  C^(9+5k)(4b-17)=3d-5,
  C^(4+5k)(3b-17)=2d-5.
Both identities hold at every k with no fixed clock bound.

Two new bridges are C^9(64x-13)=27x-5 and
C^4(48x-14)=18x-5 for x>0, with shortcut words OOEEOE and EOE.
Substitute x=8^k*v, then use the existing weighted-ladder identity
C^(5k)(8^k*z-5)=9^k*z-5 for z>0. The negative-five cycle has
shortcut word OOE and five ordinary steps. All actual paths are
positive. The negative reference is only a parity pattern.
Use the cycle at offset -5: a proposed full cycle at offset -14
can need an extra parity bit and must not be applied blindly.

FINAL EXIT AND LEAST EXCLUSION, KERNEL:
If d=5mod16, write d=16t+5. Then
  C^4(48t+10)=18t+4=C^6(32t+5).
Consequently
  C^(13+5k)(4b-17)=C^(10+5k)(3b-17),
and the full source clocks are
  C^(5R+120+18r+18j+5k)(N)
    =C^(4R+131+18r+18j+5k)(S).
Since 0<S<N, N cannot be a least counterexample. No full convergence
of the S family is needed, and no earliest meeting is claimed.
The finite full-shortcut replay adds one shared halving, ending
at 9t+2 and using full clocks one greater than the kernel equation.

All three units u,q,v are odd under these conditions. Thus the
exact binary valuations are 57+11r,9+11j,3k+4 respectively for
X+7,9a+1,b-1. This new family has b=1mod16, disjoint from the
previous successful b=23mod64 family. The final d=5mod16 guard
is still restricted and does NOT cover every secondary unit.

UNBOUNDED PURE AND WEIGHTED REALIZATIONS, KERNEL:
For EVERY r,j,k and exponent bound B, there exist R>B,R>=14
and positive u,q,v satisfying all three coordinate equations
and the final guard with w=1. The lift itself allows any r;
the actual fourth-source merger and exclusion require r>=5.
At any fixed initial R, weights w>B also satisfy the same equations.
R>=14 supplies the source bound needed for exclusion.

Set m=57+11r,K=9+11j,D=2^m,E=2^K,T=2^(3k+4),
A=3^(35+7r),c=3^(6+7j),f=9^(k+1).
The kernel scale bound E<=c uses 512<=729 and 2048<=2187.
A finite kernel lemma gives odd 0<eps<16 with f*eps=5mod16.
Set F=7cA+D(c-E)+(16-eps)*D*E*T. Since cA is odd and
cA+F is divisible by eight, the unbounded affine exponent lift
at index m+K+3k+5 gives
  cA*9^R+F=16*D*E*T*Q, Q>0.
For v=16(Q-1)+eps, cancel padding:
  cA*(9^R+7)+D(c-E)=D*E*T*v.
Cancel odd cA modulo D to obtain u>0. Add D*E and cancel D:
  c*(A*u+1)=E*(1+T*v).
Cancel odd c modulo E, obtaining q>0 with A*u+1=E*q; cancel E
to obtain c*q=1+T*v. Since A*u=9a, these are the requested
second and third equations. The residue of v gives the final guard.
Fixed-prefix weights come from a larger pure exponent L with
w=9^(L-R), L>R+B+1.

BOTH SEPARATED WINDOWS WITH LATER SUCCESS, KERNEL:
If H+6<=3k+4, the previous phase theorem still separates the
secondary N,S windows through H. In particular k>0 gives H=3k-2.
For j>0 the four primary windows remain separated through 11j-4.
These are all cross-time inequalities inside the named windows,
not separation before the base clocks or for all later time.
The specified later local N-clock 13+5k exceeds 3k-2.

ThirdEscape bundles the three coordinate equations, positive odd
units, least exclusion, secondary window separation and the explicit
later meeting. For every r>=5,j,k,H,B with H+6<=3k+4,
pure exponents and fixed-prefix weights realize ThirdEscape
beyond any bound. Taking j=k=H+1 additionally gives FourSeparated
through H. The pure_both_windows and weighted_both_windows roots
prove these simultaneous claims. This is a positive escape inside
both obstructions, not a contradiction of either obstruction.

VERIFICATION 2026-10-22T03:17:59.873490+00:00:
One fresh Lean 4.33.1 build, 3.532 seconds, 16 threads; 42 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 93 prior hashes and
all 96 current hashes authenticated. All 43 cached .olean objects,
including the new development object, match the current manifest.
Final verifier session 6529 exited 0. All milestone jobs are terminal.
Reuse authenticates compiler/source/log/object, copies into an isolated
import directory and retains nested provenance. The new module is
always fresh; without --cache all 43 modules build sequentially.
Historical manifests, source files and notes were not rewritten.

INDEPENDENT FINITE SCOPE:
930 complete four-source cases. N,S replay completely to their
common value, P,Q completely to their primary endpoints, with ordinary,
shortcut and inverse operations. Total complete ordinary steps:
3,517,062 (N 1,086,604; S 1,012,038; P,Q 1,418,420).
There are 5,580 ordinary checkpoints across the three N,S block
boundaries. Total shortcut and inverse edges, including generic
checks, are 2,137,158 each. Primary separation is checked in 750
complete cases; secondary separation in 830; both in 670.

Generic checks: 260 short bridge paths (1,690 steps), 1,024 local
meetings (12,288 steps), 335 third-profile pairs (165,955 steps),
268 conditional third meetings (135,980 steps), 8 finite odd units.
Primary phase checks total 754 pairs, 247,706 states, 246,198 steps,
with 737 actual-value set comparisons. Old three-source checks total
754 triples, 371,559 states, 369,297 steps. Secondary phase checks
total 1,098 pairs, 156,756 states, 154,560 steps, with 998 actual-set
comparisons. Main primary windows are replayed in both old and new
checks, so adding these counts does not count distinct visits.
Disjoint exact signatures prove all cross-time inequalities without
quadratic enumeration of clock pairs.

Complete maxima R=16384,r=4096,j=4096,k=4096 occur in different
examples. Maximum primary horizon 45,052; secondary 12,286.
Maximum N has 49,507 bits; S 45,273; weight 45,232; a 52,285;
b 52,290; d 52,292. Maximum full N,S clocks (including the extra
shared halving) are 82,499 and 74,086.
Pure lifts have 366 modular-only checks, including
(r,j,k)=(128,128,128),(512,1,1),(5,512,4096).
Largest exponent has 22,692 bits. These enormous pure starting
values and complete trajectories are NOT materialized.

Four larger cases use R=65536 or1048576,r=5,
(j,k)=(1,16) or(16,128). Maximum N has 3,146,419 bits.
Only four primary tails, two secondary tails, the later third merger
and their windows are replayed: 2,732 primary-transition steps,
1,372 secondary steps and 2,980 third-merger steps. Full initial
growing prefixes are NOT iterated.

NEXT LEAD, EXPLORATORY AND NOT YET FORMALIZED:
The final pair 3d-5,2d-5 has a broader variable odd-block merger.
If l>=1,z>0 is odd, d=1+2^(l+1)*z and
3^(l+1)*z=1mod4, the derived clocks are
  C^(2l+3)(3d-5)=C^(2l+5)(2d-5).
Derivation: let a=3*2^l*z-1. The first source reaches a after
one halving; the second reaches a-1 in three ordinary steps.
Apply existing MinimumLadderCover.adjacent_odd_block with
block length l and quotient 3z. This is currently a written/scratch
deduction, NOT in the new Lean module or its manifest. A scratch
integer replay checked 1,024 qualifying pairs with l=1..32,
odd z=1..127. No claim of universal final exit coverage.
The present d=5mod16 case corresponds to l=1 with z=1mod4.

This may replace the fixed final guard with another unbounded block.
The opposite odd-block exit needs another route: the existing odd
two-partner cover uses 2a+1=3d-4 in that branch. No smaller original
source reaching that companion has been constructed. The neighboring
Mersenne shift c=14 is not an obvious new partner: the scratch
negative-reference counts for c=13 and 14 both have combined ternary
exponent 69 and 108 shortcut edges, suggesting the same primary scalar
endpoint with a one-step clock shift. That has not been formalized
here. Do not promote these leads to proved exclusions.

Full family convergence, arbitrary least-counterexample exclusion,
cap/residual estimates, nontrivial cycles, divergence and full Collatz
remain open. The full goal is active.

ATTEMPT, README and reproduction commands include the new note.
Whitespace, note links, hashes and cached objects passed checks.
No installation, credential access, agents, staging, commits or Git
writes occurred. HEAD remains 8dcff74; index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing user changes are preserved.

The preceding exact halving-phase handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the exact halving-phase obstruction.

Research remains active with no external blocker. Previous goal turn:
progress (18 fourth-source merger roots). Current turn: progress
(22 kernel roots for exact binary phases, all-four primary separation,
normalized secondary separation, unbounded realizations and a convergent
witness). The positive-integer Collatz conjecture remains unresolved.
Continue with 16 Lean threads per process, sequential heavy checks
and authenticated dependency reuse. No user permission or external-state
change is needed to continue the mathematics.

LATEST ARTIFACTS:
docs/MINIMUM-SEVENTEEN-PHASE.md, lean/MinimumSeventeenPhase.lean,
verify_minimum_seventeen_phase.py, results/minimum-seventeen-phase/.
All 22 roots passed fresh kernel dependency audits. All use only standard
logical axioms; none is axiom-free. finite_phase_sets uses propext and
Quot.sound; finite_secondary_convergent_witness uses propext. No native
reduction, new mathematical axiom, unproved merger or external premise.

GENERIC PHASE MECHANISM, KERNEL:
For odd scale M and c>=M define D_M(c)=3c-M when c odd, c/2 otherwise.
If M*n+c=2^e*u with e>0,u odd, then n,c have the same parity.
An odd ordinary step multiplies this scaled sum by three and preserves
e; an even step halves it and reduces e by one. Binary exponents in
such factorizations are unique. The phase_track induction preserves
e+h=E+h_initial, where h counts halvings, and membership in a finite
table of (c,h mod L). If all c<2^B and at least B binary digits remain,
equal actual iterates force equal c and equal e. Incompatible halving
phases then separate all pairs of clocks, even with overlapping shadows.
The generic roots are binary_exponent_unique, exact_phase_step,
phase_track, phase_separation, exact_binary_from_divisibility.
The extra odd_binary_inverse root constructs inverses of every odd c
modulo every 2^(k+1), with a positive odd representative.

ALL FOUR PRIMARY WINDOWS, KERNEL:
For a>0 and 2^(H+13) dividing 9a+1, every s,t<=H satisfies
  C^s(81a-17) != C^t(72a-17),
  C^s(64a-17) != C^t(72a-17),
  C^s(48a-17) != C^t(72a-17).
The first two use the earlier disjoint shadow sets. The fourth partner
requires exact phases: 9(72a-17)+225=72(9a+1), and
9(48a-17)+201=48(9a+1). If v2(9a+1)=K, these sums begin with
exponents K+3 and K+4. Use M=9,L=11,B=13. The main phase table
has 18 states; the fourth has 31, entering the same cycle after 13.
At their first common constant 1098 the main has 4 halvings, the fourth 7.
The halving difference remains 3 modulo 11 on all shared cycle constants,
but equal positive iterates would require 1 modulo 11. The tables contain
the same 18 cycle constants, so residue-set disjointness alone fails.
All constants lie in [9,4392], below 8192. The cycle has 18 ordinary
steps, 11 halvings, 7 odd operations.

The preceding source coordinates remain
  N=4*8^R*w-5, P=2^(2R+5)*w-1, Q=2^(2R+15)*w-1,
  S=2^(2R+13)*w-1,
  9^R*w+7=2^(57+11r)*u, a=3^(33+7r)*u.
For R>=14,r>=5,w,u>0, all three partners are positive and<N.
Their primary base clocks are N:5R+91+18r, P,Q:4R+99+18r,
S:4R+100+18r. FourSeparated names the three partner-versus-main
inequalities after these bases. It does NOT assert disjointness among
partners, separation before the bases, or separation beyond H.

For every r>=5,H,B, pure exponents R>B,R>=14 realize FourSeparated.
For every fixed R>=14,r>=5 and any H,B, weights w>B realize it.
Apply the previous pure/weighted shadow lift at horizon H+1.
No uniform four-partner scalar exit bound exists even at any fixed r.

NORMALIZED SECONDARY EXIT, KERNEL:
For b>=6 and 2^(H+6) dividing b-1,
  C^s(3b-17) != C^t(4b-17), for every s,t<=H.
Use M=1,L=3,B=6, since
  (4b-17)+13=4(b-1), (3b-17)+14=3(b-1).
The reference tables are
  13,38,19,56,28,14,7,20,10,5;
  14,7,20,10,5.
They have 10 and 5 states, with cycle starts 5 and 0. The shared negative-five
cycle has 3 halvings in 5 ordinary steps. The initial path from 13 to 14
also has 3 halvings. Equal constants therefore have equal halving phases
mod3, but the initial binary exponents differ by 2. All c<64.

If 9a+1=2^(9+11j)*q and b=3^(6+7j)*q, the earlier profiles
reach 4b-17 and 3b-17 at full base clocks
  N:5R+107+18r+18j,
  S:4R+121+18r+18j.
The new secondary_source_separation applies to these two windows.

For EVERY fixed r>=5,j and arbitrary H,B, pure exponents R>B
realize this secondary separation with q POSITIVE ODD. At every fixed
R>=14, weights w>B also realize it. Thus v2(9a+1)=9+11j exactly:
the secondary delay is not an unremoved binary factor in q. A fixed
secondary exit bound fails even for odd q at every fixed j. No failure
of eventual coalescence, divergence or universal negative behavior follows.

SECONDARY UNIT LIFT, KERNEL:
Let m=57+11r,K=9+11j,D=2^m,E=2^K,V=2^(H+6),
A=3^(35+7r),c=3^(6+7j). The binary inverse lemma supplies odd
0<eps<V with c*eps=1+V*z. Set F=7A+D+(V-eps)*D*E.
The existing unbounded affine lift at index m+K+H+3 gives
  A*9^R+F=V*D*E*Q, Q>0.
With q=V*(Q-1)+eps, cancel padding to get
  A*(9^R+7)+D=D*E*q.
Cancel odd A modulo D and then D to obtain u>0 and
9a+1=E*q. Also c*q=1+V*(c*(Q-1)+z), so V divides b-1,
and q is odd. The lift works for every r,j,H,B; r>=5 is needed
when applying the fourth-source profile. Weights use w=9^(T-R)
at a pure exponent T>R+B+1.

DELAYED SUCCESS ALSO PERSISTS, KERNEL:
The previous successful b=23mod64 exit is separate from b=1mod2^(H+6).
Using pure_nested_lift/weighted_nested_lift with j=H+1 gives BOTH
FourSeparated through H and a later fourth-source merger, hence N
not least. Full kernel clocks remain
  N:5R+117+18r+18j, S:4R+128+18r+18j.
Pure exponents and fixed-prefix weights are unbounded in these
simultaneous statements. No earliest-meeting claim.

CONVERGENT SECONDARY WITNESS, KERNEL AND PYTHON:
R=14,r=5,j=1,H=128, named phaseWitnessWeight, phaseWitnessUnit,
phaseWitnessExit. Source sizes (N,P,Q,S)=(308,297,307,305) bits;
ordinary arrivals at 1 = (2683,3675,2682,2680). Lean certifies positivity,
both coordinate identities, q odd, 2^134 dividing b-1, and arrivals.
Python additionally checks first-arrival minimality over 11,720 steps.
All three primary partner windows are separated through 7; the N,S
secondary windows are separated through 128. This directly prevents
interpreting the new finite-window obstruction as nonconvergence.

VERIFICATION 2026-10-22T02:52:11.959404+00:00:
One fresh Lean 4.33.1 build, 3.375 seconds, 16 threads; 41 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 90 prior hashes and
all 93 current hashes authenticated. All 42 cached .olean objects,
including the new development object, match the current manifest.
Final verifier session 76674 exited 0. All milestone jobs are terminal.
Reuse authenticates compiler/source/log/object, copies to an isolated
import directory and retains nested provenance; the new module is
always freshly built. Without --cache all 42 modules build sequentially.
Historical manifests, sources and notes were not rewritten.

INDEPENDENT FINITE SCOPE:
458 complete primary cases and 513 complete secondary cases replay
all four source prefixes by ordinary, shortcut and inverse operations.
The secondary cases continue N,S to their secondary endpoints and
check q odd; 413 also check primary separation. Four additional cases
replay the full later merger. Total full-source ordinary steps are
4,193,046, including 324,762 in these four delayed-merger cases.
Shortcut and inverse edges: 2,407,929 each. Ordinary checkpoints: 3,904.

Finite tables contain 64 phase states. There are 272 generic pairs of
primary/secondary scalar checks and 4,585 binary-inverse checks.
Primary phase pairs: 1,152, with 301,908 states and 299,604 steps;
1,119 also compare actual integer-value sets. Secondary phase pairs:
790, with 116,820 states and 115,240 steps; 779 compare actual sets.
The older three-source checks have 1,156 windows, 458,151 states,
454,683 steps and 1,120 actual-set comparisons. The main primary
window is replayed in both the old and new checks: adding those
counts does NOT count distinct visits. Exact disjoint phase signatures
or residue sets prove every cross-time inequality without quadratic
enumeration of clock pairs.

Primary/secondary complete maxima R=16384,r=4096,j=4096,H=16384
occur in different examples; largest primary horizon 45052. Maximum
N has 49,579 bits; S 45,422; weight 45,381; a 52,357. The maximum
secondary b in these cases has 52,106 bits (52,239 including delayed
merger examples). Largest full N clock including delayed cases 82,416;
largest full S clock 73,995. Pure secondary lifts have 206 modular-only
checks, including (r,j,H)=(128,128,128),(512,1,0),(5,512,4096).
Largest exponent 14,498 bits; enormous pure sources and trajectories
are NOT materialized.

Four larger cases use R=65536 or1048576,r=5,(j,H)=(1,32) or(16,128).
Maximum N has 3,146,161 bits. Only four transition tails, two secondary
tails and their windows are replayed: 2,732 transition steps and 1,372
secondary steps. Full growing prefixes are NOT iterated.

NEXT RESEARCH:
A successful cover must allow source-dependent later clocks or add
partners with compatible phases. Merely increasing a fixed window,
even after an odd quotient exit and at fixed R,r,j, cannot work.
The new generic phase proof is reusable when ordinary shadow sets
overlap. A ternary-phase version could test candidates whose binary
phases match; it is not formalized here. The secondary near-b=1
reference follows the negative-five cycle, suggesting different later
partners or block arguments rather than more negative-seventeen copies.
Neither obstruction rules out unrestricted later coalescence.
Full family convergence, arbitrary least-source exclusion, cap/residual
estimates, nontrivial cycles, divergence and full Collatz remain open.

ATTEMPT, README and reproduction commands include the new note.
Whitespace, note links, hashes and cache checks passed. No installation,
credential access, agents, staging, commits or Git writes occurred.
HEAD remains 8dcff74; index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing user changes are preserved. The full Collatz goal remains active.

The preceding fourth-source merger handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the fourth-source merger.

Research remains active with no external blocker. Previous goal turn:
progress (14 exit-window separation roots). Current turn: progress
(18 kernel roots adding a fourth smaller source and a merger through
an arbitrary second negative-seventeen block). The positive-integer
Collatz conjecture remains unresolved. Continue with 16 Lean threads
per process on this 16-CPU machine, sequential heavy checks and
authenticated dependency reuse. The user explicitly permits increased
Lean threading for speed. No permission or external-state change is
needed to continue the mathematics.

LATEST ARTIFACTS:
docs/MINIMUM-SEVENTEEN-FOURTH.md, lean/MinimumSeventeenFourth.lean,
verify_minimum_seventeen_fourth.py, results/minimum-seventeen-fourth/.
All 18 roots passed fresh kernel dependency audits. All use only
standard logical axioms; none is axiom-free. The finite_exit_units
root uses propext and Quot.sound. No native reduction, new mathematical
axiom, unproved merger or external mathematical premise is used.

FOURTH SOURCE, KERNEL:
Assume R>=14, r>=5, w,u>0 and
  X=9^R*w, X+7=2^(57+11r)*u, a=3^(33+7r)*u.
The new source S=2^(2R+13)*w-1 is positive and smaller than
N=4*8^R*w-5. Its profiles are
  C^(4R+100+18r)(S)=48a-17,
  C^(4R+102+18r)(S)=72a-25=(72a-17)-8.
This formalizes the previous handoff's speculative fourth source.
The older partners remain P=2^(2R+5)*w-1 and Q=2^(2R+15)*w-1,
with base clocks N:5R+91+18r, P,Q:4R+99+18r and endpoints
72a-17,81a-17,64a-17. Python checks 0<P<S<Q<N; the new kernel
bound asserts 0<S<N, which is the comparison needed for exclusion.

New bridge: C^164(2^108*q-11160262)=3^56*q-17 for q>0,
where 11160262=7*3^13+1. Its Backtrack counts are 52 extra even
and 56 odd operations: 108 shortcut edges, 164 ordinary steps.
S's all-odd prefix has clock 4R+26 and reaches 3^13*X-1.
After the bridge there are r-5 old eighteen-step cycle copies.
All asserted source trajectories are positive. Negative reference
orbits only determine auxiliary parity patterns.

SECOND VARIABLE BLOCK, KERNEL:
For j>=0, q>0 with 9a+1=2^(9+11j)*q, put b=3^(6+7j)*q.
Then
  C^(16+18j)(72a-17)=4b-17,
  C^(21+18j)(48a-17)=3b-17.
The first uses the new rotated bridge
  C^16(4096q-25)=2916q-17,
with shortcut word OOOEOOOEEE. The second takes two steps to
72a-25, the old nineteen-step bridge from 4096v-33, then j cycles.
The cycle word remains OOOOEOOOEEE. There is no bound on j.

LOCAL EXIT AND FULL MERGER, KERNEL:
If b=23 modulo 64, write b=64v+23. The paths satisfy
  C^10(256v+75)=54v+16=C^7(192v+52).
Thus
  C^(5R+117+18r+18j)(N)=C^(4R+128+18r+18j)(S).
Since 0<S<N, N cannot be a least positive counterexample. This
does NOT prove convergence of every member of either family or
claim an earliest meeting. Python adds one shared halving to finish
the shortcut words, giving clocks one greater and target 27v+8.

SIMULTANEOUS OLD SEPARATION, KERNEL:
For j>0, put H0=11j-3. Since H0+12=9+11j, the earlier theorem
still separates both P,Q exit windows from the N exit window for
ALL pairs of additional ordinary clocks s,t<=H0. The new specified
meeting uses additional N-clock 26+18j, beyond H0. No separation
before the transition clocks or beyond the stated windows is claimed.
The fourth source is outside the two-partner separation theorem.

UNBOUNDED PURE AND WEIGHTED REALIZATIONS, KERNEL:
For every r,j,B, there exist R>B,R>=14,u,q>0 satisfying both
coordinate equations and b=23mod64 with w=1. The lift itself does
not require r>=5; the new merger and least exclusion do require it.
For every fixed R,r,j and weight bound B, weights w>B also exist.

Lift construction: m=57+11r, K=9+11j, D=2^m, E=2^K,
A=3^(35+7r), c=3^(6+7j). Choose odd 0<eps<64 with c*eps=23mod64.
Set F=7A+D+(64-eps)*D*E. The existing unbounded affine lift at
precision index m+K+3 gives A*9^R+F=64*D*E*Q, with Q>0.
For q=64(Q-1)+eps, padding cancellation gives
  A*(9^R+7)+D=D*E*q.
Odd-factor cancellation gives D | 9^R+7; its positive quotient u
satisfies A*u+1=E*q, hence 9a+1=E*q and the required exit unit.
For a fixed initial exponent, choose a larger pure exponent T and
set w=9^(T-R); T>R+B+1 ensures w>B.

Taking j=H+1 proves: for EVERY r>=5 and horizon H, suitable pure
exponents exist beyond every bound, satisfying the new least exclusion
while both old windows stay separated through H. At every fixed
R>=14, weights beyond every bound satisfy the same conclusions.
This is a restricted secondary exit, NOT a cover of every a=7mod64.

VERIFICATION 2026-10-22T02:20:54.099914+00:00:
One fresh Lean 4.33.1 build, 6.930 seconds, 16 threads; 40 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 87 prior hashes and
all 90 current hashes authenticated. All 41 cached .olean objects,
including the new development object, match the current manifest.
Final verifier session 15483 exited 0. All milestone jobs are terminal.
Cache reuse authenticates compiler/source/log/object, copies objects
to an isolated import directory, and always freshly builds the new
module. Nested prior reuse provenance is retained. Without --cache,
all 41 modules build sequentially. Historical manifests were unchanged.

INDEPENDENT FINITE SCOPE:
678 complete four-source cases: N,S fully replayed to their shared
meeting, P,Q fully replayed to their transition endpoints. Ordinary,
shortcut and inverse checks agree. Total full-source ordinary steps
are 3,455,114: N 1,059,590; S 984,988; P,Q 1,410,536. There are
3,390 intermediate ordinary checkpoints. Total shortcut and inverse
edges are 2,023,034 each, including generic bridge checks.

Generic checks: 260 bridge paths (23,400 ordinary steps), 1,024 local
meetings (19,456 steps), 136 second-block pairs (99,496 steps), and
32 odd exit multipliers. Of the 678 complete cases, 606 have j>0
and replay the older separated windows. Including four larger tails,
610 separated triples contain 472,992 states and 471,162 steps.
All use exact congruences and disjoint residue sets; 588 windows also
compare actual integer-value sets. No quadratic pair enumeration.

Complete maxima R=16384, r=4096 and j=4096 occur in different cases;
largest old horizon 45053. Maximum N is 49,502 bits; S 45,345;
weight 45,304; a 52,280; b 52,285. Largest recorded full N,S clocks
are 82,488 and 74,201 (including the shared extra halving).
The 278 pure checks use modular powers only, including (r,j) pairs
(128,128),(512,1),(5,512). The largest exponent has 6,306 bits;
its enormous source and trajectory are NOT materialized.

Four larger coordinate cases use R=65536 or1048576, r=5, j=1 or16.
Maximum N has 3,146,033 bits. Only four transition tails, the later
merger and old windows are replayed there: 2,732 transition steps
and 1,448 merger steps, plus window steps counted above. Their full
initial growing prefixes are NOT iterated.

NEXT RESEARCH:
The remaining secondary exit units of 4b-17 and 3b-17 need new
mergers or additional partners. The successful b=23mod64 condition
cannot be substituted for all b. The new construction establishes
that the old fixed-window barrier can coexist with later useful
mergers; it does not remove that barrier for the original P,Q pair.
Arbitrary least-source exclusion, full family convergence, cap/residual
estimates, nontrivial cycles, divergence and full Collatz remain open.

ATTEMPT, README and reproduction commands include the new note.
Whitespace and note-link checks passed. No installation, credential
access, agents, staging, commits or Git writes occurred. HEAD remains
8dcff74; index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing user changes are preserved. The full Collatz goal remains active.

The preceding exit-window separation handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the transition exit-window separation.

Research remains active with no external blocker. Previous goal turn:
progress (19 negative-seventeen transition roots). Current turn: progress
(14 kernel roots proving that no fixed exit window covers those two
partners, with pure and fixed-prefix weighted realizations). The full
positive-integer Collatz conjecture remains unresolved. Continue with
16 Lean threads per process, sequential heavy builds and authenticated
dependency reuse. No user permission or external-state change is needed
to continue the mathematics.

LATEST ARTIFACTS:
docs/MINIMUM-SEVENTEEN-SEPARATION.md, lean/MinimumSeventeenSeparation.lean,
verify_minimum_seventeen_separation.py, results/minimum-seventeen-separation/.
All 14 roots passed fresh kernel dependency audits. All use only standard
logical axioms; none is axiom-free. finite_shadow_sets uses propext and
Quot.sound; finite_convergent_witness uses propext. No native reduction,
new mathematical axiom, unproved merger or external theorem is used.

NEW SCALAR SEPARATION, KERNEL:
For every H and a>0 with 2^(H+12) dividing 9a+1, and every s,t<=H,
  C^s(81a-17) != C^t(72a-17),
  C^s(64a-17) != C^t(72a-17).
This is across ALL PAIRS of clocks in the windows, not just equal clocks.
Such a is 7 modulo 64, disjoint from the earlier successful exits 13/61.
No failure of eventual coalescence is proved. No uniform finite scalar
meeting-clock bound exists even at any fixed r for a=3^(33+7r)*u.

PROOF MECHANISM, KERNEL:
Use natural constants c with D(c)=3c-9 for odd c, c/2 for even c.
If c>=9 and 2d divides 9n+c, then d divides 9C(n)+D(c).
The initial constants for (72a-17,81a-17,64a-17) are (225,234,217),
since adding them to nine times the sources gives respectively
72(9a+1),81(9a+1),64(9a+1). Three finite D-orbits have lengths
18,11,21 and cycle-start indices 0,6,19. Their values lie in [9,2448].
The first set is disjoint from each partner set. Induction retains
divisibility modulo 4096 throughout every t<=H; the disjoint residues
of nine times the positive iterates prove the claimed separation.

At the formal pole a=-1/9, the scalar values are -25,-26,-217/9.
Their auxiliary patterns lead to the negative 17,5,1 cycles. The third
reference is rational. The actual proof stays in Nat, using the scaled
constants; it does NOT apply the ordinary integer map to a noninteger.
No actual positive orbit is asserted to remain on a negative cycle.

PURE AND FIXED-PREFIX REALIZATIONS, KERNEL:
For every r,H,B there exist R>B,R>=14,u>0 with
  9^R+7=2^(57+11r)*u,
  2^(H+12) dividing 9*3^(33+7r)*u+1.
The previous three-source theorem therefore separates the original
source windows with ordinary clocks
  N: 5R+91+18r+t,
  P,Q: 4R+99+18r+s, for every s,t<=H.
This does NOT exclude meetings before these windows or after them.

For every FIXED R>=14 and r, every H and weight bound B, there also
exist w>B,u>0 satisfying the weighted transition and the same separation.
Both partners 2^(2R+5)*w-1 and 2^(2R+15)*w-1 remain positive and
strictly smaller than N=4*8^R*w-5. Thus increasing initial R or r is
not necessary to obtain arbitrarily long separated exit windows.

Lift proof: m=57+11r,D=2^m,A=3^(35+7r). The generic odd affine
exponent lift, now with an unbounded-exponent wrapper, makes
A*9^R+(7A+D) divisible by D*2^(H+12). The base condition holds
because A+(7A+D)=8A+D is divisible by 8. Cancelling the odd A
gives D | 9^R+7. Its positive quotient u then satisfies
A*u+1=2^(H+12)*q. The new odd_power_cancel root proves cancellation
by induction on the binary exponent. For fixed weighted R, take a
larger pure exponent S and set w=9^(S-R), proving w>B separately.

CONVERGENT WITNESS, KERNEL AND PYTHON:
R=14,r=0,H=128, with named witnessWeight and witnessUnit in Lean.
The source sizes (N,P,Q) are (239,228,238) bits. Their ordinary
arrival clocks at 1 are (1795,1978,2660). Lean certifies the coordinate
conditions, shadow divisibility and arrivals. Python additionally proves
first-arrival minimality by replaying all 6,433 operations. These
convergent sources still have the separated 129-state exit windows.

VERIFICATION 2026-10-22T01:50:30.738627+00:00:
One fresh Lean 4.33.1 build, 1.991 seconds, 16 threads; 39 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 84 prior hashes and
all 87 current hashes authenticated. All 40 cached .olean objects,
including the new development object, match the current manifest.
Final verifier session 13718 exited 0. All milestone jobs are terminal.
The cache procedure retains prior reused-build provenance, authenticates
compiler/source/log/object, copies to an isolated import directory, and
always freshly builds the new module. Without --cache all 40 modules
are built sequentially. Historical manifests were not rewritten.

INDEPENDENT FINITE SCOPE:
600 complete weighted triples, with all 1,800 source prefixes checked
by ordinary, shortcut and inverse operations. Ordinary prefix steps:
1,968,997; shortcut and inverse edges: 1,132,081 each. Including
260 generic scalar triples, the explicit witness and two larger tails,
863 separated windows contain 254,871 replayed states and 252,282
ordinary steps. Exact residue sets prove separation across all pairs
of window times; 851 small windows also compare actual value sets.
No quadratic enumeration of every pair is claimed.

Maximum complete parameters R=16384,r=4096,H=16384 occur in different
examples. Maximum N has 49,365 bits; P 45,284; Q 45,294; weight
45,251; scalar a 52,143. Pure lifts have 312 modular-only checks,
including (r,H)=(128,128),(512,0),(0,4096). Their largest exponent
has 8,291 bits, but their full sources and trajectories are NOT
materialized. Larger weighted coordinates use R=65536 and 1048576,
r=0,H=32, with N up to 3,145,831 bits. Only 498 transition-tail
steps and the exit windows are replayed there, not the growing prefixes.

NEXT RESEARCH AND EXPLORATORY EVIDENCE:
Do not seek a complete two-partner proof by merely enlarging a fixed
post-transition clock window: the new theorem rules that out. A cover
allowing unbounded later clocks remains possible, as do more partners.
The earlier 13/61 exclusions remain valid and are not contradicted.

A broader SCRATCH search /tmp/collatz_seventeen_multi.py examines
Mersenne shifts c<=96 and c<=1024 whose negative reference reaches17.
At binary depth14 it matched 2552/8192 and2553/8192 odd scalar classes,
respectively; no complete cover. These are exploratory pattern matches,
not kernel exclusions. Session27388 is terminal, exit0. Adding more
large shifts barely changed this finite search, motivating the separation
argument. Failure of a search itself is not an impossibility result.

PROMISING FOURTH SOURCE, NOT YET FORMALIZED:
For the preceding transition with r>=5, let S=2^(2R+13)*w-1.
The negative reference 7*3^13+1 reaches17 after 56 odd operations
and108 halvings, ordinary clock164. Algebra predicts
  C^(4R+100+18r)(S)=48a-17,
  C^(4R+102+18r)(S)=72a-25=(72a-17)-8.
S lies between the existing smaller partners, so R>=14 suffices for
positivity and S<N. Its proposed extra seventeen-cycle count is r-5.
Four independent scratch replays at R14,r=5,6,16,64,H32 confirmed
the two displayed clocks. This formula is NOT in the kernel module,
note theorem list or verification manifest; do not report it as proved.
At a=-1/9 its reference -67/3 reaches -33 and then the negative17
cycle, so this fourth source does not share the three disjoint shadow
sets used in the new two-partner barrier. It is a concrete next lead.

ATTEMPT, README and reproduction commands include the new note. No
installation, credential access, agents, staging, commits or Git writes
occurred. HEAD remains 8dcff74; index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
All existing user changes are preserved. The full Collatz goal remains
active. Arbitrary least-source exclusion, family convergence, the cap/
residual estimates, nontrivial cycles and divergence remain unresolved.

The preceding negative-seventeen transition handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the negative-seventeen transition.

Research remains active with no external blocker. Previous goal turn:
progress (19 phase-cover roots). Current turn: progress (19 kernel roots,
variable negative-seventeen blocks and unbounded pure exponent exclusions).
The positive-integer Collatz conjecture remains unresolved. Use 16 Lean
threads per process on this 16-CPU machine; keep heavy checks sequential
and reuse authenticated verified objects. The user explicitly permits
increasing Lean thread counts for speed.

LATEST ARTIFACTS:
docs/MINIMUM-SEVENTEEN-TRANSITION.md, lean/MinimumSeventeenTransition.lean,
verify_minimum_seventeen_transition.py, results/minimum-seventeen-transition/.
All 19 roots passed a fresh kernel dependency audit. All use only standard
logical axioms. In particular finite_odd_targets is NOT axiom-free: it
uses propext and Quot.sound despite being proved by decide +kernel.
There is no native reduction, new mathematical axiom, unproved merger,
or external mathematical premise in the new module.

VARIABLE THREE-SOURCE TRANSITION, KERNEL:
Let R>=14,w,u>0,r>=0, X=9^R*w, X+7=2^(57+11r)*u,
and a=3^(33+7r)*u. Define
  N=4*8^R*w-5,
  P=2^(2R+5)*w-1,
  Q=2^(2R+15)*w-1.
Then 0<P<N and 0<Q<N, and the ordinary clocks are
  C^(5R+91+18r)(N)=72a-17,
  C^(4R+99+18r)(P)=81a-17,
  C^(4R+99+18r)(Q)=64a-17.
The three initial prefixes reach 4X-5,243X-1,14348907X-1
at clocks 5R,4R+10,4R+30. The three new bridges are
  C^19(2^12*q-33)=3^7*q-17,
  C^35(2^24*q-1702)=3^11*q-17,
  C^69(2^51*q-100442350)=3^18*q-17, q>0.
Their Backtrack counts (extra even,odd) are (5,7),(13,11),(33,18).
The latter offsets are 7*3^5+1 and 7*3^15+1. Following the bridges,
N,P,Q traverse respectively r+4,r+3,r negative-seventeen blocks.
Each block has shortcut word OOOOEOOOEEE and ordinary length18.
All actual sources and iterates here are positive; the negative orbit
is an auxiliary parity pattern, not a positive counterexample.

SCALAR EXITS AND LEAST EXCLUSIONS, KERNEL:
For a=64v+13,
  C^10(72a-17)=972v+194=b,
  C^4(81a-17)=1944v+389=2b+1, with b=2mod4.
Hence C^7(81a-17)=C^12(72a-17). Full clocks (P,N) are
4R+106+18r,5R+103+18r. Python adds one common halving to complete
both shortcut words, using clocks one larger.

For a=64v+61,
  C^12(72a-17)=1458v+1385=b,
  C^6(81a-17)=2916v+2771=2b+1,
  C^17(64a-17)=1458v+1384=b-1.
Write b+1=2^k*q with k>0,q positive odd. Either exit is covered:
  3^k*q=3mod4: P,N clocks 4R+109+18r+2k,5R+106+18r+2k;
  3^k*q=1mod4: Q,N clocks 4R+118+18r+2k,5R+105+18r+2k.
There is no bound on k. Thus a=13 or61mod64 excludes N as least.
These conditional scalar exits do NOT cover all scalar units. No
convergence of all family members or all partners is established.

UNBOUNDED PURE EXPONENTS, KERNEL:
For EVERY r,B and e in {13,61}, there exist R>B,R>=14,u>0 with
  9^R+7=2^(57+11r)*u, 3^(33+7r)*u=e mod64,
  not LeastCounterexample(4*8^R-5).
This is an existence result at every block length and exponent bound,
not exclusion of every pure exponent. Written modular consequence:
9^R=1+8R mod64, so these classes lie at R=7mod8, distinct from
the previous pure R=35mod64 phase exclusion.

Construction: m=57+11r,D=2^m,T=2^(m-3), A=liftExponent(m+3).
Existing lifts give 9^A+7=64D*t, 9^T=1+D*v with v odd.
New induction: (1+64d*v)^h=1+64d*U with U=h*v mod64.
Since 9^A=57mod64, choose h0<64 with
57*3^(33+7r)*v*h0=e mod64. The finite odd-multiplier target lemma
provides this. Set h=h0+64*(B+14), R=A+T*h,
u=64*t+9^A*U. The exact identity, target residue and bounds follow.
Do NOT materialize 9^R or the pure source even for r=0: these R
are already enormous. Use modular powers and the kernel theorem.

VERIFICATION 2026-10-22T01:18:28.186070+00:00:
One fresh Lean 4.33.1 build, 7.028 seconds, 16 threads; 38 authenticated
dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 82 prior hashes and
all 84 current hashes authenticated. All 39 cached .olean objects,
including the new development object, match the current manifest.
The final verifier session 59327 exited 0; all milestone jobs terminal.

CACHE CONTINUITY: The new verifier supports a prior record already
marked as reused. Use previous.get('command',
previous.get('prior_compile_command')) rather than previous['command'].
It retains the prior build record and original elapsed-time provenance,
copies exact authenticated objects into an isolated import directory,
and rebuilds mismatches. The new module is always fresh. Without
--cache all 39 modules are rebuilt sequentially. Do not rewrite old
manifests or claim the reused dependencies were recompiled this turn.

Independent full weighted meetings: 632 pairs, 206 even exits,
208 double-odd and 218 adjacent-odd. Complete ordinary N steps: 1,245,882;
chosen P/Q steps: 1,134,246; full unselected third-source steps: 1,049,378.
All three complete source paths have shortcut and inverse checks.
Including bridge examples, shortcut and inverse edges are 1,997,953 each.
Maximum complete R=16384, r=4096, late odd-block length=4096; maximum N
49,570 bits, chosen partner 45,166 bits, weight 45,119 bits. These maxima
need not occur in the same example. No new general prefix minimum
or optimal inverse budget theorem is claimed.

Generic bridge tests: 774 paths, 31,734 ordinary steps. Scalar tests
use v=0..2047 at both residues, plus selected full/larger local tails;
total 4,732 local pairs and 289,600 steps. There are 64 odd-target
permutation checks and 680 powered-unit examples. Modular pure
exponents: 408 cases, r=0..64,128,256,1024, three bounds at both exits;
largest exponent has 12,477 bits, but its source is NOT materialized.
Ten small exponent lifts also receive exact-power checks.

Larger weighted coordinates use R=65536 and 1048576, at (r,e)=(0,13)
and (16,61). Maximum source has 3,145,968 bits. Only 2,724 transition
tail steps plus local exits were replayed; full growing prefixes were
NOT iterated for these four large examples.

NEXT RESEARCH:
Extend the scalar relation among 72a-17,81a-17,64a-17 beyond a=13/61
mod64, or find a construction that handles arbitrary least sources.
An unrestricted merger for this triple is not proved. The current
result supplies the previously missing positive coalescence across
the negative-five to negative-seventeen transition, but only at the
specified exits. Full convergence, nontrivial cycles, divergence and
the quantitative cap/residual gap remain open.

Exploratory search (not verification): fixed-parity affine searches
around X=-7 with preceding smooth weighted sources found no direct
match through chosen precisions 128 bits and depth 32. Failure is not
an impossibility theorem. Negative-shadow Mersenne shifts 5 and 15
then yielded the adjacent derivative grades 8 and 6 around the target
grade 7; matching extra seventeen cycles gave the 72,81,64 triple.
A finite scalar search found the two formalized residues and some
deeper subclasses; no full scalar cover was found or inferred. Its final
modulo-65536 diagnostic reports 14,185 matched and 51,351 unmatched
classes. This is scratch search output, not a kernel exclusion or
impossibility result. Scratch /tmp/collatz_seventeen_triple.py session
88822 is terminal with exit 0.

ATTEMPT, README and reproduction commands include the new note.
No installation, credential access, agents, staging, commits or Git
writes occurred. Existing user changes were preserved. HEAD 8dcff74;
index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
The unbounded Collatz goal remains active, without an external blocker.

The preceding two-partner phase-cover handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the two-partner phase cover.

Research remains active, with no external blocker. Previous goal turn:
progress (12 doubled-ladder roots). Current turn: progress (19 new
kernel roots and new doubled/quadrupled weighted exclusions). The
positive-integer Collatz conjecture remains unresolved. Keep 16 Lean
threads per process and sequential heavy builds. Reuse authenticated
completed verification where possible; see the cache procedure below.

LATEST ARTIFACTS:
docs/MINIMUM-PHASE-COVER.md, lean/MinimumPhaseCover.lean,
verify_minimum_phase_cover.py, results/minimum-phase-cover/.
All 19 roots passed a fresh kernel audit. finite_phase_periods is
axiom-free; the other roots use only standard logical axioms. No
native reduction, added premise, or unproved merger is used.

NEW SCALAR COVER, KERNEL:
For EVERY b=3a+2, either Merges(2b+1,b) or Merges(a,b).
This extends the endpoint class beyond the earlier b=9a+5 cover.
The local ordinary clocks (partner first, then b) are:
  b=0 mod4: partner a, (3,2).
  b=2 mod4: partner 2b+1, (3,2).
  b odd, b+1=2^k*q with q odd:
    3^k*q=1 mod4: partner a, (2k+3,2k+2).
    3^k*q=3 mod4: partner 2b+1, (2k+4,2k+3).
For odd b, a is odd and C(a)=b-1. That supplies the adjacent
partner for the prior arbitrary-block cover. For b divisible by
four, write a=4v+2; the meeting is 3v+2. The verifier appends one
common halving in the double-even case, using clocks (4,3), so
both full shortcut words finish their forced odd-step halvings.
The larger scalar partner is NOT a descent; its original source
must separately be proved smaller than the original N.

NEW DOUBLED WEIGHTED CLASS, KERNEL:
Let R>=2,w>0,X=9^R*w, with X=17 mod256. Define
  N=2*8^R*w-5,
  P=2^(2R+1)*w-1,
  Q=3*8^(R-1)*w-5,
  b=(81X-97)/256, a=(b-2)/3.
Then 0<P<N, 0<Q<N, 3(N+5)=16(Q+5), and
  C^(5R+13)(N)=b,
  C^(4R+12)(P)=2b+1,
  C^(5R+7)(Q)=a.
Coordinates: X=768u+273, X/3=256u+91,
b=243u+86, a=81u+28. At least one of P,Q coalesces with N,
so N cannot be least. For pure w=1 this covers R=26 mod32,
which lies in the previously unresolved doubled exit k=1,
s=1 mod4, 3^k*s=3 mod4. Do not continue treating that entire
exit as untouched; other exponents in it remain unresolved.

NEW QUADRUPLED WEIGHTED CLASS, KERNEL:
Let R>=2,w>0,X=9^R*w, with X=473 mod512. Define
  N=4*8^R*w-5,
  P=2*8^R*w-5,
  Q=2*8^(R-1)*w-5,
  b=(243X-251)/512, a=(b-2)/3.
Then 0<P<N, 0<Q<N, N+5=2(P+5)=16(Q+5), and
  C^(5R+16)(N)=b,
  C^(5R+14)(P)=2b+1,
  C^(5R+11)(Q)=a.
Coordinates: X=4608u+3033, X/9=512u+337,
b=2187u+1439, a=729u+479. These b are 8 mod9, outside
the older b=9a+5 scalar cover. The two-source construction
excludes N as least. For pure w=1 it covers R=35 mod64.
Neither whole-family convergence nor all-exponent exclusion is proved.

SIX BRIDGES, KERNEL:
  C^13(1536u+541)=243u+86,
  C^10(2304u+818)=486u+173,
  C^12(256u+86)=81u+28,
  C^16(18432u+12127)=2187u+1439,
  C^14(9216u+6061)=4374u+2879,
  C^16(1024u+669)=729u+479.
Their shortcut words are respectively
OEEOOEOEE, EOEOOEE, EOOEOEOE,
OOOOOEEEEEE, OEEOEOEOO, OEEOOEOOEO.

VERIFICATION 2026-10-22T00:41:38.517236+00:00:
One fresh Lean 4.33.1 module build, 5.711 seconds, 16 threads;
37 previously verified dependency objects reused. Compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 80 prior manifest
hashes and all 82 new hashes authenticated. All 19 theorem roots
audited. Final verifier session 21715 exited 0; all jobs terminal.

CACHE PROCEDURE: Every dependency object in /tmp/collatz-locality-dev
matched the preceding manifest's olean SHA256 exactly. The new
verifier's optional --cache authenticates source, prior log, compiler
version and object bytes, copies the authenticated object into a
fresh isolated import directory, and freshly builds missing or
mismatched objects. The new module is always fresh. The manifest
marks fresh_build=false and reused_verified_build=true for reused
dependencies and retains their prior provenance. They were NOT
recompiled in this run. Without --cache, all 38 modules build afresh.
The cache now also contains the development MinimumPhaseCover.olean;
authenticate its hash against the new manifest before future reuse.

Independent full meetings: 702 distinct pairs, 351 per phase.
Doubled branch counts: 54 double-even, 54 third-even, 124 double-odd,
119 third-odd. Quadrupled: 54 double-even, 54 third-even, 119 double-odd,
124 third-odd. Actual N steps 550,493; actual chosen partner steps
526,710; shortcut and inverse edges 626,796 each. All three source
bridges add 28,431 independent ordinary steps. The 926,558 growing
prefix lower checks are finite observations, not a new uniform
weighted-prefix minimum theorem. Maximum complete R=16,419,
N has 49,259 bits and the selected partner 49,258 bits. Constructed
post-bridge odd blocks reach k=4096 at both exits, at weighted R=2.

Generic checks: a=0..8191, all four scalar branches; 262 additional
long-block examples. Including selected full-pair local tails there
are 9,156 local pairs and 325,932 local steps. Six bridge profiles
have 3,084 paths and 41,634 steps. There are 2,064 modular-only
weighted examples and 258 modular-only pure exponents; huge sources
are not materialized in that section.

Larger coordinate-only examples: doubled R=32,794 and 524,314;
quadrupled R=65,571 and 1,048,611. Maximum source bit length is
3,145,835. Only 222 bridge/local tail steps were replayed; the full
growing prefixes were NOT numerically iterated at those exponents.

NEXT RESEARCH / EXPLORATORY EVIDENCE:
Remove further endpoint restrictions, especially by a general block
relation. An arbitrary least source has not been placed in any
covered family. The opposite doubled exit and most quadrupled
exponents remain open. The pure family 8^R-5 is already excluded
as least for every R>0; its universal convergence remains unproved.

The successful new ingredient was replacing the three-partner cover
by the two-partner cover for b=3a+2. A source reaching (b-2)/3
also reaches b-1 when b is odd, and covers b=0 mod4 directly.
Earlier searches that required a separate fixed path to b-1 missed
this. A scratch symbolic search found two more potential quadrupled
classes using offset-seven sources. They are NOT yet in the kernel
or manifest:

  X=329 mod512 (pure R=9 mod64):
    N=4*8^R-5 -> b=(729X-737)/512 at 5R+17,
    P=3*8^R-5 -> 2b+1 at 5R+13,
    Q=8^R-7 -> (b-2)/3 at 5R+14.
  X=185 mod1024 (pure R=15 mod128):
    N=4*8^R-5 -> b=(729X-721)/1024 at 5R+18,
    P=2*8^R-5 -> 2b+1 at 5R+16,
    Q=2*8^R-7 -> b-1 at 5R+17,
    D=3*8^(R-1)-5 -> (b-5)/9 at 5R+10.
The first suggests the new two-partner cover; the second suggests
the existing three-partner cover. Both need a rotated negative-five
prefix, conjectured/elementary OEO form
C^(5R)(8^R*w-7)=9^R*w-7 with positivity restrictions. That prefix
has NOT been formalized here. Do not turn scratch matches into
reported theorems. The scratch search used fixed-parity affine tails,
smooth weights through six preceding blocks, Mersenne shifts -12..24,
and exponent periods through 256; failures prove no impossibility.

A broader observation worth investigating, not a proved construction:
quadrupled exponents can lift 9^R toward -7 in the binary sense,
using the prior liftExponent machinery. The terminal value then
shadows -33, whose negative orbit joins the magnitude-17 cycle.
That suggests arbitrarily long later negative-seventeen blocks,
already available as cycle_repeated/cycle_clock in MinimumNegativeCycle.
A positive-source coalescence argument for this transition is missing.

Reproduce with --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16
--cache /tmp/collatz-locality-dev. ATTEMPT and README link the new
note and reproduction command. No installation, credential access,
agents, staging, commits or Git writes occurred. HEAD remains 8dcff74;
index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Universal convergence, the cap/residual estimates, nontrivial cycles,
divergence and the full Collatz goal remain open, with no external blocker.

The preceding doubled-ladder handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the doubled-ladder extension.

Research remains active, with no external blocker. Previous goal turn:
progress (17 three-source cover roots). Current turn: progress (12 new
kernel roots for doubled weighted sources and exact exponent units).
The positive-integer Collatz conjecture remains unresolved. Continue
using the user's authorized 16 Lean threads per process, with heavy
dependent builds sequential. The machine reports 16 CPUs.

LATEST ARTIFACTS:
docs/MINIMUM-DOUBLE-LADDER.md, lean/MinimumDoubleLadder.lean,
verify_minimum_double_ladder.py, results/minimum-double-ladder/.
All twelve new theorem roots passed fresh kernel audits, with only
standard logical axioms. No native reduction, new axiom, unproved
merger hypothesis or external mathematical premise enters the results.

NEW PURE DOUBLED EXCLUSION, KERNEL:
For N=2*8^R-5, every odd R is excluded as a least counterexample.
For R=2^k*s with k,s>0 and 3^k*s=1 mod4, let P=8^R-5. Then
  0<P<N, N+5=2(P+5),
  C^(5R+2k+7)(P)=C^(5R+2k+8)(N).
Thus these even exponents are also excluded as least sources.
There is no bound on k. In particular, the exclusions include
R=2^k for positive even k, and R=3*2^k for positive odd k.
No convergence of every family member is proved.

REMAINING DOUBLED CONDITION, KERNEL:
If LeastCounterexample(2*8^R-5), R>0, then there exist k,s with
  k>0, s>0 odd, R=2^k*s, and 3^k*s=3 mod4.
Equivalently the remaining parity classes are k odd, s=1 mod4,
or k even, s=3 mod4. These are remaining conditions, not actual
counterexamples. The new construction does not handle that exit.

EXACT UNIT LIFT, KERNEL:
For EVERY natural k,s, there is a natural u with
  9^(2^k*s)=1+2^(k+3)*u, u=s mod4.
For s>0, u>0. For odd s, u is odd, so the power of two dividing
9^(2^k*s)-1 is exactly 2^(k+3). The base quotient for 9^s is
proved by induction. Doubling the exponent replaces u by
u+2^(k+2)*u^2, preserving its residue modulo 4.
This strengthens the earlier top-bit lemma without external LTE.

WEIGHTED CONSTRUCTION, KERNEL:
For R,w,k,u>0, assume
  X=9^R*w=1+2^(k+3)*u, and 3^k*u=1 mod4.
Put N=2*8^R*w-5, P=8^R*w-5, a=2^k*u, b=9a-1.
The growing prefixes have ordinary clock 5R, and
  C^(5R+6)(N)=b,
  C^(5R+5)(P)=b-1.
The two bridges are C^6(32v+29)=18v+17 and
C^5(16v+12)=18v+16. Since b+1=2^k*(9u) and its exit is
1 mod4, the earlier adjacent_odd_block theorem joins b-1 and b
after 2k+2 ordinary steps each. This yields the same full meeting
clocks as above and excludes the weighted N as least.
The common endpoint is (9*3^k*u-1)/4. Complete shortcut words:
  N: (OOE)^R OEEO O^k EE,
  P: (OOE)^R EE O^(k+1) EO.
No earliest meeting, optimal inverse cost, or uniform budget is claimed.

VERIFICATION 2026-10-22T00:16:16.994000+00:00:
37 fresh Lean 4.33.1 builds, sequential dependency order, 73.799 seconds,
16 threads per process; the new module took 1.297 seconds. All twelve
roots audited. Compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 78 preceding manifest hashes and all 80 new manifest hashes were
authenticated. Final verifier session 34180 exited 0; all jobs terminal.

Independent complete paths: 1,167 distinct pairs, from 133 pure and
1,038 weighted pairs with four overlaps counted once. Actual N steps
405,658; actual P steps 404,491; independently checked shortcut edges
479,931 and inverse edges 479,931. Local tails add 89,592 ordinary
steps. The 707,720 prefix lower checks are finite observations; no
new general weighted-prefix minimum theorem was added. Maximum
complete R=16,384; source bit lengths 49,153 (N), 49,152 (P).
Weighted secondary blocks reach k=4096, at R=1 and R=3.
The complete path replay streams large ordinary paths to save memory.

Additional finite checks: 2,052 bridge paths, 11,286 steps; 297 exact
unit examples at k=0..8,s=0..32; 256 odd-exponent smaller predecessors
with 512 steps; 256 opposite-exit nonmeetings at the specified clocks,
9,728 steps. Those nonmeetings say nothing about eventual coalescence.
There are 8,224 modular-only unit checks at k=0..256,s=1..63 odd;
their huge sources are not materialized.

Larger coordinate-only pure cases have R=65,536 and 1,048,576, with
k=16 and 20. Source bit lengths are 196,609 and 3,145,729. Only the
174 ordinary tail steps after the growing prefixes were replayed;
the full prefixes were NOT numerically iterated at these exponents.

NEXT RESEARCH:
Handle the opposite doubled exit 3^k*s=3 mod4, and the quadrupled
phase N=4*8^R-5. The whole pure family 8^R-5 is already excluded
as least by MinimumLadderCover; do not reopen its old R=9 mod16 gap.

Useful UNFORMALIZED endpoint candidates for the remaining doubled
case: R even, X=9^R, a=(X-1)/8, b=9a-1. The new pure partner
8^R-5 reaches b-1 at clock 5R+5. Other smaller sources reach:
  2*8^(R-1)-5 -> a-2 at clock 5R+1,
  6*8^(R-1)-5 -> 3a-2 at clock 5R+1,
  2^(2R-1)-1 -> a at clock 4R+2,
  2^(2R+1)-1 -> 9a+1=b+2 at clock 4R+6.
These identities were only exploratory algebra this turn; they have
not been added to the new kernel module or verification manifest.
The generic odd cover supplies a merger with 2b+1 at the remaining
exit, but no smaller original source reaching that partner is known.

For the quadrupled phase, the basic mod3 restriction leaves R odd.
Then a=(9^R-1)/8 is odd and its growing endpoint is 32a-1, with
an exact initial odd block of length five. No new quadrupled-family
exclusion was established this turn.

A limited scratch affine search refined exponents modulo 2,4,8,16,32,
using smooth weighted coefficients through eight preceding blocks,
Mersenne shifts -16..3, and negative-cycle offsets 5,7,10. It found
no additional full cover of the opposite doubled exit or quadrupled
phase. It stops when parity ceases to be fixed. Its failures are not
impossibility results; it is not a verification artifact. Prefer a
general new block relation over an expanding finite residue catalog.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 to reproduce.
ATTEMPT and README link the new module and note. No installations,
credential access, agents, staging, commits or other Git writes occurred.
Existing user changes were preserved. HEAD remains 8dcff74; index SHA256
remains ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Universal family convergence, arbitrary least-source exclusion, the
cap/residual estimates, nontrivial cycles, divergence and full Collatz
remain open. This is mathematical progress, not an external blocker.

The preceding three-source cover handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the three-source ladder cover.

Research remains active, with no external blocker. Previous goal turn:
progress (21 complementary-exit roots). Current turn: progress
(17 new kernel roots, closing all positive pure-ladder exponents as
least-counterexample candidates). The positive-integer Collatz conjecture
remains unresolved. Use 16 Lean threads per process, heavy builds sequential.

LATEST ARTIFACTS:
docs/MINIMUM-LADDER-COVER.md, lean/MinimumLadderCover.lean,
verify_minimum_ladder_cover.py, results/minimum-ladder-cover/.
All 17 theorem roots passed fresh kernel audits. finite_small_ladders
is axiom-free; the other roots use only standard logical axioms.
No native reduction axiom, unproved merger hypothesis or external
mathematical premise enters the new exclusion.

THE WHOLE PURE LADDER IS NOW EXCLUDED AS LEAST, KERNEL:
For EVERY R>0, not LeastCounterexample(8^R-5).
The old least-exponent restriction forces R=9 mod16 for R>=3;
the new three-source construction excludes that last class.
The two small cases are kernel convergence certificates:
C^7(3)=1 and C^32(59)=1.
Do not continue treating R=9 mod16 as an unresolved LEAST-source
case for this family. Convergence of every family member remains
unproved, since the smaller partners need not lie in the pure family.
No theorem forces an arbitrary least counterexample to be a pure ladder.

STRONGER WEIGHTED CONSTRUCTION, KERNEL:
For R>=3, q>0, N=8^R*q-5, X=9^R*q, assume X=73 mod128.
Let b=(9X-17)/128, with b=14 mod27, and a=(b-5)/9.
There are three positive sources strictly smaller than N:
  M=2^(2R-1)*q-1,
  P=8^(R-1)*q-5,
  D=2*8^(R-2)*q-5.
Their exact ordinary endpoints are
  C^(5R+9)(N)=b,
  C^(4R+7)(M)=2b+1,
  C^(5R+6)(P)=b-1,
  C^(5R+2)(D)=a, with b=9a+5.
The kernel also proves N+5=8(P+5)=32(D+5).
At least one of these three smaller sources coalesces with N.
Thus the entire weighted residue class is excluded as least sources.

UNIVERSAL SCALAR COVER, KERNEL:
For any natural a,b with b=9a+5, one of 2b+1, b-1, a coalesces
with b. The complete cases and LOCAL ordinary clocks are:
  b=2 mod4: partner 2b+1, clocks (3,2).
  b=0 mod4: partner a, clocks (4,2).
  b odd: factor b+1=2^k*v with k>=1 and v>0 odd.
    If 3^k*v=3 mod4: partner 2b+1, clocks (2k+4,2k+3).
    If 3^k*v=1 mod4: partner b-1, clocks (2k+2,2k+2).
Each pair lists the partner's clock first, then b's clock. The proof
uses odd factorization and the half-source meeting theorem at arbitrary
k. It is not a bounded search or extrapolation. Adding the source
prefix clocks gives the complete meetings. No earliest meeting,
optimal inverse cost, or new uniform inverse budget is claimed.

The key new source was the MINUS Mersenne path to 2b+1; the earlier
plus Mersenne path only reached 9b+2. The older proposed universal
merger between b and 4b-1 remains unproved and is NOT used. The
new cover does not assert that every positive b merges with a smaller
number: 2b+1 is larger than b, while its original source M is smaller
than N. This distinction is important for the full conjecture.

BRIDGE IDENTITIES, KERNEL:
  C^9(384u+196)=27u+14,
  C^9(128u+66)=54u+29,
  C^11(128u+60)=81u+40,
  C^12(256u+237)=81u+76.
The source prefixes use the existing weighted OOE and all-odd paths.
Condition X=73 mod128 gives X/3=67, X/9=65 and X/81=121 mod128.
The resulting b coordinates are 27u+14, 81v+41, and 729w+689.
For pure q=1 and R=9 mod16, the condition follows from the already
kernel-certified period of powers of nine. This closes the pure case.

VERIFICATION 2026-10-21T23:53:08.724317+00:00:
36 fresh Lean 4.33.1 builds, dependency order, 69.622 seconds,
16 threads per process; the new module took 3.666 seconds.
All 17 roots audited; one axiom-free. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Authenticated all 76
preceding hashes and all 78 current hashes. Historical files preserved.
Final verifier session 88039 exited 0; all jobs are terminal.

Independent generic checks: 4,096 three-partner pairs (38,909 ordinary
steps), 2,048 arbitrary-odd-block examples (277,504 steps), and 2,056
bridge paths (21,074 steps). The two small convergence replays have
39 ordinary steps total and agree with the new kernel certificates.
There are 4,128 modular-only weighted examples at R=2^j+3, j=0..128,
and h=0..31, with weight r+128h and r the appropriate odd residue.
Their enormous sources are NOT materialized. There are 262 independently
constructed secondary-block weights: k=1..128,512,1024,4096, both exits.

Complete positive coalescences: 627 distinct (R,q) pairs. Branch counts:
91 ninth-even, 92 double-even, 221 double-odd, 223 adjacent-odd.
There are 877,341 actual N steps and 810,017 actual partner steps,
917,887 independently replayed shortcut edges, 425,125 inverse-prefix
edges, and 115,981 independent local-tail steps. The 814,582 weighted
growing-prefix lower checks are finite observations; this module does
not add a general weighted-prefix minimum theorem. Reused source pairs
are counted once. Ranges: R=3..32 with eight weights in each residue
class; pure R=16h+9 for h=0..128,512,1024; both long-block exits at
k=1..128,512,1024,4096, constructed with fixed R=3.
Largest complete R=16393; largest complete source has 49,179 bits.
No convergence after these meetings is claimed.

Larger coordinate-only cases have R=65545 and R=1048585, both in the
adjacent-odd branch at k=3. Their source bit lengths are 196,635 and
3,145,755; partner bit lengths are 196,632 and 3,145,752. Only exact
coordinates and 72 short ordinary tail steps were independently
replayed; the full growing prefixes were NOT numerically iterated.

NEXT RESEARCH:
Extend beyond the weighted terminal condition 9^R*q=73 mod128 and
handle fewer initial growing blocks. The first natural missing phases
are q=2 and q=4, hence pure powers 2^L-5 with L not divisible by three.
The current weighted theorem cannot cover even q. An unformalized
bridge for q=2 is C^6(2*9^R-5)=(9^(R+1)-17)/8 for R>=1; it follows
from C^6(16u+13)=9u+8. This suggests the next endpoint to inspect,
but no new coalescence theorem for that phase was established here.

A limited symbolic diagnostic at weighted R=3, weights modulo 128,
found matches in 47 classes (including the new cover) and no match in
81, including q=2 and q=4. It tried smooth weighted coefficients
2^a*3^b<8^d for d=1..3 and Mersenne shifts -5..2, stopping when
parity ceased to be fixed. This diagnostic is not in the verification
manifest and its failures prove no impossibility. Prefer general
block relations and a justified covering argument over a growing list
of finite residue cases. Universal family convergence, arbitrary
least-counterexample exclusion, cap/residual estimates, nontrivial
cycles, divergence and the full Collatz objective remain open.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for reproduction.
No installations, credentials, agents, staging, commits or other Git
writes occurred. User changes were preserved. HEAD remains 8dcff74;
index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
ATTEMPT and README now link the new note and reproduction command.

The preceding complementary-exit handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the complementary ladder exit.

Research remains active, with no external blocker. Previous goal turn:
progress (25 variable block-exit roots and verified handoff). Current
turn: progress (21 complementary-exit kernel roots). The full
positive-integer Collatz conjecture remains unresolved. Continue with
16 Lean threads per process and sequential heavy dependent builds.

LATEST ARTIFACTS:
docs/MINIMUM-LADDER-COMPLEMENT.md, lean/MinimumLadderComplement.lean,
verify_minimum_ladder_complement.py, results/minimum-ladder-complement/.
All 21 roots passed fresh kernel audits. finite_residue_injection is
axiom-free; the other roots use only standard logical axioms. No native
reduction axiom, added premise, or external mathematical result enters
the unconditional exclusions. remaining_merge_suffices explicitly has
an unproved merger hypothesis; do not erase that hypothesis in reports.

THE PREVIOUS R=512h+5 GAP IS NOW HANDLED, KERNEL:
For odd R>=3, N=8^R-5, write 3*9^R+5=2^(k+4)*q with q>0.
If k>=2 and 3^k*q=1 mod4, choose P=6*8^(R-1)-5. Then
0<P<N, 4(P+5)=3(N+5), and
  C^(5R+2k+4)(P)=C^(5R+2k+7)(N)=b,
  4b+1=3^k*q,
  Backtrack(R+4,2R+k,b,P).
The new inverse even count GROWS with R. It is not the earlier fixed
five-even Mersenne construction and has no claimed optimality.

The weighted prefix identity is
Backtrack(r,2r,9^r*q-5,8^r*q-5) for natural q>0, using Nat subtraction;
all new positive paths use q=6. The shortcut word is (OOE)^r.
For odd R, write 9^R=48u+9 and 6*9^(R-1)=32u+6. The bridges are
C^5(48u+4)=9u+1 and C^8(32u+1)=27u+2. With 2^k*q=9u+2,
the second bridge ends at 3d-1, d=2^k*q-1. Two halvings give
2^(k-2)*(3q)-1; its odd block and EO exit join N's odd block and EE
exit. The complete forward shortcut words are
  N: (OOE)^R EEOE O^k EE,
  P: (OOE)^(R-1) OEOEO EE O^(k-2) EO.

FIRST LATER TARGETS AND UNBOUNDEDNESS, KERNEL:
For k>=3, b=20 mod27 and no ordinary clock t with
5R<=t<5R+2k+7 has residue 20. The bridge and odd-block avoidance
lemmas are reused; the last residues are 26,13,20. Combining both
exit cases gives a useful FIRST later residue-20 target for every odd
factorization with k>=3. The delays are exactly 2k+7 or 2k+8 and the
source constructions have different sizes and costs.

Adding 2^(k+2) to a previously successful exponent flips its quotient:
9^(2^(k+2))=1+2^(k+5)*a for odd a, and
Q=q+2*(3*9^R*a). The exit product changes from 3 to 1 mod4.
This constructs arbitrarily large complementary exponents for every k.
For every k>=3 and source bound, a kernel existential root supplies
a larger source with the first useful later target at exact delay 2k+7.
Small complementary seeds for k=2..10 are
29,21,101,197,5,901,1157,645,5765, with period 2^(k+3).
Existence is kernel; no all-k uniqueness theorem is claimed.

Every R=512h+5 has k=6 and the complementary condition, so the kernel
now excludes this whole progression as least counterexamples. Its first
later target is at clock 5R+19; P joins at clock 5R+16.

WHAT REMAINS, KERNEL RESTRICTION AND CONDITIONAL ROUTE:
The preceding least-source condition had R=1 mod4, k>0 and the failed
exit. The new path forces k=1, q=3 mod4, 9^R=73 mod128, hence
R=9 mod16. All R>=3 outside that class are now excluded as least
counterexample exponents for N=8^R-5. This does NOT prove convergence
of the infinite family, and is not a density statement for all integers.

For R=16h+9 the necessary factorization holds arithmetically. This is
compatibility with the post-ladder condition alone; other project
restrictions may exclude subfamilies. The kernel identifies
  b=(9*9^R-17)/128, b=14 mod27,
  C^(5R+9)(N)=b,
  C^(5R+4)(P)=4b-1.
A later merger of these particular endpoints would exclude N. That
merger for every R=9 mod16 remains UNPROVED. The R=9 member
N=134217723 reaches 1 at ordinary clock 309 in independent Python;
this is not a new Lean convergence certificate.

VERIFICATION 2026-10-21T23:25:28.434493+00:00:
35 fresh Lean 4.33.1 builds in dependency order, 66.440 seconds,
16 threads per process; new module 4.503 seconds. All 21 roots
audited, one axiom-free. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Authenticated all 73
preceding hashes and all 76 new hashes. Historical artifacts preserved.

Independent replay: 1,600 positive weighted ladders, 96,000 ordinary
steps; 3,078 generic affine paths, 26,676 steps; 890 complementary
profile paths, 37,340 steps. Checked 16 residue-injection cases,
1,023 exponent classifications, 4,064 modular complementary examples,
127 modular half-period flips, seven exact flips (k=2..8), and 17,387
lifting bit checks. Both old and remaining progressions have 257
modular checks each. Parameterized kernel claims do not rest on these
finite checks.

Complete new coalescences: 51 distinct pairs, with 508,948 actual N
steps and 508,795 actual P steps; 508,155 growing-prefix residue
checks; 35 exact first later residue-20 checks. Includes all qualifying
odd R in 3..513, R=512h+5 for h=0..16, and one lifted case for each
k=2..10. Reused duplicates are counted once. Largest complete case
R=13957 has 41,871-bit sources. All shortcut parities and inverse
guards are independently replayed.

Nineteen complete REMAINING pairs reach different endpoints b and
4b-1, with 37,506 N steps and 37,411 P steps. They are not certified
coalescences. Their R values are 16h+9 for h=0..16,64,256.
Across all replay sections: 734,219 shortcut edges, 423,749 inverse
edges. The separate R=9 convergence replay has 309 steps.

Larger coordinate-only pairs: k=12,R=65157 (195,471-bit sources),
k=16,R=663173 (1,989,519-bit sources). Only their exact algebraic
coordinates and 144 short ordinary tail steps were independently
replayed; their full growing prefixes were NOT numerically replayed.
The final verifier session 19946 exited 0. All jobs are terminal.

NEXT RESEARCH:
Try a scalable merger or different smaller source for R=9 mod16,
using the explicit pair b=14 mod27 and 4b-1. Do not assume that such
a merger is universal. A small exploratory affine search found a
candidate for R=25 mod64 with Q=2*8^(R-2)-5: setting
Y=9^(R-2)=512u+505 gives C^10(81Y-5)=C^15(2Y-5)=1458u+1438.
This symbolic Python candidate has not been formalized or included
in the new verification manifest; a general extension is preferable
to treating a growing list of finite residue cases as closure.
Useful later targets for arbitrary least-counterexample orbits,
universal family convergence, cap/residual estimates, nontrivial
cycles and divergence remain open. No general binary/ternary family
intersection theorem was added. The full goal remains active.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for reproduction.
No installations, credential access, agents, staging, commits or other
Git writes occurred. The user's existing changes were preserved.
HEAD remains 8dcff74; index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
ATTEMPT and README link the new note; reproduction command added.

The preceding variable block-exit handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the variable block-exit proof.

Research remains active, with no external blocker. Previous goal turn:
progress (21 ladder-exit kernel roots). Current turn: progress
(25 variable block-exit kernel roots). The positive-integer Collatz
conjecture remains unresolved. Keep 16 Lean threads per process as
authorized by the user, with heavy dependent builds sequential.

The latest note is docs/MINIMUM-LADDER-BLOCK-EXIT.md, with
lean/MinimumLadderBlockExit.lean, verify_minimum_ladder_block_exit.py,
and results/minimum-ladder-block-exit/. All 25 roots passed fresh
kernel audits. finite_surviving_period is axiom-free; the other roots
use only standard logical axioms. No native reduction axiom or
external mathematical premise enters this chain.

VARIABLE POST-LADDER COALESCENCE, KERNEL:
For odd R>=3, N=8^R-5, X=9^R, the orbit reaches X-5 at clock 5R,
then d=(3X-11)/16 five steps later. Write
3X+5=2^(k+4)*q with q positive and odd, so d=2^k*q-1.
If 3^k*q=3 mod4, its k odd shortcut steps end at 2mod4.
The kernel constructs P=2^(2R+1)-1, with 0<P<N and
C^(4R+2k+9)(P)=C^(5R+2k+8)(N)=b,
Backtrack(5,2R+k+2,b,P). The inverse word is
EE O^k EEOE O^(2R+1). It reuses the existing half_source_meeting
theorem rather than assuming a new universal coalescence premise.
The cubic size identity from the preceding module still applies.
The old R=7 mod8 and R=1 mod16 paths are k=0 and k=1, respectively;
the old R=11 mod16 path is a separate construction.

EXACT FIRST LATER RESIDUE-20 TARGET, KERNEL:
For k>=2, b=20 mod27, and every clock t with
5R<=t<5R+2k+8 avoids residue20. Thus this is the FIRST residue-20
visit after the growing prefix, with a smaller predecessor using only
five even inverse operations. The bridge residues are 22,11,19,4,2,1.
During the odd block the shortcut endpoint residues stay in
{1,2,17,26}; intervening ordinary odd steps also avoid 20. The final
three steps give the first later target. This all-k result is kernel.
It does not assert earliest coalescence by any method, absence of
earlier forward descent, or optimal inverse cost.

UNBOUNDED BINARY LIFTS, KERNEL:
For odd A with A+C=0 mod8 and every j, some r<2^j has
2^(j+3) dividing A*9^r+C. The proof uses the existing exact top-bit
identity for 9^(2^j). Applied here, for every k it gives a seed
r<2^(k+3) with 3*9^r+5=2^(k+4)*eps mod2^(k+6), where eps is 3
for even k and 1 for odd k. Adding multiples of 2^(k+3) preserves
the successful exit condition. Arbitrarily large odd R>=3 and N
follow. For every k>=2 and source bound, a kernel existential root
gives the first useful later target with exact delay 2k+8 after 5R.
This is an arbitrarily long FIRST-return delay, not just a deliberately
late chosen meeting. Seed examples k=0..6 are 7,1,13,53,37,69,261,
with periods 8,16,32,64,128,256,512. R>=3 remains required.

PRECEDING LADDER AND REMAINING CONDITION, KERNEL:
For R>=3 and R=3 mod16, P=8^(R-1)-5 satisfies 0<P<N, N=8P+35,
and C^(5R+5)(P)=C^(5R+8)(N). The lower exponent is even; the
growing-block endpoint identity works for even exponents too.
Together with earlier cases, every R=3 mod4 is excluded as a least
source. Even exponents are excluded by the basic source residue mod3.
Therefore a least source N=8^R-5, R>=3, would require R=1 mod4,
k>0, q odd, and 3^k*q=1 mod4 in the factorization above. Its post
odd block would end at a multiple of four, outside the new criterion.

These necessary conditions remain compatible with the unbounded
progression R=512h+5: the kernel proves k=6 and q=1 mod4 there.
No member is asserted to be a counterexample or to resist every other
method. R=5 is already kernel checked to converge in the older ladder
module. Neither coalescence with a smaller family member nor these
least-source exclusions prove convergence of an entire infinite family.

VERIFICATION 2026-10-21T23:02:05.077766+00:00:
34 fresh Lean 4.33.1 builds in dependency order, 61.149 seconds;
16 threads per process, 25 audited roots, one axiom-free root.
The new module took 5.424 seconds. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 71 preceding ladder-exit hashes and all 73 current hashes were
authenticated. Historical sources, notes and records are preserved.

Independent Python: 4,104 generic affine paths with 28,728 ordinary
steps; 38 bridge residue profiles; 1,236 qualifying odd blocks at
k=0..32,q=1..256, with 39,548 ordinary steps. There are 704 exact
small affine lifts and 12,285 bit checks across all lifting sections.
Eleven finite uniqueness censuses at k=0..10 cover 16,376 exponent
residues; uniqueness is finite evidence, while existence for every k
is kernel. Modular lifted families cover 4,128 cases at k=0..128,
h=0..31 without constructing huge sources.

Complete positive paths: 70 variable-block pairs and 19 preceding-ladder
pairs, with 177,367 actual N steps, 147,654 actual P steps, and 176,435
growing-prefix residue checks. Twenty-two complete paths verify the
exact first later residue-20 visit. Repeated small cases are reused.
The full path range reaches R=9861 (29,583 source bits), and includes
one lifted case at each k=0..10. Across all sections there are 80,955
inverse edges and 183,335 independently replayed shortcut edges.

Larger coordinate-only cases are k=12,R=48773 and k=16,R=925317,
with 146,319-bit and 2,775,951-bit sources. Only their algebraic
coordinates and 142 short ordinary tail steps are independently
replayed; their full ladder and pure odd paths are NOT numerically
replayed. The compatible progression has 129 modular cases, three
materialized factorizations, and a 160-step independent convergence
replay of its already kernel-certified R=5 member. All jobs are terminal.

CONTINUITY AND NEXT:
The next concrete gap is the multiple-of-four exit in the surviving
condition, starting with R=512h+5 and k=6. A further affine meeting,
a different smaller source, or genuinely new descent control is needed.
The new first-later-target families have NOT been proved to intersect
every ternary whole-window obstruction progression; a general such
intersection would require additional work. Do not silently combine
the two parameter constructions. A useful later target for every
possible least-counterexample orbit, universal family convergence,
cap/residual estimates, nontrivial cycles and divergence remain open.
The full Collatz goal stays active.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for reproduction.
No installations, credentials, agents, staging, commits or other Git
writes occurred. Existing uncommitted work was preserved. HEAD remains
8dcff74 and the index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
ATTEMPT and README link the new note and reproduction command.

The preceding ladder-exit handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the ladder-exit proof.

Research remains active, with no external blocker. Previous goal turn:
progress (16 whole-window kernel roots). Current turn: progress
(21 ladder-exit kernel roots). The positive-integer Collatz conjecture
remains unresolved. Keep the user's authorized 16 Lean threads per
process, with heavy dependent builds sequential.

The latest note is docs/MINIMUM-LADDER-EXIT.md, with
lean/MinimumLadderExit.lean, verify_minimum_ladder_exit.py, and
results/minimum-ladder-exit/. All 21 roots passed fresh kernel audits.
finite_exit_periods is axiom-free; all other printed dependencies are
standard logical axioms. No native reduction axiom or external
mathematical premise is used.

SMALLER SOURCES AFTER THE LADDER, KERNEL:
Write N=8^R-5 and X=9^R. The ordinary orbit reaches X-5 at clock 5R.
For R>=3, three residue conditions yield positive P<N and coalescence:

- R=7 mod8: P=2^(2R+1)-1, C^(4R+9)(P)=C^(5R+8)(N),
  meeting value (9X-1)/64, inverse counts (5,2R+2).
- R=11 mod16: P=2^(2R-1)-1, C^(4R+8)(P)=C^(5R+9)(N),
  meeting value (9X+31)/128, inverse counts (4,2R+2).
- R=1 mod16: P=2^(2R+1)-1, C^(4R+11)(P)=C^(5R+10)(N),
  meeting value (27X+13)/128, inverse counts (5,2R+3).

The kernel therefore excludes N as a least counterexample in four
of the eight ODD EXPONENT classes modulo 16. This is not a density
claim about arbitrary positive integers. Universal convergence of
these N or their Mersenne predecessors P remains unproved.

The proof combines C^(2j)(2^j-1)=3^j-1 with three short affine paths.
The inverse words before the pure odd block are EEEEOE, EEOOEOE,
and EEOEEOE. Exact cubic size identities give
(P+1)^3=8*(N+5)^2 in the first/third cases, and
8*(P+1)^3=(N+5)^2 in the second. Thus P has asymptotically two
thirds as many binary digits as N. No optimal inverse cost is claimed.
The meeting values are NOT residue-20 targets: their residues are
8mod9, 11mod27, and 2mod27, respectively. Ordinary coalescence alone
suffices for the least-counterexample contradiction.

AN ARBITRARILY LONG OBSTRUCTION FOLLOWED BY ESCAPE, KERNEL:
In the preceding family K=2*(s+3), R=1+2*3^K*(h+1), restrict
h=4a+2. Then R=7 mod8, so the first new coalescence applies.
Every target b_i with i<R still has exact inverse minimum N at
even budget i+s, and the prefix minimum through clock 5R is N.
Nevertheless, eight ordinary steps after that prefix a smaller P
joins with only FIVE even inverse operations (and 2R+2 odd ones).
For every s, visit-count bound L, and source bound B, the kernel
constructs one such source with R-1>L and N>B. The prefix obstruction
and the later escape hold simultaneously for the same source.
The root unbounded_delayed_escape also concludes N is not least.
No escape for every h in the preceding family has been proved.

VERIFICATION 2026-10-21T22:29:19.052857+00:00:
33 fresh Lean 4.33.1 builds in dependency order, 59.917 seconds;
16 threads per process, 21 audited roots, one axiom-free root.
The new module took 2.118 seconds. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 69 preceding whole-window hashes and all 71 current hashes
were authenticated. Historical sources, notes and records are preserved.

Independent Python: 3,081 generic affine path-pair queries at u=0..1023
and three larger u values, with 54,431 ordinary steps. All 4,096 residue
exponents R=0..4095 passed; the size failure at R=1 is explicitly checked.
There are 72 complete positive coalescing pairs: all covered odd R in
3..257, six larger exponents, and two whole-window examples. These use
159,497 actual N steps, 127,761 actual P steps, and 158,870 checks of
the growing prefix's residue-20 positions. Across all sections there
are 84,604 inverse edges and 200,454 shortcut edges, including the
two larger short-tail checks below.

The complete whole-window examples have R=4375 and R=10207, with
13,125-bit and 30,621-bit sources. Their P values have 8,751 and
20,415 bits, meeting at clocks (N,P)=(21883,17509) and (51043,40837).
In these two FINITE examples, and at R=17, no forward state falls
below N before the meeting. That extra prefix-minimum observation
is Python evidence, not a new universal kernel theorem.
Two larger examples R=39367 and R=354295 are materialized only for
algebraic coordinates and 30 short ordinary tail steps; their entire
paths are NOT numerically replayed. Source sizes are 118,101 and
1,062,885 bits. A separate 4,128-case modular census covers s=0..128,
a=0..31 without constructing the huge sources. All jobs are terminal.

CONTINUITY AND NEXT:
The remaining odd exponent classes in this new modulo-16 cover are
3,5,9,13. A bounded exploratory search of dyadic affine constants
found additional candidate Mersenne paths in subsets of those classes,
but no universal cover. Its failures at the imposed search depth are
not impossibility results. A useful next direction is to generalize
the short affine meetings or prove a coalescence/descent criterion
covering the remaining exponents and eventually arbitrary least
counterexamples. The result already shows that whole-prefix inverse
obstructions need not persist beyond the prefix.
Universal family convergence, a useful later residue-20 theorem for
every possible least source, cap/residual estimates, nontrivial cycles
and divergence remain open. The full Collatz goal remains active.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for reproduction.
No installations, credentials, agents, staging, commits or other Git
writes occurred. The existing uncommitted work was preserved. HEAD
remained 8dcff74 and the index SHA256 remained
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
ATTEMPT and README link the new note and reproduction command.

The preceding whole-window handoff (2026-10-22):

Last updated: 2026-10-22 local time, after the whole-ladder-window proof.

Research remains active, with no external blocker. Previous goal turn:
progress (26 inverse-locality kernel roots). Current turn: progress
(16 whole-window kernel roots). The positive-integer Collatz conjecture
remains unresolved. The user authorized increasing Lean threads for
speed; use 16 threads per process, with heavy dependent builds sequential.

The latest note is docs/MINIMUM-LADDER-WINDOW.md, with
lean/MinimumLadderWindow.lean, verify_minimum_ladder_window.py, and
results/minimum-ladder-window/. All 16 roots passed fresh kernel audits;
finite_small_paths is axiom-free. The other roots use only standard
logical axioms. No native reduction axiom or external mathematical
premise enters this chain.

SIMULTANEOUS WHOLE-PREFIX OBSTRUCTION, KERNEL:
For any fixed extra even budget s, let K=2*(s+3),
R=1+2*3^K*(h+1), N=8^R-5, and h>=0. For every 0<=i<R,
x_i=9^i*8^(R-i)-5 and b_i=(3*x_i+1)/2 have exact inverse minimum
M_(i+s)(b_i)=N. The attaining path has i even and 2i+1 odd inverse
operations, with ordinary clock 5i+2. The lower bound covers every
legal inverse word at that even budget, without an odd-count cutoff.
The kernel also proves the prefix minimum is N through clock 5R,
with exactly the b_i for 1<=i<R as residue-20 visits before that clock.
The index-zero target is included in the inverse theorem but is not
a residue-20 visit. For every s, visit-count bound L and source bound B,
one R satisfies R-1>L and N>B with all these bounds simultaneously.
Thus a fixed extra budget can fail at every visit in one arbitrarily
long growing prefix, even though the allowed total budget grows with i.

SHARP COMPANION AND POSITIVE REFERENCE, KERNEL:
For Shadow(e,o,m), m>=5, o<=2e+1, and
m<=(7 if o even, 5 if o odd)*2^(e-floor(o/2)). At the odd-count
frontier e=i+f,o=2i+1 this gives 5<=m<=5*2^f, with equality attained
by O(EOO)^i E^f. Shadow cannot have m=8. For
a=2^(f+3)-m, every inverse predecessor p has p>=3 and
3^o<=2^(f+e+o). A hypothetical smaller multiplier forces p<=6;
those positive orbits enter {1,2,4} by clock eight. The remaining
small possibilities are covered by an axiom-free finite certificate.
Excluding m=8 is essential: f=1,m=8,a=8 admits p=3 with scaled
multiplier 8/9, but that companion is impossible.

Every inverse word splits at any specified odd count. Splitting at
2i+1 gives x+m=2^f*8^R, with f<=s. From 8^R=8+3^K*q,
x=a+3^K*(2^f*q). The preceding locality theorem transfers the entire
remaining suffix to a because 2*((s-f)+(f+3))=2*(s+3)<=K.
The reference multiplier bound then gives P>=3+3^K*q=N. Words
not passing that odd-count frontier were already bounded below by N.
The general theorem applies whenever the displayed congruence holds;
the explicit family follows from the preceding kernel period theorem.

VERIFICATION 2026-10-21T22:07:30.843749+00:00:
32 fresh Lean 4.33.1 builds in dependency order, 56.137 seconds;
16 threads per process, 16 audited roots, one axiom-free root.
The new module took 2.383 seconds. Compiler commit remains
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All 66 preceding inverse-locality hashes and all 69 current hashes
were authenticated. The helper verifier is explicitly included in the
new manifest; preceding sources, notes and records remain unchanged.

Independent Python: 113,014 complete companion states at even budget 22,
maximum odd count 45; 1,089 attaining words at i,f=0..32, with 70,785
inverse and 70,785 independent forward steps. All 672 finite-certificate
tuples passed, 12 nonvacuous, plus 56 ordinary steps. Complete positive
reference box s=0..10: 20,096 trees, 100,008 states. Selected lifted trees:
498 trees, 8,028 states, 69,789 ordinary replay steps. Word splitting:
1,855 complete inverse words for targets 1..64 at even budget 5,
5,458 splits, with both segments independently replayed.

Four actual full prefixes have R=1459,2917,13123,118099; the last
uses a 354,297-bit source and 590,495 ordinary steps. Two larger sources
with R=1062883 and R=9565939 were materialized but only their first 8
and 3 blocks were replayed. Combined: 678,045 ordinary steps/residue
checks, 406,827 shortcut steps, 135,603 residue-20 visits. Complete inverse
optimization is only at the listed early indices: 51 queries, 15,407
states, 309,256 ordinary forward steps. Universal all-visit optimization
is kernel proved, not inferred from those finite queries. A separate
4,128-case modular census covers s=0..128,h=0..31 without constructing
those sources. No eventual convergence of the materialized sources
or of the whole family is claimed. All jobs are terminal.

CONTINUITY AND NEXT:
The next mathematical step must address visits AFTER clock 5R or an
extra budget that grows with the source or visit. The proposal that
a fixed extra budget succeeds somewhere WITHIN the growing ladder
prefix is now disproved, even with arbitrarily many available visits.
A fixed extra budget succeeding at a suitable later visit in the
entire orbit is still open. No single source is shown to have infinitely
many obstructed visits. Useful least-counterexample occurrence,
cap/residual estimates, nontrivial cycles and divergence remain open.

Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for reproduction.
The verifier defaults to min(16, available CPUs); --threads is configurable.
No installations, credentials, agents, staging, commits or other Git
writes occurred in this continuation. HEAD remained 8dcff74, and index
SHA256 remained ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
Existing uncommitted work was preserved. ATTEMPT and README link the
new note and reproduction command. The Collatz goal remains active.

The preceding inverse-locality handoff (2026-10-21):

Last updated: 2026-10-21 local time, after the inverse-locality proof.

The user resumed the active goal. Research is active, with no external
blocker. Previous goal turn: progress (the negative-cycle detour and its
verification). Current turn: progress (26 new audited kernel roots).
The positive-integer Collatz conjecture remains unresolved.

The latest note is docs/MINIMUM-INVERSE-LOCALITY.md, with
lean/MinimumInverseLocality.lean, verify_minimum_inverse_locality.py,
and results/minimum-inverse-locality/. No native reduction axiom or
external mathematical premise enters the new chain. The finite anchor
is axiom-free; the remaining roots use only standard logical axioms.

GENERAL INVERSE LOCALITY, KERNEL:
For Backtrack(e,o,b,p), b>0, the kernel proves p>0 and
3^o*(p+1)<=2^(e+o)*(b+1). If b+1<=2^d, then o<2*(e+d).
For K>=2*(r+d), every path with e<=r from B=b+3^K*q transfers
to a path from b with the same counts and
P=p+2^(e+o)*3^(K-o)*q, o<K. The induction derives the reference
odd-count bound before each new guard; it does not assume an odd-count
cutoff for B. Conversely, every reference path with o<=K lifts.
Thus the full bounded inverse tree is preserved, not just a selected word.
The transfer assumes b>0 and q>=0, and applies to a finite even budget.

UNRESTRICTED ANCHOR, KERNEL:
The only positive ordinary predecessor of 857 at most 507 is 507,
at clock 7. The finite certificate checks avoidance through 200 steps
and entry into the closed cycle {1,2,4} for sources 1..506, and for
C^8(507). Clocks 0..7 for 507 are checked separately. A kernel checker
soundness theorem extends avoidance to all times. Every inverse word
to 857 therefore has p>=507 and multiplier 2^(e+o)/3^o>=16/27.
The word OEOO attains 507 with one even and three odd operations.
This is a predecessor minimum at 857, not a global forward minimum:
507 reaches one at clock 35 and is not an exceptional source.

UNBOUNDED FIRST-TARGET OBSTRUCTION, KERNEL:
For r>=1, K=2*(r+10), n=507+16*3^(K-3)*q, b=857+3^K*q,
the exact minimum over ALL inverse words with e<=r is n. The first
ordinary visit to 20mod27 is b at clock 7, with prefix minimum n.
The source is unbounded as q varies. Each larger budget has its own
progression; no single unbounded source is shown to resist every budget.

RETURN-LADDER CONSEQUENCE, KERNEL:
For R=3+2*3^K*h, N=8^R-5, the first target b_1 is in the same
progression: 8^(2*3^K*h)=1+3^K*z gives q=864*z. The kernel
proves R>=3, R odd, h<N, C^7(N)=b_1, and M_r(b_1)=N.
In particular, for every extra budget s and source bound B there is
an odd R with N>B and M_(1+s)(b_1)=N. Hence a uniform extra budget
cannot work at EVERY target or uniformly at the FIRST target even
after excluding finitely many sources. This does NOT rule out a fixed
extra budget succeeding at SOME LATER visit for each source. That
quantifier, useful least-orbit occurrence, cap/residual control, and
both nontrivial cycles and divergence remain open.

VERIFICATION 2026-10-21T21:38:40.089008Z:
31 fresh Lean 4.33.1 builds in dependency order, 55.557 seconds;
26 audited roots, one axiom-free root, 66 current hashes authenticated.
All 64 preceding negative-cycle hashes authenticated before building.
The user explicitly authorized more Lean threads for speed during
this turn. The final verifier used 16 threads per process on 16 CPUs;
dependent module builds remained sequential. The new module took
13.897 seconds. Compiler commit unchanged:
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

Independent Python: 506 smaller anchor starts, 26666 ordinary steps,
plus 35 steps from 507. The longest smaller first arrival is 143 at
327. Complete anchor trees at budgets 0..20 contain 88733 counted
states across queries. General locality: 896 reference trees at
targets 1..128, budgets 0..6; 1792 lifted trees, 30882 states and
226832 ordinary forward replay steps. Family optimization: 64 complete
trees at r1..16 and q0,1,2,17, 70076 states and 1716424 forward steps.
Actual first-target prefixes: 2048 at r1..64,q0..31, 14336 steps.
Thirty materialized period/coordinate checks use 210 prefix steps;
4160 actual ladder-family checks (r1..64,h0..64) are modular only.
Apart from h=0, the enormous ladder sources were not materialized.
At r1,h1, R=62762119221 and N has188286357663 binary digits.
No continuous convergence interval or universal family convergence
is claimed. All checks are terminal.

CONTINUITY AND NEXT:
The worktree initially had clean HEAD8dcff74. The prior negative-cycle
manifest and its source files were authoritative and remained unchanged.
Exploratory complete forward caches at R1,3,5,7 confirmed no source
below N reaches any listed ladder target. Only the R3 first target857
was incorporated into the new kernel anchor; the larger caches remain
exploratory observations and are not extra formal theorems.
The mathematical next step must address a useful later visit or
source-dependent inverse complexity, rather than another fixed-budget
first-target assertion. No complete proof or counterexample was found.

Lean 4.33.1 was again absent from /tmp and restored from its official
release using the existing network authorization; no credentials were
read. Use --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16 for the
new verifier. Its default thread count is min(16, available CPUs),
and --threads remains configurable. No agents, staging, commits, or
other Git writes occurred. Index SHA256 remains
ba48d1a9910830b85695359bdd886167848b039191aa8278e056c223369be3ad.
ATTEMPT and README link the new note and reproduction command.

The preceding negative-cycle handoff (2026-10-21):

That run ended with a requested pause; the user resumed research in
the current turn. The positive-integer Collatz conjecture remains unresolved.

The latest note is docs/MINIMUM-NEGATIVE-CYCLE.md, with
lean/MinimumNegativeCycle.lean, verify_minimum_negative_cycle.py, and
results/minimum-negative-cycle/. There are 26 new audited kernel roots,
including three axiom-free finite roots. No native reduction axiom or
external mathematical premise is used.

POSITIVE CYCLE LIFTS, KERNEL:
The existing negative magnitude-17 cycle has forward shortcut word
OOOOEOOOEEE, with four even and seven odd inputs. Its inverse word is
W=EEEOOOEOOOO. For q>0, kernel composition gives
Backtrack(4k,7k,2187^k*q-17,2048^k*q-17), with ordinary clock18k.
Positivity of the displayed source is asserted for k>=1; the k=0
relation uses natural subtraction and need not have positive endpoints.
No negative-cycle assertion is interpreted as a positive counterexample.

SMALLER COALESCING SOURCES, KERNEL:
For odd n and positive q with2187^k*q=3n+18, prefixing E gives
Backtrack(4k+1,7k,C^2(n),P), P=2048^k*q-17, and
C^(18k+1)(P)=C^2(n). For k>=17,0<P<n. For k<17, this specified
pattern gives P>n. The threshold17 is NOT optimality over all words.
Thus a least counterexample cannot have3^118 dividing n+6.
For k=17(a+1), kernel3^a*(P+17)<=n+6 and3^a*P<n give arbitrarily
large improvement factors across changing sources and divisibility
conditions. They do not give arbitrarily small parents of one fixed n.

RETURN-LADDER APPLICATION, KERNEL:
Elementary cube and odd-power induction prove3^(s+2)|8^(3^s)+1
and the odd-multiple extension. For R=3^116*(2h+1), N=8^R-5,
3^118|N+6. There exists one p with0<p<N andC^307(p)=C^2(N),
and for every0<=i<R:
Backtrack(i+69,2i+119,b_i,p), C^(5i+307)(p)=b_i.
The kernel proves h<N and excludes N as a least counterexample.
The actual residue-20 visits remain1<=i<R; b0 is not a residue-20 visit.
R is divisible3, so this progression is disjoint from the preceding
R=85mod162 escape family. Its sources are723mod729, not273mod729.
The previous WRITTEN sharpness result gives M_(i+3)(b_i)=N here;
the new strict upper bound M_(i+69)(b_i)<N is kernel. The optimal
budget between them is unknown. No universal family convergence follows.

ENORMOUS SYMBOLIC SOURCES / CONCRETE WITNESSES:
The smallest new return-ladder source has3^117 binary digits, over10^55
bits. None was materialized or numerically iterated. Python checks its
divisibility via modular exponentiation; the complete paths are symbolic
kernel theorems. Separately, the general residue-class example
n=3^118-6 (188bits), p=2^187-17 (187bits) has kernel coalescence at307
and2, and kernel arrivals at1 at1247 and1552. Python independently
checks first-arrival minimality. These examples are NOT members of the
enormous return-ladder progression.

VERIFICATION2026-10-21T10:38:44.159616Z:
30 fresh sequential Lean4.33.1 builds,59.974sec;26 audited roots;
64 current hashes authenticated, with all62 preceding inverse-escape
hashes authenticated before building. Compiler Linux x86_64, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All checks terminal.
Independent replay:1024 single-block positive lifts (18432 ordinary
steps);2048 full detours for k1..64 and odd q1..63 (1204224 ordinary
steps),1536 smaller;15 larger detours through k272 (28503 ordinary
steps),all smaller. There are762878 inverse edges over all these paths.
Threshold checks cover1..17;129 repeated-gain and387 shifted/factor
comparisons are arithmetic. Ten ternary lifts s0..9 are materialized;
257 s0..256 lifts and1025 progression h0..1024 checks are modular.
Ninety small odd-multiple congruences and2799 arrival steps also pass.
No full inverse-tree optimization or continuous convergence interval
is claimed. Finite replay remains separate from kernel verification.

CONTINUITY / ENVIRONMENT:
The old top memory lagged the committed inverse-escape milestone.
docs/MINIMUM-INVERSE-ESCAPE.md and its62-hash manifest were authoritative:
27 roots already proved the three-extra-even escape atR=85mod162 and
excluded273mod729; the full sharpness classification remained written.
All those source files and historical results were preserved.
The current workspace is Linux, bash, at
/home/jeannaude/Documents/collatz-conjecture--expansion.
Lean4.33.1 was absent; with approved network access its official archive
was downloaded and extracted to/tmp/lean-4.33.1-linux. Use the verifier's
--lean /tmp/lean-4.33.1-linux/bin/lean option while that temporary compiler
exists. The repository pin is unchanged; no credentials were accessed.
Initial prototype slowdowns were unnecessary omega processing of a huge
congruence together with parity. Direct arithmetic identities fixed them.
The final proofs keep enormous exponents and symbolic iterates unexpanded
during elaboration; finite witness reduction still runs in the kernel.

ON RESUMPTION:
The current construction does not settle whether a fixed extra inverse
budget suffices for every return-ladder source. Potential next questions
are useful detours at intermediate budgets, or quantitative occurrence
on a hypothetical least-source orbit. The cap/residual and cycle gaps
remain. Do not infer a universal inverse-budget theorem from the negative
seventeen cycle or from finite searches. No complete proof or counterexample.

No agents, staging, or commits were used. HEAD remains0dad331; index
SHA256 remains9c66aaab2c3dd5a0a92853aa8d98fcb985ea5c1c4b6e9cd1df18b105bf11aae7.
The pre-existing untracked Period2Certs.lean and Period3Certs.lean were
left untouched. ATTEMPT and README link the new result and reproduction.

The preceding return-ladder handoff (2026-10-15):

Thirty-one new kernel roots determine bounded-even inverse minima at
repeated actual visits to 20 modulo 27, and prove arbitrarily long finite
windows where every fixed inverse budget is ineffective. The broader
ancestry, cap/residual and cycle gaps remain. Full Collatz is unresolved.

The latest note is docs/MINIMUM-RETURN-LADDER.md, with
lean/MinimumReturnLadder.lean, verify_minimum_return_ladder.py, and
results/minimum-return-ladder/.

ACTUAL RETURN PREFIXES, KERNEL:
For odd R>=3, n_R=8^R-5, x_i=9^i*8^(R-i)-5 for 0<=i<=R,
b_i=(3x_i+1)/2=3^(2i+1)*2^(3(R-i)-1)-7 for 0<=i<R.
The shortcut word (OOE)^R gives C^(5i)(n_R)=x_i and prefixMinimum
at clock 5R equal to n_R. Every clock t<5R has residue 20 modulo 27
iff t=5i+2 with 1<=i<R. There are R-1 visits at 7,12,17,...,5R-3.
The underlying block has affine fixed point -5; finite positive lifts
do not give an ordinary positive realization of the infinite word.

EXACT INVERSE MINIMUM, KERNEL:
Backtrack(e,o,b,p) is the inductive relation of all legal inverse
shortcut words, with e even and o odd operations. Kernel ordinary
semantics: C^(e+2o)(p)=b. For 0<=r<=i<R and odd R:
min_{e<=r,o,Backtrack(e,o,b_i,p)} p = x_(i-r).
The universal lower bound and attaining path are both kernel, with
no unformalized finite-word optimization hidden in the statement.
The attaining word has r even, 2r+1 odd inputs; ordinary clock 5r+2.
This minimum equals n_R iff r=i; it exceeds n_R if r<i. Any inverse
path to p<=n_R requires at least i even inputs, regardless of its budget.
For every fixed r,L,B, the kernel chooses odd R=2(r+L+B+3)+1 and n_R>B,
so visits i=r+1..r+L have every r-budget predecessor strictly above n_R.
At r=1, the first visit recovers n_R; all remaining visits are above it.
For r>=2, earlier i<r visits are outside this theorem. Budgets r>i remain
unproved; do not interpret these statements as unrestricted ancestry.

COMPANION MECHANISM, KERNEL:
Start inverse positive p=b_i with negative magnitude m=7. Even inverse
doubles p,m; odd inverse changes p to (2p-1)/3, m to (2m+1)/3. For e<=i:
5<=m<=7*2^e, o<=2e+1, d=2e+1-o,
2^d(m-1)<=4*3^d and 3^o(p+m)=2^(e+o)(b_i+7).
The ternary factor forces companion integrality until o=2i+1. At that
boundary, e=i,m=5,p=n_R; n_R divisible by 3 blocks another odd inverse.
After cancellation, 2^d(p+m)=3^d(x_(i-e)+5).
If d=0, m=5 gives exact equality. Otherwise 3^d/2^d>=3/2 and the kernel
buffer 14*2^e<=8^(e+1)+10 controls the possible negative offset.
The companion uses Nat arithmetic on magnitudes; no negative orbit premise.

AXIOM-FREE EXAMPLES:
R=3: n=507,x1=571,x2=643,b1=857,b2=965; first visits at clocks 7 and 12,
prefix minimum at 15 is 507. At b2, budgets 0,1,2 give minima 643,571,507.
R=5: n=32763,hit4=78725. Arrivals at 1 from 507,857,965,32763 are
35,28,23,160; first-arrival minimality is separately Python checked.
No convergence theorem for every odd R is proved.

VERIFICATION 2026-10-14T22:41:48.423658Z:
28 fresh sequential Lean 4.33.1 builds, 15.927 seconds, 31 roots, 60 hashes;
all 58 prior first-target hashes authenticated. No native finite axiom.
Independent complete sources/targets 1..65536, budgets 0..4:
327680 minima comparisons, 589710 shortcut / 917276 ordinary steps,
1568932 forward minimum visits. Strict improvements by budgets 1,2,3,4:
10922,3033,1130,918. Forward paths stop before the fifth even input;
these are bounded-word minima, not global minima or a convergence interval.
35 actual family prefixes: all odd R=3..65 plus 129,257,1025;
12495 ordinary steps, 7497 shortcut steps, 12530 residue checks,
2534 block endpoints, 2464 target visits, 4928 coordinate checks.
8796 inverse minima; attaining paths use 187032 ordinary / 110460 shortcut steps.
All inverse budgets r<=i for R<=17; larger queries are scoped samples.
Complete companion DFS for all odd R=3..17, all i, all r<=i: 516 queries,
141333 nodes. Four kernel arrival witnesses replayed over 246 ordinary steps.

WRITTEN / NEXT:
The formulas give v3(b_i+7)=2i+1 and v3(4b_i+1)=3. These are written
valuation observations, separately replayed; they explain the boundary of
an external Sodelin valuation-13 ancestor selector, reviewed but not adopted.
GettysburgResearch's catalog was also reviewed only for finite-prefix scope.
No external proof or finite convergence bound enters the new kernel chain.
Next: investigate r>i or quantify useful inverse complexity along an unknown
least orbit; visiting 20 modulo 27 alone with fixed effort is not enough.
All sources vary with R; no divergent source or cycle has been found.
The goal remains active, without an external blocker. No agents or installs.
The user committed preceding work during this turn; preserve HEAD/index.

The preceding first-target milestone (2026-10-15):

Twenty-three new kernel roots constrain odd-block
exits near a least counterexample and prove an exact first-target
obstruction family. A written generalization shows that a hypothetical
least counterexample's first visit to 20 modulo 27 has itself as the
smallest zero/one-even predecessor. A useful later visit is unproved.
The positive-integer Collatz conjecture remains unresolved.

The preceding note is docs/MINIMUM-FIRST-TARGET.md, with
lean/MinimumFirstTarget.lean, verify_minimum_first_target.py, and
results/minimum-first-target/.

HALF-SOURCE COALESCENCE, KERNEL:
For q>0 and 3^k*q=4v+3, put p=2^k*q-1 and n=2p+1.
C^(2k+3)(p)=3v+2=C^(2k+4)(n). The identity holds at k=0;
the least-source application retains k>=1, making p positive.
If n=C^t(A) for a least counterexample A, then n>=2A+1.
Hence a value y<=2A with y=2^K*q-1, q odd, K>=2 must have
3^K*q=3 mod4: exactly one extra even shortcut step at the exit.
No K>=2 assertion for every y in the band, and no return theorem.
Different source clocks coalesce; no equal-time/weight claim.

EXACT FIRST-TARGET FAMILY, KERNEL:
K=6h+3, n_h=5*2^K-1, v_h=(5*3^K+1)/4,
b_h=3v_h-1, T_h=2K+3. Kernel: C^T_h(n_h)=b_h,
prefix minimum n_h, exact shortcut count K+1 odd among K+2 steps,
b_h=20mod27 and every earlier ordinary state avoids that class.
Every all-odd affine predecessor and every predecessor with one
extra even input is >=n_h; the displayed path attains n_h.
Complete zero/one-even word enumeration is a written assembly.
Kernel (h+1)(n_h+1)<=b_h+1 and h<n_h show unbounded relative
first-target heights. Sources vary; no divergent orbit is supplied.

LEAST SOURCE'S FIRST VISIT, WRITTEN GENERALIZATION:
For n+1=2^K*q, q odd, assume K>=2, 3^K*q=3mod4,
n!=2mod3 and n!=4mod9. Its first20mod27 visit is
b=(3^(K+1)*q-1)/4 at ordinary clock2K+3, with prefix minimum n.
The first completed odd pair avoids20mod27 precisely because
n!=4mod9; pairs indexed>=2 are8mod9, intervening odd images1mod3.
The remaining bridge states are1mod3. Since b20mod27, its pure
inverse chain is b,c=(3^K*q-1)/2. Doubling b adds no odd parent;
doubling c gives3^K*q-1 and its full odd-inverse chain ends at n,
because3 does not divide q. All other candidates are larger.
Thus the minimum over ALL zero/one-even inverse words is exactly n.
Existing least_mod4, least_not_two_mod3, least_not_four_mod_nine,
and the new least_initial_exit_constraint imply these hypotheses
for every hypothetical least A. Maximal factorization and the
general first-visit/minimum assembly are WRITTEN, not new kernel
roots. No sufficient-set occurrence theorem is needed for this
first visit. It cannot give a strict smaller-source contradiction.

AXIOM-FREE KERNEL EXAMPLES:
h0:39 first reaches101 atclock9; h1:2559 first reaches73811 at21.
All earlier residues are kernel checked. Arrivals at1 from
39,101,2559,73811 are34,25,115,94, respectively. Python separately
checks first-arrival minimality. No convergence theorem for all h.

VERIFICATION2026-10-14T22:17:16.827471Z:
27 fresh sequential Lean4.33.1 builds,14.570sec,23audited roots,
58hashes; all58 prior mixed-ancestry manifest entries authenticated.
No native finite axiom or new external proof premise.
Independent half-source rectangle:k0..64,q1..256,4160filteredpairs,
561600ordinary steps,8320paired/direct comparisons;16383integer
floor compatibility checks do not instantiate a least counterexample.
Familyh0..256:257prefixes,397065ordinary/198661shortcut steps,
199175inverse candidates,397322prefix residue checks.
Complete first-hit censusn1..65536:670655ordinary steps,5204distinct
targets,36257inverse candidates. Outcomes60949below-source,4551equal,
36reach1 first,0above-source,0unfinished atclock4096.
All65536profile/equality comparisons match; all4551profile paths
match the written clock, endpoint and minimum. The converse profile
characterization is FINITE ONLY. Four arrival witnesses replay268steps.
No unknown global minimum is assigned by these prefix censuses.

NEXT / EXTERNAL CONTEXT:
An ancestry contradiction must use a later useful visit, more inverse
even steps, or further constraints. Near-source exit inheritance alone
does not force enough returns. The old residual/cap and cycle gaps
remain. The Monks et al. primary sufficient-set paper and a public
Sodelin near-return note were reviewed for scope, with links in the
new note. Neither enters the new kernel proof dependencies.
No installations, credentials, agents, staging, or commits were used.
The goal remains active, with no external blocker.

The preceding mixed-ancestry milestone (2026-10-14):

Thirty new kernel roots construct actual one-extra-even predecessor paths whose improvement over the all-odd height barrier is unbounded. Constituent kernel arithmetic gives a reduced-residue criterion; its full optimization and target density 1/6 are written. The required occurrence below a least counterexample remains unproved. Full Collatz is unresolved.

The preceding note is docs/MINIMUM-MIXED-ANCESTRY.md, with
lean/MinimumMixedAncestry.lean, verify_minimum_mixed_ancestry.py, and
results/minimum-mixed-ancestry/.

GENERAL MIXED WORDS, KERNEL:
For a positive valuation word w with length l, sum s and numerator B,
2^s*b=3^l*p+B at odd b is an actual positive odd predecessor path,
using the existing MarkedPreimageAudit inversion. If b=C^t(A) for a
least counterexample A, then p>=A and 2^s*b>=3^l*A+B.
Global minimum splitting retains the finite prefix minimum explicitly.

ONE EXTRA EVEN INPUT, KERNEL:
If k>=2, j>=0, q,v>0 and 3^k*q+1=2^(j+1)*v, put
p=2^k*q-1, b=3^j*v-1. The path has k odd shortcut steps, one
EVEN-input shortcut step, then j odd shortcut steps. Kernel:
C^(2k+1+2j)(p)=b and the minimum of this ordinary prefix is p;
shortcut endpoint b and odd count k+j are checked separately.
m(p)=min(p,m(b)); a global root b makes p a root.
If any ordinary iterate of a least A equals b, A+1<=2^k*q.
The special path 8r+3 -> 9r+4 in five ordinary steps excludes
A=4 mod9 for a least counterexample (kernel).

UNBOUNDED IMPROVEMENT, KERNEL:
Binary lifting constructs a_j<2^j with 15*9^a_j+1 divisible by
2^(j+3). Set K_j=2(a_j+2^j)+1, v_j=(5*3^K_j+1)/2^(j+3),
p_j=5*2^K_j-1, b_j=3^(j+2)*v_j-1, T_j=2K_j+1+2(j+2).
Kernel gives the exact path, prefix minimum, exactly one even input,
p_j+2<2^(K_j+3), j<p_j, and
2^(j+3)(b_j+1)=3^(j+2)(5*3^K_j+1).
If 10h<=j, then h*3^(K_j+3)<=b_j+1. For j>=10 every all-odd
predecessor of b_j is at least p_j+2, whereas the mixed predecessor
is p_j. The existential theorem includes arbitrary source bound and
arbitrary improvement factor. The source varies; no divergent orbit.
WRITTEN: K_j odd implies 3|p_j. Its inverse basin is only a doubling
ray, so this family does not itself give positive branch density.

EXACT FINITE OPTIMIZATION AND WRITTEN DENSITY:
Let s=v3(b+1) and c=2^s*(b+1)/3^s-1, the smallest all-odd
predecessor. Before c, doubling an all-odd inverse point gives no odd
inverse parent (kernel arithmetic). At c write 2c+1=3^k*q with
3 not dividing q. Kernel: 2^k*q-1<c iff k>=2 iff c=4 mod9.
Assembling these statements into the minimum over all words with at
most one even input is WRITTEN, not a formal set-minimum definition.
The improved target set has natural density1/6 by a written disjoint
progression sum: b+1=3^s*q, q=5*2^(-s) mod9. The tail is inside
3^S|(b+1), so finite progression densities pass to the limit.
This is NOT the frequency on an individual orbit.

FINITE KERNEL WITNESSES (AXIOM-FREE):
j=0: p39 -> b152 at ordinary clock11, prefix minimum39; arrivals at
one from39 and152 at34 and23. j=4: K53,
p45035996273704959 -> b551968206708544316592375437 at119,
prefix minimum p, p+2<2^56 and3^56<=b+1. Arrivals at1 are751 and632.
Python also checks first-arrival minimality for all four sources.
All these actual global minima are1, not unknown nontrivial roots.

VERIFICATION2026-10-14T21:57:16.224949Z:
26 fresh sequential Lean4.33.1 builds,12.980sec,30 audited roots,
58 hashes; prerequisite manifests authenticate50,28,14 entries with
possible overlap. No native_decide or new external proof premise.
Independent inverse targets1..65536:98298 branches,10922 strict
improvements,76434 ordinary steps replaying those strict branches.
Independent forward sources1..65536 stop BEFORE a second even input:
196606 shortcut steps,202053 in-range endpoint visits. All131072
minimum comparisons agree, plus65536 residue criteria and17 exact
progression counts. These are bounded-word minima, not global minima
or a convergence interval. Modular lifting through128,13 complete
small exponent periods(8191 residues),11 family prefixes throughindex10
(12767 ordinary steps);7 exceed the all-odd height threshold.
Large-index modular/arithmetic checks do not construct huge sources.
Four kernel arrivals replayed1440 ordinary steps. All jobs terminal.

LIMITATIONS / NEXT:
A written bounded-extra-even envelope remains: if n+1<=2^d,d>=1,
any shortcut endpoint after at most r even inputs has endpoint+1
<=3^[2^r(d-1)+1]. Thus fixed r cannot reach arbitrary heights from a
fixed small source. The new unbounded improvement varies the source.
The actual least-orbit gap is: force an encountered target whose
mixed predecessor lies BELOW A, rather than merely below that target.
The Monks et al. primary paper arxiv1204.3904v2 supplies congruence
reachability and a strongly sufficient20mod27 class inside the improved
set, but no required relative height. Reviewed only for scope, not used
as a new kernel premise. Earlier cap/residual and cycle gaps persist.
No installation, credentials, agents, staging, commits, or Git writes.
The goal remains active, without an external blocker.

The preceding minimum-root predecessor milestone:

The latest note is docs/MINIMUM-ROOT-PREDECESSORS.md, with
lean/MinimumRootPredecessors.lean and verify_minimum_root_predecessors.py.

ACTUAL INVERSE TRANSPORT, KERNEL:
m(n)=min(m_t(n),m(C^t n)).
For k>=0,q>=1, a=2^k*q-1,b=3^k*q-1:
  m_(2k+t)(a)=min(a,m_t(b)); m(a)=min(a,m(b)).
If b is a global minimum root, a is too. A growing finite block alone
does NOT establish this global-root hypothesis.

For a root b=3q+2, p=2q+1 is a root with sigma(p)=b. Every positive
root a with sigma(a)=b has p<=a.
If consecutive roots a_j,a_(j+1)=b of a nonrepeating orbit have p<a_j,
the kernel proves p is absent from the ENTIRE original orbit.
This is an additional branch, not an exponential branching theorem.
Kernel: 3|p iff b=5mod9. Such p has only doubling predecessors
(existing shortcut inverse-basin kernel result and the same ordinary
one-step calculation), hence zero natural density by a written count.
Forcing these roots alone need not add positive basin density.

LEAST COUNTEREXAMPLE RESTRICTIONS:
If A is least and C^s(p)=C^t(A) for positivep, then A<=p (kernel).
Thus if C^t(A)=3^j*q-1, j,q>=1, then A+1<=2^j*q.
For A's attained-root sequence a_k:
  NOT 3^(k+1)|(a_k+1), allk>=0.
If k>=1 and3^k|(a_k+1), kernel suppliesq>0 with
  A=2^k*q-1, a_k=3^k*q-1, C^(2k)(A)=a_k.
In particular2^k|(A+1). This is an attainment witness, not evaluation
of the arbitrary chosen rootClock.
The first successor b is1mod3 or2b=3A+1; strictupper forces1mod3.
For largek with2^k>A+1, even3^k>a_k+1 follows from the old height
bound, so the valuation exclusion must not be overstated as a new
constraint on every arbitrarily late root.

HEIGHT BARRIER, KERNEL:
For q>0, 3^d<=3^j*q implies2^d<=2^j*q.
Hence ifA<2^d andb=3^j*q-1>=3^d-1, ALL such all-odd inverse
ancestors2^j*q-1 are already>=A. Increasingj alone cannot produce
a smaller predecessor at these target heights.
Withdleast such thatA<2^d, threshold3^d is within factor3 of
(A+1)^(log2 3); this real-power comparison is written.
NEXT ANCESTRY WORK: mixed parity inverse words that remain effective
above this height barrier, or a new quantitative branch estimate.

AXIOM-FREE FINITE EXAMPLE:
From27, clocks26and44 give155and167. Withterminalclock64,
suffix minima atclocks26and27 are155and167. Parent111->334->167
is below155 and absent fromall65prefix states;111isdivisible3.
These are finite suffix minima, NOT global roots.
Kernel arrivals at1:155at85,167at67,111at69. Python independently
checks first-arrival minimality. Allthreeglobalminimaare1.

VERIFICATION2026-10-14T21:38:59.046171Z:23fresh sequential
Lean4.33.1 builds10.929sec,21audited roots,50hashes,48prior hashes
authenticated. Doc-only review21:40:02.127598Z changes no tested code,
logs, or replay hashes. All computation certificates are kernel,
not native_decide; no new external proof premise.
Python:4243odd-block sourcepairs,33944finite transportchecks,
10428conditional finite ancestor cases; source paths422592steps,
target suffixes271552steps,75520independent initialshortcutpairs.
8192complete source prefixes throughclock128orfirst1:636520steps,
49152independent suffix-record comparisons,56014parentchecks.
3368off-path parent instances,235distincttriples;2118instances
have3-divisible parents,1250units. Not asymptotic density samples.
49532saturationchecks,49536next-power exclusions,41538height-barrier
comparisons are arithmetic only. Three kernel witnesses replayed221steps.

ROUTES RECHECKED:
The previous all-root count is broader than per-orbit packing, but its
exponentlog2(29/15) is weaker than the old per-orbit entropy exponent
H2(log3 2). Its root-index corollary is NOT the strongest known inrepo.
Polynomial target counts do not give sublinear-in-K masked energy at
targetcutoff3^K. The small-seed forward-orbit term stays uncontrolled.
Earlier branch-density flow already allows positive summable increments.
The Tavares arxiv2608.27617v1 primary page still leavesstar3/Conjecture2
open; no claim from it was adopted. The external two-coordinate clone
remainscleanata7275d5a73814d3d9a400c6fe6577de9542b03a3, read-only.
No fresh external Lean replay or mathematical dependency was added.

The preceding minimum-root and cap-budget milestone:

The preceding note is docs/MINIMUM-ROOT-SPINE.md, with
lean/MinimumRootSpine.lean and verify_minimum_root_spine.py.

ACTUAL GLOBAL STRUCTURE, ALL KERNEL:
m(n)=min(n,m(Cn)); m(2n)=m(n);
m(2n+1)=min(2n+1,m(3n+2)).
A minimum root is a positive a with m(a)=a, equivalently no forward
descent below a. It need not be periodic. For sigma(a)=m(Ca),
a<=sigma(a), m(sigma(a))=sigma(a), 2sigma(a)<=3a+1, and 3 does not
divide sigma(a). Equality sigma(a)=a iff a has a positive-time return.

Set a0=m(n), a_(k+1)=sigma(a_k). Each root is attained on the original
orbit at an explicitly defined strictly increasing ordinary clock.
For a positive orbit with no eventual repetition,
  m(n)+4k<=a_k; 2^k(a_k+1)<=3^k(m(n)+1).
All roots >1 have residues7,11,15mod16; successors also avoid3,
giving residues7,11,23,31,43,47mod48. Do NOT apply the distinct least-
counterexample backward restrictions to all later roots.
No upper bound on the ordinary attainment clocks is supplied.

GLOBAL CAP CRITERION:
Delta(n)=m(Cn)-m(n)>=0; Delta(2n)=0.
Delta(n)>0 iff m(n)=n and n has no positive-time return.
This condition also allows a transient root before a hypothetical
larger cycle; positive cap is not a divergence certificate.
A_T(n)=sum_(t<T)Delta(C^t n)=m(C^T n)-m(n), and
  (exists B forall T A_T(n)<=B) iff n eventually repeats.
The same equivalence holds with bounded tail minima. Convergent
positive sources have all global caps zero.
Bounded caps universally are NOT proved, and would still leave
nontrivial cycles to exclude.

FINITE/GLOBAL DISTINCTION:
With terminal horizonT, finite suffix minima u_j=min_(j<=i<=T)C^i n
give total finite caps=C^T n-m_T(n), not the global identity.
Kernel: source1 has finite cap totals0,3,1 atT=3q,3q+1,3q+2 for everyq,
although its global total is always0. Fixed-edge caps settle to0 but
the moving finite sum oscillates.

ALL-ROOT POPULATION:
R_k counts actual roots in(2^k,2^(k+1)], r=29/15.
Kernel R_k<=2*r^(k+1)+(k+1)/2; same for finite no-descent counts at
anyT>=2(k+1), and actualR<=prefixR.
S_K=sum_(k<K)R_k/2^k and
E_K=116*(29/30)^K+(K+2)/2^K satisfy S_K+E_K<=118, E_K>=0.
Written comparison/limit: sum_(a>=1,m(a)=a)1/a<=119 including1.
Written count growth O(N^alpha), alpha=log2(29/15)<1, gives
a_k>=c*(k+1)^(1/alpha) for any nonrepeating root sequence.
This is still compatible with infinite sparse roots and exponential
upper growth; it is not a subunit minimum-tail mean.

Verification2026-10-14T21:10:53.643080Z:22 fresh sequential Lean4.33.1
builds10.470sec,52 audited roots,48 hashes,47 prior population hashes
authenticated. Doc-only review21:12:44.418201Z preserves all tested
code/log/replay hashes. No native finite axiom or new external input.
Python:65535complete shell sources2..65536,1966082ordinary steps and
65535independent exact-clock comparisons;65626finite cap telescopes,
1970655cap edges including90extra prefixes and a source1example.
Separate4096sources1..4096 all reach1 in307751ordinary steps, with
independent shortcut paths and320039witnessed zero-global-cap edges.
257consecutive envelope checks plus3large indices through4096 are
arithmetic only. Finite unfinished orbits are never assigned global minima.

NEXT: an independently useful actual residual or cap upper bound is
still missing. Sparse-root counting alone does not bound the sizes of
the basins feeding those roots. Investigate arithmetic beyond these
necessary root conditions, with both nonrepeating orbits and nontrivial
cycles still open. The full Collatz goal remains active, no blocker.

The preceding population-majorant milestone:

The preceding note is docs/MINIMUM-POPULATION-MAJORANT.md, with
lean/MinimumPopulationMajorant.lean and
verify_minimum_population_majorant.py.

NEW UNCONDITIONAL KERNEL BOUNDS:
Let r=29/15, k=floor(log2 N), and T>=2k. For every H and positive N,
  G_H(N)<=F_(H,T)(N)<=2*r^k+k/2.
At N=2^k, the sharper bound is r^k+k/4.
These apply to actual global minima, without assuming convergence.
The real power/sublinearity consequence is written; all displayed
rational inequalities and population assembly are kernel theorems.

PROOF: for shortcut odd-count a_k(n), define the integer word weight
W_k(n)=85^(k-a_k(n))*147^a_k(n), Q=120^k, M=2^k.
The exact numerator B_k satisfies M*U^k(n)=3^a*n+B_k(n).
Kernel: 3^a*Q^2<=M*W^2, W is M-periodic, and
  sum_(0<=n<M) W_k(n)=232^k.
The last-bit parity flip pairs children with weight sum232*W.
The reused binary-image theorem gives
  4*sum_(0<=n<M) B_k(n)=k*M^2,
so the mean rational affine correction B_k/M is exactly k/4.
The pointwise bound, with the actual correction retained, is
  M*Q*m_T(n)<=M*n*W_k(n)+Q*B_k(n).
Positive ranges1..M have the same mass as0..M-1. For N<=2M,
  2*Q*tailSum_(H,T)(N)<=4*N*232^k+Q*k*M.
At N=M the sharper left coefficient4 replaces2. This proves the
rational population bounds. No uncomputed global minimum is assigned
by finite replay; m<=m_T transfers the kernel upper bound directly.

Since V(N)>=r^k and (k+2)*120^k<=2*232^k, the kernel now proves
  0<=G_H(N)<=3V(N), also at N=0,
and the same upper majorant for all T>=2floor(log2 N).
Thus the prior adaptiveMean(H,L,N) majorant is unconditional as well.
The finite actual-global residual truncation and absolute-tail bounds,
and the adaptive occupation lower bound, no longer have an extra
population-majorant hypothesis. The infinite Green representation
still uses the written monotone/L1 assembly, not formal measure theory.
The least-counterexample residual diagnostic still requires an
independently small positive-residual majorant eta; that is NOT proved.

Final verification2026-10-14T20:49:42.733776Z:21 fresh sequential
Lean4.33.1 builds9.643sec,36 roots,47 hashes. Authenticated28 prior
critical-clock hashes and26 binary-image hashes (possibly overlapping).
Exact period enumeration:131071 residue/depth pairs,1966082shortcut
steps,17 weight masses and17 correction masses with17 binomial checks.
Pointwise majorant:196590 source/depth pairs,2883468shortcut steps.
Complete positive sources1..65536 through ordinary clock32:
2097152steps in EACH traversal order,1114112 matching prefix minima.
For H=0,1,16,64:262144 population bounds and262144 gauge comparisons,
68 sharper dyadic bounds. Separate adaptive PREFIX Green checks:
216 forward/backward depth comparisons and576 absolute-tail windows.
261 large-index scale/correction tests through4096 are arithmetic only.
No native finite axiom or new external mathematical premise.

Web review checked Tao's primary paper, arxiv1909.03562v5, theorem1.3
and remark1.4. Its almost-everywhere logarithmic-density statement
does not give the required uniform linear-tail bound; it is cited for
context only, not imported into any new proof. No novelty claim.

NEXT: seek actual signed/positive residual control strong enough for
the subunit budget, or exploit additional orbit arithmetic beyond a
single complete parity period. Improving this sublinear power bound
alone does not force the normalized mean below1 uniformly in N.
The Collatz goal remains active; no external blocker is present.

The preceding note is docs/MINIMUM-CRITICAL-CLOCK-LIFT.md, with
lean/MinimumCriticalClockLift.lean and
verify_minimum_critical_clock_lift.py.

Kernel constructive lift: a0=0, aj<2^j, and
  9^aj+7=2^(j+3)*qj.
Set a_(j+1)=aj if qj even, otherwise aj+2^j. The elementary induction
  9^(2^j)=1+2^(j+3)*(2cj+1)
proves the lift, without an external valuation theorem. Set
  Kj=2*(aj+2^j), Nj=2^Kj-1.
Then 2^(j+1)<=Kj<2^(j+2), log2_floor(Kj)=j+1, and
  3^Kj+7=2^(j+3)*q for some positive q.

For j>=2 the actual ordinary orbit from Nj has Kj initial odd
shortcut steps, three halvings, then j more odd shortcut steps.
The bridge 3^Kj-1=8*(2^j*q-1) stays above Nj; safety holds for K>=6.
At ordinary clock B=2*(Kj+j)+3 its endpoint is z=3^j*q-1, with
  m_B(Nj)=Nj, 3^(Kj+j)*Nj<=2^(Kj+j+3)*z.
A generic scaled-endpoint halving-buffer theorem gives
  2^T<=6^(Kj+j) => m_T(Nj)=Nj.
For H<Nj, the single diagonal source therefore gives tailSum>=Nj.
A strict budget at Nj forces 6^(Kj+j)<2^(T(Nj)), also kernel checked.
This gives mean>=1, NOT an unbounded critical-clock mean.

Kernel exact critical clock:
  criticalClock(L,N)=floor(log2(6^floor(log2(N+1))))+L.
At Nj it equals floor(log2(6^Kj))+L. For j>=max(2,L) it retains Nj.
For EVERY H,L,b there exists N>b whose tailSum at this clock is>=N.
At these cutoffs the usual floor(gamma*log2 N)+L is no larger.

WRITTEN real-log consequence, gamma=log2 6:
  T(Nj)>gamma*log2 Nj+gamma*log2 log2 Nj-2gamma
is necessary for the strict budget. This follows from log2 Nj<Kj
and log2 log2 Nj<log2 Kj<j+2. Therefore every clock
floor(gamma*log2 N+c*log2 log2 N)+L with fixed c<gamma fails at
all sufficiently large family cutoffs, for every fixed H,L.
The integer implication is kernel; the real-log comparison and
asymptotic assembly are written. Larger leading coefficients and
the full gamma log-log correction with arbitrary constant are NOT
excluded. No theorem of convergence for the infinite family is proved.

Closed axiom-free roots evaluate K2=14,K3=30 and prove Nj reaches1
at ordinary clocks159,449, respectively. Python first descents70,197
are separate minimality checks. These examples demonstrate compatibility
of the finite-prefix obstruction with eventual convergence.

Verification2026-10-14T20:29:58.476105Z:12 fresh sequential Lean4.33.1
builds6.055sec,21 audited roots,28 hashes,26 prior hashes authenticated.
Independent Python:1025 modular lifts/top-bit identities/block bounds;
8191small exponent residues;13actual prefix sources j2..14,
186810ordinary steps,186823prefix-time checks,208exact endpoints,
117shift inequalities. Largest actual source33966bits. Modular checks
at index1024 do NOT construct or census their enormous sources.
Separate9-source convergence replay80543steps, including608edges for
the two kernel witnesses. No native computation axiom or new premise.

NEXT: investigate larger cutoff-dependent clocks or an independent
bound on actual global residuals. The fixed-shift route now fails
even at the leading coefficient gamma; increasing that coefficient
or adding the full log-log term is not by itself a sufficient proof.
The full Collatz goal remains active, with no external blocker.

The preceding note is docs/MINIMUM-CLOCK-BARRIER.md, with
lean/MinimumClockBarrier.lean and verify_minimum_clock_barrier.py.
The previous turn's Green-kernel summability result remains valid.

For K,q>=1 the ordinary orbit from n=2^K q-1 satisfies
C^(2i)n=2^(K-i)3^i q-1 for0<=i<=K, with all intermediate values>=n.
Since2C(x)>=x, an endpoint>=2^s n cannot fall below n in s more
ordinary steps. Kernel:
  2^T<=6^K => m_T(2^K q-1)=2^K q-1.
In particular m_(5b)(2^(2b)q-1)=2^(2b)q-1, since32^b<=36^b.
These are finite prefixes, NOT divergent orbits.

Set T_L(N)=L+2floor(log2 N), with A_(H,L)(N) the mean of
m_(T_L(N))(n)1_(m_(T_L(N))(n)>H) over1<=n<=N.
At j>=1 let M=2^(4j+2L), Q=2^j,N=MQ=2^(5j+2L). T_L(N)=10j+5L.
All Q sources Mq-1,1<=q<=Q retain their initial minimum. For H<M-1,
  A_(H,L)(N)>=(Q+1)/2-1/M>=Q/2=2^(j-1).
The residue embedding, sum and population lower bound are kernel
checked. Thus for EVERY fixed floorH and shiftL, A_(H,L) is unbounded
overN. The corresponding strict finite-prefix tail budget fails.

More generally a strict budget at cutoff2^(d+1), with H<2^d-1,d>=1,
forces6^d<2^T (kernel). Writing gamma=log2 6, any valid strict budget
at all large dyadic cutoffs must have T(2^d)>gamma(d-1). An extra
clockL(N) above2log2 N must therefore exceed(gamma-2)d-gamma at2^d.
WRITTEN: with K=ceil(T/gamma), Q=2^(d-K), the same source class
gives F_(H,T)(2^d)>=(1/4)2^(d-T/gamma), oncefloor/endpoint conditions
hold. Hence every coefficient0<c<gamma in floor(c log2 N)+L yields
polynomially growing tail means. That earlier calculation alone does
not rule out coefficients>=gamma; the newer lift above addresses equality.

Kernel pointwise settling: A_(H,L)(N) decreases in L and eventually
equals actual G_H(N) at each fixedN, whether or not Collatz is true.
The proof uses a finite sum of attained minimum clocks; this is not an
effectively known time bound. Under full Collatz,G_H=0 at H>=1, so
the finite approximants would still fail uniform convergence over N.
Unconditionally, no difference A-G is assigned without knowing G.

WRITTEN residual consequence for H>=1: sinceT_L>=2log2N, the prior elementary
bound gives0<=A_(H,L)<=3V uniformlyL. Its clockless residual evaluates
each child with its OWN cutoff-dependent clock, not parent clock-1/-2.
Green unrolling yields A_(H,L)=E sum R_(H,L), so signed and positive
residual occupation are unbounded in N for every fixedL. For fixedN,
R_(H,L)->R_H and the6V envelope gives convergence in L1 of their
occupation difference. This convergence has no uniform-in-N rate.
The finite lower bound2^(j-1)-3rho^J V(N) on signed occupation is
kernel checked with the explicit majorant premise. The population
upper majorant and infinite assembly remain written.

Closed kernel witness: atH64,N1024,T20, the sources255,511,767,1023
alone contribute2556, so tail mean>=639/256. Their hitting clocks to1
are47,61,59,62, checked by kernel reduction without axioms. This is
a certificate for those four sources, not the entire interval.

Final verification2026-10-14T20:10:10.422631Z:11 fresh sequential
Lean4.33.1 builds5.426sec,30 roots,26 hashed files,24 prior hashes.
Exact Python:1596selected sources,501492ordinary prefix steps;
418large-family arithmetic cases,256dyadic clock thresholds;
131072complete sources throughclock35,4587520ordinary steps in each
traversal order,786432matching minima,22population bounds. The separate
1024source settling census has maximum first-one clock178. Huge
family cutoffs are arithmetic consequences, not interval censuses.

NEXT: estimate actual global residuals directly, or use extra clock
growing with cutoff beyond the necessary threshold. Do not try to
make these fixed-additive-shift approximants uniformly subunit.
No new external premise; full Collatz remains unresolved.

The preceding note is docs/MINIMUM-GREEN-KERNEL.md, with
lean/MinimumGreenKernel.lean and verify_minimum_green_kernel.py.
Put q=29/30,rho=1704/1711. For n>0,k=floor(log2 n),p=2^k,
  V(n)=q^k(p+14n)/15; V(0)=0.
Kernel: V>=1 at positive n, V<=n*q^k, and PV<=rho*V for every n>=2,
where Pf(n)=[f(n//2)+f(3((n-1)//2)+2)]/2 is the AUXILIARY source-cutoff
average, not an individual Collatz orbit. Two exact integer cell
inequalities include all odd/even rounding. 1-rho=7/1711.

WRITTEN population input from elementary finite parity:
  G_H(N)<=Nq^k+(2q)^k+(3/2)^k<=q^k(N+2p)<=3V(N),
for k=floor(log2 N), actual global minimum m, and
G_H(N)=mean m(n)1_(m(n)>H). It follows from m<=m_(2k); it assumes
neither Collatz nor the older analytic mixing. The population assembly
is written, NOT a new unconditional Lean theorem about G<=3V.

At floor H>=1, tau is the first auxiliary cutoff <=H. Generic kernel
finite bounds, for 0<=f<=3V and f=0 at the floor, give
  E[f(N_J)1_(tau>J)]<=3rho^J V(N),
  f(N)=E[f(N_J)1_(tau>J)]+E sum_(j<J,j<tau)(f-Pf)(N_j).
Nonnegativity improves |f-Pf|<=3V on active states, hence for all J,K
  E sum_(J<=j<J+K,j<tau)|f-Pf|(N_j)<=(5133/7)rho^J V(N).
The survival bound Pr(tau>J)<=rho^J V(N) also holds for H=1,2.

WRITTEN monotone convergence on the absolute sum, followed by L1
convergence, now justifies
  G_H(N)=E sum_(j<tau)R_H(N_j), R_H=G_H-PG_H,
with the same infinite absolute-tail bound. The signed truncation error
is between0 and3rho^J V(N). This closes the earlier expectation/sum
interchange gap at each fixed initial cutoff. It does NOT bound the
means below1 uniformly in N. V grows without bound. At linear weight
r=2 the general contraction formula becomes rho=1, so that endpoint
cannot be substituted into this argument.

For a hypothetical least counterexample A, kernel proofs give m(A)=A,
m(n)=1 for1<=n<A and EXACTLY G_(A-1)(A)=1. If its active residual is
bounded above by eta*V, eta>=0, the conditional finite kernel diagnostic
is 1<=[3rho^K+eta(1-rho^K)/(1-rho)]V(A). The written limit requires
  sup_(n>=A) max(R_(A-1)(n),0)/V(n) >=7/(1711V(A)).
This supremum need not be attained. No independent upper bound
contradicting it is known here. Defining R from G does not estimate G.

Verification passed 2026-10-14T19:46:20.762332Z:10 fresh sequential
Lean4.33.1 builds in4.666sec,34 new kernel roots,24 hashed files,
26 previous hashes authenticated. No native finite axiom. Python:
66696 exact gauge checks including1161 large cell/dyadic cases;
36 profile trees,468 forward/backward depth comparisons,3276 absolute
tail windows. Actual PREFIX census16589sources through clock28,
464492ordinary steps in each traversal order,248835 matching minimum
snapshots,49767 population bounds. Two synthetic profiles are separately
identified. Huge cutoff tests are arithmetic, NOT orbit censuses.
No global minimum is inferred from a finite alive prefix.

NEXT: estimate the actual positive/signed residual independently strongly
enough to force a uniform subunit budget. The integration issue is
closed; the missing Collatz estimate is not. No new external input.

The preceding result concerns the auxiliary fair cutoff chain, NOT an
individual Collatz orbit. Let F_T(N)=mean m_T(n)1_(m_T(n)>H), and
R_T(N)=F_T(N)-[F_(T-1)(a(N))+F_(T-2)(b(N))]/2, where a=N//2,
b=3((N-1)//2)+2. A lower/upper cutoff step consumes ordinary clock1/2.
Stop at cutoff<=H or remaining clock<=1. Exact finite unrolling gives
  F_T(N)=B_T(N)+S_T(N),
where B is the terminal mean and S the expected signed residual sum.

Kernel dyadic potential: ell(n) is binary length with ell(0)=0.
For n>=4, P^3 ell(n)<=ell(n)-1/8. Compare the eight leaves from
n<2^(k+3) to those of 2^(k+3)-1: one p-1, three3p-1, three9p-1,
one27p-1, p=2^k. Their total bit length is <=8k+23.
V=ell+Pell+P^2ell has PV<=V-1/8 and 0<=V<=3ell for n>=2.
Thus E sigma<=24ell(N), but
  E N_sigma=N-(1/2)E(number of even active cutoffs)>=N-12ell(N).
The clock-zero/one tail means are >=3N/8-H. Consequently the actual
finite-clock terminal contribution satisfies, for EVERY T,
  B_T(N)>=3N/8-(9/2)ell(N)-H  (H>=3,N>=2).
The auxiliary cutoff family can fail uniform integrability even though
the floor is reached almost surely. This is NOT a failure of actual
Collatz minimum uniform integrability.

At H4,N256, B_T>=103/2 for every T. Kernel-checked literal paths have
10971 ordinary edges and maximum floor-hit clock125 for all256sources.
Therefore F_T(256)=0 for EVERY T>=128, and S_T(256)<=-103/2 at every
such clock. The finite paths are checked with decide +kernel, with
generic soundness and monotonicity proofs; no native finite axiom.
Dropping the terminal term or seeking vanishing total error already
fails on this verified floor-reaching finite population.

The WRITTEN leading boundary law is sharper. With
  c_T=3/7+(-3/4)^T/14, c0=1/2,c1=3/8,
  c_T=(c_(T-1)+3c_(T-2))/4,
the local residual of c_T*n is c_(T-2)/2 at even cutoffs and
(c_(T-1)-c_(T-2))/4 at odd cutoffs, always of absolute value<=1/4.
The short-clock/floor terminal error is <=H+1, so
  |B_T(N)-c_T*N|<=H+1+6ell(N), uniformly in T.

Elementary finite-parity counting gives a WRITTEN bound independent of
the previous analytic mixing/tightness. For k shortcut steps, slope
A=3^j/2^k and affine correction B<= (3/2)^k-1. The parity words run
bijectively through residues mod2^k. Rational word weights
  e=17/24, o=49/40, q=(e+o)/2=29/30
satisfy e^2>=1/2, o^2>=3/2. Thus w=e^(k-j)o^j has w^2>=A and
min(1,A)<=w. For ordinary T>=2k, m_T(n)<=n*w+(3/2)^k, hence
  F_T(N)/N <= (1+2^k/N)q^k + (3/2)^k/N.
Choose k=min(floor(T(N)/2),floor(log_2 N)). Whenever T(N)->infinity,
F_(T(N))(N)=o(N). This is only an o(N^2) unnormalized tail SUM.
At any fixed H>=3, therefore B_(T(N))(N)/N->3/7 and
S_(T(N))(N)/N->-3/7. This coefficient is NOT the unknown mass b.
Leading cancellation does not imply the required unscaled F<1.

The same parity argument gives G_H(N)=mean m(n)1_(m(n)>H)=o(N)
for the actual GLOBAL minimum, with no analytic mixing premise.
For its CLOCKLESS unroll to depth J or floor, given epsilon choose K
with G_H(n)<=epsilon*n aboveK and M_K=max_(n<=K)G_H(n). Then
  E G_H(N_(tau wedge J)) <=epsilon*N+M_K*Pr(tau>J)->epsilon*N.
Let epsilon go to0: this terminal term does vanish. Exact clockless
unrolling therefore gives G_H(N) as the limit of finite expected signed
residual sums. Do NOT interchange expectation with an infinite random
sum without a separate integrability argument; the newer Green-kernel
result above now supplies one. Either control this
clockless signed residual or retain and cancel the finite-clock boundary.
The necessary subunit uniform tail estimate remains unproved.

The preceding cap audit retains the truncation of a finite prefix minimum at
its odd source. With g_H(y)=y 1_(y>H), define
  d_H(s,y)=g_H(y)-g_H(min(s,y)),
  D_(H,t)(X)=sum_(n=1..X) d_H(2n+1,m_t(3n+2)).
Here m_t includes all ordinary steps from0 through t. Kernel proofs give
  m_(t+1)(2n)=m_t(n),
  m_(t+2)(2n+1)=min(2n+1,m_t(3n+2)),
and d_H(s,y)=g_H(y) for s<=H, otherwise (y-s)_+.
Thus D decreases in t. Once D=0, every later D at the same H,X is0,
without any assumption about future convergence.

Let N>=3, a=floor(N/2), X=floor((N-1)/2), c=3X+2, H>=1,
F_t(M)=mean_(n<=M) g_H(m_t(n)),
delta_t(X)=mean_(n<=X) g_H(m_t(3n+2))-F_t(c). Then
  N F_(t+2)(N)+D_(H,t)(X)=a F_(t+1)(a)+X F_t(c)+X delta_t(X).
Both unnormalized population parities are kernel checked. Subtracting
the fair half-weighted children leaves
  R=(X/N)delta-D/N-Q,
where Q=(1/2-a/N)F_(t+1)(a)+(1/2-X/N)F_t(c)>=0.
The favorable cap is separate from the progression sampling error.

An actual small witness is H1, X1, N3, t4. The child tail values through5
are [0,0,3,0,2], the parent clock6 sum through3 is2, and the even child
is0. Thus delta=1, R=1/6 and D=0; ALL future D are0. The closed values
and cross-multiplied residual sign are kernel proved. They reject
uniform finite bounds by any nonnegative current or future cap charge
at this fixed floor/cutoff. They do not exclude past-cap charges,
signed time cancellation, eventual large-scale estimates, added boundary
terms, or separate bounds on actual infinite minima.

The independently replayed larger witness has H64, parent clock256,
tail clock254, source cutoff65536 (also65537). Its parent tail sum33999,
even child sum182, upper child sum100001 and progression sum33817
give zero cap and a positive fair residual. At N65536 this is
47479783/6442385408. The upper cutoff is98303 (98306 for N65537).
All 294918 minima at clocks254,255,256 through source98306 were
recomputed source by source after a separate time-major census.
The large finite values are Python, NOT kernel certificates; their
all-future zero-cap implication is the generic kernel theorem.
Since33999>32768, the dyadic half budget fails at H64,T(2^k)=16k,k16.
This does not refute the strict S<N budget at this cutoff or another
floor/clock, and no future minimum is assigned to an alive prefix.

Weighted layer-cake is exact: g_H(y)=H1_(y>H)+sum_(s=H..c-1)1_(y>s)
for y<=c. Even granting threshold-uniform discrepancy epsilon, summing
absolute errors only yields c*epsilon. Arbitrary fixed log-power
bounded-label errors therefore do not supply a linear weighted estimate
by this argument. A new finite-clock threshold mixing theorem is not
asserted. The next target is the whole signed residual or stronger
weighted progression control, not cap-only accounting.

The preceding rigidity result uses m(n)=min_t C^t(n), not the minimum at a finite
clock. The attained minimum satisfies m(m(n))=m(n). Therefore
  U(H)=sup_N mean_(n<=N) m(n)1_(m(n)>H)
is either zero or at least one: any minimum a>H is its own diagonal
source and contributes a at cutoff N=a. Even the pointwise-in-N
strict budget sum m(n)1_(m(n)>H)<N for every positive N forces all
minima <=H. A verified convergent floor H then gives full Collatz.
These implications are kernel checked and need no analytic mixing or
external predecessor theorem. The needed budget is NOT proved.

Replacing m by its finite-prefix upper bound m_T gives a kernel-checked
sufficient condition, for any proposed population clock T(N). All
source cutoffs must satisfy it. A written dyadic variant needs twice
the prefix-minimum tail sum at 2^k to be <=2^k for every k: the least
dyadic cutoff above a lies strictly below 2a. No prescribed clock is
asserted equivalent to Collatz, and finite sample success is insufficient.

UI of the actual minimum itself is equivalent to a global finite bound
on minima, hence to a finite collection of eventual cycles. Apply the
bound at every forward state to force repeated visits to a finite set.
This does not select the known cycle without verifying that floor.
Uniformly bounded first moments, or a finite moment of the limiting
minimum law, are weaker: an explicit separate map doubling powers of
two >1 and sending all other states to1 has mean minimum bounded by3
but escaping powers of two and limiting minimum law delta1.

For the earlier DensityCountermodel (NOT Collatz), half the sources
escape, even halving and the known 1,4,2 cycle are retained, and every
target has written predecessor density >=1/(2a). Its minimum labels
are 1 and v_k=2^(k+2)-1, with masses 1/2 and pi_k=1/(v_k+1).
Sources with label v are exactly 2^a(v+2(v+1)j), a,j>=0. Their finite
population probabilities are <=2/v<=3pi_k. Consequently, for any
nonnegative finite weight w, uniform minimum-level tail decay is
equivalent to sum_k w(v_k)/(v_k+1)<infinity. This includes m^p for
p<1 and even m/[log_2(m+1)]^q for q>1. At the endpoint and beyond
the corresponding means tend to infinity. At cutoff 2^L the exact
linear mean is L-1+2^(1-L), and each visible spine atom already equals
its limiting density. These are comparison-map deductions, not a
Collatz counterexample or a disproof of its desired moment bound.

The existing actual-Collatz logarithmic moments cannot be extrapolated
to the linear budget; constants depend on the exponent. Even proving
the nearly linear weights above would not close the route using those
properties alone. Additional 3n+1 arithmetic or the actual linear-tail
budget is still needed. No new external theorem is used in this step.

The preceding written deduction keeps both clock shifts through the entire
two-sided population recurrence. Set L=log(4/3), kappa=3/L, and
sigma^2=2(log 6)^2/L^3. At T_N(u)=floor(kappa log N+u sqrt(log N)),
  mean z_T -> b Phi(u/sigma),
  mean A_T/sqrt(log N) -> b[u Phi(u/sigma)+sigma phi(u/sigma)].
Phi and phi are standard normal CDF and density; b is the existing
nonconvergent lost-weight mass, not a landing state. Thus the critical
instantaneous limit, previously undecided, is b/2, and the critical
integrated coefficient is b sigma/sqrt(2pi). The old normalization by
log N still yields zero for every b and does not decide the conjecture.

Use the FAIR CUTOFF chain, not a probabilistic model of an individual
Collatz orbit. Lower/upper cutoffs consume ordinary clocks one/two.
At absorption below H, H/2<=N_tau<=H, E tau<=log(2N/H)/d, d=L/2,
and E sum_(j<tau) 1/N_j<=6/H. With iid branch signs and S their sum,
  J_tau=kappa(log N-log N_tau)+kappa(log 6/3)S_tau+kappa R_tau,
  E|R_tau|<=12/H.
Take H=floor(exp((log N)^(1/4))). The stopped-sign isometry
E(S_tau-S_m)^2=E|tau-m|, m=floor(log N/d), proves the Gaussian clock
limit. Its L2 sign bound and L1 rounding error give convergence of
positive-part means, not just distributional convergence.

Two-sided cell/deficit recurrence errors are bounded by g_R(N) and
T g_R(N), with g_R=K_R(log N)^(-R)+(log N+7)/(6N). Logarithmic and
reciprocal-logarithmic potentials give expected error occupation
eta_H=O((log H)^(-3)) at R=4. Thus cell error is o(1) and deficit
error is o(sqrt(log N)) for the chosen floor. The terminal terms are
POPULATION MEANS at cutoff N_tau, not values on that single source.

For M->infinity and s/log M->infinity, the earlier written minimum
tightness, minimum-clock concentration and mean lost-weight limit
give Z_s(M)->b and F_s(M)/s->b. Fix a minimum bound K first and use
max_(a<=K)[W_floor(s/2)(a)-W_infinity(a)]->0 for ordinary weights;
then let K grow. This yields uniform terminal settling on
H/2<=M<=H, epsilon sqrt(log N)<=s<=T_N(u), so no independence of the
exit state and clock is needed. No lifetime-deficit UI is used.

These analytic steps are WRITTEN, not formalized or independently peer
reviewed. With the prior separately EXTERNAL predecessor positivity,
full Collatz is equivalent to either mean z_floor(kappa log N)->0 or
sum A_floor(kappa log N)=o(N sqrt(log N)). Both remain UNPROVED.
Along N=2^k the latter scale is 2^k sqrt k and its coefficient is
b sigma sqrt(log 2)/sqrt(2pi). The Gaussian profile identifies b more
sharply but supplies no argument that b vanishes.

The preceding audit rechecked Tao's published inversion, passage event
equivalence, collision factorization and paired-product structure.
It found no contradiction in retaining the ordinary clock, but does
not claim a full formalization or independent validation of mixing.
For a word of length k and sum s ending at M, the ordinary prefix
clock is k+s. If M has m Syracuse passage steps left with tail sum
sigma, the full clock is k+s+m+sigma ONLY if no earlier passage
occurred. The odd path 19->29->11->17->13 at floor16 demonstrates the
need: the tail from17 crosses at ordinary clock3, while source19 first
crosses at6, not8+3=11. This does not refute the existing gated argument.

If |S_j-2j|<=E for all prefix sums, then M<=4^E N_j+3^k for each
prefix odd state. Thus M>4^E H+3^k excludes every earlier crossing;
the analytic intermediate-height window ensures this for sufficiently
large scales. For an interval shift from N=2^s(M-F)/3^k to U=2^sM/3^k,
F/M<=eta places every membership change in the two actual source
layers [(1-eta)y,y) and [2(1-eta)y,2y). Unique inversion at fixed k
prevents an exponential word-count factor. Exact tests include a
rational endpoint with a nonzero membership change. No effective
asymptotic constants or additional convergence conclusion is obtained.

The preceding minimum-tail result concerns m(n)=min_t C^t(n), which exists for every
positive orbit without being assumed equal to one. At a first odd
record landing b, m(source)=m(b), so the preceding coupling controls
the whole minimum law, uniformly over thresholds H, even when H is
above the passage floor. For f_H=1_(m>H), the even identity is exact;
the odd identity is f_H(2n+1)=1_(2n+1>H) f_H(3n+2). Retain this killed
boundary factor. Parity splitting yields
  F_H(N)<=[F_H(floor(N/2))+F_H(3floor((N-1)/2)+2)]/2
          +K_(r+1)(log N)^(-r-1),
for N>H sufficiently large, with F_H=0 below H.

The two cutoffs a,b satisfy 4ab<3N^2, giving mean log drift at most
-d, d=.5log(4/3). The auxiliary FAIR CUTOFF chain stops below H with
overshoot no lower than H/2 and finite expected duration. It is not
a random model of an individual Collatz orbit. The convex potential
(log N)^(-r) sums all errors, giving the uniform minimum-tail bound.
Every fixed power of log m is uniformly integrable; source moments
converge if the earlier written minimum law is also used. This says
nothing about lifetime-deficit UI, arrival-clock moments, powers of m
itself, or minimum one. Constants and thresholds depend on r; sending
r to infinity at a fixed floor is invalid. All analytic claims remain
WRITTEN consequences of the prior local mixing argument.

The preceding result compares SAME-SCALE source laws, not different scales.
It extends the local joint fine-scale argument with one endpoint
valuation fixed, using Tao's published paired Fourier and collision
inputs. Odd source classes 1 and 2 modulo three have joint first-odd-
passage landing/ORDINARY-clock laws within O_R((log y)^(-R)) of the
unrestricted odd source law, for every fixed R. The common coarse laws
agree before summing over the word length or valuation sum; no renewal
phase averaging or irrationality exponent is used in this comparison.
Do not upgrade the previous DIFFERENT-SCALE stabilization rate to this
arbitrary-power rate. All these analytic statements remain WRITTEN.

At matched landing b and common clock I, prefix weight retention gives
  0<=A_t(source)-A_((t-I)_+)(b)<=epsilon_x*t
simultaneously for every finite t, without assuming arrival at one.
Arrival flags agree at every clock, and censored cells differ by at
most epsilon_x. Coupling, initial-halving decomposition, dyadic blocks,
and the omission of source2 give the all-positive-source comparison
  |delta_t(X)|<=C_R*t/(log X)^R,
uniformly in t, for X>=X_R. At X=2^k,t=8k the absolute discrepancy is
O_R(k^(-R)) for every fixed R after reindexing the exponent. This is
weaker in X than O(t/X), and does not contradict the finite witnesses.
No effective constants or thresholds are supplied. The leading bulk
profile b(t-kappa log X) obeys the population balance for any b because
kappa log(4/3)=3. This comparison alone does not establish b=0. The later
critical-window argument above performs the clocked iteration and settles
its moving-cutoff boundary, but the amplitude remains unknown.

The preceding finite recurrence uses ORDINARY time and includes every source.
For n>=1 and q=3n+2,
  A_(t+1)(2n)=A_t(n),
  A_(t+2)(2n+1)=A_t(q)+e_t(q),
  e_t(q)=(1+min(t,tau_1(q))-A_t(q))/(2q).
Thus 1/(2q)<=e_t(q)<=(t+1)/(2q), without assuming future arrival.
Write F_t(N)=mean_(n<=N) A_t(n), P_t(X)=mean_(n<=X) A_t(3n+2),
delta_t(X)=P_t(X)-F_t(3X+2), and E_t(X)=sum_(n<=X)e_t(3n+2).
Exact parity splitting gives
  (2X+1)F_(t+2)(2X+1)=X F_(t+1)(X)+X F_t(3X+2)+X delta_t(X)+E_t(X).
The explicit correction E is positive and at most (t+1)H_X/6.
That bound does not control the separate progression sampling error.
At X=2^20,t=160, certified intervals give delta>9t/X and X delta>8E.
The native census is NOT kernel certified; closed endpoint arithmetic
is. The smaller full Python census at X=2^17,t=136 independently gives
delta>2t/X. No larger unspecified constant or eventual asymptotic bound
is refuted. The required all-source zero limit remains open.

The preceding censored-clock test includes ALL positive sources and uses ORDINARY time.
Set z_t(n)=1_(first arrival at 1 > t)(1-W_t(n)) and A_T=sum_(t<T)z_t.
Only the finite prefix and an arrival flag are needed to compute A_T.
It is bounded by T; an alive flag is not a nonconvergence certificate.
For kappa=3/log(4/3), the written phase law gives
  mean_(n<=X) A_floor(c log X)(n)/log X -> b(c-kappa)_+,
locally uniformly in c, including zero at the critical coefficient.
Here b=mu(odd states outside the basin of one)=1-r_B-d. It detects
both escape and additional cycles. In particular, full Collatz is
equivalent, with the stated inputs, to
  sum_(n<=2^k) A_(8k)(n)=o(k*2^k).
The exact integer comparison (4/3)^8>2^3 places 8k above the critical
clock. This all-source estimate is UNPROVED. Omitting the arrival flag
instead gives the generally positive slope 1-d; restricting to known
convergent sources gives zero regardless of b. Neither substitution
tests the full conjecture. The earlier known-basin UI problem remains
open and is not required to identify this weaker normalized statistic.

The preceding profile is Q_L(n)=sum_(h<(T(n)-L)_+)(1-W_h(n)), where
T is first attainment of the global minimum, not necessarily one.
Initial halvings preserve the whole profile. The common-landing
comparison holds simultaneously for every L, giving a WRITTEN limiting
law in c_0 with the supremum norm, under the same local written
first-passage and packing inputs. Do not infer compactness from a
bounded norm in c_0: the full norm coupling is needed. Profile tails
vanish uniformly in probability over source populations, not in mean.
For Q^B=1_(minimum=1)Q, its zero coordinate is D_B and
Q^B_L=integral (G-L)_+ dmu_n. The bounded differences D_B-Q^B_L
identify E(limit D_B)=integral G dmu, allowing infinity. This closes
the identification explicitly left open in the preceding clock note.
Source-deficit uniform integrability is equivalent to uniform mean
clock-tail decay, and to source mean convergence to that FINITE value.
None is proved. Under them the known-child pre-arrival mean would
tend to ZERO, using its vanishing nonfusion support. Negative arrival
advances, post-arrival drift and unknown-child pairs remain separate.

The preceding identity is D(n)=sum_(j<tau(n))(tau(n)-1-j)*ell_j(n).
The coefficient is tau-1-j, not tau-j. Extend D by zero outside the
known basin only for the restricted source average. Then D_B(n) is
the integral, against the existing weight-loss probability mu_n, of
G(v)=tau(Uv) at odd convergent targets v>1 and zero elsewhere.
The existing TV limit supplies convergence for min(G,L), not for G.
Uniformly vanishing excess-clock tails are equivalent to convergence
of these source moments to their finite limiting moment. A uniform
prefix mean A would bound known-child pre-arrival means by 46A+1.
With the separately EXTERNAL reciprocal weighted-density floor, it
would also force summable tau(v)/v^2 on convergent odd units and
tau(v)=o(v^2) throughout the known basin. None of the assumed mean or
tail bounds is proved. Mean D is sufficient, not shown necessary, for
the original averaged pre-arrival problem; retain direct alternatives.

The preceding limiting-law argument defines D_m(n) up to first attainment of the orbit's
global minimum, which exists without assuming that minimum is one.
Sources coupled at a common first odd landing have deficit difference
at most their maximum minimum clock times the small prefix weight loss.
Finite descending coupling chains bound those clocks using a fixed
population's finite, not effectively bounded clock T_B. Fix B first,
then send the source scales to infinity; do not assume T_B B^(-gamma)
tends to zero. The global minimum, D_m and terminal weight have a joint
written limiting law for uniform integers. On the known basin D_m=D.
The pre-arrival transfer gives uniform tightness for H on pairs with
3n+2 known convergent, even if the parent is not known convergent.
Tightness supplies no integrable tail or uniform mean bound. The new
argument depends on written analytic inputs, unlike the transfer below.

The preceding pre-arrival transfer uses elementary affine identities and weight retention,
without packing, external density or universal-convergence assumptions.
For a known convergent v, D(v)=sum_(h<tau(v))(1-W_h(v)). A uniform
pre-arrival cost over pairs with q=3n+2 known to converge is equivalent
to bounded D on the convergent unit basin. It implies a uniform linear
arrival-clock bound there. The affine family n_j=8(10*64^j-1)/9 has
pre-arrival cost tending to 243/1600 but parent losses during that
interval tending to zero. A separate 404-bit convergent source exceeds
its COMPLETE future parent-loss budget with multiplier one, by more
than 1/200. Larger complete-future multipliers and averaged bounds are
not excluded. If the supremum is instead over ALL finite prefixes
before either endpoint reaches one, its finiteness is equivalent to
universal convergence PLUS bounded D on the unit basin. This stronger
condition is unproved, and is not asserted equivalent to Collatz alone.
The known-basin and unrestricted suprema must not be confused.

The preceding result localizes the conditional power obstruction
to G_k^+=sum_s(B_s-A_s)_+^2. Under universal convergence its pth moments
still have cumulative lower growth K^((p+1)/2), for p>1. This does not
force the corresponding downward or reversed costs to grow. For a
convergent pair, a sufficiently long negative arrival advance forces
current count reversal, giving J_k>=c^2/8 (D_--R)_+. There is also an
exact decomposition: J_k is comparable up to fixed constants and
nonfusion slack to H_k+D_-, where H_k is the reversed cost before
either endpoint reaches one. The pair n=823, q=2471 has equal first
arrivals at 86 but J_9=H_9=6289513358589/491370708992000>0. A pure
multiplier of the negative clock advance cannot bound all reversed
costs. Additive and averaged bounds remain open. No external theorem
is used in this refinement; the analytic conclusions remain written.

The preceding power result is explicitly CONDITIONAL ON UNIVERSAL CONVERGENCE.
Remaining first-arrival clocks have mean at least k/2 on the kth binary
band, while only O(k^-1/2) of binary edges can change them. Their pth
increment moments, summed through level K, must grow at least as
K^((p+1)/2) for p>1. The uniform positive first-hit weight floor then
gives the same growth for the complete accumulated squared gradients
G_k. Thus a uniform full-interval power bound above one is incompatible
with full Collatz. This does not settle power bounds on particular
returned progressions, density-weighted pairings, reversed negative
drift, uniform first moments, bounded E_s or Q. No external theorem is
used in this new conditional argument; its analytic steps are written.

The user resumed work after an accidental interruption. The preceding
argument strengthens the dyadic defect result to defects whose parent
already reaches one. Their harmonic source mass is infinite. A uniform
positive first-hit weight and the known-cycle Green factor four imply
Z_H(1), Z_H(2) -> infinity even using only those convergent even sources.
These are ALL-clock nonfusion traces, not the selected equal-count
return densities. Their earlier O(sqrt H) upper bound and vanishing
Cesaro means remain valid. Neither selected return trace is decided.
External PLD at one is the only density premise. Its 389 retained
objects and build logs were reauthenticated, and their recorded source
hashes match the retained archive inventory. The temporary external
source files are now absent; do not claim a fresh source audit or replay.
The new verifier handles this provenance distinction explicitly.

The preceding argument proves E sum P_j^theta (1+S_j)^q<infinity for
all nonfused returns when 0<=theta<1 and 0<=q<1/2. Group starts also allow
theta=1; restoring their common-parity runs uses Holder and requires
theta<1. The FULL lower-endpoint image density, including every overlap,
now belongs to Haar Lp for beta<1 and p<4/(3+beta). For beta=0 this
is every p<4/3. Its Lp clock-truncation error is O(H^-delta) for
delta<(4-3p)/(2p). The density differs from the original first-endpoint
K*_beta. No endpoint exponent, full L2, infinite-cutoff integer sampling
or actual-gradient bound is proved. The complete analytic argument is
WRITTEN; seven arithmetic roots and finite exact power checks passed.

The preceding argument includes every previously omitted one-step return.
The initially odd correction has finite entropy moment
E[b_F log_2,+ b_F]<=480. This controls the group-start mixed moment
P log_2(D+1), and hence the total smaller-endpoint coefficient over
ALL nonfused returns by A_star=2100000+281000000 C_star. Complete
clock/count component squared norms sum to at most 2 A_star.
Reusing the nested-source estimate leaves exactly the disjoint-source
cross terms between different components in this lower-image L2
decomposition. Their finiteness remains unproved. The original
fixed-endpoint density is different, and neither actual-gradient control
nor escape or other-cycle exclusion follows. Infinite entropy and
probability arguments remain WRITTEN; see the last dated entry.

**Current status: active following the user's resumption.** Collatz remains
unresolved. The external predecessor-density replay has passed all 389
modules and all three public theorem audits, with standard axioms only.
There is no live external replay to resume. Upper natural density one of
convergence would now suffice; it remains unproved. A further written
argument gives decay of target predecessor densities within each fixed
basin, but does not apply to a divergent forward orbit. Its finite fibre
and graph inputs have twelve new kernel proofs. The latest written
argument strengthens predecessor-density convergence to a supremum over
all targets, including moving targets, using eleven new kernel passage
lemmas. Uniform convergence does not make moving-target densities small;
a hypothetical divergent component can still carry positive mass to a
late target. The analytic density limits and rates remain written,
not kernel checked. The latest branch audit shows that a divergent orbit
would have summable unused-branch density ratios. A relative lower bound
of order 1/log(target) would exclude divergence but is unproved; an
absolute lower bound of order 1/target is summable by the existing
packing result and gives no contradiction by this argument. Exact finite
branch counts passed, without certifying asymptotic ratios. The latest
comparison-map audit now gives a concrete obstruction to deducing the
missing relative bound from those general properties alone. Its altered
odd branch allows half the starts to escape, with an explicit r_a>=1/(2a)
bound and diffuse first passage. Fourteen kernel theorems verify its
escaping family. This is not the Collatz map: its odd-parent arithmetic
and its behavior at multiples of three differ. The preceding
operator result still leaves decay of the constant starting function open.
The 128 existing finite-horizon contractions remain that route's full
certified scope. See the last entry for provenance and the remaining gaps.

The latest actual-Collatz arithmetic gives at most 38 distinct predecessors
at twelve ordinary steps, attained at target 364, and all-depth bounds.
Seventeen kernel theorems passed. Its written clock consequence is a
necessary lower bound about 3.29889 log X for hitting one target from a
fixed positive fraction of starts through X. It is not a sufficient clock.
The written density-spectrum argument identifies every positive
accumulation value of r_a with a divergent component's mass. Uniform
finite-time approximation with vanishing error remains unproved.

The newest clock result, conditional on the existing WRITTEN first-passage
mixing premise, gives tau_M(n)/log n -> kappa=3/log(4/3) in natural density,
approximately 10.42818. Here tau_M is first attainment of the actual global
minimum; it does not identify that minimum with one. Twenty-two kernel
theorems check minimum attainment and exact clock transfer, and independent
finite checks passed. The asymptotic statement is not kernel formalized.
For each fixed target, clock c log n captures zero limiting density when
c<kappa and its full predecessor density when c>kappa. The uniform
truncation defect at c log X tends to the largest component mass below
kappa and the largest divergent-component mass above it. Neither mass is
determined; the critical clock is also undetermined. In particular the
fixed clock 11 log X captures the one-target density p_1. Proving this
finite-clock proportion tends to one would imply full Collatz via external
PLD, but p_1=1 remains unproved. Nontrivial cycles and escape remain open.

The newest audit shows why full-period coalescence counts do not supply
that missing initial-interval estimate. Seven kernel lemmas prove exact
reflection between the plus and minus shortcut maps and identical
adjacent weighted coalescence counts at every depth, although the minus
map has the separate cycle 5,7,10. The earlier fibre bound gives an
unconditional written limit zero for cycle entry at depth k averaged over
1..2^k; the conditional logarithmic-clock limit on 1..X remains p_1>0.
The actual interval occupies a vanishing fraction of its parity period.
This is a limitation of the tested route, not evidence that p_1=1 or a
counterexample to Collatz. Fresh builds and exact finite replay passed.

The latest comparison strengthens the earlier altered-map obstruction:
swapping only O(log X) odd inputs through X preserves even halving, the
known cycle, allowed odd-image congruences, at most two parents, and
zero predecessor density at multiples of three. Kernel basin inclusions
inherit external PLD at every unit target, giving positive lower density
of both convergence and escape for this DIFFERENT map. A written early
coupling preserves the conditional large-floor passage estimates and
fixed-depth parity laws. Twenty main kernel theorem roots passed fresh
builds. The exact odd-parent values change at the swapped images; the
actual Collatz conjecture is still unresolved. See the last entry.

The latest actual-map calculation assigns loss W/(3n+1) at each odd
input and retains weight W*3n/(3n+1). Eighteen main kernel roots check
finite conservation, affine product identities, and geometric cycle
repetition. The written packing bound makes infinite remaining weight
positive exactly on divergent orbits. Conditional written passage
mixing gives a total-variation limit of the whole loss distribution,
including an infinity atom d. Its exact mass identity is
  d + sum_(N positive odd) B_N*D_N/(3N+1) = 1,
with weighted first-hit means D_N and cycle factors B_N. External PLD
makes d=0 equivalent to universal eventual periodicity, but d=0 is
unproved and additional cycles are still allowed. Under the prior
written clock theorem, the mean remaining weight at c log X tends to
one for c<3/log(4/3) and to d for larger c. Exact finite clock means,
including c=11, do not determine d. See the newest entry for scope.

The newest actual-map result proves that the stopped absolute difference
of adjacent odd counts has mean one over every full parity period, even
after conditioning on either initial input parity. Twenty-three audited
kernel roots yield an unmerged fraction at least 1/H at every depth H.
Thus whole-period balanced-coalescence errors cannot be summable; the
fair-bit fusion time has infinite mean. A stronger central-binomial
lower bound and a conditional dyadic criterion for d=0 are written.
Summability of the ACTUAL infinite-weight refinement changes remains
unproved and is not disproved by this lower bound on a larger finite-time
exception set. No external coalescence-density theorem was adopted.

The latest follow-up now proves that the actual eventual-unbalanced
even-pair fractions B_k are themselves nonsummable, using positive lower
density of the known basin from the replayed external theorem. It uses
no natural-passage premise. Eighteen kernel roots prove grade transport,
a strict pre-arrival contraction, and a three-odd-step cap for balanced
descendants of one. Written counting shows that uninterrupted balanced
refinements from any convergent root occupy zero limiting fraction.
If full Collatz holds, almost every binary path still has infinitely
many unweighted grade defects, although its infinite weights are all
zero. Thus the unweighted sufficient criterion has a false premise;
the actual WEIGHTED refinement criterion remains open. See the last
entry for the external dependency, finite scope, and verification.

The newest follow-up gives a quantitative unconditional mean bound for
the auxiliary V: mean(V_T, n<=X) <= (14/3)*X^(-log_2(8/7)) for every
T>=ceil(log_2 X), and the same bound for V_infinity. Thirteen new kernel
roots prove the finite affine identities and all-depth moments; the
source split, real power bound, and limit identification are WRITTEN.
No external PLD or passage assumption is used for this bound. Auxiliary
dyadic amplitudes are consequently summable almost surely. The exact
duality V_T*W_T=(3/4)^a does NOT give an upper bound on the escape weight.
Under the prior written natural component law and replayed PLD, any
divergent orbit would force infinite squared dyadic variation of W_infinity
almost surely. No upper bound proving finite such variation is established.
Fresh local builds and finite checks through depth 20 passed. Neither
escape nor other cycles are excluded; see the newest entry for details.

The newest actual-weight audit defines time-matched binary refinements
H_(s,k)=2^k*W_(s+k)(floor(2^k*x))/floor(2^k*x). Twenty-one kernel roots
give exact child formulas, reciprocal affine moments, and a fixed-offset
family of individual jumps >=27/512 at arbitrarily fine levels. A WRITTEN
tail makes E_s=sum_k integral|H_(s,k+1)-H_(s,k)|^2 finite for each s,
with E_s<=3s/2+23/4. Exact finite rational checks plus that written tail
give E_0<1/7 and E_16>1/4: the energies do not contract monotonically.
The required bounded subsequence as s tends to infinity remains unproved.
A WRITTEN real-scaling rigidity argument now removes the natural-passage
premise from the sufficient limiting-energy criterion. Binary stabilization
of a Collatz-invariant indicator gives a measurable limit invariant under
both x->2x and x->3x, hence a constant zero-or-one limit and natural density.
The positive gap of W_infinity converts finite squared variation into
such stabilization for the divergence indicator. Replayed PLD then excludes
escape if that finite-energy premise holds. No finite-energy premise is
established for W_infinity, and other positive cycles remain open.

The latest coalescence refinement improves the WRITTEN all-offset bound
to E_s <= (28401483/52428800)*s+6 <= 0.542s+6. Seventeen new kernel
roots give exact source-annulus transport, later equality of refinement
data, and the cutoff ceil(121s/50); independent direct counts through
depth twenty supply its constants. The strongest levelwise combination
of full-period noncoalescence caps and the existing geometric tail has
an upper-bound certificate that grows at least harmonically (using the
kernel tail), and at square-root order (using the written walk bound).
These are NOT lower bounds on E_s. Thus deeper counts alone cannot
prove bounded energy; the actual weighted contribution of unmerged
pairs still needs control. The even pair 6,7 first has equal odd counts
at positive time eleven but never merges at a common clock, and a
whole residue class has the same finite absorption-without-fusion defect.
The bounded subsequence and all other full-Collatz gaps remain open.

The newest actual-weight argument bounds the total negative refinement
drift before a reversal of the adjacent odd-count order by fourteen,
summed over ALL time offsets and binary levels. Thirty-one new kernel
roots prove shifted-weight order, first-return endpoint order, reciprocal
moments, positive-offset transitions, and exactly k+1 one-turn parity
prefixes on each depth-k source annulus. The classification induction,
source-height cutoff, and real sum are WRITTEN. The negative contribution
after a count reversal remains uncontrolled. An exact family at offset
six makes its downward product tend to 81/1024 while the immediate parent
time losses tend to zero, so no fixed pointwise charge of that kind can
cover it. The family cells have summable lengths and do not refute an
integrated bound. All fresh builds and independent checks passed; the
full escape and other-cycle gaps remain open. See the latest entry.

The newest clock argument uses the exact valuations of `3^d-1` and a
finite symmetric-walk Green function to give the WRITTEN uniform
first count-return tail `7/sqrt(H)`. The existing finite return-cycle
budget then gives balanced noncoalescence of order `H^(-1/2)` and
actual refinement energy `E_s=O(sqrt(s))`. Fifteen new kernel roots
check arithmetic inputs; the probability and energy arguments remain
written. The return-separation power budget now holds for every
`0<beta<1/3`. A separate written first-return family has separation four
and unbounded multiplier `(243/256)*(3/2)^m`, ruling out a constant bound
on raw aggregate image coefficients, but not on the actual weighted
gradients. The square-root order matches the previously proved lower
order of the coalescence-only upper-bound certificate, not a lower bound
on actual energy. Bounded actual energy and full Collatz remain open.

The newest return-image argument gives WRITTEN logarithmic moments for
the ternary density K_beta weighted by return separation: it lies in
L(log L)^alpha whenever beta>=0, alpha>0, and 3beta+2alpha<1. Twelve
new kernel roots verify prefix-weight bounds, endpoint caps, and integer
residue-count discrepancy. The resulting truncated density bounds also
hold on actual finite integer intervals, with an explicit depth/length
error. These do not permit an infinite cutoff at a fixed interval or
bound pairing with the actual future weighted gradients. The actual
energy estimate remains O(sqrt(s)), and Collatz remains unresolved.

The newest boundary-stop argument improves those WRITTEN return moments
to every power below 1/2. The affine correction has drift 1/4; combining
bounded stopping with the gap-boundary clock bound and Fatou gives
Pr(B_tau>L)<=7/(2 sqrt(L)). For returned separation from initial D,
Pr(D'>L)<=(D+6)/sqrt(L). Twelve new kernel roots check the actual
numerator and finite stopping identities and constants. The improved
cycle budget is E N<=540*2^5180. The return-image logarithmic-moment
region is now beta+alpha<1/2, and its Haar truncation error is at most
7 H^(beta-1/2)/(1-2 beta) for 0<=beta<1/2. All infinite probability
and real-analysis steps remain written. The pairing with actual weighted
gradients and bounded energy remain unproved; Collatz is unresolved.

The newest all-return argument gives the WRITTEN exponential cycle
moment E[(1+2^-5192)^N]<=2^5182. This counts cycles, not physical time.
The occupation measure over every nonfused return has clock and
separation tails O((1+log H)/sqrt(H)), giving L(log L)^alpha control
of the accumulated ternary density K*_beta for beta+alpha<1/2.
Its Haar truncation rate is O_beta((1+log H)H^(beta-1/2)). Fifteen
new kernel roots also show that the persistent family first returns
at (clock,count,separation)=(6,2,1), then has an arbitrarily costly
second excursion pointwise. Averaging remains necessary. The actual
future-gradient pairing, bounded energy, escape, and other cycles
remain unresolved; all infinite probability steps remain written.

The newest actual-gradient result rules out uniform moments
exp((G_m/C)^p) for p>1 and fixed C, on both actual returned intervals
and their progressions. The persistent family makes G_m grow linearly
at one point while the interval length grows exponentially. Eight new
kernel roots support this written norm obstruction. Thus a single
uniform complementary Orlicz norm after summing time contributions
cannot use the earlier L(log L)^alpha density estimates with alpha<1.
Ordinary averaged energy is not shown unbounded. The next result
improves the available density moments and changes the complementary
estimate that could suffice; it does not invalidate this obstruction.

The newest binary-image argument now gives the WRITTEN theorem
K*_beta in Lp for 0<=beta<1/2 and 1<=p<10/(9+2beta), counting all
nonfused returns. Eleven new kernel roots prove affine-numerator
injection on each image fibre, the exact numerator mass t*4^t/4,
and the required polynomial arithmetic. Written fibre counting yields
||rho_t||_2^2<=(t+1)(t+4)/2, hence a 3H^2 norm bound for the
all-return truncation. Its existing L1 tail then gives the Lp theorem
by dyadic interpolation. This permits every finite logarithmic moment
order for each beta<1/2. Truncated pth moments transfer to integer
intervals with factor 1+3^H/M. No bound for the actual gradient pairing
or bounded-energy subsequence follows yet; Collatz remains unresolved.

The newest temporal argument gives a weaker WRITTEN conditional escape
criterion: for every fixed k, the time average of N^rev_(s,k) tends
to zero, with no uniformity across source levels. This would make the
limiting refinements nondecreasing and their limiting energy at most
1/2. An explicit convergent inverse spine now removes PLD from this
particular implication: its normalized growth has a positive limit,
so irrational rotation makes its binary significands dense. Every
binary cone therefore contains a known predecessor of one. A positive
limiting weight cannot be closed under both binary children, proving
zero limiting weights under the proposed condition. The condition
is unproved for all levels. Twelve new kernel roots and exact full
future-time checks on fifteen finite annuli passed. Neither absence
of escape nor exclusion of other cycles has been established.

The latest density improvement controls the cumulative affine coefficient
C_t=(3^a_t+N_t)/2^t at ALL nonfused returns. Its continuation identity
C_next=lambda*C_current+b and the existing conditional return moments
give a finite summed C^eta budget for every eta<1/2. Fractional fibre
counting and binomial concentration then prove the WRITTEN improvement
K*_beta in Lp for 0<=beta<1/2 and 1<=p<6/(5+2beta), in particular
p<6/5 when beta=0. Eight new kernel roots and exact finite checks passed.
For the unweighted density, a complementary power above six could now
suffice; neither that actual-gradient estimate nor the required ordinary
integer sampling bound is proved. The temporal criterion Q and both
parts of full Collatz remain unresolved. See the last dated entry.

The newest return-slope argument proves WRITTEN exact mean slope 1/2
for every odd fresh separation, conditional on either initial parity;
the even-separation one-step mean is one. For odd separation, the
initially odd endpoint's correction has mean at most 5/4, while the
initially even correction and returned separation have infinite means.
The first even-source nonfused return already forces K*_beta outside
Haar L1 for beta>=1. Below one, the improved fresh correction budget is
72/(1-eta), and occupation tails are O((log u)^2/u). Weighted clock
truncation improves to O_beta(H^(-(1-beta)/2)(1+log H)^(1+beta)).
Nine kernel arithmetic roots and exact finite checks passed; all
infinite stopping and probability arguments remain written. No external
analytic theorem is needed. The optimal density p exponent, actual
gradient estimate, escape exclusion, and other-cycle exclusion remain
open. See the last dated entry for verification and the precise law.

The newest occupation argument proves WRITTEN bounds of 44 for the
expected sum of cumulative slopes over every count return, and 70 for
the sum weighted by each return's excursion length, from adjacent inputs.
Terminal fusion and all one-step returns are included. The conditional
tilted odd-separation return clock has mean at most 27; grouping the
even-separation returns gives a killed logarithmic drift. This yields
finite total individual-column squared Haar mass, but does NOT bound
the cross terms in the squared norm of the full return density.
Thirteen new kernel arithmetic roots and exact finite checks passed.
No external analytic theorem is needed. The earlier infinite first
separation moment remains valid; these are different weighted budgets.
The actual forward-gradient estimate and Collatz remain unresolved.

The newest overlap argument proves WRITTEN finite total cross energy
for nested binary source prefixes. The return-conditioned tilted clock
has second moment at most 6369; squared logarithmic drift gives
E sum_j Lambda_j log_2(D_j+1)<=12383. An original-law restart from
separation D has mean fusion count at most C_star+100 log_2(D+1)+2.
Consequently the diagonal plus nested-source cross energy is at most
88 C_star+2476820, with C_star=540*2^5180. The complementary overlaps
between disjoint binary source cylinders remain uncontrolled. Twelve
new kernel arithmetic roots and exact finite energy decompositions
passed; the infinite arguments remain written. No external analytic
theorem is used, and no full L2 or actual-gradient bound is established.

The newest lower-endpoint argument proves WRITTEN finite total mean
coefficient over nonfused ends of odd-separation excursions. Clipping
the initially even correction at lambda*D costs at most 12log_2(D+1),
despite its infinite untruncated mean. Grouped minimum drift gives
coefficient budget 4100+36000C_star, and quotient injection bounds the
sum of ENTIRE fixed-clock, fixed-count lower-image squared norms by
8200+72000C_star. Eleven kernel arithmetic roots and exact finite checks
passed. These norms include internal disjoint-source cross terms.
Changing endpoint labels preserves pairwise squared gradients but
changes the density; grouping omits the intervening one-step returns.
Cross-component overlaps and a complete actual-gradient estimate remain
open. No full L2, escape or additional-cycle exclusion is established.

This file records continuity, not an additional mathematical proof. Check
current source files and their verification manifests before relying on a
specific result. The historical session transcript has already been analyzed;
the current repository contains substantial subsequent work.

## Objective and honest status

The long-term objective is a proof or disproof of the positive-integer
Collatz conjecture. No complete proof or positive-integer counterexample has
been found. Follow the latest user request when deciding what work to do next.

Two broad possibilities still require exclusion: nontrivial positive integer
cycles and nonperiodic divergent orbits. Ruling out the remaining mechanical
mask family would not by itself settle either broader problem completely.

On 2026-09-13 the user asked whether progress felt nearer 30% or 70%.
The assistant's explicitly subjective answer was nearer 30%, possibly below,
as a description of the maturity of the approach. This is **not** a measured
completion percentage, a probability of success, or a mathematical result.
We have useful restrictions but no convincing complete proof strategy with
only a few manageable gaps. Preserve this candid assessment rather than
inferring that a proof is imminent from the user's encouragement.

## Working preferences and environment

- The user wants continuity with the research direction in
  [codex-session-transcript.md](codex-session-transcript.md), rather than
  repeatedly restarting the initial analysis. Search relevant transcript
  sections when needed; current corrected notes supersede historical claims.
- The user stages and commits during ongoing work. HEAD and the index can
  change between commands. Inspect status, preserve their work, and leave
  staging/committing to them unless they explicitly request otherwise.
- Current workspace (2026-10-21):
  `/home/jeannaude/Documents/collatz-conjecture--expansion`, Linux, bash,
  timezone Africa/Johannesburg. Earlier macOS descriptions in dated
  entries are historical. Allow longer Rust/Lean runs. On 2026-10-21
  the user explicitly authorized increasing Lean threads for speed;
  the latest verifier uses16 threads per process, with dependent builds
  in sequence. A short tool timeout is not a mathematical or build failure.
- The user has cloned `/Users/jean/Personal/collatz-two-coordinate-obstruction`.
  Prefer this local source for further review. On 2026-10-13 its clean HEAD
  was `a7275d5a73814d3d9a400c6fe6577de9542b03a3`. The local review and
  exact source/finite-check scope are in `docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md`.
- [lean-toolchain](lean-toolchain) pins `leanprover/lean4:v4.33.1`.
  The last verified compiler commit is
  `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
  The latest verified executable is `/tmp/lean-4.33.1-linux/bin/lean` on
  Linux; this temporary path may need restoration in a later session.
  The installed elan directories had4.33.0 and4.31.0, and `lean` was not
  on PATH. The new verifier accepts `--lean /path/to/lean` and enforces
  version4.33.1 and the recorded commit. Recheck Rust if needed.
- The research Lean modules use standalone Lean without Mathlib or a Lake
  project. Build imported `.olean` files into a temporary directory and
  supply that directory through `LEAN_PATH`.
- The user said the local `.env` contains a `SUDO` credential and authorized
  its use for necessary package installations. The password itself has not
  been copied into this memory. Access it only when needed for an authorized
  installation; never echo it, embed it in visible command arguments or
  artifacts, or stage the file. Recent research checks needed no installs.

## Where to resume reading

1. [ATTEMPT.md](ATTEMPT.md): overall status, exact gaps, and reproduction.
2. [README.md](README.md): module map and links to verification records.
3. [MASK-RANK-ARITHMETIC.md](docs/MASK-RANK-ARITHMETIC.md): latest completed
   arithmetic step and its limitations.
4. [CYCLE-LOCAL-LIFTS.md](docs/CYCLE-LOCAL-LIFTS.md): preceding general
   obstruction to residue-consistency-only arguments.
5. [MASK-SPAN-BOUND.md](docs/MASK-SPAN-BOUND.md) and
   [EXPLICIT-LOG-GAP.md](docs/EXPLICIT-LOG-GAP.md): stronger written span
   restriction and explicit analytic/finite inputs.

## Established structure and remaining gaps

- [CollatzContradiction.lean](CollatzContradiction.lean) proves convergence
  equivalent to eventual strict descent for every start above one. A least
  counterexample must lie in residues `{7,15,27,31,39,43}` modulo 48.
  Universal descent in those infinite classes is still unproved.
- [CollatzCycleCriterion.lean](CollatzCycleCriterion.lean) gives a kernel
  necessary-and-sufficient test for every nonempty positive halving word:
  `D=2^H-3^k>0` and `D | W`, where
  `W=sum_i 3^(k-1-i) 2^(h_0+...+h_(i-1))`.
  Intermediate integrality, positivity, oddness, and exact valuations are
  proved. The criterion permits repetitions of the known cycle.
- Packing, ballot, growth, and repeated-prefix results constrain divergent
  trajectories but do not exclude all of them. Relevant notes include
  [ORBIT-PACKING-BOOTSTRAP.md](docs/ORBIT-PACKING-BOOTSTRAP.md),
  [ORBIT-PACKING-LOG.md](docs/ORBIT-PACKING-LOG.md), and
  [NO-DESCENT-BALLOT.md](docs/NO-DESCENT-BALLOT.md).
- The mechanical distance work excludes the specified cycle words through
  nearest half-Hamming distance 31. Full critical `21→12` mask families
  contain positive rational cycles far beyond that distance; rational
  realization does not establish integer realization.
- [MechanicalMaskArithmetic.lean](lean/MechanicalMaskArithmetic.lean)
  proves `W_mask = D + 4C-X`, with `0 ≤ X ≤ C`, for tokenized independent
  `21→12` edits. Integrality is exactly `D | (4C-X)`.
- [MaskSubsetDecoder.lean](lean/MaskSubsetDecoder.lean) proves complete
  decoding of the possible integer subset targets. Native finite
  certificates reject all `2^80` masks at `(k,N)=(193,306)` and all
  `2^1231` at `(2966,4701)`. This is not an all-count theorem.
- The repository's written resonance/logarithm arguments exclude the full
  critical mask family through `N=10^4000`, using the recorded finite cover
  and external small-period input. They also exclude the specified pure
  `22→13`, alternating `21→12`, and no-adjacent-halving-ones subclasses at
  every period. The all-index analytic proofs are written, not wholly
  formalized; read [the scope record](results/explicit-log-gap/verification.json).
- The narrow-cycle classification is a written reduction of primitive
  integer cycles satisfying `3M+1<8m` to critical masks. Here `m,M` are
  the minimum and maximum odd states. The stronger written all-period
  conclusion is `20M>49m` for nontrivial integer cycles, with the
  dependencies in [the span record](results/mask-span/verification.json).
  These inequalities do not exclude arbitrary wider cycles.
- Automatic folded rank order holds for the surviving close count regime.
  It is compatible with arbitrary positive rational mask forcing, so
  ordering alone does not reject the remaining masks.

## General local lifts: completed preceding step

[CycleLocalLifts.lean](lean/CycleLocalLifts.lean) proves that every nonempty
positive halving word with `D>0` has positive odd integer edge witnesses
forming a closed residue walk modulo every `2^a 3^b`, for `a>0,b≥0`.
The actual accelerated map at each witness has the prescribed exact
halving exponent. Successive chosen witnesses need agree only modulo the
chosen modulus, not as integers.

This theorem does not assume `D | W`. Therefore pure residue consistency
at powers of two and three cannot reject any such word. A complementary
kernel lemma recovers integer divisibility when a fixed height bound makes
the congruence an equality. This does not invalidate the residue sieve,
which retains actual descent inequalities.

The explicit modulus-64 walk is `43→33→57→43`, with integer edge witnesses
`107,161,57`. Their actual successors are `161,121,43`, so these witnesses
are not an integer cycle.

[Verification](results/cycle-local-lifts/verification.json) records kernel
proofs and independent checks of 2,883 small words at four precisions,
75,016 actual integer edges, and four larger masks.

## Latest result: mechanical rank normalization

Sources:
[MaskRankArithmetic.lean](lean/MaskRankArithmetic.lean),
[written argument](docs/MASK-RANK-ARITHMETIC.md),
[independent replay](verify_mask_rank_arithmetic.py), and
[verification manifest](results/mask-rank-arithmetic/verification.json).

For coprime counts `k,N` with `k>1`, `3k≤2N<4k` and `D=2^N-3^k>0`:

- Set `s=2k-N`. Cut the lower mechanical halving word after its first
  symbol. Eligible pair midpoints have ranks `j=0,...,s-1`.
- Choose `qN=kt+1` and `z=2^t(3^q)^(-1) mod D`.
  Then `2z^k=1`, `3z^N=1`, and `4z^s=3` modulo `D`.
- In this rank order, `c_j=2^(N-2)z^j mod D`.
  If `G_s=1+z+...+z^(s-1)`, then `4(1-z)G_s=1 mod D`.
  Hence the total coefficient satisfies `gcd(C,D)=1`.
- With `E(z)=sum_j epsilon_j z^j` and `epsilon_j∈{0,1}`, the exact mask
  condition becomes `(1-z)E(z)=1 mod D`.
  This is an equivalent reformulation; no all-mask exclusion follows yet.

The modular algebra, explicit phase/exponent implication, unit-to-gcd
conversion, and equation equivalence are kernel checked. Full mechanical
floor/permutation reindexing and specialization are written bridges.

Written consequences include the exact gcd formula for repeated mechanical
words and recovery of the unedited mechanical-cycle exclusion. A separate
written lemma says that `M-1` arbitrary unit coefficients modulo `M`
have subset sums covering every residue. Thus tests at divisors of `D`
with combined least common multiple `M≤s+1` cannot reject every mask.
Separate smallness of each divisor is insufficient for this conclusion.
The combined modulus matters.

Large multiplicative order does not imply linear independence of powers.
The checked example `k=11,N=18,D=84997` has divisor 11 and `z=6 mod 11`
of order 10, but `4+3z+4z²+3z³=814` vanishes modulo 11.
The corresponding mask fails divisibility by the full denominator.

Latest fresh verification used sequential Lean 4.33.1 builds of
`CollatzCycleCriterion`, `CycleLocalLifts`, and `MaskRankArithmetic`.
All passed without warnings, admitted proofs, or native evaluation.
Only standard logical axioms were printed.
The Python replay passed 42,158 rank-coefficient checks, rejected 30,436
exhaustively enumerated masks at the recorded small coprime critical
count pairs, and checked further masks, repeated-word gcds, and modular
coverage instances. File hashes and local links were checked.
No Rust code changed in this latest research step.

To reproduce just this step:

```sh
rank_build_dir=$(mktemp -d /tmp/collatz-mask-rank.XXXXXX)
lean -o "$rank_build_dir/CollatzCycleCriterion.olean" CollatzCycleCriterion.lean
LEAN_PATH="$rank_build_dir" lean -o "$rank_build_dir/CycleLocalLifts.olean" lean/CycleLocalLifts.lean
LEAN_PATH="$rank_build_dir" lean lean/MaskRankArithmetic.lean
python3 verify_mask_rank_arithmetic.py
```

## Known implementation issues and research cautions

Two tooling issues were reproduced during the initial analysis and remain
unfixed in the code inspected on this date:

- [src/bin/residue-sieve.rs](src/bin/residue-sieve.rs): canonical-path
  comparison misses distinct hard links to the same inode. Aliased
  certificate and manifest destinations can overwrite the certificate.
- [bench/compare.py](bench/compare.py): the certificate path from a
  historical manifest can be an absolute path from the previous Mac.
  The check-only path then fails on Linux.

These are separate from the current mathematical research. Recheck their
current status before fixing them.

Keep these distinctions explicit when continuing:

- Distinct subset sums as ordinary integers need not be distinct modulo `D`.
- Compatible local residues and positive rational cycles are not integer cycles.
- An equivalent normalized equation is not a new exclusion.
- Finite bounds, however large, do not measure distance to a universal proof.
- Kernel lemmas do not automatically certify the written analytic or
  combinatorial arguments that use them.
- Progress on a restricted cycle family does not settle wider cycles or
  nonperiodic divergence.

The next research advance must address the remaining full-denominator
equation or add an argument covering every positive-integer orbit. Fixed
small-modulus consistency alone has the limitations recorded above.
Treat this as a direction to investigate, not a promised proof strategy.

## Persistence mechanism

[AGENTS.md](AGENTS.md) points future repository sessions to this file.
Repository-level AGENTS.md discovery is documented in
[the official OpenAI instructions guide](https://learn.chatgpt.com/docs/agent-configuration/agents-md).
This is explicit file-based project memory, not a claim that a separate
account-level memory service was updated.

## 2026-10-08 update: current workspace and coalescence

The September environment and latest-result descriptions above are historical.
The current workspace is `/Users/jean/Personal/collatz-conjecture--expansion`,
macOS with zsh and the same Lean 4.33.1 pin. The user pulled remote research;
merge commit `23e746a` integrated it. The requested conflict check found no
unmerged index entries or conflict markers. Preserve untracked `.DS_Store`
and `CLAUDE.md`; the latter prohibits Git writes without explicit consent.
No staging or committing was performed during this work.

[CoalescenceDescent.lean](lean/CoalescenceDescent.lean) now kernel proves:

- Convergence is equivalent to every `n>1` meeting an orbit from some
  `0<m<n`, with potentially different meeting times. Strong induction
  transfers convergence from the smaller start.
- Exact affine certificate soundness, combining direct descent and
  equal-time/equal-weight merging of residue classes.
- The complete depth-eight table covers 240/256 classes, compared with
  237 for direct descent alone. New residues are 63, 207, and 223.
  A least counterexample must belong to the remaining 16 residue classes
  listed in Section 9 of APERIODIC-ATTEMPT.md.
- For every fixed horizon K there is a start above one that cannot meet
  any smaller natural start within K steps on either orbit. The theorem
  allows unequal times and is a universal kernel proof, not an inference
  from finite testing. It does not provide one orbit that never merges.

The key obstruction uses `2^K | n+1` and `3^K | n`. For a hypothetical
meeting `U^(c+a)(m)=U^a(n)`, split the smaller orbit into a prefix with
odd weight i and a suffix with odd weight h. The suffix's maximal additive
bound and exact all-odd growth force its start to be at least
`3^(a-h)*n`. Divisibility by `3^i` and the discrete orbit bound then pull
this back to `m >= 2^c*T`. The lower additive bound yields `A <= B`, where
`A=3^(i+h)` and `B=2^c*3^a`, and therefore `m>=n`.
The formal existence proof recursively cubes `n+1`, starting at n=3,
to increase both divisibilities. No CRT library or outside theorem is needed.

[verify_coalescence.py](verify_coalescence.py) independently checks 1,198
large and small lifts of the depth-eight certificates. At depths 12, 16,
and 18, coalescence adds 44, 394, and 1,391 classes respectively beyond
direct descent at the same depth. These larger counts are Python-only.
An exhaustive inverse-tree replay for horizons 1 through 24 checks 716,286
nodes and 571,137 shifted-start identities. All passed.

Reproduction and hashes are in
[results/coalescence/verification.json](results/coalescence/verification.json).
Build CollatzAffine, CollatzContradiction, and CollatzGrowth into LEAN_PATH
before building the new module. No admitted proofs or native evaluation
are used in this module. The universal Collatz claim is still unresolved.

The immediate research implication is that coalescence is a sound broader
induction tool, but a fixed bound on both orbit lengths cannot close it.
Further work must give a genuinely start-dependent argument or another
global constraint. Do not mistake the 16 remaining residue labels for
a finite set of unresolved integers.

## 2026-10-08 follow-up: horizon versus input size

[CoalescenceHeight.lean](lean/CoalescenceHeight.lean) imports the preceding
module and proves that its witnesses can be chosen with
`3^K <= n < 6^K` for every K≥1. Reduce the constructive large witness
modulo `2^K*3^K`; the two divisibilities survive, and the residue is
nonzero. This gives a universal logarithmic lower bound on the necessary
meeting horizon along an unbounded sequence. It does not disprove a
logarithmic upper bound, which remains unproved.

The same module proves an exact example with no cap on the smaller orbit:
for 0<m<27, a<59, and every b≥0, `U^a(27) != U^b(m)`.
All smaller starts lie in the 34-element invariant set
`{1,...,26,29,32,35,38,40,44,53,80}`, disjoint from the first 59 states
of the orbit of 27. At time 59 it reaches 23. The first coefficient
drop is also 59. These are kernel proofs without admitted terms or
native evaluation.

[verify_coalescence_height.py](verify_coalescence_height.py) independently
checks the invariant set and CRT representatives for horizons 1–256.
It also computes exact minimum values of max(a,b) for smaller-start
meetings for n=2,...,32768, searching through 192 steps. Every start
finds a meeting, making the minimum exact within this finite range.
The largest observed ratio to ceil(log2(n)) is 59/5 at 27. This supplies
no universal upper bound. The verification manifest is
[results/coalescence-height/verification.json](results/coalescence-height/verification.json).

The attempted bridge from first multiplier drop to smaller coalescence
remains unproved. The direct-descent version is the coefficient stopping
time conjecture already recorded in CollatzAffine.lean; the new work must
not silently assume it. A universal finite first-drop theorem is also
missing. Section 10 of APERIODIC-ATTEMPT.md records these gaps and the
primary literature reference. The objective remains the full conjecture.

## 2026-10-08 follow-up: bidirectional ranks

The next attempt allowed a rank to decrease along either a forward or
inverse Collatz edge. Strong induction on a natural-valued rank, plus a
finite verified base, would prove the full conjecture. This sufficient
criterion is kernel proved in
[CoalescenceEnvelope.lean](lean/CoalescenceEnvelope.lean).

The same module strengthens the CRT-class obstruction to exact inequalities:
if `U^a(n)=U^b(m)`, a,b≤K, `2^K | n+1`, and `3^K | n`, set
`A=2^a*3^wt(b,m)` and `B=2^b*3^a`. Then `B*n <= A*m` and
`A*(m+1) <= B*(n+1)`. Thus `m=q*n+c` with `q=B/A >=1` and
`0<=c<=q-1`. Both time orderings are kernel checked. Independent Python
replay checks 716,286 inverse nodes.

[search_graph_ranks.py](search_graph_ranks.py) uses exact Z3 linear-real
constraints for `R(n)=a_r*n+b_r`, r modulo M, with positive slopes.
It allows neutral leading slopes with strictly negative constant change,
and arbitrary finite exceptional ranges. All 22 tested moduli through
the recorded maximum 144 returned unsat. These are SMT results, not Lean
certificates. The user approved downloading z3-solver into
`/tmp/collatz-rank-solver`; version 5.1.0.0 was installed with uv. No
repository environment or dependency file was changed. Use PYTHONPATH
pointing there, or install that package in a chosen environment for replay.

Section 11 of APERIODIC-ATTEMPT.md gives a broader written obstruction:
no rank selected from a finite set of positive-slope affine formulas can
offer a decreasing adjacent edge at every sufficiently large integer.
The assignment of formulas need not be periodic. This complete theorem
is written, not fully Lean checked. Its proof uses the kernel envelope:
a strictly decreasing path is forward then backward (no reversal after
the first inverse edge), and its normalized leading rank stays between
the smallest and largest palette slopes. Strict leading drops have a
fixed multiplicative gap; neutral oriented runs cannot revisit a formula,
since that would require `2^length=3^odd_count` with positive length.
These give a fixed path-length bound contradicted by a sufficiently
deep, sufficiently large CRT start.

[results/coalescence-envelope/verification.json](results/coalescence-envelope/verification.json)
records all scopes, hashes, builds, independent replay, and SMT outcomes.
The full conjecture remains unresolved. The finite-affine bidirectional
rank template is exhausted by the written obstruction; repeating that
search at larger moduli is not a useful next step. Nonlinear ranks or
unbounded arithmetic features are not excluded by this theorem.

## 2026-10-08 follow-up: four-feature valuation ranks

APERIODIC-ATTEMPT section 12 gives a written exclusion of every bounded-below
rank `C log₂n+a ν₂(n)+b ν₂(n+1)+c ν₃(n)+d ν₃(n+1)`, `C>0`,
that supplies a decreasing shortcut-graph neighbor at all sufficiently
large integers. Along `3·2^k`, boundedness below forces `C+a≥0`.
Use a single shared `L=C log₂(3/2)`, with `7C<12L` and `5L<3C`.
Treating forward and inverse logarithms as independent bounds can create
false feasibility; the shared variable is essential.

Five stable progression patterns, with seeds 131,134,137,142,147 and
moduli 432,1296,216,864,72, give exhaustive neighbor alternatives.
Their odd forward limit conditions are strict; odd inverse conditions
are weak because the true ratio tends to 2/3 from below. All 108 ways
to select an alternative contradict the common background inequalities.
Each contradiction has nonnegative integer weights with identically zero
coefficient sum and a positive weight on a strict inequality.

[ValuationGraphRank.lean](lean/ValuationGraphRank.lean) kernel-checks the
five universal feature/edge progression lemmas, the two logarithm-bound
power comparisons, and all 108 finite certificate identities and selection
coverage. The all-real weighted-sum interpretation and logarithmic limit
argument are written bridges. No full real-valued rank theorem is claimed
as kernel formalized. The independent
[verifier](verify_valuation_graph_rank.py) reconstructs the constraint rows
and checks the integer certificates without Z3. Files and hashes are in
[the verification record](results/valuation-graph-rank/verification.json).

Boundedness below alone does not ensure termination of a decreasing
real-valued rank; finite sublevel sets would be a sufficient extra condition.
Here even the local decreasing-edge property fails under the weaker
bounded-below assumption. This does not exclude arbitrary nonlinear
functions of valuations or additional features. Exploratory larger-feature
SMT results were not promoted to verified universal theorems. The full
Collatz objective remains unresolved and active.

## 2026-10-08 follow-up: proper nonlinear and quadratic ranks

An unrestricted nonlinear bounded-below rank is not enough:
`R(n)=log₂n-ν₂(n)+2^(-ν₂(n))` is positive and decreases on every doubling
edge. Along powers of two it tends to zero. A useful real rank needs a
well-founded decrease condition; finite sublevel sets (properness) suffice.

[GraphRankNecessity.lean](lean/GraphRankNecessity.lean) proves that any
natural-valued graph rank with local descent beyond N has
`R(2n)>R(n)` and `R(U(n))<R(n)` for every `n>N` divisible by three.
Such n have no odd predecessor. If doubling failed to increase rank,
local descent on the degree-two doubling ray would force an infinite
strict rank descent. The Lean proof uses strong induction on the rank.
The written extension to proper real ranks takes a rank minimum on the
ray, whose sublevel sets are finite.

APERIODIC-ATTEMPT section 13 uses this graph restriction to exclude every
proper `C log₂n+P(ν₂(n),ν₂(n+1),ν₃(n),ν₃(n+1))`, C>0, with P of total
degree at most two. Let the variables be x,y,z,w. Terms xy and zw vanish
identically. Properness plus the graph restriction forces coefficients
of x² and y² to vanish. For linear coefficients A of x and B of y and
cross coefficients G_yw,G_xw, necessary inequalities are
`C+A≥0`, `B≤0`, `G_yw≥0`, `A+G_xw≤0`. The written proof also derives
G_yz=0, but the finite contradiction does not need that constraint.
These restrictions use explicit unbounded valuation families, not a
finite sample inference. A finite quadratic fit otherwise evades every
sample by placing its eventual turning point beyond the tested range.

Six stable patterns at seeds 151,153,155,170,230,233, plus those inequalities
and `12L>7C` for L=C log₂(3/2), contradict all 162 possible edge selections.
At seed 153 the forced forward condition replaces bidirectional choice.
Nonnegative integer certificate weights have maximum 36. No numerical
logarithms or trusted SMT answers enter the final replay.

[QuadraticValuationRank.lean](lean/QuadraticValuationRank.lean) proves all
six universal feature/edge progressions and checks all finite certificate
identities and their exhaustive selections. The independent
[Python verifier](verify_quadratic_valuation_rank.py) reconstructs the
quadratic differences and checks all 162 certificates. The universal
properness/coefficient/logarithm argument and weighted-sum interpretation
over reals remain written bridges; this is not a full Lean real-rank theorem.
The [manifest](results/quadratic-valuation-rank/verification.json) records
fresh builds, logs, hashes, and exact scope.

Do not repeat the quadratic synthesis search without a new feature or
changed hypothesis: this whole proper template is excluded by the written
argument. General nonlinear functions, additional features, and unrelated
global proof strategies remain open. No full proof or counterexample has
been found; the original Collatz goal stays active.

## 2026-10-08 follow-up: graph orientation and the broader rank obstruction

[GraphRankOrientation.lean](lean/GraphRankOrientation.lean) proves a generic
functional-graph theorem: if S is forward closed and a well-founded relation
offers a decreasing adjacent neighbor outside S, then the forward successor
itself decreases outside S. Well-founded induction: a smaller predecessor
outside S must decrease back to the original vertex, a forbidden two-cycle.
The generic theorem and its asymmetry lemma have no axioms.

For a Collatz proof with a **verified convergent finite base** 1..N,
enlarge the base to its entire forward closure plus zero. This is finite,
closed, and bounded by some B. Any natural graph rank, or proper real graph
rank, therefore decreases forward at every integer above B. Bounded-below
real ranks alone do not suffice. Existence/boundedness of this closed base
must not be assumed for an unverified arbitrary N.

Combining with section 8's exact growing path
`192s-5 → 288s-7 → 432s-10 → 216s-5` gives a kernel obstruction for
natural ranks monotone between matching four-valuation/residue features.
Take s a sufficiently large multiple of the modulus so the whole path
lies above B. The endpoints have valuations (0,2,0,0), equal residues,
and increasing size, contradicting forced forward rank decrease.

APERIODIC-ATTEMPT section 14 combines the generic orientation theorem with
section 8's written all-polynomial valuation construction. The written
corollary excludes **any** size-monotone well-founded graph rank built from
a fixed finite set of polynomial valuations at finitely many primes and
fixed-modulus residues, with a bounded closed base. In particular, proper
`C log₂n+G(features)` ranks are excluded for arbitrary nonlinear G, C>0.
This closes the larger proof strategy rather than only quadratic formulas.
Unlike the earlier quadratic exclusion, this argument explicitly uses
bounded forward closure of the exceptional base; keep that hypothesis.

The proper-real well-foundedness bridge, constructing the finite closure
from verified base convergence, and the full polynomial-feature corollary
are written. The general well-founded graph theorem and natural-rank
four-feature obstruction are kernel proved. The independent replay checks
six closed finite bases through 32768 and 42 growing witnesses above their
maxima. [Manifest](results/graph-rank-orientation/verification.json).

Do not continue enlarging polynomial degree or adding finitely many
polynomial valuation features to this size-monotone graph-rank template.
For this proof strategy these changes are excluded by the written corollary.
Other magnitude dependence, different information, or a non-ranking global
argument remains open. The actual Collatz objective remains unresolved.

## 2026-10-08 follow-up: separated binary blocks

The next attempt used binary digit counts, outside the preceding finite
polynomial-valuation theorem. Weighted counts of zero-padded windows
failed exact SMT synthesis at widths 1–9. The final proof does not trust
SMT: four families supply an all-width positive-weight cancellation.

For a window width w, pad the usual binary word on both ends by w-1 zeros.
A score `R(n)=β+α bitlength(n)+Σ λ_v count_v(n)` satisfies
`R(2n)=R(n)+z`, z=α+λ_zero, and for a,b>0 with k-bitlength(b)≥w-1,
`R(a·2^k+b)=R(a)+R(b)+(k-bitlength(b))z-c`,
c=β+(w-1)λ_zero. The written counting proof separates windows meeting
the two blocks; only the extra all-zero windows remain.

For q=2^k and sufficiently large k, the edges and rank differences are:
`2q+2 → q+1`: -z;
`2q+21 → 3q+32`: R(3)-R(21)+3z;
`6q+9 → 9q+14`: R(7)-R(3);
`14q+1 → 21q+2`: R(21)-R(7)-z.
The first requires z>0; the other three sum to 2z. Their weighted sum
with weights (2,1,1,1) is zero, so strict decrease on all four is impossible.
All sources grow without bound. No finite exception range fixes this.

[DigitBlockRank.lean](lean/DigitBlockRank.lean) kernel-proves the four
edges and no eventual forward descent for any integer score satisfying
the two structural laws, at any fixed gap threshold. The window-count
interpretation for all widths and extension to real scores are written
bridges in APERIODIC-ATTEMPT section 15. The independent replay checks
widths 1–64, minimum and larger gaps, and the exact feature-vector
cancellation up to exponent 4096. [Manifest](results/digit-block-rank/verification.json).

This also excludes well-founded graph ranks of this form with a bounded
forward-closed verified base, by section 14. Do not overgeneralize:
independent prefix/suffix corrections, nonlinear counts, distant-block
interactions, and varying return times are not covered. The particular
zero-padding/additivity hypotheses matter. No Collatz proof or positive
counterexample has been found; the full goal remains active.

## 2026-10-08 follow-up: inverse basins versus orbit packing

Do not compare an inverse-basin lower bound directly with the project's
orbit-packing upper bound. The latter requires a forward-closed set with
injective U. A branching inverse basin does not satisfy that hypothesis.

[InverseBasinAudit.lean](lean/InverseBasinAudit.lean) proves:
for 3|a, B(a) is exactly {2^k a}; for 3∤a, explicit distinct positive
basin points have the same immediate image and reach a within two steps.
Every forward-closed injective subset of B(a) is a chain under forward
iteration, by cancellation of equal iterates. In B(1), such a subset
contains only 1 and 2; the last theorem has no axioms. This shows why
even large basin cardinality does not provide the injective orbit count
needed for a contradiction. No universal nonconvergent-basin upper bound
or sufficient injective-chain lower bound has been established.

The chain conclusion is also proved for forward-closed injective subsets
of the full coalescence component C(a)={n: some iterate of n equals some
iterate of a}. For a nonperiodic a, B(a) contains no nonempty forward-closed
subset at all: closure would include U(a), whose return to a would make a
periodic. This additional closure issue is kernel checked. Switching to
C(a) restores forward closure but not injectivity or branching counts.

The literature check used the original Krasikov–Lagarias paper
https://arxiv.org/pdf/math/0205002 only for scope: its x^0.84 count is an
inverse-basin count for roots coprime to three, not a single-orbit count.
No claim about the current best exponent is made.

Search metadata for arXiv:2512.13760 still showed v1's claimed x^0.946
improvement, but the current v2 (17 December 2025) reports x^0.3227.
The audit kernel-checks a counterexample to v1 Lemma 2.2: u=(3,1) allows
v1=5 or 6 and v2=1 or 2, none satisfying its congruence modulo nine.
It also checks failure of uniqueness as stated in v2 Lemma 3.1: at level
one and u1=2, exponents 8 and 10 both meet the displayed conditions and
yield 85 and 341. This does NOT refute the weaker final density bound
or every possible repaired argument. Neither version is a dependency.
Use versioned primary links in APERIODIC-ATTEMPT section 16, not stale
search snippets, for these claims.

The independent Python replay checks 21,846 small-root collisions, six
large roots, 325 dyadic basin examples, and the congruence examples. The universal structure results
are kernel checked separately. [Manifest](results/inverse-basin-audit/verification.json).
The full Collatz conjecture remains unresolved and the goal remains active.

## 2026-10-08 follow-up: quantitative fibre multiplicity

The largest fibre of U^k among residues below 2^k **at a fixed parity
weight** has size D_k at least
`max_j ceil(binom(k,j)/3^j) ≥ ceil(4^k/((k+1)3^k))`.
There are binom(k,j) weight-j parity residues and only 3^j possible images.
For the second bound multiply binom(k,j)≤D_k 3^j by 3^(k-j), sum, and
use the binomial theorem. This all-depth proof is written, not fully Lean.
It excludes any constant, polynomial, or subexponential universal bound
on this multiplicity; it does not give an upper bound or the exact rate.

[InverseFibreGrowth.lean](lean/InverseFibreGrowth.lean) proves weight
periodicity under shifts by 2^k, and equivalence of same-weight fibre
equalities between all aligned blocks. It certifies 48 distinct positive
residues r below 65536 with wt(16,r)=4 and U^16(r)=2. For every q≥0,
65536q+r therefore share weight four and endpoint 81q+2. No convergence
claim about arbitrary shifted endpoints is made.

The Python replay enumerates all 2,097,150 residue inputs at depths 1–20,
checks binomial histograms and exact weighted identities, and determines
the finite maxima: 48 at depth 16; 140 at depth 20 (weight 5, endpoint 47).
Maximality is Python evidence; the Lean certificate only proves the
48-member family and its universal lifts. It also replays 288 shifted
certificate members, including large quotients.
[Manifest](results/inverse-fibre-growth/verification.json), APERIODIC-ATTEMPT section 17.

This rules out fixing the previous inverse-basin packing mismatch with
a uniformly small collision multiplier. It does not show that any of
these large fibres lie in a nonconvergent component. A bound using special
properties of an exceptional component, or a different global argument,
is still missing. Do not equate generic fibre growth with Collatz failure.
The full objective remains unresolved and active.

## 2026-10-08: external method review and fixed-root branching

The user suggested https://github.com/openai/math as methodological inspiration.
APERIODIC-ATTEMPT section 18 records the targeted review and source links.
The main leads are: explicitly account for information lost by collisions;
investigate scale-dependent trapping with variable return times; and audit
conditioning and quantifiers rather than replacing every-start claims with
almost-everywhere statements. No external theorem from the collection is
adopted as a premise. Its mass-action scope covers initial-state-dependent
bounds, not necessarily the stronger later common absorbing-set statement.
Comparator challenge `sorry` placeholders are statement specifications;
separate solution modules are selected by their JSON configurations. We
did not build those external solutions or validate all manuscript proofs.

The previous suggestion that exceptional components might avoid large
collisions is now excluded for unrestricted fixed-root fibres.
`lean/UniformInverseBranching.lean` proves that for every a%3≠0, its binary
inverse tree has 2^h distinct positive unit leaves n with time 6h, weight h,
endpoint a, and 3^h*n≤64^h*a. Children are 192*(a/9)+d with pairs
r1:(16,20), r2:(32,40), r4:(80,85), r5:(104,106), r7:(148,149),
r8:(160,170). They arise by synchronizing the two valid inverse exponents
in 1..6; every child is greater than its parent and reaches it in six steps.

Written corollaries: if a<3^h all leaves are below 2^(6h); a bad root
would make every leaf bad; a uniform leaf distribution loses exactly h
bits when mapped to its common endpoint. Every hypothetical counterexample
eventually has a unit iterate, so this applies to every hypothetical bad
component. Do not confuse this with an upper bound, with entropy of whole
affine maps, or with a count along one orbit. Basin1 has these trees too.

`python3 verify_uniform_inverse_branching.py` passed 6,679 root checks,
36,846 leaf checks, and three fresh Lean builds. The manifest is
`results/uniform-inverse-branching/verification.json`; APERIODIC section19.
Lean's printed dependencies have no sorryAx or native evaluator axioms.
The all-depth counting, distinctness, weight, endpoint and height bound
are kernel checked; the entropy and exceptional-component interpretations
are written. Full Collatz remains unresolved; the goal stays active.

Local merge audit at this point: HEAD7590f75, tracked tree initially clean,
no unmerged index entries, no MERGE_HEAD, and no conflict markers found
in the source/document scan. `.DS_Store` and `CLAUDE.md` were untracked
and were preserved. No staging, commits, pull or other Git mutations.

## 2026-10-08: residue shadows and the scale-dependent certificate gap

The previous goal turn was progress: universal binary inverse trees were
kernel verified. This turn examined what finite residue information can
contribute to the proposed variable-return trapping approach.

APERIODIC section 20 proves in writing that every positive unit root a
has arbitrarily large ancestors in every residue class modulo `2^A*3^B`.
Choose positive n in the class and k≥A with n<2^k. Then j=wt(k,n)>0
and y=U^k(n) is coprime to three. Solve a2^e≡y mod3^(j+B), increase e by
period `2*3^(j+B−1)` until Q=(a2^e−y)/3^(j+B)>0, and put
N=2^k3^B Q+n. The affine identity gives U^k(N)=a2^e, hence
U^(k+e)(N)=a; increasing e gives arbitrarily large N. A full elementary
modular-lifting proof is included via `4^(3^s)=1+3^(s+1)c_s`, with `c_s≡1 (mod 3)`.

Consequently, convergence of all sufficiently large members of ANY one
fixed mixed residue class would imply full Collatz. If a counterexample
exists, both convergent and nonconvergent starts occur arbitrarily high
in every class. This is congruence/topological density, not positive
natural density. It does not refute whole-class descent certificates or
scale-dependent arithmetic certificates. The ancestors can be enormous;
no smaller predecessor or quantitative trapping estimate follows.

`lean/BasinResidueShadow.lean` proves unit preservation and the exact
transport identities conditional on the displayed power equality, plus
capture by a forward-closed set containing that cylinder. Universal power
lifting, density and the one-class equivalence are WRITTEN, not kernel
proved. No admitted theorem/extra axiom supplies existence.

`python3 verify_basin_residue_shadow.py` passed 3,276 ancestor checks,
2,184 modular lifts and three fresh Lean builds. Four unit roots include
2^128+1; all residue classes with A=0..5 and B=0..2 are checked. Largest constructed
ancestor: 39,098 bits. Pure-halving tails use the separately kernel-proved
identity rather than enumerating every halving. Manifest:
`results/basin-residue-shadow/verification.json`.

Next research still requires an actual size-sensitive progress estimate
for variable return times. Repeating the density argument or merely
restating a descent equivalence would not supply that estimate. Both
nontrivial cycles and divergent orbits remain unresolved; goal active.

## 2026-10-08: quantitative residue transport and fixed-prefix cost

Previous goal turn classified as progress: the mixed-residue construction
and conditional transport were checked. This turn quantified its size
and tested whether it could produce smaller values for induction.

APERIODIC section 21: fix positive representative n<2^k, j=wt(k,n)>0,
y=U^k(n), J=j+B, T=2*3^(J-1), 2^L>y, E=L+T-1. The minimal
admissible power exponent e satisfies e≤E for every unit root a. The
constructed ancestor F(a) reaches a by time k+E and obeys
3^j F(a)+D=2^(k+e)a, D=2^k y-3^j n>0; hence F(a)≤C a with
C=2^(k+E)/3^j fixed for the cylinder. On odd roots the map is injective,
because 2^e a=2^f c forces a=c. This transfers counts from the odd unit
part of any predecessor-closed set to every cylinder without changing
the count exponent. It does not apply directly to a single forward orbit.

For the FIXED prefix followed only by halvings, the sharp worst
asymptotic multiplier is C*=2^(k+T-1)/3^j>1. Infinitely many odd roots
in a fixed class modulo3^J force e=T-1. Every prefix intermediate has
slope at least (4/3)^j>1 as a function of these roots; the halving tail
stays at least a. For sufficiently large roots in that class, the whole
constructed path contains no value below a. This excludes using the
same construction alone as a universal descent certificate. It does not
exclude other inverse paths or prefixes chosen adaptively for each root.

`lean/ResidueShadowCost.lean` kernel-proves conditional size bounds,
odd dyadic uniqueness, shadow injectivity and that the prescribed prefix
ends at least as high as its root. Universal modular existence, counting
transfer, sharp asymptotics and intermediate-slope argument are WRITTEN.
`python3 verify_residue_shadow_cost.py` checks 42,532 ancestors, 343
odd roots across 124 cylinders, and 248 sharp witnesses with complete
path checks. Four fresh Lean builds pass; standard propext/Quot.sound
only in printed dependencies. Manifest: `results/residue-shadow-cost/verification.json`.

Next work must supply a genuine progress estimate, potentially through
root-dependent path selection. A fixed-cylinder linear upper cost is
not a contraction, and count transfer alone does not defeat the basin
versus injective-orbit obstruction. Full objective unresolved and active.

## 2026-10-08: adaptive inverse paths on unit roots

Previous turn was progress: the fixed-prefix cost was quantified and
checked. This turn permitted every inverse path within a chosen depth.
`lean/AdaptiveInverseBarrier.lean` kernel-proves the exact positive
inverse level at a=3^K*q+1 for k≤K:
m=r+2^k*3^(K-j)*q, with 0<r≤2^k, U^k(r)=1, j=wt(k,r)=wt(k,m).
Use the unique positive remainder r modulo 2^k, whose image is in
[1,3^j]; the image's congruence to 1 modulo 3^j forces it to equal 1.
The converse affine lift is proved too, and 3^j*r≤2^k gives m≥a.
Strict m>a for q>0,k>0 is a written corollary. Hence even the odd
unit roots 2*3^K+1 have no smaller ancestor within K inverse steps.

APERIODIC section 22 additionally proves in writing: if n>1 is 1 modulo
3^K and −1 modulo 2^K, no m<n has U^a(n)=U^b(m) with a,b≤K.
For b≥a, c=b−a, z=U^c(m), i=wt(c,m), h=wt(a,z), P=3^i,
d=3^(a−h), the old intercept bounds give d*n≤z≤d*(n+1)−1.
If P≤d, scaled-image bounds give m≥n. Otherwise P≥3d; positive
residue reduction of m modulo 2^c gives s=U^c(r) in [d,2d−1] and
the exact quotient Q=d*3^(K−i)q where n=3^Kq+1. If 2^c*d<P,
the coefficient bound forces r=1. Its cycle {1,2} forces d=s=1,
contradicting P>2^c*d. Thus 2^c*d≥P, yielding m≥n. This extends
the earlier nonunit CRT obstruction to unit roots. For K≥2 the least
CRT witness lies between 3^K and 6^K, giving logarithmic lower bounds.

The inverse-level statement is KERNEL checked; the unit-root two-sided
extension and logarithmic consequence are WRITTEN. Do not merge their
verification scopes. `python3 verify_adaptive_inverse_barrier.py`
checks 30,188 inverse ancestors for 80 roots through depth 20, then all
397,752 inverse nodes for 72 two-sided witnesses through K=18. Five
fresh Lean builds pass. Manifest:
`results/adaptive-inverse-barrier/verification.json`.

The obstruction concerns bounded depth, even with adaptive branch
selection. It does not exclude unbounded rules whose depth grows with
input size. No such universally successful rule or other complete proof
has been found. The Collatz objective remains unresolved and active.

## 2026-10-08: openai/math review II, citation correction, mask barrier

A review of openai/math in update order found no manuscript on Collatz.
Its μ(π)=2 method was adapted on 2026-10-08 to μ(log α)=2 for rational α
(github.com/jdb19937/log-irrationality-measure). That paper explains why
ratios such as log₂3 are out of reach (Baker regime), so it gives no input
for cycles.

**Superseded source assessment:** this review incorrectly concluded that
Wu–Wang proves only μ(log 3) ≤5.1163051 and removed the three-term
theorem attribution. A subsequent primary-source check, recorded below,
confirms that Theorem 1 is precisely the three-term bound. The original
attribution and the historical verification records were correct on that
point. EXPLICIT-LOG-GAP still supplies the explicit cutoff used later.

An independent exact replay (even n=2..14) confirmed EXPLICIT-LOG-GAP's
partial fractions, zero residue at −1, Q_n·B_n integrality, A_n bounds
and A_n log z + B_n(z) = 70J_n, 70(J_n+K_n). The bound implies
μ(log₂3) ≲ 5.2. The claim that no stronger published bound was found is
superseded: Wu–Wang's Theorem 1 implies μ(log₂3) ≤5.1163051. Do not
suggest that the local 5.2 consequence is a new irrationality record.

Barrier, now in EXPLICIT-LOG-GAP §8: the unrestricted 21→12 family has
selection entropy h → 0.26186, so the distinct-factor route needs c < 2.8188,
an effective μ(log₂3) < 3.8188. Do not spend effort shaving c below 4.2.
Neither cycles nor divergence is resolved; the objective remains active.

## 2026-10-08: half-multiplier descent certificate

The previous bounded-depth obstruction led to a positive sufficient
estimate, now kernel checked in `lean/HalfSlopeDescent.lean`.
Let A_t=3^wt(t,n)/2^t. If A_t≥1/2 for t<k, then
`3*2^k*U^k(n)≤3^wt(k,n)*(3*n+2*wt(k,n))`. Each odd step adds
1/(3A_t)≤2/3 to U^t(n)/A_t. At a first half crossing this gives
`U^k(n)≤n/2+wt(k,n)/3`, hence descent if `2*wt(k,n)<3*n`.
The additive terms are included and no first-coefficient-drop claim
is used. Any half crossing K≤n for n>0 implies some descent by K,
by selecting the first crossing and using weight≤K≤n.

`conjecture_of_half_certificate` proves that a convergent base through
N plus such crossings for every n>N would imply full Collatz. Its
universal crossing premise is NOT proved, nor claimed necessary.
Kernel certificates include n=27,k=65,w=40,endpoint10,budget80<81,
and n=1,k=6,w=3,endpoint1, which demonstrates the need for the budget.

`python3 verify_half_slope_descent.py` passes six fresh Lean builds,
all starts 1..32768 and 3,072 CRT-family cases through depth512.
No search exhausts its fuel. Only n=1 fails the odd-step budget in
the interval; none of the family cases fail it. The stronger k≤n
fails at interval starts1,3,7,27,31,41,47,55 and five family cases.
These are exact finite Python checks; they stop at the half crossing,
not necessarily at one. Universal statements and two example
certificates are kernel checked without native evaluation or sorryAx.
Manifest: `results/half-slope-descent/verification.json`; explanation:
APERIODIC section23. No mathematical novelty is asserted.

The universal early-crossing estimate remains the substantive gap.
A universal logarithmic bound would suffice eventually, but is not
known here. Both cycles and divergence remain unresolved; goal active.
Local merge audit: no unmerged index entries, no MERGE_HEAD, no source
conflict markers, and `git diff --check` clean before these additions.
Existing logarithm-note corrections and untracked local files were
preserved. No staging, commits or other Git writes were performed.

## 2026-10-08: source recheck and a first-drop polynomial budget

Previous goal turn was progress: the half-margin theorem, builds and
replay were completed. This turn examined the missing crossing argument.
The current packing and first-passage estimates still permit exponential
escape; no new contradiction from those estimates was established.

A primary-source recheck corrected the intervening literature edit.
Wu–Wang, JNT142 (2014), DOI10.1016/j.jnt.2014.03.007, Theorem1,
DOES bound |p+q1 log2+q2 log3| by H^(-4.1163051-epsilon) beyond an
effective threshold. The publisher's indexed theorem statement was read;
the full proof was not independently formalized. Its log3 irrationality
measure is a corollary, not the paper's entire scope. The earlier
"misattribution" correction was incorrect. MASK-CYCLE-OBSTRUCTIONS,
MASK-TRANSITIONS, MASK-DENSITY, EXPLICIT-LOG-GAP and ATTEMPT now reflect
this, and the superseded memory entry is marked. In particular, the
local 5.2 consequence is not a new irrationality-measure record.
The catalog limitation in EXPLICIT-LOG-GAP is also explicitly phrased
as a limitation of those upper bounds, not of every counting method.

New `lean/FirstSlopeBudget.lean` kernel-proves, for a first coefficient
drop k, w=wt(k,n), A=3^w,D=2^k,G=D-A>0:
`3*D*U^k(n)≤A*(3*n+w)` and descent if `A*w<3*n*G`.
More generally, `A^q<k^p*G^q` and `k^(p+q)≤(3*n)^q` imply descent.
The (p,q)=(21,5) specialization uses `k^26≤(3*n)^5`.
No logarithm theorem is imported as a Lean axiom or proved there.

Written bridge in APERIODIC§24: lambda=log(D/A)≥k^(-21/5) implies
G/A=exp(lambda)-1>lambda and therefore the integer power gap above.
Wu–Wang gives this eventually. EXPLICIT-LOG-GAP supplies the explicit
cutoff k≥10^4000; every first drop k≥5 satisfies its cone
11w≤7k and k<2w (full elementary argument in§24). Thus
n≥k^(26/5)/3 guarantees descent at such a first drop. No existence or
upper-time bound for every start has been proved. This complements the
half-margin criterion; neither is asserted necessary or uniformly stronger.

Kernel example n30913060423816076283,k65,w41 has multiplier about.989,
endpoint30560730293104027237, and passes the exact power criterion.
n27,k59 descends but fails the simpler sufficient gap budget.
`python3 verify_first_slope_budget.py` passes six fresh Lean builds,
all starts1..32768 and969 prescribed near-critical first-drop/lift cases
throughk512. No fuel exhaustion. Gap-budget passes32764 interval starts
(failures1,27,47,63) and968 family cases (failure1). Power certificates
pass13184 and933 respectively. These are finite Python counts, not
universal stopping proofs. Manifest: results/first-slope-budget/verification.json.
All printed kernel dependencies are standard logical axioms; no sorryAx
or native evaluator axiom. The Collatz goal remains unresolved and active.

Concurrent work added the natural-density note recorded below. This
first-drop turn read it but did not independently validate its transfer
of Tao's joint mixing, uniform-start stabilization, or final iteration.
Those analytic steps are a useful next audit target; its finite numerical
checks cannot certify the universal density theorem. Preserve that work
and distinguish its written claim from the kernel results above.

## 2026-10-08: natural-density almost bounded orbits (written)

Jean asked for "project 3": upgrade Tao's log-density theorem to natural
density. docs/NATURAL-DENSITY-ALMOST-BOUNDED.md gives a written proof of
`#{N≤X: Col_min(N)>N₀} ≪ X(log N₀)^(-c)`, hence almost bounded minima
outside a natural-density-zero set. There are two new ingredients:

1. Tao's (74) takes absolute values after conditioning on b_j, so the
   tilt e(θ|a|) drops out (Lemma 2.1). This gives fine-scale mixing
   jointly with |a| (Proposition 2.3), which is his Remark 1.16 route.
2. A renewal lemma for {kβ}, β=log₂3, with weights P(S_k=⌈kβ+τ⌉). It
   uses the local CLT, Erdős–Turán–Koksma, and any finite irrationality
   exponent for β. The constant 1/ln(4/3) matches Tao's log formula.

Uniform starts U_y on [y,2y) replace log-uniform ones, and Tao's Section 3
iteration then runs verbatim.

The original `python3 verify_natural_density.py` run checked three things.
Tilted / product bound ≤ 0.913 for n=2..5. R(τ) was within 4e-4 of
1/ln(4/3) at four tested values above 300, not uniformly for τ≥300.
At x=2^40, the reported TVs compared coarsened Monte Carlo histograms,
not the full passage laws. The later audit below corrects the sampler
and numerical labels. These are sanity checks only; there is no Lean.
Unrefereed 2026 claims of the same upgrade exist, so novelty is not
asserted. Collatz itself remains unresolved, because the zero-density
exceptional set need not be empty. Goal active.

The earlier Wu–Wang "misquote" claim (review II above) is superseded by
the primary-source recheck. Astra's wording in the mask notes stands.

## 2026-10-08: natural-density audit and limiting minima

The previous goal turn was progress: the first-drop certificate and
source correction passed their checks. This turn audited the concurrent
natural-density note against Tao's v7 HTML, especially Sections 3, 5,
6 and 7. The paired conditioning removes the unit-modulus total-sum
tilt; the unnormalised sum slices then pass through the collision bound
and telescoping. No failure of this joint-mixing step was found.

The written note now supplies details needed for uniform-start transfer:
support of c_(n,s) implies 2^s/y≪x^(-.8); the renewal sum is bounded for
every real shift, including negative atypical shifts; and its Gaussian
mass is computed by an integral. The reduced-modulus harmonic bound is
proved with weights 2^(-A)(a_m+1), whose sum is 3. For A>H=.5 log₂x,
the extra term is bounded by 3^(2m)P(S_m>H)≤18^m(3/4)^H=o(1).
This avoids using the nonuniform coarse sum (sqrt(2)+1)^m. The strict
f(N) corollary now uses f/2, and the dyadic cover includes the final
partial block. Formula numbers and a reversed-word notation were fixed.

Proposition 4.1 holds uniformly for every y in [x^α,x^(α²)], not just
the endpoints: all size and renewal-centre estimates are uniform there.
New Section 6 deduces a further WRITTEN result. For fixed B, let
h_B(y)=P(Syr_min(U_y)≤B). For Y≥B^α and Y≤Z≤Y^α,
|h_B(Z)-h_B(Y)|≪(log Y)^(-c). Telescoping along Y^(α^j) makes h_B
Cauchy as y→∞. Dyadic summation and the even-part decomposition give
a natural density d_B for {Col_min≤B}. ND implies d_B→1, so the
differences p_m=d_m-d_(m-1) form a limiting distribution of minima.
This does not establish d_1>0 or d_1=1, and even d_1=1 would not prove
Collatz for every integer. No novelty or kernel verification is claimed.

The verifier now labels floating-point truncation and uncertified
roundoff, and the Monte Carlo TV applies only to the 108 defined bins.
Logarithmic samples are odd from the proposal stage and accepted by
integer rejection; under ideal uniform randomness this is exactly the
1/n law. The earlier sample-then-round-to-odd procedure was not exact.
Every trajectory has 10,000 Syracuse steps of fuel; exhaustion is
recorded as unresolved and fails the check. The rerun passed: 240,000
trajectories, none exhausted, maximum 322 steps; coarse pairwise TVs
0.014667–0.017483 versus same-law 0.015717. Tilt ratios and four renewal
values are unchanged. The numerical tests do not certify the theorem.

Git audit found no unmerged index entries, MERGE_HEAD, or source
conflict markers. Existing changes and the index were preserved; no Git
writes were performed. The OpenAI collection remains methodological
inspiration (APERIODIC§18), not an imported Collatz proof. The full
objective is unresolved and remains active.

## 2026-10-08: total variation, component masses, and a false external axiom

The preceding goal turn was progress: it audited the natural-density
argument and repaired its verifier. This turn checked the route from
that result to individual exceptions. New docs/DENSITY-TO-POINTWISE.md
proves a stronger WRITTEN consequence of the same Proposition 4.1.
If first passage below x is finite, the global orbit minimum equals
the minimum of the passage state. Data processing therefore transfers
stabilisation to the entire law of the minimum, uniformly over all
subsets of possible minima. Telescoping across Y^(α^j) gives a Cauchy
bound O((log Y)^(-c)) in total variation. Finite support at one scale
proves the limiting measure p has total mass one. Dyadic decomposition
and conditioning on ν₂ give the same rate for all starts up to X.
This also proves Theorem ND directly from first-passage stabilisation,
without a separate adaptation of Tao's Section 3 iteration.

Pushing p through the component label π(minimum) gives countably
additive natural densities for coalescence components and their unions.
At least one component has positive density; the union of zero-density
components has density zero. Divergent starts also have a natural
density. None of these densities is evaluated, and p_1>0 or p_1=1
is still unproved. Even assuming p_1=1 yields only X/(log X)^c bad
starts, compatible with the external Krasikov–Lagarias lower bound
X^0.84 for an eligible root's inverse basin. A bound o(X^0.84) for
the ENTIRE bad set would instead rule out every exceptional component.
The primary paper's abstract was rechecked; its computational proof
is not locally replayed. No claimed 0.901 improvement was imported.

A source search encountered AIDoctrine/CollatzLayerA's v8.1 claim of
a complete Lean proof. Its actual source declares odd_steps_certificate
as an axiom: all n≥2^71, n≡3 mod4 have a prefix k≤200 with ≤44 odd
and ≥71 even ordinary steps. This is FALSE. The new standalone
lean/BudgetAxiomAudit.lean uses the source's map/count equations and
kernel checks n=2^111−1=2596148429267413814265248164610047. For all
k≤200 its odd count is ceil(k/2), so the asserted budget never holds.
The witness exceeds even 2^109. Lean also checks it reaches 1 in1476
steps; it is not a Collatz counterexample. Printed dependencies are
only propext/Quot.sound where needed, with no foreign or native axiom.

python3 verify_budget_axiom.py passes a fresh standalone Lean build
and 105 exact finite family instances (L=101..132,201,512,1024;
q=1,3,5 in 2^L*q−1). Only the main witness's full trajectory is
replayed: first arrival1476, peak177bits, no fuel exhaustion. The
foreign repository was not built. Sources, scope and hashes are in
results/budget-axiom-audit/verification.json; explanation is in
docs/BUDGET-AXIOM-AUDIT.md. This excludes an invalid proposed shortcut
while leaving the universal descent problem open.

The user committed the preceding work during this turn; Git status
was rechecked and that new HEAD preserved. No Git writes were made.
The current verified compiler is Lean4.33.1, arm64-apple-darwin24.6.0,
/opt/homebrew/bin/lean, in /Users/jean/Personal/collatz-conjecture--expansion.
The earlier Linux environment entry is historical. Goal remains active
and unresolved; no external-state blocker prevents further research.

## 2026-10-08: user-requested pause and exact resumption point

The user explicitly stopped the research and requested this next task:
"examine a weighted counting approach that would rule out every orbit
staying above a verified finite range, if its required contraction bound
can be proved". The goal service confirms status PAUSED. The full
objective is unchanged and unresolved, not completed or blocked.

The interrupted weighted-counting turn only re-read current files and
searched existing notes. No weighted-counting computation, new theorem,
or kernel proof was completed. Its starting formulation is:

- Use the shortcut map U(n)=n/2 for even n and (3n+1)/2 for odd n.
- Fix a cutoff H for which convergence of every positive n≤H has an
  actual certificate. Let χ_k(n) indicate U^j(n)>H for every 0≤j≤k.
- For s>1 consider the finite weighted mass M_k(s)=Σ_n χ_k(n)n^(-s).
  The intended target is an eventual uniform contraction
  M_(k+1)≤ρ M_k with ρ<1, or another rigorous argument forcing M_k→0.
  Any eternal survivor would contribute its fixed positive weight for
  every k, so such a limit would exclude every survivor above H.
- First derive the exact predecessor identity, retaining the cutoff:
  M_(k+1)=Σ_(y>H) χ_k(y)[(2y)^(-s) +
  1_(y≡2 mod3 and (2y−1)/3>H)·((2y−1)/3)^(-s)].
  The odd-predecessor eligibility and its +1 correction must stay in
  the calculation. This is a proposed starting derivation, not an
  already verified contraction certificate.
- Do not assume residue classes are independent after conditioning on
  survival. Finite horizon estimates or finite experiments alone cannot
  establish the required all-future contraction. Check the existing
  rank obstructions before searching for fixed residue-dependent
  pointwise weights; an aggregate mass estimate is a different claim.

A possible external lead, read only at README level in the preceding
turn, is https://github.com/GettysburgResearch/collatz/blob/main/research/integrated/exceptional-mass/README.md .
It reports failure of a naive one-third weighted residue-share bound
and describes conditional alternatives. Those claims and calculations
have NOT been independently replayed here and are not proof inputs.
Read their exact definitions and source proofs before using them.

Resume from ATTEMPT.md, docs/DENSITY-TO-POINTWISE.md, and the latest
verification records. The density argument's pointwise gap and the
kernel counterexample to the external 200-step axiom remain as recorded
above. Existing local changes and untracked research artifacts were
preserved. No staging, commits, or other Git writes were performed.
All commands started in the interrupted turn had finished; no live
research process was identified at the pause.

## 2026-10-09: weighted survivor mass after resumption

The user resumed the full active goal. The preceding interrupted research
turn had only read files and searched notes; it made no mathematical
progress. This turn took the next safe action from that handoff and
completed the exact weighted-counting investigation below. No claim of
solving Collatz is made, and the goal remains active.

`docs/WEIGHTED-SURVIVORS.md` derives the exact predecessor identity for
`M_k(s)=sum_{tau_H(n)>k}n^(-s)`, keeping the odd-predecessor cutoff and
the factor `(1-1/(2y))^(-s)`. For a certified floor, M_k tending to zero
is equivalent to universal convergence. Define corrected residue mass
Qtilde and `kappa_s=(2^s-1)/3^s`. Nested survival proves the unconditional
strict bound `Qtilde_k/M_k<kappa_s`, but only summable lower bounds for
the relative loss are currently available. The full conjecture is
equivalent to divergence of the sum of these positive bias deficits.

Two WRITTEN implications sharpen the research target:

- An exponential envelope M_k<=C exp(-delta k) is equivalent to a
  universal O(log n) hitting-time bound for this fixed floor. A uniform
  eventual ratio contraction implies it; the converse gives an envelope,
  not necessarily contraction at every step.
- A fixed contraction at infinitely many horizons suffices, even without
  positive frequency. For H64,s3/2 and eligible endpoints y>=98,y=2 mod3,
  `Q_k<=69 M_k/200` at infinitely many k would settle Collatz. Each such
  horizon gives M_(k+1)<.993 M_k. Neither this recurrent bound nor the
  stronger eventual bound has been proved. Finite strict loss alone does
  not establish divergent total relative loss.

A separate WRITTEN all-odd-path argument excludes every pointwise killed
inverse supersolution comparable above and below to n^(-s), even with
arbitrary bounded multiplicative modulation and a non-strict factor one.
This leaves aggregate survivor-mass contraction open.

`lean/WeightedSurvivors.lean` KERNEL checks the exact killed inverse
branches, complete finite inverse-cone membership, the height bound
n<=2^k H, universal survival for n>2^k H, convergence of all positive
n<=64 within71 shortcut steps, the equivalence of full Collatz with
eventual absorption there, and the integer contraction comparisons.
It does not formalize infinite sums, analytic tails, or the all-time
estimate. Two fresh Lean4.33.1 builds pass with no warnings, admitted
proofs, or native evaluator axioms; only standard logical axioms appear.

`python3 verify_weighted_survivors.py` independently reconstructs the
external Mellin note's finite test using integer square roots, a common
denominator2^96, and simple directed integral tails at65536. It constructs
all37 complete inverse cones k0..36; k19 has18847 starts and k36 has
2510783. It certifies 3Q19>M19, refuting the naive one-third ceiling,
while all37 levels satisfy200Qk<69Mk. The largest share is at k34,
with outward decimal enclosure [.34110155,.34110313], checked against
the exact rational endpoints in replay.json. The more detailed printed
decimal values are display approximations, not proof inputs.

The numerical definitions and test were independently reconstructed from
https://github.com/GettysburgResearch/collatz/blob/main/research/astra-three-routes/ROUTE1_MELLIN.md .
No foreign code was run and no external convergence range was assumed.
Independent forward checks cover all n1..2^18 plus4316 larger frontier
members, totaling266460 starts. Sources, scope, logs, exact intervals and hashes are in
`results/weighted-survivors/verification.json`. The infinite-tail integral
inequalities remain written proofs, not kernel-certified analysis.

Next pursue an arithmetic reason that the critical bias deficits cannot
be summable, possibly by proving recurrent separation rather than a
uniform eventual gap. Neither unconditioned residue equidistribution nor
more finite levels establishes that premise. Both nontrivial cycles and
nonperiodic divergence remain unresolved. No staging or commits were
performed; earlier modifications and untracked files were preserved.

## 2026-10-09: backward closure cannot supply the aggregate contraction

The previous goal turn was progress: its source hashes and successful
build records were rechecked. This turn tested whether predecessor
closure, cofiniteness, and known absorption of omitted starts could force
the missing weighted gap. No blocker required user input.

New `docs/WEIGHTED-BASIN-BARRIER.md` gives a WRITTEN obstruction. Let
P A={n>H:U(n) in A}, mu(A)=sum_A n^(-s). For every H>=1,s>1, fixed
k>=0,r>=1 and rho<1 (rho>0), there is a cofinite backward-closed A with
S_T subset A subset S_k for some finite T, yet mu(P^r A)>rho mu(A).
Every omitted positive start provably hits the floor within T steps.
These populations need NOT equal any actual S_j. This does not refute
recurrent contraction along the actual survivor sequence.

The construction first uses K odd steps from x=2^K q-1 to b=3^K q-1.
For a convergent all-index family take a=3^(K-1), b=2^a, q=(b+1)/3^K.
The source then halves to one after reaching b, and x/b<=(2/3)^K.
Its killed ancestor basin B_b consists entirely of convergent starts and
has exact boundary B_b minus P B_b={b}. Hence relative mass loss is at
most(2/3)^(sK), arbitrarily small. The K9 witness uses b=2^6561 and a
6556-bit source, reaching one in6570 shortcut steps; its basin retains
more than.993 of its weight in one step.

For cofiniteness, remove only starts that reach H before hitting b or
[R,infinity). This removed set is finite and has a verified-by-construction
hitting bound R; cycles trapped below R are retained, never labeled
absorbed. The remaining exit set is contained in {b} plus even integers
in[R,2R). Choose R with sum_(n>=R)n^(-s)<=b^(-s). Fixed iterates of P
cost at most powers of Gamma_s=2^(-s)+2^s, so long enough rising prefixes
give the fixed-block obstruction and the sandwich S_(k+R) subset A subset S_k.
This infinite weighted analysis and the huge cofinite construction are
WRITTEN, not full Lean theorems or explicit giant enumerations.

A further WRITTEN restriction rules out every uniform loss profile
mu(A minus P A)>=c*mu(A)^p on this class when1<=p<log_2(3). Use fixed
q=H+2 and arbitrary K, without assuming convergence of that whole family;
the loss/mass^p ratio is at most a constant times(2^p/3)^(sK).
For H64,s=p=3/2,c1, a manageable witness uses K64,q66:
x=1217485108864830406655 and b=226623132139305823987418039892545.
The exact inequality16*x^9<b^6 and the choice R=4*b^3+1 refute that
profile. Both x and b themselves reach one in560 and496 shortcut steps.
No loss estimate with p>=log_2(3) is established or excluded here.

`lean/WeightedBasinBarrier.lean` KERNEL checks the universal basin
boundary/convergence statements, power-of-two nonreturn and convergence,
all-index divisibility3^(k+1) divides2^(3^k)+1, growth paths and ratios,
the K9 parameters and hitting certificate, and the finite power-profile
witness's arithmetic and convergence. The all-index division theorem
uses an elementary polynomial identity, with no external lifting result.
Only standard logical axioms occur; no admitted proofs or native checks.

`python3 verify_weighted_basin_barrier.py` passes four fresh sequential
Lean4.33.1 builds. It independently checks K1..12 arithmetic (largest
source177140 bits), fully replays the first10 trajectory certificates,
and checks the two profile-witness trajectories with first arrivals and
peaks. It builds12 moderate cofinite examples, directly replays49245
removed starts (with repetitions across examples), and makes611343
direct loss-layer membership checks. Every finite exit and five complete
inverse loss layers per example are checked. No trapped positive cycle
was found. The directed mass enclosures reuse the previous written
integral tail bounds; they are not Lean real-analysis proofs.
Manifest: `results/weighted-basin-barrier/verification.json`.

Next investigate information tied to the exact common clock S_k=P^k S_0,
or a weaker state-dependent boundary loss beyond the excluded powers.
Simply extending the static closure argument cannot justify the proposed
uniform gap. No such remaining estimate has been proved; both cycles
and divergence remain unresolved and the full goal is active. Existing
changes and the index were preserved; no staging or commits were made.

## 2026-10-09: finite trajectories give a time-independent entry correction

The goal remains active and unresolved. This turn extended the orbit-packing
argument to finite simple trajectories.
The preceding weighted-survivor and basin manifests were rechecked against
their source hashes; their successful heavy checks were reused.

New `docs/FINITE-PATH-PACKING.md` gives a WRITTEN uniform bound
`#(path values in [a,a+L)) <= 256 L^sigma`, sigma=H_2(log_3 2)<19/20,
for every finite prefix whose states are distinct. The prefix need not be
forward closed, and its later orbit may converge. At scale ell=ceil(log_2 L),
discard at most ell terminal positions. The other ell-step images remain
inside the same prefix and are distinct, so the previous strong induction
applies at each shorter image interval. Its low/high contributions are
less than 128 L^sigma and 64 L^sigma; the terminal cost is at most 2 L^sigma.
This also bounds the distinct value set of every individual orbit, but
does not bound a branching ancestor basin.

Dyadic shells give the WRITTEN estimate sum_(distinct v>=Y)1/v
<8192 Y^(-1/20). The exact integer inequality 32^20<2*31^20 supplies
the loose geometric-series constant. Before finite first entry below Y,
all states are distinct, the final step is even, and the landing y lies
in(Y/2,Y]. If h is the entry time and j the odd count, then
`n=(2^h*y/3^j)*R`, where
`R=product_(odd steps i)(1-1/(2*x_(i+1)))`.
All successors in this product are distinct and above Y. Therefore its
correction sum Lambda is less than epsilon(Y)=4096 Y^(-1/20), and
`1-epsilon(Y)<R<=1`, independently of h. The bound is not for a trajectory
with repeated cycle traversals. The explicit useful margin R>2/3 begins
only at Y>=12288^20; no small-floor numerical improvement is claimed.

For fixed h,y and a source shell[X,2X), sources with R>=1-delta,
0<=delta<=1/3, have the same odd count. Their common uncorrected value
B=2^h*y/3^j is less than 3X, and they lie in [(1-delta)B,B]. Hence their
number is at most 1+3delta X. Combining this with the new correction bound
gives 1+12288 X Y^(-1/20) for each fixed h,y above the explicit threshold.
No union over unbounded times is controlled by that estimate.

`lean/FinitePathPacking.lean` KERNEL checks first-entry distinctness,
terminal-position counts, finite-prefix image membership/injectivity,
local packing transfer, even entry and its landing interval, the integer
odd-count uniqueness implication, and the new constant comparison.
The entropy induction, reciprocal sums, products, real interval counts,
and analytic fibre estimate remain WRITTEN. Four fresh sequential builds
pass, including CollatzPacking, FirstPassagePacking, and PackingExponent.
Only standard logical axioms occur; no native evaluation or admitted proof.

`python3 verify_finite_path_packing.py` checks 18 complete source shells at
floors 1,2,16,64,256,1024: 19,082 starts and 312,115 shortcut steps.
It checks exact rational products/correction sums and 11,494 qualified
fixed-time fibres. There are 199 selected paths, including shortened
prefixes, with 18,417 image checks, 16,708 fixed-weight groups, 3,093 terminal
counts, and 59,802 sampled interval counts. These interval samples do not
prove the all-length packing theorem. The largest qualified fibre in
these shells has 10 sources, at floor 256, shell [2048,4096), time 22,
landing 173 and odd count 11. A separate rising-to-power-of-two witness
has 6,556 source bits and first reaches the floor 2^300 after 6,270 steps;
its product and correction sum were replayed exactly.
Manifest: `results/finite-path-packing/verification.json`.

The elementary fixed-time fibre idea was inspected in Section 4 of the
Shaik first-passage draft at
https://raw.githubusercontent.com/shaikidris/FirstPassageLinearTransport/main/paper/collatz_first_passage_natural_density.md .
The local proof is given in full. No global density claim from that draft
was assumed, no foreign Lean code was executed, and no novelty is claimed.
The functional-operator paper https://arxiv.org/html/2106.11859 was also
inspected: its Hardy-space fixed-point statement does not apply to the
summably weighted survivor indicators. It did not supply the needed gap.

The exact losses S_k minus S_(k+1)=P^k D_0 have a common first-entry time,
with D_0 the even integers in(H,2H]. The new result removes elapsed time
from their relative additive correction, but only controls paths that
enter. It neither forces entry nor proves that these loss layers exhaust
the initial weighted mass. Next work must control the unabsorbed starts
or justify a useful sum over possible entry times; more upper bounds on
already absorbed paths alone do not close this gap. Both cycles and
divergence remain unresolved. No staging or commits were performed.

## 2026-10-09: equal-weight fibres, divergence, and an all-time induction obstruction

The previous turn was progress: the finite-path packing sources and
verification hashes were rechecked unchanged. This continuation sought
constraints on unabsorbed trajectories. No external blocker occurred;
the goal stays active and the full conjecture remains unresolved.

New `lean/EqualWeightFibres.lean` KERNEL proves two integer envelopes.
For y=U^k(n), j=wt(k,n), e=k-j:
`3^j*(n+1) <= 2^k*y+2^j` and
`2^k*(y+1) <= 3^j*(n+2^e)`.
In reverse coordinates z=n+1, odd steps multiply by 2/3, while even
steps send z to 2z-1. The full inverse error lies between
`(2/3)^j*(2^e-1)` and `2^e-1`. Thus fixed k,j,y sources have diameter
at most `(1-(2/3)^j)*(2^e-1)` and cardinality at most 2^e. The cardinality
and uniqueness when e<=1 are kernel checked; these are bounds for every
finite time, not a uniform-in-time constant.

`docs/EQUAL-WEIGHT-FIBRES.md` gives a WRITTEN coefficient-moment consequence.
For s>log_3(2), sum_(U^k(m)=y)(3^wt(k,m)/2^k)^s is at most
`(3/2)^(s*k)/(1-2/3^s)`. All-odd paths to targets varying with k give
the matching exponential rate (3/2)^s. This is a coefficient moment,
not actual m^(-s) weights or a killed survivor contraction. No global
conclusion follows by exchanging those quantities.

Define F_k(n)={m>0:U^k(m)=U^k(n), wt(k,m)=wt(k,n)}. These sets are
nested. The kernel proves the complete endpoint cap
`m <= floor((2^k*U^k(n)+2^wt(k,n))/3^wt(k,n))-1`, and eventual
stabilization if a uniform integer M bounds
`2^k*(U^k(n)+1) <= 3^wt(k,n)*(M+1)`.
The finite-set stabilization proof is general and contains no analytic
or convergence axiom.

WRITTEN divergence bridge: on a nonrepeating orbit, reciprocal summability
gives P_k=product_odd(1+1/(3*x_i)) tending to finite P_inf. Then
C_k=3^wt/2^k=x_k/(n*P_k) tends to infinity, and
B_k=(x_k+1)/C_k tends to L=n*P_inf. B_k is nondecreasing: an odd step
leaves it fixed; an even step adds 1/C_k. Thus B_k<=L supplies the
kernel's boundedness hypothesis and forces F_k(n) eventually constant.
Proving unbounded growth of these particular fibres for every start
would exclude divergence, but no such premise is proved. Maximum fibre
growth at independently chosen targets/weights cannot be substituted.

Also WRITTEN: divergence exists iff some positive start has every
coefficient prefix at least one. For a divergent orbit choose a time
of global minimum of C_k, which exists since C_k tends to infinity.
Conversely such a supercritical start cannot eventually cycle, because
the coefficient around a positive cycle is strictly below one. This
does not prove universal coefficient stopping, and even that statement
would still leave nontrivial cycles to exclude.

Two complete KERNEL examples constrain the search. F_34(1)={1} but
F_35(1)={1,159}; the endpoint caps 132 and 176 make the finite tables
complete for every source. The start 159 reaches one at time 36. Thus a
finite plateau is not evidence of permanent stabilization.
The start 27 reaches one at time 70 yet has no positive smaller
equal-time, equal-weight mate at ANY time. At time 72 all starts 1..27
are in {1,2}, and all smaller starts have a different state/count pair.
Earlier mates would persist to 72; later mates cancel back to 72 because
the map is injective on the standard cycle and cannot erase a count
difference. The kernel proves this all-time cancellation and exclusion.

The WRITTEN classification for convergent starts is by integer arrival
label d(n)=T-2*wt(T,n), with U^T(n)=1. Extra cycles do not change d.
Two convergent starts eventually become equal-time/equal-weight mates
iff their labels agree. Here d(27)=-12, unlike every smaller start.
There are unboundedly many convergent starts with no smaller mate of
this restricted type: each label a>=0 is realized by 2^a; its least
convergent representative has no smaller mate, and distinct labels give
distinct representatives. This all-index corollary is WRITTEN. It
rules out repairing the restricted induction with a larger finite base.
The broader coalescence criterion allowing different clocks/counts is
not refuted, nor is unbounded growth of each entire fibre refuted.

`python3 verify_equal_weight_fibres.py` passes four fresh sequential
Lean 4.33.1 builds with only standard logical axioms and no native
evaluation or admitted proofs. It checks 131,071 canonical residue
envelopes through depth 16, 774 large affine lifts, and 88,573 complete
target residue classes for coefficient moments at exponents 1 and 2
through depth 10. It makes 8,454,144 direct source/time checks in the
source window 1..65536 through time 128 for four tracked fibres. Every
snapshot says whether the endpoint cap makes that window complete.
For example F_76(1) has 1,655 members with complete cap 55,932; later
window counts are not silently called complete. First-one times and
arrival labels are independently replayed for all starts 1..27.
Manifest: `results/equal-weight-fibres/verification.json`.

Next retain the all-source cap and variable odd-count/time information
when seeking useful merges. Requiring a smaller mate with both clock
and odd count unchanged is false even on arbitrarily large convergent
starts. The new necessary stabilization condition does not construct
the missing merges or settle the weighted-loss estimate. Both cycles
and divergence remain open. Source files, existing changes, and the
index were preserved; no staging or commits were performed.

## 2026-10-09: coalescence grades and a conditional odd/even credit rank

The previous turn was progress: all-index equal-weight fibre bounds and
the induction obstruction were proved and recorded. This turn continues
that work; it is not a blocked audit. The full Collatz goal remains active
and unresolved. No sub-agents were used.

New files: `docs/COALESCENCE-GRADES.md`,
`lean/CoalescenceGrades.lean`, `verify_coalescence_grades.py`, and
`results/coalescence-grades/`. The Lean module imports EqualWeightFibres
and CollatzContradiction; earlier verified sources and manifests are
unchanged. All claims below described as kernel have no added axioms,
admitted proofs, or native-decision axiom.

KERNEL: dyadic envelope `2^k*orbit(k,n)<=2^(2*wt(k,n))*n` for n>0.
For any arrival U^T(n)=1 of nonnegative integer grade a=T-2*wt(T,n),
this gives `2^a<=n`. Powers of two realize equality, so the least
convergent representative of grade a>=0 is EXACTLY 2^a. The earlier
nonconstructive unbounded-minima argument is now explicit and kernel
checked: for every a,k and positive m, an equal-time/equal-weight mate
of 2^a at time k satisfies m>=2^a. Increasing a finite base still cannot
repair induction with both restrictions.

KERNEL: the core identity is `k+orbit(k,x)=2*wt(k,x)+x` for x=1 or 2.
Two convergent starts eventually have an equal-time/equal-weight meeting
iff their integer arrival grades agree. For ANY physical meeting
U^a(n)=U^b(m) of convergent starts,
`d(n)-d(m)=a-b-2*(wt(a,n)-wt(b,m))`.
Lean writes this using natural-number cross-sums, with no truncated
negative grades. Every positive m<27 has nonnegative grade, whereas
d(27)=-12. Thus a same-clock meeting of 27 with such m needs at least
six more odd steps on 27's side; an equal-weight meeting needs the
partner's clock at least twelve steps later. Both are sharp:
U^70(27)=U^70(1)=1 with weights 41 and 35;
U^70(27)=U^82(1)=1 with weights 41 and 41.
The complete small table is kernel reduced and the all-time extension
uses the general meeting identity.

KERNEL full equivalences, retaining physical ordinary paths:

- Collatz iff each n>2 has a positive smaller same-clock meeting partner,
  with odd counts unrestricted. Under known convergence, partner 1 or 2
  supplies the phase; 2 must be included in the base.
- Collatz iff each n>1 has a positive smaller equal-weight meeting partner,
  with clocks unrestricted. Under known convergence at time T with j odd
  steps, partner 1 at clock 2j works.

Both reverse implications are strong induction. Neither universal
meeting premise is proved; these equivalences bypass the earlier
restricted-method obstruction without resolving the conjecture.

KERNEL conditional rank: credit A means `2*wt(k,n)<=k+A`, so odd steps
never outnumber even steps by more than A. Remaining credit is
`g=A+k-2*wt(k,n)>=0`. The natural rank
`R(x,g)=2^(g+1)*(x-1)+g` strictly decreases while x>1 and credit remains
nonnegative. On an even step its drop is `2^(g+1)-1`; on an odd step
with g>=1 the drop is `2^(g-1)*(x-3)+1`. Consequently an all-time credit A
implies hitting one by `R(n,A)=2^(A+1)*(n-1)+A` steps. Checking the credit
only through time R(n,A)+1 also suffices. Any hypothetical nonconvergent
positive source must exceed EVERY proposed credit A at some time at most
R(n,A)+1. This applies to both cycles and divergence, with no analytic
packing dependency in its proof.

KERNEL: a certified arrival at time T gives full-orbit credit A=T+1.
Thus convergence of each positive start is equivalent to existence of
a finite credit for that start. This is still an EXACT REFORMULATION,
not the missing proof: using the arrival time to choose A is circular
as a universal convergence strategy. A fixed credit for all sources is
impossible, since `2^K*q-1` with q>0 has K initial odd steps and requires
credit at least K. No universal formula A(n) is proved.

Verification: six fresh sequential Lean 4.33.1 builds passed, with only
standard logical axioms and no warnings. The independent Python census
certifies first arrivals, arrival grades, and minimum FULL-ORBIT credits
for every source 1..2,000,000. This larger range is PYTHON, not a kernel
range theorem. Its lowest grade is -65 and largest minimum credit is 74,
both attained at 1,723,519. The difference matters: credit records the
largest odd excess anywhere along the path, not just at arrival.
Independent direct replay covers sources 1..8192 with 476,621 step checks,
including dyadic envelopes and exact rank drops. At common clock 165,
the grade and state/weight partitions of those 8192 sources coincide
(40 classes, thus 67,108,864 ordered pairs classified by partition equality).
The finite 27 replay checks 900 same-clock meetings and 1185 equal-weight
meetings through clock 128. There are 1024 large all-odd checks with
lengths 1..256 and four positive quotients. These finite scopes do not
imply a universal credit bound.
Manifest: `results/coalescence-grades/verification.json`.

Next: the useful open target is an independently justified finite credit
for EVERY positive source, or a complete relaxed physical-coalescence
selector. The integer rank verifies the consequence of such a bound;
further finite censuses or the grade equivalences alone cannot supply it.
Both nontrivial positive cycles and divergence remain open. Preserve the
index and all existing changes; no staging or commits were performed.

## 2026-10-09: survivor parity bounds and the strength of a credit estimate

The previous goal turn was progress: it added the kernel arrival-grade
classification and conditional credit rank. This turn revalidated all
16 hashes in that manifest before extending the argument. The full
Collatz goal remains active and unresolved; no sub-agents were used.

New files: `docs/PARITY-SURVIVAL.md`, `lean/ParitySurvival.lean`,
`verify_parity_survival.py`, and `results/parity-survival/`.
Earlier verified source files and manifests were preserved. The new
module imports CoalescenceGrades and WeightedSurvivors, reusing the
kernel table that every positive start at most 64 reaches one within
71 shortcut steps. No analytic packing or external theorem is an input.

KERNEL: `AvoidsFloor H k n` means U^i(n)>H for i<k, so the endpoint
may be the first floor entry. A generic induction on an odd-step bound
`2P*U(x)<=Q*x` gives `P^j*2^k*U^k(n)<=Q^j*n`, where j=wt(k,n).
For avoiding one use P=3,Q=10; for avoiding 1..64 use P=65,Q=196.
The exact power comparisons `10^4<3^4*2^7` and
`196^5<65^5*2^8`, together with n<=2^b and positive endpoint, give:

- `4k<=7*wt(k,n)+4b` on prefixes avoiding one;
- `5k<=8*wt(k,n)+5b` on prefixes avoiding 1..64.

The generic power-to-count conversion and both specializations are
kernel checked using only natural-number arithmetic.

KERNEL: put K=4A+5b+1. The SINGLE endpoint condition
`2*wt(K,n)<=K+A` forces an entry into 1..64 by time K-1;
otherwise the second inequality above gives K<=4A+5b, a contradiction.
The certified base then gives an arrival at one by `4A+5b+71`.
This condition does NOT require that credit A held at earlier indices.
In particular, full-orbit credit A now implies this LINEAR bound in A
and b, improving the earlier exponential-in-A bound. The earlier theorem
remains valid; this new module does not change its manifest.

KERNEL: a hypothetical positive counterexample avoids 1..64 forever,
so `5k<=8*wt(k,n)+5b` holds at EVERY clock. In integer terms its excess
D_k=2*wt(k,n)-k satisfies D_k>=(k-5b)/4. Thus each proposed A is exceeded
at the specific clock K=4A+5b+1, stronger than the earlier bounded-time
existence of some excess witness. Both nontrivial cycles and divergent
counterexamples are included. A single sparse prefix satisfying
`8*wt(k,n)+5b<5k` proves ordinary convergence.

WRITTEN consequence: every hypothetical counterexample has lower
limiting odd frequency at least 5/8. Convergent trajectories have limiting
odd frequency 1/2. A universal individual-orbit estimate crossing 5/8
would suffice, but none is proved. Density-one results about source sets
do not supply this pointwise estimate; long parity prefixes also cannot
be counted as uniform independent bits beyond their justified modulus.

KERNEL quantitative implications: a full-orbit credit A<=C*b+D gives
a hitting certificate T<=(4C+5)*b+(4D+71). Conversely a hitting certificate
T<=C*b+D gives credit A=T+1<=C*b+(D+1). Thus, as a WRITTEN interpretation
of these exact formulas with b=ceil(log2 n), uniform O(log n) credit is
equivalent to uniform O(log n) TOTAL stopping time. This changes the next
research action: fitting a logarithmic credit formula is not a weaker
quantitative escape from the strong stopping-time conjecture. The full
ordinary Collatz conjecture alone supplies no such uniform constants.

Verification: eight fresh sequential Lean 4.33.1 builds passed, with
only standard logical axioms, no warnings, no admitted proofs and no
native-decision axiom. Python checks 131,054 positive canonical
source/depth pairs through depth 16; 130,271 avoid one and 115,979 avoid
1..64 over the required prefixes. Independent direct trajectories for
all sources 1..32768 give 2,142,640 index checks. Nine selected sources
produce 260 endpoint tests: 79 valid certificates, 181 failed conditions
on convergent sources, and 52 valid certificates despite an earlier
violation of that same allowance. For example, n=27, A=12, b=5 gives
K=74 and wt=43, so the endpoint condition holds even though the full
orbit's minimum credit is 21. A failed endpoint test is not a
counterexample to convergence.

There are 1024 large all-odd prefix checks through length 256, plus eight
explicit convergent family checks with K=2..9:
a=3^(K-1), q=(2^a+1)/3^K, n=2^K*q-1. They reach 2^a after K odd steps,
then one after a halvings, and have full-orbit credit K. The largest
source has 6556 bits, arrives at one at 6570, and satisfies the new
conditional bound 32887. No convergence of arbitrary all-odd prefix
realizers is inferred. Manifest: `results/parity-survival/verification.json`.

External directions read but NOT adopted as proof inputs: Inselmann's
arXiv:2402.03276v2 states density-one approximation over a logarithmic
time range and explicitly treats uniform logarithmic total time as an
additional hypothesis. The Gettysburg `research/integrated/rank-merging/`
guide and `research/astra-three-routes/pass4/MOVING_GHOST_RANK.md` describe
an input-dependent four-candidate envelope rank; they still have no
universal successful merger selector, and the rank is not globally
decreasing. The Trikoz repository's exposed deep-brake and block-length
scripts are finite random-sample tests, not a pointwise proof used here.
No universal theorem was imported from those claims.

Next: obtain an independently justified parity estimate for EACH
positive orbit, an actual dynamically reusable survivor-mass estimate,
or a complete physical coalescence selector. More conditional bounds
and finite censuses alone will not resolve that obligation. The present
result quantifies the strength of the credit route; it does not prove
its missing premise. Both nontrivial cycles and divergence remain open.
No staging or commits were performed; preserve the user's index.

## 2026-10-09 — All-depth parity-prefix inverse-fibre bound

Substantive progress on the inverse-fibre estimate; no proof or disproof
of Collatz. The active user goal remains unchanged. Files:
`docs/FIBRE-PREFIX-BOUND.md`, `lean/FibrePrefixBound.lean`,
`verify_fibre_prefix_bound.py`, and `results/fibre-prefix-bound/`.
README and ATTEMPT link this follow-up. Earlier source files and manifests
were preserved; their results remain valid.

KERNEL: for same-time, same-weight mates with e=k-j>0, the two shifted
bounds imply m+1<n+2^e. Thus a grid of spacing at least 2^e-1 contains at
most one fibre member. On a grid 3^a*x+r, splitting x by source parity
and mapping x to floor(x/2) gives an even image grid of spacing 3^a,
and an odd image grid of spacing 3^(a+1); each part maps injectively.
The even branch consumes one even step, the odd branch increases a.
Define B(e,a)=1 if 3^a+1>=2^e, otherwise
B(e,a)=B(e-1,a)+B(e,a+1). Both calls decrease e-a. The universal theorem
`grid_fibre_cardinality` bounds ANY finite Nodup index list on this grid
by B(k-j,a). Setting a=r=0 bounds all finite same-time, same-weight
fibres by B(e,0), at every depth and target. The existing endpoint cap
also establishes finiteness of each complete fibre.

KERNEL: B(2,0)=2, so two even steps allow at most two sources. The bound
is sharp at arbitrarily large targets: for every q>=0, 8q+4 and 8q+5
both reach 3q+2 in three steps with odd count one. No all-index exact
maximum is asserted for e>=3. Python recurrence values include
B(6,0)=31, B(10,0)=341, B(16,0)=9389, B(20,0)=80386 and
B(30,0)=18721780. Those numerical evaluations are Python checks; the
applicability of the recurrence is the kernel theorem.

WRITTEN analysis: majorize B by the leaf count L(T) of a binary tree
with children T/2,T/3, stopped at T<=1. Then L(T)<=2*T^delta for T>=1,
where 2^(-delta)+3^(-delta)=1. The base intervals 1<T<=2 and 2<T<=3
have respectively two and three leaves; the defining equation closes
the induction above three. Therefore N(k,j,y)<=2*alpha^e,
alpha=2^delta=1.726541379..., delta=0.787884911... . This improves the
previous 2^e exponential rate. It is not asserted to be optimal.

WRITTEN consequence: the coefficient moment Z(k,s,y), summing
(3^j/2^k)^s over positive k-step preimages of y, is at most
2/(1-alpha/3^s)*(3/2)^(s*k) for s>log_3(alpha)=0.497100032... .
This includes s=1/2. An explicit bound is
Z(k,1/2,y)<=4000*(3/2)^(k/2). The new Lean module kernel checks
1000^24<2^19*579^24, 1000^24<3^19*421^24, and
2^19*2000^24<3^12*1999^24. Written positive-root extraction gives
delta<19/24 and 2^(19/24)/sqrt(3)<1999/2000, establishing the constant.
The real-analysis statements are NOT themselves Lean theorems.

The all-odd affine sources retain the matching uniform-target lower
exponential rate (targets vary with k). A separate WRITTEN averaging
identity over a complete high target interval of length 3^k is
average Z(k,s,y)=((1+3^(s-1))/2^s)^k. Hence a uniform constant times
(3/2)^(s*k) is impossible when s<log_3(3/2)=0.369070246... . The gap
between this obstruction and the proved threshold remains open.

Verification: five fresh sequential Lean 4.33.1 builds passed with only
standard logical axioms, no warnings, no admitted proofs and no native
reduction axiom. Python directly checked all 524287 canonical
source/depth pairs at k=0..18, including the exact shifted error formula.
The separate even-position word algorithm agreed with all 8191
canonical words through depth 12. It enumerated 8215772 additional
selected words with up to 64 odd steps, reconstructed complete maximal
canonical fibres, and directly replayed 3621 witnesses and affine lifts,
including q=2^100+37. These are complete fixed-depth, fixed-weight
maxima for all target classes, not bounds on the supremum over depths.
Nine even steps give maximum 25 at j=7 but 26 at j=8, demonstrating why
an earlier plateau must not be extrapolated.

There are 91392 finite source/depth checks on grids with spacing
3^a for a=0..6 and several small/large offsets, plus eight two-even
sharp-family checks. Exact integer square-root enclosures checked the
moment and combinatorial average over all 29524 target classes at
k=0..9. No floating-point decisions enter these checks. All 14 new
manifest hashes match; the previous equal-weight (13 hashes) and
parity-survival (21 hashes) records also still match.

LIMITATION: this is a coefficient moment whose upper bound GROWS with
k, not actual source-weight mass and not a dynamically reusable killed
survivor contraction. An upper bound on fibre size also does not force
new mates along an individual forward orbit, so conditional fibre
stabilization under divergence is not contradicted. Both nontrivial
positive cycles and divergent positive orbits remain unresolved. No
external theorem or claimed online proof was adopted as an input.

Next research should retain the grid-spacing information while deriving
an estimate for the ACTUAL surviving layers, or obtain a physical
coalescence selector/parity estimate for each source. Improving the
uniform coefficient exponent alone does not close the pointwise gap.
No staging or commits were performed; preserve the user's index.

## 2026-10-09 — Direct exit mass certifies 128 actual survivor horizons

The preceding goal turn was substantive progress: its all-depth kernel
fibre recurrence is valid (all 14 manifest hashes were rechecked). This
turn produced a further finite result for the ACTUAL weighted survivor
sequence, without treating the coefficient moment as a contraction.
Collatz remains unresolved and the full user goal remains active.

New files: `docs/SURVIVOR-EXIT-MASS.md`,
`verify_survivor_exit_mass.py`, `results/survivor-exit-mass/`.
README and ATTEMPT link the result. There are NO new Lean theorems in
this milestone. Previous kernel verification for inverse branches and
floor64 convergence is reused, with hashes checked, not rebuilt or
reclassified. The numerical certification is independent exact Python;
the infinite-sum and integral-tail arguments are written analysis.

For H=64 and s=3/2, let D_k=M_k-M_(k+1) be the weight of the exact
first-entry layer tau_H(n)=k+1. With a finite cutoff R, let P_k(R) be
survivor mass from n<=R and E_k(R) the exit mass from n<=R. Then
M_k<=V_k=P_k(R)+2/sqrt(R), D_k>=E_k(R), and
M_(k+1)/M_k<=1-E_k(R)/V_k. This retains actual time labels and uses
known exit mass; it does not subtract independent unknown-tail errors.
The integer test 1000*exit_lower>=7*mass_upper certifies the full
infinite-mass contraction M_(k+1)<=.993*M_k, without assuming anything
about convergence of n>R.

At R=2000000 and scale 2^96, the exact test passes at ALL k=0..126,
and also k=128: 128 finite successful horizons. The old inverse-cone
replay's sufficient eligible-share bound covered k=0..36. At k=128,
the certified relative-loss lower bound exceeds .00711966. The test
first fails at k=127, with lower bound .0067158801... . That is an
INCONCLUSIVE sufficient test, NOT a refutation of actual contraction.
At k=128 the full mass is enclosed between approximately .0002084957
and .0016227093; its numerator includes only known exits. Decimal
values are explanatory; every decision was made with exact integers.

The Python table gives the FIRST entry into 1..64 for every start
1..2000000. Its maximum time is 335, at 1723519. Table rows use the
format source,first_floor_entry followed by newline; SHA256:
6356252123ad73d8a8c57a2eea7ff5326918aa8da9c0ab5ab8e177f7c4a98277.
A guard failure would stop certification, not assert divergence.

Independent full-trajectory replay covers all starts1..65536 plus
2306 extra samples, including endpoints of all 290 attained time
layers, for 3097900 direct steps. An additional complete certificate
check covers EVERY one of the 1999936 nonbase table rows: follow its
actual path to first return into 1..R and verify that the time label
falls by the excursion length. There are 1666603 immediate returns,
333333 outside excursions, and 3370618 physical steps in these checks.
All intermediate outside states exceed the floor. Induction on the
strictly decreasing nonnegative labels certifies the exact first-entry
times; this full finite certificate is checked in Python, not Lean.

Each n^(-3/2) is enclosed by integer square roots, with its squared
inequalities verified. The unknown tail above R is bounded by the
integral 2/sqrt(R). For a lower mass bound, n>max(R,64*2^k) are known
survivors, giving an integral lower tail from that threshold plus one.
This positive tail can round down to zero at scale2^96 at very large
k; zero is a valid numerical lower bound, not a claim that mass vanishes.
All 37 previous complete inverse-cone mass intervals and 36 exit-mass
intervals overlap the new bounds at shared horizons.

The new six-file manifest matches. The previous weighted-survivor
(seven hashes) and fibre-prefix (14 hashes) verifications still match.
Whitespace and document links were checked. No staging or commits.

The earlier natural-density proof was reread; no new mathematical
correction or extension was established. Its unconditional first-passage
law was NOT assumed to hold after arbitrary survivor conditioning.
No external claimed proof was adopted as an input to this new result.

NEXT: an analytic exit-mass lower bound valid at arbitrarily large
horizons, or a proof that a specified growing cutoff schedule supplies
infinitely many successful tests. A larger finite census by itself
cannot settle this obligation and should not be mistaken for an
infinite extension. The grid-spacing moment still has no established
bridge to this exit lower bound. Both nontrivial cycles and divergent
positive trajectories remain open; the goal is not complete or blocked.

## 2026-10-09 — Cutoff and precision budgets for exit certificates

The preceding goal turn made substantive progress with 128 finite
exit-mass certificates. Their six hashes, the seven weighted-survivor
hashes, and all 14 fibre-prefix hashes were revalidated. This turn
proved a limitation on extending that certificate method. It did NOT
certify additional horizons or prove the missing infinite extension.
The full Collatz goal remains active and unresolved.

New files: `docs/EXIT-CERTIFICATE-BUDGET.md`,
`lean/ExitCertificateBudget.lean`, `verify_exit_certificate_budget.py`,
and `results/exit-certificate-budget/`. README and ATTEMPT link them.
The earlier exit-mass source, document, and manifests are unchanged.

KERNEL: for integer envelopes U(k), exit lower numerators L(k), and
good-index flags, U(k+1)+L(k)<=U(k) and (q+h)*L(k)>=h*U(k) imply
(q+h)*U(k+1)<=q*U(k) at good indices. At all horizons K,
(q+h)^G(K)*U(K)<=q^G(K)*U(0), where G counts good indices below K,
even when they are not consecutive. A retained floor B<=U(K) gives
the same product bound with B. With B>0 and h>0, a separate weaker
kernel bound gives G(K)<=U(0)-B. Seven theorems passed a fresh
standalone Lean build, using only propext and Quot.sound; no native
evaluation or admitted proofs. These are abstract integer theorems,
not Lean theorems about real infinite mass or adaptive source cutoffs.

WRITTEN: for general H>=1, s>1, T(R)=R^(1-s)/(s-1), exact partial
survivor/exit masses P_k(R),E_k(R), and V_k(R)=P_k(R)+T(R),
V_(k+1)=V_k-E_k. For R' >= R, integration proves V_k(R')<=V_k(R),
whereas E_k(R')>=E_k(R). This monotonicity is for EXACT real bounds;
rounded integer envelopes need not be monotone in R. Each implemented
integer success nevertheless implies the exact real test at its R.

For G successful DISTINCT horizons, take R_* as their largest cutoff.
Every success transfers to R_*. Telescoping gives
T(R_*)<=rho^G*V_0(R_*)<=rho^G*T(H), hence
R_*>=H*rho^(-G/(s-1)). At H64,s3/2,rho993/1000 this is
64*1000^(2G)<=R_* *993^(2G). The schedule need not be monotone.
Variable certified losses ell_i obey
sum[-log(1-ell_i)] <= (s-1)*log(R_*/H), also bounding sum ell_i.
A method using a sharper omitted-tail estimate than the entire
power-sum integral would need separate analysis; it is not excluded.

WRITTEN independent precision bound: a successful positive integer
exit numerator is at least one. At the last of G successes,
1/S_*<=D_k<=M_k<=rho^(G-1)*M_0, and M_0<T(H). Thus
S_*>(s-1)*H^(s-1)*rho^(-(G-1)). In this case,
S_*>4*(1000/993)^(G-1). A bounded integer scale cannot provide
infinitely many successes even if source cutoffs grow without limit.
This reasoning uses actual masses; it is written, not kernel checked.

EXACT PYTHON: all 336 saved envelope transitions satisfy
U(k)-U(k+1)=L(k)+known_exit_count, with a constant-tail extension
after the final row. Every prefix satisfies the product theorem's
inequality; all and only the previous 128 successful horizons pass.
At R2000000, B=112045541949572279837463878 and
U0=19729971610812289723786322775. Exact powers allow G736 and
exclude G737. The real adaptive-cutoff bound also excludes G737
whenever every cutoff is <=2000000, at any precision. These are
necessary upper bounds, NOT achievable counts: the existing finite
table already has no exits after first-entry time335, so it has no
possible successful horizon beyond334. For scales <=2^96, exact
powers allow G9276 and exclude G9277, regardless of the cutoff.
The full old trajectory table was reused by hash, not recomputed.

CONSEQUENCE: polynomial cutoffs through K permit at most O(log K)
fixed-factor successful horizons, which still leaves infinitely many
sparse successes possible. If the actual mass has exponential decay,
however, E_k/V_k is eventually below every fixed positive threshold
when R_k is polynomial: E_k<=M_k decays exponentially while V_k
retains a polynomial tail. Failure of such tests would then occur
even though the desired actual decay holds. No actual exponential
decay has been established here.

Scope remains a METHOD LIMITATION, not a Collatz counterexample or
a disproof of eventual contraction. Growing cutoff and scale are
necessary, not sufficient, for an infinite fixed-factor certificate
extension. The exact integer theorem and source records are checked;
the analytic bridge is written. A brief primary-literature search
supplied no new proof input; no online proof claim was adopted.

NEXT: the missing work remains a lower bound on ACTUAL exit mass at
arbitrarily large horizons, or an individual-orbit descent argument.
Do not repeat a fixed-cutoff or fixed-precision census expecting an
infinite conclusion. A polynomial cutoff alone cannot track even a
hypothetically exponential mass decrease with this tail enclosure.
Both nontrivial positive cycles and divergent positive orbits remain
unresolved. No staging or commits; preserve the user's index.

## 2026-10-12 — Actual source weights and the killed operator spectrum

The preceding goal turn was progress: the cutoff/precision budget and
its seven manifest hashes were revalidated, along with all 13 equal-weight
fibre hashes, 14 fibre-prefix hashes and 12 weighted-basin hashes.
The full Collatz goal remains active and unresolved. No sub-agents were
used. This turn did not enlarge a source census or certify new mass
contractions; it addressed the missing conversion from coefficient
weights to actual source weights.

New files: `docs/KILLED-OPERATOR-BOUNDS.md`,
`lean/KilledOperatorBounds.lean`, `verify_killed_operator_bounds.py`,
and `results/killed-operator-bounds/`. README and ATTEMPT link them.
Earlier sources and verification records were preserved.

KERNEL: for y=U^k(n), j=wt(k,n), the shifted envelope implies
`2^k*y <= 3^j*n+3^k`. If `2*3^k<=2^k*y`, then
`2^k*y<=2*3^j*n`. Also `2^k*y<=3^k*(n+1)`, so sources of targets
tending to infinity at a fixed depth escape every bounded interval.
These statements apply even to paths that might repeat above a floor;
there is no unproved distinctness or convergence premise.

KERNEL: for every H,k,B there are x,y>B with a surviving length-k
path above H and `3^k*x<=2^k*y`. Use x=2^k*q-1,y=3^k*q-1 with
q=H+B+2. A separate all-index theorem for K>=7 uses
a=3^(K-1), b=2^a, q=(b+1)/3^K, x=2^K*q-1. The previous divisibility
theorem makes q a positive integer. The path stays above 64 for K steps,
reaches b at K, and reaches one at K+a. Thus the norm-growth witnesses
can all be chosen among provably convergent starts.

WRITTEN: define X_(H,s) by norm sum_(n>H)|f(n)|*n^(-s), s>1, and
K_H f(n)=1_(U(n)>H) f(U(n)), n>H. This is composition on functions,
not forward transport of probability masses. Its kth norm is exactly
sup_(y>H) y^s sum_(U^k(n)=y, tau_H(n)>k) n^(-s).
For y>=2*(3/2)^k, the kernel comparison converts this to at most
2^s times the old coefficient moment. For smaller y, the full summable
source tail bounds it. Consequently
`(3/2)^(s*k) <= ||K_H^k|| <= C_(H,s)*(3/2)^(s*k)`.
At H=64, s=3/2 the constant C can be replaced by5, using the kernel
integer comparisons 8<9 and 25<27. This is an actual-weight norm bound,
but its exponential rate is greater than one.

WRITTEN: at fixed k, every target residue modulo3^k has a coefficient
sum Z_k(r) from the canonical residues a modulo2^k. Along that target
class, actual column masses tend to Z_k(r) as the target tends to
infinity; every finite killing condition eventually disappears.
The essential norm is exactly max_r Z_k(r). Finite column truncations
prove the upper bound. For the lower bound, disjoint image columns
and a Cauchy subsequence of their images under any compact operator
give the matching bound. The proof does NOT assume that normalized
coordinate vectors in l1 are weakly null. The old fibre moment bound
and the all-odd column give
`r_ess(K_H)=r(K_H)=(3/2)^s` by the spectral radius formula.
Thus this space has no gap between spectral and essential spectral
radius; equivalent norms and compact corrections do not repair that.
A different stronger space would need separate justification.

WRITTEN explicit example at H64,s3/2: for the power targets b_K above,
set f(b_K)=(3/4)^K*b_K^(3/2), K>=7, and f=0 elsewhere. Its norm is
2187/4096, but `||K_64^K f|| >= (243/128)^(K/2)`, tending to infinity.
For every fixed n, K_64^k f(n) is nevertheless eventually zero: if
the orbit ever hits the support it reaches a power of two and then
the floor; otherwise all values are zero. Every contributing source
converges. The real infinite function and its norm are written; the
support paths and cubic ratio inequality are kernel checked.

VERIFICATION: nine dependency/final modules passed sequential Lean
4.33.1 builds in this turn. The final replay reused the first eight
after matching source/log/olean hashes and freshly built the new
module, which prints ten theorem dependencies. Only standard logical
axioms occur; no admitted proof, native reduction axiom or warnings.
Default reproduction makes all nine builds fresh.

Exact Python checks cover 32767 canonical sources through depth 14,
98301 large affine lifts, 90939 qualified high-target comparisons,
and 159056 source-escape implications. At depths 0..12 and floors 1,64,256,
5211 complete killed fibres (43886 members) agree between inverse
branching and independent canonical lifting. Actual power3/2 column
bounds use integer square roots at scale 2^112. There are 144 coefficient
limit checks in selected complete target classes; 48 large-target
intervals certify relative discrepancy below 2^(-70). These finite
checks do not prove the infinite spectral argument.

There are 771 all-odd column witnesses through k=256 and 98688 direct
steps, plus six convergent power-target witnesses K=7..12. Their first
four pure-halving suffixes are fully replayed (29160 steps); the last
two use the exact power-of-two endpoint and the reused kernel power
hitting identity. The largest source has 177140 bits. All 25 hashes in
the new manifest match. No external Collatz theorem is a proof input.
Standard infinite-sum and Banach-algebra facts remain written analysis.

A primary-source renewal paper was inspected at
https://arxiv.org/html/2606.27488v1 . Its Section 2 hypotheses assume
the requisite killed induced contraction/renewal bounds; no such
bound for Collatz was imported. The Gettysburg exceptional-mass guide
likewise retains a survivor-specific hypothesis. Neither supplies the
missing estimate for the actual constant-vector orbit.

The old external predecessor-density audit's progress file still says
running, but an authorized process-list inspection on 2026-10-12 found
no live Lean/lake or collatz-density audit process. It has 121 recorded
successful modules out of 389, with no completed theorem audit. Its
existing progress changes and untracked logs were left intact; it was
not restarted and no result from it was adopted.

NEXT: focus on the specific bounded functions K_H^k(1), or prove a
usable regularity condition preserved along that orbit. Global operator
contraction on X_(H,s) or an equivalent renorming cannot work. Removing
finitely many target columns does not remove the obstruction. The scalar survivor masses remain nonincreasing
and may still vanish; the norm-growth theorem neither proves nor
refutes this. No nontrivial cycle or divergent orbit has been found.
No staging, commits, or other Git writes were performed.

## 2026-10-12: authenticated predecessor-density source and resumed replay

The universal proof/disproof goal remains active, with no token budget.
No complete proof or positive counterexample was found. No blocker was
declared. This entry concerns an external result under verification,
not an adopted theorem or a completed Collatz proof.

The public Mazur predecessor-density claim and formalization were read:
https://www.proofatlas.ai/proofs/artifact.collatz.predecessors_positive_lower_density.v001.html
https://www.proofatlas.ai/formalizations/positive-lower-density-collatz-predecessors/
The public roots assert positive lower natural density for predecessors
of each fixed positive target not divisible by three, amplification of
any positive counterexample to a positive-lower-density nonconvergent
set, and universal convergence conditional on upper-density-one
convergence. That last density-one premise is not proved.

Source semantics were inspected directly: the ordinary map is even n/2,
odd 3n+1; Reaches means existence of an iterate, including zero steps;
predecessor sets contain positive starts; natCount counts distinct n<X.
The target-dependent constants need not be uniform. A static scan found
no custom axioms, sorry/admit, native_decide, unsafe declarations, kernel
bypass options, or environment mutation. The only run_cmd traverses and
reports public theorem dependencies in Verification.ReleaseAudit.
These inspections are not substitutes for the pending kernel replay.

New `verify_predecessor_density_archives.py` authenticated both published
ZIP hashes and compared all 404 assembled files byte for byte against
archive members. The Lean sources are 377 baseline modules plus 12
companion modules (10 support/implementation modules, public interface,
and release audit). The public interface closure has 388 modules, the
whole replay 389. Record:
`results/predecessor-density-review/archive-authentication.json`.
Baseline `/private/tmp/collatz-positive-density-baseline.zip`:
914975 bytes, SHA256
23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f.
Companion `/private/tmp/collatz-predecessor-density-source.zip`:
55103 bytes, SHA256
55ceb4df0cca17ae728dc65b30bf5077000e1b47f2dc322454eea9f637ac75b3.
The separately downloaded `collatz-positive-density-source.zip` is an
older/differently packaged checked source and is NOT the pinned slim
baseline archive for this replay; do not substitute it.

The stale replay was confirmed not live with an authorized process-list
inspection. All 121 existing source/log/olean hashes matched; there
were exactly 121 project objects and no unrecorded project objects.
`verify_predecessor_density_source.py` now has `--resume`: it checks
the exact topological successful prefix, all those hashes, compiler
commands, toolchain, pinned dependency revisions, and absence of extra
project objects. It uses atomic progress writes, a per-assembly flock,
and records each resumed session's prior progress and verifier hashes.

The replay was actually launched, sequentially with one Lean worker,
at 2026-10-12 13:47:45 UTC. As of the latest poll while writing this
entry, 133/389 modules had passed; the current module was
`Erdos1135.Tao.Fourier.Lemma74CanonicalClaimStar`. This number will grow:
read `results/predecessor-density-review/progress.json` for the current
state. No compiler failure has occurred in this resumed run so far.
The runner PID is 65674 and the unified tool session is 93435; prefer
polling that session, then inspect live processes if it is unavailable.
Do not launch another replay while this one is running.

Assembled tree: `/private/tmp/collatz-density-audit/assembled`.
Assembly SHA256:
9da50833f18f8427523da5cd89ff4a0dbf1198fe09a9a4acccf4583898ac2ec3.
Compiler: Lean4.30.0-rc2, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc.
Pinned official third-party compiled libraries are reused; they are
not rebuilt from source and no independent Lean checker is being run.
The verifier writes `verification.json` only after all 389 modules
pass and all three public root axiom reports contain exactly propext,
Classical.choice, Quot.sound. A status of running with a dead process
is not success. If interrupted, first establish that no audit is live,
then use:
`python3 verify_predecessor_density_source.py /private/tmp/collatz-density-audit/assembled --resume`.

New `docs/PREDECESSOR-DENSITY-REVIEW.md` records the exact statements,
provenance, pending scope, and conditional connection to the written
minimum law. Assuming both the external PLD theorem and that law,
universal convergence is equivalent to p_1=1, with no improved error
rate required; p_1>0 follows from PLD at target1. Every coalescence
component would have positive density, not merely some component.
This does not prove there is only one component or establish p_1=1.
ATTEMPT, README, and the older DENSITY-TO-POINTWISE note now link this
pending review without adopting the external theorem prematurely.

A notation typo in the killed-operator note's introduction was fixed
(stray commas in two exponents). Its manifest records the old/new
document hash and reuse of the unchanged Lean/Python evidence. All
25 manifest hashes matched afterward; no heavy replay was repeated.

NEXT: continue the existing external replay, inspect all three public
statements/axioms after completion, and update the review's status only
if the whole check passes. Then the remaining density route is to
prove p_1=1, not to seek a faster rate assuming it. Until completion,
PLD remains a conditional external input in this project. The actual
weighted survivor functions remain another possible direction; whole
operator contraction on the previous space is ruled out. Preserve the
index and user changes. No staging, commits, or Git writes were done.

## 2026-10-12: completed predecessor-density audit and fixed-target densities

The universal proof/disproof goal remains active, with no token budget.
No complete proof or positive counterexample was found. No blocker was
declared. This entry supersedes the preceding entry's pending replay
status. The audit processes have finished; sessions 93435 and 11119 are
not live work to resume.

### Completed external Lean replay

The source replay completed all 389 modules: the previously validated
121-module prefix plus 268 further successful compilations, including
CollatzPredecessorDensity and Verification.ReleaseAudit. The accumulated
compiler time in the module records is 3536.928 seconds. All return codes
are zero. The three public roots use exactly propext, Classical.choice,
and Quot.sound. Their printed types were read and match the ordinary
positive-integer predecessor-density and conditional convergence claims.
The release audit enumerates 4717 project declarations in their combined
dependency closure and rejects an imported unproved universal Collatz
declaration. Linter/deprecation warnings are present, without proof
admissions or extra axioms.

After all Lean compilations passed, the Python script initially exited 1
because it parsed only the first line of a wrapped axiom list. The actual
multiline lists all contained the three standard axioms. The parser now
reads complete bracketed blocks. Two valid formats were accepted, and
seven invalid cases were rejected: sorry axiom, native reduction axiom,
extra custom axiom, missing root, duplicate root, wrong root name, and
missing standard axiom. Record:
`results/predecessor-density-review/axiom-parser-check.json`.
This was a report-formatting failure, not a Lean proof failure.

The final `--resume` validated all 389 source/log/olean records and exact
compiler commands, toolchain, manifest, and dependency revisions. It
compiled zero modules, then passed the corrected final gate at
2026-10-12T14:44:35.318300+00:00. The final record is
`results/predecessor-density-review/verification.json`, SHA256
fa39ce531d0cf5d3e6f11f8de159a50709bca37536bea7762e2c5d22562e3582.
`progress.json` also says passed. Verifier SHA256:
0359ff5a2f5aa4882e32f964160b775619b9211c67116ef80d303529f31376ad.
ReleaseAudit log SHA256:
943c598e4bf3d55f6ce45ce4a01c75249d2b76ff488e54df0b91992773a798a7.
The two resume sessions preserve the prior-progress hashes. The parser
record separately preserves the initial post-build failure provenance.

The authenticated assembly and archive hashes are those in the preceding
entry. The compiler was Lean4.30.0-rc2, commit
3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc. Pinned official third-party
compiled libraries were reused; they were not rebuilt from source and
no independent kernel implementation was used. Within that stated scope,
the external PLD theorem is now adopted as an independently replayed
proof input. This is separate from the local standalone Lean4.33.1 work.

For each fixed positive target a with 3 not dividing a, PLD says that
the distinct positive starts whose ordinary Collatz orbit reaches a have
positive lower natural density. Its constants depend on a. A positive
counterexample therefore forces the entire nonconvergent set to have
positive lower natural density. Upper natural density one of convergence
would exclude every counterexample, both a nontrivial cycle and a
divergent orbit. The upper-density-one premise is not proved.

`docs/PREDECESSOR-DENSITY-REVIEW.md`, ATTEMPT, README, and the current
density-to-pointwise note have been updated to this completed scope.
Historical memory entries remain unchanged. Under the separate written
minimum law, PLD gives p_1>0 and makes p_1=1 sufficient without a faster
error rate. The older X^0.84 comparison alone had needed more; that rate
requirement is superseded by the linear predecessor lower bound.

### New written deductions and their limits

`docs/DENSITY-TO-POINTWISE.md` now includes:

- From the written uniform first-passage Proposition 4.1, every finite
  odd-target visitation profile has a limiting law. Thus every fixed odd
  target a has a natural predecessor density r_a.
- Summing the written finite-orbit packing bound over a finite target
  interval and then taking densities gives sum r_a <= 256 L^sigma over
  odd targets, with sigma=H_2(log_3 2)<19/20. In particular no uniform
  positive lower bound over all eligible targets is possible.
- Along a forward Syracuse orbit a_j, r_(a_j) increases to the density
  lambda of its coalescence component. This uses tightness of the written
  minimum law: the finitely many possible minima <=B eventually merge
  with a_j, and the minimum-law tail tends to zero. It does not assume
  arbitrary countable additivity of natural density.
- A separate coarse overshoot estimate extends the profile result to
  every positive target, including even targets. With alpha=1.001 and
  n0=floor(log_2(x)/10), Tao Proposition 1.9 and Chernoff give
  19n0/10 <= S <= 3n0 except on an O(x^(-c)) event. The affine formula
  gives entry by n0, because 3^5<2^8 and
  alpha^2-3/100=972001/1000000<1. The last valuation is <=3n0, so the
  odd landing exceeds x^(7/10). For x^(7/10)>max A no target in a finite
  set A is visited in the prior ordinary halving segments. The added
  error is summable in the same scale telescope. Initial halving of an
  even source changes a profile for only O_A(log X) starts up to X.
- Every ordinary orbit value lies in V union 2V for the shortcut value
  set V. Thus sum r_a <=512 L^sigma over all positive targets in a
  length-L interval. The forward-density limit extends to ordinary
  orbits as well. Targets divisible by three have only repeated-doubling
  predecessors and density zero. PLD makes all other r_a positive.

All of these new conclusions are written analysis, not new Lean or
native certificates. The older odd-target proof alone still does not
handle even targets; Section 5 explicitly supplies the additional bound.
The record `results/density-to-pointwise/written-review.json` contains
12 source/evidence hashes and the exact dependency distinctions. The
prior natural-density manifest's 2 hashes and finite-path-packing
manifest's 12 hashes were checked; no old numerical or Lean suite was
rerun unnecessarily. The natural-density numerical checks remain only
floating-point and Monte Carlo sanity checks.

The written first-passage argument was reread against Tao arXiv v7,
https://arxiv.org/html/1909.03562v7 (July 2026). The paired-sum Fourier
tilt, weighted submeasure mixing, renewal mass 1/(2-log_2 3), and harmonic
sum bounds were rechecked. The shifted renewal parameter has the factor
2*m0*(2-log_2 3), correctly accounting for the E-prime scale; do not
replace it by a single m0. No new analytic gap was found in that review,
but this does not turn the written adaptation into a kernel proof.

NEXT: the density route needs p_1=1, not merely positivity or existence
of density. A divergent component would have lambda>0 and r_(a_j)
increasing to lambda along its unbounded forward orbit. A bound forcing
these particular densities to tend to zero would exclude divergence,
but the summed target-interval bound does not supply it: a sparse orbit
is compatible with that bound. Nontrivial cycles also remain open.
The actual bounded weighted survivor functions remain another route;
global contraction on the previously studied weighted space is already
ruled out. No staging, commits, or Git writes were performed.

## 2026-10-12: first-passage atoms and density flow inside a fixed basin

The full proof/disproof goal remains active and unresolved. The preceding
turn was progress: it completed the external 389-module proof replay and
added written fixed-target density results. This turn strengthens the
density argument, without finding a complete proof or counterexample.
There is no blocker and no live compiler left to poll at the end of this
entry. The completed verifier session was 88164.

New `docs/PREDECESSOR-DENSITY-FLOW.md` proves, under the written uniform
first-passage Proposition 4.1 and its early-valuation estimates, that

  for each fixed a>0, sup {r_b : b>R and b reaches a} tends to zero
  as R tends to infinity.

Here r_b is the already established written natural density of the
ordinary predecessor basin P_b. The threshold depends on the fixed root
and finite first-hit paths. It is not a bound uniform over all targets
or all roots. The proof has three steps:

1. At most 2^(k+1)-1 distinct positive starts can hit any fixed positive
   target by k shortcut steps. This is now kernel checked for all k and
   all targets, using an exact list of inverse predecessors. No factor
   depending on the target's magnitude is present.
2. For each fixed floor x, F_x(n)=SyracusePass_x(oddpart(n)), including
   an infinity mark, has a limiting law nu_x for uniform positive starts.
   The exact identity F_x(n)=F_x(Pass_u(n)) for u>=x allows the same
   scale telescope. Its error at an odd source scale Y>=x^alpha is
   O((log Y)^(-c)). On the early-valuation good event at Y=x^alpha,
   T_x<=n0 and total valuation <=3n0, so entry uses <=3n0 shortcut steps.
   The finite fibre bound makes every atom of that base passage law
   O(x^(-c)). Thus max_z nu_x({z})=O((log x)^(-c)), including infinity.
3. Fix a, choose a large x>=a, and if a is periodic include its whole
   finite cycle below x. Let Q_x be the finite union of paths from each
   z<=x that actually reaches a, stopped at its first hit of a. It does
   not assume that all z reach a. If b in P_a lies above max Q_x, no
   source reaching b can visit any z<=x before b; otherwise that retained
   path would contain b. Nor can it visit a before b, since b is outside
   a's cycle. Therefore P_b is contained in one atom of F_x, namely
   F_x(b). This gives r_b<=max_z nu_x({z}), proving the fixed-basin limit.

The new limit applies to every simple infinite inverse chain and in
particular to the doubling ray: r_(2^j a)->0 for each fixed a. This
removes the explicit remainder from a finite branch partition. For a
nonperiodic ordinary root,

  r_a = r_(2a) + 1_(a mod 6 = 4) r_((a-1)/3).

For an odd nonperiodic a, telescope along its doubling chain:

  r_a = r_(2^K a) + sum_(1<=k<K, 3 divides 2^k a-1) r_((2^k a-1)/3).

Letting K tend to infinity now proves the countable inverse Syracuse
flow identity, with no assumed interchange of a density limit and an
arbitrary infinite union. Nonperiodicity is essential: the ordinary
root 4 has parents 8 and 1 whose basins overlap (witness start 8), and
the Syracuse self-parent 1 cannot precede a first hit of 1.

New `lean/BoundedHitFibres.lean` has twelve checked theorems. In addition
to the finite fibre bound and exact inverse-list membership, it proves
first-hit uniqueness/recursion, uniqueness of hit times at a nonperiodic
ordinary root, disjointness of distinct immediate predecessor basins
there, ordinary predecessor arithmetic, and the one-step decomposition.
These use only propext, Classical.choice, Quot.sound (some use a subset),
with no native evaluation, sorry, warnings, or extra axioms in the final
build. Compiler: the local Lean4.33.1 at commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

New `verify_predecessor_flow.py` accepts optional --reuse-build-dir. In
the completed run it copied three dependency objects from
`/tmp/collatz-killed-operator-build` only after checking compiler version,
source/object/log hashes, and successful records. The new module was
compiled afresh, in an isolated temporary directory. The older cache has
no compilation command fields, so reused records use null for that field
rather than inventing executed commands. Default reproduction rebuilds
all four modules sequentially. No external PLD modules were rebuilt.

The independent Python replay passed these exact finite scopes:

- 288 complete bounded-time fibres: targets 1..32, depths 0..8; 135168
  forward-simulated sources, using the earlier kernel inequality
  n<=2^k U^k(n) for a complete source bound.
- 4096 ordinary trajectories followed through their first repeated
  state, all ending in the known cycle; 311850 ordinary steps.
- 47463 terminal halving marks, 1298432 doubling-tail identities,
  and 491520 finite inverse-branch partitions.
- 89680 finite-basin first-passage transport checks, using retained
  first-hit paths at roots 1,5,27 and floors 32,64,128.

Records: `results/predecessor-density-flow/verification.json` and
`results/predecessor-density-flow/replay.json`, plus four Lean logs.
The density-law arguments and infinite branch sum are written analysis;
the finite checks do not prove those limiting statements. PLD is used
only for positivity and the comparison with a hypothetical divergent
component, and retains the preceding entry's external trust scope.
The preceding written-review record's 12 dependency hashes were checked;
its DENSITY-TO-POINTWISE hash was updated with explicit provenance for
the appended follow-up link, while Sections 1-5 and their evidence were
left unchanged. ATTEMPT and README now link the new result.

NEXT: (fixed-basin decay) and (r_(a_j) increasing to lambda>0 along a
divergent forward orbit) do not contradict one another. Later a_j leave
every earlier P_(a_J), since a return would create a cycle. Changing the
root with j loses the fixed-basin threshold. The next density question
is what additional control on moving targets or conditional first-passage
laws could bridge that distinction. A weaker statistical reformulation
alone would not prove p_1=1. Nontrivial cycles and divergent orbits both
remain unexcluded. No staging, commits, or Git writes were performed.

## 2026-10-12: approximation uniform over every predecessor target

The full proof/disproof goal remains active and unresolved. There is no
blocker or live compiler to resume. The completed verifier session was
41536; its final record reports passed at
2026-10-12T15:52:39.109292+00:00. No positive counterexample was found.

New `docs/UNIFORM-PREDECESSOR-APPROXIMATION.md` proves, conditional on
the earlier written uniform first-passage estimates, that

  sup_(a>=1) |R_X(a)-r_a| = O((log X)^(-c)),
  R_X(a) = #{1<=n<=X: n reaches a}/floor(X).

This constructs the limits directly and strengthens the earlier
fixed-target density statement. The constants are independent of a, so
targets may vary with X. The result does not assert that r_a is small
when a varies. It is uniform convergence of the target-indexed function,
not total variation convergence of whole orbit-value sets.

The exact argument works for any passage predicate. Let F_H(n) be the
first ordinary odd state <=H, or infinity if no entry occurs. If n
reaches a, either the landing itself reaches a or F_H(n)=F_H(a). Thus
for any source law with passage law q,

  0 <= P(n reaches a) - sum_(odd b<=H) q(b) 1_(b reaches a)
    <= q(F_H(a)) <= maxatom(q).

This includes even and cyclic targets and nonentry. It assumes no
independence between landing and future behavior. The earlier flow
note's Section 2 supplies nu_H, with TV error O((log Y)^(-c)) for odd
source intervals [Y,2Y), Y>=H^alpha, alpha=1.001, and maximum atom
delta_H=O((log H)^(-c)), including infinity. Choosing H=floor(Y^(1/alpha))
gives a target-uniform Cauchy estimate for every larger source scale Z.
Dyadic mixing and initial valuations transfer it to positive sources.
The initial-halving discrepancy for any single target lies among the
starts 2^j a and is bounded uniformly by 1+floor(log_2 X) counts.

For each fixed H this also gives the finite-mixture formula

  0 <= r_a - sum_(odd b<=H) nu_H(b) 1_(b reaches a)
    <= nu_H(F_H(a)) <= delta_H, uniformly in a.

The mixture retains the actual seed orbits. Certifying all seeds up to
one tested floor gives a bound outside their finite orbit union, but
does not certify arbitrarily large floors or yield a numerical analytic
error constant. No general decay along divergent orbits follows.

New `lean/PassageApproximation.lean` imports only CollatzContradiction.
It constructs a noncomputable first-passage mark and checks eleven
theorems: first-entry existence and uniqueness; finite/nonentry mark
characterizations; reachability transitivity; suffix transport; nonentry
after a hit; landing-hit inclusion; the passage comparison; early-hit
mark equality; and its odd-floor specialization. Standard axioms only
(propext, Classical.choice, Quot.sound, or subsets), without sorry,
native evaluation, extra axioms, or warnings. The analytic convergence
and rates are not Lean theorems. The noncomputable mark does not decide
whether an arbitrary orbit ever enters.

New `verify_uniform_predecessor_approximation.py` compiled the new module
afresh with Lean4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, in an isolated temporary
directory. Only CollatzContradiction was reused from the validated
`/tmp/collatz-killed-operator-build` cache, checking compiler version and
source, object, and log hashes. Default reproduction builds both modules
sequentially. No external PLD modules were rebuilt.

The independent exact Python replay followed all 2048 original source
orbits through their first repeat, obtaining a closed universe of 4457
reachable targets (maximum value 1276936). It checked source cutoffs
32,128,512,2048 and ten predicates, including empty and partial-entry
sets. Across those 40 population/predicate comparisons it passed:

- 17828 initial-halving target bounds;
- 27200 landing-orbit inclusion checks;
- 1469630 early-hit passage-mark equalities;
- 178280 target histogram comparisons.

Both finite-population target vectors vanish outside the complete closed
universe, so those comparisons cover every possible target for the
represented populations. This is a finite replay, not an asymptotic or
universal convergence certificate. Records and two Lean logs are under
`results/uniform-predecessor-approximation/`; the verification record
has 11 dependency hashes. It also revalidated all 14 hashes in the
preceding flow record and all 12 in the density written-review record.
README and ATTEMPT link the new result; prior analytic notes and their
records were not modified in this turn.

NEXT: uniformity alone does not bridge the remaining gap. In a hypothetical
divergent component of density lambda>0, choose a forward target a_(j_X)
beyond all meeting points of its finitely many starts <=X and with
a_(j_X)>X. Then R_X(a_(j_X)) equals that component's proportion up to X,
so both it and r_(a_(j_X)) can tend to lambda. First-passage uniformity
therefore supplies no smallness at such targets. A separate estimate
must rule out the possible divergent seed orbits in the finite mixture,
or establish r_1=p_1=1; nontrivial cycles also remain unexcluded.
No staging, commits, or Git writes were performed.

## 2026-10-12: unused branch mass and the reciprocal-density barrier

The full proof/disproof goal remains active and unresolved. The previous
turn was progress: its passage comparison and uniform-density deduction
were saved and verified within their stated scopes. This turn examined
whether the inverse density flow could force mass toward a finite cycle.
No complete proof, positive counterexample, or external blocker was found.

New `docs/DENSITY-BRANCH-LEAKAGE.md` makes the remaining density comparison
precise. On a hypothetical divergent Syracuse orbit b_j, discard the first
state if needed so that all b_j are odd and not divisible by three. Put
v_j=3b_j+1 and u_j=2v_j. The exact nonperiodic parent partition gives
r_(v_j)=r_(b_j)+r_(u_j); the following halving segment can add further
branches, so r_(b_(j+1))>=r_(b_j)+r_(u_j). All these densities are positive
by the already replayed external PLD theorem. Since r_(b_j) increases to
the component density lambda, the written consequences are

  sum_j r_(u_j) <= lambda-r_(b_0),
  sum_j rho_j <= (lambda-r_(b_0))/r_(b_0),
  product_(j<N)(1+rho_j) <= lambda/r_(b_0),
  rho_j = r_(u_j)/r_(b_j).

Thus a divergent component would require summable relative increases.
A bound rho(b)>=kappa/(1+log b), for all sufficiently large nonperiodic
odd b not divisible by three, would exclude divergence: Syr(b)<=2b
gives log b_j<=log b_0+j log 2, making those contributions nonsummable.
The bound is not proved. In particular divergence would force
liminf_j (1+log b_j) rho_j=0. This condition does not address cycles,
where the nonperiodic parent partition fails.

The finite-path packing bound supplies an obstruction to a tempting
weaker route. With sigma=H_2(log_3 2)<19/20 and s>sigma,

  sum_(j: b_j>=R) b_j^(-s)
    <= 256 R^(sigma-s)/(1-2^(sigma-s))  (integer R>=1).

This is a dyadic sum of the existing bound for distinct orbit values,
valid on any hypothetical divergent orbit. In particular sum_j 1/u_j is
finite. Even granting a target-uniform absolute lower bound r_a>=c/a
would therefore give only summable lower contributions at unused branches.
A scalar sequence d_(j+1)=d_j+c/u_j stays bounded on a sufficiently late
tail, illustrating that these inequalities alone do not contradict one
another. That sequence is not an actual Collatz density construction.
The same summability issue affects relative polynomial bounds with an
exponent s>sigma. A nonsummable cumulative relative estimate is needed.

A current primary-source search found and inspected Renato Augusto
Tavares, arXiv:2608.27617v1 (27 August 2026),
`https://arxiv.org/html/2608.27617`, on Wirsching's predecessor-density
program. It describes the c/a lower bound as the program's target and
leaves its condition (star 3), approached by Conjecture 2, open. Its new
theorems were not adopted as inputs or replayed here. Even the proposed
stronger lower bound would not close the above summation argument.
The existing written joint-mixing adaptation was also reread; no new
gap or new verification claim resulted, and those sources were unchanged.

New `verify_density_branch_leakage.py` builds the complete ordinary
forward graph of sources 1..524288, then aggregates distinct-source
weights through its acyclic part. The only remaining cycle is {1,2,4}.
The graph contains 1137753 vertices, maximum value 24648077896. A separate
direct replay for all starts 1..4096 took 311850 ordinary steps and
matched all 1137753 graph target counts, including zeros. The exact
parent partition was checked for all 1137750 noncycle vertices at
cutoffs 4096,8192,65536,524288: 4551000 checks in total.

The fixed example b=3077, v=9232, u=18464 has counts at X=524288:
206048 used-branch sources, 39 unused-branch sources, and 206088 sources
reaching v (including v itself). The exact finite ratio is 39/206048,
below 1/1000. At X=65536 the two branch counts are 25511 and 6; at
X=8192 they are 3263 and 0. The example converges. These observations
show finite branch imbalance, not an asymptotic upper bound on r_u/r_b,
nor a disproof of every possible logarithmic balance constant.

Verifier session 80826 finished successfully; the final record is
`results/density-branch-leakage/verification.json`, dated
2026-10-12T16:18:31.609227+00:00, with 11 dependency hashes. It revalidated
the preceding flow, uniform approximation, and finite-path packing
records (14,11,12 hashes respectively). No new Lean theorem or Lean
compilation is claimed. The old nonperiodic partition supplies the
kernel input; density limits, the logarithmic criterion, and the
summability argument remain written deductions. There is no live
process to resume. README and ATTEMPT now link this audit.

NEXT: an absolute predecessor-density improvement alone is not the
missing step. Investigate arithmetic or conditional information that
forces a nonsummable total of relative unused-branch masses, or a
different direct route to r_1=1. Do not replace actual natural-density
ratios by the recorded finite ratios without error bounds. Divergent
orbits and nontrivial positive cycles remain unexcluded. No staging,
commits, or Git writes were performed.

## 2026-10-12: an explicit density countermodel with ordinary even halving

The full Collatz proof/disproof goal remains active and unresolved. The
previous branch-density turn was progress, and this turn tests which
properties can force its missing relative inequality. No actual Collatz
counterexample, complete proof, or external blocker was found. There is
no live process to resume; verifier session 92289 finished successfully.

New `docs/DENSITY-COUNTERMODEL.md` gives an explicitly DIFFERENT map F.
Its even branch is n/2, and F(1)=4, F(4)=2, F(2)=1. Its odd branch is
changed; for example F(3)=14, whereas ordinary Collatz C(3)=10. Keep
this distinction prominent. This is a counterexample only to a proposed
deduction from general density/passage/packing properties.

Odd states are g_m=4m-3 and d_m=4m-1. For non-power m, their odd index
map removes the highest binary one, m -> m-2^floor(log_2 m). At powers,
the g-index halves toward one, whereas the d-index doubles forever.
Ordinary odd steps insert powers of two so that every target still has
at most one odd parent in addition to its even parent. The exact clocks
and special g-index-one handling are in the source and note.

Every start whose odd part is 1 mod 4 reaches the known cycle; every
start whose odd part is 3 mod 4 escapes. Both sets have density 1/2.
The escaping spine b_k=4*2^k-1 obeys F(b_k)=2*b_(k+1) and F^2(b_k)=b_(k+1).
The minimum law is p_1=1/2 and p_(b_k)=2^(-k-2), with no other atoms.

The written predecessor densities are explicit. For odd targets:

  r_(g_(2^k)) = 2^(-k-1),
  r_(d_(2^k)) = 1/2 - 2^(-k-2),
  r_(4m-c) = 2^(-k-2) for 2^k < m < 2^(k+1), c in {1,3}.

For a=2^v q with q odd and q's index in binary level k:

  r_(2q)=r_q; r_4=1/2;
  r_(2^v)=2^(1-v) for v>=3;
  r_(2^v q)=2^(-k-v) for v>=2 and q!=1.

These come from single residue classes or their complements among odd
source indices, with at most one excluded source. The even-target formulas
use a residue characterization of all possible incoming odd parents,
not an assumed exchange of an infinite union with a density limit.
Conditioning on initial valuations gives the same natural densities.
In particular every target has r_a>=1/(2a), and the target-uniform
finite-count error is <=8*(1+floor(log_2 X))/X.

First odd passage below H>=7 is explicitly periodic among odd sources
above H. For type c, use h=floor((H+c)/4), q=2^floor(log_2 h), Q=2q,
and z=m mod Q. A nonzero residue lands at z if z<=h, else z-q; zero
lands at q in the g component and never enters in the d component.
Convert indices back with 4z-c. A period P<=4H gives a limiting law
with maximum atom <=8/H, including infinity, and TV error <=4H/Y for
uniform odd sources in integer intervals [Y,2Y), Y>H. Full positive
sources have the same limit because even halving changes no passage mark.
This is stronger stabilisation than the earlier written Collatz input,
yet escape has density 1/2 in this comparison map.

Every orbit has at most ten distinct values per dyadic band: the odd
levels strictly descend before the terminal cycle or escaping spine,
each ordinary descent spike is <4 times its odd start, and a halving
block contributes at most one even value per band. The explicit spine
adds at most two values per band. Thus an arbitrary length-L integer
interval contains <=10*(log_2 L+2) distinct orbit values. Also r_a<=8/a
outside the escaping odd spine and its doubled targets; only finitely
many of those can reach a fixed target. This proves decay inside each
fixed predecessor basin while r_(b_k) increases to 1/2 along escape.

At merge 2*b_(k+1), the unused even parent is u_k=4*b_(k+1). Its density
is 2^(-k-3), and r_(u_k)/r_(b_k)=1/(b_k-1). Hence even the global lower
bound r_a>=1/(2a) coexists with summable relative branch contributions
and failure of any positive logarithmic relative lower bound along this
spine. This map does not preserve the actual Collatz odd-parent congruence
or r_a=0 at multiples of three, so it is not a countermodel to all of the
project's arithmetic statements.

New `lean/DensityCountermodel.lean` has fourteen kernel theorems: even
halving, the three known cycle edges, a positive spine bound, its one-
and two-step identities, iteration addition and both parity formulas,
nonarrival at one, a power lower bound, unboundedness, and the explicit
disagreement with C at 3. All report only standard axioms (or none).
No native evaluation, sorry, warnings, or extra axioms remain. The
density, passage, orbit classification, parent classification, and packing
arguments are written, not claimed as additional kernel proofs.

New `verify_density_countermodel.py` compiled the module afresh using
Lean4.33.1, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Only CollatzContradiction was reused after checking the cached compiler
and source/object/log hashes. Default reproduction builds both modules
sequentially. The finite replay passed:

- 512 inverse-parent targets and 393984 forward source checks;
- 8192 classified sources and 8437760 exact target-membership comparisons;
- 8192 rational density-formula targets, with parent flow checked at
  the 8189 noncycle targets;
- 129 explicit spine parameters;
- 504 first-passage residue classes and 1152 interval spot checks;
- the recorded rational finite-density and total-variation bounds.

The direct traces terminate at the known cycle or a symbolic escaping
tail proved by the new Lean module. No timeout is treated as escape or
nonentry. Records and two Lean logs are under `results/density-countermodel/`.
The final record passed at 2026-10-12T16:53:27.940017+00:00 and has nine
dependency hashes. A notation-only accidental comma in the earlier
branch note's subscript was removed; that record and the new record
track the corresponding hash updates with explicit provenance. No
mathematical statement or executable check changed in that correction.

NEXT: focus on the actual 3n+1 odd-parent arithmetic, including the
zero-density multiples-of-three property and unit preservation after
odd steps, rather than deriving the relative inequality from the general
properties refuted here. The comparison-map formulas cannot be imported
as formulas for actual Collatz densities. Both divergent ordinary Collatz
orbits and nontrivial cycles remain unexcluded. No staging, commits, or
Git writes were performed.

## 2026-10-12: actual inverse congruences and the finite-clock gap

The follow-up examined the actual odd-parent restrictions and the sibling
map b -> 4b+1. No relative density lower bound was obtained. Smaller-source
coalescence and bidirectional ranks were checked against the existing
sections 9–14 and 20–24 of APERIODIC-ATTEMPT; do not restart the excluded
fixed-horizon or finite-affine searches. No new external theorem was
adopted from this turn's literature searches.

New files:

- `docs/DENSITY-TIME-TRUNCATION.md`
- `lean/DensityTimeTruncation.lean`
- `verify_density_time_truncation.py`
- `results/density-time-truncation/{verification,replay}.json` and two Lean logs.

For ordinary C, the exact two-step parents of a are 4a, and at most one
additional source: (2a-1)/3 if a%3=2, or 2*((a-1)/3) if a%6=4.
These optional cases are mutually exclusive. The recursive inverse-list
length f_k(a), at time 2k, is periodic modulo 2*3^k. Under a shift by
2*3^k*q, its primary child shifts by 2*3^(k-1)*(12q), and its optional
child by 2*3^(k-1)*(2q). This supports the kernel induction.

Kernel evaluation of all 1458 residues proves f_6(a)<=38 for every a.
The target 364 attains 38 with a separately checked duplicate-free list.
Composition gives, for every k and target a,
  # {n : C^(2k)(n)=a} <= 2^(k mod 6) * 38^(k/6).
The exact formal cardinality statement bounds every finite distinct
source list; the inverse enumeration supplies a finite cover. Seventeen
kernel theorems passed with only standard axioms. The finite certificates
use `decide`, not `native_decide`. No added axiom or admitted proof.

Written clock corollary: at j=12q+s, 0<=s<12, the exact-time fibre has
at most 2^ceil(s/2)*38^q sources. Summing over j<=T gives fewer than
195*38^(T/12) sources reaching one target by T, uniformly in the target.
A fraction p>0 among starts through X therefore requires
  T >= (12/log 38)*log(p*X/195),
with coefficient approximately 3.29889093291 for the natural logarithm.
This is a necessary lower bound, not a sufficient time to converge or
reach a growing set. Improving the finite block maximum alone would only
improve this lower bound; it would not solve the missing termination step.

The new written density result uses the previously established written
uniform target approximation delta_X=sup_a|R_X(a)-r_a| -> 0, the written
component law, and external PLD positivity. For epsilon>0 choose delta_X
<epsilon. Then every target with r_a>=epsilon lies on one of the finitely
many complete forward orbits of starts 1..X. Outside finitely many prefix
values these form finitely many divergent tails; cyclic parts are finite.
On each divergent tail r_a tends to its component mass lambda_C. Hence
the positive accumulation values of r_a as a->infinity are exactly the
divergent component masses. In particular,
  lim_A sup_(a>A) r_a = lambda_div,
where lambda_div is the largest divergent component density, or zero
if none exist. Positivity and summability of all component masses make
a nonzero supremum a maximum. Global r_a -> 0 would exclude divergence
but allow other cycles. It has not been proved.

Let R_(X,T) count sources hitting a by time T, and
Delta_X(T)=sup_a(R_X(a)-R_(X,T)(a)). At fixed X, this defect is eventually
exactly d_X, the largest sampled fraction in one divergent component.
The lower bound holds for EVERY finite T: a late common target beyond
all sampled T-prefixes receives every source from that component.
For the upper bound, eventually the finite orbit sets of all sampled
cyclic sources have been covered. A missed target then belongs to just
one divergent component. The threshold is not supplied as a usable bound.

Thus the two iterated limits are
  lim_X lim_T Delta_X(T) = lambda_div,
  lim_T lim_X Delta_X(T) = lambda_* = max_C lambda_C.
For fixed T, the finite-fibre bound makes sup_a R_(X,T)(a) -> 0,
which proves the second equality. If full Collatz were true, the two
limits would be 0 and 1. A clock below (1-eta)*(12/log38)*log X leaves
defect tending to lambda_*. Existence of ANY clock with Delta_X(T(X))->0
is equivalent to no divergent positive orbit under the density inputs
and PLD. This is not a construction of that clock or a proof of its
existence. It does not exclude nontrivial cycles.

The verifier passed at 2026-10-12T17:26:43.837589+00:00, with thirteen
artifact/dependency hashes. It validated eleven hashes from the uniform
predecessor record and twelve from the written density record. Only the
CollatzContradiction dependency was reused after matching compiler and
source/object/log hashes; the new module was compiled afresh in 7.51s.
The compiler is the pinned Lean 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. The replay passed:

- 2184 residue fibres by ordinary one-step inversion, 28632 source entries;
- 546 residue lifts, including quotients above 2^65;
- 455 complete forward fibres at roots 0..64, times 0,2,...,12;
- 349511 forward source enumerations, with 3961386 ordinary steps;
- 95 all-depth composition checks through 36 ordinary steps;
- 4096 complete known-cycle paths, with 311850 distinct path entries
  counted separately per source;
- 93224 target comparisons across 24 finite-clock populations.

The sample cutoffs are 256,1024,4096 and their complete orbit-cover
times are 127,178,237. Their eventual defect is zero; no divergent sample
is asserted. The density limits, the spectrum, and the interchange-of-
limits analysis remain WRITTEN, not Lean theorems. The external PLD
source was not rebuilt. No current verifier or Lean process is live.

NEXT: the remaining task needs an upper estimate on the mass persisting
beyond a finite clock, or a relative unused-branch estimate, or a new
arithmetic argument. The target-uniform density limit alone supplies
neither; interpreting its finite source sample as finite-time support
would already assume away divergence. Nontrivial cycles remain a second
unresolved case. The full goal stays active. No Git writes were made.

## 2026-10-12: a typical logarithmic clock for the actual global minimum

The follow-up retained passage times while telescoping the existing
WRITTEN natural-density passage laws. It gives a new written consequence
conditional on the same unformalized Proposition 4.1, not an independent
validation of that proposition and not a proof of Collatz. No novelty is
claimed. New files are:

- `docs/CLOCKED-MINIMUM.md`
- `lean/ClockedMinimum.lean`
- `verify_clocked_minimum.py`
- `results/clocked-minimum/{verification,replay}.json` and two Lean logs.

For each positive n, M(n)=min_t C^t(n) exists and is attained at some
finite time tau_M(n), even if n diverges afterward. Every finite population
therefore has a finite common minimum-attainment clock T_B. Its existence
uses well-ordering, not convergence; no computable bound is supplied.
First ODD passage is a strict record low in the ordinary path, so entry
at time i with landing b gives M(n)=M(b), tau_M(n)=i+tau_M(b). Do not
claim that every previous ordinary state exceeds the floor: at source
85 and floor 31, odd landing 1 occurs at time 9, but even 16 is already below
the floor at time 5. Those earlier values still exceed the landing.

The first version of the argument used n0=floor(log x/(10 log2)), the
existing entry bound by n0 Syracuse steps, and the upper valuation tail
S_n0 <=(201/100)n0 outside a power-small event. Its Chernoff certificate
is the exact inequality
  101^100 * 201^201 < 100^100 * 202^201.
With r=202/201, the tail is at most q^(n0/100), where q is the ratio of
the two sides. Ordinary passage time is at most
L(x)=301 log x/(1000 log2). A test on the landing's remaining minimum
time uses g(infinity)=0, with source nonentry already charged to the
exceptional event. Nonentry is NOT inferred to imply a late minimum.

For alpha=1001/1000, descend Y_i=Y^(alpha^-i), shared floors
x_i=Y^(alpha^(-i-2)), until Y_J in [B,B^alpha). Clock sums give
E(Y,K log Y+T_B) <= C (log B)^(-c), where
  K=301000/(1001 log2)=433.817389917660... <435.
The rational checks use log2>53056/76545>693/1000. This proves the
coarse 435 log n upper clock in natural density. The later sharper
argument in Section 6 retains the clock spent by BOTH sources:

Put d=log(4/3), kappa=3/d=10.428178490346623.... For each fixed eta>0,
the ordinary first odd passage time from U_y to floor x is within
eta log x of kappa log(y/x), except with probability O_eta(x^-c_eta),
uniformly for y in [x^alpha,x^(alpha^2)]. Tao's Proposition 1.9 and
Lemma 2.2 were rechecked at https://arxiv.org/html/1909.03562v7.
Uniform residues mod 2^(3n0) give the required valuation law; a union
of Chernoff bounds gives |S_j-2j|<=h log x for every j<=n0 outside
a power-small event. Until first Syracuse entry k, exact logarithms give
  log N_j = log n - d*j - (S_j-2j)*log2 + e_j,
  0<=e_j<=j/(3x),
because all previous ODD states exceed x. Compare j=k and k-1 to
bound k, then use ordinary time k+S_k. Choose h in terms of eta.
No stochastic assertion after this first passage is needed.

Couple landing marks using their TV distance, then lift to full source
marginals by conditional distributions given each mark. When marks
match and both clocks are good,
  tau_M(n)-tau_M(m)=I_x(n)-I_x(m),
so centered times tau_M(U_y)-kappa log y and tau_M(U_z)-kappa log z
differ by at most 2 eta log x. No independence or new joint clock/landing
mixing claim is used. For D_y(w)=P(|tau_M(U_y)-kappa log y|>w), this gives
  D_y(w+2 eta log x)<=D_z(w)+C_eta(log x)^(-c).
At the final scale the centered times are bounded by the finite constant
W_B=T_B+kappa*alpha*log B. Summing clocks gives
  D_Y(W_B+2 eta log Y/(alpha*(alpha-1)))<=C_eta(log B)^(-c).
Fix eta sufficiently small for a requested epsilon, then let Y->infinity
first and B->infinity second. Odd dyadic decomposition and the initial
even-halving identity prove the written conclusion
  #{2<=n<=X: |tau_M(n)/log n-kappa|>epsilon}=o(X).
The initial even valuation a contributes only the fixed centered shift
a*(1-kappa log2); truncate large a before taking the density limit.

For a fixed positive target a, first hitting time tau_a on its actual
predecessors differs from tau_M by bounded constants depending on a:
  tau_M(n)-tau_M(a) <= tau_a(n) <= tau_M(n)+V_a.
Here V_a is the largest first hitting time of a from the finitely many
m<=a that actually reach it. If a is visited before the minimum the upper
bound is immediate; otherwise begin at that minimum. Thus a fixed target's
density captured by c log n, or the population clock c log X, tends to
zero for 0<=c<kappa and to r_a for c>kappa. Finite target profiles follow.
The case c=kappa and an effective convergence rate are NOT determined.

For Delta_X(T)=sup_a(R_X(a)-R_(X,T)(a)), the written conclusion is now
  Delta_X(floor(c log X)) -> lambda_*   if 0<=c<kappa,
  Delta_X(floor(c log X)) -> lambda_div if c>kappa.
Above kappa, choose an intermediate minimum clock and cover the finitely
many cyclic tails from minima<=B. Divergent targets receive at most the
largest sampled divergent-component fraction d_X, and a late common
target always gives the lower bound d_X. Below kappa, each FIXED target's
clocked proportion tends to zero; choose fixed targets with r_a arbitrarily
close to lambda_*, and use sup_a R_X(a)->lambda_* for the upper bound.
This avoids claiming a uniform vanishing bound on clocked proportions.

Since log(4/3)>2/7, kappa<10.5<11. Hence the computable finite-clock
proportion of starts through X reaching 1 by floor(11 log X) tends to p_1.
External PLD makes full Collatz equivalent to this specific limit being 1.
It remains unknown: a typical minimum clock does not force the minimum
to be 1, and the optimal uniform defect may still be lambda_div>0.

The Lean module has 22 kernel theorems, including minimum existence,
finite-population clocks, strict record entry, exact first-minimum suffix
transport, uniqueness, and the equality s+j=t+i for two sources meeting
at record times i,j with first minimum times s,t. It also proves finite
minimum-time equivalence with hitting 1 for an ALREADY CONVERGENT start.
The analytic concentration, real logarithms, infinite sums, and all density
limits remain WRITTEN. Only standard axioms or none are reported; no
native evaluation, sorry, warnings, or extra axioms were introduced.

Final verification passed at 2026-10-12T18:11:02.855342+00:00. The new
module compiled afresh in 1.541s with pinned Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Only CollatzContradiction was
reused after validating compiler/source/object/log hashes. The manifest
has 13 artifact/dependency hashes, all revalidated, and validates 13 prior
time-truncation hashes and 12 prior written-density hashes. Finite replay:

- 8192 complete known-cycle trajectories, with 684579 distinct path entries
  counted separately per source;
- 57344 first-record/minimum-time checks and 57344 coupled clock checks;
- 436408 target-before-or-after comparisons;
- 480 exact one-sided and 640 exact centered probability inequalities;
- 129 rational geometric clock sums and 771 ordinary budget comparisons;
- 8192 nonentry marks at the empty floor 0, not inferred from timeouts.

The exact finite maximum minimum times at cutoffs 64, 256, 1024, 4096, 8192
are 112, 127, 178, 237, 261; all those sources reach the known cycle. These
finite data do not certify an asymptotic error, rate, or divergent orbit.
The external PLD source was not rebuilt. The final verifier exited 0;
there is no live build to resume. README and ATTEMPT now link the result.

NEXT: the finite clock is now concrete, but its limiting convergence
fraction p_1 remains unidentified. Further work must constrain component
mass or use new 3n+1 arithmetic; merely improving the logarithmic time
coefficient, or treating attainment of a minimum as convergence to 1,
cannot settle the goal. Nontrivial cycles remain a separate obstruction
when studying divergence alone. The full goal stays active. No staging,
commits, or Git writes were performed.

## 2026-10-12: reflected coalescence and the actual source interval

The preceding clock turn is classified as progress: it supplied a
conditional written typical minimum clock and 22 exact kernel lemmas,
while leaving the convergence density p_1 unknown. This turn tested
whether complete-period adjacent coalescence could constrain that mass.
It found an exact limitation of the proposed statistic, not the missing
density estimate. The full Collatz goal remains active and unresolved.

New artifacts:

- docs/PREFIX-COALESCENCE-AUDIT.md
- lean/ReflectedCoalescence.lean
- verify_prefix_coalescence.py
- results/prefix-coalescence/verification.json and replay.json
- results/prefix-coalescence/CollatzAffine.log and ReflectedCoalescence.log

Let U_+ be the shortcut map and U_- its odd-offset-minus counterpart;
both halve even inputs and fix zero. Let w count odd inputs in k steps.
The kernel induction proves, whenever n+m=2^k*q,
  U_-^k(n)+U_+^k(m)=3^(w_-(k,n))*q,
  w_-(k,n)=w_+(k,m).
The current states have equal parity until the remaining factor of two
is exhausted, and the odd +/-1 offsets cancel in their sum. Specializing
to n=r, m=2^k-r gives reflection of endpoints and odd counts on the full
residue interval. The bijection r -> 2^k-1-r therefore identifies the
adjacent weighted coalescence masks of the two maps at EVERY depth.
Both endpoint agreement and equal odd counts are required for the
all-progression identity supplied by CollatzAffine.affine.

The kernel also proves that U_- traps 5 in the cycle 5,7,10 and never
reaches 1, whereas U_+^4(5)=1. Identical whole-period coalescence counts
alone do not select the basin containing one. This does not rule out
all coalescence methods and does not transfer external plus-map PLD to
the minus map. The counts through k=20 match OEIS A398792, which already
records the sign symmetry; no novelty is claimed. Primary comparison:
https://oeis.org/A398792. The first twenty counts are
  0,0,1,3,8,18,39,82,170,351,721,1476,3012,6130,12450,25241,
  51105,103358,208840,421643.

For F_X(k)=X^-1 #{1<=n<=X: U_+^k(n) in {1,2}}, every shortcut step
uses at most two ordinary steps. The earlier ordinary finite-hit bound
<195*38^(T/12) per target therefore implies the WRITTEN unconditional
bound
  F_(2^(6q))(6q) <= 390*(19/32)^q -> 0.
The same argument extends to every k=6q+s, 0<=s<6, with an absolute
constant factor. This counting consequence of a previous kernel bound
is not a new Lean theorem about real limits.

In contrast, the preceding WRITTEN density and clock arguments give
  F_X(ceil(11 log X)) -> p_1 > 0.
Sandwich ordinary first hits of 1 by floor(11 log X) below this shortcut
cycle-entry fraction, and eventual hits of 1 above it; positivity uses
external PLD. The parity period at this clock is between
X^(11 log2) and 2*X^(11 log2), so the actual source interval occupies
Theta(X^(1-11 log2)), with exponent approximately -6.62462. Averaging over
that whole period does not estimate the much shorter initial interval.
The required estimate remains
  #{n<=X: U_+^ceil(11 log X)(n)>2}=o(X).
Together with existing inputs it would settle Collatz, but this turn
does not prove it. No existence of a divergent orbit is inferred.

Fresh verification passed at 2026-10-12T18:45:01.853783+00:00 with
pinned Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. CollatzAffine compiled afresh
in 1.840s and ReflectedCoalescence in 0.439s. All seven new theorem
reports use standard axioms or none, with no native evaluation, sorry,
warnings, or extra axioms. The final record contains 12 artifact hashes,
all independently revalidated, and validates 13 hashes from each of the
clocked-minimum and time-truncation records. The verifier exited 0;
there is no live build or verification job to resume.

Independent exact finite replay checked:

- 2097170 reflected endpoint/odd-count identities;
- 2097150 reflected adjacent mask comparisons, through depth 20;
- ordinary first-one times for starts through 65536, with 142216 stored
  time rows checked by the exact step and strict decrement;
- shortcut first-{1,2} times for those starts, with 104146 such rows;
- independent direct trajectories for 4096 starts in both maps,
  totaling 307751 ordinary and 201676 shortcut steps;
- clocks at thirteen populations X=2^j, j=4..16, decided using exact
  rational upper/lower bounds on log 2 rather than floating point.

At X=65536, the ordinary floor clock is 121 and captures 41607 sources;
the shortcut ceiling clock is 122 and captures 62444. The largest entry
times in that finite interval are respectively 339 and 213. These are
finite known-cycle data, not certified asymptotic errors or rates.

The external PLD explicit coefficient construction was read locally:
b=2^80, choose a large target-dependent seed r>=16^b, m=132*r*C+1,
eta=9*(2/3)/(16*3^m), and c_a=eta/(32*r). It supplies no established
relative sibling-density estimate. No external source was rebuilt.
The public natural-density page advertises a 599-file Lean package at
https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/.
That package was NOT downloaded, replayed, or adopted. Our passage
premise and analytic consequences remain explicitly WRITTEN.

NEXT: retain the initial-interval location and actual 3n+1 arithmetic
when seeking control of p_1 or component masses. Do not replace the
needed initial-interval estimate by a full parity-period average, or
infer a density zero-one law from 2-adic Haar ergodicity. Neither this
audit nor the known coalescence sequence establishes density one.
README and ATTEMPT link the audit and its reproduction command. No
staging, commits, or Git writes were performed.

## 2026-10-12: sparse odd-output swaps retain the density inputs

The preceding coalescence turn is classified as progress: seven kernel
lemmas and exact finite data ruled out a specific inference from full
parity periods to the needed source interval. This turn tried to derive
the missing relative branch bound using actual inverse congruences.
The new evidence is a stronger comparison map: the residue restrictions,
unit-target positivity, zero density at multiples of three, and the
existing passage inputs still do not force convergence. The exact odd
parent formula at EVERY target remains an essential available distinction.
The full goal is active, with neither a proof nor a counterexample for C.

New artifacts:

- docs/SPARSE-COLLATZ-PERTURBATION.md
- lean/SparseCollatzPerturbation.lean
- verify_sparse_collatz_perturbation.py
- results/sparse-collatz-perturbation/verification.json and replay.json
- results/sparse-collatz-perturbation/CollatzContradiction.log and
  SparseCollatzPerturbation.log

Define A_j=(4^(3j+8)-1)/3, so A_0=21845 and A_(j+1)=64*A_j+21.
Let B_j=(2*A_(j+1)-1)/3; B_0=932067. We have A_j=5 mod12,
B_j=3 mod4, and A_j<B_j<A_(j+1). For t>=0, let pi_t exchange
A_j and B_j for j>=t and fix everything else. The altered map is
F_t(n)=C(pi_t(n)). Its changed input set has at most
2*(1+floor(log_64 X)) members through X. It agrees with C below A_t.
The Lean definition uses classical choice of a unique index; a finite
geometric search computes it, separately checked in Python.

The ordinary formulas are F_t(A_j)=2*A_(j+1), F_t(B_j)=4^(3j+8).
Even halving and 1,4,2 remain unchanged. The kernel proves
  F_t^(2k)(A_t)=A_(t+k),
  F_t^(2k+1)(A_t)=2*A_(t+k+1),
and never-one for this path or any source that reaches A_t. The displayed
values tend to infinity. By contrast C(A_t)=4^(3t+8), so A_t itself
is an explicitly convergent actual-Collatz start. This is NOT a positive
counterexample to C. The F_0 replay preserves every checked trajectory
from 1..64, whose largest ordinary state is 9232<A_0. Any prescribed
finite collection of trajectories is preserved by choosing a larger t.

The exact inverse formula, also kernel checked, is
  F_t(n)=a iff n=2a OR (a=4 mod6 AND n=pi_t((a-1)/3)).
Hence the allowed ordinary odd images, their uniqueness, and the
two-parent maximum remain exactly as for C. The shortcut odd parent
is pi_t((2a-1)/3), allowed precisely when a=2 mod3. Nevertheless its
VALUE differs at swapped images. For 3|a the kernel proves
  F_t^k(n)=a iff n=2^k*a.
The predecessor density there is zero by written dyadic counting.

Unit-target PLD is inherited by an exact inclusion, without the written
natural-density premise. Under the ORIGINAL C, the set of all powers
of two and all A_j, B_j, 2*A_j is forward invariant. Every c>1 with
c=1 mod12 lies outside it. Thus original paths reaching c avoid every
modified input before that hit and have the SAME hitting time under F_t.
For any positive unit a, choose e in 6..11 with 2^e*a=4 mod9 and
c=(2^e*a-1)/3. Then c>1, c=1 mod12, and F_t^(e+1)(c)=a by one
unchanged odd step and e halvings. The kernel proves
  P_c^C subset P_a^(F_t).
External PLD at this original unit c proves positive lower density at
every modified-map unit a. At a=1 it gives positive lower density of
convergence; at a=A_t it gives positive lower density of escape. No
exact fraction is asserted. Existence of modified-map natural densities
uses the additional written passage theory, not PLD alone.

WRITTEN stability of the large-floor passage input: sample odd n from
[y,2y), with x^alpha<=y<=x^(alpha^2), alpha=1.001. On the old-map
good event, first odd passage below x takes at most T=4*n0 ordinary
steps, n0=floor(log x/(10 log2)); its failure probability is O(x^-c0).
Until the first modified input the two paths coincide, and a modified
odd value <=x is already a landing, before its changed outgoing step.
Any discrepancy therefore hits a modified input above x by old time T.
All old states lie below B=2*y*4^T, with log B=O(log x). Only O(log x)
modified inputs lie there. At most 2^(T+1)-1 positive sources hit any
one target by T, and 2^T<=x^(2/5). Thus the coupling error is
  O(x^-c0)+O((log x)*x^(2/5-alpha))
  = O(x^-c0)+O(x^(-3/5)).
This transfers nonentry and uniform TV stabilization, with constants
independent of t. The clocks coincide on the coupled good event too.
It compares GROWING floors and nearby source scales, not fixed-small-
floor limiting laws or eventual basin probabilities. The asymptotic
claim remains WRITTEN and conditional on the existing C passage input.

For each FIXED shortcut depth k, only O_k(log X) sources through X
can encounter a modified input, using the same inverse-fibre union
bound and the old upper envelope 2^k X. Thus all fixed-length shortcut
parity words retain density 2^-k. This is not infinite-path randomness.
Orbit packing with the old sigma<1 also persists in writing: an F_t
path is a C prefix followed by either the explicit geometric escape or
halving into the known cycle. The additional distinct values contribute
O(1+log L) in any length-L interval.

With target densities r'_a supplied by the transferred passage theory,
the escaping odd spine satisfies the exact nonperiodic partition
  r'_(A_(j+1))=r'_(A_j)+r'_(4*A_(j+1)).
The unused/used ratios are summable, while log A_j=O(j+1). Consequently
a uniform lower ratio kappa/log A_j with kappa>0 fails in this system.
Such a relative bound cannot follow from the shared density, passage,
packing, and inverse-congruence properties alone. Every odd step on
the explicit escaping tail uses a modified input: sparsity among source
integers gives no control of concentration along an individual orbit.

Final verification passed at 2026-10-12T19:23:30.975017+00:00. The
new module contains 44 theorem declarations, with 20 main theorem roots
explicitly audited. Fresh sequential builds used Lean 4.33.1, compiler
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6:
CollatzContradiction 0.486s, SparseCollatzPerturbation 0.886s.
Only propext, Classical.choice, Quot.sound (or subsets) occur. No native
evaluation, sorry, warning, or new axiom is present. The final manifest
has 12 artifact/dependency hashes. The verifier also revalidated all
389 source/object/log triples from the COMPLETED external PLD replay
without rebuilding it, and the preceding audit's 12 artifact hashes.
All verifier processes are terminal with exit 0; nothing is live to resume.
The record's later written_scope_review adds the explicit odd-step
growth-bound limitation and refreshes only the note's hash; compiled
and finite-check artifacts are unchanged and were not rerun for that edit.

Exact finite scope:

- 384 large-index swap cases, 3072 support cutoffs through 1024 bits,
  and 768 explicit escaping-path states;
- 1048592 forward sources, compared against inverse formulas at 65536
  ordinary targets and 32768 shortcut targets;
- 16404 safe-ancestor paths, 18196 safe-target occurrences, and 252473
  unchanged safe-prefix states;
- classification of starts through 262144, using 568838 state rows
  checked by strict time decrease to either one or a proved spine;
- independent direct traces for 4096 sources, totaling 307751 steps;
- 786432 source-step comparisons for shortcut prefix coupling and
  exact finite histogram/union-bound inequalities.

At cutoffs 64,1024,16384,65536,262144 the classified escaping counts
are 0,0,1,26,123, respectively. These are finite altered-map data, not
estimates of its eventual density and not exceptional actual-Collatz
starts. No timeout is treated as an infinite orbit.

The public natural-density page and the 2026 Wirsching-program preprint
were read as scope checks; neither supplied a new adopted theorem.
The 599-file external natural-density package is still NOT downloaded
or replayed, and our analytic passage premise remains written.

NEXT: an actual-Collatz exclusion must use the exact odd-parent values
or an equally strong property that this sparse perturbation violates.
Do not infer the relative logarithmic branch lower bound from the shared
properties, finite parity statistics, or positivity alone. The original
map's upper odd-step growth bound is also violated at the upward swaps;
this construction does not test an argument that uses that bound in an
essential way. No p_1=1 estimate was obtained. README and ATTEMPT link
the result. No staging, commits, or Git writes were performed.

## 2026-10-12: weighted loss accounting for the actual Collatz formula

The preceding turn made progress: the sparse-perturbation record's twelve
hashes were revalidated before continuing. Its comparison-map result is
not an actual counterexample. This turn returned to C(n)=3n+1 for odd n
and derived an exact finite accounting identity, then a conditional
weighted escape diagnostic. The full goal remains ACTIVE and unresolved.

New artifacts:

- docs/WEIGHTED-DISSIPATION.md
- lean/WeightedDissipation.lean
- verify_weighted_dissipation.py
- results/weighted-dissipation/verification.json and replay.json
- results/weighted-dissipation/CollatzContradiction.log and
  WeightedDissipation.log

Write x_j=C^j(n), W_0=1, and multiply W by 3*x_j/(3*x_j+1) at each
odd input, leaving it unchanged at even inputs. The exact loss then is
ell_j=W_j/(3*x_j+1) at odd inputs, zero otherwise. For EVERY finite
prefix, including repeated cycle traversals,
  W_T + sum_(j<T) ell_j = 1,
  W_T = n*3^(odd inputs)/(2^(even inputs)*C^T(n)).
The Lean module defines integer numerator A, denominator B, and a
common-denominator loss L, proves A+L=B, positive denominators/numerators,
concatenation, and the affine identity with recursively defined slope
products. Reading those products as powers of three/two is written.
Positive returns necessarily include an odd input, have A<B, and their
weights repeat geometrically. The known ordinary cycle has A=3,B=4.
There are nineteen theorem declarations and eighteen audited main roots.

WRITTEN, using the existing finite-path packing estimate: W_infinity
exists by monotonicity. It is zero on every eventually periodic orbit
and satisfies exp(-8192/3)<=W_infinity<=1 on every divergent orbit.
The latter uses the reciprocal sum over DISTINCT odd orbit values.
Do not apply that packing estimate to infinitely repeated cycle visits.

Define mu_n on positive odd targets plus a separate infinity symbol by
putting every loss ell_j at x_j and placing W_infinity at infinity.
Finite telescoping plus monotone summation makes this a probability
measure. At any time i,
  mu_n = prefix_loss_measure + W_i(n)*mu_(C^i(n)),
so TV(mu_n,mu_(C^i(n)))<=1-W_i(n). For first ODD passage below H,
the prefix loss is <=(8192/3)*H^(-1/20), independently of its duration.
Only prior odd inputs need exceed H; intermediate even values may not.

CONDITIONAL WRITTEN on local natural passage Proposition 4.1: the
natural averages X^-1 sum_(n<=X) mu_n converge in TV at a logarithmic
rate to a countably additive probability measure mu. The nearby-scale
coupling and telescope work for probability-valued observables. A fixed
reference mu_n may have INFINITE support, but its finite heads are tight;
completeness in TV therefore still preserves mass one. Initial halving
does not change mu_n. No new external density premise is adopted.

For odd N, w_N(n) is its first-hit weight, zero when unreachable.
B_N=1 for nonperiodic N, and B_N=1/(1-beta_N) on a cycle, where beta_N
is its full-cycle weight. Exact pointwise geometric summation gives
  mu_n(N)=B_N*w_N(n)/(3N+1).
The TV limit supplies natural weighted means D_N=mean(w_N); partial
summation gives the same logarithmic means. In particular
  d + sum_(N positive odd) B_N*D_N/(3N+1) = 1,
  d = mean(W_infinity).
The series interchange uses TV, not only individual-coordinate limits.
At N=1, B_1=4 and the charge is D_1, not D_1/4. Positivity gives
D_1>0 and hence d<1. If Lambda_div is the TOTAL density of divergent
starts, exp(-8192/3)*Lambda_div <= d <= Lambda_div. External PLD means
any divergent orbit forces Lambda_div>0. Thus d=0 is equivalent to
universal eventual periodicity, but d=0 remains UNPROVED. This does
not exclude additional cycles or establish full Collatz.

CONDITIONAL WRITTEN on the prior ordinary clock theorem, with
kappa=3/log(4/3): mean W_floor(c log X) tends to 1 for c<kappa and to
d for c>kappa, for both population and individual log clocks. The
critical coefficient and an effective error remain undetermined.
Below the clock, omit early hits of finitely many small odd targets and
the minimum-law tail; a repeated prefix without a small hit would be a
cycle entirely above the floor and belongs to that tail. This cycle
exception is required before using distinct-prefix packing. Above the
clock, first reach the global minimum in time c' log n, kappa<c'<c;
W_t(m)->W_infinity(m) uniformly over the FINITE set m<=H, without
classifying those orbits. Tightness of minima then finishes the limit.

For fixed T, C^j(n)>=n/2^j gives
  1-W_T(n)<=(2^T-1)/(3n),
so lim_T lim_X mean(W_T)=1 while lim_X lim_T mean(W_T)=d<1.
This noncommutation persists even if all positive starts converge.

Verification passed at 2026-10-12T19:53:36.591815+00:00. Fresh sequential
Lean 4.33.1 builds (compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6)
took 0.488s for CollatzContradiction and 0.268s for the new module.
The eighteen audited roots use only standard propext, Classical.choice,
and Quot.sound, or subsets. No native computation, sorry, new axiom,
or warning occurred. Fifteen artifact/dependency hashes are recorded.
Prior records' 12 finite-path, 13 clocked-minimum, and 12 density-law
hashes were checked. The completed 389-module external PLD build was
not rerun. The later written-scope review refreshes only the new note's
hash after adding sample counts and the consequence d<1; builds and
finite replay are unchanged. All jobs are terminal with exit zero.

Independent exact rational checks:

- 2048 complete paths to the known cycle, 138104 forward prefixes;
- 1092 reverse integer recursions, 1019 concatenations;
- 4352 geometric cycle repetitions with visit multiplicity;
- 106345 full-measure cocycle coordinate comparisons;
- 5120 passage TV/product inequalities, 2196 first-hit charge coordinates,
  and 28 finite charge partitions;
- 436800 source-clock pairs at cutoffs 64,256,1024,4096,16384,65536,
  including 1920 independent direct Fraction comparisons.

At X=65536, coefficients 4,8,11,16 give ordinary clocks44,88,121,177
and mean weights approximately .92162543,.57855998,.38637200,.11060250.
The finite means have exact rational enclosures of width <=2^-48.
The clocks' floors are bounded by rational atanh-series intervals for
log 2. None of these finite intervals bounds the asymptotic error or
determines d. Sample infinite measures only use completely verified
paths into 1,4,2; no timeout was classified as escape.

External context reviewed, NOT adopted: Lucas Valbuena's public
collatz-two-coordinate-obstruction README and paper/tao-basin-densities.tex
describe uniform reciprocal predecessor bounds, stationary traces,
an occupation lower bound with divergent excess, and an inverse-path
clock. The manuscript explicitly leaves the occupation upper bound open.
The source downloaded to /tmp/collatz-tao-basin-densities.tex has SHA256
fa4e6c790002bdbb32c1679eb0b833574e110f0462f16a0e2303594137822850.
Its claimed formal bundles were not downloaded, replayed, or imported.
The local proof above uses only the already recorded written premises
and the previously replayed target-dependent PLD theorem. Do not treat
the public uniform c/N claim or its claimed audits as a new local input.

NEXT: a concrete remaining target is to prove mean W_floor(11 log X)
goes to zero for the ACTUAL map, or prove the full charge series equals
one. Both are open, and finite decay at chosen clocks is insufficient.
The conservation identity alone cannot force loss of all weight: the
packing estimate explains precisely how an escaping path could retain
a positive product. Seek an actual-map estimate on this finite mean,
not another claim that identifying the infinity atom removes it. README
and ATTEMPT link the result. No staging, commits, or Git writes occurred.

## 2026-10-12: stopped odd-count mass and the coalescence tail

The preceding goal turn made progress: all fifteen weighted-dissipation
hashes were revalidated before this follow-up. This turn tested a concrete
route to the missing mean d=0, using exact balanced adjacent coalescence
and dyadic refinement. It produced an unconditional all-depth lower
bound that prevents the simplest summable-error argument. Full Collatz
remains unresolved and the goal remains ACTIVE.

New artifacts:

- docs/COALESCENCE-TAIL.md
- lean/CoalescenceTail.lean
- verify_coalescence_tail.py
- results/coalescence-tail/verification.json and replay.json
- results/coalescence-tail/CollatzAffine.log and CoalescenceTail.log

For the ACTUAL shortcut map, Delta_H(r)=wt H r-wt H(r+1). Adding
the next source bit 2^H preserves the first H odd counts and flips
both time-H endpoint parities, since the affine slopes 3^wt are odd.
Thus the next gap either holds for both children, or is Delta_H+1
and Delta_H-1 with equal multiplicity. This remains valid at the
boundary r=2^H-1: the affine theorem permits r+1=2^H.

Define G_H=abs(Delta_H) until its first zero at time >=1, and keep
G zero thereafter. Delta_1 is always +/-1. The two children of every
depth-H node, H>=1, have G-values summing to twice the parent's value.
The kernel proves ALL-DEPTH identities
  sum_(r<2^H) G_H(r) = 2^H,
  sum_(s<2^(H-1)) G_H(2s+e) = 2^(H-1), e=0,1.
Also 0<=G_H<=H, and balanced coalescence (equal endpoint AND equal
odd count) forces G_H=0. Consequently the full-period unmerged
fraction is at least 1/H, separately for each initial parity. These
are universal integer theorems, not finite-count extrapolations.
The kernel also verifies odd-count periodicity, balanced periodicity,
and persistence of balanced coalescence with time.

Stopping is essential. For the actual pair (1,2), the signed odd-count
gaps at depths 1,2,3 are [1,0,1]. The raw absolute gap can reactivate
and does not have conserved mean. G stays zero after depth two.

WRITTEN: the coherent uniform-bit/Haar law gives a balanced fusion
time T with P(T>H)=1-p_H. The harmonic tail implies E T=infinity,
also conditioned on the first bit. This does NOT say P(T=infinity)>0,
does not use a uniform probability on all positive integers, and does
not imply any actual positive orbit escapes. It remains compatible
with p_H tending to one; no external theorem asserting that limit is
adopted here.

WRITTEN stronger bound: orient the initial gap to +1 and generate
active increments and holding bits with two independent fair-coin
stacks. Activity is determined before the next bit, and active input
orientation preserves conditional fairness. At most H-1 active steps
have occurred by depth H. Survival of a simple walk for H-1 steps
therefore ensures G_H>0. Reflection/telescoping gives
  1-p_H^(e) >= P(G_H>0|e)
             >= binom(H-1,floor((H-1)/2))/2^(H-1), e=0,1,
of order H^(-1/2). This coupling and binomial formula are NOT Lean
formalized. Python only checks their finite instances through H=20.

WRITTEN sufficient criterion for d=0: write w(n)=W_infinity(n),
f(n)=w(n)/n and h_k(x)=2^k*f(floor(2^k*x)) for 1<=x<2. The weight
cocycle gives f(n)=3^(wt H n)/2^H * f(U^H n), so balanced adjacent
starts have equal f. Since w(2n)=w(n), even dyadic children exactly
retain the parent's h-value. Odd children also do so when (2n,2n+1)
eventually balance. Let B_k be the fraction of n in [2^k,2^(k+1))
whose even pair never balances. The actual changed-cell measure is
at most B_k/2. If sum B_k is finite, Borel--Cantelli makes h_k
eventually EXACTLY constant almost everywhere. Its limit has countable
range. Existence of the prior conditional natural mean d of w gives,
by partial summation, integral_a^b h_k -> d*log(b/a). Bounded convergence
identifies that limit with d/x. For d>0 the latter cannot have countable
range almost everywhere; hence summability would force d=0.

No such summability was proved. At any finite depth H<=k+1 the dyadic
even-input interval samples whole even residue periods exactly, giving
B_k<=1-p_H^(0). Each such upper-bound VALUE is at least 1/(k+1), so
these certificates cannot be summable over k. This is NOT a lower
bound on B_k or on the actual weight-change measure. Pairs unmerged
at H can balance later, and zero infinite weights can agree without
balanced coalescence. H>k+1 returns to the proper-source-subinterval
problem in the earlier audit. Even proving d=0 would leave additional
cycle exclusion before full Collatz.

Verification passed at 2026-10-12T20:35:20.537311+00:00. Fresh sequential
Lean 4.33.1 builds used compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6, taking 0.382s for the affine
import and 0.516s for the new module. Twenty-three main roots were
audited; their dependencies are propext/Quot.sound or subsets, with
orbit_snoc using no axioms. No warnings, native computation, sorry,
or added axiom occurred. Twelve new artifact/dependency hashes are
recorded. The previous coalescence record's 12 hashes and weighted
record's 15 hashes were validated. No external replay was restarted.

Independent finite checks:

- 1,048,575 affine parity-flip pairs;
- 1,048,574 local stopped-mass identities;
- 2,097,150 pointwise gap bounds over all periods through depth 20;
- 826,010 balanced child-persistence checks;
- 48,151 direct integer pair paths, without affine recursion;
- 456 direct lifted paths at nonzero quotients 1,3,29,2^20.

At depth 20, each parity half has 524288 residues and stopped-gap
mass 524288. Positive stopped gaps occur for 133209 even and 122214
odd representatives; balanced counts are 289565 even and 132078 odd,
total 421643 as in the earlier independent enumeration. The complete
unmerged fraction is 626933/1048576. The written walk lower bound is
46189/262144, while the kernel harmonic bound is 1/20. All jobs are
terminal with exit zero.

NEXT: seek a bound on ACTUAL weighted dyadic changes (or an equivalent
finite-clock mean on the actual source interval), not a summable claim
for whole-period noncoalescence. The lower bound above closes that
specific shortcut but does not determine d. The original targets of
zero escaping mass and other-cycle exclusion remain open. README and
ATTEMPT link the new proof and reproduction command. No staging,
commits, or Git writes were performed.

## 2026-10-12: actual dyadic coalescence defects inside the known basin

The preceding goal turn made progress, with 23 audited kernel roots for
the complete-period tail. Its twelve hashes and all fifteen weighted-loss
hashes were revalidated before this follow-up. This turn strengthened
the route audit: under the already replayed positive-lower-density theorem
at one, the ACTUAL eventual-unbalanced dyadic fractions B_k are themselves
nonsummable. The weighted refinement criterion remains open. Full Collatz
is unresolved and the goal remains ACTIVE.

New artifacts:

- docs/DYADIC-COALESCENCE-DEFECTS.md
- lean/DyadicCoalescenceDefects.lean
- verify_dyadic_coalescence_defects.py
- results/dyadic-coalescence-defects/verification.json and replay.json
- seven fresh local build logs in that results directory

For a start known to reach one, define its arrival grade g(n)=t-2a,
where t is shortcut arrival time and a its odd count. The earlier grade
theorem makes this independent of the chosen arrival. Define the auxiliary
V(n)=2^g(n)/n on this basin and zero outside it. V is NOT W_infinity:
W_infinity vanishes on the entire known basin, while V is positive there.
Even steps preserve V. At an odd input before FIRST arrival, n>=3, so
  V(n)=(3n+1)/(4n)*V(U n) <=(5/6)*V(U n).
Thus 0<V(n)<=(5/6)^a<=1. The new kernel module proves the integer
strict prefix envelope
  3^(wt t n)*2^t*U^t(n) <=10^(wt t n)*n,
for positive prefixes avoiding one before time t. This avoidance cannot
be omitted: the odd input one does not have the strict factor 5/6.

The existing dyadic envelope, now specialized in a new kernel theorem,
gives t<=L+2A for any arrival from n<=2^L with a<=A. The kernel also
proves that endpoint plus the complete parity word determine the source,
and checks word length, binary entries, and odd count.

WRITTEN counting: encode the arrival length t and its at most A
one-positions, padded by zeros, using positions 1..t. With t<=L+2A,
this is an injection into (L+2A+1)^(A+1) tuples. Hence the number of
sources <=2^L with at most A odd inputs before first arrival is at most
that polynomial. No classification of other starts is used. This also
proves the natural mean of V is zero, by first fixing A and letting the
source cutoff grow, then letting A grow.

A binary refinement is called safe in the Lean module if it goes to
2n, or to 2n+1 when (2n,2n+1) eventually balances at a common time
and odd count. Kernel grade transport proves: a safe child of a
convergent root converges, with grade increased by one. Consequently
an uninterrupted safe descendant n of a fixed convergent root m at
depth k has grade g(m)+k and lies in [2^k*m,2^k*(m+1)). Thus
  V(n)>c_m=2^g(m)/(m+1)>0.
Choose A_m with (5/6)^(A_m+1)<=c_m. Its first-arrival odd count is
at most A_m, uniformly in depth. The tuple bound then shows there
are only polynomially many safe descendants versus 2^k binary choices.
The probability of remaining safe forever from any convergent root
is zero. The count and probability limits are written, not Lean formalized.

At root one c_1=1/2 and A_1=3. A separate KERNEL theorem proves the
stronger finite statement: n<2^(k+1), g(n)=k, and a FIRST arrival imply
a<=3. The proof yields 6^a<2*5^a, while 2*5^a<=6^a for a>=4.
Thus uninterrupted safe descendants from one number at most (k+8)^4
at depth k; their fraction is bounded by min(1,(k+8)^4/2^k).
This does not assert that an unsafe child fails to converge.

WRITTEN actual-interval consequence: let n_k(x)=floor(2^k*x) for
uniform x in [1,2), and let D_k be the event that the next bit is 1
AND the pair (2n_k,2n_k+1) never balances. Its measure is B_k/2,
where B_k is the fraction defined in the previous coalescence-tail note.
On S={only finitely many D_k}, all sufficiently late refinements are
safe. If such a path later visits a convergent prefix, it is then a
forever-safe chain from a convergent root. Section 3 makes each such
binary cylinder event null; the countable union over prefixes is null.
Thus on S the known-basin indicators of n_k tend to zero almost surely.
Dominated convergence gives
  limsup q_k <= P(D_k infinitely often),
where q_k is the known-basin fraction in [2^k,2^(k+1)). Positive lower
natural density delta at one implies limsup q_k>=delta. The replayed
external PLD theorem supplies delta>0, so the first Borel--Cantelli
lemma yields sum B_k=infinity. This uses NO natural-passage premise,
no natural-density existence, and no external coalescence-density-one
claim. If full Collatz holds, q_k=1 and the defects occur infinitely
often almost everywhere, while all actual infinite weights are zero.

This rules out the unweighted summability premise itself, not merely
the preceding whole-period upper-bound method. The prior implication
from sum B_k finite to d=0 remains logically valid but has a false
premise under the replayed input. The smaller actual weighted-change
sets could still be summable. A forward pointer in COALESCENCE-TAIL.md
and its document-only hash review record this development; no earlier
kernel theorem or finite replay changed.

Verification passed at 2026-10-12T21:00:26.609704+00:00. Fresh sequential
Lean 4.33.1 builds used compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Build times were 0.346s
CollatzPacking, 0.478s CollatzContradiction, 0.197s FirstPassagePacking,
0.212s FinitePathPacking, 0.923s EqualWeightFibres, 0.628s
CoalescenceGrades, and 0.298s DyadicCoalescenceDefects. Eighteen main
roots use standard propext/Classical.choice/Quot.sound or subsets;
grade_one has no axioms. No warnings, native computation, sorry, or
added axiom occurred. Twenty-two artifact/dependency hashes are recorded.
The prior records' 16 grade, 12 tail, and 15 weighted-loss hashes were
checked. All 389 external PLD module source/object/log hashes and its
lake manifest were revalidated. The completed external package and
its third-party caches were not rebuilt; this is the same adopted PLD
input, used only at one. All jobs are terminal with exit zero.

Finite checks:

- 524288 complete first-arrival integer bounds;
- 262144 doubling-grade identities and 311 leading-grade odd caps;
- 190 non-root safe descendants of one in the census;
- 4096 independent direct first-arrival paths and 205771 prefix bounds;
- 142 independently reversed parity-word certificates;
- 96 finite low-odd-count bounds and 944 direct Fraction comparisons;
- 379 safe leaf checks across roots 1,3,5,13,27 through depth 12.

At binary depth 18, there are 19 uninterrupted safe descendants of one
among 262144 possibilities. This finite count is not extrapolated to
an all-depth exact formula; the proved written bound is polynomial.
The auxiliary V mean there is approximately 0.00429495; exact rational
enclosures have width at most 2^-48. These values are NOT estimates of
d or W_infinity. All sampled starts explicitly reach one.

NEXT: actual weighted defects must exclude the many grade defects inside
the known basin. The unweighted Borel--Cantelli proxy is now ruled out.
Seek an actual-weight or finite-clock estimate that uses this distinction;
do not infer positive escaping mass from persistent unweighted defects.
Both zero escaping mass and other-cycle exclusion remain open. README
and ATTEMPT link the result and reproduction command. No staging,
commits, or Git writes were performed.

## 2026-10-12: quantitative auxiliary grade-weight moments

The preceding turn is classified as progress: it ruled out the actual
unweighted dyadic summability premise, with eighteen audited kernel roots.
This turn first returned to the weighted occupation and inverse-density
approaches. The exact inverse recursion still did not supply a uniform
upper bound over growing targets or a sharp logarithmic occupation bound.
The cached public basin manuscript was reviewed as context only: its
claimed inverse-linear floor, Green trace, and occupation assertions were
not replayed or adopted. No uniform C/N upper bound was proved or refuted.
The substantive new result is instead an unconditional power bound for
the auxiliary grade weight; it does not bound the remaining escape mass.

Added:

- docs/GRADE-WEIGHT-MOMENTS.md;
- lean/GradeWeightMoments.lean;
- verify_grade_weight_moments.py;
- results/grade-weight-moments/verification.json and replay.json;
- three fresh local Lean build logs in that result directory.

For the shortcut path x_t=U^t(n), with a_t odd inputs, define
  V_t(n)=2^t*x_t/(4^a_t*n).
An even step preserves V_t; an odd input x multiplies it by
(3x+1)/(4x)<=1. At x!=1 this is at most 5/6. Positive infinite paths
have infinitely many odd inputs, so the WRITTEN limit is the previously
defined arrival-grade V on the known basin, and zero on every orbit
never reaching one, including hypothetical other cycles and divergence.
Once one is reached the shortcut cycle preserves V_t exactly.

KERNEL integer moments: with 2^t*x_t=3^a_t*n+b_t, put
E_t=4^(t-a_t), P_t=3^a_t*E_t, Q_t=b_t*E_t. The new module defines
these recursively without rational arithmetic and proves their identities,
periodicity, envelope, and cross-multiplied monotonicity. The two next-bit
children sum to (7P,5E,7Q+2^t E). Over 0<=n<2^t it proves exactly
  sum P_t=7^t, sum E_t=5^t, 3*sum Q_t+7^t=10^t.
Periodicity permits the positive representatives 1..2^t instead.
All thirteen audited roots use standard propext/Quot.sound, with
Classical.choice also in the child and moment roots. No native evaluation,
warnings, sorry, or new axioms occur in the successful fresh builds.

WRITTEN quantitative deduction: V_t=P_t/4^t+Q_t/(4^t*n). If
c_t=Q_t/4^t then 0<=c_t/n<=1 and
sum c_t=((5/2)^t-(7/4)^t)/3 over the positive period. Split sources
at the real Y=(8/5)^t. The correction sum is at most Y+(sum c_t)/Y.
Consequently the mean of V_t on 1..2^t is at most
  (7/8)^t+(4/5)^t+(1/3)*(25/32)^t <= (7/3)*(7/8)^t.
Nonnegativity and monotonicity then give, for every integer X>=1,
  mean_(n<=X) V_T(n) <= (14/3)*X^(-eta),
  eta=log_2(8/7)=0.192645...,
whenever T>=ceil(log_2 X). The same bound holds for V_infinity.
This controls the actual initial interval, is uniform over all later
times, and uses no passage/density assumption or external PLD. The real
source split, powers, and limits are written, not additional kernel claims.
The associated dyadic amplitudes V(floor(2^k*x)) are summable for almost
every x in [1,2), by the integral bound and Tonelli. Their normalized
refinements have finite total amplitude variation; this does NOT imply
summability of the sets on which their exact values change.

The shortcut correction weight satisfies W_t=n*3^a_t/(2^t*x_t), hence
  V_t*W_t=(3/4)^a_t.
Small V_t gives no upper bound on W_t. V is positive on every convergent
start and can have zero mean even if full Collatz holds. Do not call the
new power bound a decay theorem for escape or for nonconvergent density.

A further WRITTEN criterion uses the actual escape refinements
h_k=2^k*W_infinity(floor(2^k*x))/floor(2^k*x). Under the prior natural
component law and external PLD, existence of a divergent orbit makes
the natural density lambda of divergence lie strictly between zero and
one. For any set E of natural density lambda, its dyadic-prefix indicators
converge weakly against L1 tests to lambda. Testing the set of paths with
only finitely many visits shows that set is null when lambda>0; apply the
same argument to the complement when lambda<1. Thus almost every binary
path switches between divergent and nondivergent prefixes infinitely
often. The uniform positive gap for W_infinity gives a squared h-increment
at least exp(-16384/3)/4 at every such switch. Therefore any divergent
orbit would force sum_k |h_(k+1)-h_k|^2=infinity almost everywhere.
A finite integrated squared-variation bound would exclude divergence,
but NO such bound is proved. The unconditional amplitude estimate above
is for V, not W. This criterion also leaves other cycles untouched.

Verification passed at 2026-10-12T21:35:23.422954+00:00 with pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Fresh
sequential build times were 0.372s CollatzAffine, 0.476s CoalescenceTail,
and 0.354s GradeWeightMoments. Fourteen new artifact/dependency hashes
were independently revalidated. The verifier also revalidated 22 dyadic,
12 coalescence-tail, and 15 weighted-dissipation hashes. It did not
rebuild external PLD or third-party modules; none is needed for the new
unconditional bound. All verification jobs have exited zero.

Independent finite replay checked:

- 2097150 affine data rows and the same number of positive-source weights;
- 1048575 paired next-bit moment identities;
- all twenty complete-period moment triples through depth 20;
- 41878 direct residue paths and 41858 exact Fraction dualities;
- 384 nonzero-quotient lifted data rows;
- 4096 first-arrival paths, 205771 monotonicity steps, and 101980 strict
  pre-arrival odd steps;
- 49152 known-cycle plateau steps.

At depth 20 and cutoff 1048576, the finite mean V_20 is enclosed between
0.06947364531946555 and 0.0694736453194691, with exact rational endpoints
and width below 2^-48. This is a finite-time auxiliary mean, not the
terminal V mean and not an escape estimate. The all-depth rate follows
from the identities and source split, not extrapolation of this number.

NEXT: return to actual W_infinity, or another estimate controlling p_1.
The auxiliary moment contraction has factor 7/8; its exact duality does
not transfer that contraction to W. A finite integrated squared-variation
bound is sufficient for excluding escape under the existing conditional
inputs, but no upper bound is currently available. Sharp occupation
control, vanishing escape mass, and exclusion of other cycles remain open.
The goal stays active. README and ATTEMPT include the result and command.
No staging, commits, credentials, installations, or Git writes occurred.

## 2026-10-13: actual escape-weight refinements and real-scaling rigidity

The previous turn is classified as progress: thirteen kernel roots and
the written initial-interval power bound quantified the auxiliary V, while
explicitly leaving the actual W uncontrolled. This turn returned to W.
It obtains finite-offset energy bounds, disproves two overly strong
contraction ideas, and removes an analytic premise from the sufficient
limiting-energy criterion. The needed bound itself is still unproved.
The full positive-integer Collatz goal remains active.

Added docs/ESCAPE-WEIGHT-REFINEMENTS.md,
lean/EscapeWeightRefinements.lean, verify_escape_weight_refinements.py,
and results/escape-weight-refinements/{verification,replay}.json with
three fresh local build logs. README and ATTEMPT include the new note
and reproduction command. Older checked source files and manifests were
not modified.

For shortcut x_t=U^t(n), odd count a_t, write
W_t(n)=n*3^a_t/(2^t*x_t), f_t=W_t/n. Define, for x in [1,2),
  n_k=floor(2^k*x),
  H_(s,k)(x)=2^k*f_(s+k)(n_k)=3^a_(s+k)/(2^s*x_(s+k)).
The integer offset s is fixed while k indexes binary refinement.
KERNEL even/odd path formulas yield the following WRITTEN rational
relations: the even child equals the parent exactly; the odd child is
3*2^k*f_(s+k)(3n_k+2). Both values lie in [0,1]. They are not a
martingale. With parent a and odd child b, the conditional squared
increment is (b-a)^2/2=(b^2-a^2)/2-a*(b-a); the drift has both signs.

KERNEL reciprocal affine moments: 2^t*x_t=3^a_t*n+b_t. Define
D_t=3^(t-a_t), Q_t=b_t*D_t recursively with integers. The two next-bit
children sum to (4D_t,6Q_t+2^t D_t). At every depth, over one period,
  sum D_t=4^t, 2*sum Q_t+6^t=8^t.
The scaled affine identity and periodicity are proved as well. Thus,
WRITTEN, c_t=b_t/3^a_t=Q_t/3^t has period 2^t and total
((8/3)^t-2^t)/2 over that period. Since 1-W_t=c_t/(n+c_t)<=c_t/n,
the actual-annulus mean L_(s,k) of 1-W_(s+k) satisfies
  L_(s,k) <= (1/2)*(8/3)^s*(2/3)^k.
For s>=1 the annulus lies inside one period; for s=0 it is a translated
whole period. In particular, for EACH FIXED s, H_(s,k)->1/x almost
everywhere and in L2 as k->infinity. No limit uniform in s follows.

WRITTEN energy: e_(s,k)=integral |H_(s,k+1)-H_(s,k)|^2,
E_s=sum_k e_(s,k). Compare H_(s,k) with g_k=2^k/n_k. The baseline
odd-child jump is <=2^(-k-1), and its deficit is <=1-W_(s+k).
Using the three-term square inequality gives
  e_(s,k) <= (3/8)*4^-k + (7/4)*(8/3)^s*(2/3)^k,
  sum_(k>=K) e_(s,k) <= (1/2)*4^-K + (21/4)*(8/3)^s*(2/3)^K.
Also e_(s,k)<=1/2, since even children do not change. Taking K=3s
gives E_s<=3s/2+23/4. This is an unconditional fixed-offset bound for
the ACTUAL W. Its linear dependence on s is insufficient for the needed
limiting-energy argument.

An actual infinite family rules out uniform decay of individual jumps.
For j>=1 set
  n_j=8*(64^j-1)/9, q_j=3n_j+2,
  k_j=6j-1, t_j=k_j+6=6j+5, A_j=3^(3j-1).
KERNEL formulas, with the divisible seed constructed for every j, give
  U^(t_j-2)(n_j)=A_j+1, odd_count=3j+1,
  U^(t_j-2)(q_j)=1, odd_count=1,
  2^k_j<=n_j<2^(k_j+1).
The first five steps from n_j reach 2^(6j-2)+1, then an exact affine
lift of the known cycle supplies the remaining path. q_j reaches a power
of two in two steps and halves to one. No long-term convergence claim is
made for ALL n_j. Only the stated finite trajectories are used.

At s=6 the odd child of n_j has normalized value 27/64. The parent is
9A/(16(A+1)) for even j, and 27A/(16(3A+5)) for odd j. A kernel
two-step bound for odd A>=9 yields, after written rational division,
  parent-minus-odd-child >= 27/512,
and the difference tends to 9/64. Thus maximum individual jumps do not
vanish even at fixed offset six. Their exhibited half-cells have summable
length, so this does NOT refute a uniform INTEGRATED energy bound.

The energies themselves are not nonincreasing in s. Exact finite rational
enclosures through k=12, combined with the WRITTEN tail bound for s=0,
prove E_0<1/7 and E_16>1/4. The certified upper/lower values used are
approximately 0.129820327955 and 0.258372418074. The latter is already
a finite partial sum; the former includes every later level via the
geometric tail. This disproves monotone energy contraction, not a larger
uniform bound or a bounded subsequence.

WRITTEN real-scaling rigidity removes the prior natural-passage premise
from the escape criterion. Let a(n) in {0,1} be U-invariant, and suppose
a(floor(2^k*x)) converges a.e. on [1,2). Its bounded measurable limit A
extends to all positive x with A(2x)=A(x). There is L1 convergence on
compact subintervals. Even-child invariance gives
||a(2*floor(2^k*x)+1)-a(floor(2^k*x))||_1
 =2||a_(k+1)-a_k||_1 ->0.
By the exact odd rule the first label is a(3*floor(2^k*x)+2).
Map each parent cell linearly with slope one into its corresponding
third cell. This map S_k has disjoint images, uniformly tends to 3x,
and has bounded pullback of L1 errors. Continuous approximation of A
therefore gives A(x)=A(3x) almost everywhere. In log_2 coordinates A
is periodic and invariant under irrational rotation log_2(3); Fourier
uniqueness makes it constant zero or one. L1 control of partial annuli,
not just complete annuli, then gives ordinary natural density zero or one.

Apply this to the divergence indicator. The previous WRITTEN packing
bound gives W_infinity>=exp(-8192/3) on divergence and W_infinity=0
elsewhere. A binary switch of the indicator costs at least
exp(-16384/3)/4 in squared normalized W increment. Thus finite squared
variation almost everywhere gives indicator stabilization. The rigidity
argument supplies density zero or one WITHOUT the natural-passage law.
If a divergent orbit existed, replayed PLD would give positive lower
density both to its predecessors at a unit target and to the known basin
of one, excluding both zero and one. Finite limiting energy would
therefore exclude escape using PLD and packing alone. The same rigidity
can be used for the indicator of failure to reach one, but no summability
bound for that stronger indicator is proved either.

For each fixed k, H_(s,k)->h_k=2^k*W_infinity(n_k)/n_k as s->infinity.
Fatou shows that liminf_(s->infinity) E_s<infinity would suffice for
finite integrated limiting energy. It is enough to find a bounded
subsequence at offsets tending to infinity; a supremum bound over all s
is stronger than needed. NEITHER is proved. Other positive cycles remain
unexcluded even if escape were removed.

The primary operator papers were reviewed at
https://arxiv.org/html/2106.11859v9 and
https://arxiv.org/html/2303.03203v1 . Their unweighted coefficient operator
does not equal the weighted 1/2,3/2 operator for f_t. The Hardy fixed-point
argument cannot be applied to f_infinity merely because f_infinity<=1/n.
Nonzero W_infinity is itself not square summable along a doubling ray.
No new operator theorem or other external result was adopted or replayed.

Exploratory prototypes /tmp/collatz_escape_energy.cpp and
/tmp/collatz_escape_energy_sample.cpp produced floating-point energy
data in the corresponding .csv files. The first enumerated through
level 19; the second used a fixed pseudorandom seed at larger levels
through 60. These estimates motivated investigating bounded energy, but
are NOT certificates for any uniform bound or asymptotic behavior.
Both prototype jobs exited zero. The exact new verifier supersedes their
finite scope for all quantitative claims made in the note.

Fresh verification passed at 2026-10-13T00:20:50.567988+00:00 with
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Sequential
builds took 0.360s CollatzAffine, 0.447s CoalescenceTail, and 0.492s
EscapeWeightRefinements. All twenty-one audited roots use only standard
propext/Classical.choice/Quot.sound or subsets, with no warnings, native
evaluation, sorry, or new axioms. Sixteen artifact/dependency hashes were
independently revalidated. Prior 14 grade-weight, 15 weighted-dissipation,
and 22 dyadic-defect hashes were revalidated. The external PLD record is
hashed and reused; its already replayed 389 modules and third-party
caches were not rebuilt this turn. All verification jobs are terminal.

Exact finite replay checked 524286 reciprocal affine rows, 262143 paired
moment identities, all eighteen complete-period moment pairs, 18825
independent direct paths, and 258 nonzero quotient lifts. It checked
128 jump-family members and 4092 independent two-step bounds. Energy
checks cover offsets 0,4,8,16,32,48,64 through level 12, with 114681
weight enclosures, 57337 binary energy cells, 665 independent Fraction
cells, and 91 mean-loss bounds. Enclosures use scale 2^60, not floats;
floating-point numbers are display-only. The all-depth tail and rigidity
argument remain written, not additional Lean claims.

NEXT: pursue a bounded subsequence of E_s at arbitrarily late offsets,
or a direct limiting-energy bound. Do not infer it from finiteness at
each fixed offset or from exploratory O(1)-sized samples. A martingale
argument, monotone contraction in s, and uniformly small individual
jumps are unavailable as stated. The exact drift term in the energy
identity is a possible next quantity to control on average. No escape
exclusion, other-cycle exclusion, staging, commits, installations,
credentials, or Git writes occurred. The goal remains active.

## 2026-10-13: coalescence energy caps and their unavoidable growth

The preceding completed refinement turn is progress: it gave twenty-one
kernel roots, actual-weight bounds, and a stronger written rigidity
criterion. The intervening drift, time-average, and weighted-operator
investigations did not establish the needed bounded subsequence. The
current milestone is progress: it supplies a sharper valid energy bound
and proves that a proposed method of improving it cannot remove its
growth. Full positive-integer Collatz remains unresolved and active.

Added docs/COALESCENCE-ENERGY-CAPS.md, lean/CoalescenceEnergyCaps.lean,
verify_coalescence_energy_caps.py, and results/coalescence-energy-caps
with verification/replay JSON and four fresh local build logs. README
and ATTEMPT include the result and reproduction command. Prior checked
modules, notes, and manifests were preserved.

Write p_H^(0) for balanced coalescence of even adjacent residues at
depth H, and q_H=(1-p_H^(0))/2. KERNEL persistence, refinement data
equality, and exact repeated-period counts on every dyadic source
annulus give the WRITTEN energy cap
  e_(s,k) <= q_H for every s>=0 and 1<=H<=k+1.
The depth is limited by the actual source period, not by the potentially
much longer evaluation time. The even child equals the parent; balanced
pairs have exactly equal odd-child data as well. Other jumps have square
at most one. No infinite-time fusion assumption is used.

A new independent direct census through depth twenty, without the old
high-bit lift recursion, reproduces all prior parity-conditioned counts:
  p_20^(0)=289565/524288, q_20=234723/1048576,
  sum_(H=1..19)q_H=699653/131072.
These are Python finite checks, not kernel evaluations of a million
residues. All-depth source transport is separately kernel proved.

KERNEL J(s)=ceil(121s/50) satisfies 121s<=50J<121s+50 and
  2^(3s+J(s)) <= 3^(s+J(s)).
The proof uses 2^271<=3^171 and fifty exact remainder cases, all kernel
decide, without native_decide. It follows WRITTEN that
(8/3)^s*(2/3)^J<=1. Split the energy at K=19+J, sum the first nineteen
caps, use q_20 for the next J levels, and apply the prior geometric tail:
  E_s <= (699653/131072)+(234723/1048576)*J(s)+T_19,
  T_19=(1/2)*4^-19+(21/4)*(2/3)^19.
The exact additive constant after bounding J is approximately 5.5641463,
giving E_s <= (28401483/52428800)*s+6 <= 0.542*s+6.
This improves the earlier 1.5*s+5.75 bound for sufficiently large s,
but is still insufficient for the limiting-energy criterion.

The WRITTEN obstruction concerns the strongest levelwise certificate
from these two estimates, not the actual energy:
  B_s=sum_k min(q_(k+1), (3/8)*4^-k+(7/4)*(8/3)^s*(2/3)^k).
For k<=2s the tail expression exceeds 1/2, so the minimum is q_(k+1).
The old kernel harmonic bound gives B_s >= (1/2)*sum_(j<=2s+1)1/j.
The old WRITTEN walk comparison sharpens this to
  B_s >= (2s+1)*binomial(2s,s)/4^s-1/2 ~ 2*sqrt(s/pi).
The central-binomial finite-sum identity is written and independently
checked on 257 finite cases. Thus B_s and its Cesaro means diverge even
if exact coalescence counts at EVERY depth were available. This does
NOT show E_s diverges. Actual unmerged weights can be small or zero.
Next work must retain those weights, or add information beyond these
caps and this tail; deeper full-period counts alone cannot suffice.

For any fixed H, the same argument bounds limsup E_s/s by (121/50)*q_H.
If an additional theorem establishes p_H^(0)->1, this would imply
E_s=o(s), still insufficient. That coalescence limit was not adopted.
The cited Said Duran/Gao pages at Zenodo records 23003524 and 23003500
were inaccessible through the web tool; no source was downloaded or
replayed and no external result was added. The already cached basin
manuscript remains unadopted. The unrelated OpenAI multiplicative
two-point-correlation result was not used.

KERNEL even-pair obstruction: the first POSITIVE time of equal odd
counts for 6,7 is eleven; the endpoints are then 2,1 and both counts
are five. The pair never has equal endpoints at a common clock, hence
is never balanced, although both starts reach one. For every q>=0,
the pair 2048q+6,2048q+7 has its first positive count equality at eleven
with endpoints 243q+2,243q+1 and counts five. Its stopped gap is zero
but its noncoalescence indicator is one. This one residue class is
1/1024 of even inputs modulo 2048. Eternal nonfusion is asserted only
for q=0. Equal-count absorption cannot replace actual fusion in a cap.

WRITTEN exact drift formulation: the ordinary partial-sum limit
  D_s=lim_m sum_(k<m) integral H_(s,k)*(H_(s,k+1)-H_(s,k))
exists, since the finite energy identity telescopes and fixed-offset
H_(s,k)->1/x in L2. It satisfies E_s=1/2-W_s(1)^2-2D_s.
Absolute convergence of the drift series is not asserted. A lower bound
on D_s along arbitrarily late offsets, or bounded Cesaro energy means,
would suffice for the existing bounded-subsequence criterion; both
remain unproved. Other positive cycles remain a separate open gap.

Fresh verification passed at 2026-10-13T07:39:26.462211+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Builds
were sequential: CollatzAffine 0.370s, CoalescenceTail 0.444s,
EscapeWeightRefinements 0.495s, CoalescenceEnergyCaps 0.221s. All seventeen
new roots have standard axioms only, with no native evaluator, sorry,
warnings, or added axioms. The new record has sixteen artifact hashes;
twelve coalescence-tail and sixteen actual-refinement hashes were also
revalidated. Subsequent note-only formula-formatting corrections and a
non-strict decimal comparison did not change code or theorem statements;
the record explicitly refreshes that one documentation digest.

Finite checks: 20,971,540 exact shortcut updates; 2,097,150 adjacent
residue comparisons; 4,103 first-return lifts including 2048-bit inputs;
4,096 base-pair clocks; 24,570 independent rational refinement cells at
offsets 0,7,16,32,64,128 and levels 0..11; 1,024 cutoff instances; and
257 walk-tail sum identities. All jobs exited zero. No installation,
credentials, staging, commits, or other Git writes occurred.

Exploratory follow-up after this certificate (NOT incorporated into its
verified scope): /tmp/collatz-first-count-return-moments.json contains
exact finite prefix-tree moments of endpoint separation at the first
positive equality of odd counts. Through depth twenty, conditioning on
an initial even input, the returned mass is 391079/524288, absolute
distance moment 364626/524288, and squared-distance moment
2700594/524288. The latter already exceeds one. Initial-odd values are
402074/524288, 740776/524288, and 4593136/524288 respectively.

A second exploratory state aggregation in
/tmp/collatz-count-return-state-moments.json matched those prefix data.
Until count equality, orient the lower-count endpoint as x and write
the higher-count endpoint as y=3^d*x+c, d>=1. The two fair endpoint
parities give these transitions:
  c even: (d,c/2), (d,(3c+1-3^d)/2);
  c odd:  (d+1,(3c+1)/2), (d-1,(c-3^(d-1))/2).
Initial states are (1,2) for an even pair and (1,-1) after swapping an
odd pair. At d=0 the signed offset is the return separation. The tested
invariant c<=3^d-1 gives c<=0 at return. The aggregated finite even
absolute-distance numerator already exceeds its probability denominator
at depth 27: 68790693/67108864. This calculation stopped both branches at
its planned 400000-state threshold and exited 0; their last recorded
moment rows are at depth 28.
It is not a verified all-depth moment or contraction result. Retaining
only unweighted separation moments looks inadequate for the desired
energy bound; any further use needs an exact bridge and actual weights.

Potential next algebraic input: U(n)+1=3^(n mod 2)*(floor(n/2)+1).
If y+1<=P*(x+1), then floor(y/2)+1<=P*(floor(x/2)+1).
Together these preserve y+1<=3^d*(x+1) while the count difference d
stays nonnegative, proving the observed endpoint order at first return.
This was derived on paper only in this follow-up, not added as a new
kernel theorem or used to claim an energy estimate. The missing weighted
cancellation, escape exclusion, and remaining-cycle exclusion are open.

## 2026-10-13: summable ordered drift and the remaining count reversals

The preceding turn is classified as progress: it established the sharper
energy caps and a verified obstruction to using those caps with the old
tail to get bounded energy. This turn is also progress. It controls an
infinite part of the ACTUAL weighted drift, and proves why the same
pointwise charge cannot cover its complement. Collatz is still unresolved;
the active goal is neither completed nor blocked.

Added docs/ORDERED-WEIGHT-DRIFT.md, lean/OrderedWeightDrift.lean,
verify_ordered_weight_drift.py, and results/ordered-weight-drift with
verification/replay JSON and four fresh local build logs. README and
ATTEMPT include the result and reproduction command. Older checked
source files, notes, and manifests were preserved.

For positive n, put f_t=3^a/(2^t*x_t) and z_t=3^a/(2^t*(x_t+1)).
KERNEL U(x)+1=3^(x mod 2)*(floor(x/2)+1). The WRITTEN fractions give
two decreasing sequences: f loses f/(3x+1) on odd inputs and zero on
even inputs; z loses f*x/((x+1)(x+2)) on even inputs and zero on odds.
For n_k=floor(2^k*x), write A_(s,k)=2^k*f_(s+k)(n_k)=H_(s,k),
Z_(s,k)=2^k*z_(s+k)(n_k), and g_k=2^k/n_k. Both refinements copy
their even children. They satisfy 0<Z<=A<=g<=1 on the source annulus.

Call the pair 2n,2n+1 ordered through T when its odd member's count b_i
has never fallen below its even member's count a_i for 1<=i<=T.
KERNEL all-depth propagation gives Y_T+1<=3^(b_T-a_T)*(X_T+1).
It also proves Y_T<=X_T at the first positive return of equal counts,
without identifying count equality with fusion. The exact cross product
then gives, WRITTEN, A*(A-B)_+<=A^2/(X+1), where B is the odd child
and X the parent endpoint. This is bounded by
  3*(A_(s,k)-A_(s+1,k))+2*(Z_(s,k)-Z_(s+1,k)).
The kernel checks the reciprocal cross inequality and the elementary
denominator bounds used here.

KERNEL shifted affine correction: R_t=Q_t+2^t*D_t, with the earlier
D=3^(t-a), Q=b*D, has period 2^t and satisfies
  D_t*2^t*(x_t+1)=3^t*n+R_t,
  2*sum_(n<2^t)R_t(n)+6^t=3*8^t.
WRITTEN source-annulus bounds give finite deficits
  M_s=sum_k integral(g_k-A_(s,k)) <= J(s)+3/2,
  Mtilde_s=sum_k integral(g_k-Z_(s,k)) <= J(s)+9/2,
where J(s)=ceil(121s/50) uses the previously checked cutoff. The ordered
negative drift N_ord_s is at most (3/2)*(M_(s+1)-M_s) plus
Mtilde_(s+1)-Mtilde_s. Thus its first S offsets sum to at most
(5/2)*J(S)+27/4 < (121/20)*S+37/4. This estimate is valid but is
superseded by the stronger summable bound below.

KERNEL positive-offset transitions: in an ordered downward refinement,
write Y=3^d*X+c. Initially (d,c)=(1,2). Odd parent steps keep that
state. The first even parent step gives (1,1). Subsequent even steps
alternate (d,1)->(d+1,2) and (d,2)->(d,1). An odd step after the first
even gives Y'<=3^d'*X', so closes the negative difference. KERNEL
unshifted order persists while the count difference remains nonnegative.
The WRITTEN induction therefore confines every ordered downward cell
at parent time t to a parity word 1^L 0^(t-L).

KERNEL exact count: precisely k+1 residues at depth k have a parity word
consisting of an initial odd run followed by even steps; the same count
holds on [2^k,2^(k+1)). Two next-bit children have opposite final
parities. The count recurrence is c_(k+1)=c_k+1, since appending zero
keeps every admissible prefix while appending one keeps just the unique
all-odd prefix. This is an all-depth proof, not a census extrapolation.

WRITTEN source clock: a positive n in that annulus with word 1^L0^(t-L)
satisfies 2^t*U^t(n)+2^L=3^L*(n+1) and 2^L divides n+1. Hence L<=k+1,
2^t<2^(3k+3), and t<=3k+2. For t=s+k, any ordered downward cell thus
requires s<=2k+2. Since A*(A-B)_+<=1, its integrated level contribution
is at most (k+1)/2^(k+1). Nonnegative sums give the strongest new bound
  N_ord_s <= 2 for all s,
  sum_(s>=0) N_ord_s <= sum_k (2k+3)*(k+1)/2^(k+1) = 14.
Also N_ord_s <= (K+2)/2^K for K=max(0,ceil(s/2)-1). It tends to zero
exponentially. The classification induction, height deduction, and real
summation are WRITTEN, using the new finite-step and counting kernels.
No PLD, passage law, or other external input is used for this estimate.

The full fixed-offset drift series is now shown WRITTEN absolutely
convergent: the earlier geometric bound makes sum_k sqrt(e_(s,k))
finite, and Cauchy--Schwarz bounds each absolute drift integral by that
square root. The old note only asserted ordinary convergence, which
remains true. This is not a bound uniform in s.

N_rev_s is the complementary negative drift from cells whose odd-count
order has reversed at some earlier or current clock. The energy identity
gives E_s<=1/2+2*N_ord_s+2*N_rev_s. Thus bounded Cesaro means of N_rev
along an unbounded sequence of offset counts would suffice for the prior
bounded-energy-subsequence criterion and, using prior packing and the
replayed external PLD, exclude escape. This estimate is OPEN. It is a
sufficient criterion, not asserted necessary: positive drift might also
cancel an unbounded negative part. Other positive cycles remain open.

KERNEL n=37,k=5,s=6 has reversed pair counts 5,4 and endpoints 5,2;
its downward values are 243/320 and 81/128. Both sources reach one.
A KERNEL specialization of the earlier jump family gives a stronger
WRITTEN obstruction to an immediate parent-loss estimate. For even j>=2,
  n=8*(64^j-1)/9, k=6j-1, s=6, Astar=3^(3j-1),
the parent endpoint is the odd number (Astar+1)/4, its count is 3j+1,
and the odd child's count at the matched pair clock is three. The parent
value P=9*Astar/(16*(Astar+1)) and child B=27/64 satisfy
  P*(P-B)/(P-A_(7,k))
    =9*(Astar-3)*(3*Astar+7)/(256*(Astar+1)) -> infinity.
The shifted parent loss is exactly zero. P*(P-B)->81/1024 while the
unshifted loss tends to zero. Thus NO fixed multiplier of the two
immediate parent losses bounds all reversed downward cells. The family
half-cells have summable lengths, so this does not refute an INTEGRATED
bound. No universal eventual behavior of that family is asserted.

Fresh verification passed at 2026-10-13T14:22:16.286386+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All
31 audited new roots use standard axioms only, with no warnings, sorry,
native evaluator, or new axioms. The four builds were sequential.
Sixteen hashes in each of the preceding refinement and energy-cap
records were revalidated. No external replay or installation was needed.

Independent exact checks covered 1048576 adjacent pair clocks, 805599
ordered endpoint/cross-product checks, 6820 first positive count returns,
32770 ordered negative parity/height checks, 524287 shifted affine rows,
524287 annulus parity rows, 405 nonzero quotient lifts, all moment and
one-turn counts through depth 18, 200606 rational refinement/time-loss
cells, 157635 ordered time charges, 2156 annulus deficit bounds,
97 cumulative budgets, 64 even-indexed jump-family members, and 1024
cutoff/constant checks. Integrated finite sums use rational enclosures
at scale 2^64; floats are display-only. These checks do not establish
any late-offset bound on N_rev. Every verification job is terminal.

The external basin repository's current README was reviewed through
the web tool, including newer stationary-density claims. None was
replayed or adopted, and none is an input to the new result.

NEXT: control the actual reversal contribution over source intervals,
or its cancellation with positive drift. Do not revisit the ordered
part as though it were still an unbounded error. A uniform pointwise
charge to the parent's next time step is impossible by the family above.
Earlier unweighted first-count-return distance moments are also not
contractions; any induced-pair estimate must retain the actual weights.
The full Collatz goal remains active. No staging, commits, credentials,
installations, or other Git writes occurred.

## 2026-10-13: persistent reversals require averaging across source cells

This follow-up is progress, not completion of the Collatz goal. It proves
a stronger obstruction to the parent-loss approach and records a precise
remaining averaging question. Escape and additional cycles remain open.
The prior ordered-drift result and its verification record were preserved.

Added docs/REVERSAL-PERSISTENCE.md, lean/ReversalPersistence.lean,
verify_reversal_persistence.py, and results/reversal-persistence. README
and ATTEMPT link the result and reproduction command. Eight new kernel
roots use standard axioms only. No new external theorem was adopted.

KERNEL, for all h,x, with a=wt(h,x), y=U^h(x):
  3*2^h*y+3^a <= 3^a*(3x+2^h),
  2^h*(y+1) <= 3^a*(x+2^h).
WRITTEN these give W_h(x)>=3x/(3x+2^h-1), z_h(x)>=1/(x+2^h).
For a parent value P at endpoint X and its shifted value Z=PX/(X+1),
after h more steps the cumulative parent charge satisfies
  3*(P-P_h)+2*(Z-Z_h) <= 3P*(2^h-1)/X.
It tends to zero whenever 2^h/X tends to zero, not only at fixed h.

Use the prior family, even j>=2:
  n=8*(64^j-1)/9, k=6j-1, R=3^(3j-1), X=(R+1)/4.
At s=6 its parent is P=9R/[16(R+1)] and its odd child B=27/64.
Set H=3j-5. KERNEL: for every 0<=h<=H, 4*2^h<=X,
the actual parent at offset 6+h is >=1/2, the actual odd child is
<=27/64, and the history includes a count reversal. The parent lower
bound and child ceiling are checked as integer cross products of actual
orbit/weight expressions, not just arithmetic on assumed endpoints.

WRITTEN each such cell has negative product >=5/128 and square gap
>=25/4096. The 3j-4 consecutive offsets therefore have accumulated
negative drift >=5*(3j-4)/128. Yet the entire future parent charge
telescopes to at most 3P+2Z<45/16, regardless of the parent's eventual
behavior. No uniform multiplier can charge a cell's accumulated drift
to all that parent's future losses; it would have to exceed (3j-4)/72.
Also no fixed lookahead charges the initial jump, whose negative product
tends to 81/1024. Even the displayed linear-in-bit-length horizons fail
to charge the initial jump, since 2^H/X tends to zero. Thus replacing
the failed immediate charge with a bounded block is insufficient.

The guaranteed persistence rectangles have total source/offset measure
sum_(m>=0)(6m+2)/2^(12m+12)=2q(1+2q)/(1-q)^2, q=2^-12, finite.
This is only the measure of the stated finite horizons. It is NOT a
proof of all-time integrability of this family's contribution. These
obstructions still do not disprove an averaged source-interval bound.

Precise OPEN sufficient estimate: let L_(s,k) be the sum of
3*(A_(s,k)-A_(s+1,k))+2*(Z_(s,k)-Z_(s+1,k)) over all parent sources
2^k<=n<2^(k+1), multiplied by the half-cell length 2^(-k-1).
If N_rev_(s,k)<=C*L_(s,k) uniformly, the earlier deficits give
sum_(s<S,k)L_(s,k)<=(5/2)*ceil(121S/50)+27/4. Together with the
ordered total <=14, this yields the WRITTEN conditional conclusion
limsup_S (1/S)*sum_(s<S)E_s <= 1/2+121C/10. This would feed the prior
escape criterion, but no such C is proved and other cycles remain open.

Independent exact finite annulus checks support C=8 only on
0<=k<=10, 0<=s<=96. They certify that C=6 already fails at k=5,s=46,
where the exact ratio is approximately 6.607568163248772. Decisions
use fractions and rational enclosures at scale 2^64; decimals are
display-only. This is not evidence of a verified all-level constant.

Fresh verification passed at 2026-10-13T15:10:45.976999+00:00 on
pinned Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All five local modules were freshly compiled sequentially. The eight
new roots use only propext/Quot.sound; no warnings, sorry, native
evaluation, or extra axioms. All 16 prior ordered-drift hashes were
revalidated. New independent checks cover 528384 endpoint clocks,
36876 retained-half comparisons, 64 family members and 12224 persistent
offset cells, 198559 rational annulus cells, and 1067 finite C=8 bounds.
The first replay reached all checks but hit Python's decimal-digit limit
when serializing huge exact sum denominators. Cumulative family sums
were changed to exact rational enclosures, and the full replay passed.
This was a reporting-size issue, not a failed mathematical inequality.

Uncertified exploratory files, NOT inputs to the result:
/tmp/collatz-reversal-average-charge.cpp and its two CSV outputs scan
floating normalized weights through k=20,s=1024. The levelwise maximum
ratio there decreases from 6.607568 at k=5 to about 1.02274 at k=20.
There is no all-level estimate. /tmp/collatz-time-area-samples.py and
its JSON sample 2000 sources at each bit length 20,40,80,160,320,640,1280.
Exact integer trajectories but floating weight sums give mean all-time
per-level energies approximately 3.47,4.32,5.77,7.44,8.54,10.39,10.15;
all samples reached {1,2}, with an explicit two-step geometric tail.
These samples are not a uniform bound, nor a proof about untested sources.
Do not mistake time summability at every cell for an easy substitute:
it would already force equality of the limiting adjacent weights.

The external basin manuscript and quadratic-cylinder-energy manuscript
were browsed again for quantitative coalescence or occupation input.
No newly reviewed claim was replayed or adopted. Zenodo 23003500 and
the GitHub formal-periodic-census directory/README remained inaccessible
through the web tool. The former source's almost-sure inverse-height law
explicitly lacks the expectation/occupation upper bound needed to close
its separate route. Its Haar stationary-density claims concern a
different measure from actual integer trace values.

NEXT: attack the whole-source averaging estimate or signed cancellation.
Do not retry immediate, fixed-block, or cell-by-cell total-future loss
charges: the new all-parameter family rules them out. The ordered part
is already summable. All verification jobs have terminated; no agents,
installations, staging, commits, or credentials were involved.

## 2026-10-13: count-return control and sublinear actual energy

The previous reversal-persistence turn was progress and its fourteen
recorded hashes were revalidated at this turn's start. This turn makes
further progress: a new WRITTEN probability argument bounds repeated
count-gap restarts and gives actual energy E_s=O(s^(4/5))=o(s).
This is not bounded energy, escape exclusion, or a solution of Collatz.
The full goal remains active; no blocked condition has been declared.

Added docs/COUNT-RETURN-CONTROL.md, lean/CountReturnControl.lean,
verify_count_return_control.py, and results/count-return-control.
README and ATTEMPT describe the result and reproduction command.
The twelve kernel roots are arithmetic inputs. The stopping-time,
fractional-moment, finite-set, probability, and real-energy proofs are
WRITTEN, not completely Lean formalized. No external coalescence theorem
was assumed, installed, or replayed, and no novelty claim is made.

The probability law is Haar-uniform binary input, equivalently uniform
complete residue periods. After any exposed prefix, both endpoints are
odd affine functions of the remaining Haar input. Each marginal next
parity is fair; the pair is dependent. Countably partitioning by finite
prefixes gives the same property at an almost-surely finite stopping time.
These are not probabilities uniformly sampling all positive integers.

KERNEL exact unstopped gap accounting: the two next-bit absolute gaps
sum to twice the current absolute gap, plus two exactly when the current
gap is zero and the endpoint parities differ. Thus the normalized
full-period first moment increases by the departure-from-zero probability.
This includes all restarts, unlike the old stopped-gap identity.

WRITTEN uniform first positive count-return tail:
  Pr(tau>H) <= 16 H^(-1/5), for every starting separation D>0.
While counts differ by d>=1, orient Y=3^d X+c. The lower-count endpoint
X is conditionally Haar. Holding for h steps is equivalent to
  (3^d-1)X+c == 0 mod 2^h.
If v=nu_2(3^d-1), this event has probability <=min(1,2^(v-h)).
KERNEL 0<3^d-1<2^(2d), so v<=2d-1. The expected clock until the next
active gap step is <=v+2<=2d+1, uniformly in c. The active gap is a
simple symmetric walk absorbed at zero. Up to m active steps it has
physical expected clock <=3(m+1)^2 and survival <=2/sqrt(m+1).
Markov with m=floor(H^(2/5)) yields the displayed tail and proves the
first return is finite almost surely. An initial even separation returns
after one step; an odd one departs to absolute gap one.

WRITTEN stopped moment, with all stopping justified rather than inferred
from fixed-time bounds: U^t(X)=lambda_t X+B_t,
lambda_t=3^a/2^t, B_(t+1)=m_t B_t+epsilon_t/2. Marginal parities are
independent fair bits. At alpha=1/2, r_alpha<31/32 gives E B_t^alpha<=16.
For beta=1/16, Holder on dyadic events 2^(j-1)<tau<=2^j gives
E[B_tau^beta; event] <=64*2^(-j/20). The tau=1 contribution is <=2;
sum 2^(-j/20)<50, so E B_tau^beta<=3202 for either endpoint, uniformly
in D. The nonnegative supermartingale lambda_t^beta and optional stopping
give E lambda_tau^beta<=r_beta<509/512. At equal counts the slopes agree,
so the new separation D' satisfies the WRITTEN drift inequality
  E[(D')^(1/16) | D] <= (509/512) D^(1/16)+6404.
No independence between the two corrections is used.

WRITTEN finite expected number of count-return cycles:
take V(D)=D^(1/16), R=1093120^16<2^336. Outside D<=R, the drift is
at most -1, so expected return cycles to that finite set are <=V(D).
KERNEL prescribed descent transitions: for even D choose both even to
get D/2. For odd D choose the lower endpoint even to obtain count gap one
and c=(3D+1)/2; keep choosing both even until c is odd, then choose the
lower-count endpoint odd. This first count return has D'=(c-1)/2<=
(3D-1)/4. Thus prescribed returns decrease separation by factor <=3/4.
From D<=R, 1344 returns suffice for fusion, using <=338 bits per return.
The success probability is >=2^(-454272). After an attempt, expected
V is <2186070. Including the next visit to D<=R, each attempt has
expected length <=2187414 return cycles. Conditional success is uniformly
positive, so from adjacent starts the expected number N of return cycles
until balanced fusion is bounded by
  C_star = 2187414 * 2^454272.
This enormous explicit constant is finite; no numerical optimization is
claimed. The integer comparisons for all constants are kernel checked.

WRITTEN consequences:
  E|a_t(x)-a_t(x+1)| <= C_star for every complete-period depth t;
  1-p_H <= 21*C_star*H^(-1/5).
For the latter, E min(tau,H)<=21H^(4/5) uniformly at each return. Whether
cycle j is needed is determined before it starts. Conditional expectation
and Tonelli therefore bound E sum_(j<=N) min(tau_j,H) by
21*C_star*H^(4/5); on T>H this sum is >=H. This avoids any independence
assumption about return times or the number of returns. Conditioning on
either first parity doubles these bounds. The existing H^(-1/2) lower
bound and infinite physical mean coalescence clock are compatible.

Apply the old KERNEL actual-annulus cap e_(s,k)<=q_(k+1), where
q_H=(1-p_H^even)/2, plus its WRITTEN geometric tail. For
J(s)=ceil(121s/50), the new WRITTEN actual energy bound is
  E_s <= (105/4)*C_star*J(s)^(4/5)+23/4.
Thus E_s=o(s), without adopting any new external result. The old
0.542s+6 bound remains much better at practical offsets because C_star
is huge. Neither estimate supplies a bounded-energy subsequence.

Fresh verification passed at 2026-10-13T15:49:07.064642+00:00 using
pinned Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Four local modules were freshly compiled sequentially. All twelve new
roots use standard axioms only; no warnings, sorry, added axioms, or
native evaluation. The sixteen energy-cap and fourteen reversal-persistence
hashes were revalidated. No previous source or manifest was rewritten.

Independent exact checks: 131056 actual pair residue paths, 208 complete
state distributions for initial separations 1..16 through depth 12,
25 exact raw-gap recurrences through depth 24, 216189 state nodes,
270072 holding-prefix/congruence comparisons, 1320 exact congruence counts,
and actual balanced-fusion witnesses for every separation 1..8192. Those
witnesses use 173305 prescribed bits and 86026 strictly descending return
cycles in total; maximum witness clock 33 and return count 19. They were
recomputed as actual integer orbits, not only as offset-state transitions.
The full adjacent depth-24 law has raw gap mass 32206350, restart mass
421301, and balanced mass 6966495 over denominator 16777216. Finite checks
do not substitute for the all-depth probability proof.

Uncertified exploration retained in /tmp/collatz-full-gap-moments.json
(initial even branch, state aggregation through 29 further clocks) and
/tmp/collatz-full-gap-samples.json (5000 random state paths, seed
2026101302, through 32768 clocks). The samples suggested bounded mean
restart count and motivated the fractional-moment argument; neither file
is an input to the new theorem or verification record.

NEXT: use the uniform FULL count-gap moment and return-separation moment
to control the actual weighted reversal contribution, or its signed
cancellation, across source intervals. Do not treat the old stopped-gap
mean-one identity as if it included restarts. Optimizing the unweighted
coalescence exponent alone cannot establish bounded energy: the earlier
cap-plus-tail obstruction still applies. Full escape and cycle exclusion
remain open. All checks are terminal; no agents, staging, commits,
installations, credentials, or other Git writes were used.

## 2026-10-13: actual-annulus logarithmic height coupling and return transport

The preceding count-return turn was progress; its fourteen recorded
hashes were revalidated before use. This turn is progress as well: it
transfers the full count-gap control to actual real endpoint heights,
adds a cumulative return-separation budget, and identifies the exact
arithmetic-progression factor in a prospective weighted-energy transfer.
The full Collatz goal remains active and unresolved.

Added docs/ANNULUS-HEIGHT-COUPLING.md, lean/AnnulusHeightCoupling.lean,
verify_annulus_height_coupling.py, and results/annulus-height-coupling.
README and ATTEMPT link the result and reproduction command. Twelve
new kernel roots cover integer height and count identities. Logarithm,
threshold, probability, and cumulative-return consequences are WRITTEN.
No new external theorem or package was used.

Let t>=1, N=2^t, m=N+2r for 0<=r<N/2, X=U^t(m), Y=U^t(m+1),
and a,b their odd counts. These are actual even/odd refinement pairs
at source level k=t-1 and offset zero, not arbitrary later clocks.
Set u=X/3^a, v=Y/3^b. The KERNEL normalized-height comparison gives,
after WRITTEN division,
  mean |u-v| <= (2/3)^t,   u,v>=1.
It uses the earlier exact correction moment
2*sum_(n<N)Q_t(n)+6^t=8^t. The checked integer form is
  2^(t+1)*sum_(r<N/2)|h_t(N+2r+1)-h_t(N+2r)| <= 8^t,
where h_t(n)=3^(t-a_t(n))*U^t(n). Height lifts add the same 3^t*q
to both scaled endpoints, so the gap transports exactly to the annulus.
The individual difference is bounded by the two nonnegative affine
corrections plus the source increment; the correction moment cancels
the remaining source-increment term in the complete even/odd sum.

WRITTEN log comparison, because u,v>=1:
  mean |log(Y/X)-(b-a)*log(3)| <= (2/3)^t.
The earlier full-gap bound conditioned on even input yields
  mean |log(Y/X)| <= 2*C_star*log(3)+(2/3)^t.
Equivalently, integrate over all logarithmic height thresholds z the
probability that exp(z) lies between X and Y; that total disagreement
has the same uniform bound. This gives an actual height-coupling budget.
It does not claim future weight is a monotone function of height.

KERNEL signed count mean is exactly one: mean(b-a)=1 on every such
actual annulus. Hence WRITTEN
  |mean log(Y/X)-log(3)| <= (2/3)^t.
Meanwhile the earlier written coalescence rate gives probability
log(Y/X)!=0 <=42*C_star*t^(-1/5), tending to zero. These logarithmic
differences are therefore NOT uniformly integrable, even though their
first absolute moment is bounded. For every 0<theta<1, Holder gives
mean |log(Y/X)|^theta=O(t^(-(1-theta)/5)). Do not replace the first
moment bound by first-mean convergence; its signed limit is log(3).
None of this lower-bounds actual refinement energy.

Additional WRITTEN return budget under the Haar binary law: let D_j
be the separation at count-return cycle boundaries, D_0=1, with N
cycles until fusion. Applying the earlier drift with absorption at zero
and telescoping deterministic truncations gives
  E sum_(j<N) D_j^(1/16) <= (512/3)*(1+6404*C_star).
Also log(1+D)<=16D^(1/16), so the total expected logarithmic separation
cost over all these returns is finite. This is NOT asserted for a
finite uniform integer interval followed indefinitely past the end of
its source bits. The distinction between those laws remains essential.

Exact return transport: if r,r+1 first have equal counts a at clock tau
and endpoints x0,y0, then for every q>=0 their lifted endpoints are
  X(q)=3^a*q+x0, Y(q)=3^a*q+y0.
With lambda=3^a/2^tau and f_h(n)=3^a_h/(2^h U^h(n)), the difference
at clock tau+h is lambda*(f_h(X(q))-f_h(Y(q))). For source annulus
[A,2A), A=2^K,K>=tau, a fixed even prefix has q=Q..2Q-1, Q=A/2^tau.
Put M=3^a Q=lambda*A. Its normalized squared contribution is
  lambda*M*sum_(q=Q..2Q-1) G_h(3^a*q+x0)^2,
where G_h(x)=f_h(x)-f_h(x+y0-x0).
The endpoint sample is one progression of spacing 3^a inside an interval
of length M. To recover the binary branch factor 2^(-tau) by interval
averaging requires paying for that spacing. Trivial inclusion instead
retains lambda, larger by 3^a. The note gives an explicit unproved
progression-versus-interval inequality, while also warning that this
inequality alone would not settle the other transport and tail issues.

An independent exact finite witness shows substantial progression bias.
For tau=10,r=200,a=4, first-return endpoints are 17,16. At Q=1 the
progression samples 98,97, with containing interval 98<=x<179. At
continuation clock h=128,
  81*(f_128(98)-f_128(97))^2 /
     sum_(x=98..178)(f_128(x)-f_128(x-1))^2
  =10453976883/926254009 >11.
All 82 sources 97..178 are checked to lie in {1,2} by this clock. Thus
even a factor of eleven fails for this finite progression comparison.
It does not exclude every possible uniform constant, and it is NOT the
earlier, different whole-annulus parent-loss inequality with tested C=8.

Fresh verification passed at 2026-10-13T16:27:34.956994+00:00 on
pinned Lean 4.33.1, commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Five local modules were built
sequentially; the twelve new roots use standard axioms only, without
warnings, sorry, extra axioms, or native computation. The previous
count-return record's fourteen hashes were checked without modifying it.
Independent exact checks cover 524287 actual even-annulus pairs through
clock 19, 284 quotient lifts, nineteen full mass/count identities,
5540 first-return prefix-tree edges and 245 first-return prefixes,
960 exact lifted weight factorizations, 384 progression-energy transports,
and the 82 cycle endpoints in the finite bias example. Floating logarithm
table columns are diagnostic only and make no verification decisions.

Exploratory /tmp/collatz-return-progression-late-ratios.json computes
late-even-clock ratios for 64 nonfused prefixes using known-basin arrival
grades. Its largest observed ratio motivated the independently replayed
h=128 example above; the exploratory file is not a proof input. No claim
of an all-prefix progression bound is made.

NEXT: control the actual weighted progression averages, possibly after
aggregating several returned residues, using the available total return
cost. The bounded logarithmic height coupling covers the source-bit
boundary only and cannot by itself propagate to arbitrary later clocks.
Do not silently turn a ternary progression into an interval average or
replace bounded first moments by uniform integrability. The actual
energy bound remains O(s^(4/5)); bounded energy, escape exclusion, and
additional-cycle exclusion remain open. All jobs are terminal; no agents,
installations, credentials, staging, commits, or other Git writes occurred.

## 2026-10-13: square-root count-return clock and the remaining sampling gap

The preceding actual-annulus height-coupling turn was progress, and its
fifteen hashes were authenticated. This turn is progress too: it improves
the WRITTEN clock and energy exponents, strengthens the return-separation
moment range, and gives an all-parameter obstruction to a raw image-column
bound. Collatz remains unresolved, and the full goal remains active.
No unchanged blocker was declared.

Added docs/COUNT-RETURN-CLOCK.md, lean/CountReturnClock.lean,
verify_count_return_clock.py, and results/count-return-clock. README and
ATTEMPT include the result and reproduction command. Fifteen new kernel
roots are arithmetic inputs; the probability, real-energy, moment, and
raw image-density deductions are WRITTEN. The prior source files and
verification records were authenticated without modification.

WRITTEN uniform first positive count-return tail, for every separation D>0:
  Pr(tau>H) <=7/sqrt(H), H>=1.
Even D has tau=1. For odd D, the first step gives absolute count gap one.
At a nonzero gap d, orient Y=3^d X+c with X conditionally Haar. The prior
congruence gives expected wait to the next active step <=v(d)+2, uniformly
in c. The exact valuation is v(d)=1 for odd d and 2+nu_2(d) for even d.
KERNEL cofactors prove 3^u=3 mod8 for odd u, then
3^(2^(j+1)u)-1=2^(j+3)*q with q odd, and nondivisibility by the next power.
Decomposition of d and the valuation interpretation are written.

Count multiples of powers of two to get
  B(n)=sum_(d=1..n) nu_2(d)=sum_(r>=1) floor(n/2^r)<=n,
  C(n)=sum_(d=1..n)(v(d)+2)=3n+floor(n/2)+B(n), 2C(n)<=9n.
The repeated-halving bound and integer cost bound are kernel checked;
the finite double-sum interpretation is written.

Stop the embedded active simple symmetric walk, starting at one, when
it hits 0 or K. Its upper-exit probability is 1/K, and expected visits
to d before exit are G(1,d)=2(K-d)/K<=2, 1<=d<K. The kernel checks the
cross-multiplied finite Green equations, boundaries, and cap. The finite
walk interpretation and uniqueness are written. Conditioning before
each holding wait and using Tonelli gives, including the initial step,
  E sigma_K <=1+sum_d G(1,d)(v(d)+2)<=1+2C(K-1)<=9K-8.
No independence of holding times and subsequent exit events is assumed.
Then Pr(tau>H)<=1/K+(9K-8)/H. Set K=floor(sqrt(H)/3)+1 to obtain
7/sqrt(H). This replaces the earlier, weaker H^(-1/5) bound without
changing that prior authenticated proof or its constants.

WRITTEN consequences using the existing C_star=2187414*2^454272:
  E min(tau,H)<=14sqrt(H),
  Pr(balanced fusion clock T>H)<=14*C_star/sqrt(H).
Conditioning on either first input parity doubles the latter bound.
Predictable cycle gating and the existing E N<=C_star justify the sum
of truncated waits; no independent-cycle assumption is used. The old
central-binomial lower bound has the same H^(-1/2) order. Infinite mean
physical coalescence time is still consistent with these estimates.

With the existing actual-annulus cap and J(s)=ceil(121s/50),
  E_s <=28*C_star*sqrt(J(s))+23/4 =O(sqrt(s)).
The old 0.542s+6 bound still has a much smaller practical constant. The
coalescence-cap-plus-tail certificate now has matching square-root upper
and lower orders. This is NOT a square-root lower bound for actual E_s.
Further improvement to bounded actual energy needs the weights or signed
cancellation, not a better power in unweighted coalescence alone.

WRITTEN stronger return-separation budget: for every 0<beta<1/3,
  E sum_(j<N) D_j^beta <infinity.
Choose 3beta<alpha<1. Fixed-time alpha moments of the affine correction
B_t are bounded by M_alpha=2^(-alpha-1)/(1-r_alpha), r_alpha<1. On a
dyadic stopping block, Holder plus the new return tail gives decay
2^(-j(1-3beta/alpha)/2). Thus E B_tau^beta<=B_beta<infinity uniformly
in starting separation, and optional stopping gives
E lambda_tau^beta<=r_beta<1. Consequently
  E[(D')^beta|D]<=r_beta D^beta+2B_beta,
  E sum_(j<N) D_j^beta <=(1+2B_beta*C_star)/(1-r_beta).
No endpoint result at beta=1/3 is proved, and this budget is under the
Haar binary law, not indefinite continuation of a finite integer interval.

WRITTEN raw image-coefficient obstruction, independently checked on
finite family members: choose v_m odd in 1..127 with
3^m v_m=125 mod128; r_m=2^(m+1)v_m-2; tau=m+8; a=m+5. Parent parity
word is 0, then m ones, then 0011111; child word is 1, then m ones,
then 0110110. After the initial and common-odd steps, X=128z+124,
Y=384z+374. The seven-step suffix returns first to equal counts at
endpoints 243z+242 and 243z+238. Their separation is four, while
  lambda=3^a/2^tau=(243/256)*(3/2)^m ->infinity.
The larger base endpoint is (3^(m+5)*v_m+601)/128. This family is not
among the fifteen new Lean roots; its all-parameter proof is written.

For nonfused even first-return prefixes, the raw ternary density
K_H(z)=sum_(tau<=H)lambda*1_(z=x0 mod3^a) has Haar integral
sum2^(-tau)<=1/2 by prefix freeness. Its increasing limit is integrable.
But the displayed family makes its essential supremum unbounded, and
also makes the raw positive-integer columns unbounded using the q=1
annulus lifts. A simple constant column bound therefore cannot repair
the earlier progression transfer. This does NOT disprove a bound for
actual weighted gradients, which can offset a large coefficient.

Fresh verification passed at 2026-10-13T16:57:55.756923+00:00, pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. One new
standalone module was freshly built, fifteen roots use standard axioms
only, and there were no warnings, admitted proofs, or native evaluation.
The prior count-return, energy-cap, and height-coupling records had
14, 16, and 15 hashes authenticated respectively; their builds were
reused rather than repeated.

Independent exact finite replay: 8192 coefficient valuations, 352
structured dyadic odd cofactors, 65536 valuation/cost mass identities,
197376 holding congruence counts with 16448 exact wait expectations,
384 rational finite-walk systems, 14012 Green equations, 132 stopped
clock envelopes, 98304 actual stopped residue paths in 24 full-period
laws, 65536 exact squared horizon comparisons, and 516 actual lifts
of the expanding return family. No floating decisions were used.

Exploration before the new argument: /tmp/collatz-return-image-columns.json
scanned raw columns through first-return depth 22, and
/tmp/collatz-return-max-slope.json found the displayed family's pattern
through depth 24. Those exploratory float tables are not proof inputs;
the family was separately replayed using exact integers. A web review of
https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/tao-basin-densities.tex
looked at the external masked quadratic-cylinder energy criterion. Its
E'_K uses canonical inverse-word densities at integer targets, not this
project's dyadic E_s. No bridge between the energies, new external theorem,
or external replay was adopted. Sublinear bounds on our E_s do not satisfy
that other criterion automatically.

NEXT: use the strengthened return-separation budget with the actual
weighted progression samples or signed cancellation. Raw image columns
cannot have a uniform constant bound; ternary Haar integrability does
not control positive-integer trace samples. The coalescence-only energy
certificate already has its square-root growth order, so do not try to
obtain bounded energy merely by optimizing its constants or tail power.
Bounded actual energy, full escape exclusion, and additional-cycle
exclusion remain open. All jobs have terminated. No agents, installations,
credentials, staging, commits, or other Git writes were used.

## 2026-10-13: return-image logarithmic moments and finite integer sampling

The previous square-root-clock turn was progress; its eleven recorded
hashes were revalidated at this turn's start. This turn is progress too:
it proves a WRITTEN logarithmic-moment bound for return-image densities
and transfers its truncated version to finite integer intervals. This
provides positive sampling control after the raw coefficient obstruction.
It does not settle the pairing with actual future gradients. The full
Collatz goal remains active and unresolved; no blocked condition applies.

Added docs/RETURN-IMAGE-BOUNDS.md, lean/ReturnImageBounds.lean,
verify_return_image_bounds.py, and results/return-image-bounds. README
and ATTEMPT include the result and reproduction. Twelve kernel roots
supply arithmetic. Integration, convexity, logarithms, Holder estimates,
and all infinite probability consequences remain WRITTEN.

Use nonfused first positive count-return prefixes i for adjacent even
sources, with clock tau_i, even residue r_i, common count a_i, endpoints
x_i,y_i, and separation D_i=|x_i-y_i|>0. Let p_i=2^(-tau_i), the
UNCONDITIONAL binary prefix mass, so sum p_i<=1/2. Put
  lambda_i=3^a_i/2^tau_i,
  F_i(z)=3^a_i * 1_(z=x_i mod3^a_i),
  K_beta(z)=sum_i p_i D_i^beta F_i(z).
F_i has ternary additive Haar integral one. M_beta=integral K_beta is
finite for 0<=beta<1/3 by the prior written return-separation moment.
K_(beta,H) retains only tau_i<=H. The density is periodic for every finite
H and includes all integer representatives of each cylinder; requiring
an additional allowed source quotient only reduces its positive columns.

WRITTEN joint first-return moment:
  sum_i p_i D_i^beta (1+tau_i)^alpha <infinity
whenever beta>=0, alpha>0, and 3beta+2alpha<1. The clock tail gives
E(1+tau)^q<infinity for q<1/2. For beta>0 choose
beta/(1-2alpha)<beta'<1/3, then apply Holder using the beta' separation
moment and q=alpha beta'/(beta'-beta)<1/2. No independence is assumed.
For beta=0 use the clock moment alone. Also
  ||K_beta-K_(beta,H)||_1 <=C_(beta,eta) H^(-eta)
for every 0<eta<(1-3beta)/2; beta=0 permits eta=1/2 directly.

WRITTEN logarithmic moment: Phi_alpha(t)=t(log(1+t))^alpha is convex
for alpha>0. With Mbar_beta=max(1,M_beta), apply finite-mixture Jensen
to weights p_iD_i^beta/Mbar_beta and add unused weight at zero, then use
monotone convergence. The result is
  integral K_beta [log(1+K_beta/Mbar_beta)]^alpha <=A_(beta,alpha),
  A_(beta,alpha)=(log3)^alpha sum_i p_iD_i^beta(1+tau_i)^alpha<infinity.
Thus K_beta is in L(log L)^alpha for 3beta+2alpha<1. This is NOT an
L^p bound for p>1 or an essential-supremum bound.

The moment gives an explicit modulus of absolute continuity on a Haar
set A of measure delta>0:
  integral_A K_beta <=Mbar_beta sqrt(delta)
     + A_(beta,alpha)/[log(1+delta^(-1/2))]^alpha.
Ternary cylinder averaging P_L fixes each F_i with a_i<=L. Since
otherwise tau_i>L, its L1 contraction and the truncation tail give
  ||K_beta-P_L K_beta||_1<=2C_(beta,eta)L^(-eta).
These are ternary Haar assertions; the finite-integer result below is
separate. Do not confuse this uniformly integrable image-density family
with the non-uniformly-integrable endpoint log-height differences from
the earlier annulus note. They have different values and sampling laws.

KERNEL cubic child identity: 3^a_(t+1)(r)+3^a_(t+1)(r+2^t)=4*3^a_t(r),
and complete-period cubic mass is 4^t. Parent parity words give a binary
prefix tree, because each source-prefix split has opposite new endpoint
parities. Giving its even/odd branches tilted weights 1/4 and 3/4, the
prefix-free stopped mass satisfies sum_i 3^a_i/4^tau_i<=1. Thus
  sum_(tau_i<=H) lambda_i<=2^H.
The abstract pruned-tree integer inequalities and cubic identities are
kernel checked; their probability/word interpretation is written.

KERNEL endpoint comparison: orbit_t(r)<2*3^a_t(r) for r<2^t, via the
previous shifted retention bound. For the equal-count pair this gives
D_i<2*3^a_i. Therefore, in WRITTEN real powers,
  sum_(tau_i<=H)lambda_i D_i^beta<=2^beta(2*3^beta)^H.
The kernel also checks an integer floor counter's discrepancy
|q*count-M|<q. Its identification with the number of representatives of
one residue in an interval is elementary written counting, independently
replayed by direct enumeration.

For any interval I of M>=1 nonnegative integers, WRITTEN division and
summation give the actual finite-integer bound
  |mean_I K_(beta,H)-sum_(tau_i<=H)p_iD_i^beta|
       <=2^beta(2*3^beta)^H/M.
Applying the pointwise convex-mixture bound before counting gives
  mean_I K_(beta,H) [log(1+K_(beta,H)/Mbar_beta)]^alpha
       <=A_(beta,alpha)
          +2^beta[(H+1)log3]^alpha(2*3^beta)^H/M.
For beta=0 and H=floor((1-epsilon)log_2 M), epsilon fixed in (0,1),
these are uniform logarithmic moments on the actual finite intervals.
For general beta use H=floor(c log M), c<1/log(2*3^beta). This improves
on a Haar-only mass bound but retains the essential truncation error.
It is invalid to fix M and pass H to infinity in these estimates.

An explicit unweighted version does not use the huge C_star constant:
  integral K_0[log(1+K_0)]^(1/4) <80,
  mean_I K_(0,H)[log(1+K_(0,H))]^(1/4)<82
whenever 2^H(H+1)<=M. This permits H=log_2 M-log_2 log_2 M+O(1).
The associated finite-interval mass above coefficient R is at most
82/[log(1+R)]^(1/4). The exact rational root comparisons give
E(1+tau)^(1/4)<356/5 and (log3)^(1/4)<11/10, so the Haar bound is
<3916/50<80. The logarithm comparison uses the written inequality
exp(4/3)>1+4/3+8/9=29/9>3. Seven exact constant comparisons accompany
the finite verifier; the real steps remain written.

Fresh verification passed at 2026-10-13T17:40:34.195980+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Six modules
were freshly built sequentially; all twelve new roots use standard
axioms only, with no warnings, admitted proofs, or native evaluation.
The prior clock, height, and persistence records had 11, 15, and 14
hashes authenticated respectively without rewriting the prior records.

Independent exact replay: 32767 actual cubic-child/endpoint comparisons,
15 full-period masses, 75562 first-return tree edges, 2494 first-return
prefixes (2478 nonfused) through depth 18, 17 pruned-tree identities,
51 finite integer-power column bounds, 30240 direct interval residue
counts, 12 exact ternary projection comparisons covering 2125764 residue
values, and 160 truncated-density interval comparisons covering 174840
integer values. The finite integer-power checks at powers 1 and 2 test
counting algebra, not infinite separation moments of those powers.
No floating arithmetic was used in the verification decisions.

Exploration only: /tmp/collatz-annulus-charge-scan.rs and its CSV scan
whole-annulus reversal drift/parent-loss ratios through k=18,s=512 using
floating weights and checked u64 orbit arithmetic. The largest observed
ratio remains about 6.607568 at k=5,s=46 (the old exact witness). At k=18
the largest observed ratio is about 1.039756 at s=81. These new larger
ranges are NOT certified C=8 inequalities; the earlier exact certified
rectangle remains k<=10,s<=96. The scan's finite-level energy peaks
near 0.702683 at s=50 through level 18, but does not bound omitted levels.
The process terminated; no job is left running.

External reading used primary sources: Tao's 2020 post
https://terrytao.wordpress.com/2020/01/25/equidistribution-of-syracuse-random-variables-and-density-of-collatz-preimages/
and the recent archimedean almost-boundedness preprint
https://arxiv.org/html/2609.33018v1 . No new external theorem or estimate
was adopted, replayed, or used in the new result. The latter's announced
almost-boundedness conclusion would not itself supply the weighted
progression comparison or full convergence.

NEXT: exploit the new logarithmic-moment control in the actual pairing
with [f_h(x)-f_h(x-D_i)]^2, or find a direct bound for that pairing.
Its continuation clock and endpoint interval depend on the prefix.
Neither Haar L(log L) integrability nor the truncated finite-interval
bound allows replacing it by an interval energy with a fixed constant.
The actual energy bound remains O(sqrt(s)); bounded energy, escape
exclusion, and additional-cycle exclusion remain open. All jobs are
terminal; no agents, package installs, credentials, staging, commits,
or other Git writes occurred.

## 2026-10-13: corrections stopped at gap boundaries and half-power moments

The preceding return-image turn was progress. At this turn's start its
twenty recorded hashes and the clock record's eleven hashes matched.
This turn also made progress: a different stopping argument improves
the moment range, the explicit return-cycle constant, and the image
truncation rate. No full proof or counterexample was found. The user's
unbounded Collatz goal remains active; no blocker requires user input.

Added docs/RETURN-CORRECTION-MOMENTS.md,
lean/ReturnCorrectionMoments.lean,
verify_return_correction_moments.py, and
results/return-correction-moments. README and ATTEMPT were updated.
The earlier hashed notes, source files, and records were not rewritten.

The probability law is still the coherent full binary residue law,
equivalently Haar binary input. After each finite stopping prefix each
endpoint's next parity is conditionally fair; paired parities are
dependent. No infinite-time uniform law on a fixed finite integer
interval is assumed. For the actual affine coefficients
  U^t(X)=lambda_t X+B_t, lambda_t=3^a/2^t, B_0=0,
the conditional identities are
  E(lambda_(t+1)|F_t)=lambda_t,
  E(B_(t+1)|F_t)=B_t+1/4.

NEW KERNEL inputs (twelve audited roots): actual additive numerator
recurrence, residue lift, and two-child sum; the algebraic power identity;
an exact finite stopping-tree correction identity, clock bound, and
slope identity; named reuse of the prior gap-boundary clock budget;
quarter-root comparisons, drift/small-set constants, prescribed-attempt
constants, and the odd-offset bit bound. The correction tree has
P=d4^h E B_terminal, Q=2^h E extra_clock, initial B=N/d, and satisfies
4P=4^(h+1)N+d2^h Q. The stopped slope numerator is 4^h A from A/d.
Their probability interpretation and infinite stopping are WRITTEN.

WRITTEN boundary-stop proof: for odd initial separation D, sigma_K is
the physical time of first gap-walk exit from 0..K, including the first
departure step. The earlier proof gives upper-exit probability 1/K and
E sigma_K<=9K-8. For K=1, sigma_K=1. Even D has tau=1 and can use
sigma_K=1 without an upper exit. For S=sigma_K truncated at n,
  E B_S=E S/4, E lambda_S=1.
Fatou, nonnegativity, and monotone convergence give only the inequalities
  E B_sigmaK<=(9K-8)/4, E lambda_sigmaK<=1.
Do not claim equality at the unbounded stop or assume uniform
integrability. On lower exit sigma_K=tau, the first positive count
return. Therefore, for L>=1,
  Pr(B_tau>L)<=1/K+(9K-8)/(4L).
Taking K=floor(sqrt(L))+1 proves
  Pr(B_tau>L)<=7/(2 sqrt(L)),
  E B_tau^beta<=m_beta=1+7beta/(1-2beta), 0<beta<1/2.
Each endpoint's quarter-power moment is at most 9/2, uniformly in D
and conditionally at every return boundary. No independence is used.

WRITTEN direct returned-separation tail: at equal counts,
  D'<=D lambda_tau+B_tau^(1)+B_tau^(2).
The nonnegative process Z_t=D lambda_t^(1)+B_t^(1)+B_t^(2) has drift
1/2. The same stopped calculation yields
  E Z_sigmaK<=D+(9K-8)/2,
  Pr(D'>L)<=1/K+[D+(9K-8)/2]/L<=(D+6)/sqrt(L).
For adjacent starts D=1 the coefficient is seven. This is under the
full unconditioned binary law; restricting nonnegative sums to even,
nonfused return prefixes decreases them.

WRITTEN improved cycle budget: for beta<1/2,
  E (D')^beta<=r_beta D^beta+2m_beta,
  r_beta=(2^(-beta)+(3/2)^beta)/2<1.
Use nonnegative stopped slope powers after time one to get
E lambda_tau^beta<=r_beta, since tau>=1. At beta=1/4, the exact root
comparisons 120^4<2*101^4 and 3*120^4<2*133^4 imply r_beta<39/40:
  E (D')^(1/4)<=(39/40)D^(1/4)+9.
With V=D^(1/4) and R=400^4=25,600,000,000<2^35, the drift is at
most minus one outside R, so expected return-cycle time to R is <=V.
The existing prescribed descent paths shrink separation by at most
3/4 each cycle; (3/4)^4<1/2 gives at most 140 cycles from D<=R.
Each uses at most 37 bits because c=(3D+1)/2<2^36. Thus each attempt
succeeds with conditional probability >=2^-5180. From V<=400,
the expected V after any number of cycles stays <=400, using
(39/40)*400+9=399. Attempt plus reentry therefore costs at most 540
in conditional expectation. Summing over the geometric bound for
reached attempts proves
  E N<=C_quarter:=540*2^5180.
Attempts are not assumed independent. This supersedes the numeric
constant 2187414*2^454272, not the existing valid exponent bounds.
It also gives
  E sum_(j<N) D_j^beta<=[1+2m_beta C_quarter]/(1-r_beta), beta<1/2,
and at beta=1/4 the bound 40(1+9 C_quarter).
The fusion-clock upper tail can use 14 C_quarter/sqrt(H), and the
actual-energy bound 28 C_quarter sqrt(ceil(121s/50))+23/4. The
physical mean fusion time remains infinite, and bounded energy is open.

WRITTEN image consequences: the logarithmic-moment parameter region
is now beta>=0, alpha>0, beta+alpha<1/2. Choose
beta/(1-2alpha)<beta'<1/2 and reuse the prior Holder and Jensen proofs.
More sharply, from the two adjacent-pair tails
Pr(tau>H)<=7/sqrt(H) and Pr(D'>u)<=7/sqrt(u), integration split at H
gives
  E[(D')^beta 1_(tau>H)]<=7 H^(beta-1/2)/(1-2beta).
For beta=0 use the clock tail on nonfused prefixes. Thus, for H>=1,
  ||K_beta-K_(beta,H)||_1<=7 H^(beta-1/2)/(1-2beta), 0<=beta<1/2.
This reaches the endpoint decay rate, improving the prior strict
Holder exponent. Ternary conditional projection at depth L>=1 has
L1 error at most 14 L^(beta-1/2)/(1-2beta). The finite-integer-interval
formulas and their depth/length errors are unchanged; the unweighted
quarter-logarithmic constants 80 and 82 remain valid. No beta=1/2
moment, L^p density bound for p>1, or actual-gradient pairing is proved.

Fresh verification passed at 2026-10-13T18:04:21.422785+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Six modules
were freshly built sequentially. All twelve roots use only standard
axioms; there were no warnings, admitted proofs, or native evaluation.
The control, clock, and image records had 14, 11, and 20 hashes
authenticated respectively. The new verification manifest has 21 hashes.

Exact finite replay passed: 16383 direct affine child identities;
14 full-period correction/slope masses; 12130 independently recomputed
stopped endpoint trajectories; 272774 actual stopping-tree edges;
1092 bounded stopped laws; 4992 finite correction-tail comparisons;
78 finite returned-separation tail checks; 41524 prescribed return
cycles across 4167 fusion paths; nine constant comparisons;
20405 rational tail-bound comparisons; and 2450 exact truncation
coefficient identities. Stopping trees used thirteen separations,
including values near R and 2^35, six gap barriers, and horizon 14.
Prescribed fusion samples included all D<=4096, dyadic boundary values,
and values near R; the observed maximum was 42 cycles and 81 bits.
These finite observations do not replace the general written bounds.
No floating arithmetic was used in verification decisions.

Exploration only: /tmp/collatz-return-image-l2.rs and its executable/CSV
enumerate the nonfused even-prefix image density through depth 24. The
trie evaluates exactly
  integral K_H^2=sum_(i,j) p_i p_j 3^min(a_i,a_j)
                    1_(compatible ternary image cylinders).
The CSV stores binary-mass numerator over 2^24 and squared-density
numerator over 2^48. Diagnostic floating values were about 0.002197 at
H=6, 0.056691 at H=10, 0.168366 at H=14, 0.274069 at H=18, and
0.416410 at H=24. At depth 24 there were 1,931,482 live prefixes and
54,364 trie nodes. No convergence or divergence conclusion follows,
and this exploration is not part of the new verification manifest.

NEXT: use the stronger separation-weighted image estimates in the
actual future-gradient pairing, or prove a direct integrated return
comparison. The unweighted coalescence-only certificate already has
its square-root growth order. Merely improving its constants, or
sampling deeper L2 image densities, does not establish bounded energy.
A possible additional route is exponential moments of the number of
return cycles from the multiplicative drift outside R; this has not
been adopted or verified. The exploratory tilted-slope return-law idea
is also unproved and unused. Escape and additional cycles remain open.
All processes are terminal. No agents, installations, credentials,
staging, commits, or other Git writes occurred.

## 2026-10-13: exponential cycle count and the all-return occupation density

The previous stopped-correction turn was progress. This turn authenticated
its 21 hashes, the image record's 20, and the ordered-drift record's 16
before proceeding. The new work is also progress: it controls the
sampling density accumulated over every nonfused count return, and
rules out a scalar pointwise charge at a return. The full user objective
remains active and unresolved. There is no genuine user/external blocker.

Added docs/RETURN-OCCUPATION-DENSITY.md,
lean/ReturnOccupationDensity.lean,
verify_return_occupation_density.py, and
results/return-occupation-density. Updated README and ATTEMPT.
Earlier hashed sources and records were not changed.

NEW KERNEL arithmetic (fifteen roots):
- The fixed even first-return cylinder r=48 mod 64 has tau=6,
  common count two, and endpoints 9q+8,9q+7; alive through time five.
- The persistent family 2n_j=16(64^j-1)/9, even j>=2, returns at
  six to X=2^(6j-2)+1 and Y=2^(6j-2).
- Odd counts are nondecreasing in the clock; for a>=2 and
  0<t<=3a-2, wt_t(2^(2a)+1)>wt_t(2^(2a)). This verifies that the
  whole known persistent window lies within the SECOND count excursion.
- Multiplicative drift arithmetic outside V>=400; a general finite
  inverse Bernoulli inequality and its exponential linearization;
  the rational denominator and failed-attempt contraction inequalities;
  half-power root comparisons and the total attempt constant.
- Selected all-return cubic weights are bounded by full-period cubic
  mass; cumulative slope-column numerator plus 2^(H+1) is <=2*4^H.

WRITTEN obstruction: the earlier family has unaveraged negative drift
at least 5(3j-4)/128 during that second excursion. Its first-return
data (tau,a,D) are always (6,2,1), with common multiplier 9/64.
Thus no finite function of these data alone bounds the accumulated
pointwise excursion cost. Separation moments do not repair that
pointwise approach, even when the separation is exactly one. The
displayed source cells are rare; this does not refute integrated bounds.

WRITTEN exponential cycle moment, now adopted (superseding the previous
entry's tentative suggestion): retain D_j, N, V=D^(1/4), R=400^4,
and the conditional drift E V_next<=(39/40)V+9. Outside D<=R,
this is at most qV with q=399/400. If sigma is the cycle count to
reach D<=R, the killed potential gives
  Pr(sigma>n)<=V(D)q^n/400,
  E s^sigma<=1+(s-1)V(D)/[400(1-sq)], 1<s<1/q.
These are conditional estimates given any finite return history;
neither Markov independence nor independent attempts is needed.

Take the previous attempt length M=140 and success lower bound
p=2^-5180. Set delta=p/4096=2^-5192 and s=1+delta. An attempt
starts in the positive part of D<=R, runs M cycles with zero absorbing,
then waits to reach D<=R again if needed. It can fuse during this
reentry. Use the upper-bound attempt length L=M+sigma, even when
fusion occurred earlier. Since E V(D_M)<=400,
  E[s^L 1_failed | attempt start]
       <=s^M[1-p+delta/(1-sq)]<=1-p/2=:rho<1.
The arithmetic uses 1-sq>=1/800, s^140<=1+280delta, and
(1+280delta)(1-p+800delta)<=1-p/2. The last inequality is proved
with cleared rational denominators for arbitrary 0<=p<=1.

IMPORTANT: fusion during reentry can take MORE than M cycles. Do not
bound successful length by M. Instead bound the entire attempt:
  E s^L<=s^M[1+delta/(1-sq)]
         <=(1+280delta)(1+800delta)<=2.
The discounted probability of reaching attempt k is <=rho^(k-1).
Summing the successful contributions gives
  E(1+2^-5192)^N<=A:=4/p=2^5182.
This is a WRITTEN probability theorem. It concerns return-cycle count,
not physical clock. The physical fusion time still has infinite mean.

WRITTEN occupation measure: for physical return clocks S_j, fusion
clock T=S_N, and C=540*2^5180, define
  integral g dnu = E sum_(1<=j<N) g(D_j,S_j).
Its total mass is <=C. From the prior Pr(T>H)<=14C/sqrt(H) and
the new exponential cycle moment, for integer ell>=1,
  nu(S>H)<=14C ell/sqrt(H)+A s^(1-ell)/delta.
Taking ell=max(1,ceil(logH/[2logs])) gives
  nu(S>H)<=[A_T+B_T logH]/sqrt(H), H>=1,
  A_T=14C+A s/delta, B_T=7C/logs.

For gamma in [1/4,1/2), convexity of r_gamma and the two endpoint
root comparisons give r_gamma<=39/40. Since
2m_gamma<=7/(1-2gamma), the summed separation moment obeys
  integral D^gamma dnu<=B/(1-2gamma), B=40(1+7C).
For u>=16 choose gamma=1/2-1/log_2(u), and for u<16 use mass<=C:
  nu(D>u)<=B(1+log_2 u)/sqrt(u), u>=1.
Consequently D+1+S has every nu moment below 1/2, and
  E sum_(1<=j<N) D_j^beta(1+S_j)^alpha<infinity
for beta>=0, alpha>0, beta+alpha<1/2. No independence is assumed.

WRITTEN all-return density: index EVERY nonfused even-source return
prefix i, not just first returns. Ancestors and descendants can both
appear. Let t_i be its total source clock, a_i its common total odd
count, x_i=U^t_i(r_i), D_i>0 its separation, p_i=2^-t_i, and
  F_i(z)=3^a_i 1_(z=x_i mod 3^a_i),
  K*_beta=sum_i p_i D_i^beta F_i.
Its Haar mass M*_beta is finite for beta<1/2. With
Mbar=max(1,M*_beta), the same convex mixture/Jensen proof gives
  integral K*_beta[log(1+K*_beta/Mbar)]^alpha
       <=A*_(beta,alpha)<infinity, beta+alpha<1/2,
  A*=(log3)^alpha sum_i p_i D_i^beta(1+t_i)^alpha.
Prefix disjointness is not needed; the finite occupation mass supplies
the mixture normalization.

WRITTEN all-return truncation: for 0<=beta<1/2, c=1/2-beta, H>=1,
  ||K*_beta-K*_(beta,H)||_1 <= H^(beta-1/2) times
    [A_T+B_T logH
       +beta B{(1+logH/log2)/c+1/(c^2 log2)}].
At beta=0 the final term is zero. This is
O_beta((1+logH)H^(beta-1/2)); the logarithm has not been removed.
It follows by splitting the layer-cake integral at H and using the
two occupation tails. Ternary projection at depth L has error at most
twice this bound with H=L. First-return bounds remain stronger for
their smaller density; do not confuse the two objects.

WRITTEN finite integer sampling: each level's return slopes have sum
<=2^t, and all levels through H have sum <=2^(H+1)-2. The kernel
cumulative-column recurrence checks the latter's integer form. Since
D_i<2*3^a_i, for any beta>=0 the finite coefficient sum is bounded by
  sum_(t_i<=H) lambda_i D_i^beta<=2^(beta+1)(2*3^beta)^H.
Thus the all-return truncated mean on any integer interval of length M
differs from its Haar mean by at most this quantity divided by M.
The logarithmic-moment transfer has the additional [(H+1)log3]^alpha
factor. No infinite separation moment at beta>=1/2 is asserted.
The old explicit logarithmic constants 80 and 82 are first-return
constants and are NOT asserted for this larger occupation density.

Fresh verification passed at 2026-10-13T18:31:07.233846+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten modules
were freshly built sequentially. All fifteen new roots use only the
standard axioms; no warnings, admitted proofs, or native evaluation.
The correction, image, and persistence records had 21, 20, and 14
hashes authenticated respectively. The new manifest records 29 hashes.

Independent exact finite checks passed: 4112 fixed-return cylinders,
16 full persistent second excursions, 752 persistent drift offsets,
19305 inverse-Bernoulli cases, 5241 exponential linearizations,
8384 failed-attempt rational comparisons, five explicit cycle-constant
checks, and 1249 near-half moment coefficient comparisons. The exact
comparison at the actual delta=2^-5192 was checked with integers.

The all-return tree through depth 16 had 30750 edges and 2552 nonfused
return prefixes: 744 first returns and 1808 later returns, up to return
index seven. All were independently matched against 32768 directly
iterated even inputs in the full period. Sixteen occupation identities
and 45 finite column bounds passed. The finite occupation mass was
13623/65536, and balanced-fused mass 17685/65536; these are finite
values, not claimed limiting masses. Also passed: 36 ternary projection
checks covering 117936 density values, 16752 direct interval residue
counts, and 72 interval bounds covering 5328 density values. Finite
integer-power checks at beta=1 or 2 verify counting algebra only,
not infinite moments. No floating arithmetic was used in decisions.

NEXT: the sampling weight over all returns is now controlled. The
remaining obstacle is its pairing with the actual future squared
weight differences, at prefix-dependent continuation clocks and
endpoint intervals. Prove complementary integrability or a direct
averaged charge. A separation-only cost per excursion is now excluded
pointwise even at fixed return clock and count. Improving unweighted
coalescence tails or cycle constants again would not settle bounded
energy. The tilted-slope idea remains unproved and unused. Escape and
other cycles remain open; the full Collatz goal stays active.
All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes occurred.

## 2026-10-13: actual-gradient complementary-norm obstruction

The previous occupation-density turn was progress. Its 29 hashes,
the correction record's 21 hashes, and the energy-cap record's 16
hashes matched at this turn's start. This turn also made progress:
it rules out the proposed uniform complementary norm for accumulated
actual gradients, then identifies a candidate replacement below.
The full Collatz goal remains active and unresolved; no user or
external blocker prevents further research.

Added docs/GRADIENT-ORLICZ-OBSTRUCTION.md,
lean/GradientOrliczObstruction.lean,
verify_gradient_orlicz_obstruction.py, and
results/gradient-orlicz-obstruction. Updated README and ATTEMPT.
Earlier hashed sources and records were not rewritten.

For m>=0 define Q=2^(12m+6), M=9Q, and the actual image interval
I=[9Q+8,18Q+8), length M. The fixed return cylinder r=48 mod64
maps source quotients Q<=q<2Q to paired endpoints 9q+8,9q+7.
Q=1 mod9, q_m=16 floor(Q/9)+1 lies in that quotient interval, and
x_m=9q_m+8=16Q+1=2^(12m+10)+1 belongs to the sampled progression.
Its paired endpoint is x_m-1. This is the earlier persistent family
with j=2m+2 and fixed first-return data (tau,a,D)=(6,2,1).

Define the FINITE accumulated returned squared gradient
  G_m(x)=sum_(h=0)^(6m+1)
       [M(f_(12m+12+h)(x)-f_(12m+12+h)(x-1))]^2.
It is defined on all of I and its actual progression; no eventual
orbit convergence or infinite time sum is required. The exact scale
identity is M/2^(12m+12+h)=9/2^(h+6). New kernel versions of the
retained-parent and child-ceiling bounds give throughout this window
  M f_(12m+12+h)(x_m)>=1/2,
  M f_(12m+12+h)(x_m-1)<=27/64.
Therefore the written squared sum is
  G_m(x_m)>=L_m:=25(6m+2)/4096.
The window lies entirely in the second count excursion.

NEW KERNEL roots (eight): Q mod9, actual interval/progression location,
the returned scale identity, returned parent retention, returned child
ceiling, a general cross-product gap lower bound, its squared version,
and an exact large quadratic-exponential integer comparison. The real
division, finite sum, exponential growth, and norm consequences are
WRITTEN, not full Lean formalizations.

WRITTEN obstruction: for any p>1,C>0, the interval average of
exp((G_m/C)^p) is at least exp((L_m/C)^p)/M, which tends to infinity
because log M=(12m+6)log2+log9 grows linearly and (L_m/C)^p grows
superlinearly. The actual progression has Q elements and yields the
same conclusion with Q in the denominator. Under the convention
mean(exp((G/C)^p)-1)<=1, the Luxemburg norm is at least
  L_m/[log(M+1)]^(1/p),
or L_m/[log(Q+1)]^(1/p) on the progression. It grows at least as
m^(1-1/p). At m=16384,p=2,C=1, the kernel integer comparison and
the written log2<1, log9<3 bounds imply an average >exp(100000).
That large example uses the general family proof, NOT an orbit replay
at the huge source size.

For Phi_alpha(u)=u[log(1+u)]^alpha, define the convex conjugate
Psi_alpha(v)=sup_u(uv-Phi_alpha(u)). Taking
u=exp((v/2)^(1/alpha))-1 gives, for v>=2,
  Psi_alpha(v)>=(v/4)exp((v/2)^(1/alpha))
              >=(1/2)exp((v/2)^(1/alpha)).
Thus mean Psi_alpha(G_m/C) is unbounded for every alpha<1 and C>0.
In particular, the available density exponents alpha<1/2 demand an
exponential power >2 whose uniform norm fails. This excludes the
specific method of first accumulating time contributions and then
using ONE uniform complementary norm. It does not exclude clockwise
estimates, support-sensitive estimates, or use of actual correlation.

IMPORTANT scope: the exceptional point contributes only L_m/M to
the ordinary mean lower bound, which tends to zero and is summable
over m. This does NOT show unbounded ordinary means, failure of an
averaged density-gradient pairing, or unbounded actual energy. The
single return column has bounded value 9/64 on the residue 8 mod9.
An ordinary exponential norm (p=1) at sufficiently large scale is
not excluded by this family; no such uniform bound is proved.

Fresh verification passed at 2026-10-13T18:50:44.028881+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eleven
modules were freshly built sequentially. All eight new roots use only
standard axioms, with no warnings, admitted proofs, or native evaluation.
The occupation and persistence records had 29 and 14 hashes verified.
The new manifest records 29 hashes.

Independent exact replay checked 21 image/family instances through
m=64, 84 direct original-source transport identities, 1866 returned
gradient offsets, all 576 gradients on the smallest interval [584,1160),
and all 64 sampled progression gradients there. The exceptional x=1025
has G_0=39778923825/516006608896. Exact ordinary mean enclosures are
saved; they concern only that finite interval. Five large quadratic
exponential comparisons and two elementary exponential constants also
passed. No floating arithmetic was used in verification decisions.

External reading was limited to primary sources. Tao's 2019/2020
Syracuse-law discussion and the OpenAI ordinary-correlation catalogue
did not supply the stopped weighted-gradient comparison. A more useful
lead is Lucas Valbuena's 8 October paper:
https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/quadratic-cylinder-energy.tex
It uses distinct offset quotients to obtain polynomial cylinder energy
for the stationary Syracuse law, then combines it with Tao mixing to
obtain subcritical L^p integrability. Its stationary result is NOT our
return density; no external proof bundle was replayed or adopted here.

NEXT — PROMISING CANDIDATE, NOT YET ADOPTED OR VERIFIED:
Adapt that quotient-counting idea to our finite binary image law.
For ALL r<2^t, let a=wt_t(r), N=2^t U^t(r)-3^a r, and
  rho_t(z)=sum_(r<2^t) 2^-t 3^a 1_(z=U^t(r) mod3^a).
This has Haar integral one and dominates the selected return density
at total clock t. At fixed (t,a,image residue v), N has fixed residue
mod3^a. Distinct r give distinct N: the exact affine equation plus
gcd(3^a,2^t)=1 forces r=r' if N=N' within the full binary period.
Thus q=floor(N/3^a) is injective on such a fibre and q<=Y=N/3^a.
If its cardinality is m_f, the elementary distinct-quotient count gives
  m_f^2<=2 sum_fibre(1+Y).
Summing and using Cauchy over a=0..t should give
  ||rho_t||_2^2 <=2(t+1) sum_(r<2^t) 3^a4^-t(1+N/3^a)
                 =2(t+1)(1+t/4)=(t+1)(t+4)/2.
The exact inputs are sum3^a=4^t (already kernel) and
4 sumN=t4^t. The latter follows from the new numerator child sum
4N+2^t, but currently needs its own all-depth kernel proof if used.
No Tao mixing or external stationary theorem is needed for this
finite-binary argument. Check the fibre injection carefully before
adopting it, especially t=0,a=0.

If that quadratic bound holds, each selected return layer kappa_t is
pointwise <=rho_t and ||kappa_t||_2<=t+2. Hence the all-return
truncation has
  ||K*_(0,H)||_2<=H(H+5)/2<=3H^2 for H>=1.
Combine it with the VERIFIED WRITTEN L1 clock-truncation error
O((1+log H)H^-1/2). Dyadic increments at H=2^j have L1 size
O(j2^-j/2) and L2 size O(2^(2j)). Interpolation gives Lp increment
exponent [-(2-p)/2+4(p-1)]/p = (9p/2-5)/p.
This is summable in j for 1<p<10/9. Thus a prospective result is
K*_0 in Lp for every 1<=p<10/9, substantially stronger than the
currently adopted logarithmic moments. This has NOT yet been promoted
to a proved project result or checked by a verifier.

Possible extensions once the unweighted claim is verified:
- Pointwise Holder over columns gives
  K*_beta <=(K*_gamma)^(beta/gamma)(K*_0)^(1-beta/gamma).
  With gamma<1/2, K*_gamma in L1 and K*_0 in Lp0, this would give
  K*_beta in Lp for 1<=p<10/(9+2beta), 0<=beta<1/2.
- K*_(beta,H) is periodic mod3^H, so any interval mean of its pth
  power is <=(1+3^H/M) times its Haar pth moment. This may transfer
  uniform power bounds when 3^H<=M, using actual finite intervals.
- A first-return-only variant may improve the L2 growth to H^(3/2)
  using stopped slope/correction budgets and then allow p<8/7; this
  is more tentative and is not needed for the all-return result.

The weighted-gradient comparison remains the actual objective of this
route. Even a new Lp density theorem would still require control of
the complementary power moment of the accumulated gradients, or an
estimate retaining their correlation. Do not treat density integrability
as bounded actual energy or escape exclusion. All processes are
terminal. No agents, installs, credentials, staging, commits, or other
Git writes occurred.

## 2026-10-13: quadratic binary image energy and all-return Lp moments

The candidate in the preceding entry is now ADOPTED as a WRITTEN
analytic theorem with fresh kernel arithmetic and independent exact
finite verification. This supersedes the preceding candidate status.
Added docs/BINARY-IMAGE-ENERGY.md, lean/BinaryImageEnergy.lean,
verify_binary_image_energy.py, and results/binary-image-energy/.
README and ATTEMPT include the result and reproduction command.

For r<2^t put a=wt_t(r), x=U^t(r), and N=2^t*x-3^a*r>=0.
Define the full ternary Haar image density
  rho_t(z)=sum_(r<2^t) 2^-t*3^a*1_(z=x mod3^a).
It has mass one. At fixed t and a, equal N forces equal r: subtract
the affine equations and use coprimality of 2^t and 3^a. At fixed
image residue v, N=2^t*v mod3^a, so floor(N/3^a) is injective
on that fibre. This includes t=0 and a=0; no exceptional case is
left unproved. If the fibre has m sources, sorting its quotients
gives q_j>=j for j=0,...,m-1 and
  3^a*m^2 <= 2 sum_fibre(3^a+N).
The injection, residue, and ranked cost lemmas are kernel checked;
the sorting/existence of a ranked finite enumeration is written.

The new all-depth kernel identity is
  4 sum_(r<2^t) N_t(r) = t*4^t.
Its induction sums the previous numerator children 4N+2^t. Combining
it with the existing cubic mass sum3^a=4^t gives
  4 sum(3^a+N)=(t+4)*4^t.
Group rho_t by count a, apply the fibre square bound, then Cauchy
over the t+1 possible counts. The WRITTEN Haar consequence is
  ||rho_t||_2^2 <= (t+1)(t+4)/2,
  ||rho_t||_2 <= t+2.
This is a bound at every finite depth, not an asymptotic extrapolation
from the enumerated periods.

At total clock t, the selected even nonfused return layer kappa_t
is pointwise <=rho_t. Its first endpoint is consistently U^t(r),
not reordered by size, so the domination matches the occupation
density definition exactly. Nested returns at different clocks are
allowed; each r at a fixed clock appears at most once. Minkowski
and the new finite sum roots give
  ||K*_(0,H)||_2 <= H(H+5)/2 <=3H^2 for H>=1.
Use the prior WRITTEN occupation tail
  ||K*_0-K*_(0,H)||_1 <=(A_T+B_T log H)/sqrt(H).
For Delta_j=K*_(0,2^(j+1))-K*_(0,2^j),
  ||Delta_j||_1 <=(A_T+B_T*j*log2)*2^(-j/2),
  ||Delta_j||_2 <=12*2^(2j).
For theta=(2-p)/p, eta=2(p-1)/p, interpolation yields
  ||Delta_j||_p <=12^eta (A_T+B_T*j*log2)^theta
                    *2^[-j(5/p-9/2)].
This is summable for 1<p<10/9. Positive partial sums, Minkowski,
and monotone convergence prove K*_0 in Lp in that range. No endpoint
claim is made. An explicit norm bound recorded in the note is
  C_p=3+12^eta*(A_T+B_T*log2)^theta
                  /[1-2^(-(5/p-9/2))]^2.

For 0<beta<gamma<1/2, pointwise column Holder gives
  K*_beta <=(K*_gamma)^(beta/gamma)*(K*_0)^(1-beta/gamma).
The prior separation occupation budget makes K*_gamma integrable.
Combining this with any base p0<10/9 and taking gamma towards 1/2
proves the WRITTEN result
  K*_beta in Lp for 0<=beta<1/2, 1<=p<10/(9+2beta).
Consequently every finite logarithmic moment order alpha is allowed
for each fixed beta<1/2. The earlier beta+alpha<1/2 region remains
valid but is no longer the best membership statement. Its earlier
explicit bounds and cutoff errors remain in their original scope.

The truncated density K*_(beta,H) is periodic modulo 3^H. Every
residue occurs at most M/3^H+1 times in an integer interval I of
length M. Therefore
  mean_I K*_(beta,H)^p <=(1+3^H/M)||K*_beta||_p^p.
This is uniform in interval location when 3^H<=M, but it is NOT an
infinite-cutoff integer trace theorem. Haar sets also gain a power
absolute-continuity modulus from ordinary Holder.

Fresh verification passed 2026-10-13T19:07:39.164678+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten
modules were freshly built sequentially; eleven new roots have only
standard axioms, without warnings, sorry, or native evaluation.
The occupation and image records had 29 and 20 hashes authenticated.
The new record contains 26 hashes, all reauthenticated after the run.

Exact replay covered 131071 sources over all binary periods t=0..16,
41109 injective fibres and rank bounds, 17 complete image energies,
and 9841 direct ternary density values through depth eight. Independent
direct adjacent trajectories numbered 65535 through depth sixteen,
including 2552 nonfused return prefixes; all 16 selected-layer
dominations and 16 cumulative energy bounds passed. Further checks:
66339 exact column Holder inequalities, 180 finite periodic interval
power bounds, 4950 interpolation exponent identities, and twelve
weighted exponent examples. All decisions used exact arithmetic.
The finite interval tests use integer beta=0,1,2 and p=2,3 only
to check finite counting; no infinite moment is claimed there.

At t=16 the full image squared norm is
  15611322797/2147483648,
against the general upper bound 170; its largest fibre has 48 sources.
The all-return truncation at H=16 has mass 13623/65536 and squared
norm 3820172355/4294967296. These examples are not asymptotic claims.

Provenance: the distinct-quotient counting idea is attributed to
Valbuena's primary paper linked in the preceding entry and the new
note. No external theorem, stationary Syracuse result, or Tao mixing
result is imported. The proof is the binary-period adaptation above
plus the project's earlier WRITTEN return occupation estimates.

NEXT: return to the actual weighted-gradient pairing with the stronger
density class available. In the unweighted case a complementary Lq
bound would require q>10; for beta it would require q>10/(1-2beta).
The known exceptional point makes an exponential-power norm fail but
does NOT make any fixed polynomial moment fail: its single-point
contribution is a polynomial in m divided by an exponential in m.
One must still handle prefix-dependent image scales and clocks, and
retain correlations as needed. Finite power-moment experiments should
use the actual returned progressions/intervals and exact weights,
without replacing full-period laws by uncontrolled integer sampling.
The first-return-only p<8/7 refinement mentioned in the prior entry
remains a candidate, not a verified theorem and not needed here.

The actual energy bound is still O(sqrt(s)), with no bounded subsequence
proved. Escape and additional cycles remain open. The user's full
Collatz goal remains active. All processes are terminal. No agents,
installs, credentials, staging, commits, or other Git writes occurred.

## 2026-10-13: complete temporal budgets and a PLD-free escape criterion

The previous goal turn was verified progress (binary-image Lp theorem).
This turn made further progress on the actual-gradient question, without
proving the universal condition or full Collatz. Added:
  docs/ANNULUS-TIME-BUDGETS.md
  lean/AnnulusTimeBudgets.lean
  lean/BinaryConePredecessors.lean
  verify_annulus_time_budgets.py
  results/annulus-time-budgets/
README and ATTEMPT contain the result and reproduction command.

NEW WRITTEN SUFFICIENT CONDITION Q:
For every fixed source level k,
  (1/S) sum_(s<S) N^rev_(s,k) -> 0 as S -> infinity.
There is NO uniformity requirement across k. This is weaker than the
previous uniform complementary power norm or a uniform all-time budget.
It is NOT proved for all k. The proof of its implication is:
- On each fixed cell, parent and odd-child weights A_s,B_s decrease
  to limits, and the historical reversal flag is either always zero
  or eventually one. Thus the finite annulus reversed-negative average
  has a limit. Q makes that limit zero.
- The ordered negative averages also tend to zero, using the existing
  sum_(s,k) N^ord_(s,k)<=14. Nonnegativity of the finitely many cells
  yields A_inf*(A_inf-B_inf)_+=0 on every cell. Hence B_inf>=A_inf,
  including when A_inf=0.
- With exact even-child copying, h_k(x)=2^k f_inf(floor(2^k x))
  is nondecreasing in k. It starts at h_0=0 and its limit is <=1/x.
  Sum of squares of nonnegative increments is <= square of their sum,
  so sum_k integral(h_(k+1)-h_k)^2 <=1/2. This is limiting energy,
  NOT an assertion of a bounded subsequence of finite-offset E_s.

The criterion now has a more direct escape implication WITHOUT PLD,
real-scaling measure rigidity, or an external mixing theorem. Reuse
the old six-step inverse child from UniformInverseBranching, choosing
the false branch, and define v_0=1, v_(j+1)=child(v_j,false).
The new kernel induction proves:
  v_j>0, v_j%3!=0, U^(6j)(v_j)=1, wt_(6j)(v_j)=j,
  3 v_(j+1)=64 v_j-d_j with 4<=d_j<=32,
  29*64^j+32*3^j <=61*3^j*v_j <=61*64^j.
The child table for residue r=1,2,4,5,7,8 mod9 has offsets
16,32,80,104,148,160 after 192*floor(v/9), and errors
16,32,16,8,4,32 respectively. The construction works at every depth.

WRITTEN: r_j=3^j v_j/64^j decreases to c in [29/61,1], with
  0<=r_j-c<=(32/61)*(3/64)^j.
Therefore log2(v_j)=j*(6-log2(3))+log2(c)+o(1). Irrational rotation
(log2(3) irrational by prime factorization) and a shrinking error
make the binary significands dense, with arbitrarily late visits to
every open subinterval of [1,2]. Every binary cone
  C(n)={2^ell*n+r : ell>=0, 0<=r<2^ell}
therefore contains arbitrarily large known predecessors v_j of one.
This is leading-digit density, NOT positive natural density.

Under Q, positivity of f_inf(n) propagates to both 2n and 2n+1.
The new kernel binary_cone_closed lemma propagates such closure to
every member of C(n). A spine member in that cone has f_inf=0,
so f_inf(n)>0 is impossible. Thus Q implies W_inf=0 everywhere.
Only the prior WRITTEN packing/weight characterization is then needed
to exclude escape. Other cycles are NOT detected by W_inf and remain
open. Do not conflate this conditional reduction with proving Q.

Quantitative alternatives are also recorded. Define possibly infinite
  T_k=sum_s e_(s,k), R_k=sum_s N^rev_(s,k), L_k=sum_s L_(s,k).
Always L_k<=5/2, by telescoping parent and shifted-parent losses.
For J(S)=ceil(121S/50), K>=J(S), S>=1, the prior geometric tail
and N^rev_(s,k)<=sqrt(e_(s,k)/2) give the WRITTEN inequalities
  sum_(s<S) E_s <=sum_(k<K) T_k+73/20,
  sum_(s<S) E_s <=S/2+2 sum_(k<K) R_k+54.
Consequently a finite lower Cesaro source-level average a of T_k
gives an upper bound 121*a/50 for the lower Cesaro offset energy;
the corresponding average b of R_k gives 1/2+121*b/25. The weaker
charge R_k<=C L_k after summing time would give 1/2+121*C/10.
These hypotheses also imply Q, hence their escape implications now
avoid PLD. None is proved over unbounded source levels.

Exact all-time census: every sampled endpoint is directly checked to
enter {1,2}. Two further cycle steps settle the historical reversal
flag. Both weights multiply by 3/4 every two steps; the squared gap
and reversed negative product multiply by 9/16. The remaining tail
is exactly (16/7)*(cost_phase_0+cost_phase_1). Six new kernel roots
check known-cycle continuation, periodic count comparison, weight
data, and the finite geometric identity. Infinite sums remain written.

For all 32767 parent pairs n,3n+2 with 1<=n<32768 (levels 0..14),
the exact census includes EVERY future offset and verifies
  T_k<4, R_k<5/4, R_k<=L_k.
It also proves R_13>1. Selected display values, backed by rational
enclosures: T_14 about 3.146954, R_14 about 0.963368,
L_14 about 1.729177, and R_13 about 1.010606. The latest tail start
at level 14 is parent clock 214. No universal k bound follows.

The actual return cylinder r=48 mod64 was checked separately at
Q=2^L, M=9Q, L=0,2,4,6,8,10. It uses source [64Q,128Q), image
[M+8,2M+8), and progression x=9q+8, Q<=q<2Q. Its full future field
  G_L(x)=sum_(s>=0)[M*(f_(L+s)(x)-f_(L+s)(x-1))]^2
contributes (1/64)*mean_progression G_L to T_(L+5). This exact
original-source transport was checked. Certified moment enclosures
for p=1,2,4,8,12 are stored on both the progression and full interval.
The pairing with 9*1_(x=8 mod9) is retained exactly. At L=10 the
display means are interval 8.454073/progression 8.683249, and display
L12 norms are 60.893131/48.677974. This neither proves nor disproves
a uniform high power norm as L grows.

Fresh verification passed 2026-10-13T19:42:30.582547+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Seven
modules were built sequentially, and all twelve new roots use only
standard axioms, without warnings, sorry, or native evaluation.
Prior records reauthenticated: persistence 14 hashes, energy caps 16,
escape refinements 16, binary image 26, uniform inverse branching 8.
The final new manifest has 24 hashes, all reauthenticated.

Finite counts: 45052 pairs with certified cycle entry (32767 source
pairs plus 12285 returned-interval pairs), 2906007 exact pre-tail cost
terms, 180208 terminal-phase ratio checks, three complete rational
cross-checks, 45 annulus bounds, 1365 original-source transports, and
60 exact progression/interval pairings. Rounded aggregation used
outward enclosures with denominator 2^96; no floating decisions.
The inverse spine checked 1226 normalized growth bounds and 1225 direct
six-step links; 68 full trajectories were checked separately. By index
1225 it supplies exact cone witnesses for every root 1..1023. The last
new prefix 1023 uses binary shift 5398. Universal cone density remains
the WRITTEN irrational-rotation proof, not finite extrapolation.

Exploratory f64 scouts in /tmp/collatz-gradient-power-scout.rs and
/tmp/collatz-actual-energy-scout.rs ran to level 21 and are terminal.
They suggested testing correlated temporal means instead of assuming
uniform high moments. Their larger-range displays were not adopted as
certified results. A brief primary-source literature search supplied
no external theorem used here. No packages were installed.

NEXT: use the weaker local temporal condition Q as a direct target.
The required statement is now zero limiting reversed negative drift
on each fixed source annulus, or any proved sublinear temporal bound
there. Uniform high moments across annuli are unnecessary for this
criterion. Correlated mean estimates using the Lp return densities
remain possible, and the time-summed whole-annulus charge R_k<=C L_k
is still an alternative, supported only on the finite range above.
The spine/cone lemma applies to any set closed under both binary
children and disjoint from the basin of one; proving such closure
for the full nonconvergence set would also exclude other cycles, but
that closure is NOT proved. Preserve the distinction between escape
and all counterexamples.

Collatz remains unresolved and the full user goal remains active.
All jobs are terminal. No agents, installs, credentials, staging,
commits, or other Git writes occurred in this turn.

## 2026-10-13: cumulative affine return budgets and the 6/5 density range

The previous goal turn was progress. The full conjecture remains
unresolved and the active goal is unchanged. The new substantive result
is WRITTEN, with eight kernel arithmetic roots and exact finite support:

  K*_beta in Lp(mu_3) for 0<=beta<1/2, 1<=p<6/(5+2beta).

For beta=0 this improves p<10/9 to p<6/5. It does not prove the actual
gradient pairing, the temporal criterion Q, escape exclusion, or absence
of other cycles. The grade-sensitive weight considered at the beginning
of this turn was already exactly V_t in GRADE-WEIGHT-MOMENTS.md; no new
result was claimed for that duplicate construction.

Files:
  docs/RETURN-AFFINE-BUDGET.md
  lean/ReturnAffineBudget.lean
  verify_return_affine_budget.py
  results/return-affine-budget/verification.json
  results/return-affine-budget/replay.json and eleven build logs.

Let C_t=lambda_t+B_t=(3^a_t+N_t)/2^t. This is the formal affine image
of one under the sampled parity prefix, NOT generally the actual orbit
of the integer one. New KERNEL identities prove augmented-numerator
recurrence and lifting, exact composition
  C_(t+h)=lambda_continuation*C_t+B_continuation,
the parity-count generating polynomial for every natural argument,
finite drift telescoping with denominators cleared, and the sorted
fibre rank inequality 3^a*(j+1)<=3^a+N_j.

WRITTEN fixed-time moment: for 0<eta<1,
  r_eta=(2^(-eta)+(3/2)^eta)/2<1,
  sup_t E C_t^eta <= A_eta=1+2^(-eta-1)/(1-r_eta).
At a count return the existing fresh-prefix estimates give
  E lambda_tau^eta<=r_eta,
  E B_tau^eta<=m_eta=1+7eta/(1-2eta), for eta<1/2.
Killing at balanced fusion, composing C, and telescoping gives
  E sum_(j<N) C_(S_j)^eta
    <=M_eta=(1+m_eta*C_*)/(1-r_eta), eta<1/2,
  C_*=540*2^5180.
At eta=1/4 the bound is <=40+180*C_*. The sum includes j=0;
the occupation measure uses 1<=j<N and so is also bounded. No
independence between the continuation slope and correction is assumed.

WRITTEN fractional fibre estimate, alpha=p-1>0:
  ||kappa_(t,a)||_p^p <= p*2^(-t)*sum_selected C_t^alpha.
Sort the injective numerator quotients, use
  m^p<=p*sum_(j=1)^m j^(p-1),
then integrate each ternary fibre. Combining all t,a without paying
for their overlap would be invalid; the proof does pay that cost.

The full-period count is Binomial(t,1/2). Define typical counts by
  |a-t/2|<=2*sqrt(t*log(t+2)).
The elementary exponential-moment proof gives atypical mass
<=2*(t+2)^(-8). Holder against the fixed-clock half moment makes
the selected atypical density satisfy
  ||psi_t||_p^p << (t+2)^(17alpha-8),
so these norms are summable for p<6/5.
There are O(H^(3/2)*sqrt(log H)) typical (t,a) components in H<=t<2H.
Using the all-return C^eta budget and the prior occupation-clock tail
O((1+log H)/sqrt H), their combined density Delta_H satisfies
  ||Delta_H||_p^p << H^[3alpha/2-1/2+alpha/(2eta)]
                     *log(H+1)^[alpha/2+1-alpha/eta].
Choosing alpha/(1-3alpha)<eta<1/2 is possible exactly for alpha<1/5.
Dyadic Minkowski and monotone convergence give p<6/5. Column Holder
with the prior separation moments then gives p<6/(5+2beta).
Neither the endpoint nor optimality is claimed.

For beta=0 a complementary power strictly above six could suffice,
instead of strictly above ten. The actual accumulated gradient norm
is still unproved, and the Haar estimate is not an infinite-cutoff
trace bound on a fixed ordinary integer interval. The finite transfer
factor 1+3^H/M remains. This is the same substantive arithmetic gap.

Verification passed 2026-10-13T20:12:43.907413+00:00 on pinned
Lean 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Eleven sequential fresh builds took 6.282 seconds; all eight new roots
have only standard axioms and no warnings, sorry, or native evaluation.
The manifest authenticates 28 files. Prior records reauthenticated:
binary image energy 26 hashes, return correction 21, occupation 29.

Exact finite replay checks 36864 compositions, 12288 lifts,
131071 full-period rows through clock sixteen, 102 generating-polynomial
identities, 17 fourth moments, 41109 full and 2232 selected image fibres,
459 full and 174 selected fractional component bounds, 65535 adjacent
return tests, and 2552 nonfused even return prefixes. A full source
period through clock fourteen checks 14109 cumulative return
compositions and eight finite killed-drift inequalities. Direct ternary
moments use 81162 power evaluations, plus 2480 exact dyadic/atypical
exponent checks and twelve weighted exponent checks. Fractional powers
are enclosed with integer roots at denominator 2^48. No floating
comparison decides a claim. Finite p=3/2 checks are explicitly NOT an
infinite integrability result at that exponent.

An editorial correction in ANNULUS-TIME-BUDGETS.md now states correctly
that source-level average budgets are weaker than its uniform charge
(3), but stronger than its qualitative condition Q. The complete
annulus verifier was rerun and passed at
2026-10-13T20:15:34.293783+00:00; its 24 hashes were reauthenticated.
The finite all-future cost results are unchanged. Both final manifests
were independently rehashed after these checks.

### Next candidate: a bounded potential at active gap steps (NOT adopted)

A potentially stronger stopping estimate was derived after the verified
6/5 milestone. It has not yet been written as a reviewed theorem,
formalized, or added to any verification manifest. Check it next rather
than rediscovering it. It may extend returned correction moments to
all eta<1, but no such extension is claimed in the authoritative note.

At absolute count gap d>=1, let W be the wait INCLUDING the next active
step. COUNT-RETURN-CLOCK gives E[W|prefix]<=v(d)+2 with
v(d)=v_2(3^d-1)<=d+1. The next active sign is fair, although W and
the coefficient data can be correlated. The holding time is NOT bounded
deterministically; only this uniform conditional expectation is needed.

For the affine coefficients lambda_W,b_W of either endpoint during
that block, bounded stopping followed by Fatou should give
  E lambda_W^eta <= r_eta,  0<eta<1, W>=1,
  E b_W <= E W/4,
  E b_W^eta <= ((v(d)+2)/4)^eta <= d+3.
Choose r_eta<q<1 and define the bounded half-line Green potential
  h(d)=2 sum_(j>=1) min(d,j)*q^(j-1)*(j+3).
Then h(0)=0, h>=0, and
  [h(d-1)+h(d+1)]/2 = h(d)-q^(d-1)*(d+3).
It is bounded by h(infinity)=(8-4q)/(1-q)^3, with
  h(1)=(8-6q)/(1-q)^2.
The correct closed form is
  h(d)=[8-4q-2*q^d*((d+4)-(d+2)*q)]/(1-q)^3.
A terminal exact rational calculation checked the finite-sum curvature
at d=1,2,7,31 with q=9/10; that calculation alone is not a global proof.

If a current cumulative coefficient is B>=0, put
  F(B,d)=q^d*B^eta+h(d).
Across the active block, B'=lambda_W*B+b_W and d'=d+-1. Thus
  E[q^d'*(B')^eta]
    <=q^(d-1)*(r_eta*B^eta+d+3)
    <=q^d*B^eta+q^(d-1)*(d+3).
The h term cancels the last cost exactly, suggesting F is a
nonnegative supermartingale at active epochs. Stop at gap zero or K
and use nonnegativity at K, then let K increase. The known a.s. finite
return would give E B_return^eta <= F(B_start,d_start).
For a fresh count-return cycle, even D returns in one step; odd D
departs to gap one after one step, with E b_1^eta=2^(-eta-1).
The prospective uniform conclusion is
  E b_tau^eta <= q*2^(-eta-1)+h(1) <= 1+h(1), eta<1.

If this audit succeeds, reuse E lambda_tau^eta<=r_eta to obtain
returned separation drift and all-return C and D moment budgets for
every eta<1, retaining the already proved C_* as the cycle-count
constant. In the present density proof, replacing eta<1/2 by eta<1
would improve the unweighted range to p<5/4 and the separation-weighted
range to beta<1, p<5/(4+beta). Atypical estimate (13) still works for
alpha<1/4. These are prospective consequences, NOT current results.
They would still leave ordinary-integer sampling and actual gradients
uncontrolled, so even a successful potential does not settle Collatz.

All jobs are terminal. A primary-source literature check added no new
external theorem. No agents, installations, credentials, staging,
commits, or other Git writes were used by the assistant. The user
committed the preceding milestone while work continued; preserve the
index and their concurrent changes.

## 2026-10-13: local two-coordinate-obstruction source review

The user explicitly pointed out their local clone and asked whether its
code could help solve Collatz. Reviewed the clean clone at
  /Users/jean/Personal/collatz-two-coordinate-obstruction
  a7275d5a73814d3d9a400c6fe6577de9542b03a3 (2026-10-08).
Use this source rather than redownloading the same manuscripts. The clone
was read only. No new external theorem was replayed or imported into the
local Lean dependency graph. Collatz remains unresolved; the goal is active.

Added:
  docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md
  verify_two_coordinate_review.py
  results/two-coordinate-review/verification.json
README and ATTEMPT link the review and distinguish its external inputs.

The review reads all four paper summaries, the envelope proof, the relevant
energy/occupation/Fourier sections, theorem maps, and selected Lean endpoint
proofs. Independent published-inventory checks authenticate 7,493 distinct
files in eight packages plus four paper/source/map sets. The module manifests
check 2,457 source entries; broader inventories contain 2,522 Lean files,
including audit/provenance sources. These are integrity checks, NOT fresh
Lean compilation or authentication of external compiled libraries. Seven
retained upstream execution records report PASS and are hash authenticated.
Density bundles use Lean 4.30.0-rc2; Fourier uses 4.35.0-rc3. Do not confuse
these records with our earlier completed 389-module PLD replay.

NEW WRITTEN EXTERNAL DEDUCTION: denote our full binary image density by b_t
to distinguish it from their Syracuse cylinder rho^S_k. Exact parity-word
enumeration gives b_0=1 and b_(t+1)=L b_t, where
  Lf(z)=f(2z)/2+(3/2)1_(z=2 mod3)f((2z-1)/3).
The new external envelope satisfies LE<=E POINTWISE, E>=c>0 on units,
E(n)=g(n)=delta G_n n D_n at every positive integer, and E in Lp for p<2.
Here delta=log(4/3)/2, G_n is the periodic Green factor, D_n the actual
weighted first-hit density. Write h=(3/2)1_(z=2 mod3). Then
  b_t=2^-t+sum_(j<t)2^(-(t-1-j)) L^j h
     <=2^-t+(3/c)(1-2^-t)E.
This proves externally dependent uniform full-image Lp bounds for every
1<=p<2 and b_t(n)<=2^-t+(3/c)g(n) at fixed positive integers. It improves
the previous time-growing bound for the full law, not the all-return law.
The integer majorant g is unbounded in every unit residue class.

A common-noise coupling with a stationary binary affine chain gives weak
convergence of b_t to the stationary law: the difference acquires a factor
3^a with a~Binomial(t,1/2). Uniform L2 bounds would then bound all stationary
cylinder L2 norms and contradict the external non-L2 theorem. This is a
written external consequence, not a local kernel theorem or a claim about
the optimal exponent of our selected return density.

For dyadic all-return block Delta_H, uniform per-clock Lq gives ||Delta_H||q
<=C_q H, while the existing L1 clock tail is O(H^-1/2 log H).
Interpolation yields p<3q/(2q+1); taking q<2 recovers p<6/5 only.
Our prior independent RETURN-AFFINE-BUDGET proof is unchanged. No stronger
all-return exponent, actual-gradient estimate, or infinite-cutoff integer
sampling bound follows from this review.

MOST USEFUL TARGETS IN THE CLONE:
- GammaFreeFirstHitCoefficient.lean discharges its reciprocal-density floor
  in the public endpoint; exact first-hit coefficients satisfy a_k(N)<=L N D_N
  at positive odd depths, including periodic targets. Its finite fan selects
  a unit nonperiodic predecessor with exponent <=6 and uses disjoint basins.
- MaskedEnergyPeriodicityEquivalence.lean proves E_K/(K+1)->0 iff every
  positive orbit is eventually periodic. E_K is the squared normalized
  Syracuse cylinder density at odd N<3^K with no return in <=K odd steps.
  This is NOT our dyadic E_s. The decomposition controls the no-small-ancestor
  portion by L epsilon(M)(2+3K+(64/81)^K(1+2K)), epsilon(M)->0. The remaining
  small-ancestor portion is on actual forward orbits of bounded seeds and
  remains open. Even a successful estimate permits additional cycles.
- RawOccupationDivergentExcess.lean proves that a divergent odd unit root
  forces liminf sum_(odd N<=R)D_N/log R >=1/log(4/3)
  +D_u/(P_infinity(u)log(3/2)), with a strictly positive additional term.
  The matching upper bound is open. ActualInverseHeightClock.lean proves an
  a.s. inverse-path height rate at fixed nonperiodic unit roots, without the
  expectation/uniform-integrability estimate needed for that upper bound.
- The Fourier theorem selects exact TOTAL-EXPONENT slices, uniformly in
  affine seed and total-exponent phase. It does not select arbitrary paired
  return histories. Polynomial slice mass does not repair this distinction:
  conditioning a uniform cyclic law on its first third of residues gives
  probability 1/3 and a primitive Fourier coefficient with modulus >=1/2.

Exact local finite checks passed: 2,047 direct binary residue rows, 2,047
independently generated affine words, 88,572 full ternary transfer values
through depth ten, 2,816 actual positive-target inverse-tree comparisons,
and four rational interpolation exponent tests. These certify finite
identities only. The written all-depth operator argument is in the review.

CURRENT UNADOPTED CANDIDATE: before the clone review, added
lean/ActiveGapPotential.lean. Its nine standalone kernel arithmetic roots
passed a development build using the existing temporary dependency objects:
min/Green curvature, nonnegative Green cap, two geometric polynomial
identities and caps, and exact fractional-slope constants. This has no final
verification manifest or completed analytic note yet. The prospective
eta<1 return moment and p<5/4 all-return range in the preceding entry are
still NOT adopted. Resume that audit without mistaking the development
module for a complete verified milestone.

No agents, installations, credentials, staging, commits, or other Git
writes were used. Preserve the user's index and existing changes. The next
research step can use the external majorant as an explicitly stated input,
or continue the independent active-gap potential; neither route has closed
the actual-gradient/integer-sampling gap.

## 2026-10-13: active-gap potential and the 5/4 density range

The previous local-clone review turn was progress. This turn completed
the formerly unadopted active-gap potential. The new infinite results are
WRITTEN, with nine kernel arithmetic roots and independent exact finite
checks. The Collatz objective remains active and unresolved.

Files:
  docs/ACTIVE-GAP-POTENTIAL.md
  lean/ActiveGapPotential.lean
  verify_active_gap_potential.py
  results/active-gap-potential/verification.json
  results/active-gap-potential/replay.json and twelve build logs.
README and ATTEMPT link the new result. The prior 6/5 note remains intact
as a verified earlier result. The local-clone review now links this later,
independent improvement; its own new stationary comparison is still an
external deduction and is not used in the active-gap proof.

At a nonzero absolute count gap d, the physical wait W INCLUDING the next
active step has conditional mean <=v_2(3^d-1)+2. Bounded physical stopping
and Fatou give, for either endpoint and every 0<eta<1,
  E lambda_W^eta <=r_eta=(2^-eta+(3/2)^eta)/2<1,
  E b_W <= E W/4,
  E b_W^eta <=d+3.
The last bound needs only v(d)<2d and concavity; no deterministic wait
bound is used. The two endpoint parities, wait, and active sign can be
correlated. Each marginal next parity is fair, and the next active sign
is conditionally fair under the coherent binary residue law.

Choose r_eta<q<1. The bounded half-line Green potential is
  h_q(d)=2 sum_(j>=1)min(d,j)q^(j-1)(j+3),
  h_q(0)=0, h_q(1)=(8-6q)/(1-q)^2,
  0<=h_q(d)<=(8-4q)/(1-q)^3,
  [h_q(d-1)+h_q(d+1)]/2=h_q(d)-q^(d-1)(d+3).
For current cumulative correction B, define F(B,d)=q^d B^eta+h_q(d).
Across an active block B'=lambda_W B+b_W and d'=d+-1. Using
q^d'<=q^(d-1) gives
  E[q^d' B'^eta]<=q^d B^eta+q^(d-1)(d+3).
The h curvature cancels this cost exactly. Thus F is a nonnegative
supermartingale at ACTIVE epochs. Finite active-step cutoffs followed
by Fatou are sufficient: the fair gap walk hits zero a.s. from every
finite gap, and every wait is finite a.s. by its finite expectation.
No optional-stopping equality or integrability of the full physical
return time is assumed.

For a fresh count-return cycle, even separation returns in one step.
Odd separation first departs to gap one. Both cases give the uniform
conditional bound
  E b_tau^eta<=b_eta:=1+h_q(1), all 0<eta<1.
This replaces eta<1/2. For eta=1/2,3/4,7/8 take q=63/64,127/128,255/256
and obtain b_eta=8577,33537,132609 respectively. These are coarse constants;
retain the older quarter-power constants when using the old EN estimate.

Use C_t=lambda_t+B_t, the FORMAL image of one under the sampled parity
word, and retain C_*=540*2^5180 as the bound on E N. Killing at balanced
fusion and finite drift telescoping prove
  E sum_(j<N) C_(S_j)^eta <=(1+b_eta C_*)/(1-r_eta),
  E sum_(j<N) D_j^eta <=(1+2b_eta C_*)/(1-r_eta), 0<eta<1.
These sums include j=0; the occupation measure uses 1<=j<N. Restricting
to even initial sources only decreases nonnegative integrals.

For eta>=1/2, concavity of 1-r_eta and the exact half-moment cap imply
1-r_eta>=(1-eta)/16. Choose q=1-(1-eta)/32. Then
  b_eta<=8193/(1-eta)^2,
  both occupation moment budgets <=B/(1-eta)^3,
  B=16(1+16386 C_*).
Choosing eta=1-1/log_2 u for u>=4 gives
  nu(C>u),nu(D>u)<=2B(log_2 u)^3/u,
  Pr(b_tau>u)<=16386(log_2 u)^2/u.
No endpoint first moment is asserted.

The previous fractional-fibre and binomial-concentration proof now takes
alpha/(1-3alpha)<eta<1, alpha=p-1, which is possible iff alpha<1/4.
The atypical exponent (17alpha-8)/p is still <-1. Dyadic Minkowski yields
  K*_0 in Lp for 1<=p<5/4.
Column Holder with D^gamma moments for gamma<1 gives the stronger range
  K*_beta in Lp for 0<=beta<1, 1<=p<5/(4+beta).
The method's limiting dyadic exponent is 2alpha-1/2. Its range is not
claimed optimal; stronger overlap or joint clock/coefficient control would
be needed to improve this component-counting argument further.

Holder against the existing O(H^-1/2 log H) clock tail and the near-one
moment constants also gives the written truncation rate
  ||K*_beta-K*_(beta,H)||1
    =O_beta(H^(-(1-beta)/2)(1+log H)^(1+2beta)), beta<1.
The unweighted complementary gradient exponent can now be any q>5.
Actual accumulated-gradient power bounds and infinite-cutoff integer trace
sampling are still unproved. The finite transfer still has its
1+3^H/M factor. The temporal criterion Q and exclusion of other cycles
remain open. No external stationary result was needed for these bounds.

Final verification passed 2026-10-13T21:00:53.975945+00:00 on pinned
Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Twelve sequential fresh builds took 4.729 seconds. All nine new roots
use standard axioms only; no warnings, admitted proof or native evaluation
occurred. The manifest authenticates 31 files. The affine-budget,
occupation, and count-clock prior records had 28,29,11 hashes checked.

Exact finite replay checked 1,584 integer Green curvatures, 375 geometric
identity pairs, 1,152 exact series remainders, 384 rational curvatures/caps,
three fractional slope/budget constants, and 31 near-one chord comparisons.
It checked 270,816 actual active-block paths at gaps 1,2,3,4,8,16,31,32 and
varied affine offsets, retaining unfinished paths through clock caps
4,8,12; 404 bounded-stop slope/correction identity pairs; 1,488 active-time
sign balances; 3,348 partial terminal potential bounds with initial
correction 0,1,16; and 1,116 partial block moment comparisons.
Fresh-return tests covered 34,816 paths at eight starting separations,
plus 96 moment bounds. A complete binary period through clock fourteen
checked 20,239 cumulative compositions (including terminal fusion),
84,654 fractional moment values at nonfused returns, 48 killed drift
bounds and six finite total budgets. There are 3,120 exact density-exponent
and fifteen weighted-exponent checks. Fractional roots use outward rational
enclosures at denominator 2^48, reusing and authenticating the earlier
integer-root implementation. No float decides a verification inequality.

The review verifier was rerun after its follow-up link changed, passing at
2026-10-13T21:00:48.377013+00:00. Final independent rehashes checked all
31 potential files and all four review-local hashes; local links passed.

NEXT: the active-gap candidate is now completed, so do not restart it as
unadopted. The remaining problem needs information about actual gradients
or integer sampling, or a sharper structural treatment of the selected
return columns. A possible identity to audit if grouping by common odd
count helps: let A f=f(2z)/2 and B f=(3/2)1_(z=2 mod3)f((2z-1)/3).
For the FULL binary density pieces rho_(t,a), summing over t at fixed a
formally gives Sigma_0=2 and Sigma_a=(I-A)^(-1)B Sigma_(a-1), suggesting
Sigma_a=2 rho^S_a for the canonical Syracuse cylinder density. This is
only a recorded lead, not a new theorem or verification claim. A uniform
norm per count alone would still recover only p<6/5 with the current
clock tail; any improvement needs the selected-return structure as well.

All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's concurrent
work and index. The full positive-integer conjecture remains unresolved.

## 2026-10-13: fixed-integer return Cesaro limit from the local clone

This goal turn is progress. It completed a new WRITTEN, externally
dependent arithmetic consequence of the local obstruction repository:
  K*_(0,H)(n)/H -> 0 for EVERY FIXED positive integer n.
Here K*_(0,H)=sum_(1<=t<=H)kappa_t is the unweighted density accumulated
over all nonfused equal-count returns of even initial adjacent pairs.
This is a fixed ordinary-integer trace statement, not just Haar-a.e.
It is sublinearity of a truncated sum, NOT finite total occupation,
pointwise decay of kappa_t, uniformity for growing target intervals,
the temporal criterion Q, or the Collatz conjecture.

Files:
  docs/INTEGER-RETURN-CESARO.md
  lean/IntegerReturnCesaro.lean
  verify_integer_return_cesaro.py
  results/integer-return-cesaro/verification.json
  results/integer-return-cesaro/replay.json and four build logs.
README, ATTEMPT, and the local-clone review link this follow-up.

EXACT INTEGER BRIDGE:
Existing CollatzPacking.residue_image_bound already proves
  U^t(r)<3^a for r<2^t, a=wt(t,r).
It was NOT necessary to rediscover that bound. New kernel roots transfer
the packing definitions to CollatzAffine and prove that a matching
positive target column n=U^t(r) mod3^a has a unique nonnegative quotient
q=floor(n/3^a), hence a positive actual source m=2^t q+r reaching n.
Conversely every positive predecessor has this residue and quotient.
Thus b_t(n)=sum_(m>0,U^t(m)=n)3^wt(t,m)/2^t exactly. Balanced fusion
and count equality lift with the residue. Kernel source bound m<=2^t n
makes every finite-clock inverse sum finite. Balanced fusion persists,
so nonfusion at t implies nonfusion at every L<=t; its mask has period 2^L.

EXTERNAL INPUTS, NOT LOCALLY REPLAYED:
Clone still clean at a7275d5a73814d3d9a400c6fe6577de9542b03a3.
WeightedSourcePeriodicMean.lean proves, for ANY fixed periodic p in[0,1],
  X^-1 sum_(m<=X) w_n(m)p(m) -> D_n mean(p).
There is NO odd/unit support restriction in this source-mean theorem.
FirstHitWordWeights.lean gives lambda_firsthit=n*w_n(m)/m, w in[0,1].
ActualUnconditionalCanonicalTrace.lean proves zero logarithmic density
of first-hit ELAPSED SHORTCUT clock exceptions among odd basin sources,
with drift delta=log(4/3)/2. Its sources may be divisible by three.

IMPORTANT SUPPORT AUDIT:
PeriodicMarkedFirstHitMeanFromSources.lean's PUBLIC marked theorem has
odd-unit support and an odd-count clock. It is not directly applicable
to our nonfusion masks. The new deduction explicitly uses the more
general source mean plus the separate elapsed clock, not an unstated
strengthening of the public marked theorem.

WRITTEN PROOF:
For m=2^ell q with q odd and q>n, first-hit clocks satisfy
tau_n(m)=ell+tau_n(q). At fixed ell, the difference from
log(m)/delta is a fixed shift of the odd clock error. Thus each fixed
valuation layer inherits zero logarithmic exception density. The
remaining layers have harmonic mass at most 2^-J(1+log X). Take X->infinity
first and J->infinity next to extend the clock law to all positive sources.
Initial-halving hits are finite exceptions on each retained layer.

Partial summation gives sum_(m<=X)w_n(m)p(m)/m
=D_n mean(p)logX+o(logX). Squeeze the finite first-hit mass F_H^p(n)
using good-clock cutoffs exp(delta H/(1+-epsilon)); bad sources contribute
o(H) because every hit by H has m<=2^H n. Thus
  F_H^p(n)/H -> delta*n*D_n*mean(p).
No new unbounded-source tail estimate is needed.

Let B_t^p(n)=sum_(m>0,U^t(m)=n)lambda_t(m)p(m).
At a nonperiodic target, total visits through H equal first hits.
At a periodic target of least period R and ratio rho=3^a/2^R<1,
  sum_(t<=H)B_t^p(n)=sum_(jR<=H)rho^j F_(H-jR)^p(n).
The convergent first-hit mean gives F_h<=C(h+1), so geometric dominated
convergence proves
  H^-1 sum_(t<=H)B_t^p(n) -> g(n)mean(p),
  g(n)=delta*G_n*n*D_n, G_n=(1-rho)^-1 if periodic and 1 otherwise.
This is physical-time Cesaro, not the external Syracuse-depth statement.
Setting p=1 also identifies the Cesaro limit of our full b_t(n).

Now p_L(m)=nonfusion of (m,m+1) by L is periodic modulo 2^L with mean
q_L=Pr(T>L)->0 by our existing WRITTEN coherent-binary clock bound.
For t>=L, selected actual returns satisfy kappa_t(n)<=B_t^(p_L)(n).
Hence limsup_H K*_(0,H)(n)/H<=g(n)q_L for each fixed L. Send L->infinity.
This proves the claimed fixed-target limit. It is uniform over each
FIXED finite target set, implies zero time density of kappa_t(n)>=epsilon,
and implies the corresponding vanishing Abel average. There is no rate
uniform in the period 2^L or target n. The old proposed fixed-odd-count
identity Sigma_a=2rho^S_a was bypassed and remains only a recorded lead.

VERIFICATION:
Final record passed 2026-10-13T21:18:28.322266+00:00 on pinned Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Four fresh sequential
builds took 1.327 seconds. All nine audited roots use standard axioms only;
no warning, admitted proof, or native computation. Thirteen local hashes,
eleven prior clock hashes, four review-local hashes, and nine specific
external source hashes were authenticated. The review was refreshed at
2026-10-13T21:18:26.254688+00:00 after the new link; all 7,493 distributed
hashes and its existing exact finite transfer checks passed again.

Exact finite checks through clock 12 and targets 1..128:
8,191 residue endpoint bounds; 15,832 positive column preimages;
1,664 complete residue/inverse-tree bijections; 15,615 first-hit weight
identities; 101,364 lifted mask/selection checks; 7,424 marked selection
bounds; 19,968 finite all-visit reconstructions with twelve periodic marks;
the known periodic targets 1 and 2; 10,668 dyadic first-hit clock transports;
2,322 exact dyadic harmonic tail identities. Rational finite averages are
diagnostics only, with no convergence-rate claim or nonperiodicity
inference from a finite search. No floating value decides a check.

NEXT GAP:
The new theorem handles fixed inverse targets. It does not control the
moving endpoints of a hypothetical divergent forward orbit, nor sum
actual gradient costs. Their target dependence can grow while every
fixed-target Cesaro limit still vanishes. A moving-target or joint
source/target estimate is still needed; do not infer Q from (1). The
external inverse Doob height clock likewise lacks the expectation/UI
bound needed for the raw occupation upper estimate. The independent
active-gap potential and p<5/(4+beta) range remain completed and valid.

All work is terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's index and
existing changes. The Collatz goal remains active and unresolved.

## 2026-10-13: independent uniform harmonic return trace bound

This goal turn is progress. A new WRITTEN argument strengthens the last
integer Cesaro conclusion and REMOVES its external analytic dependencies
for that conclusion. It proves, for EVERY n>0 and integer H>=1,
  K*_(0,H)(n) <= Z_H(n) <= 350 C_star n G_n sqrt(H),
  C_star=540*2^5180.
Z_H counts ALL nonfused inverse visits, not just even-source equal-count
returns. G_n=1 for nonperiodic n and (1-rho)^-1 for a periodic target,
rho=3^a_R(n)/2^R at its least positive shortcut period R.
New kernel arithmetic proves G_n<=3n+1 in all cases. No unknown cycle
is assumed absent. The Collatz goal remains active and unresolved.

Files:
  docs/HARMONIC-RETURN-TRACE.md
  lean/HarmonicReturnTrace.lean
  verify_harmonic_return_trace.py
  results/harmonic-return-trace/verification.json
  results/harmonic-return-trace/replay.json and five build logs.
README, ATTEMPT, the earlier integer Cesaro note, and the clone review
link this stronger follow-up. The older marked full-image identification
g(n)*mean(p) REMAINS an external deduction; it was not reclassified.

NEW WRITTEN PROOF:
Let p_L(m) be nonfusion of (m,m+1) by clock L, and q_L its full binary
period mean. p_T<=p_L for L<=T; p_L has period 2^L; q_0=1.
Reuse the existing local WRITTEN fusion tail q_L<=A/sqrt(L), L>=1,
with A=14 C_star. No external density, clock or envelope input is used.

For any hit U^t(m)=n with t<=h, local arithmetic gives
  m<=2^h n,   2^h(n+1)<=3^h(m+1).
Thus any two positive sources u,v reaching n by h satisfy
  v<=3^h(u+1)<=2*3^h*u.
Their complete source interval meets at most 2h+2 binary ranges
[2^j,2^(j+1)), independently of n. This controls the RATIO of source
sizes, so no log(n) term or fixed-target asymptotic is needed.
The affine lower bound also gives lambda_t(m)/n<=1/m.

For a binary SOURCE range j and mask clock T, put L=min(j,T).
The mask p_L has exactly 2^j q_L marked points in that full range;
p_T<=p_L and 1/m<=2^-j imply
  sum_(2^j<=m<2^(j+1)) p_T(m)/m <= q_min(j,T).
The earlier mask is essential for small sources. At m=1, p_12(1)=1,
while q_12=655/1024. Replacing every band bound by q_T is false.
Write Q_T=sum_(j<T) q_j. Any interval meeting B source ranges has
harmonic p_T mass <=Q_T+B*q_T. From the square-root tail,
Q_T<=2 A sqrt(T) for T>=1 (the initial j=0 term is included).

Let F_H(n) count FIRST hits through H with coefficient lambda_tau and
mask p_tau. In a clock block T<=tau<2T, the sources lie in P_(2T-1)(n),
whose interval meets at most 4T binary ranges. Hence
  block mass/n <=Q_T+4T*q_T <=6 A sqrt(T).
Sum blocks T=1,2,4,...<=H. Their square roots sum to less than 4sqrt(H).
The clock-zero source m=n adds at most one after division by n.
Therefore F_H(n)<=25 A n sqrt(H), uniformly over n.

If n is nonperiodic, Z_H(n)=F_H(n). If it is periodic, each source's
later visits acquire factors rho^j and their nonfusion masks can only
decrease. Thus Z_H(n)<=G_n F_H(n). An actual positive cycle has an odd
step; the new positive-count coefficient inequality
  (3m+1)3^a_t(m)<=3*2^t*U^t(m) whenever a_t(m)>0
gives rho<=3n/(3n+1)<1 and G_n<=3n+1. This proves the stated bound.

CONSEQUENCES:
- sup_(n>0) K*_(0,H)(n)/(H n G_n)<=350 C_star/sqrt(H).
- For each fixed positive target, the previous vanishing Cesaro limit
  now has an independent O_n(H^-1/2) proof, also for the larger Z_H.
- Unnormalized convergence is uniform on all-target windows
  n<=R(H)=o(H^(1/4)); on nonperiodic targets, R(H)=o(sqrt(H)) suffices.
- For every sigma>1/2, the ACTUAL integer trace with a time discount
  sum_(t>=1)t^-sigma kappa_t(n) is finite, bounded by
  350 sqrt(2) C_star n G_n / (1-2^(1/2-sigma)).
- Its Abel average satisfies
  (1-z)sum_(t>=1)kappa_t(n)z^t
     <=350 C_star n G_n sqrt(z(1-z)), 0<z<1.
These are written consequences, not additional kernel real-analysis claims.

VERIFICATION:
Final record passed 2026-10-13T21:37:01.446836+00:00. Five fresh sequential
builds took 2.649 seconds on pinned Lean 4.33.1 commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten audited roots use standard
axioms only, with no warnings, admitted proofs, or native computation.
The manifest has fourteen local hashes and authenticates all eleven
hashes of the prior count-return-clock record. No external source or
compiled external library is needed for this proof.

Exact finite checks at clock cap 16 and 134 targets, including targets
2^40+1 and 2^80+17, passed:
131,071 direct residue masks; 983,041 positive-count correction bounds;
187 nested range population checks and 187 exact harmonic range bounds;
882 rational harmonic interval comparisons; 52,173 actual inverse paths
and coefficient checks; 2,278 predecessor span bounds; 670 first-hit
clock blocks; both known periodic targets 1 and 2; 2,144 nonfusion and
selected-return trace comparisons. A finite-table coefficient A=3 fits
the tested mask table ONLY; it is not an all-depth constant claim.
All verification decisions use integers or exact fractions.

The older review was refreshed after its new follow-up link at
2026-10-13T21:35:54.949033+00:00 (all 7,493 source hashes passed again).
The original integer Cesaro record was refreshed at
2026-10-13T21:35:58.316654+00:00 after the historical note gained the
independent-proof link. Its original full marked limit still depends
on the external theorems. No external Lean replay was done.

REMAINING GAP / NEXT RESEARCH:
The sqrt(H) bound still allows a persistent individual contribution at
a moving divergent-orbit target: lambda_t(m)/U^t(m)=W_t(m)/m may tend
to a positive number. Thus this does not prove Q or absence of escape.
Time-discounting the inverse returns does not pay for an arbitrarily
long future excursion following one fixed return prefix; actual gradient
costs and their correlations remain the issue. Finite total undiscounted
occupation at a fixed integer also remains open. The source/count
grouping lead Sigma_a=2rho^S_a remains unused, not adopted.

All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's index and
concurrent changes. The full Collatz goal remains active and unresolved.

## 2026-10-14: exact return-slope tilt and critical first moments

This goal turn is progress. The new WRITTEN change-of-measure argument
proves an exact fresh-return slope law and a sharp obstruction at the
first separation moment. The improved fractional estimates also lower
the logarithmic powers in occupation and clock-truncation tails. This
does not prove Q, exclude escape or other cycles, or solve Collatz.

Files:
  docs/RETURN-SLOPE-TILT.md
  lean/ReturnSlopeTilt.lean
  verify_return_slope_tilt.py
  results/return-slope-tilt/verification.json
  results/return-slope-tilt/replay.json and seven build logs.
README and ATTEMPT link the result. Earlier authenticated research
notes and records were not edited or reclassified.

LAW AND EXACT SLOPE:
Use the coherent full binary residue law, not one finite interval of
ordinary integer inputs followed forever. A fresh pair has positive
integer separation D. At the first positive count return tau its
endpoint slopes agree. For odd D, condition on either first input
parity and label F the initially odd endpoint and S the initially even
one. The lead k=a_F-a_S stays positive until the return.

Tilting by either endpoint's continuation slope changes its conditional
odd probability to 3/4. Active/holding status is predictable: both
endpoint parities flip with the fresh bit. At nonzero gap k the endpoint
relation is Y=3^k X+c. At least h holds requires
2^h | (3^k-1)X+c, allowing at most 2^v(k) source residues modulo 2^h,
where v(k)=v_2(3^k-1). The same count holds for either endpoint.
Every endpoint parity word has tilted mass at most (3/4)^h. Thus
  P_tilt(at least h holds | prefix) <=min(1,2^v(k)(3/4)^h) ->0.
Every active step is finite under the tilted laws as well.

The embedded walk under F tilt has outward probability 3/4, giving
zero-hit probability h_F(k)=3^-k. Under S tilt, inward probability
is 3/4 and h_S(k)=1. On [0,K] the respective probabilities are
  (3^(K-k)-1)/(3^K-1), (3^K-3^k)/(3^K-1).
Finite exit and the maximum principle identify them; then send K up.
Summing finite stopping cylinders proves
  E[lambda_sigma 1_(sigma finite) | prefix] = P_tilt(sigma finite).
No unbounded optional-stopping equality or UI is assumed. Original
return is almost surely finite by the existing fair-walk/holding proof.

At fresh odd D, the initial multipliers give
  E lambda_tau = (1/2)h_S(1) = (3/2)h_F(1) = 1/2,
conditional on either initial parity. For even D, tau=1 and the
unconditioned mean is one. Jensen gives E lambda_tau^eta<=2^-eta for
odd D, but even D retains r_eta; no uniform endpoint contraction follows.

CRITICAL MEANS:
Pathwise b_tau=(1/2)sum_(j<tau)1_odd(j)lambda_(j+1,tau).
Tonelli evaluates future slope factors using h_S and h_F above.
The original fair gap walk from 1 killed at 0 has expected visits
exactly 2 to EVERY positive level k (finite Green 2(K-k)/K).
It has mean one inward active step at each level. Each is odd for S
and has remaining expected slope one. Consequently E b_S=infinity.

For F the first correction costs 1/6. At a visit to k, the conditional
wait bound E W<=v(k)+2 and predictable holds give expected cost at most
(1/4)3^-k(v(k)+4/3). Sum Green visits and use v(k)<2k:
  E b_F <=1/6+(1/2)sum_(k>=1)3^-k(2k+4/3)=5/4.
The pathwise inequality b_S<=D_next+b_F+lambda_tau D then forces
E D_next=infinity, without subtracting infinite expectations.
All these statements hold for every odd D and either initial parity.

For our even-source adjacent occupation, the first endpoint is S.
Fusion contributes D_next=0 and has b_S=lambda_tau+b_F, of finite
mean. Removing fused paths therefore leaves infinite means of both
D and the cumulative formal C=lambda+B already at return index one.
Every nonfused integer D>=1, and each Haar column integrates to one.
Hence K*_beta is NOT in Haar L1 for beta>=1. The earlier beta<1 range
is sharp for L1; optimality of the separate density exponent p is unknown.
These are distributional statements, not ordinary-orbit divergence.

IMPROVED FRACTIONAL BOUNDS:
For 0<eta<1 set a=(3/2)^eta/2, b=(1/2)^eta/2,
z=2^eta[1-sqrt(1-(3/4)^eta)] and z_F=3^-eta z.
Both roots lie in (0,1), with a/z+bz=1 and b/z_F+a z_F=1.
The stopped physical processes lambda_S^eta z^k and
lambda_F^eta z_F^k are nonnegative supermartingales: active factors
have mean one and holding factors have mean r_eta<1.
Bounded stopping and Fatou give future slope moments <=z^k, z_F^k.

Subadditivity of correction contributions and Green visits imply
  E b_S^eta <=2^-eta sum_(k>=1)[(v(k)+1)z^k+z^(k-1)].
The earlier valuation prefix mass sum_(k<=N)(v(k)+2)<=9N/2 and
Abel summation bound this by 9/[2(1-z)]. The root identity gives
1-r_eta=(1-z)[1-b(1+z)]<=1-z. The existing chord estimate
1-r_eta>=(1-eta)/16 for eta>=1/2 yields the UNIFORM fresh correction
budget b_eta=72/(1-eta). F follows from Jensen and its finite first
moment; even D is one step. For eta<1/2 the prior bounds remain valid.

With C_star=540*2^5180 and B_star=16(1+144 C_star), the existing
killed-return drift gives
  integral C^eta dnu, integral D^eta dnu <= B_star/(1-eta)^2.
For u>=4 this gives fresh tail <=144 log_2(u)/u and occupation tails
<=2 B_star(log_2 u)^2/u. Holder against the existing occupation-clock
tail improves weighted truncation to
  O_beta(H^(-(1-beta)/2)(1+log H)^(1+beta)), 0<=beta<1.
The established density range p<5/(4+beta) is unchanged.

VERIFICATION:
Record passed 2026-10-13T22:05:51.227230+00:00 (2026-10-14 local).
Seven fresh sequential builds took 4.753 seconds on pinned Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Nine audited roots
use standard axioms only, with no warnings, admissions, or native
computation. Twenty-two hashes record the new sources and artifacts;
the prior active-gap, correction, clock, and occupation records had
31, 21, 11, and 29 authenticated hashes respectively.

Exact independent checks passed:
- 2,142 finite biased hitting/exit values and 2,016 fair Green values,
  obtained by rational tridiagonal elimination on intervals through 64.
- 513 geometric fast-correction budgets and four fractional root
  enclosures, using integer-root intervals at precision 2^48.
- 419,328 actual fresh-return paths for D=1,3,5,9,31,63, clocks 8,12,16.
  Both initial parities are checked separately; unfinished paths remain
  in the bounded-stop identities and are NOT declared returned.
- 300,141 returned separation comparisons; 24,155 even-source fusion
  correction identities; 36 conditional bounded-stop identity groups;
  144 stopped fractional-potential pairs and 144 partial-moment groups.
- Six even-separation one-step laws; 98,208 actual tilted holding paths
  and 480 tail pairs at eight nonzero count gaps and six offsets.
No floating value decides a verification check. Finite partial means
do not prove the infinite means; those follow from the written argument.
No external analytic theorem or external compiled library is used.

NEXT GAP:
The slope contraction and below-one moments still do not control the
actual future gradients after a return. The infinite first separation
moment rules out extending that particular occupation budget to eta=1.
It does not refute the needed actual-gradient average. Correlations
between returned columns and future orbit losses, or a stronger direct
temporal argument, remain necessary. Q, escape exclusion, additional
cycle exclusion, and full Collatz are unresolved.

All work is terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. The user committed the preceding
milestones during the turn; their index and changes were preserved.
The unbounded Collatz goal remains active.

## 2026-10-14: summable cumulative slopes over all count returns

This goal turn is progress. A new WRITTEN argument proves, for adjacent
inputs under the coherent binary residue law,
  E sum_(1<=j<=N) Lambda_j <=44,
  E sum_(1<=j<=N) Lambda_j h_j <=70.
Here S_j is the jth positive equal-count return, Lambda_j=3^a_j/2^S_j
is the CUMULATIVE slope, h_j=S_j-S_(j-1), and N is first balanced
fusion. The terminal fusion and every one-step return are included.
This does not improve E N or the unweighted physical fusion clock.
Collatz, the actual-gradient estimate and Q remain unresolved.

Files:
  docs/RETURN-SLOPE-OCCUPATION.md
  lean/ReturnSlopeOccupation.lean
  verify_return_slope_occupation.py
  results/return-slope-occupation/verification.json
  results/return-slope-occupation/replay.json and eight build logs.
README and ATTEMPT link the result. Earlier authenticated notes were
not modified; the previous critical first-moment result remains valid.

RETURN-CONDITIONED TILT:
Fix one endpoint and tilt the entire binary law by its slope martingale.
At a fresh odd separation, its next parity is odd with probability 3/4.
That positive signed count excursion returns with probability 1/3;
the initially even case, probability 1/4, returns with probability one.
Total tilted return probability is therefore 1/2, at EVERY such prefix.

Condition on a return. The harmonic factor 3^-k changes the outward
3/4 active walk to inward 3/4. In the initially even case it already
has inward probability 3/4. Holds preserve k, so their return-probability
factor cancels under conditioning. Their tilted tail remains
min(1,2^v(k)(3/4)^h), where v(k)=v_2(3^k-1).
Hence expected wait, including the next active step, is <=3v(k)+4:
split the tail at 3v(k), using (27/32)^v<=1, then sum the geometric tail.

The inward walk's finite Green row from one on [0,K] is
4(3^(K-k)-1)/(3^K-1), increasing to 4*3^-k at each k>=1.
Using v(k)<2k and adding the initial departure yields
  E_tilt[tau | return] <=1+4 sum_(k>=1)3^-k(6k+4)=27.
Thus the ORIGINAL fresh E[lambda_tau*tau]<=27/2 for odd D, including
either conditional initial parity. For even D the unconditioned mean
is one because tau=1. All unbounded change-of-measure identities sum
nonnegative finite return cylinders, without a UI assumption.

GROUPED DRIFT AND ALL RETURNS:
At equal counts with D>0, exactly v_2(D) consecutive one-step returns
occur before D becomes odd. Common parity gives D'=D/2 or 3D/2 with
tilted probabilities 1/4,3/4, and removes one factor two each step.
There is no fusion during those positive-separation steps.

Set ell(D)=log_2(D+1). The polynomial identity
  (3D+2)^3(D+2)+18D^2+28D+11=27(D+1)^4
and 3^5<2^8 give E_tilt ell(D')<=ell(D)+1/5. Since v_2(D)<=ell(D),
the odd separation Dbar after that run satisfies
  E_tilt ell(Dbar)<=6 ell(D)/5.

New kernel arithmetic gives numerator(t,n)+2^t<=3^t, and at EQUAL
counts D_next+1<=(3/2)^tau(D+1). This is not a bound at intermediate
opposite-parity steps. The tilted returned clock bound therefore gives
  E_tilt[ell(D_next) 1_return | Dbar] <=ell(Dbar)/2+81/10.
Fusion contributes ell(0)=0.

Group each complete zero-gap run with the following odd-separation
excursion. Stop on fusion or a tilted excursion that never returns.
Let q_j be the mass starting a nonfused group and l_j its ell(D) mass.
Then q_0=1, l_0=ell(D_0),
  q_(j+1)<=q_j/2,  l_(j+1)<=3 l_j/5+81 q_j/10.
Finite telescoping yields
  sum q_j<=2, sum l_j<=(5/2)ell(D_0)+81/2.
Each group supplies expected return count <=ell(D)+1/2 and returned
excursion-length cost <=ell(D)+27/2, including a terminal fusion.
Tilted occupation equals original slope-weighted occupation by Tonelli.
This gives general bounds
  (5/2)log_2(D_0+1)+83/2,
  (5/2)log_2(D_0+1)+135/2,
and 44,70 for D_0=1. No use of the huge earlier E N constant is needed.

IMAGE CONSEQUENCE / PRECISE REMAINING OVERLAP:
For each even-source nonfused prefix, p_i=2^-t_i and
F_i=3^a_i 1_(z=x_i mod3^a_i). Its individual squared Haar norm is
  ||p_i F_i||_2^2=p_i^2 3^a_i=p_i Lambda_i.
Therefore sum_i ||p_i F_i||_2^2<=44 and the same sum with weight h_i
is <=70. Excursions of age greater than L contribute diagonal mass
at most 70/L. The age h_i is NOT the total source clock t_i.
This is NOT an L2 bound for K*_0=sum_i p_i F_i; cross terms are missing.
Actual prefixes (t,r,a,x)=(6,48,2,8) and (7,74,3,17) have disjoint
binary sources but nested ternary images and cross inner product
9/8192. The finite verifier includes all cross terms in truncated norms.

VERIFICATION:
Final record passed 2026-10-13T22:33:13.602180+00:00 (2026-10-14 local).
Eight fresh sequential builds took 3.246 seconds on pinned Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Thirteen audited
roots use only standard axioms; no warnings, admissions or native
computation. Twenty-three hashes record the new sources and artifacts.
The prior slope-tilt 22 hashes and occupation 29 hashes were authenticated.
All probability, logarithmic, infinite Green and occupation steps remain
written. No external analytic theorem or compiled library is used.

Exact finite checks passed:
2,016 inward Green values, 128 conditioned active-transition pairs,
512 partial clock budgets, 1,089 tail-shift comparisons, 1,025
logarithmic polynomial values, 516 rational grouped-drift budgets;
209,664 conditioned holding paths, 1,152 direction-ratio checks,
144 bounded wait means; 1,536 zero-gap paths and 132 logarithmic
drift checks; 174,578 affine correction cap pairs; 26,112 fresh
return paths, 17,486 equal-count separation caps and 24 conditional
clock budgets; 69,888 all-return paths through clocks 8,12,16,
93,309 completed return/age contributions and 18 grouped-drift pairs.
Three exact column-diagonal identity pairs, 1,597 ternary cylinder
energy terms, one independent whole-period energy calculation, and
three positive overlap witnesses passed. Logs use 32 positive atanh
terms plus an explicit remainder and outward rounding to precision
2^40. No floating-point value decides any check.

At H=16 the all-source partial slope sum, INCLUDING fusion, is
3396379515/4294967296; the age-weighted sum is 211291431/67108864.
The even-source NONFUSED diagonal squared mass is
461042127/4294967296, whereas the full truncated squared norm is
3820172355/4294967296. These are finite values, not limit estimates.
Unfinished paths remain unfinished.

EXPLORATION AND NEXT ACTION:
A separate floating exploratory census measured full future squared
gradients on the fixed return progression x=9q+8, 2^k<=q<2^(k+1),
3<=k<=13. Every tested trajectory reached the known cycle; its tail
was then summed geometrically. Mean gradient costs stayed around
6.5--9.3, while sixth norms grew roughly 18--40. These are exploratory
displays only, not exact certificates or a uniform norm claim; the
finite data neither prove nor refute the desired gradient estimate.

The new exact slope budget controls individual image columns but not
their overlap. A next useful target is the cross sum, or a direct
estimate retaining correlations of those columns with actual future
losses. Do not promote the diagonal bound to Haar L2, an ordinary
integer sampling theorem, or Q. Escape and other positive cycles
remain unexcluded.

All jobs are terminal. No agents, installations, credentials, staging,
commits, or other Git writes were used. Preserve the user's concurrent
index and source changes. The unbounded Collatz goal remains active.

## 2026-10-14: finite energy from nested binary source prefixes

This goal turn is progress. The new WRITTEN argument controls all
return-column cross terms from nested binary source prefixes, leaving
exactly the disjoint-source cross sum unresolved in the Haar L2
decomposition. It does not prove Q, bound actual forward gradients,
exclude escape or other positive cycles, or solve Collatz.

Files:
  docs/RETURN-ANCESTRAL-OVERLAP.md
  lean/ReturnAncestralOverlap.lean
  verify_return_ancestral_overlap.py
  results/return-ancestral-overlap/verification.json
  results/return-ancestral-overlap/replay.json and nine build logs.
README and ATTEMPT link the result. Existing authenticated research
notes were not changed. The previous slope and separation results
retain their stated scope.

SECOND CLOCK MOMENT:
Condition the endpoint slope tilt on a fresh odd-separation return.
The absolute active gap is the inward-3/4 walk. At each finite prefix
with gap k, W includes the next active step and is stochastically
bounded by 3v(k)+G, with v(k)=v_2(3^k-1)<2k, E G=4, E G^2=28.
Consequently E W<=6k+4 and E W^2<=36k^2+48k+28.

Set V(k)=6k^2+20k. Its inward-walk curvature is 6k+4; bounded
active-block stopping gives mean remaining physical clock <=V(k).
In the square expansion, bound the next-state potential by V(k+1)
before multiplying by W. This avoids assuming duration/direction
independence. The per-visit cost is
  c2(k)=72k^3+468k^2+616k+236.
The Green row 4*3^-k gives 4 sum_k 3^-k c2(k)=6316.
Add the initial departure and the earlier mean remaining clock 26:
  E_tilt[tau^2 | return]<=1+52+6316=6369.
Apply the expansion at finite active-block cutoffs first; the bounds
there are finite and monotone convergence supplies the full moment.

SLOPE-WEIGHTED LOGARITHMIC OCCUPATION:
For the grouped return chain, ell(D)=log_2(D+1), q is surviving
mass, l its ell mass, and m its ell^2 mass. Initially q=l=m=1.
The preceding result gives sum q<=2 and sum l<=43.

On a zero-gap common step, delta=ell(D')-ell(D) has mean <=1/5,
and mean square <=13/25 under tilted parity probabilities 1/4,3/4.
After v=v_2(D)<=ell(D) steps, with L=ell(D),
  E ell(Dbar)^2<=36L^2/25+12L/25.
The odd excursion returns with probability 1/2 and satisfies
ell(Dnext)<=ell(Dbar)+(3/5)tau. Its two clock moments yield
  m_next<=18m/25+492l/25+57321q/50.
Finite telescoping gives
  sum m<=(50+984*43+57321*2)/14=78502/7<11215.

The one-step returns in a group have total mean logarithmic cost
<=11L^2/10+L/10. Odd-return costs are the next group-start logs;
their sum is <=42, and fusion contributes zero. Therefore
  E_tilt sum_(all completed returns) ell(D_j)<=61914/5<12383.
Summing the finite return-cylinder likelihood ratios gives
  E_original sum_(j=1..N) Lambda_j ell(D_j)<=12383.
This is cumulative slope, and the law is the coherent binary residue
law, not a fixed finite interval of integers followed forever.

ORIGINAL-LAW RESTART AND NESTED OVERLAPS:
For arbitrary D, the earlier killed fourth-root drift gives a
return-count hitting tail <=D^(1/4)q^n/400 for entry into D<=400^4,
where q=399/400. The kernel inequality 2*399^400<400^400 and
n0=ceil(100log_2(D+1)) make the tail after n0 sum to at most one.
Uniform compact-state attempts cost at most C_star=540*2^5180.
Thus at every fresh finite prefix,
  E_original N<=C_star+100log_2(D+1)+2.

For a proper binary ancestor i of j, a_i<=a_j, and
  p_i p_j integral F_i F_j<=Lambda_i p_j.
The continuation prefix has conditional probability p_j/p_i.
Sum over future returns using the restart bound, then over ancestors
using the preceding total slope 44 and the new logarithmic bound:
  diagonal+2*nested_cross_sum<=88C_star+2476820.
Any two binary cylinders are nested or disjoint. Hence full K*_0
belongs to Haar L2 iff the remaining disjoint-source cross sum is
finite. Neither that finiteness nor its failure is proved here.
Full L2 is not asserted necessary for Collatz or sufficient by itself.

VERIFICATION:
Final record passed 2026-10-13T23:03:05.536117+00:00 (14 October local).
Nine fresh sequential builds took 3.517 seconds on pinned Lean 4.33.1
commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Twelve audited
arithmetic roots use standard axioms only; no warnings, admissions
or native computation. Twenty-seven source/artifact hashes were
recorded. Prior slope-occupation, occupation-density and correction
records authenticated 23, 29 and 21 hashes respectively.
The infinite probability, logarithm and energy steps remain written;
no external analytic theorem or compiled library is used.

Exact finite checks passed:
257 geometric second-moment identity pairs; 2,016 finite inward-clock
potential values and 63 killed second-moment budgets; 129 group-square
telescoping budgets; eight logarithmic restart tail comparisons through
D=2^128; 8,188 actual zero-gap paths and 44 square/total-log bounds;
17,408 fresh odd-separation paths with 16 partial second-clock bounds.
All-return trees use 69,888 paths through clocks 8,12,16, with 66,510
nonfused logarithmic costs and 18 capped group-square drift checks.
The overlap audit counts 3,778 binary ancestor pairs, of which 129
have compatible images, and 777 source-path image intersections.
Three exact path/prefix identifications and two independent all-pair
decompositions passed, with 840 positive finite pair products.
Logarithms use the authenticated rational enclosure at precision
2^40; no floating-point value decides a check. Unfinished paths remain
unfinished, and finite sums are not extrapolated.

At H=16, the even-source nonfused energy splits as
  diagonal = 461042127/4294967296,
  nested-source cross = 8819973/536870912,
  disjoint-source cross = 822142611/1073741824,
  full squared norm = 3820172355/4294967296.
The cross terms here already include their factor two.

LOCAL CLONE AND EXPLORATION:
The user-provided clone was reconfirmed clean at
a7275d5a73814d3d9a400c6fe6577de9542b03a3. The existing source review
is docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md. Its external stationary
majorant supplies uniform full-image Lp for p<2, but not the selected
return cross correlations. No new external Lean replay was performed.

A separate exact exploratory tree through H=22 gave full return
squared norm 8824364377245/4398046511104, about 2.00643.
For the FULL binary-image density b_t=L^t1, algebra gives
  ||b_(t+1)||_2^2=||b_t||_2^2+
    (1/2) integral b_t(y)b_t(3y+1) dmu_3.
Finite computations through 22 kept the correlation <=1; no uniform
correlation bound, linear energy theorem, or limiting growth law was
proved or adopted from those computations. The external Fourier
total-exponent selection still does not cover our paired return masks.

NEXT ACTION:
Study the disjoint-source cross sum or an estimate retaining its
correlation with actual forward losses. The nested-source estimate
does not bridge Haar integration to an infinite cutoff on actual
integer intervals. The actual-gradient criterion Q, escape and other
cycles remain unresolved.

All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. The user's existing
index and concurrent changes were preserved. The full goal stays active.

## 2026-10-14: lower-endpoint coefficient and grouped component energy

This goal turn is progress. The new WRITTEN argument controls the
complete fixed-clock, fixed-count image energies of smaller endpoints
at grouped returns. It includes internal cross terms from disjoint
binary sources. The endpoint convention and the selected return set
differ from K*_0; no full norm, Q or Collatz conclusion is established.

Files:
  docs/LOWER-RETURN-ENERGY.md
  lean/LowerReturnEnergy.lean
  verify_lower_return_energy.py
  results/lower-return-energy/verification.json
  results/lower-return-energy/replay.json and thirteen build logs.
README and ATTEMPT link the result. Earlier authenticated notes and
verification records were preserved.

FORMAL MINIMUM:
At an equal-count prefix, the two formal images of starting values
one and two are Lambda+B0 and 2Lambda+B1. Put
  P=min(Lambda+B0,2Lambda+B1).
Their separation is the actual positive integer D. Their ordering is
also the ordering of the actual endpoints: the latter add the same
Lambda*(n-1). The formal values are P and P+D, although they need not
be iterates of the ordinary integers one and two.

At a fresh equal-count return,
  Pnext=lambda*P+min(b_lower,lambda*D+b_higher).
The kernel lower_formal_identity checks
  2^t min(U^t(n),U^t(n+1))+3^a=3^a*n+lowerAugmented(t,n).
If endpoint n+e is the smaller one, its augmented coefficient is at
most lowerAugmented. For even sources, choosing e in {0,1} preserves
distinct source inputs and keeps them inside the same full period.

CLIPPED SLOW CORRECTION:
At odd separation, label the initially odd endpoint F and initially
even endpoint S. The existing conditional laws are
  E lambda=1/2, E b_F<=5/4, E b_S=infinity.
The new estimate is instead
  E min(b_S,lambda*D)<=12log_2(D+1).

Condition on the first parity and use the S endpoint slope tilt.
Its first multiplier is 1/2; subsequent parity bits are iid with
odd probability 3/4. S has inward active probability 3/4, so its
return has tilted probability one. Let
  R_h=(1/3) sum_(j=1..h) 1_odd(j) product_(i<j) m_i^-1,
where m_i=3^epsilon_i/2. Then b_S/lambda=2 R_(tau-1).
For 1/2<=eta<1, subadditivity gives
  E_tilt R_infty^eta <= 3^(1-eta)/(4(1-r_(1-eta))),
  r_u=(2^-u+(3/2)^u)/2.
The kernel root comparisons give r_(1/2)<31/32; convexity gives
1-r_u>=u/16 for 0<=u<=1/2.

The finite-cylinder change of measure, including the initial factor
one half, therefore gives
  E min(b_S,lambda D)
  <=(3/8)(2/3)^eta D^(1-eta)/(1-r_(1-eta))
  <=6 D^(1-eta)/(1-eta).
For odd D>=3 choose eta=1-1/log_2(D+1), obtaining 12log_2(D+1).
For D=1 the bound E lambda=1/2 is enough. No first moment of the
reciprocal-slope perpetuity or optional-stopping equality is assumed.

GROUPED MINIMUM BUDGET:
If the lower endpoint is F, bound the extra minimum by b_F.
If it is S, use b_F+min(b_S,lambda D). The two initial parity cases
have probability one half. Consequently
  E Pnext<=P/2+5/4+6ell(D), ell(D)=log_2(D+1), D odd.
For the first adjacent return a simpler selection of F gives the
sharper all-source bound E Pnext<=2 (conditional bounds 7/4 and 9/4).

Before an odd-separation excursion there are v=v_2(D) one-step
returns. Under the ORIGINAL fair law, E Pbar=P+v/4, while D has
constant mean and Jensen gives E ell(Dbar)<=ell(D). Since v<=ell(D),
  E P_group_next<=P/2+49ell(D)/8+5/4.
Kill the process at fusion. If q,l,p are group-start probability,
logarithmic separation mass and formal-minimum mass, then
  8p_next<=4p+49l+10q.
The old return-count and fourth-root budgets give
  sum q<=C_star, sum l<=328+2880C_star.
The latter follows from log_2(D+1)<=8D^(1/4), with harmless slack.
Finite telescoping yields
  sum p<=4020+(70565/2)C_star<4100+36000C_star.
Nonfused grouped returns are exactly the next group starts.
This does NOT sum the coefficient over every intervening one-step
return; that would require an additional mixed moment with v_2(D).

COMPONENT ENERGY:
For even-source, nonfused grouped-return prefixes, let y be the
smaller endpoint and form kappa_low_(t,a) from every prefix with that
fixed physical clock t and common count a. Distinct even sources give
distinct chosen endpoints r+e in [0,2^t). Existing quotient injection
and the new coefficient comparison yield
  ||kappa_low_(t,a)||_2^2
       <=2 sum_(i at t,a) 2^-t C_lower_i
       <=2 sum_(i at t,a) 2^-t P_i.
Hence sum_(t,a)||kappa_low_(t,a)||_2^2<=8200+72000C_star.
Unlike an individual-column diagonal bound, this includes every
disjoint-source collision INSIDE each component.

Products BETWEEN different components remain missing. The squared
pair gradient is unchanged by relabeling the smaller endpoint first,
but the one-endpoint sampling density is changed. No argument here
allows omitting the one-step returns from the whole energy transport.
Neither the original all-return K*_0 nor the sum of these new
components has a proved full L2 bound.

VERIFICATION:
Final record passed 2026-10-13T23:33:51.847484+00:00 (14 October local).
Thirteen fresh sequential builds took 4.972 seconds on pinned Lean
4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
Eleven roots use standard axioms only; no warnings, admissions or
native computation. Thirty-four hashes record sources and artifacts.
Prior affine-budget, slope-tilt and correction records authenticated
28, 22 and 21 hashes respectively.

Exact finite checks passed:
65,536 minimum-continuation inequalities; 2,860 geometric identities;
129 finite grouped telescoping checks; four fractional chord/clipping
comparisons; 4,352 independently enumerated tilted perpetuity words;
8,188 zero-gap paths and 44 mean/logarithmic drift groups.
Fresh return trees used 419,328 actual paths, retaining unresolved
ones, with 300,141 clipping/formal identities and 36 conditional
partial budgets. Grouped trees used 69,888 paths through 8,12,16,
93,309 equal-count formal identities, 10,068 even-source grouped
path visits and 18 capped grouped drift checks.
The image audit checked 1,501 quotient fibres and 88 whole component
energy bounds. Two independent full pair decompositions counted 799
positive column products. Powers use precision 2^48 and logarithms
2^40; no float decides a check. Infinite analysis remains written.

At H=16, the even-source lower grouped density has 1,486 columns in
58 clock/count components. Its exact finite values are
  minimum coefficient cost = 945335273/4294967296,
  selected endpoint augmented cost = 43888745/268435456,
  column diagonal = 243856827/4294967296,
  sum of entire component norms squared = 246148317/4294967296,
  internal disjoint-source cross energy = 1145745/2147483648,
  cross-component energy = 198196641/1073741824,
  full truncated squared norm = 1038934881/4294967296.
The finite cross terms include their factor two; no limit was inferred.

OTHER EXPLORATIONS / NEXT ACTION:
An exact backward correlation recursion for the full image law b_t
was explored using J_t(k,c)=integral b_t(x)b_t(3^k x+c).
For k>=1, c divisible by three gives 2^-t. Otherwise the next value
is one quarter times the (k,2c) and (k+1,3^k+2c) values; for c=2
mod3 add three quarters times (k-1,(2c-1)/3) and
(k,3^(k-1)+(2c-1)/3). At k=0 use translation symmetry and the
three mixed/even branches, plus the both-odd branch when 3 divides c.
The scout matched J_18(1,1)=381080939/536870912, about 0.709819.
It was deliberately stopped when its state count exceeded 3.5 million,
and is terminal. No all-depth correlation bound was proved or adopted.

Grouping the full image law by count rather than clock still suggests
Sigma_a=2rho^S_a, as recorded earlier. That lead alone does not control
selection by paired return histories. A proposed real-interval
disjointness shortcut is FALSE: first-odd words 1100 (t=4,a=2,N=5)
and 10001 (t=5,a=2,N=19) have the same image residue 2 mod9 and
nested real image intervals [5/16,14/16), [19/32,28/32).
Thus prefix-free words with fixed count do not suffice for that
disjointness assertion.

The next useful targets are the cross-component sum for these lower
images, a justified treatment of the intervening common-parity returns,
or a direct estimate of the actual gradient pairing. Do not promote
componentwise square summability to the squared norm of their sum.
Q, escape exclusion, additional cycles and full Collatz remain open.

All processes are terminal. No agents, installs, credentials, staging,
commits or other Git writes were used. Preserve the user's concurrent
index and changes. The unbounded Collatz goal remains active.

## 2026-10-14: every lower return, including the common-parity runs

The preceding goal turn was progress, as its current sources and
verification record confirm. This goal turn is also progress: the new
WRITTEN argument closes the omitted one-step-return part of the lower
coefficient budget. It does not settle the cross-component sum, Q,
escape, additional cycles, or Collatz. The full goal remains active.

Files:
  docs/ALL-RETURN-LOWER-ENERGY.md
  lean/AllReturnLowerEnergy.lean
  verify_all_return_lower_energy.py
  results/all-return-lower-energy/verification.json
  results/all-return-lower-energy/replay.json and sixteen build logs.
README and ATTEMPT link the result. Earlier authenticated research
notes and verification records were left unchanged.

FAST CORRECTION RESTART AND ENTROPY:
At any finite prefix with positive lead k of the initially odd endpoint
F, its remaining expected slope is 3^-k. The return-conditioned tilted
remaining clock is at most V(k)=6k^2+20k. The original fair active Green
row from k is 2 min(k,l), bounded by 2l. Summing the expected new
correction contributions gives a uniform restart mean at most two.
This is the NEW correction after the prefix, not the old correction
multiplied by its future slope.

For a fresh odd-separation excursion, write b_F=sum_j w_j, with
w_j=(1/2)1_(F odd at j) lambda_(j+1,tau). The exact geometric budgets
give E sum_j w_j (tau-j-1)<=315/4. For h>=1, split contributions at
physical clock h. Earlier contributions on tau>2h cost <=315/(4h);
later contributions cost <=2 Pr(tau>h)<=28/sqrt(h), allowing the
factor two for conditioning on the initial parity. Hence
  E[b_F 1_(tau>2h)]<=107/sqrt(h).
Dyadic summation gives E[b_F log_2 tau]<430. The finite entropy
inequality and log_2,+ w_j <=(3/5)(tau-j-1) give
  E[b_F log_2,+ b_F]<=480.
The initially even correction still has infinite mean. No moment
of b_F above power one is asserted.

MIXED DRIFT:
Let P be the smaller formal endpoint and L=log_2(D+1). At odd D,
P'=lambda P+c, with c<=b_F+Q and Q=min(b_S,lambda D).
The prior tilted clock moments give
  E[lambda L']<=L/2+81/10,
  E[lambda tau^2]<=6369/2.
The reciprocal perpetuity half-moment gives E[Q^2/lambda]<=10D^(3/2),
so Cauchy gives E[Q tau]<=179D^(3/4). The clipped mean costs 12L.

For b_F L', Young's entropy inequality uses
Y=1+lambda+b_F+b_S. The conditional quarter-moment of b_S is bounded
by NINE, explicitly allowing a factor two over the old unconditioned
9/2 bound; consequently E Y^(1/4)<13. The final constants are
  E[b_F log_2 Y]<=2024,
  E[b_F L']<=2034D^(3/4).
Together with the clipped cost (768+108)D^(3/4), these give
  E[P'L']<=PL/2+(81/10)P+3000D^(3/4).
Do not use the smaller pre-audit intermediate constants 1984/1994.
The final source and verification use 2024/2034.

ALL RETURNS:
At a group start, v=v_2(D)<=L. During its common-parity run,
  E Pbar=P+v/4,
  E[Pbar ell(Dbar)]<=(6/5)PL+(2/5)L^2,
  E Dbar^(3/4)<=D^(3/4).
The first part of the mixed bound uses slope tilting; the additive
correction part uses its exact mean and the deterministic log cap.
After the odd excursion,
  E[Pnext ell(Dnext)]<=(3/5)PL+(81/10)P+3030D^(3/4).
For killed group-start means m,p,z, previous results supply
  sum p<=B_star=4100+36000C_star,
  sum z<=Z_star=257+36864C_star.
Finite telescoping gives sum m<=5/2+(81/4)B_star+7575Z_star.

The entire completed common-parity block costs exactly
  E sum_(h=1..v) P_h=vP+v(v+1)/8<=PL+9D^(3/4).
Including the nonfused odd-excursion ends yields
  E sum_(1<=j<N) P_j
    <=4072431/2+280341576 C_star
    <A_star=2100000+281000000 C_star.
All nonfused returns are included. C_star remains 540*2^5180.

COMPONENT ENERGY / PRECISE REMAINDER:
The lower-image fixed-clock/fixed-count component squared norms sum
to at most 2 A_star. This includes internal disjoint-source collisions.
The earlier nested-source bound transfers because its pair estimate
only uses p_i p_j integral F_i F_j<=Lambda_i p_j, not the chosen
image residue. Thus within-component products plus proper nested-source
products have total at most 2 A_star+88 C_star+2476820.
The full lower-image L2 norm is finite iff the remaining DISJOINT-source
cross sum BETWEEN distinct clock/count components is finite. Neither
direction of its finiteness/divergence is established. Actual-gradient
pairing and infinite-cutoff ordinary-integer sampling remain separate
gaps. The original first-endpoint K*_0 is not relabeled silently.

VERIFICATION:
Final record passed 2026-10-14T10:35:33.279231+00:00.
Sixteen fresh sequential builds took 17.845 seconds on pinned Lean
4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Thirteen
audited roots use standard axioms only, without admissions, warnings
or native computation. Forty-one source/artifact hashes were recorded
and reauthenticated. Prior lower-energy, ancestral-overlap and slope-tilt
records authenticated 34, 27 and 22 hashes. The complete analytic
proof is written, not kernel formalized; no external analytic input
was adopted.

Exact finite checks passed:
129 correction/age series pairs; 10,416 finite fair Green row values;
129 mixed-drift telescoping identities; 18,423 actual common-parity
paths and 99 block mean/occupation/mixed bounds; 39,936 actual
positive-gap continuation paths and 39 conditional restart budgets.
Fresh trees used 279,552 paths, with 5,717 independent suffix-age and
entropy decompositions, 96 conditional clock-tail checks, 72 fresh
mixed-drift checks and 24 entropy/age/clipping budget groups.
All-return trees used 69,888 paths through clocks 8,12,16, with
93,309 formal-minimum identities, 14,164 selected path visits and
18 capped mixed-drift checks. Image checks covered 2,545 fibres,
88 entire component bounds, 81 compatible nested-source pairs,
1,113 positive independent pair products and two exact three-way
energy decompositions. Logarithms use precision 2^40 and powers
2^48 with outward rational bounds. No float decides a check.
Unfinished paths remain unfinished.

At H=16 there are 2,552 lower-return columns in 58 components,
including 1,066 common-parity columns omitted by the previous note.
Exact finite values:
  all-return minimum cost = 1889028813/4294967296,
  common-parity minimum cost = 235923385/1073741824,
  chosen endpoint augmented cost = 178610703/536870912,
  individual column diagonal = 461042127/4294967296,
  sum entire component norms squared = 465484653/4294967296,
  within-component cross energy = 2221263/2147483648,
  nested-source cross energy = 617805/536870912,
  disjoint-source cross-component energy = 368521587/1073741824,
  full truncated squared norm = 1944513441/4294967296.
Cross terms include their factor two. No limiting norm is inferred.

NEXT ACTION:
The common-parity omission is now closed for the lower coefficient
and component-energy argument. Study the remaining disjoint-source
cross-component sum, or retain its correlation with actual future
gradients in a direct transport estimate. Do not promote summability
of separate component squared norms to the squared norm of their sum.

All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. Preserve the user's
concurrent index and changes. The unbounded Collatz goal remains active.

## 2026-10-14: joint total clocks and full lower-image powers below 4/3

The preceding goal turn is classified as progress after authenticating
its 41 source/artifact hashes. This turn is progress: the new WRITTEN
argument handles all lower-image overlap terms in subcritical power
norms. It does not prove full L2, Q, escape exclusion, exclusion of
additional cycles, or Collatz. No live process needed resumption.

Files:
  docs/LOWER-RETURN-CLOCK-MOMENTS.md
  lean/LowerReturnClockMoments.lean
  verify_lower_return_clock_moments.py
  results/lower-return-clock-moments/verification.json
  results/lower-return-clock-moments/replay.json and seventeen build logs.
README and ATTEMPT link the new result and reproduction command.
The preceding authenticated proof sources and records are unchanged.

CLOCK/LOG OCCUPATION:
The existing measure on all nonfused returns has clock tail
O((1+log H)/sqrt(H)) and all separation powers below one. Holder
therefore gives finite integrals of (1+S)^u ell(D)^r for EVERY
u<1/2 and every finite r>=0. No clock/separation independence is used.
Group starts are a subset of these returns plus time zero.

ONE GROUP'S DURATION:
For 0<q<1/2 the previous conditional fast tail yields
  E[b_F tau^q]<=F_q
    =(5/4)2^q+107*2^(2q)/(1-2^(q-1/2)).
The old slope-clock and clipped-clock estimates yield
  E[P' tau^q]<=(27/2)P+F_q+179D^(3/4)
at any odd-separation departure. The group duration is G=v+tau,
v=v_2(D), with incoming L=ell(D). Combine subadditivity, the common
block means and the old grouped minimum drift to obtain
  E[Pnext G^q]<=PL/2+(27/2)P+608D^(3/4)+F_q.
The constant 608 is 392+10+27+179. Fusion may be included before
dropping its nonnegative cost in the killed next state.

TOTAL CLOCKS:
Put R_j=E[P_j^g (1+T_j)^q; group j exists], where T_j is the TOTAL
group-start clock, not its age. Then
  R_(j+1)<=R_j/2
    +(49/8) E[L_j(1+T_j)^q]+(5/4) E[(1+T_j)^q]
    +(1/2) E[P_j^g L_j]+(27/2) E[P_j^g]
    +608 E[(D_j^g)^(3/4)]+F_q Pr(group j exists).
Every forcing sum is finite by the clock/log occupation and the
preceding coefficient/mixed budgets. Finite telescoping proves
  sum_j E[P_j^g (1+T_j)^q]<infinity, q<1/2.
This statement includes the coefficient power ONE at group starts.

At a common-parity step h<=v, concavity gives
E P_h^theta<=P^theta+h^theta, for 0<theta<1. The complete block
cost is at most
  L P^theta(1+T)^q + P^theta L^(q+1)
    +L^(theta+1)(1+T)^q+L^(q+theta+1).
Holder bounds the P terms using the preceding first moment and
the finite clock/log occupations, e.g.
  integral P^theta(1+T)^q L^r
   <=(integral P(1+T)^q)^theta
     (integral (1+T)^q L^(r/(1-theta)))^(1-theta).
This proves the ALL-return joint moment
  E sum_(1<=j<N) P_j^theta(1+S_j)^q<infinity
  for theta<1, q<1/2.
Do NOT claim theta=1 with positive q for all returns; restoring
the common blocks at that endpoint still needs another mixed moment.

FULL LOWER-IMAGE DENSITIES:
For p=1+alpha<4/3, the selected-endpoint fibre bound gives
  ||kappa_low_(t,a)||_p^p<=p sum_(i at t,a) 2^-t P_i^alpha.
The new kernel inequalities P<=C_first and equality of the chosen
endpoint count allow the old binomial exceptional-count estimate:
atypical density power is O(t^(17alpha-8)), with summable Lp norms.

A dyadic typical-clock block has O(H^(3/2) sqrt(log H)) components.
Choose 3alpha/2<q<1/2 and use the new joint moment. The full block
power norm, keeping all cross terms, is
  O(H^(3alpha/2-q) (1+log H)^(alpha/2)).
Minkowski and monotone convergence give
  K_low,0 in Lp for 1<=p<4/3.
Separation-weight interpolation with any integrable K_low,gamma,
gamma<1, gives
  K_low,beta in Lp for beta<1, p<4/(3+beta).
For beta>=1 its L1 mass is infinite by the existing first separation
moment, independent of the chosen endpoint label.

The unweighted Lp tail has every rate
  ||K_low,0-K_low,0,H||_p=O(H^-delta),
  0<delta<(4-3p)/(2p), 1<p<4/3.
Finite integer power means retain factor 1+3^H/M. This does NOT
permit an infinite cutoff on a fixed integer interval. The new norm
is for the LOWER-endpoint density, not the original first-endpoint
K*. A suitable unweighted complementary gradient power above FOUR
could now suffice, but the actual-gradient and arithmetic sampling
estimates are still absent.

VERIFICATION:
Final record passed 2026-10-14T10:54:47.136056+00:00.
Seventeen fresh sequential builds took 12.679 seconds on pinned Lean
4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Seven new
arithmetic roots use standard axioms only; no warnings, admissions
or native computation. Forty-five hashes record the new proof and
finite artifacts. Prior all-return lower, slope-tilt, occupation and
affine-budget records authenticated 41, 22, 29 and 28 hashes.
All infinite probability and power norm arguments remain WRITTEN.
No external analytic theorem was adopted.

Exact finite checks passed:
2,795 rational exponent/rate windows; 384 dyadic fast-clock partial
sums; 195 total-clock telescoping identities; 256 exact binomial
exception bounds; 24 complete common-word mean checks and 288
common-block fractional clock bounds.
The actual trees use 69,888 paths through clocks 8,12,16, retaining
40,295 unfinished paths at the largest cap. They check 93,309
minimum/first-coefficient identities, 63 group-duration budgets and
54 total-clock drift bounds. Image checks cover 264 entire fractional
component bounds, six independently enumerated whole-period power
norms, twelve integer-interval comparisons, 27 joint moment sums and
18 full dyadic component-sum bounds. Power precision is 2^48,
logarithm precision 2^40, all with outward rational bounds. No float
decides a check.

At H=16 the same 2,552 even-source lower-return columns give the
following enclosures for the FULL pth power integral, with denominator
2^32:
  p=9/8:   [927061695, 927061696]/2^32,
  p=5/4:   [978772778, 978772779]/2^32,
  p=13/10: [1004891881,1004891882]/2^32.
These are finite quantities, not estimates of the infinite norm.

EXPLORATION / NEXT ACTION:
A temporary native C++ census at /tmp/collatz_lower_overlap.cpp matched
the independently checked H=16 squared-energy decomposition, and ran
through H=28. That deeper exploratory result has 8,237,115 columns,
full squared norm 110317192810534872/72057594037927936, and lower
coefficient cost 68353195546900554/72057594037927936. It was not
independently replayed at H=28 and is not a kernel or asymptotic result.
The finite growth establishes neither boundedness nor divergence.
All scout processes are terminal.

Use the improved full subcritical norm when investigating actual
gradient pairing, while retaining the lower-endpoint and finite-integer
sampling conventions. A full L2 bound, its remaining disjoint-source
cross-component sum, and both parts of Collatz remain open. No need
to repeat the preceding component-budget or common-parity arguments.

No agents, installations, credentials, staging, commits or other Git
writes were used. Preserve the user's concurrent index and changes.
The full unbounded Collatz goal remains active.


## 2026-10-14: known-basin nonfusion traces are infinite at one and two

The user resumed after an accidental interruption. No live process needed
resumption. The preceding lower-clock result and all 45 of its recorded
hashes were authenticated. This turn records an obstruction to one larger
integer majorant, not a solution of the actual-gradient or Collatz gaps.

Files:
  docs/KNOWN-BASIN-NONFUSION-TRACE.md
  lean/KnownBasinNonfusionTrace.lean
  verify_known_basin_nonfusion_trace.py
  results/known-basin-nonfusion-trace/verification.json
  results/known-basin-nonfusion-trace/replay.json and eight build logs.
README and ATTEMPT link the result and reproduction command. Earlier
verified research documents and their records were left unchanged.

KNOWN-BASIN DEFECTS:
Let B be the basin of one and D={n in B: the pair (2n,2n+1) never
balanced-fuses}. The second endpoint need not be known to converge.
The WRITTEN strengthening is sum_(n in D) 1/n=infinity. This cannot be
inferred just by restricting the old divergent defect sum to a subset.

For uniform x in [1,2), mark an odd binary edge whose parent n_k is in D.
Its probability is d_k/2, where d_k is the D fraction on [2^k,2^(k+1)).
On the set S of paths with finitely many marked edges, any later known-
basin visit starts an infinite balanced refinement chain. The new kernel
unmarked_known_chain verifies the finite implication without presupposing
the odd child's convergence. The old fixed-root polynomial bound makes
such infinite chains a null set. Hence the known-basin indicators tend
to zero almost everywhere on S, giving limsup q_k<=Pr(infinitely many
marked edges). External PLD at one gives limsup q_k>=delta>0. Borel--
Cantelli therefore gives sum d_k=infinity, and the band bound
sum_(n in D, 2^k<=n<2^(k+1))1/n>=d_k/2 gives the harmonic divergence.
No independence, full Collatz, natural density, or passage mixing is used.

INTEGER GREEN SUBSERIES:
Before first arrival at one, the path has distinct odd inputs. The local
WRITTEN reciprocal packing bound gives sum 1/u<=8192, so its first-hit
weight satisfies c0=exp(-8192/3)<=w_1(n)<=1 uniformly on B.
For n in D, source m=2n is convergent and never balanced-fuses with m+1.
Its first coefficient at one is w_1(n)/(2n). Subsequent visits occur
every two shortcut steps with coefficient ratio 3/4. Thus its COMPLETE
contribution at one is 2 w_1(n)/n, and at two it is 4 w_1(n)/n.
Nonnegative summation proves that both restricted subseries are infinite.
Consequently Z_H(1), Z_H(2) -> infinity, even on these convergent even
sources. These Z are ALL-clock nonfusion inverse traces, not K* or K_low.
The existing O_a(sqrt H) upper bound still holds, hence Z_H(a)/H->0 at
these targets. Discounts sigma>1/2 make their per-clock series finite;
no result is claimed for 0<sigma<=1/2 or for a lower growth rate in H.

Do not infer divergence of either selected equal-count return density
from divergence of a larger majorant. Finiteness of K*_0(n), K_low,0(n),
the required actual-gradient norms and sampling estimates, Q, escape,
other-cycle exclusion, and Collatz remain unresolved. The new result
rules out proving undiscounted finiteness by first dropping the equal-
count restriction and bounding all nonfused clocks at those targets.

VERIFICATION:
Passed 2026-10-14T11:23:30.762339+00:00. Eight fresh sequential builds
on pinned Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6
took 6.224 seconds. Eight new roots have standard axioms only, with no
warnings, admissions or native computation. The new record has 31 hashes.
Prior records authenticated 22 (dyadic defects), 15 (weighted dissipation),
14 (harmonic trace), 24 (annulus time), and 45 (lower clock moments).

Finite exact counts:
  208385 first-arrival links,
  131072 certified sources and first-hit weights,
  2054 independent first-arrival replays,
  5380352 independently followed paired steps,
  65535 grade-vs-paired-trajectory classifications,
  131070 full future source Green identities,
  16 harmonic band lower bounds and eight exact harmonic cross-checks,
  142799 inverse source/forward/mask checks through clock 32,
  18 exhaustive small inverse-layer cross-checks,
  129 independently summed finite geometric identities.
There are 26806 defective parents among 1<=n<65536, with both endpoints
in the known basin in this finite census. The complete target-one Green
contribution from these finite sources is about 8.673416892 (display only;
the record stores its exact dyadic fraction), and target two is twice
that. No asymptotic inference is based on these numbers.
Exact full inverse trace values at H=32:
  Z_32(1)=17448416503/1073741824,
  even-source Z_32(1)=13221224439/2147483648,
  Z_32(2)=16652118755/536870912,
  even-source Z_32(2)=53772161509/4294967296.
Harmonic enclosures use denominator 2^80. All verification decisions are
integer/rational; finite source traces use exact geometric cycle tails.

EXTERNAL REPLAY RETENTION ISSUE:
The old validate_external function in verify_dyadic_coalescence_defects.py
now fails because all 389 temporary external .lean sources and the root
lake-manifest.json are missing under /private/tmp/collatz-density-audit/
assembled. All 389 previously built .olean objects and all repository
build logs remain. The new verifier freshly authenticates those object
and log hashes, checks all 389 recorded source hashes against the retained
archive-authentication inventory, and checks its recorded manifest hash.
It explicitly records zero freshly authenticated live project sources,
389 missing source files, and no new external build. The historical
completed replay remains the external input; do not describe this turn
as a new external source replay. The old verifier was not modified, to
preserve its recorded provenance and dependent hashes. Reconstructing a
fresh external source tree would require the original authenticated
archives (the old temporary ZIP files are also absent).

NEXT:
Retain the equal-count selection in any integer-trace estimate, or keep
a time discount. The stronger lower-return Haar p<4/3 norm is unchanged.
The larger all-clock integer majorant cannot be made finite at 1 or 2.
The previous gradient scouts already ran through level 21; repeating them
would add no certificate. Actual forward gradients remain a separate
open target, and the new obstruction supplies no uniform power bound.

All jobs are terminal. No agents, installations, credentials, staging,
commits or other Git writes were used. Preserve concurrent user changes.


## 2026-10-14: conditional power obstruction from remaining arrival clocks

The preceding goal turn was progress: its known-basin nonfusion trace
result and all 31 hashes were authenticated. The goal is active again
in the goal tool. This turn is progress: a written conditional theorem
rules out a broad uniform-gradient ingredient under full convergence.
It does NOT prove either full Collatz or a counterexample. All earlier
selected-density theorems and their scopes are unchanged.

Files:
  docs/CONDITIONAL-GRADIENT-POWER-OBSTRUCTION.md
  lean/GradientClockObstruction.lean
  verify_gradient_clock_obstruction.py
  results/gradient-clock-obstruction/verification.json
  results/gradient-clock-obstruction/replay.json and seven build logs.
README and ATTEMPT link the result and reproduction command. Prior
verified source documents and records were not rewritten.

CONDITIONAL THEOREM:
Assume EVERY positive integer reaches one. At M=2^k, M<=n<2M, define
  G_k(n)=sum_(s>=0)[M f_(k+s)(n)-3M f_(k+s)(3n+2)]^2.
This is the unhalved cell energy from the annulus-time note. For every
p>1 there are c_p>0 and K0 such that
  sum_(k<K) mean G_k^p >= c_p K^((p+1)/2), K>=K0.
Therefore sup_k mean G_k^p=infinity. The maximum Lp norm through K
is at least c_p^(1/p) K^((p-1)/(2p)); this is not an every-level rate.
The analytic theorem is WRITTEN, and its universal-convergence premise
is NOT established by the finite checks. No external density theorem
is used in the new proof.

ARRIVAL CLOCKS:
Let tau(n) be the first shortcut arrival at one and T_k(n)=tau(n)-k.
On a complete binary source band, tau>=k and U^k(n)>=3^(a_k(n))>=2^a,
so tau(n)>=k+a_k(n). The exact band mean of a_k is k/2. Consequently
F_k=mean T_k>=k/2. These lower-clock and parity-mass facts have new
kernel proofs; they are not an assumed stopping-time asymptotic law.

Even children preserve T. For the odd child put
  Delta_k(n)=tau(2n+1)-tau(n)-1.
The exact mean identity is
  2 F_K=sum_(k<K) mean Delta_k, F_0=0.
Individual Delta may have either sign. If (2n,2n+1) has balanced-fused
by physical clock k+1, neither first arrival can precede that clock,
so their first-arrival times agree and Delta=0. Their normalized weight
profiles also agree for every future offset, so G=0 on that same set.

The even residue mask on this actual band has fraction eta_k bounded
by 28 C_star/sqrt(k+1), with C_star=540*2^5180 from the improved local
mean cycle budget. Hence Q_K=sum eta_k<=A sqrt K, A=56 C_star.
No fair bits are assumed beyond the source sampling depth k+1.
Holder on the disjoint union of these finite supports immediately gives
  sum_(k<K) mean |Delta_k|^p >= (2F_K)^p/Q_K^(p-1)
                              >=A^(1-p)K^((p+1)/2).
This conditional clock-increment result does not require packing.

FROM CLOCKS TO ACTUAL PROFILES:
The local written simple-path packing bound gives a uniform first-hit
weight floor c=exp(-8192/3). Normalized child profiles are at least c/2
through their remaining first-arrival clock, then decay by 3/4 every
two steps on the known cycle. Choose J with (3/4)^J<=c/4 and set
R=2J, C=16/c^2. Between the earlier arrival plus R and the later arrival
there are (|Delta|-R)_+ clocks with squared gap at least c^2/16. Thus
  |Delta_k| <= R 1_(nonfused prefix) + C G_k.
Together with the mean identity this gives
  K <= R Q_K + C sum_(k<K) mean G_k.
For K>=4R^2A^2, the last sum is at least K/(2C). Holder on the support
of G gives the stated theorem with c_p=(2C)^(-p) A^(1-p).

This applies also to the BROADER adjacent field on a whole dyadic band:
  mathcalG_j(m)=sum_(t>=j)[2^j(f_t(m)-f_t(m+1))]^2.
Exactly mathcalG_(k+1)(2n)=G_k(n); its full mean is at least half the
even-source mean. Thus uniform full-interval accumulated-gradient powers
above one are incompatible with universal convergence. This does not
prove an unconditional divergence result or produce a counterexample.
It does not decide a norm on a particular returned progression, a
pairing weighted by the actual return density, or reversed negative
terms alone. Uniform first moments T_k=mean G_k/2 and bounded fixed-
offset E_s remain possible. Q and both parts of Collatz remain open.

FINITE VERIFICATION:
Final record passed 2026-10-14T11:56:15.261510+00:00. Seven fresh sequential builds
took 3.881 seconds on Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Twelve new roots use standard
axioms only, without warnings, admissions, or native computation.
The record has 30 hashes. Prior hash counts: finite-path-packing 12, count-return-clock 11, return-correction-moments 21, annulus-time-budgets 24, known-basin-nonfusion-trace 31.

Exact finite work certifies first arrivals for 65536 sources, using
104145 cached trajectory links and 2053 independent full replays. All
these finite first-hit weights are at least 3/4; the observed minimum
is exactly 1840049047529878113/2305843009213693952. This finite floor
is NOT substituted for c in the infinite theorem.

Checks include 65535 remaining-clock lower bounds, 32767 actual-band
versus even-residue masks, 17392 fused edges with equal arrival clocks,
16 exact parity/arrival means, and 15 mean-clock telescoping identities.
For 553 selected cells, the full future energy was recomputed with
23996 pre-tail terms and 2212 exact cycle-tail ratio checks. Their
arrival windows contain 7192 independently evaluated profile terms.
With the finite floor 3/4, the exact bound checked is
  G_k >= (9/256)(|Delta_k|-12)_+,
  |Delta_k| <=12 1_E+(256/9)G_k.

Previously certified ALL-cell energy moments on levels 0..14 were
reauthenticated and reused, not recomputed for every cell. Seventy-five
finite clock-increment Holder bounds and 75 finite energy-moment lower
bounds passed for p=1,2,4,8,12. Seven of the finite energy lower bounds'
clock margins are nonzero (K=9..15). At K=15:
  F_K=480101/8192,
  Q_K=145077/16384,
  2F_K-12Q_K=22435/2048,
  sum mean |Delta_k|^2=19991031/2048,
  its clock-derived lower bound=230496970201/148558848.
All decisions use integer/rational arithmetic. Neither this finite
census nor its finite 3/4 weight floor establishes universal convergence.

EXPLORATION AND NEXT DIRECTION:
A terminal in-memory inverse-tree scout retained equal-count selection
at target one through clock 38. Its displayed truncated values were
about 0.166187715 for the first endpoint and 1.194213709 for the lower
endpoint. No new independent certificate or asymptotic inference was
made from these exploratory values. The selected integer traces remain
open; this scout does not show convergence or divergence of their sums.

The actual-profile clock identity produced a stronger route distinction:
when using lower-image Lp bounds, do not assume a uniform broad full-
interval accumulated-gradient power above one as an unconditional
lemma compatible with full Collatz. Keep return restrictions, signs,
clock aggregation or correlations. The time-summed reversed negative
budget R_k, its weaker local Cesaro criterion Q, and density-adapted
pairings remain possible targets. The conditional theorem does not
control those quantities or rule them out.

The earlier external source-retention issue is unchanged. This new
verifier uses no external validation routine or external analytic theorem;
its first-arrival memoization helper is a finite local computation only.
All jobs are terminal. No agents, installations, credentials, staging,
commits or other Git writes were used. Preserve concurrent user changes.
The full Collatz goal remains active and unresolved.

## 2026-10-14: signed arrival windows isolate upward growth and reversed costs

The user resumed after an accidental interruption. The last completed
milestone was the conditional gradient-power obstruction; its 30 hashes
were reauthenticated. The interrupted exploration had not produced a new
artifact or left a live job. This turn is progress: the written argument
now locates the forced power growth on the upward side and decomposes
the distinct reversed-negative cost. Collatz remains unresolved and the
goal stays active. No general reverse budget has been proved.

Files:
  docs/SIGNED-ARRIVAL-WINDOWS.md
  lean/SignedArrivalWindows.lean
  verify_signed_arrival_windows.py
  results/signed-arrival-windows/verification.json
  results/signed-arrival-windows/replay.json and eight build logs.
README and ATTEMPT link the result and reproduction command. Previously
verified source documents and verification records were not changed.

ORIENTED WINDOWS:
At M=2^k and M<=n<2M, set q=3n+2 and keep
  A_s=M f_(k+s)(n), B_s=3M f_(k+s)(q).
Let R_s flag a historical count reversal a_t(n)>1+a_t(q). Define
  G_k^+=sum_s(B_s-A_s)_+^2,
  G_k^-=sum_s(A_s-B_s)_+^2,
  J_k=sum_s R_s A_s(A_s-B_s)_+.
The previous G_k=G_k^++G_k^- and mathcal R_k=mean J_k/2.
For a pair known to reach one, alpha=tau(n)-k, beta=tau(q)-k,
Delta=beta-alpha=tau(2n+1)-tau(n)-1, and D_+=Delta_+, D_-=(-Delta)_+.
Both clocks are nonnegative. Off the same prefix nonfusion set E_k,
all these costs and delays vanish.

With c=exp(-8192/3) from local written simple-path packing, choose
J so (3/4)^J<=c/4 and put R=2J. In the window from the early arrival
plus R to the late arrival the later profile is >=c/2 and the earlier
one <=c/4. When the parent is later, its endpoint X>=2 while the
child endpoint Y is 1 or 2. If a<=b+1, then A/B=3^(a-b-1)Y/X<=1,
contradicting the downward gap. The CURRENT count order is reversed;
therefore so is the historical flag, without an extra hypothesis.
The written window bounds are
  G_k^+ >= c^2/16 (D_+-R)_+,
  G_k^- >= c^2/16 (D_--R)_+,
  J_k >= c^2/8 (D_--R)_+,
  D_+ <= R 1_E +16/c^2 G_k^+,
  D_- <= R 1_E +8/c^2 J_k.
These are lower drift bounds from delays, NOT upper drift estimates.

CONDITIONAL UPWARD POWER GROWTH:
Assume EVERY positive integer reaches one. The exact clock identity is
  sum_(k<K) mean D_+ = 2F_K+sum_(k<K) mean D_- >= K.
The old nonfusion mass Q_K<=A sqrt K, A=56 C_star, is unchanged.
With C=16/c^2 and K>=4R^2A^2, the upward window alone gives
  sum_(k<K) mean G_k^+ >= K/(2C),
  sum_(k<K) mean (G_k^+)^p
    >=(2C)^(-p)A^(1-p)K^((p+1)/2), p>1.
Thus the preceding conditional obstruction is already carried by the
UPWARD accumulated squared gradients. The signed clock identity supplies
no analogous lower growth for D_-. No boundedness or unboundedness of
the downward powers or reversed budgets on all bands is established.
The universal hypothesis is never inferred from the finite replay.

WHAT THE ARRIVAL CLOCKS MISS:
Let H_k be the reversed-negative cost before min(alpha,beta). The
reversed cost before the parent's arrival consists of H_k followed
by at most D_- terms, each <=1. From the parent's first arrival onward,
the exact known-cycle square sum is 25 A_alpha^2/7<=25/7. Therefore
  J_k <= H_k+D_-+(25/7)1_E,
  H_k+D_- <= (1+8/c^2)J_k+R 1_E.
On convergent bands, uniform first-moment bounds for J and H+D_- are
equivalent up to fixed constants. Neither is proved on all bands;
these arrival clocks are not defined for an unknown nonconvergent pair.

The exact witness n=823, k=9, q=2471 has tau(n)=tau(q)=86 and
  D_+=D_-=0,
  J_9(823)=H_9(823)=6289513358589/491370708992000>0.
Hence J<=C D_- is false for every multiplier C. This does not refute
a charge with an additive constant or an averaged bound. The full
finite census finds 321 equal-arrival cells with positive reversed
cost in levels 0..14, all at levels 9 and above.

VERIFICATION:
Final record passed 2026-10-14T12:34:25.994528+00:00. Eight sequential
fresh builds took 3.748 seconds on Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eleven new roots have only
standard axioms, with no admissions, warnings or native computation.
They check odd arrival transfer, cycle continuation, prearrival
endpoint size, current reversal, window arithmetic, partition,
denominator-cleared negative product and positive clock accounting.
The real profiles, packing, geometric limits, Holder and conditional
infinite power theorem remain written.

The record has 34 hashes. Revalidated prior hash counts: gradient-clock
obstruction 30, annulus-time-budgets 24, finite-path-packing 12,
count-return-clock 11, return-correction-moments 21. No external
analytic theorem, validation routine or external rebuild is used.

Exact finite checks covered all 32767 parent pairs in levels 0..14,
using the 65536-source first-arrival memo (104145 links, 2053 independent
full replays). Every pair was followed independently, including both
actual first arrivals and the known cycle. The pair first-hit floors
were checked 65534 times, all >=3/4. This is a finite floor only.
The finite constants are R=12, G^+>=9/256(D_+-12)_+,
G^->=9/256(D_--12)_+, J>=9/128(D_--12)_+.

The replay evaluated 2139918 pre-tail signed cost terms, certified
393204 cycle-tail ratios, checked 163835 pointwise window bounds and
32767 prearrival partitions/tail bounds. It checked 289075 upward
window terms and 99796 negative window terms with CURRENT count
reversal. Seven independent exact rational whole-cost sums agree with
the older complete_pair implementation. Fifteen clock-band comparisons
and 30 old annulus enclosure comparisons passed. All decisions use
integers or fractions, including 75 upward Holder bounds; nine prefixes
have a nonzero positive-clock margin.

At K=15 the exact cumulative statistics are
  Q_K=145077/16384,
  sum mean D_+=40787/256,
  sum mean D_-=172491/4096,
  sum mean D_+-12Q_K=217361/4096.
The resulting lower bound on sum mean (G_k^+)^2 is
1275636716667/3245317554176. These are finite checks only.
For orientation, at level 14 the DISPLAY means are approximately
G^+=4.622117, G^-=1.671791, J=1.926736, H=0.053462,
the middle late-parent cost=1.700410 and the post-parent-arrival
cost=0.172865. The mean negative advance is exactly 18955/4096.
No asymptotic inference is made from these displays.

NEXT DIRECTION:
The conditional obstruction now explicitly concerns the upward sign.
A useful reversed estimate must bound the pre-arrival overlap cost
and negative arrival advances together, or bypass arrival clocks and
control the actual reversed integrand. A negative-delay bound alone
does not pay for the equal-arrival witness. Conversely, the large
upward power theorem does not rule out the desired reversed bound.
The small finite H means do not prove a uniform H estimate. Avoid
assuming new fair bits after the finite source sampling depth or
transferring Haar image bounds to infinite-cutoff integer samples.

A brief targeted web search for adjacent stopping-time correlation
results supplied no lemma adopted in this turn. It is not an exhaustive
literature audit or a claim that no relevant theorem exists.
All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. Preserve concurrent
user changes. Q, escape and additional cycles remain open.

## 2026-10-14: pre-arrival costs transfer to lifetime weight deficits

The previous goal turn was progress: all 34 signed-arrival hashes were
reauthenticated. This turn is progress, with a new written transfer,
an infinite pointwise charge obstruction before either arrival, and a
larger exact convergent witness. The full goal remains active. None of
the required uniform or averaged estimates, full convergence, or a
positive-integer counterexample has been established.

Files:
  docs/PREARRIVAL-DEFICIT-TRANSFER.md
  lean/PrearrivalDeficitTransfer.lean
  verify_prearrival_deficit_transfer.py
  results/prearrival-deficit-transfer/verification.json
  results/prearrival-deficit-transfer/replay.json and eleven build logs.
README and ATTEMPT link the result and reproduction command. Previously
verified source notes and records were not edited.

SINGLE-TRAJECTORY QUANTITY:
On the basin B of one, define
  D(v)=sum_(h<tau(v))(1-W_h(v)).
The finite sum is defined using the FIRST arrival, not a later visit.
Exact weight factorization gives
  D(1)=0, D(2v)=D(v),
  (3v+1)D(v)=3vD(Uv)+tau(Uv) for odd v>1.
Thus tau(v)<=(3v+1)D(v)+1 on odd convergent v. Removing initial
halvings, using h+1<=2^h, yields on every convergent v
  tau(v)/v <=(10/3)D(v)+1/2.
The same inequality holds with a finite clock L and D_L(v) whenever
the orbit has not reached one before L. After the first odd input o>1,
each later weight has deficit at least 1/(3o+1). These sum and clock
arguments are WRITTEN, with exact finite checks; they are not complete
Lean formalizations of real weighted sums.

KNOWN-BASIN PRE-ARRIVAL TRANSFER:
For n>=1 with q=3n+2 in B, let k=floor(log2 n), M=2^k, and use
physical clocks A_t=M f_t(n), B_t=3M f_t(q). Stop at the first clock
T where EITHER endpoint is one. This is finite because q is known
to converge, without assuming convergence of n. Define H(n) as the
historically reversed A(A-B)_+ sum for k<=t<T. When both starts
converge, this is exactly the preceding H_k(n).

Since A_t<=A_0, B_t=B_0 W_t(q), A_0-B_0=2M/(nq), and A_0,B_0<=1,
  H(n)<=D(q)+2tau(q)/q <=(23/3)D(q)+1.

For the converse take convergent v>1, v=1 mod 9, and j>=1:
  n_j=8(64^j v-1)/9, q_j=3n_j+2,
  a=3j-1, T_j=6j+3, X_j=3^a v+1.
The new kernel family theorem proves at clock T_j:
  parent endpoint X_j and count a+2,
  q_j endpoint v and count 1.
Choose ell>=3 with 2^ell<=8v/9<2^(ell+1). The source band is exactly
k_j=6j+ell. Set h0=ell-3 and b_v=9*2^ell/(8v), so 1/2<b_v<=1.
When a>=tau(v), the parent cannot reach one before the child, and
the current count order is reversed through the needed window.
At T_j+h its profiles are exactly
  A=b_v (X_j-1)/X_j W_h(X_j), B=b_v W_h(v).
Elementary retention, WITHOUT packing, gives
  H(n_j) -> b_v^2 sum_(h0<=h<tau(v))(1-W_h(v)),
  0<=limit-H(n_j)<=2 b_v^2 (2^tau(v)+2tau(v))/(3X_j).
The omitted prefix has deficit <1/27 by
1-W_h(v)<=(2^h-1)/(3v) and 2^h0<=v/9.
Every positive unit modulo three can be doubled at most five times
to become one modulo nine; D and convergence are preserved.

Writing D_star=sup_(v in B,3 does not divide v) D(v), and
H_star=sup_(n>=1,3n+2 in B) H(n), the written quantitative result is
  (1/4)(D_star-1/27)_+ <= H_star <=(23/3)D_star+1.
This includes infinite suprema. A bound H_star<=B would force
  tau(v)<=[(40/3)B+101/162]v
on the convergent unit basin. Neither supremum's finiteness or infinitude
is proved. This is a pointwise reduction, not an averaged bound.

UNRESTRICTED FINITE-PREFIX VERSION:
Define D_hat over ALL positive units and finite prefixes with no one
before their ending clock. Define H_hat over ALL pairs (n,3n+2) and
finite windows ending before or at the first arrival of either,
without assuming that q converges. The same two inequalities hold
with hats: use the finite-prefix clock bound for the upper estimate,
and replace tau(v) by the finite ending clock in the clone construction.
If a start never reaches one, its first odd input exceeds one, causing
a fixed positive permanent deficit, so its prefix deficits diverge.
Every positive start reaches a unit modulo three (new kernel proof).
Consequently the written criterion is
  H_hat finite iff [full Collatz AND D_star finite].
This does NOT prove full Collatz or bounded D_star, and it is NOT
claimed to be equivalent to Collatz alone. Do not substitute the
restricted H_star for the stronger unrestricted H_hat in this claim.

NO CHARGE TO THE PARENT'S LOSSES DURING THE PRE-ARRIVAL WINDOW:
Use v=10, whose path is 10,5,8,4,2,1 and D(10)=3/16. Then
ell=3, k_j=T_j, b_v=9/10 and H(n_j)->243/1600.
For EVERY j>=2, put R=3^(3j-1), X=10R+1. Kernel retention proves
A_(k_j+h)>=7/8 for h<=4. At h=2,3,4, the child profile is 27/32,
and current count reversal holds, so H(n_j)>=21/256.
The parent loss during the complete interval through the child's
first arrival at k_j+5 satisfies
  L_j=3(A_k-A_(k+5))+2(Z_k-Z_(k+5))<=93/X ->0.
Thus H/L >=7X/7936 ->infinity. No fixed multiplier can charge the
pre-arrival cost to parent losses DURING THAT INTERVAL. This is an
unconditional finite-prefix family argument; no universal convergence
of its parents is used or claimed.

COMPLETE-FUTURE MULTIPLIER ONE ALSO FAILS:
Take v=597484, j=64, n=8(597484*64^64-1)/9 and k=403.
Exact replay certifies n has 404 bits, tau(n)=1863, tau(3n+2)=538,
and
  H(n)>3A_403+2Z_403+1/200.
Both sources actually reach one. Therefore the parent cap is its
complete future weighted-loss budget, and multiplier one fails even
with all future losses. No failure for arbitrary complete-future
multipliers, and no failure of an averaged charge, is proved.
Displays only: H~4.940950760188, parent cap~4.935897865047.
The exact H numerator/denominator have 48027/48025 bits. The replay
stores exact-decision enclosures and hashes of their unsigned big-endian
integers, not thousands of decimal digits. A certified gap lower bound is
200165798662695239002407819/39614081257132168796771975168 >1/200.

VERIFICATION:
Final record passed 2026-10-14T13:12:22.152977+00:00. Eleven fresh
sequential builds took 3.804 seconds on Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Thirteen new roots have
standard axioms only, no admissions, warnings or native computation.
They cover the parametric affine lift and clone, seed and shell,
current reversal, no early arrival from a large endpoint, unit residue
transfer, the ten suffix and retention bound, halving clock comparison,
and eventual entry into a unit class. The infinite analytic statements
and real weighted recurrences remain written.
The record has 35 hashes. It reauthenticates the 34 signed-window and
14 reversal-persistence hashes. There is no external analytic input,
new external source audit, packing premise or universal convergence
hypothesis in the transfer or explicit family obstruction.

Finite checks: 16384 lifetime-clock inequalities, 43249 finite-prefix
clock inequalities, 27239 exact memoized recurrence links, 8192
doubling identities, 8191 odd deficit/clock identities, 2731 unit
doubling transfers and 1038 independent direct deficit sums. There
were 1113 independent first-arrival replays totalling 90684 steps.
All 4095 parents below 4096 pass the one-trajectory upper bound;
12 pre-arrival band means agree with authenticated signed-window
enclosures. The replay evaluates 148020 exact pre-arrival cost terms.

Twenty-five clone cases on targets 10,19,28,37,55,82,109,597484,
4086964 passed, with sources up to 772 bits. For every finite case
both first arrivals were also independently certified, though the
written theorem does not require the parent's future convergence.
There are 25 endpoint identities, 1025 reversed window terms,
25 whole-window error bounds, 1050 finite-prefix error bounds,
nine target-ten loss comparisons and the one complete-budget witness.
All verification decisions use integers or fractions.

EXPLORATION AND NEXT DIRECTION:
A terminal floating C++ scout in /tmp/collatz-prearrival-scout.cpp
scanned levels 0..23. Its level-23 DISPLAY mean H was about 0.074115,
maximum about 4.921805, and largest parent-cap ratio about 0.992930.
This suggested a multiplier-one cap, but the exact affine witness
above disproves it. Those floating maxima are not certificates.
A terminal floating deficit scout below 2^20 found a unit candidate
at 1021741 with D about 5.081642; its individual value, and the target
597484, were subsequently checked exactly, not the full maximum claim.

The new single-orbit functional may be useful, but a pointwise bound
already entails global clock control on the known basin. Do not assume
it from small finite values. For the original escape route, an averaged
pre-arrival estimate can be substantially weaker; negative arrival
advances and drift after a known child has arrived remain separate.
The existing all-time reversed charge is not repaired by restricting
its parent losses to the interval before either arrival. All suprema
and conditional criteria above retain their explicit domains.

All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. Preserve concurrent
user changes. The Collatz goal remains active and unresolved.


## 2026-10-14: deficit limiting law and tightness on actual source bands

The user resumed after an accidental interruption. The previous completed
turn was progress: the pre-arrival/lifetime-deficit transfer and the
404-bit counterexample passed. The interrupted follow-up had inspected
average deficits and the earlier first-passage proof without new edits.
This turn completes a new positive WRITTEN result. The full Collatz goal
remains active and unresolved; no genuine blocker was encountered.

New files:
- docs/DEFICIT-LIMIT-LAW.md
- lean/DeficitLimitLaw.lean
- verify_deficit_limit_law.py
- results/deficit-limit-law/{verification.json,replay.json,DeficitLimitLaw.log}
README and ATTEMPT describe the result and its limitations.

FUNCTIONAL AND EXACT TRANSPORT:
Let m(n) be the global shortcut minimum, T(n) its first attainment,
D_m(n)=sum_(h<T(n))(1-W_h(n)), P(n)=W_T(n). Well-ordering makes T(n)
finite for every positive n; it does not identify m(n) with one. This
prefix is simple. The known packing input gives P>=exp(-8192/3).
For a source in the basin of one, D_m is the preceding lifetime D.
Initial halvings preserve (m,D_m,P).

At a first odd landing b below x, at shortcut clock i, put p=W_i and
A=sum_(h<i)(1-W_h). All preceding odd inputs exceed x and all preceding
states exceed b; some preceding EVEN states may already be below x.
Then
  T(n)=i+T(b),
  D_m(n)=A+p D_m(b)+(1-p)T(b)
        =D_m(b)+A+(1-p)(T(b)-D_m(b)).
If the prefix weights are >=1-e, this lies between D_m(b) and
D_m(b)+e T(n). For two sources with the same landing,
  |D_m(n)-D_m(n')|<=e max(T(n),T(n')),
  |P(n)-P(n')|<=e.
Packing only the odd inputs supplies
  e(x)=min(1,(8192/3)x^(-1/20)).
The finite rational algebra is kernel checked; its application to real
packing bounds remains written.

FINITE CHAINS AND LIMIT LAW:
Use alpha=1001/1000 and the LOCAL WRITTEN natural first-passage input.
For source scales in [x^alpha,x^(alpha^2)], a maximal landing coupling,
lifted to source marginals, has common finite landing and both clocks
<=L log x outside C(log x)^(-c). The old ordinary-clock L is also an
upper bound for shortcut time. No clock/landing independence is used.
Glue finite descending scale couplings Y -> Z -> B. Full links reduce
log scale by alpha; at most two partial links occur. Total failure is
<=C_1(log B)^(-c). On the good event all minimum labels agree and
  T(n_u)<=T_B+C_2 log u,
where T_B is the finite maximum minimum-attainment clock of odd starts
in [B,2B). It may be unknown and has no effective estimate here.
Summing weight-loss errors above Z, with gamma=1/(40 alpha^2), yields
  |D_m(n_Y)-D_m(n_Z)|+|P(n_Y)-P(n_Z)|
    <=C_5(T_B+1) Z^(-gamma)
outside the same failure event. FIRST fix B for the desired failure
probability, THEN send Z to infinity. Do NOT claim that
(T_B+1)B^(-gamma) tends to zero.

The common base gives tightness, and the two-scale estimate gives a
Cauchy family of joint laws of (m,D_m,P), hence a limiting probability
law for odd uniform bands. Dyadic summation and initial-halving
invariance give the same law under uniform positive integers up to X
and fixed multiplicative intervals. This uses standard finite coupling
and weak-convergence arguments, written rather than Lean checked.
The minimum marginal agrees with the previous minimum distribution.
Restriction to m=1 gives a finite limiting submeasure for known-basin
D with mass d_1. No claim d_1=1 is included, and no PLD input is needed.
Bounded truncated moments converge; untruncated moments are not proved.

PRE-ARRIVAL CONSEQUENCE:
For q=3n+2 known convergent, H(n)<=(23/3)D(q)+1. Counting these q in
[1,6*2^k+2] transfers the actual-integer tightness to
  lim_(R->infinity) sup_(k>=0) 2^(-k)
    #{2^k<=n<2^(k+1):3n+2 in basin(1), H(n)>R}=0.
First take limsup in k, then absorb finitely many early bands.
The parent need not have a certified future arrival. This statement
is weaker than a bounded mean: no integrable tail estimate is given.
Uniform integrability would suffice, but is stronger than merely a
uniform bound on first moments. The negative arrival advance and
post-arrival reversed drift remain separate open quantities.

VERIFICATION:
Final record passed 2026-10-14T13:46:26.924291+00:00. One fresh Lean
build took 0.888 seconds on 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten new rational finite-list
roots use only propext, Classical.choice, Quot.sound; no admissions,
native computation or warnings in the final build. These are
  deficit_append, deficit_scaled, deficit_splice, deficit_range,
  deficit_prefix_bound, splice_increase_bound, common_tail_bound,
  shared_terminal_weight_bound, deficit_chain, clock_chain.
The verification record hashes 14 files and authenticates the prior
prearrival 35, clocked-minimum 13, finite-path-packing 12, and
natural-density 2 hashes. No prior long suite was rerun.

Exact Python counts: 4095 independently replayed first arrivals,
205759 shortcut steps, 209854 prefix-splice/increment checks and the
same number of finite-product loss bounds; 2047 halving invariances;
25970 memoized recurrence links; 24570 odd-passage record checks and
24570 common-landing comparisons. Twenty-five maximal couplings have
exact marginals and mismatch equal to TV. There are 400 bounded
truncated-moment transport checks and 100 marginal clock union bounds.
A five-link gluing over 1024 starts has 766 good chains, 258 bad,
base clock 75, failure union bound 189/512; all good chain clock and
deficit budgets passed. Fourteen band means and second moments on
1<=n<16384 have exact rational enclosures of width at most 2^(-96).
Every sampled orbit actually reaches one; no hypothetical orbit's
minimum was inferred from finite fuel.

EXPLORATION AND SOURCE REVIEW:
A terminal floating scout /tmp/collatz-deficit-average-scout.cpp and
its executable scanned starts below 2^26 using memoized clocks and
floating D. Last three mean displays: 1.874136956231347,
1.873695531846466, 1.873234248957095. Display maxima about
5.083346014300823 occur on doublings of 2697; these are not certified
maxima or limit values, and 2697 is divisible by three. Do not confuse
these all-source values with the previous unit-only candidates.
No floating value is used by the new verification decisions.

The earlier natural-density note was reread against the primary Tao
v7 HTML, https://arxiv.org/html/1909.03562v7, and its existing audits.
No new gap was found in the paired-sum tilt, renewal reassembly or
summation. In particular the factor 2*m0*(2-log_2 3) incorporates the
E-prime scale; an apparent single-m0 replacement would be wrong.
No old analytic claim was upgraded to a kernel or external theorem.
There was no new external Lean build or external source-archive audit.

NEXT: obtain an integrable tail estimate or a uniform mean for the
actual pre-arrival deficit; tightness alone does not close that step.
Retain the separate negative-arrival and post-arrival drift questions.
All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. Preserve user changes.


## 2026-10-14: the deficit's remaining-clock moment and its missing tail

The preceding goal turn was progress: the written deficit limiting law
and ten finite rational kernel roots were completed. Its 14 hashes were
reauthenticated at this turn's start. The full Collatz objective remains
active and unresolved; no blocker or completion claim applies.

New files:
- docs/DEFICIT-CLOCK-MOMENT.md
- lean/DeficitClockMoment.lean
- verify_deficit_clock_moment.py
- results/deficit-clock-moment/{verification.json,replay.json,two Lean logs}
README and ATTEMPT link the result and reproduction command.

EXACT IDENTITY:
For a convergent shortcut source with first arrival T=tau(n), let
ell_j=W_j-W_(j+1). Then
  D(n)=sum_(j<T)(T-1-j)ell_j.
The factor T-1-j is important: using T-j adds exactly 1-W_T.
At an odd pre-arrival target v>1, ell_j=w_v(n)/(3v+1) and
T-1-j=tau(Uv), so
  D(n)=sum_(odd visited v>1) tau(Uv) w_v(n)/(3v+1).
This is an exact finite identity, with no density or external premise.

Let B be the basin of one, and extend D_B by ZERO outside B only for
the restricted source average. This convention does not claim a finite
arrival time outside B. Define a finite-valued nonnegative observable
on the existing weight-loss space by
  G(v)=tau(Uv) if v>1 is odd and in B, and G(v)=0 otherwise;
  G(infinity)=0.
The ordinary and shortcut loss measures agree. All targets v>1 in B
are nonperiodic, and no source outside B can reach them. Hence
  D_B(n)=integral G dmu_n
for every positive n. The atom at one has G=0, so the infinitely many
known-cycle losses are not charged an arrival clock. In the finite
checks mu_n({1})=W_T and the other odd losses sum to 1-W_T.

WRITTEN MOMENT TRANSFER:
The previous WRITTEN weighted-dissipation argument gives
nu_X=(1/X)sum_(n<=X)mu_n -> mu in TV, error C(log X)^(-c).
Write d_v for its weighted FIRST-HIT density, not the lifetime D(v).
At nonperiodic odd targets mu({v})=d_v/(3v+1). Consequently
  M=integral G dmu=sum_(odd v>1 in B) tau(Uv)d_v/(3v+1)
is an extended nonnegative number. Bounded clock cutoffs satisfy
  |integral min(G,L) dnu_X - integral min(G,L) dmu|
    <=CL(log X)^(-c).
Thus M<=liminf_X mean D_B. M is not proved finite, and equality is
not justified just by TV. No equality with the first moment of the
separate D_m limiting law is claimed.

Define R_L(X)=integral (G-L)_+ dnu_X. With the stated TV limit,
  lim_(L->infinity) sup_X R_L(X)=0
iff mean D_B -> M<infinity. The converse uses convergence of full
and capped moments, then finite early source populations. This is
stronger than merely a bounded mean: a bounded mean could retain a
nonvanishing amount in rare large values. The exact clock-weighted
loss tails are now the specific missing estimate.

If A=sup_X mean D_B is finite, the q=3n+2 targets from the kth parent
band lie below 6*2^k. Their average D is at most 6A, giving
  mean_(n in band, q in B) H(n) <=46A+1.
The mean uses the full parent-band denominator. The parent need not
be known convergent. This does not control negative arrival advances,
post-arrival drift or unknown-child pairs. A bounded mean D is a
SUFFICIENT route, not shown necessary for the original H mean.

CONDITIONAL CLOCK CONSEQUENCE:
Unweighted predecessor density r_v gives r_v D(v)<=A, because D does
not decrease along a path followed backwards before arrival. Combined
with the earlier clock bound this gives
  tau(v)<=(10/3)Av/r_v+v/2 when r_v>0.
Positivity alone does not make this a uniform polynomial bound.
If additionally using the EXTERNAL reciprocal weighted-density floor
from docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md Section 2,
  d_v>=c_star/v for odd convergent units v>1,
then bounded A would force
  sum tau(Uv)/v^2 <=4A/c_star,
  sum tau(v)/v^2 <infinity
on those targets. Therefore tau(v)=o(v^2) there, and hence on all
convergent starts by initial halvings and the one-step passage of an
odd multiple of three to a unit. The external floor comes from its
unit envelope and g(v)=delta*v*d_v at nonperiodic targets. It is NOT
newly replayed or independently revalidated in this turn. This is an
optional, explicitly externally dependent implication. It proves no
clock bound without the unproved bounded-mean hypothesis.

VERIFICATION:
Final record passed 2026-10-14T14:10:41.497887+00:00. Two fresh
sequential Lean builds took 0.633 seconds total on Lean 4.33.1,
compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Seven roots
use only propext, Classical.choice, Quot.sound, with no admissions,
native computation or warnings in the final build:
  loss_age_identity, normalized_loss_age, total_nonneg, total_mono,
  total_scaled, weighted_total_bounds, capped_moment_split.
The record hashes 18 files. It authenticates the previous limiting-law
14, pre-arrival 35 and weighted-dissipation 15 hashes. Existing long
suites were not rerun. No new external Lean build or archive audit.

Exact Python replay: 8191 independent arrivals, 452032 shortcut steps,
8191 complete loss-age identities, 8191 off-by-one diagnostics, 8191
probability-mass identities, 6144 independently summed capped/tail
splits, 13025 memo recurrence links, 224339 odd loss/remaining-clock
identities, 13 authenticated band mean comparisons, and 11 finite
progression/prefix mean transfers. Directed integer rounding uses
scale 2^96; recorded intervals for sums include every term's error.
All sampled sources actually reach one; unknown basin membership is
not inferred from finite fuel.

In the last checked band [4096,8192), the exact intervals display
mean D about 1.876659341956211. Contribution from odd targets >8191
has upper display 0.003730503546312; excess remaining clock beyond
128 has upper display 0.000012269525576. Separate exact Fraction
comparisons of the recorded upper endpoints certify each <1/250.
These finite tails do not prove a uniform-in-source cutoff. The
remaining-clock tail above 256 is zero only for this finite population.
A preliminary exact identity scout on [1024,2048) also passed; its
floating displays were exploratory and are superseded by the record.

RESEARCH CONTEXT AND NEXT:
Reviewed the existing weighted-dissipation probability measure and
cached external basin manuscript. No new external assertion was adopted
as an unconditional local input. A primary-source web search located
Inselmann arXiv:2402.03276v3 (13 Aug 2024),
https://arxiv.org/html/2402.03276v3. It states the average total-clock
lower bound and a matching limit assuming tau(n)=O(log n). It does
not supply the missing upper moment and is context only, not used by
the new theorem. Prior memory mentioned v2; no novelty is claimed.

Next seek an actual bound on R_L(X), or at least on integral G dnu_X,
uniform in source cutoff. The already bounded total lost mass controls
G=1, not this remaining-clock observable. Finiteness of the limiting
series alone is necessary but does not exclude moment concentrated at
moving targets. Keep direct estimates for mean H available: proving
its sufficient mean-D bound may be stronger than necessary. The
negative arrival and post-arrival terms remain separate open questions.
All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes were used. Preserve user changes.

## 2026-10-14: whole deficit tail profiles and the common extended mean

The user resumed after an accidental interruption. Reauthenticated the
preceding records and completed the interrupted tail-profile note,
Lean file and exact verifier. The full Collatz objective remains active.

NEW FILES:
- docs/DEFICIT-TAIL-PROFILE.md
- lean/DeficitTailProfile.lean
- verify_deficit_tail_profile.py
- results/deficit-tail-profile/{verification.json,replay.json,three Lean logs}
Updated ATTEMPT.md, README.md and this memory. Earlier hashed research
artifacts were preserved; the new note closes one previously unclaimed
identification without changing the older record's historical scope.

EXACT PROFILE:
For every positive n, let m(n) be its global minimum, T(n) its first
attainment, and Q_L(n)=sum_(h<(T(n)-L)_+)(1-W_h(n)). These clocks are
finite by well-ordering, not by an assumption that m=1. The profile
belongs to c_0, is nonnegative and nonincreasing, and is preserved by
initial halvings. Put Q^B=1_(m=1)Q and D_B=Q^B_0. Then
  Q^B_L=integral (G-L)_+ dmu_n,
  0<=D_B-Q^B_L=integral min(G,L) dmu_n<=L.
The same G as in the preceding note is zero at one, at infinity and
outside the convergent odd targets. No arrival clock is assigned to
a source outside the basin of one.

For a first odd record landing b at clock i, write t=T(b), p=W_i,
A=prefix deficit, and assume prefix weights >=1-e. If L<=t, then
  Q_L(n)=A+p Q_L(b)+(1-p)(t-L).
If L>t, the landing profile vanishes and the cutoff stays inside the
source prefix. Both cases give 0<=Q_L(n)-Q_L(b)<=eT(n), for ALL L
simultaneously. Hence two sources at a common landing satisfy
  norm_infinity(Q(n)-Q(n'))<=e max(T(n),T(n')).
The common minimum also makes this valid for Q^B. Only previous odd
inputs, not every earlier even state, must exceed the passage floor.

WRITTEN SEQUENCE-SPACE LAW:
Substitute this simultaneous norm estimate into the existing finite
coupling chains. For odd source scales Y>=Z>=B0, failure probability
is C(log B0)^(-c); off failure, minima agree and
  norm(Q(n_Y)-Q(n_Z))+|P(n_Y)-P(n_Z)|
     <=C'(T_B0+1) Z^(-gamma), gamma=1/(40 alpha^2).
Fix B0 first, then send Z to infinity. Do not assume any effective
bound for T_B0 or that T_B0*B0^(-gamma) tends to zero. The laws are
Prokhorov-Cauchy on the complete separable space N_positive*c_0*[0,1].
Dyadic summation and halving invariance give the same law for uniform
positive source prefixes and fixed multiplicative bands.

This is convergence in the supremum norm topology, not just in each
coordinate. A bounded norm alone would NOT imply compactness in c_0.
Weak convergence gives uniform tightness. Compact subsets of c_0 have
uniformly vanishing coordinate tails by a finite norm-ball cover, so
for every epsilon>0,
  lim_L sup_X Pr_X(Q^B_L>epsilon)=0.
This is a probability-tail result, not a mean-tail bound. The same
statement holds for the unrestricted minimum profiles Q.

IDENTIFICATION AND OPEN MOMENT:
The limiting restricted profile q lies in c_0 and inherits the closed
shape conditions. Write Z=q_0. For fixed integer L, q_0-q_L is
bounded by L and continuous on the laws (clamp it on the full space).
Its limiting expectation equals integral min(G,L) dmu by the existing
TV law. Since q_L decreases to zero, monotone convergence gives
  E Z = integral G dmu
      =sum_(odd v>1 in B) tau(Uv)*d_v/(3v+1),
as an extended value in [0,infinity]. This DOES close the identification
left open in the preceding clock-moment note. Z is finite almost
surely, but E Z may be infinite. Source unbounded moments still cannot
be interchanged with their limit.

Pointwise, (D_B-K)_+<=Q^B_K, and
  E_X Q^B_L <=epsilon+K Pr_X(Q^B_L>epsilon)+E_X(D_B-K)_+.
Together with the uniform probability-tail decay, these prove the
equivalence of source-deficit uniform integrability, uniform mean
clock-tail decay, and source means converging to the finite common
moment. NONE of these equivalent conditions is proved. A bounded
first moment alone remains weaker than uniform integrability.

CONDITIONAL PRE-ARRIVAL IMPROVEMENT:
Let eta_k be nonfusion frequency of siblings by physical clock k+1;
the existing written coalescence bound gives eta_k->0. H vanishes
off this event. For all integer L>=0, with the full parent-band
denominator and restriction only to q=3n+2 in B,
  mean H <=((23/3)L+1)eta_k+46 sup_X E_X Q^B_L.
The factor six uses distinct child targets below 6*2^k. Under UI,
first k->infinity at fixed L, then L->infinity, would make this mean
tend to ZERO, stronger than the earlier bounded-mean consequence.
This does not bound negative arrival advances, post-arrival drift,
or unknown-child pairs. Direct mean-H estimates may still require
less than the sufficient full source-deficit UI condition.

VERIFICATION:
Final record passed 2026-10-14T14:34:11.434720+00:00. Three fresh
sequential Lean builds took 2.825 seconds total on Lean 4.33.1,
compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eight roots
have standard axioms only, without admissions, warnings or native
computation. The record hashes 22 files and authenticates the prior
clock-moment 18, limiting-law 14, pre-arrival 35 and signed-window 34
hashes. No large earlier suite or external Lean replay was rerun.

Exact replay certifies 4095 independent first arrivals, 205759 shortcut
steps and independent losses, 213949 all-cutoff loss-age identities,
213949 profile-shape/cap checks, 32760 scalar-tail bounds, 196560 UI
splits, 6476 memoized deficit links, and 2047 whole-profile halving
invariances. Six first-odd-passage floors give 24570 landing bounds
and 24570 source-pair norm comparisons. A long-prefix representative
is used instead of always comparing against the landing itself;
22623 comparisons have positive weight loss on BOTH source prefixes.
The cutoff cases contain 398224 after-landing and 885470 before-landing
checks. There are 72 authenticated prior clock-tail comparisons.

The 1023 pre-arrival pairs have 28723 exact cost terms, 8184 sparse
tail bounds, 80 band/prefix transfers and ten prior band comparisons;
508 fused-at-prefix pairs have zero pre-arrival cost. Aggregates use
directed integer rounding at scale 2^96, never floating decisions.
For [2048,4096), the displayed mean deficit is about 1.8677929625,
and the tail beyond 128 has upper display about 0.000004124914.
That finite band has no Q_128>1/16 and Q_256=0. No uniform-in-source
tail follows from these finite observations.

NEXT:
The missing step is now an actual mean-tail or UI estimate, or a
weaker estimate restricted to rare nonfused child progressions. The
extended-mean identification by itself does not supply finiteness.
Do not count c_0 tightness, a bounded total loss, or the preceding
finite experiments as the missing integrability argument. No new
external premise was adopted, and no reciprocal density floor is
needed for this milestone. All jobs are terminal. No agents,
installations, credentials, staging, commits or other Git writes
were used. Preserve the user's changes and index.

## 2026-10-14: an all-source censored deficit at an integer logarithmic clock

The preceding goal turn was progress; its 22 manifest hashes were
reauthenticated. Investigated whether rare nonfused pairs permit a
direct pre-arrival mean estimate. Rarity alone still does not control
cost on those pairs, and no such bound was obtained. The useful change
of direction is an ALL-SOURCE finite-prefix criterion that avoids the
stronger known-basin lifetime-deficit UI assumption. Collatz remains
unresolved and the original goal remains active.

NEW FILES:
- docs/CENSORED-DEFICIT-CLOCK.md
- lean/CensoredDeficitClock.lean
- verify_censored_deficit_clock.py
- results/censored-deficit-clock/{verification.json,replay.json,three logs}
Updated ATTEMPT.md, README.md and this memory. Older research files and
verification records were preserved.

ORDINARY CLOCK AND ARRIVAL FLAG:
This note uses ORDINARY C, not shortcut U. W_t loses a factor
3v/(3v+1) at an odd input and is unchanged at an even input.
Let tau_1 be first arrival at one, infinity if absent, and define
  z_t(n)=1_(tau_1(n)>t)*(1-W_t(n)),
  A_T(n)=sum_(t<T) z_t(n).
Computing A_T requires only T steps, or earlier arrival at one.
It does not require deciding future convergence. Always 0<=A_T<=T;
for n=1 it is zero. For h_t=1_(tau_1<=t), exact accounting is
  z_t=1-h_t-W_t+h_t W_t.
The last term cannot be dropped at finite clocks. The checker includes
a bounded_censored_deficit(n,horizon) implementation which always
finishes within that finite horizon.

THE MASS:
Let B be the basin of one and r_B its existing natural density. Let
mu be the WRITTEN TV limit of whole-orbit loss probability measures,
d=mu(infinity), and b=mu(odd states outside B). Exactly at each source,
  mu_n(odd states in B)=1_B(n),
  mu_n(odd states outside B)=1_(outside B)(1-W_infinity(n)).
TV therefore gives b=1-r_B-d and 0<=b<=1-r_B. The mass b includes
lost weight on both escaping and hypothetical additional cyclic
components. It differs from d, the unlost escape weight.

WRITTEN PHASE AND INTEGRATED LIMIT:
Put kappa=3/log(4/3), with natural logarithms. Existing written results
give, at floor(c log X), hit proportion ->0 below kappa and ->r_B above;
mean W ->1 below and ->d above. The mean of h_t W_t tends to zero on
both sides. Above kappa, choose kappa<c'<c: arrivals by c' log X have
cycle weight at most (3/4)^floor((c-c')log X/3+O(1)), and arrivals
between the two clocks have asymptotically zero proportion. Hence
  mean z_floor(c log X) -> b*1_(c>kappa), c !=kappa.
The instantaneous critical value remains unspecified.

Define Phi_X(c)=mean A_floor(c log X)/log X. Integrating the bounded
step function f_X(u)=mean z_floor(u log X) over [0,c] differs from
Phi_X(c) by at most 1/log X. Dominated convergence yields
  Phi_X(c) -> b*(c-kappa)_+ for EVERY c>=0,
including zero at c=kappa. The finite Lipschitz error 1/log X makes
convergence uniform on each compact coefficient interval. No lifetime
deficit first moment or UI enters this bounded-integration argument.
Testing at or below kappa cannot distinguish b=0 from b>0.

Two important modifications would lose the desired criterion:
- WITHOUT the arrival flag, the normalized mean limit is
  (1-d)*(c-kappa)_+, positive above kappa under full convergence.
- Restricting the censored average to sources in the known basin gives
  zero at every coefficient, even if b>0. Below kappa use the all-source
  integrand bound; above it use r_B minus the clocked hit proportion.
Thus the new open estimate must include all sources, not only known B.

POINTWISE IMPLICATION AND EXTERNAL PREMISE:
For a nonconvergent source with global minimum m>1, m is odd and
W_infinity<=3m/(3m+1). The first odd step from m supplies this bound,
regardless of the accumulated earlier weight p<=1. If pi_m is the
minimum density, b>=sum_(1<m<=H) pi_m/(3m+1). The minimum law has
total mass one, so b=0 iff r_B=1 under the written local inputs.

External PLD for EVERY positive unit target then makes b=0 equivalent
to full Collatz, including cycle exclusion. A nonconvergent orbit
reaches a positive unit v; its predecessors all remain nonconvergent
and have minimum <=v, yielding b>=r_v/(3v+1)>0. This uses no uniform
reciprocal density floor, only positivity for that fixed target.
The earlier 389-module source replay remains historical evidence.
This turn authenticated its local provenance records, not a fresh
external source build or a new rehash of all 389 external objects.
The previously recorded temporary source absence remains unchanged.

INTEGER CLOCK:
At X=2^k, T=8k is above the transition because
  4^8-2^3*3^8=13048>0.
Thus
  (1/(k*2^k))*sum_(n<=2^k) A_(8k)(n)
     ->(8-3 log2/log(4/3))*b.
With the stated inputs, proving this sequence tends to ZERO would
settle full Collatz. Its zero limit is NOT established here. This is
a finite-prefix mean criterion, not a claim to have proved its missing
bound. There is no effective convergence rate from the written inputs.

VERIFICATION:
Final record passed 2026-10-14T15:00:47.670099+00:00. Three fresh
sequential Lean builds took 4.018 seconds total on Lean 4.33.1,
compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten roots
use standard axioms only (the closed integer comparison uses none),
with no admissions, warnings or native computation. These prove finite
rational accounting, cutoff and cap comparisons, positive-loss algebra
and the integer clock margin, not the analytic limits or the zero value.
Twenty files are hashed. Prior local records authenticate 15 weighted
dissipation, 13 clocked minimum, 22 tail-profile and 31 known-basin
trace hash entries. Earlier large suites were not rerun.

Exact Python checks: 16384 independent complete first arrivals;
1467643 ordinary weight steps; 16384 ordinary/shortcut clock and
deficit comparisons; 25970 memoized deficit links; 16384 independent
bounded-prefix computations at clock 112; 28800 every-clock censor
and known-cycle comparisons; 218240 population source/clock pairs;
50 exact population accounting enclosures; 25 comparisons against
authenticated older finite weight means. All aggregate intervals use
directed integer rounding at scale 2^96, with no floating decisions.
At clock 112, 5541 starts through 16384 remain alive, but each later
arrival is separately checked. These are not counterexamples.

For the T=8k rows with k=6,8,10,12,14, the displayed upper values of
mean A_T/k are approximately .1821874, .1784645, .1661004, .1537981,
.1388862. At k=14 the unnormalized mean A_112 is about 1.9444064;
the uncensored mean divided by k is about 2.1963352. These are finite
values with exact enclosures, not certified estimates of b or a trend
that can be extrapolated.

RESEARCH CONTEXT AND NEXT:
A primary-source search rechecked Inselmann arXiv:2402.03276v3,
https://arxiv.org/html/2402.03276v3 (13 Aug 2024). Its matching average
total-clock upper limit assumes tau(n)=O(log n); it supplies no missing
unconditional upper bound here. It was context only, not a proof input.
Other search hits on polynomial analogues and finite computation were
not adopted as integer-Collatz results.

The next useful full-goal estimate is sum_(n<=2^k) A_(8k)(n)=o(k2^k).
Seek an actual bound for these finite prefixes, including sources not
yet known to converge. A bound only on the restricted known-basin
deficit, or observing finite survivor proportions, does not suffice.
The direct rare-pair pre-arrival mean remains an alternative open
route. All jobs are terminal. No agents, installations, credentials,
staging, commits or other Git writes occurred. Preserve user changes.

## 2026-10-14: exact censored progression transport and failed finite bounds

Resumed after the user's accidental interruption. The preceding completed
goal turn was progress; its 20 censored-clock manifest entries were
reauthenticated. The interrupted work had already captured the native
k=20 census. Its source, binary and output hashes matched. The integrated
checker then reproduced the same output and added the independent census
and formal transport. This is a finite obstruction to specific proposed
bounds, not the missing all-source asymptotic estimate. Collatz remains
unresolved and the full research goal stays active.

NEW FILES:
- censored_progression_census.rs
- verify_censored_progression_transport.py
- lean/CensoredProgressionTransport.lean
- lean/CensoredProgressionCertificates.lean
- docs/CENSORED-PROGRESSION-TRANSPORT.md
- results/censored-progression-transport/{verification.json,census.json,
  replay.json,native-k17.json,native-k20.json,independent-k17.json,
  two native provenance records,two Lean logs}
Updated ATTEMPT.md, README.md and this memory. No existing research
source or earlier verification record was changed.

EXACT FINITE RECURRENCE:
All clocks are ORDINARY. L_t(n)=min(t,tau_1(n)); the minimum is t if
there is no arrival. A_t sums 1-W_h at alive input clocks h<L_t.
Even transport is A_(t+1)(2n)=A_t(n). For n>=1 and q=3n+2, the
odd source follows 2n+1 ->2q ->q, with retained factor
  r=(2q-1)/(2q),
so A_(t+2)(2n+1)=(1-r)+r A_t(q)+(1-r)L_t(q)
                  =A_t(q)+e_t(q),
  e_t(q)=(1+L_t(q)-A_t(q))/(2q).
Since L_t-A_t is the sum of alive weights, e is positive and
  1/(2q)<=e_t(q)<=(t+1)/(2q).
This includes clock zero, arrivals exactly at the boundary, and alive
sources; there is no assumption about a later first arrival. The odd
source one is excluded from this formula and contributes zero in sums.

Define B_t(N)=sum_(n<=N) A_t(n), F_t(N)=B_t(N)/N,
P_t(X)=mean_(n<=X) A_t(3n+2), E_t(X)=sum_(n<=X)e_t(3n+2), and
delta_t(X)=P_t(X)-F_t(3X+2). There are exactly X progression terms,
from 5 through 3X+2. The reference is all sources 1..3X+2.
Parity splitting gives the KERNEL finite identity
  B_(t+2)(2X+1)=B_(t+1)(X)+sum_(n<=X)A_t(3n+2)+E_t(X).
The WRITTEN normalized form is
  (2X+1)F_(t+2)(2X+1)
    =X F_(t+1)(X)+X F_t(3X+2)+X delta_t(X)+E_t(X).
The WRITTEN harmonic bound is E_t(X)<=(t+1)H_X/6
  <=(t+1)(1+log X)/6.
The explicit affine correction E and the sampling error X delta must
remain separate; the bound on E is not automatically a bound on delta.

EXACT FINITE COUNTEREXAMPLES TO PROPOSED BOUNDS:
For X=2^20=1048576, Y=3145730 and t=160, directed intervals certify
  delta_t(X)>9t/X>0,
  X delta_t(X)>8 E_t(X).
Decimal diagnostics only: delta about .00138426786795,
X delta/t about 9.07193790, E about 172.30790118,
and X delta/E about 8.42393212. At scale S=2^64, raw endpoints are
  progression sum lower P-=35531119056706020611884338,
  prefix sum upper B+=106513097985271158323620897,
  correction sum upper E+=3178519754951037415201.
The certificate checks Y P->X B++9tYS and Y P->X B++8Y E+.
These are kernel arithmetic comparisons of NATIVE census endpoints,
not a kernel derivation of those endpoints.

At X=2^17=131072, Y=393218 and t=136, both the native and independent
Python censuses give delta>2t/X; X delta/t is about 2.41816135.
Thus P<=F, delta<=9t/X, and X delta<=8E fail as universal finite
inequalities. Do NOT claim failure of all constants, all O(t/X), all
O(t log X/X), all multiples of E, or an eventual bound after some
unspecified threshold. The all-source zero-limit criterion is untouched.

VERIFICATION AND PROVENANCE:
Final record passed 2026-10-14T15:36:43.849288+00:00. Two fresh sequential
Lean 4.33.1 builds took .686 seconds total, using compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eight actual-map roots use
standard axioms only. They define ordinary C, its rational weight
factor, finite alive clock, and deficit from arbitrary initial weight;
they prove scaling, even and odd transport, odd loss, correction,
deficit/correction bounds, and the finite parity population identity.
Three generated closed integer comparisons use no axioms. No admissions,
warnings, native_decide or native proof reduction occur in these roots.
The full census is NOT kernel certified.

Native checked-overflow Rust 1.98.1 ran sequentially at k=17 and k=20,
taking 41339617 and 396719184 ordinary steps respectively. At k=20,
132829174 steps were odd and 1169637 sources were alive at cutoff160.
Alive is only a finite arrival flag, not nonconvergence evidence.
Native weight intervals propagate floor/ceiling products at scale2^64;
deficit and explicit correction sums use directed integer rounding.
Compiler, command, source/output/binary hashes and timings are retained.
The temporary build binaries need not persist to replay the commands.

The independent Python census uses unbounded integers and at each alive
clock reconstructs W=n*3^odd/(2^even*current_state), not the native
propagated intervals. At k=17 its narrower sum intervals lie within the
native intervals. Its 41339617 ordinary steps, 13876677 odd steps,
150471 alive sources and all population counts match. The independent
census took 10.364 seconds. There is NO full independent Python replay
of the k=20 population. No verification decision uses floating point.

The census stage passed 2026-10-14T15:32:28.880166+00:00 and was then
reused after hash authentication for the final manifest. The default
verifier reruns it; --census-only saves this stage and --reuse-census
authenticates it before fresh kernel builds and Fraction replay.
Sixteen files are hashed by the final manifest; the preceding
censored-clock record's 20 entries were also authenticated.

Separate Fraction-product replay: 4290 bounded prefixes, 273403 actual
weight steps, 132096 even transport checks, 132096 odd transport and
correction checks, and 42 exact population identities. The odd checks
include 71541 alive-child and 60555 arrived-child cases. All parent
indices 1..1024 and cutoffs0..128 are included. No later arrival is
needed for these checks.

NEXT AND LIMITS:
The remaining estimate is still sum_(n<=2^k) A_(8k)(n)=o(k2^k).
The exact recurrence now isolates the progression average that a direct
induction would have to control. Seek an actual estimate strong enough
for that recurrence, or another direct all-source argument. Failure of
the tested constants does not exclude the whole approach. The earlier
known-basin UI and direct rare-pair bounds remain alternative open work.
No external density theorem or asymptotic premise enters this finite
transport or obstruction. The earlier proposed zero-limit equivalence
keeps its separate WRITTEN clock/weight and EXTERNAL PLD dependencies.
No fresh external source replay or literature audit was performed.
All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes occurred. Preserve user changes.

## 2026-10-14: clocked progression mixing and a uniform logarithmic-power error

The previous goal turn was progress: exact actual-map transport and
finite counterbounds were saved. Its 16 manifest entries were freshly
authenticated. This turn sought an estimate that can be used in that
recurrence rather than testing another small constant. It obtains a
WRITTEN asymptotic progression estimate, with finite algebra and replay
checked separately. The all-source zero limit and full Collatz remain
unresolved; the original research goal remains active.

NEW FILES:
- docs/CLOCKED-PROGRESSION-MIXING.md
- lean/ClockedProgressionMixing.lean
- verify_clocked_progression_mixing.py
- results/clocked-progression-mixing/{verification.json,replay.json,three logs}
Updated ATTEMPT.md, README.md and this memory. The preceding research
sources and verification records were preserved.

WRITTEN QUANTIFIED RESULT:
For delta_t(X)=mean_(n<=X) A_t(3n+2)-mean_(n<=3X+2) A_t(n),
  for every R>0 there are C_R,X_R such that
  |delta_t(X)|<=C_R*t/(log X)^R for all X>=X_R and every finite t>=0.
All clocks here are ORDINARY; no assumption of eventual arrival is made.
Analogous bounds C_R/(log X)^R hold uniformly in t for the progression
discrepancies of s_t=1_(tau_1>t) and z_t=s_t(1-W_t).
In particular at X=2^k,t=8k the absolute, unnormalized A discrepancy is
O_R(k^(-R)) for every R, after using exponent R+1 in the displayed bound.
The constants and thresholds are not made effective. This is weaker in
X than O(t/X); it is compatible with the prior exact finite violations.

SOURCE CONGRUENCE AND FIXED ENDPOINT:
For a Syracuse word a of length n and total S, write
  Aff_a(N)=3^n 2^(-S)N+F_n(a), B=2^S F_n(a) integer.
Requiring the preimage N of an odd M to satisfy N=r mod 3 strengthens
the usual M=F_n mod 3^n condition to
  M=V_(n,r):=F_n+3^n 2^(-S)r mod 3^(n+1).
For r1 choose c=2; for r2 choose c=1, so 2^(-c)=r mod 3. Then
  F_(n+1)(c,a)=F_n(a)+3^n 2^(-S-c)=V_(n,r) mod 3^(n+1).
Under reversal this is the usual offset X_N with its LAST valuation
fixed to c, and the preceding N-1 valuations still independent Geom(2).
Its reduction modulo3^m for m<=n is exactly the ordinary F_n marginal,
jointly with S. Do not drop the conditioning on the valuation sum.

WRITTEN FOURIER AND COLLISION EXTENSION:
For odd N, pair the first N-1 coordinates. The fixed final-coordinate
term and the sum tilt are unit phases after conditioning on pair totals.
The original paired absolute product bound is unchanged. For even N,
condition on the first coordinate a and use
  X_N^c=2^(-a)(1+3X_(N-1)^c).
This reduces to odd length at primitive modulus3^(N-1), uniformly in a.
It avoids discarding an uncontrolled pair factor. Integrate the tilt
to obtain uniform UNNORMALIZED fixed-sum Fourier bounds; never divide
by the possibly small probability of an exact sum.

In the collision/Plancherel proof, conditioning on the endpoint costs
at most 2^c in exceptional-event probabilities. The first entropy block
ends near .7925 N and is unchanged. The independent tail either retains
the fixed endpoint, when the new Fourier bound applies, or loses it
under a lower-modulus projection, when an ordinary fixed-sum mixture
applies. Each visible Fourier block still has length comparable to N.
Lower-level projected joint laws are mixtures of ordinary fixed-sum
laws, so the preceding local joint-mixing argument finishes the proof.
This analytic extension is WRITTEN, not kernel formalized or peer reviewed.

SAME-SCALE MARKED PASSAGE COMPARISON:
Take alpha=1001/1000, y=x^alpha and odd sources on [y,2y), either uniform
or conditioned to source residue r1 or r2 modulo3. Retain the mark
(b,I), with b the first odd landing <=x and I its ORDINARY clock.
The marked TV difference is O_R((log y)^(-R)) for every fixed R;
nonentry has probability O(x^-c). The early dyadic valuation estimate
survives the source residue restriction by elementary coprime-modulus
counting. An expanded clock window covers the entire narrow source
interval; all discarded valuation and window errors are stretched-
exponentially small in log x, hence smaller than any fixed log power.

In the preimage formula, n is the Syracuse passage count, n'=n-m0,
s is the initial word sum, and M has exactly m0 remaining Syracuse
steps to first passage. The ordinary clock is exactly
  I=n+s+S_m0(M).
Thus every bounded test of (b,I) can be retained as a test of (n,s,M).
For fixed(n,s), the source restriction changes the residue modulus
from 3^n' to 3^(n'+1), and source count from K_y to K_(y,r).
Both counting coefficients remain uniformly bounded. After smoothing
to 3^m0, the joint laws agree exactly, while their scalar ratio is
  K_y/(3K_(y,r))=1+O(1/y).
There are only O((log x)^(3/2)) relevant (n,s) pairs; the arbitrary-power
joint mixing absorbs this number. No summation over the passage clock
is needed to identify the common main term.

This SAME-SCALE comparison does NOT use the renewal lemma, a local
limit theorem, or the irrationality exponent forlog_2 3. Do not apply
its arbitrary inverse-log-power rate to the earlier DIFFERENT-SCALE
stabilization, whose phase reassembly is a separate argument.

TRANSFER TO EVERY FUTURE CUTOFF:
Lift a maximal marked coupling to sources. On its good event both
sources reach the same b at the same I. Finite-path packing gives all
prefix weights in [1-epsilon_x,1], epsilon_x=min(1,(8192/3)x^(-1/20)).
Only odd prefix inputs need to exceed x. No repeated state occurs
before a finite first passage. For any t, let a be the deficit through
min(t,I), p the retained weight at I, d=A_((t-I)_+)(b), and
l=L_((t-I)_+)(b). Then
  A_t(source)=a+p*d+(1-p)*l,
  0<=A_t(source)-d<=epsilon_x*t.
Both coupled sources lie in that same interval. Their deficits differ
by at most epsilon_x*t simultaneously for all t, their arrival flags
agree at all times, and their censored cells differ by at most epsilon_x.
On the bad event use the caps t and1. This gives the uniform bounds on
odd blocks without any future-convergence assumption.

For all integers, split by the initial v2=a and use the same a in the
coupling. The conditioned odd part has residue 2*2^(-a) mod 3, a unit.
Discard a>(log_2 y)/2 at mass O(y^-1/2); retained odd scales are >=sqrt y.
Mixture-weight errors total O(log y/y). Then dyadically decompose the
prefix 1..Y down to sqrt Y, with weighted errors and a discarded O(Y^-1/2)
mass. At Y=3X+2, conditioning on residue 2 includes source 2 and X+1 terms;
the desired progression omits 2. Renormalization costs<=t/X (or1/X).
These errors all fit every fixed inverse logarithmic power.

WHY THE ALL-SOURCE ZERO LIMIT IS STILL OPEN:
At t~log X the new progression error and E_t(X)/X both tend to zero.
But the bulk profile H_t(N)=b(t-kappa log N), above the critical clock,
obeys 2H_(t+2)(2X)=H_(t+1)(X)+H_t(3X) for ANY b, since
  3-kappa log(4/3)=0.
This is only a bulk algebra check, not a constructed orbit law or a
proof that the estimate can never help. It shows why comparing leading
coefficients alone does not force b=0. Control of the full iteration
and its small-scale boundary data, or another all-source argument,
remains necessary. Existing phase-law b=1-r_B-d is still undetermined.

VERIFICATION:
Final finite record passed 2026-10-14T16:04:59.284994+00:00. Three fresh
sequential builds took .917 seconds total on Lean 4.33.1, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Ten new finite roots use only
standard axioms, with no admissions, warnings or native proof reduction.
They prove integer inverse/seed relations, affine algebra, matched-clock
window/cell bounds, finite coupling sums and the neutral bulk identity.
They do NOT prove Fourier decay, marked mixing or the asymptotic bound.
Fifteen files are hashed. The prior transport's 16 entries were validated.
A later documentation-only wording clarification refreshed that note's
hash with an explicit review entry; completed finite checks were reused.

Exact Python replay:

- 19,530 affine/modular/reversal checks;
- 39,060 seeded offset and pointwise low-marginal checks;
- 175,770 cleared source-residue equivalences;
- 270 exact joint low-marginal comparisons;
- 168 conditional pair-convolution identities;
- 6,660 even-length head-removal identities;
- 2,688 independently computed first odd passages, 76,328 ordinary steps;
- 95 distinct pairs with common landing AND ordinary clock;
- 285 bounded prefixes, 23,340 additional weight steps;
- 12,797 all-cutoff deficit/cell/arrival checks, including 3,582 before
 landing, 9,215 at/after landing, and 95 exact landing boundaries.
The geometric-word enumeration truncates each random valuation at 5
and records exact omitted mass 1-(31/32)^n. These finite oscillations
and passage TVs are not a test of the asymptotic regime or constants.
No floating-point decisions or Monte Carlo enter this verification.

EXTERNAL REVIEW AND NEXT:
Rechecked primary source https://arxiv.org/html/1909.03562v7,
Tao, 16 July 2026 version, Sections 5, 6, 7.1. The published inputs and
proof structure are distinguished from the new local written deduction.
No external PLD premise is needed for this progression estimate, and no
external Lean source replay was performed. The earlier zero-limit/full-
Collatz equivalence keeps its own written and external dependencies.
The next task is to exploit the small progression error through the full
recurrence without silently assuming boundary convergence or b=0.
All processes are terminal. No agents, installations, credentials,
staging, commits or other Git writes occurred. Preserve user changes.

## 2026-10-14: cutoff descent and all logarithmic moments of the minimum

The user resumed after an accidental interruption. The unfinished
CutoffDescent.lean argument was recovered, its one compilation error
in the even population proof was fixed, and the written argument and
independent verification were completed. The preceding progression
mixing milestone was progress; this turn strengthens its consequence
for global minima. It does not settle the all-source censored-deficit
zero limit. Collatz remains unresolved and the research goal is active.

NEW FILES:
- docs/MINIMUM-LOG-MOMENTS.md
- lean/CutoffDescent.lean
- verify_cutoff_descent.py
- results/cutoff-descent/{verification.json,replay.json,two build logs}
Updated ATTEMPT.md, README.md and this memory. Prior research sources
and verification records were preserved. The Git index hash remained
f852ffcf0641b616658fa46c94d16cb37a86db08b4014fb414a2c4a2fa426a63.

WRITTEN RESULT AND ITS INPUT:
For m(n)=min_t C^t(n), f_H(n)=1_(m(n)>H), F_H(N)=mean_(n<=N)f_H(n),
  for each r>0, sup_N F_H(N)<=C_r (log H)^(-r), H>=2.
The constants and thresholds depend on r and are not effective here.
The preceding marked source-class coupling has a common first odd
landing b that is a strict record. Thus m(source)=m(b) on its good
event, simultaneously for all H, even when H exceeds the passage floor.
Initial halvings preserve the minimum. The same source decomposition
and omission of source2 give
  |mean_(n<=X) f_H(3n+2)-F_H(3X+2)|<=A_R (log X)^(-R),
uniformly in H, for every fixed R and sufficiently large X.
This uses the preceding local WRITTEN same-scale progression mixing;
it is not a new theorem attributed to Tao or a kernel mixing proof.
No external predecessor density or different-scale renewal estimate
is used in this new tail deduction. No weight-retention bound is
needed to transport the minimum label itself.

ACTUAL MAP AND AUXILIARY CUTOFFS:
  f_H(2n)=f_H(n),
  f_H(2n+1)=1_(2n+1>H) f_H(3n+2)<=f_H(3n+2),
  f_H(n)=0 for n<=H.
Do not omit the killed odd boundary factor. Let a=floor(N/2),
l=floor((N-1)/2), b=3l+2. Parity splitting gives
  F_H(N)<=(a/N)F_H(a)+(l/N)F_H(b)+(l/N)delta_H(l)
         <=[F_H(a)+F_H(b)]/2+|delta_H(l)|/2.
For N>=9, l>=N/3>=sqrt N; using R=r+1 gives error
K_(r+1)(log N)^(-r-1), with K_(r+1)=2^r A_(r+1), for all N>H
once H>=max(9,3X_(r+1)). The boundary mean is exactly zero.

The fair auxiliary chain chooses a or b until its cutoff is <=H.
It is not a random model or proof of termination of a Collatz orbit.
For even N, 4ab=3N^2-2N; for odd N, 4ab=3N^2-2N-1.
Thus mean log cutoff decreases by at least d=.5log(4/3)>0.
For N>H>=3, both children are >=H/2 and b>N. Finite drift summation
gives E(tau wedge J)<=log(2N/H)/d. Hence E tau is finite and the
auxiliary survival remainder tends to zero for each fixed initial N.

SUMMING THE ERRORS:
Convexity of s^(-r) and the negative log drift imply
  P[(log n)^(-r)](N)-(log N)^(-r)>=rd(log N)^(-r-1).
Use V_H(n)=[log(max(n,H/2))]^(-r), which agrees at every active state
and its children and is bounded by [log(H/2)]^(-r). Finite telescoping
bounds the expected occupation of (log N_j)^(-r-1) by
  [log(H/2)]^(-r)/(rd).
Unroll the mean inequality, bound the terminal contribution by auxiliary
survival probability, then let depth tend to infinity separately for
each initial N. The resulting bound is independent of N, so taking
the supremum afterwards is legitimate. Enlarging constants handles
the finitely many smaller floors and proves the stated log-power tail.

For independent rational testing, 8ab<=3N(a+b) also gives
  P(1/n)(N)-1/N>=1/(3N).
The stopped reciprocal potential min(1/n,2/H) yields
E sum_(j<tau wedge J)1/N_j<=6/H at every finite depth.
This finite rational budget does not formalize the log convexity step.

MOMENTS AND LIMITATIONS:
With Z=log m(U_N), the tail is <=B_R u^(-R) for Z>u. For p>0,R>p,
  E[Z^p 1_(Z>L)]<=B_R R/(R-p) L^(p-R)
for large L, uniformly in N. Every fixed log-minimum power is therefore
uniformly integrable. Using the earlier WRITTEN existence of the minimum
law pi additionally identifies the limit as sum_a pi_a(log a)^p<infinity.
That limit-law input is not needed for the tail or uniform integrability.

These are not moments of arrival time or lifetime deficit D, nor
positive power moments of m itself. At a fixed small floor the bound
is a generally positive, unspecified number. Sending r to infinity
while fixing constants and thresholds is invalid. A fixed non-one
minimum for a hypothetical cycle or divergent orbit is compatible with
the estimate. Neither pi1=1 nor the required all-source zero limit is
proved. The previous known-basin deficit UI problem remains open.

VERIFICATION:
Final record passed 2026-10-14T16:32:38.766012+00:00. Two fresh sequential
Lean 4.33.1 builds took .950 seconds, compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Sixteen new roots use only
propext, Classical.choice and Quot.sound, with no warnings, admissions,
or native proof reduction. The noncomputable infinite-survival predicate
is used only for implications and finite population statements; no
positive infinite-survival instance is asserted. The finite stopping
and potential lemmas are rational. All analytic limits remain written.
The manifest hashes 12 files. The prior mixing's 15 and transport's 16
manifest entries were authenticated, without rerunning their censuses.

Independent exact replay:
- 6,146 direct ordinary prefixes, 798,980 ordinary steps;
- 2,377,728 even and 2,377,728 killed-odd finite survival identities;
- 1,565 nontrivial killed-boundary cases and 1,800 shifted population
  splits/bounds, across nine floors and clocks through 130;
- 516 first odd strict records, 33,540 finite minimum equalities and
  167,700 threshold comparisons, including thresholds above the floor;
- 99,998 integer product/reciprocal checks and 698,623 overshoot checks;
- 15 auxiliary chains through depth12, 195 distribution-versus-recursion
  agreements and finite unroll/budget checks, 2,063 active expansions.
At clock128, 1,208 of the 6,146 prefixes have not reached one. These
are finite live prefixes, not infinite-survival claims; no later
arrival decision was used. All verification decisions are exact.

NEXT:
This closes the minimum-tail iteration, not the censored-deficit
iteration. A useful next direction is to retain the time shifts and
boundary terms in that latter recurrence, or audit the local analytic
mixing premise independently before relying on stronger consequences.
Large-minimum tightness alone does not control arbitrary clocks at
the finitely many remaining states. No new external theorem, external
Lean replay, agents, installations, credentials, staging, commits, or
other Git writes occurred. All processes are terminal.

## 2026-10-14: audit of marked preimages and uniform-source endpoints

The previous goal turn was progress: the conditional minimum log-tail
argument and finite cutoff proofs were completed. Its 12 manifest
entries were freshly authenticated. This turn audited the analytic
premise's finite passage bridge instead of deriving another consequence
from it. No contradiction was found in retaining the ordinary clock.
The full analytic mixing estimate is still neither kernel formalized
nor independently peer reviewed. The original research goal is active;
the all-source zero limit and Collatz remain unresolved.

NEW FILES:
- docs/MARKED-PREIMAGE-AUDIT.md
- lean/MarkedPreimageAudit.lean
- verify_marked_preimage_audit.py
- results/marked-preimage-audit/{verification.json,replay.json,three logs}
Updated ATTEMPT.md, README.md and this memory. Prior research sources
and manifests were preserved. No index changes were made; its SHA256
remains f852ffcf0641b616658fa46c94d16cb37a86db08b4014fb414a2c4a2fa426a63.

PRIMARY SOURCE REVIEW:
Reopened https://arxiv.org/html/1909.03562v7 and inspected Lemma2.1,
Proposition5.2 and its event-equivalence proof, Section6's initial/tail
factorization at a fixed partial valuation sum, and Section7's paired
absolute-product bound. The published passage proposition is for
log-uniform sources and unmarked landing sets. It does not by itself
assert the local uniform-source clock-marked extension. The proof's
event equivalence permits a bounded marked test; the uniform interval
replacement still needs its own endpoint counting argument.

No lost independence was found in the two local analytic modifications:
after fixing the initial sum l, a total sum s imposes only tail sum s-l;
after conditioning on pair totals, the total-sum tilt is a unit phase.
For a fixed final valuation, the early collision block remains unchanged
and the tail law is treated as in the preceding note. These observations
are a source-based written audit, not a new kernel Fourier theorem or
a claim of external endorsement. No external Lean replay was performed.

NEW KERNEL INVERSION AND CLOCK RESULTS:
For a positive word w of length k and sum s, define its integer numerator
by B_[]=0 and B_(a::v)=3^len(v)+2^a B_v. The cleared equation
  2^s M=3^k N+B_w
with M odd is equivalent to an actual chain of odd positive integers
2^(a_i) N_i=3N_(i-1)+1. The Lean proof extracts the first integer quotient
using coprimality of powers of two and three and then applies induction.
Odd power-of-two factorization gives uniqueness of the word and endpoint
for a fixed source and length. The exact ordinary clock is k+s.

If the intermediate state M first crosses the odd floor after m Syracuse
steps and tail valuation sum sigma, the full mark is (b,k+s+m+sigma)
provided no earlier odd passage occurred in the prefix. The ordinary
first-passage splice and landing identity are kernel proved. Thus an
arbitrary bounded clock test is a function of (k,s,M), without retaining
the rest of the word after grouping by residue and total sum.

WHY THE PREFIX PASSAGE CONDITION IS NECESSARY:
The exact odd path is 19->29->11->17->13, with valuation word [1,3,1,2]
and ordinary clocks [0,2,6,8,11]. At floor16, source19 first crosses at
11 at clock6. The intermediate state17 first crosses at13 after clock3.
The prefix word [1,3,1] has |S_j-2j|<=1 but splicing its clock8 with3
does not give a FIRST passage from19. This witness is kernel checked.
It refutes deleting the earlier-passage condition, NOT the existing
argument, which retains an intermediate-height buffer.

EXPLICIT SUFFICIENT HEIGHT CONDITION:
If every prefix partial sum obeys |S_j-2j|<=E, then every suffix has
multiplicative coefficient <=4^E and offset <=3^k. Consequently
  M<=4^E N_j+3^k
at every prefix odd state N_j. The strict bound M>4^E H+3^k forces
every N_j>H. Even states exceed their next odd endpoint. The rational
envelope implication is kernel proved; the suffix coefficient estimate
is written and tested exactly on the finite words.

In the analytic windows, E=ceil((log x)^.6), k<=n0, and
  M>=x(4/3)^m0 exp(-(log x)^.7).
The positive linear term m0 log(4/3) in log(M/x) eventually dominates
both sublinear logarithmic powers; also 3^k/x decays. Thus the existing
height window supplies the sufficient condition at all sufficiently
large scales. No effective starting scale is computed.

UNIFORM INTERVAL REPLACEMENT:
Let F=B_w/2^s, N=2^s(M-F)/3^k, U=2^sM/3^k and F/M<=eta<1.
Then (1-eta)U<=N<=U. Different membership of N,U in [y,2y) forces N
into [(1-eta)y,y) or [2(1-eta)y,2y). This endpoint localization is
kernel proved, with half-open endpoints. At fixed k, unique inversion
makes (word,M)->N injective. The change is bounded by actual boundary
sources, not by the number of possible valuation words.

On a source lattice of spacing d=2 or 6 there are at most 3 eta y/d+2
such sources, and K=y/d+O(1) source points in the original band. Thus
the per-length normalized marked error is O(eta+1/y). The analytic
F/M<=x^(-.8) estimate and O((log x)^.8) lengths give a power-small
total error. Restricting to a class modulo3 changes both spacing and
normalization by three, with no new exponential word factor.

Grouping by s and by the residue F mod3^k, or
F+3^k2^(-s)r mod3^(k+1) for source class r, is exact. The factor
2^s/K cancels the geometric word weight 2^(-s). An arbitrary bounded
mark test remains inside the endpoint count, whose coefficient stays
uniformly bounded in the analytic support. The same coarse-law
comparison and normalization ratio K_y/(3K_yr) then apply as before.

FINITE VERIFICATION:
Final record passed 2026-10-14T16:50:39.811090+00:00. Three fresh
sequential Lean 4.33.1 builds took 2.379 seconds; compiler commit
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Eleven new roots have only
propext, Classical.choice and Quot.sound, with no admissions, warnings
or native proof reduction. The manifest hashes 14 files and authenticates
the prior cutoff-descent's 12 and clocked-progression's 15 manifest entries.

Exact Python checks:

- 18,374 forward source prefixes, 100,830 Syracuse steps;
- 9,088 tail prefixes and 248 selected forward sources;
- 34,573 inverse integrality and 103,719 source-residue comparisons;
- 1,096 recovered actual words and ordinary first-passage marks;
- 3,918 suffix envelope checks and 20,591 ordinary replay steps;
- 52 complete forward/inverse marked-law agreements;
- 52 complete fixed-total/residue reassembly agreements, 3,464 terms;
- 208 boundary-source injection checks, including a nonzero change.

Thirteen populations use floors 32, 64, 128, tolerances 1, 2 and tail
lengths 1, 2, plus a deliberate rational source endpoint. Every word
satisfying its finite partial-sum condition is enumerated; there is no
extra hidden valuation truncation. With tolerance 1 the word counts at
lengths 1..4 are 3, 8, 21, 55; with tolerance 2 they are 4, 14, 47, 155.

The original power-of-two bands had no changed endpoint membership.
To exercise this case, the final population uses floor 32 and
y=5455/6=909+1/6. Word [3], endpoint 341 has actual source 909 and
unshifted source 909+1/3, crossing that lower band boundary. The exact
complete marked L1 discrepancies are 1/454 unrestricted and 1/151 in
source class 0; the two unit-class discrepancies are zero. The refined
finite eta=259/32768 gives actual boundary counts 11 unrestricted and 4
in class 0. These finite errors do not test the asymptotic mixing rate.

NEXT AND LIMITS:
The finite passage bridge is better supported, but neither the tilted
Fourier estimate nor the collision/Plancherel extension has been kernel
formalized. No effective mixing constant, all-source zero limit, or
escape/cycle exclusion follows from this audit. Return to the exact
censored-deficit recurrence with its time shifts and boundary data, or
continue the analytic formalization. Keep the original full objective.
All processes are terminal. No agents, installations, credentials,
staging, commits, or other Git writes occurred.

## 2026-10-14: the critical ordinary-clock Gaussian window

The user resumed an accidentally interrupted turn. The preceding marked
preimage audit was progress. The interrupted critical-window work was
recovered from its written note and Lean source; a lost compiler result
was not assumed successful. A development build found a remaining
cell-correction proof error, which was fixed explicitly. The full
verifier then passed all 15 roots and the independent exact replay.

NEW FILES:
- docs/CRITICAL-CLOCK-WINDOW.md
- lean/CriticalClockWindow.lean
- verify_critical_clock_window.py
- results/critical-clock-window/{verification.json,replay.json,three logs}

WRITTEN RESULT, CONDITIONAL ON THE PRECEDING ANALYTIC INPUTS:
For ordinary z_t=1_(tau_1>t)(1-W_t), A_T=sum_(t<T)z_t, let
L=log(4/3), d=L/2, kappa=3/L, sigma^2=2(log 6)^2/L^3, and
T_N(u)=floor(kappa log N+u sqrt(log N)). For each fixed real u,
  mean z_T_N(u) -> b Phi(u/sigma),
  mean A_T_N(u)/sqrt(log N)
    -> b[u Phi(u/sigma)+sigma phi(u/sigma)].
The amplitude b is the unknown mean lost weight outside the basin
of one. At u=0 the cell limit is b/2; the integrated coefficient is
b log 6/[sqrt(pi) L^(3/2)]. On N=2^k the integrated coefficient after
normalization by sqrt k is b sigma sqrt(log 2)/sqrt(2pi).

The new cell transport is z_(t+1)(2n)=z_t(n) and, for q=3n+2,
z_(t+2)(2n+1)=r z_t(q)+(1-r)alive_t(q), r=(2q-1)/(2q).
Its excess lies in [0,1/(2q)]. Both parity cutoffs have fair-coefficient
deficit exactly 1/N; retain the two-sided errors 1/N and T/N. The
clock-one cell case has a separate harmonic correction. With preceding
mixing the fair recurrence errors are bounded by g_R and T g_R, where
g_R(N)=K_R(log N)^(-R)+(log N+7)/(6N).

The FAIR CUTOFF chain consumes clocks one and two on its lower/upper
branches. At absorption below H, its state lies in [H/2,H]. Previous
potentials give E tau<=log(2N/H)/d and E sum 1/N_j<=6/H. With iid
signs xi=-1,+1 and their sum S,
  log N_tau-log N+(L/3)J_tau=(log 6/3)S_tau+R_tau,
  E|R_tau|<=12/H.
Choose H=floor(exp((log N)^(1/4))). For m=floor(log N/d), the exact
stopping isometry E(S_tau-S_m)^2=E|tau-m|=O(sqrt(log N)) reduces the
clock limit to the iid-sign CLT. L2 sign control and L1-small errors
also give convergence of expected positive remaining clocks, needed
for the cumulative deficit. This is source averaging, not a random
model of a Collatz trajectory.

Potentials (log n)^(-3) and (log n+8)/n sum g_4 to
eta_H=O((log H)^(-3)). Two-sided unrolling therefore has cell error
o(1) and deficit error o(sqrt(log N)). Only fixed exponent R=4 is used.
Terminal values are population means at the terminal cutoff and its
remaining clock, not observations on that single integer.

If M->infinity and s/log M->infinity, the prior written minimum-clock
concentration, minimum tightness and mean q limit give Z_s(M)->b and
F_s(M)/s->b. Fix a minimum bound K first. Outside
{tau_min>s/2} union {minimum>K}, a basin-one source is censored and
a nonconvergent source differs from its limiting lost weight by at most
max_(a<=K)[W_floor(s/2)(a)-W_infinity(a)]. These are ordinary uncensored
weights. Let the source scale grow, then let K grow. The statement is
uniform on H/2<=M<=H and remaining time >=epsilon sqrt(log N); shorter
positive remaining times occupy a vanishing Gaussian interval as
epsilon->0. No exit-state/clock independence, effective minimum clock
bound, or lifetime-deficit moment/UI assumption is used.

VERIFICATION:
The full run completed 2026-10-14T17:19:56.371477Z. Three fresh
sequential builds took 3.854 seconds in aggregate, using Lean 4.33.1,
compiler 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. All 15 new roots
use only propext, Classical.choice and Quot.sound as applicable. No
native evaluation, added axioms or admitted proofs are used. The record
authenticates 17 files and reauthenticated prior cutoff-descent 12,
marked-preimage 14, clocked-progression 15 and censored-clock 20 entries.
This is not a fresh external source replay. A documentation-only review
after the run is recorded separately.

Exact Python checks:
- 1,024 independently generated prefixes, 26,624 ordinary steps;
- 25,600 cell/deficit increment checks;
- 6,400 each of even cells, odd cells/corrections, and paired deficit
  transports;
- 644 exact population identities and 700 two-sided residual bounds;
- 360 clocked unroll/cost comparisons and 1,692 node residual checks;
- 117 stopped-sign moment identities and 1,635 branch-clock balances;
- 16 bounded stopping/fixed-time isometries over 16,384 sign words;
- five exact critical-clock logarithmic brackets and 242,943 exact DP
  transitions in a separately labeled IDEAL multiplicative chain.

At clock 26, 771 actual source prefixes remain alive; no future arrival
is used to classify them. The ideal chain uses n/2 and 3n/2 on real
positive states, not the rounded cutoffs or actual Collatz. Ratios
2^8,2^16,2^32,2^64,2^128 give critical clocks 57,115,231,462,925,
certified using rational atanh bounds. Exact CDFs, missing masses and
positive-part expectations are recorded. These are finite illustrations,
not a proof of the Gaussian limit.

LIMITS AND NEXT WORK:
The Gaussian limit is written mathematics conditional on the earlier
local analytic arguments; finite replay does not certify those inputs.
No effective constants or rates, lifetime-deficit UI, or zero amplitude
is proved. With separately EXTERNAL positive predecessor density, either
critical mean-cell zero or cumulative o(N sqrt(log N)) is equivalent
to full Collatz, but both remain unproved. The coarser critical N log N
normalization vanishes automatically and is inadequate. Future work
must constrain the unknown nonconvergent mass or strengthen and audit
the analytic premises; another finite sample alone cannot establish
the zero limit. The full objective stays active.

ATTEMPT.md and README.md link the new note, theorem module and record.
No agents, installations, credentials, staging, commits or other Git
writes were used; the user's index was preserved.

## 2026-10-14: minimum-tail rigidity and the sharp sublinear barrier

The previous goal turn was progress: the critical Gaussian window and
finite checks were completed. Its 17 manifest entries were reauthenticated.
This turn tested whether improved minimum tails plus positive predecessor
density could force the unknown amplitude b to vanish. They do not yet
do so. A direct diagonal implication and a stronger comparison-map
obstruction now identify the missing scale precisely.

NEW FILES:
- docs/MINIMUM-TAIL-RIGIDITY.md
- lean/MinimumTailRigidity.lean
- verify_minimum_tail_rigidity.py
- results/minimum-tail-rigidity/{verification.json,replay.json,four logs}

CORE RESULT:
For actual attained m(n)=min_t C^t(n), m(m(n))=m(n). Hence if any
minimum a exceeds H, the tail sum at cutoff a is at least a. A uniform
linear tail budget S_H(N)<N for EVERY positive N forces m(n)<=H for
EVERY positive n. The normalized supremum U(H) has a gap: it is zero
or at least one. The generic idempotent-map argument, actual minimum
construction and the implication from a verified convergent floor are
kernel checked. This implication uses no external theorem or local
analytic mixing premise. Its uniform budget assumption is unproved.

The finite prefix m_T(n)=min_(t<=T) C^t(n) bounds m from above, and
x 1_(x>H) is nondecreasing. The kernel therefore gives the same
sufficient condition using m_(T(N)) for any prescribed clock function.
A written dyadic version needs twice the sum at 2^k to be <=2^k for
every k. The least dyadic cutoff above a has a<=2^k<2a, so the
diagonal term contradicts that half budget. No particular clock is
shown to satisfy this, and the prescribed-clock statement is not
asserted equivalent to Collatz.

WRITTEN MOMENT CONSEQUENCES:
First-moment UI of m is equivalent to a global finite bound on minima,
by the gap. Such a bound is equivalent, for any positive deterministic
integer map, to a finite collection of eventual cycles: every forward
suffix must return to a fixed finite set, so some state repeats; every
cycle contains a bounded minimum. This allows extra cycles unless the
floor is also verified. Bounded first means and finite limiting-law
moments do not imply UI. The explicit comparison J doubles powers of
two >1 and sends every other state to1. Its mean minimum has supremum3
and its limiting minimum law is delta1, but it has escaping powers of
two and linear diagonal tails >=1. J does not retain even halving and
does not satisfy the predecessor-positivity premise; keep it distinct
from the structured comparison below.

For the existing DensityCountermodel, with changed odd branch only,
the exact minimum is1 for good odd parts and v_k=2^(k+2)-1 for bad
odd parts 4j-1 with nu_2(j)=k. Binary deletion gives this classification;
the new kernel spine theorem proves every future iterate of v_k >=v_k.
Sources with this label are precisely 2^a(v_k+2(v_k+1)j), a,j>=0.
The finite per-valuation last-member bound and dyadic floor sum give
frequency <=2/v_k<=3/(v_k+1), uniformly in source cutoff. Limiting
masses are pi1=1/2, pi_k=1/(v_k+1), from the earlier written counting.
Thus uniform weighted minimum-level tail decay holds EXACTLY when
sum_k w(v_k)/(v_k+1) is finite, for any nonnegative finite weight w.
Proof: three-times-pi domination for sufficiency; finite-label density
limits and bounded means for necessity. Divergent series imply means
tending to infinity by finite partial-sum lower bounds.

Consequences: all m^p, 0<=p<1, all fixed logarithmic powers, and even
m/[log_2(m+1)]^q with q>1 have vanishing uniform tails in this map.
For q>1 the tail after spine index K is <=3/[(q-1)(K+1)^(q-1)].
For q<=1 or powers p>=1 the means tend to infinity. Half the map's
starts nevertheless escape, and it has the previously written reciprocal
predecessor floor r_a>=1/(2a). It is NOT a Collatz counterexample.
At cutoff 2^L, label v_k has exactly 2^(L-k-2) sources for k<=L-2;
there are 2^(L-1)+1 sources with minimum1. Hence the weighted mean is
(1/2+2^-L)w1+sum_(k<=L-2)w(v_k)/(v_k+1), and the exact linear mean
is L-1+2^(1-L). This supplies a direct finite identity for its divergence.

VERIFICATION:
The final full run completed 2026-10-14T17:45:28.518558Z. Four fresh
sequential Lean 4.33.1 builds took 4.184 seconds in aggregate, with compiler
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Nineteen new roots use only
propext, Classical.choice and Quot.sound as applicable. No admitted
proofs, extra axioms or native evaluation occur. The record authenticates
18 files and the prior critical-clock 17, cutoff-descent 12, and comparison 9
manifest entries. A later documentation-only review is recorded separately.

Exact replay checked:
- all 256 maps of four positive states: 1024 minimum idempotences,
  1280 budget equivalences, 640 diagonal witnesses, 6400 prefix implications;
- 8192 actual Collatz prefixes, 1048576 ordinary steps, 315 tail-monotonicity
  checks, and 360 selected population/floor/clock budgets (68 pass locally);
- 32768 comparison-map sources, 696615 directly followed steps, with tails
  classified only at 1 or the previously proved infinite escaping spine;
- 393248 uniform finite atom majorants, 14 explicit escaping diagonal
  witnesses, 83 complete atom-count comparisons, 24 exact dyadic gauge means,
  108 nearly linear tail comparisons, 256 rational square-tail inequalities;
- 4000 dyadic atom-formula comparisons and 68 exact linear-mean formulas,
  including cutoff 2^1024; these are arithmetic source-count formula
  evaluations, NOT trajectory enumeration through 2^1024;
- 32768 bounded-first-mean checks for the separately defined map J.

At comparison cutoff 32768, 16383 sources escape by the explicit model
classification; its linear mean is 229377/16384. At cutoff 32767 and
floor 32766, its tail sum is exactly 32767, giving normalized diagonal 1.
No actual Collatz finite prefix is labeled divergent or assigned its
unknown future minimum.

PRIMARY-SOURCE CHECK:
The current ProofAtlas natural-density endpoint still has growing
thresholds, and its predecessor endpoint still has target-dependent
positive constants. Those checked quantifiers do not supply the needed
linear budget. No new external theorem, source installation or external
Lean replay was used; the new rigidity and comparison arguments are
independent of these external inputs.

NEXT AND LIMITS:
All fixed logarithmic moments, fractional moments below one, and even
the nearly linear comparison weights cannot by themselves close this
route. Controlling constants while changing exponents is also unproved.
The useful stronger target is an actual uniform linear minimum-tail
budget below one at a verified floor (or the dyadic half budget), or
additional 3n+1 arithmetic that excludes the comparison behavior. These
are not supplied by the current cutoff recurrence. The nonconvergent
mass b and full Collatz remain unresolved, and the goal stays active.
ATTEMPT and README were updated. All processes are terminal; no agents,
installs, credentials, staging, commits or other Git writes were used.

Final read-only Git inspection found HEAD 7506094 ("updated collatz")
with an empty staged diff. The earlier research files are now tracked;
only this milestone's new files and the three updated summaries remain
in the worktree. The index changed during the run from the initial
f852ffcf0641b616658fa46c94d16cb37a86db08b4014fb414a2c4a2fa426a63
to cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.
Preserve that current state. The assistant issued no staging or commit
commands. Final Git reads used GIT_OPTIONAL_LOCKS=0.

## 2026-10-14: exact minimum-cap transport and zero-future-cap witnesses

The user asked to continue after an accidental interruption. The active
unbounded Collatz research goal was retained. The previous linear-tail
rigidity milestone's 18 manifest entries and cutoff-descent's 12 entries
were reauthenticated. The proposed improvement was to keep the negative
odd-source truncation loss when comparing the weighted minimum population.
That term is exact and useful, but cannot by itself pay all positive
finite sampling errors. This is progress in auditing this route, not a
resolution of the conjecture or a claim that all stronger routes fail.

NEW FILES:
- docs/MINIMUM-CAP-TRANSPORT.md
- lean/MinimumCapTransport.lean
- verify_minimum_cap_transport.py
- results/minimum-cap-transport/{verification.json,replay.json,five logs}

KERNEL RESULT:
For the finite prefix minimum m_t, the even one-step identity and odd
two-step capped identity hold for all natural clocks and sources.
For g_H(y)=y1_(y>H), d_H(s,y)=g_H(y)-g_H(min(s,y)) equals g_H(y)
if s<=H and max(y-s,0) otherwise. It is nondecreasing in y. Since
m_t decreases with t, each cap and its population sum D decrease in t.
Any zero cap sum remains zero at EVERY future time, without knowing
any future iterate or global minimum. Source1 has zero tail for H>=1.

For N>=3, a=N//2, X=(N-1)//2, c=3X+2, the exact population identity is
  sum_(n<=N) g_H(m_(t+2)(n)) + D_(H,t)(X)
    = sum_(n<=a) g_H(m_(t+1)(n)) + sum_(n<=X) g_H(m_t(3n+2)).
The Lean module proves it for both N=2X+1 and N=2(X+1), including
the extra even endpoint in the latter. Normalization gives the written
residual formula R=(X/N)delta-D/N-Q, with Q>=0 the two coefficient
deficits from the fair half-weighted child means. No sign is discarded.

SMALL ACTUAL-COLLATZ OBSTRUCTION:
At H1,t4,X1,N3,c5, child tail values are [0,0,3,0,2]. The parent
clock6 tail sum through3 is2; the even clock5 tail sum through1 is0.
The single progression term is2, so delta=1 and fair residual R=1/6.
The cap is zero because m_4(5)=2<=3. All later caps at this H,X
are therefore zero. Closed sums and positive discrepancy are kernel
decide proofs; the cross-multiplied residual sign is 10*2>15*0+3*5.
The theorem small_future_cap_obstruction allows every finite future
cap sum with arbitrary natural weights. All real nonnegative weights
and infinite sums also give zero termwise, as a written consequence.
No nonnegative current/future cap charge at this SAME floor/cutoff
can bound those strictly positive errors for all finite clocks.

LARGER EXACT PYTHON WITNESSES:
The time-major census follows 98306 actual sources through clock256.
Its schedule uses k4..16, parent clocks factor*k for factors4,6,8,10,12,16,
both N=2^k and N=2^k+1, and floors1,16,64,256,1024: 780 rows in all.
Fifteen rows have strictly positive fair residual with cap exactly zero.
At H64,parentT256,tailt254, the adjacent cutoffs65536 and65537 share:
  parent tail sum33999, even child sum182,
  full upper child sum100001, progression sum33817, cap sum0.
For N65536: a32768,X32767,c98303,
  delta=6797112/460156343, R=47479783/6442385408.
For N65537: a=X32768,c98306,
  delta=23790617/1610645504, R=778747256741/105556874395648.
The zero cap persists at every later clock by the generic kernel
implication applied to the Python finite equality. Keep those scopes
separate; the large equality is NOT a kernel census.

At the dyadic cutoff65536, the prefix tail sum33999 exceeds32768.
This rejects the sufficient dyadic half-budget at the specific floor64
and clock T(2^k)=16k. It does NOT refute S<N at this cutoff (it passes),
another floor/clock, or the desired infinite-minimum estimate.
No alive prefix is labeled nonconvergent or assigned its future minimum.

WRITTEN WEIGHTED-ERROR LIMIT:
For integer y<=c, g_H(y)=H1_(y>H)+sum_(s=H..c-1)1_(y>s), for H<=c.
Therefore the weighted sampling error is H times the threshold-H error
plus the sum of the threshold errors through c-1. Even granting a
uniform bound epsilon on every bounded-label discrepancy at this clock,
absolute summation only gives c*epsilon. With c~X and a fixed arbitrary
logarithmic power this is O_R(X/log^R X), not a uniformly small linear
error. This is only what this bound proves; cancellations or a stronger
weighted comparison are not ruled out. No new uniform finite-clock
threshold mixing claim was used or asserted.

VERIFICATION:
The full run passed 2026-10-14T18:12:29.976288Z. Five fresh sequential
Lean4.33.1 builds took 11.754 seconds in total using compiler
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Twenty-two new audited roots
use only propext and Quot.sound where needed; the small closed sums
and sampling sign use no axioms. No added axiom, admission or native
computation is used. The record authenticates15 files, prior rigidity18
and cutoff12 hashes, with a separately recorded later documentation-only
review adding the adjacent dyadic witness and final counts.

Independent integer/rational replay checked:
- small actual census through source3074 and clock130:399620 steps
  and the same number of prefix-monotonicity comparisons;
-132096 individual even and132096 individual odd minimum transports;
-660480 scalar cap formulas and655360 individual cap-monotonicity checks;
-25800 small population identities and280 weighted layer-cake identities;
-large actual census:25166336 ordinary steps and780 population identities;
-independent per-source replay:10542123 ordinary steps,98306 sources,
  all294918 minimum values at clocks254,255,256 compared individually.
The second traversal stops early only on an already attained minimum1;
it uses no memoized arrival table or presumed eventual convergence.
The large witnesses are finite Python checks, not asymptotic evidence.

NEXT AND LIMITS:
Past-cap accounting, signed cancellation over clocks or cutoffs,
an added boundary term, eventual large-scale estimates, and direct
infinite-minimum estimates are still possible. The next useful target
is a bound on the entire signed residual or genuinely weighted
progression control strong enough for the all-cutoff linear-tail budget.
The cap-only current/future route is excluded at finite clocks. The
needed budget and b=0 remain unproved; the full goal stays active.

ATTEMPT and README were updated without altering prior research files.
No agents, installations, credentials, staging, commits or other Git
writes were used. All run processes finished. The index remained
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8
at the most recent read-only inspection; Git reads use
GIT_OPTIONAL_LOCKS=0 to preserve the user's index.

## 2026-10-14: the persistent linear boundary and its leading cancellation

The previous goal turn was progress: exact minimum-cap transport and
zero-future-cap witnesses were completed. The cap15, cutoff12 and
critical-clock17 manifest entries were authenticated. This turn examined
the FULL signed recurrence, including the finite-clock boundary that
bounded-observable arguments can otherwise conceal. The new result also
supplies an elementary route to a vanishing CLOCKLESS boundary, without
the previous analytic mixing premise. Full Collatz remains unresolved.

NEW FILES:
- docs/MINIMUM-LINEAR-BOUNDARY.md
- lean/MinimumLinearBoundary.lean
- lean/MinimumLinearBoundaryFinite.lean
- verify_minimum_linear_boundary.py
- results/minimum-linear-boundary/{verification.json,replay.json,ten logs}

KERNEL STRUCTURE:
The auxiliary cutoffs are a=n//2 and b=3((n-1)//2)+2, chosen fairly.
The lower branch consumes one ordinary clock and the upper two. Stop
when cutoff<=H or remaining clock<=1; finite depth T is sufficient.
For any rational function f, the terminal term plus signed residual
occupation equals f at the root. For the actual prefix-tail mean F,
write this as F_T(N)=B_T(N)+S_T(N).

Let ell(n) be binary length, ell(0)=0. Both cutoff maps are monotone.
At the maximal source 2^(k+3)-1, the eight three-step leaves are
p-1, three copies of3p-1, three of9p-1, and27p-1, p=2^k. Their
total bit length is <=8k+23. Hence P^3ell<=ell-1/8 for n>=4.
The rational potential V=ell+Pell+P^2ell satisfies PV<=V-1/8 and
0<=V<=3ell for n>=2. Exact finite stopping yields E sigma<=24ell(N).
This proves a logarithmic occupation bound without real logarithms.

In contrast, a+b=2n-1_even gives the exact stopped size identity
E N_sigma=N-(1/2)E(number of active even cutoffs), hence
E N_sigma>=N-12ell(N). The actual clock-zero/one tail means satisfy
F_s(N)>=3N/8-H. This follows from exact sums of m_1, and g_H(y)>=y-H.
The kernel consequently proves at every clock T, for H>=3,N>=2,
  B_T(N)>=3N/8-(9/2)ell(N)-H.
The auxiliary cutoff terminal family can fail uniform integrability
despite almost-sure absorption. This is not a statement that actual
Collatz minimum UI fails.

FULLY KERNEL-CHECKED FINITE EXAMPLE:
For H4,N256, B_T>=103/2 at EVERY T. The finite module supplies literal
paths for sources256 down through1, with10971 ordinary edges and
longest floor-hit clock125. The generic checker verifies every edge,
fuel bound and final value<=4. Kernel reduction then proves the
clock128 prefix-tail sum through256 is0. Prefix monotonicity extends
this to all T>=128, and exact unrolling gives S_T(256)<=-103/2 at every
such T. Native evaluation and its extra axiom are not used.

Initial direct reductions of deeply nested prefix minima were stopped
because they were expensive; literal path certificates avoid repeated
orbit-expression reduction. A temporary debugging build identified
and fixed simplifier issues. Only the final fresh passing builds below
are verification evidence; temporary files remain outside the repo.

WRITTEN LEADING LAW:
For c0=1/2,c1=3/8 and c_T=(c_(T-1)+3c_(T-2))/4,
  c_T=3/7+(-3/4)^T/14, with3/8<=c_T<=1/2.
The local residual of phi_T(n)=c_T*n is c_(T-2)/2 at even n and
(c_(T-1)-c_(T-2))/4 at odd n. Its absolute value is <=1/4.
The actual short-clock/floor terminal values differ from phi by <=H+1.
Finite unrolling and the kernel occupation bound therefore give
  |B_T(N)-c_T*N|<=H+1+6ell(N), uniformly in T.
This sharper estimate and the limit assembly remain written arguments;
the exact finite coefficient and rounding identities are replayed.

ELEMENTARY FINITE-PARITY ESTIMATE:
Each length-k shortcut parity word occurs once mod2^k. For the induction,
the lifts r and r+2^k share their first k parities, and their kth images
differ by the odd number3^j, so their next parities are opposite.
The existing CollatzAffine affine identity was freshly rebuilt.
The affine slope is A=3^j/2^k; its correction is <=(3/2)^k-1.
Choose rational weights e=17/24,o=49/40, q=(e+o)/2=29/30.
Their squares exceed1/2 and3/2, respectively. For w=e^(k-j)o^j,
w^2>=A and min(1,A)<=w. Since k shortcut steps take at most2k ordinary
steps, m_T(n)<=n*w+(3/2)^k for T>=2k. Counting residues gives
  F_T(N)/N <=(1+2^k/N)q^k+(3/2)^k/N.
If N>=2^k this is <=2q^k+(3/4)^k. Choose
k=min(floor(T(N)/2),floor(log_2 N)); any T(N)->infinity gives
F_(T(N))(N)=o(N), uniformly in the floor. This is only an o(N^2)
unnormalized tail sum. For T>=2floor(log_2 N), it also gives a weak
sublinear power mean bound with exponent1+log_2(29/30)<1; the residue
endpoint error grows when k is increased far beyond log_2 N.

Combining this with the boundary profile, for fixed H>=3 and any
T(N)->infinity, B_(T(N))(N)/N->3/7 and S_(T(N))(N)/N->-3/7.
The constant3/7 concerns the exhausted-clock boundary, not the unknown
nonconvergent mass b. The finer remainder needed for F_T(N)<1 is open.

CLOCKLESS ROUTE:
The same parity bound applies to actual global minima m<=m_(2k), so
G_H(N)=mean m1_(m>H)=o(N) independently of prior analytic mixing.
For clockless stopping at floor or depth J, sublinearity gives
  E G_H(N_(tau wedge J))<=epsilon*N+M_K*Pr(tau>J),
where G_H(n)<=epsilon*n aboveK and M_K=max_(n<=K)G_H(n).
Absorption follows from the dyadic occupation bound. Let J grow, then
epsilon decrease: this boundary vanishes. G_H(N) is thus the limit of
the finite expected signed residual sums. An expectation/infinite-sum
interchange is NOT asserted. No external theorem or earlier analytic
mixing premise is needed for this written argument.

VERIFICATION:
The final full run passed 2026-10-14T19:15:43.895645Z. Ten fresh
sequential Lean4.33.1 builds took10.649 seconds, with compiler
819816b2e0a3bf405af45ae5c7af2491d8f5bee6. Thirty new roots use only
standard propext, Classical.choice and Quot.sound where applicable.
The finite path and persistence roots use only propext and Quot.sound.
The record authenticates26 files and the prior cap15, cutoff12 and
critical17 hashes. A later documentation-only review records the
sharper N>=2^k choice and final counts, without changing tested code.

Independent exact checks include:
- 66181 cutoff size/rank checks,66180 potential upper bounds,66178
  three-step rank/potential drifts, including645 huge-dyadic arithmetic
  cases up to2^1024 (NOT Collatz orbit enumeration there);
- 10971 literal path edges, a separate32768-step replay of all256
  sources through clock128, and12288 short-clock formulas/lower bounds;
- 257 leading coefficients and66045 exact profile rounding identities;
- 32767 complete residue words through shortcut length14,425986 shortcut
  steps,120 rational word-majorant sums and comparisons;
- 83981 actual Collatz sources through clock32:2687392 ordinary steps,
  9451 queried prefix population values;
- 78 forward/recursive signed cutoff-tree comparisons,9724 active and
  3145 terminal states,637 normalized prefix majorant comparisons;
- 8 longer arithmetic cutoff trees,58063 memoized cutoff states total,
  and20743 exact state checks of the separately identified ideal tilt.
No floating-point proof decisions occur. Extremely large rational
outputs are saved as tagged outward rational enclosures with exact
binary digests; all comparisons use the original exact fractions.
An initial output write exceeded Python's decimal integer conversion
limit; that reporting issue was fixed and the full final replay passed.

NEXT AND LIMITS:
The first-order signed cancellation is now identified. It cannot by
itself enforce the subunit uniform linear-tail budget. A viable next
step must bound the finer remainder or the clockless signed residual;
it must not discard the exhausted-clock boundary or infer UI from
vanishing clock-boundary probability. Full Collatz, minimum UI and
b=0 remain unproved. The goal stays active.

ATTEMPT and README link the new note and verification. All processes
are terminal. No agents, installations, credentials, staging, commits
or other Git writes occurred. The most recent index hash is still
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8;
Git reads use GIT_OPTIONAL_LOCKS=0.


## 2026-10-14 — Absolutely integrable clockless Green kernel

Classification: progress. The preceding linear-boundary milestone left
an expectation/infinite-sum interchange open. This turn supplies a
quantitative absolute-integrability argument without analytic mixing.
The subunit budget and the active full-Collatz goal remain unresolved.

NEW FILES:
- docs/MINIMUM-GREEN-KERNEL.md
- lean/MinimumGreenKernel.lean
- verify_minimum_green_kernel.py
- results/minimum-green-kernel/{verification.json,replay.json,*.log}

RATIONAL GAUGE AND KERNEL SCOPE:
For q=29/30 and k=floor(log2 n), V(n)=q^k(2^k+14n)/15, V(0)=0.
The fair auxiliary cutoff operator has PV<=rho V for every n>=2,
rho=1704/1711, gap7/1711. At positive n, V>=1 and V<=nq^k.
The proof uses exact dyadic cell locations and two integer inequalities.
For source2p<=n<4p, lower childa and upperchildb:
  if b<=4p:295(88p+420a+406b)<=17040(2p+14n);
  if b>=4p:295(2132p+6300a+5887b)<=255600(2p+14n).
Odd/even rounding is retained. This is not a Collatz orbit contraction.

Generic finite bounds are kernel theorems with the explicit premise
0<=f<=3V and, for telescoping, f=0 at the floor H>=1:
  Pr(tau>J)<=rho^J V(N),
  0<=f(N)-E sum_(j<J,j<tau)(f-Pf)(N_j)<=3rho^J V(N),
  E sum_(J<=j<J+K,j<tau)|f-Pf|(N_j)<=(5133/7)rho^J V(N).
The sharper absolute constant uses |f-Pf|<=3V from nonnegativity;
the initial triangle estimate3(1+rho)V was unnecessary.
Occupation splitting and geometric sums are also kernel checked.

WRITTEN ASSEMBLY:
The prior elementary parity argument gives
G_H(N)<=Nq^k+(2q)^k+(3/2)^k<=q^k(N+2*2^k)<=3V(N),
with k=floor(log2 N), by bounding actual global minima with the
finite prefix at2k. This all-population assembly is NOT a new Lean
theorem; no axiom hides it. It needs no external density or mixing.
Monotone convergence applied to the absolute occupation gives L1
convergence of signed partial sums. Therefore
G_H(N)=E sum_(j<tau)(G_H-PG_H)(N_j), with the same infinite absolute
tail bound and signed truncation error. This closes the gap at fixed N.
The gauge grows with N, so it does not imply the all-cutoff subunit
budget. The general interpolation constant is
rho_r=1/(2r)+3r/(2(r+2)); at r=2 it equals1. The linear endpoint
cannot be obtained with a finite Green constant.

LEAST-COUNTEREXAMPLE DIAGNOSTIC:
Kernel proofs show m(A)=A, all positive smaller minima1, and
G_(A-1)(A)=1 exactly if A is a least counterexample.
A residual upper bound R_(A-1)<=eta V, eta>=0, would force at
every finiteK:
  1<=[3rho^K+eta(1-rho^K)/(1-rho)]V(A).
This formal implication explicitly assumes the majorant G<=3V.
The written limit gives
sup_(n>=A) max(R_(A-1)(n),0)/V(n)>=7/(1711V(A)).
No attained maximum is asserted. No independent residual bound
contradicting this lower bound is proved.

VERIFICATION:
Full run passed2026-10-14T19:46:20.762332Z.
Ten fresh sequential Lean4.33.1 builds took4.666sec, compiler
819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All34 new roots use only propext, Classical.choice and Quot.sound;
no sorry/native finite axiom. Manifest hashes24files and validates
all26prior linear-boundary hashes. Documentation-only review after
the run added counts and restored inline math formatting; tested
sources, logs, and exact replay were not changed.

Exact Python checks:
-66696gauge/contraction bounds,22554low-cell and44142high-cell;
-1161huge dyadic/breakpoint cases through exponent1024, arithmetic
 only rather than orbit censuses;257geometric identities;
-16589actual sources through ordinaryclock28,464492ordinary steps
 in each of independent time-major/source-major traversals;
-248835matching prefix-minimum snapshots and49767mean majorants;
-36cutoff profile trees,468forward/backward depth comparisons,
 3621active residual checks,3276absolute-tail windows,15954recursive
 states. Two synthetic profiles are labeled separately from the
 actual finite profile T(N)=2floor(log2 N).
Finite alive prefixes are never identified with global minima.
No floating-point proof decisions occur.

NEXT:
Seek an independent actual signed/positive residual estimate that
would force the subunit minimum-tail budget. The current identity
alone, because R is defined from G, is not such an estimate.
No new external theorem, installation, credentials, agents, staging
or commits were used. All jobs are terminal; the goal remains active.
ATTEMPT and README link the result. Git reads use
GIT_OPTIONAL_LOCKS=0; the index hash remains
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.


## 2026-10-14 — Unbounded tails at fixed additive logarithmic clocks

Classification: progress. The preceding Green-kernel turn closed the
absolute-integrability gap. This turn investigated uniformly small
residuals for its computable finite-prefix approximants and found a
kernel-certified obstruction. It does not refute the global-minimum
residual route. Full Collatz remains unresolved and the goal active.

NEW FILES:
docs/MINIMUM-CLOCK-BARRIER.md; lean/MinimumClockBarrier.lean;
verify_minimum_clock_barrier.py; results/minimum-clock-barrier/.

ALL-INDEX ORDINARY PREFIX:
For q>=1, n=2^K q-1, the first2K ordinary steps stay>=n and
C^(2i)n=2^(K-i)3^i q-1 for0<=i<=K. Kernel prefix concatenation and
2C(x)>=x show that an endpoint>=2^s n stays>=n for s further steps.
Thus, for EVERY q>=1,K,T,
  2^T<=6^K => m_T(2^K q-1)=2^K q-1.
The proof includes ordinary odd intermediates, endpoint correction,
and the caseT<=2K. K=0 can give source0 in the general arithmetic
theorem; all counterbudget sources are positive. No infinite orbit
or eventual convergence is inferred from these surviving prefixes.

POPULATION OBSTRUCTION:
For periodM>=2 and Q surviving class members Mq-1,1<=q<=Q, aboveH,
  sum tail throughMQ >= M Q(Q+1)/2-Q,
  mean tail >=(Q+1)/2-1/M>=Q/2.
The injection into the full source sum and exact arithmetic are
kernel checked. Put
  M=2^(4j+2L), Q=2^j,N=2^(5j+2L), T_L(N)=L+2floor(log2 N).
Then T_L(N)=10j+5L and the source class survives because
32^(2j+L)<=36^(2j+L). For j>=1,H<M-1,
  A_(H,L)(N)>=2^(j-1).
For EVERY fixed H,L this prefix mean is unbounded in N, so its strict
all-cutoff subunit budget fails. A finite floor chosen as a function
of L cannot avoid the same universal statement.

NECESSARY CLOCK THRESHOLD:
If a strict prefix-tail budget holds at2^(d+1), d>=1,H<2^d-1,
then6^d<2^T. Otherwise just the two sources2^d-1,2^(d+1)-1 supply
a sum>=2^(d+1). This integer implication is kernel checked.
WRITTEN: gamma=log2 6; with K=ceil(T/gamma), period2^K,
Q=2^(d-K), the lower mean atN=2^d is >=(1/4)2^(d-T/gamma) when
the floor and endpoint conditions hold. Therefore every fixed
0<c<gamma in T=floor(c log2 N)+L yields a polynomially growing tail
mean along dyadic N. Any successful strict budget must have
T(2^d)>gamma(d-1), and an extra clockL(N) above2log2 N must satisfy
L(2^d)>(gamma-2)d-gamma for all sufficiently large d.
No coefficient>=gamma, faster clock, or global-minimum estimate is
excluded. The elementary growth mechanism is not claimed novel.

POINTWISE AND RESIDUAL SCOPE:
Kernel: A_(H,L)(N) is nonincreasing in L and eventually equalsG_H(N)
at each fixed N. A finite sum of the attained global-minimum clocks
of sources1..N is a valid settling threshold, without Collatz; this
is not an effective known time bound.
WRITTEN: the elementary majorant0<=A_(H,L)<=3V is uniformL because
T_L>=2floor(log2N). The new residual uses each child's OWN T_L,
not the parent clock minus1/2 of the older finite-clock recurrence.
For H>=1, Green unrolling givesA_(H,L)=E sum R_(H,L), and both
signed and positive residual occupation are unbounded overN for
every fixedL. The finite lower bound
2^(j-1)-3rho^J V(N) is a kernel implication with explicit majorant.
For each fixedN, pointwise residual settling and the6V envelope
give E sum|R_(H,L)-R_H|->0 by written dominated convergence.
It has no uniform-in-N rate. If full Collatz holds, G_H=0 forH>=1,
yet the finite approximants remain unbounded for every finiteL.
Unconditionally the difference A-G is not assigned a false lower
bound: the missing global G is still unknown.

CONVERGENT WITNESS:
At H64,N1024,T20 the sources255,511,767,1023 alone supply2556.
Thus mean>=639/256. Their ordinary hitting clocks to1 are47,61,59,62.
The subset lower bound is kernel checked; the four hitting statements
use decide +kernel and their root is axiom-free. The Python replay
also checks they are first arrivals. This kernel certificate covers
four sources, not the whole interval.
The complete Python prefix census has tail sum98058 atH64,N1024,T20.
AtH64,L1,j3,N131072,T35, the8class sources contribute589816; the
complete tail sum is889202768. Both are finite-prefix quantities.

FINAL VERIFICATION:
Passed2026-10-14T20:10:10.422631Z. Eleven fresh sequential Lean4.33.1
builds took5.426sec, compiler819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
All30new roots pass with only standard logical axioms as applicable;
the closed hitting root uses none. No native finite axiom or sorry.
The manifest hashes26files and authenticates24prior Green hashes.
The earlier29-root run was superseded after adding the exact necessary
clock threshold. Later documentation-only review added final counts;
tested code, logs and replay retain their hashes.

Independent exact replay:
1596selected sources,501492ordinary steps,503088prefix-time checks,
100908closed even-clock formulas, with odd-prefix lengths through4096;
418large-family arithmetic cases (cutoff exponents through7168),
256necessary dyadic-clock checks; these enormous populations are NOT
enumerated intervals.
The complete census131072sources throughclock35 performs4587520
ordinary steps in each traversal order and786432minimum comparisons.
100enumerated class-source checks support22complete population bounds.
The four kernel witnesses have229independently replayed edges.
A separate1024source fixed-cutoff check performs282624steps and56
monotonicity/settling comparisons; every source reaches1 and the
maximum first-arrival clock is178. This larger interval statement is
Python evidence, not a new Lean interval certificate.

HOUSEKEEPING AND NEXT:
Repaired two Markdown links in the preceding Green note that its
inline-math formatting pass had accidentally escaped; only its
documentation hash/review metadata changed, before the new verifier
authenticated it. No earlier tested code or replay was altered.
ATTEMPT, README and top memory now link this milestone.
Next seek an actual global-residual bound, or extra clock that grows
with cutoff beyond the necessary threshold. Fixed additive shifts
cannot make the positive residual occupation uniformly small.
No external theorem, agents, installs, credentials, staging, commits,
or other Git writes occurred. All processes are terminal. Index SHA256:
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.
Git reads use GIT_OPTIONAL_LOCKS=0.


## 2026-10-14 — Second growing block at the critical clock

Classification: progress. Continued after the accidental interruption.
The preceding all-odd residue calculation excluded coefficients below
log2 6, but did not decide equality. A new constructive exponent lift
now excludes every fixed additive correction at equality. This is a
finite-prefix budget obstruction; the Collatz goal remains active.

NEW FILES:
docs/MINIMUM-CRITICAL-CLOCK-LIFT.md;
lean/MinimumCriticalClockLift.lean;
verify_minimum_critical_clock_lift.py;
results/minimum-critical-clock-lift/.

CONSTRUCTION AND KERNEL SCOPE:
Let a0=0 and qj=(9^aj+7)/2^(j+3). Set a_(j+1)=aj for even qj,
otherwise aj+2^j. Induction proves aj<2^j and the quotient integral.
The elementary identity 9^(2^j)=1+2^(j+3)*(2cj+1) supplies the
parity flip; its witness update is cj+2^(j+1)*(2cj+1)^2.
Set Kj=2*(aj+2^j), Nj=2^Kj-1. Then
2^(j+1)<=Kj<2^(j+2), floor(log2 Kj)=j+1, and
3^Kj+7=2^(j+3)*q for a positive integer q.

For j>=2, the ordinary path has Kj odd shortcut steps, then three
halvings, then j more odd shortcut steps. Its bridge is
3^Kj-1=8*(2^j*q-1). The intermediate minimum remains Nj, because
3^Kj-1>=8*(2^Kj-1), already true for K>=6.
After B=2*(Kj+j)+3 ordinary steps, endpoint z=3^j*q-1 satisfies
3^(Kj+j)*Nj<=2^(Kj+j+3)*z. A generic scaled-endpoint buffer proves
2^T<=6^(Kj+j) implies m_T(Nj)=Nj. The single source at its own
cutoff gives tailSum>=Nj at every floor H<Nj. A strict budget forces
6^(Kj+j)<2^T. All these are kernel statements, not sample inferences.

The exact integer clock floor(log2(6^floor(log2(N+1))))+L equals
floor(log2(6^Kj))+L at Nj. For j>=max(2,L), its prefix retains Nj.
Kernel: for EVERY H,L,b there exists N>b whose tail sum at this clock
is >=N. Written comparison transfers this to the usual critical clock
floor((log2 6)*log2 N)+L at those same cutoffs.

WRITTEN LOG-LOG CONSEQUENCE:
With gamma=log2 6, log2 Nj<Kj and log2 log2 Nj<j+2 imply the necessary
T(Nj)>gamma*log2 Nj+gamma*log2 log2 Nj-2gamma.
Thus any fixed c<gamma in
floor(gamma*log2 N+c*log2 log2 N)+L fails the strict budget at all
sufficiently large family cutoffs. The real-log comparison is written;
its integer premise is formal. No claim that critical-clock means are
unbounded, no exclusion of every larger leading coefficient, and no
exclusion of the full gamma log-log correction with arbitrary constant.
No conclusion about actual global minima or future divergent behavior.

VERIFICATION:
Final full run: 2026-10-14T20:29:58.476105Z. Twelve fresh sequential
Lean4.33.1 builds in6.055sec;21 audited roots,28 file hashes,26 prior
clock-barrier hashes authenticated. Two closed roots are axiom-free;
other dependencies are standard logical axioms only. No native finite
axiom, sorry, new external theorem, or analytic mixing premise.
Documentation-only final count review preserves all tested code,
replay and build hashes and records its own timestamp in the manifest.

Independent Python modular checks for j0..1024:1025 each of the
lift congruence, top-bit identity, block bounds, and second congruence.
Full finite exponent ranges j0..12 enumerate8191 residues and compare
13 selected lift exponents. Large indices do not construct their
astronomical source integers or census intervals.
Actual ordinary replays:13 sources j2..14,186810 steps,186823
prefix-time checks,208 exact endpoint comparisons,117 shifted-clock
inequalities. Largest actually iterated source has33966bits.
Nine separate convergence replays j2..10:80543 ordinary steps.
N2=16383 and N3=1073741823 reach1 at159 and449, also checked by
axiom-free kernel reduction;608 replay edges. First descents70 and197
and first-arrival minimality are Python claims. The entire infinite
family is not proved convergent.

NEXT AND HOUSEKEEPING:
Investigate faster cutoff-dependent clocks or actual global residuals.
The extra log-log term is necessary along this family, not sufficient
for the uniform subunit estimate. No external blocker is present.
ATTEMPT, README and top memory contain the new result and preserve
kernel/written/Python distinctions. The prior clock note and its
manifest remain unchanged; the new note explicitly strengthens it.
No agents, installations, credentials, staging, commits, or other Git
writes occurred. All processes are terminal. Index SHA256 remains
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.
Git reads use GIT_OPTIONAL_LOCKS=0.


## 2026-10-14 — Actual population bound and unconditional finite Green estimates

Classification: progress. The previous clock-lift turn was also progress.
Rather than only extend necessary clock obstructions, this turn closed
an explicit kernel premise in the actual-global-minimum residual route.
It additionally improved the population estimate by retaining the exact
period-average affine correction. Full Collatz remains unresolved.

NEW FILES:
docs/MINIMUM-POPULATION-MAJORANT.md;
lean/MinimumPopulationMajorant.lean;
verify_minimum_population_majorant.py;
results/minimum-population-majorant/.

UNIVERSAL KERNEL ESTIMATE:
For r=29/15,k=floor(log2 N),T>=2k and every H,
G_H(N)<=F_(H,T)(N)<=2*r^k+k/2 for N>0.
At N=2^k the bound is r^k+k/4. The proof uses integer weights
W=85^(k-a)*147^a with scaleQ=120^k. Their square dominates the
affine slope:3^a*Q^2<=2^k*W^2. Periodicity and the exact endpoint
parity flip prove all-depth mass sumW=232^k. The existing numerator
mass theorem gives4*sumB=k*4^k, hence average correction B/2^k=k/4.
No new parity-model or external density premise is used.

For the actual ordinary prefix minimum, the integer pointwise bound
is M*Q*m_T(n)<=M*n*W+Q*B, M=2^k. Summing the positive source range
and using at most two periods gives2*Q*S<=4*N*232^k+Q*k*M.
One period at N=M gives4*Q*S<=4*M*232^k+Q*k*M.
All endpoint accounting and rational cancellations are kernel checked.
The global-minimum bound follows from m<=m_T, without limits or an
assumption that any uncomputed source reaches1.

DISCHARGED PREMISE AND REMAINING GAP:
The same module provesV(N)>=r^k andk/2+1<=r^k, so the former written
population input0<=G_H<=3V is now an unconditional kernel theorem.
All adaptive prefix shifts L>=0 satisfy the same majorant.
The finite global-residual truncation, absolute-tail and adaptive
occupation lower estimates now need no extra population premise.
The least-counterexample diagnostic still retains its independent
positive-residual upper hypothesis. No useful small eta is proved.
Infinite expectation/occupation assembly remains written measure theory.
The real exponent log2(29/15)<1 gives sublinearity, not a uniform
subunit normalized mean; the bound itself grows with the cutoff.

PRIMARY-SOURCE REVIEW:
Read Tao arxiv1909.03562v5, theorem1.3 and remark1.4, at
https://arxiv.org/html/1909.03562v5#S1.SS1 . Its logarithmic-density
floor control does not imply the needed uniform linear-tail estimate.
This is context only, not an external proof dependency. Broad search
results claiming complete proofs were not accepted as evidence.
No novelty claim is made for the elementary parity-weight mechanism.

VERIFICATION:
Final full run2026-10-14T20:49:42.733776Z:21 fresh sequential builds
in9.643sec under Lean4.33.1,36 audited roots. All axiom reports are
standard logical axioms or empty; no native finite axiom or sorry.
47hashed files, with28 hashes authenticated from the latest critical
clock manifest and26 from the binary-image manifest. Documentation
count review leaves all tested code, logs and replay hashes intact.

Independent exact Python:
-131071full-period residue/depth pairs and1966082shortcut steps;
 17exact weight sums,17exact correction sums,17binomial cross-checks.
-196590actual pointwise majorants,2883468additionalshortcut steps.
-65536complete positive sources through ordinary clock32 in two
 traversal orders,2097152steps each,1114112minimum comparisons.
-262144population bounds at EVERY cutoff1..65536 for H0,1,16,64;
 262144gauge comparisons and68sharperdyadic bounds.
-216finite Green depth comparisons and576absolute-tail windows for
 computable adaptive PREFIX profiles. Not unknown global residuals.
-261large-index scale/correction checks through4096, arithmetic only.

Example H64,N65536,T32 actual prefix tail mean252697831/65536.
This is a finite prefix, not a computed global minimum mean.
All finite evidence and kernel/written scopes are separate in the note,
verifier and manifest. ATTEMPT, README and the top memory link the result.

NEXT: estimate actual signed/positive residuals independently strongly
enough to force the subunit budget. Investigate whether additional arithmetic beyond the first complete
parity period can improve this averaging argument enough. Earlier
clock obstructions remain valid.
The goal stays active. All jobs are terminal. No agents, installations,
credentials, staging, commits, or other Git writes occurred. The index
SHA256 is unchanged:
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.
Git reads use GIT_OPTIONAL_LOCKS=0.


## 2026-10-14 — Attained minimum roots and the exact scope of cap budgets

Classification: progress after resuming the interrupted investigation.
The previous population-majorant result was reauthenticated. Examination
of the least-counterexample residual did not yield a useful small eta:
its upper auxiliary cutoff near1.5A still contains uncontrolled minima,
and the universal population estimate is too large to close that gap.

NEW FILES: docs/MINIMUM-ROOT-SPINE.md; lean/MinimumRootSpine.lean;
verify_minimum_root_spine.py; results/minimum-root-spine/.
The full result and exact scope are summarized at the top of this memory.

The new module proves actual global Bellman/parity transport and constructs
successive self-minima on the original orbit. The crucial distinction is
kernel checked: accumulated global caps are bounded iff the orbit
eventually repeats, whereas finite caps telescope to the moving endpoint.
Source1 already gives finite totals0,3,1 forever and global totals0.
No universal bound on actual caps and no exclusion of nontrivial cycles
was obtained. Positive cap support means self-minimal and nonperiodic at
that point; it does not by itself exclude later entry into a larger cycle.

Population bounds yield kernel root-shell counts and a finite reciprocal
majorant118. The real reciprocal sum over all positive roots is at most119
by a written comparison/limit. The written count-growth consequence gives
a superlinear power lower bound in the root index; its ordinary clocks
remain unbounded, and sparse infinite roots remain compatible. These are
necessary restrictions, not a complete proof or a counterexample.

Full verification2026-10-14T21:10:53.643080Z:22fresh sequential builds,
10.470sec,52new audited roots,48hashes;47prior hashes authenticated.
The subsequent doc-only review at21:12:44.418201Z clarified the hypothetical
cycle case and written power corollary and inserted the completed counts.
All tested source, verifier, log, and replay hashes remained unchanged.
Independent finite evidence:65535shell sources with1966082ordinary steps;
65626finite cap telescopes with1970655edges;4096explicit convergence
witnesses with307751ordinary steps, all independently replayed;257+3
envelope arithmetic checks. No unfinished orbit is assigned a global
minimum. The 4096-source convergence census is Python, not a Lean range
certificate. No external mathematical theorem or novelty claim was added.

ATTEMPT, README and top memory link the new note. All48hashes and the new
links authenticated after documentation review. All jobs are terminal.
No agents, installations, credentials, staging, commits, or Git writes.
HEAD remains75060940e57cb13b532f7c09ad47ec3abc45be1e, staged diff empty,
index SHA256 cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8.
Git reads use GIT_OPTIONAL_LOCKS=0. The goal remains active, with no
external blocker; actual residual control and both counterexample types
are still open.


## 2026-10-14 — Minimum-root ancestry, ternary restrictions, and a height barrier

Classification: progress. The preceding root-spine turn was also progress,
and its48hashes reauthenticated. The new21root local kernel module and
finite replay are detailed in the top memory and the new note
docs/MINIMUM-ROOT-PREDECESSORS.md. All23fresh sequential modules passed
in10.929sec, finalrun21:38:59.046171Z,50hashes. The21:40:02.127598Z
doc-only count review left all tested source/log/replay hashes unchanged.

The investigation did not find a cap or energy upper bound. Existing
branch-density work already allowed the summable leakage being considered.
The root-count exponent does not improve the older per-orbit packing
exponent, and a polynomial target count is too large atcutoff3^K for the
requiredsublinearK masked energy. The external clean clone remainedat
a7275d5a73814d3d9a400c6fe6577de9542b03a3 and was only read. Rechecked
the primary arxiv2608.27617v1 page; its missingstar3/Conjecture2 remains
explicit. No new external analytic result was assumed or kernel replayed.

Useful actual arithmetic: all-odd inverse ancestry preserves global
self-minimality; a strict additional contracting parent is absent from
the whole nonrepeating orbit; it may be divisible3and have zero-density
basin. A least counterexample's kthroot cannot have3^(k+1)|(a_k+1), and
saturationat3^k forces an exact all-odd block fromtheoriginalsource.
The firstsuccessor is1mod3orattainsitsmaximal(3A+1)/2value.

The kernel also proves this method's limitation: above3^d-1, whereA<2^d,
everyall-odd inverse ancestor is already>=A. More of the same inverse
family cannot exclude an escaping tail. Next investigate mixed parity
inverse words or an actual nonsummable relative branch estimate, retaining
the separate nontrivial-cycle problem. No smaller source or divergent
orbit was exhibited, and Collatz remains unresolved.

The axiom-free witness155,167,111 uses finite suffix minima onthe27prefix;
allthreeareseparatelykernelcheckedtoreach1. Python's8192sourcecensus and
4243blockpairs never assign global minima to unfinished paths. The19th
and20th arithmetic roots are the all-depth height comparison and barrier;
all21audited roots have standard logical axioms only or none.

ATTEMPT, README and top memory were updated. All jobs are terminal.
No agents, installations, credentials, staging, commits, or Git writes.
The index remainscedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8,
with staged diff empty. The full goal remains active; no external blocker.


## 2026-10-14 — One-even mixed ancestry beats the all-odd barrier

Classification: progress. The preceding turn completed the pending
hash/link verification of the root-predecessor milestone; this turn
adds actual mixed inverse arithmetic and an unbounded improvement family.
The30-root module, note, verifier and results are summarized at the top.

The exact two-block path and its parity count establish that one extra
even-input shortcut step suffices to defeat the old all-odd height
barrier by unbounded factors at increasing sources. The hypothesis that
a least counterexample actually encounters a useful target is retained.
No unknown orbit minimum or divergent source is inferred from a prefix.
The family sources are all divisible3, so their inverse basins remain
zero-density doubling rays; this is recorded as a written observation.

The exhaustive inverse/forward census led to a closed arithmetic
criterion: reduce b by all-odd inverses to c, then an extra even input
improves the minimum iff c=4mod9. The key arithmetic is kernel; complete
set-minimum assembly and the natural target density1/6 are written.
A least source itself cannot be4mod9(kernel). This does not control
frequency or relative height on an exceptional orbit.

Final verification21:57:16.224949Z:26fresh sequential builds12.980sec,
30roots,58hashes;50+28+14 prior manifest entries authenticated.
65536targets and65536forward sources agree on131072 minima comparisons;
10922 strict improvements,65536 residue comparisons,17 progression counts.
Two axiom-free numerical examples include a56-bit source reaching above
its old threshold atclock119, then1 at751. Four arrivals are kernel
witnessed and independently replayed; no interval convergence claim.
Modular lifting through128 is separate from exact family paths through10.

The written fixed-extra-even envelope shows why this still cannot
cover arbitrary heights from a fixed source. The Monks primary paper
was reviewed for the gap between residue reachability and a smaller
predecessor; no external theorem entered the kernel dependency chain.
The next ancestry question needs actual-orbit relative height control,
with general mixed word inversion now available. Full Collatz remains
unresolved, including both nontrivial cycles and divergent orbits.

ATTEMPT, README, and top memory are updated. No live jobs, agents,
installations, credentials, staging, commits, or Git writes. The index
SHA256 remainscedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8
and staged diff is empty. The active goal has no external blocker.

## 2026-10-15 — Near-source exit inheritance and the exact first target

Classification: progress. The user accidentally interrupted the active
goal and asked to continue. Resumed the completed 23-root first-target
module, strengthened the written consequence, and finished verification
and the research handoff. The preceding mixed-ancestry milestone remains
authenticated; its tested files were not changed.

The kernel half-source meeting applies at different ordinary clocks
and forces a two-halving exit to lie above twice a least source. This
gives exactly one extra even step after a maximal odd block of length
at least two at any qualifying value in the band up to twice A. It
does not assert that enough values return to that band.

The parameterized kernel first-target family has one-even inverse
minimum equal to its starting source even at arbitrarily large relative
target heights. The decisive written refinement applies to a least
counterexample itself: its known exclusions imply the explicit profile
K>=2, 3^K*q=3mod4, A!=2mod3, A!=4mod9 when A+1=2^K*q with q odd.
Its first20mod27 visit is therefore at2K+3 and its full zero/one-even
inverse minimum is exactly A. This first occurrence cannot yield the
desired strict contradiction. This general assembly is written; it is
not silently included among the 23 new kernel roots.

The independent finite census matched that profile with all4551
first-target equality cases among65536starts. There were60949strictly
smaller predecessors,36arrivals at1 before a target, and no above-source
or unfinished outcomes atclock4096. Equality implies the profile only
as a FINITE check here; a universal converse is not claimed.

Final full run2026-10-14T22:17:16.827471Z:27fresh sequential
Lean4.33.1 builds,14.570sec,23roots,58hashes;58prior entries validated.
The four axiom-free arrival witnesses are independently replayed.
Documentation-only review22:18:56.572088Z updates the note hash and
preserves every tested source, log and replay hash. All58current hashes
and new-note local links subsequently authenticate; git diff --check
passes. Details and exact remaining gaps are at the top of this memory.

README, ATTEMPT and reproduction commands now include the new milestone.
Both nontrivial cycles and divergent orbits remain unresolved. Next work
needs a useful later visit, longer inverse words, or actual quantitative
cap/residual control; sufficient-set reachability alone is inadequate.
No live jobs, agents, installs, credentials, staging or commits remain.
The index SHA256 is unchanged at
cedad64e614f84baaa0cb348e8d639558020d1ad7fefa40cb42e98301c3321e8;
the staged diff is empty. The unbounded goal remains active, without an
external blocker.

## 2026-10-15 — Exact inverse cost at repeated residue-20 visits

Previous goal turn: progress; it completed the interrupted first-target
milestone. Current turn: progress. The new 31-root return-ladder module
extends the analysis from one inverse even step to every prescribed
finite budget, with a kernel universal inverse relation and exact minima.

Initial exploration of later visits showed that source 27 does not
obtain a smaller one-even predecessor until its tenth visit; source
7527 needed fourteen in the finite census through 16384. This changed
the next question from a small visit bound to an unbounded construction.
The OOEO block first supplied long windows, but the simpler OOE block
gave the exact family n_R=8^R-5 and a useful negative-five companion.
The abandoned OOEO prototype was not added as a new result.

The decisive step is the companion invariant, including its integrality
at every inverse guard and its terminal ternary boundary. It bounds
the odd inverse count by 2e+1 and proves the exact minimum x_(i-r)
for r<=i. All words in the budget are covered; this is stronger in
formal scope than the preceding written zero/one-even optimization.
The kernel also constructs the attaining word and proves every actual
ordinary target visit in the long positive prefix. No fixed budget can
keep pace with arbitrarily long late windows in this varying-source family.

The full verification passed at 2026-10-14T22:41:48.423658Z:
28 fresh sequential Lean builds, 15.927 seconds, 31 roots, 60 hashes,
with all 58 prerequisite entries authenticated. Independent complete
forward and inverse censuses agree on 327680 minima through 65536 for
budgets 0..4. Full companion-tree replay covers 141333 nodes in 516
queries; larger actual family prefixes extend through R=1025.
Four axiom-free kernel arrival witnesses are independently replayed.
Documentation-only review at 22:45:12.588539Z updated the note hash,
preserving all tested sources, logs and replay. All 60 hashes, local
note links and new-file whitespace checked; git diff --check passed.

The important open boundary is r>i. Preliminary exploration, outside
the final verifier manifest, found no smaller ancestors for the twelve
targets at R=3,5,7 in a complete ascending forward cache through 2097147
sources (4553804 newly visited ordinary edges). Further bounded inverse
queries through budget24 also found no smaller source at selected
R=3,5,7,9,11,21 targets. These are exploratory Python observations,
not a theorem for all R or unrestricted ancestry. If pursuing that
boundary, reproduce the relevant observation rather than promote it.
At odd-count depth 2i+1 with more than i even steps, the negative
companion can cease to share the positive inverse guard; that is the
specific point the present proof does not control.

The two external pages cited in the note were read for scope only:
Sodelin's refined residue-20 ancestor selector and GettysburgResearch's
result catalog. No external theorem, external finite range, or claimed
proof was imported. The actual family has v3(4b_i+1)=3, while the other
coordinate v3(b_i+7)=2i+1 grows. These valuation observations are written
and separately checked, not additional unnamed kernel roots.

README, ATTEMPT, reproduction commands and the top memory are current.
The user committed preceding work during the turn: last observed HEAD
9daca496bba4d1ba2172cf338a8ceaf9463097f7 and index SHA256
4db425a7440cea411ba44230cbbeb2a6d674a3868ef0350deef245d412ba5572.
The staged diff is empty; no assistant staging or commits occurred.
All jobs are terminal. No agents, installations or credentials were used.
The goal remains active with no external blocker. Collatz, including
nontrivial cycles and divergence, remains unresolved.
