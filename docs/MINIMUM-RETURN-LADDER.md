# Exact inverse complexity at repeated target visits

**Later visits alone do not repair the first-target ancestry argument.**
There are arbitrarily long positive Collatz prefixes with consecutive
visits to 20 modulo 27 for which any prescribed fixed inverse budget
fails to produce a predecessor below the original source. The new
result gives the exact minimum over all inverse words in the specified
budget, not just over a selected collection of paths.

The [Lean module](../lean/MinimumReturnLadder.lean) has 31 audited roots.
Its universal inverse inequality, attaining words, exact ordinary
visit positions and unbounded finite-window theorem are kernel proofs.
The numerical convergence witnesses use axiom-free kernel computation.
No external theorem enters these proofs and no novelty claim is made.
**The positive-integer Collatz conjecture remains unresolved.**

## 1. Actual growing prefixes with many target visits

Use the shortcut map U(n)=(3n+1)/2 for odd n and U(n)=n/2 for even n.
An even input counts an extra halving; the halving paired with each
ordinary odd step is already included in U.

For an odd integer R>=3 put

    n_R = 8^R-5,
    x_i = 9^i*8^(R-i)-5,                       0<=i<=R,
    b_i = (3x_i+1)/2
        = 3^(2i+1)*2^(3(R-i)-1)-7,             0<=i<R.

The repeated shortcut word is (O O E)^R. Each block is the actual
five-step ordinary path

    8u+3 -> 24u+10 -> 12u+5 -> 36u+16 -> 18u+8 -> 9u+4.

Every value in a block is at least its starting value, and successive
block starts strictly increase. The kernel proves

    C^(5i)(n_R)=x_i,      m_(5R)(n_R)=n_R,
    C^(5i+2)(n_R)=b_i.                                      (1)

It also classifies every clock t<5R:

    C^t(n_R)=20 mod27  iff  t=5i+2 for some 1<=i<R.           (2)

Thus the visits occur at 7,12,17,...,5R-3, with no intervening visits.
There are R-1 visits before clock 5R. At each completed block x_i
with i>0 the residue is 4 modulo 9, and its first odd shortcut step
gives the target. The other intermediate ordinary states have residues
that exclude 20 modulo 27. The initial source is 3 modulo 9.

The affine block relation x_(i+1)+5=(9/8)(x_i+5) is also the
positive finite-prefix lift of the negative shortcut cycle
-5 -> -7 -> -10 -> -5. This explains the choice of the offset five.
It supplies no single positive source with an infinite repeated word.

## 2. The complete minimum for a bounded inverse budget

At a positive target x the two possible shortcut inverse operations are

    E: x -> 2x,
    O: x -> (2x-1)/3,   allowed exactly when x=2 mod3.

The module defines the inductive relation Backtrack(e,o,b,p), recording
every such finite inverse word from b to p, with e even and o odd
operations. The kernel proves its actual ordinary endpoint identity

    C^(e+2o)(p)=b.

For the targets in (1), the main theorem is

    min {p : Backtrack(e,o,b_i,p) for some e<=r and o}
        = x_(i-r) = 9^(i-r)*8^(R-i+r)-5,      0<=r<=i<R.    (3)

Both parts of this minimum statement are kernel checked. Every
admissible word obeys the lower bound, and an explicit word attains
it with exactly r even inputs and 2r+1 odd inputs. The attaining
forward word is (O O E)^r O, of ordinary length 5r+2.

In particular, (3) equals n_R at r=i and is strictly larger at r<i.
Any inverse word reaching a source p<=n_R must therefore use at least
i even inputs. The kernel proves this necessary cost without imposing
an a priori budget on that word. It does not exclude a smaller p
when the budget is greater than i.

For any fixed r, window length L and source bound B, another kernel
theorem chooses an odd R and n_R>B such that the L consecutive visits
with indices r+1,...,r+L all have **every** predecessor using at most
r even inputs strictly above n_R. One explicit choice is

    R=2(r+L+B+3)+1.

For r=1 the first visit recovers n_R, and all remaining visits before
5R give a strictly larger minimum. Thus an arbitrary fixed number of
visits cannot force a strict descent through the one-even test.

For r>=2, the theorem about a late window must not be read as a claim
about the earlier visits i<r; those exceed the range of (3). In every
case the source changes when the window is lengthened.

## 3. Why the lower bound covers every inverse branch

The proof attaches an arithmetic companion -m to the positive inverse
state p. Initially p=b_i and m=7. Under inverse operations the magnitude
changes by

    E: m -> 2m,
    O: m -> (2m+1)/3.

This is arithmetic bookkeeping with positive magnitudes m, not a
negative or positive orbit introduced as a conjectural premise.
For a path with e<=i even inputs and o odd inputs, the kernel proves

    5<=m<=7*2^e,       o<=2e+1,
    d=2e+1-o,
    2^d*(m-1)<=4*3^d,
    3^o*(p+m)=2^(e+o)*(b_i+7).                            (4)

The potential in (4) makes the odd-operation count exact enough to
be useful. Doubling changes m-1 to 2(m-1)+1, at most (9/4)(m-1)
because m>=5. An odd inverse multiplies m-1 by 2/3. At zero
remaining exponent d, the bound forces m=5, which has no legal odd
inverse companion.

Legality is retained throughout the positive path. While o<2i+1,
the factor 3^(2i+1) in b_i+7 transfers each positive inverse guard
to its companion. At the only possible boundary o=2i+1, (4) forces
e=i, m=5 and p=n_R. Since odd R makes n_R divisible by three,
the positive path has no further odd inverse there either. Thus
there is no unproved assumption that a companion remains integral.

Cancelling powers in (4) gives another kernel identity,

    2^d*(p+m)=3^d*(x_(i-e)+5).                            (5)

If d=0, then m=5 and p=x_(i-e). If d>0, the ratio 3^d/2^d
is at least 3/2. The possible additive loss is controlled by

    14*2^e <= 8^(e+1)+10 <= x_(i-e)+15.

These integer bounds give p>=x_(i-e). Monotonicity of the x_j then
gives p>=x_(i-r) for e<=r. This proves the universal half of (3),
including nonminimal branches and arbitrarily long odd blocks that
would otherwise have to be considered in the inverse search.

## 4. Examples, ternary coordinates, and the remaining gap

At R=3, n_R=507. Its two visits are:

| Visit i | Ordinary clock | Target b_i | Budget 0 minimum | Budget 1 minimum | Budget 2 minimum |
|---|---:|---:|---:|---:|---:|
| 1 | 7 | 857 | 571 | 507 | Outside (3) |
| 2 | 12 | 965 | 643 | 571 | 507 |

The kernel separately checks convergence of 507, 857 and 965 at
ordinary clocks 35,28 and 23. It also checks n_5=32,763 reaches
one at clock 160. Python verifies first-arrival minimality. No
convergence theorem for every odd R is claimed.

The formulas give the following written valuation identities for
1<=i<R and odd R:

    v3(b_i+7)=2i+1,       v3(4b_i+1)=3.                    (6)

The replay checks these as well. A public
[refined residue-20 ancestor construction](https://github.com/Sodelin/Collatz-Conjecture-Work/blob/main/proof-search/lemmas/Residue20_Refined_Ancestor.md)
uses a large valuation of 4b+1 and explicitly retains a missing
return argument. Its uniform threshold does not cover (6). We use
that comparison only to locate the remaining gap; no result from
the external note is assumed or independently replayed here.

A separate public
[research catalog](https://github.com/GettysburgResearch/collatz/blob/main/research/RESULTS_CATALOG.md)
also distinguishes arbitrarily long finite growth patterns from an
ordinary integer realizing an infinite pattern. The distinction is
essential here: (1)--(3) concern different finite prefixes as R grows.
They establish no divergent positive orbit or nontrivial positive cycle.

The exact minima for budgets r>i remain unproved in this analysis.
The broader task still needs a theorem forcing an actually useful
predecessor below a hypothetical least counterexample, or independent
quantitative cap/residual control. Counting visits without controlling
their inverse cost does not supply that theorem.

## 5. Reproduction and evidence

Run `python3 verify_minimum_return_ladder.py`. The
[verifier](../verify_minimum_return_ladder.py) authenticates the
preceding first-target manifest, freshly builds 28 Lean modules
sequentially, and audits every one of the 31 new roots. It rejects
warnings, admitted proofs, native reduction axioms and nonstandard
printed axioms. The finite witness is axiom-free.

An independent complete census compares inverse minima with forward
paths for every source and target from 1 through 65,536, for budgets
0 through 4. Forward paths stop before their fifth even input. Since
a target is its own zero-length predecessor, a source above the
cutoff cannot supply its minimum, so this forward comparison covers
all relevant sources. These are bounded-word minima, not numerical
assignments of unknown global minima or a convergence interval.

Family checks traverse every ordinary prefix for odd R=3 through 65,
plus R=129,257,1025. All target visits are checked. All inverse budgets
r<=i are checked for R<=17; larger inverse queries have the explicitly
listed smaller budgets and target samples in the replay. Separate
complete inverse-tree traversals check every companion invariant and
every branch for all odd R<=17, every i and every r<=i.

The [manifest](../results/minimum-return-ladder/verification.json) and
[replay](../results/minimum-return-ladder/replay.json) retain exact
counts, compiler identity, source/log hashes and these scope limits.

The final full run completed at 2026-10-14T22:41:48.423658Z using
Lean 4.33.1. The 28 fresh builds took 15.927 seconds; all 31 new
roots passed, with 60 file hashes and all 58 prerequisite hashes
authenticated. The complete census matched 327,680 minima, using
589,710 forward shortcut steps and 917,276 ordinary steps. Increasing
the budget from 0 to 1, 1 to 2, 2 to 3 and 3 to 4 gave respectively
10,922, 3,033, 1,130 and 918 strict improvements in this finite interval.

The 35 family prefixes contain 12,495 ordinary steps and 2,464 target
visits. Their 8,796 inverse-minimum comparisons have independently
replayed attaining paths totaling 187,032 ordinary steps. The complete
companion checks traverse 141,333 inverse nodes across 516 queries.
The four kernel arrival witnesses are independently replayed over
246 ordinary steps. No unresolved global minimum enters these checks.
