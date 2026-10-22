# Fixed extra inverse budgets across a whole return ladder

For every fixed extra budget s, there are arbitrarily large sources
`N=8^R-5` for which **every** residue-20 target in the growing ladder
prefix has inverse minimum N, even with i+s even operations at the
ith target. The permitted budget grows with the visit index i. The
number of obstructed visits can exceed any prescribed bound.

This strengthens the preceding
[first-target obstruction](MINIMUM-INVERSE-LOCALITY.md) to simultaneous
control of all targets in one arbitrarily long growing prefix. It
excludes the proposal that a fixed extra budget must succeed at some
residue-20 visit before that prefix ends. Visits after the prefix,
source-dependent extra budgets, and the positive-integer Collatz
conjecture remain unresolved.

The [Lean module](../lean/MinimumLadderWindow.lean) has 16 audited kernel
roots. The all-word lower bound, the attaining paths, the explicit
family, and its unboundedness are kernel proofs. One finite certificate
is axiom-free. No native reduction axiom or external mathematical
premise is used.

## The statement and its quantifiers

For the [return ladder](MINIMUM-RETURN-LADDER.md), write

    N = 8^R-5,
    x_i = 9^i*8^(R-i)-5,
    b_i = (3*x_i+1)/2,                    0<=i<R.

For odd R>=3, the ordinary orbit has `C^(5i+2)(N)=b_i`, and its
prefix minimum through clock 5R is N. Before that clock, the visits
to 20 modulo 27 are exactly b_i with `1<=i<R`. The index zero target
is included in the inverse theorem but is not a residue-20 visit.

Let M_r(b) be the minimum over positive predecessors p admitting a
legal inverse shortcut word with at most r even operations. Odd
operations have no imposed cutoff. The complete relation is
`Backtrack(e,o,b,p)`, with ordinary semantics `C^(e+2o)(p)=b`.

The new kernel theorem says that, if

    K >= 2*(s+3),       8^R = 8+3^K*q,       q>=0,

then simultaneously for every `0<=i<R`,

    M_(i+s)(b_i) = N.                                  (1)

The source is attained by a word with i even and 2i+1 odd operations.
Every other permitted word has predecessor at least N. Thus (1)
is a full minimum statement, including words whose ordinary clocks
are much larger than the displayed forward clock.

An explicit family satisfying these hypotheses is

    K_s = 2*(s+3),
    R_(s,h) = 1 + 2*3^K_s*(h+1),          h>=0.         (2)

The kernel proves R>=3, R odd, and h<R<N. Consequently, for every
s, every visit-count bound L, and every source bound B, there is
one R with N>B and R-1>L such that (1) holds at all its targets.
This is simultaneous failure within one finite prefix, not a
different source chosen separately for each visit.

## A sharp bound for the negative companions

The earlier inverse analysis uses the magnitude relation Shadow,
starting at 7, with operations

    E: m -> 2m,
    O: m -> (2m+1)/3 when this is integral.

For every `Shadow(e,o,m)`, the new kernel invariant is

    m>=5,       o<=2e+1,
    m <= 7*2^(e-floor(o/2))     if o is even,
    m <= 5*2^(e-floor(o/2))     if o is odd.            (3)

An E operation doubles the bound. For an O operation, the two cases
use `14T+1<=15T` and `20T+1<=21T` for T>=1. If an odd count were
already 2e+1, its magnitude would be exactly 5, which has no legal
odd inverse. This proves the count bound as part of the same induction.

At the critical odd count 2i+1, put e=i+f. Equation (3) becomes

    5 <= m <= 5*2^f.                                  (4)

The word `O(EOO)^i E^f` attains `m=5*2^f`, so this upper bound is
sharp for every i and f. It improves the preceding bound
`4^f*(m-1)<=4*9^f`. Also m cannot be 8: an even inverse giving 8
would need magnitude 4, while an odd inverse always gives an odd
magnitude. These are statements about finite legal companions;
no assertion about convergence of all negative integers is needed.

## A small positive reference at every frontier

For any f,m satisfying (4) and m!=8, set

    a = 2^(f+3)-m.

The kernel proves `3*2^f<=a` and `a+5<=2^(f+3)`, and a is outside
the cycle {1,2,4}. Every inverse predecessor p of a satisfies

    p>=3,       3^o<=2^(f+e+o).                         (5)

The second inequality bounds the inverse multiplier from below by
`2^(-f)`. To prove it, suppose the multiplier were smaller. The
preceding inverse-size inequality gives

    3^o*(p+1) <= 2^(e+o)*(a+1) < 8*3^o,

so p<=6. Those six positive orbits enter {1,2,4} by ordinary clock
eight and are at most 16 beforehand. Since a lies outside that
cycle, a hit must occur before eight and `3*2^f<=a<=16` forces f<3.
A kernel finite certificate checks all the remaining counts and
ordinary hits. It includes zero only as a harmless extra finite
index; the mathematical predecessor argument requires p>0.

The exclusion m!=8 is necessary. At f=1,m=8, the reference target
is a=8 and two odd inverses give p=3, with scaled multiplier 8/9.
This countercase cannot occur in Shadow, as proved above.

## Splitting every possible improving word

The earlier kernel theorem `before_escape_lower` already proves
that any word to b_i with at most 2i+1 odd operations has p>=N,
regardless of its even count. Every hypothetical improvement must
therefore pass the odd-count frontier 2i+1.

A new kernel splitting theorem factors every Backtrack proof at
any prescribed odd count. At this frontier, the prefix has i+f
even operations with f>=0, and a positive value x satisfying

    x+m = 2^f*8^R,       Shadow(i+f,2i+1,m).            (6)

If the full word has at most i+s even operations, then f<=s and
the remaining suffix has at most s-f even operations. Using
`8^R=8+3^K*q`, equation (6) becomes

    x = a + 3^K*(2^f*q),       a=2^(f+3)-m.             (7)

Here `a+1<=2^(f+3)`. The previous inverse-locality theorem therefore
transfers the entire suffix to the positive reference a, because

    2*((s-f)+(f+3)) = 2*(s+3) <= K.

If the suffix has e even and o odd operations, its predecessor is

    P = p + 2^(e+o)*3^(K-o)*(2^f*q),       o<K.

By (5), the second term is at least `3^K*q`, and p>=3. Hence

    P >= 3+3^K*q = 8^R-5 = N.

This excludes every possible improving suffix. Together with the
before-frontier theorem and the attaining word, it proves (1).
The argument permits arbitrarily large i and arbitrary odd counts;
it does not replace either by a finite search limit.

## Verification and the boundary of the result

Run

    python3 verify_minimum_ladder_window.py --lean /tmp/lean-4.33.1-linux/bin/lean --threads 16

The [verifier](../verify_minimum_ladder_window.py) authenticates the
66 hashes in the preceding inverse-locality manifest, freshly builds
32 Lean modules in dependency order, and audits the 16 new roots.
The requested thread count applies to each Lean process. Historical
sources and verification records are preserved.

Independent Python replay covers the complete negative companion
tree through even budget 22, the sharp attaining words, every tuple
of the small positive certificate, and complete reference trees
through extra budget ten. Separate word tests split every inverse
word for targets 1 through 64 at every available odd count.

For the actual family (2), four complete growing prefixes are
streamed through R=118,099. Two larger sources have only their
stated initial blocks replayed. Complete inverse optimizations are
restricted to specified early indices; the universal all-visit
claim rests on the kernel proof. A separate modular census covers
s=0 through 128 and h=0 through 31 without constructing those
enormous sources. The [manifest](../results/minimum-ladder-window/verification.json)
and [replay](../results/minimum-ladder-window/replay.json) retain exact
counts, ranges, hashes, commands, and compiler identity.

The theorem does not address residue-20 visits after clock 5R, or
an extra budget growing with the source or the visit. It does not
give infinitely many obstructed visits from one fixed source:
increasing the desired window changes R and N. Universal convergence
of (2), useful later visits on a hypothetical least-counterexample
orbit, the cap/residual estimates, and both kinds of counterexample
remain unproved. The full Collatz goal remains active.
