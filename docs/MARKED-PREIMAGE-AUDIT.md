# Audit of the marked first-passage preimage formula

**Status: an audit of the finite inversion, first-passage condition,
clock mark, and interval replacement in the local progression-mixing
argument. Eleven new kernel roots and exact forward/inverse counting
checks support these steps. This is not a kernel proof or an independent
peer review of analytic mixing. Collatz remains unresolved.**

The [progression-mixing note](CLOCKED-PROGRESSION-MIXING.md) claims a
comparison of source laws retaining both the first odd landing and its
ordinary clock. The [minimum-tail consequence](MINIMUM-LOG-MOMENTS.md)
depends on that local written analytic premise. This audit checks the
passage formula used to connect the mixing statement to actual sources.
It finds no contradiction in retaining the clock, and makes two necessary
details explicit: excluding an earlier passage, and counting endpoint
errors by sources rather than by valuation words.

## 1. What the external source supplies

[Tao's paper, Sections 2, 5, 6 and 7](https://arxiv.org/html/1909.03562v7)
was checked against the local adaptation. Lemma 2.1 identifies an odd
integer affine endpoint with the unique actual valuation word.
Proposition 5.2 is stated for log-uniform sources and unmarked landing
events. Its proof establishes an event equivalence on a good valuation
set, using an intermediate state with a fixed number of passage steps
remaining. This event equivalence allows a bounded clock test to be
inserted, but its published statement alone does not give the local
uniform-source, clock-marked formula.

The paper's Section 6 factorization splits at a fixed partial valuation
sum, with the initial collision block independent of the remaining
coordinates. Section 7 bounds the absolute paired product. These are
the published ingredients used in the local fixed-total and fixed-endpoint
extensions. The audit did not find a lost independence at those two
steps: a total-sum condition becomes a fixed-sum tail restriction after
the initial sum is fixed; the sum tilt is constant once pair totals
are fixed. Those analytic extensions remain written deductions.

## 2. Exact inversion and the ordinary clock

For a positive valuation word `w=(a_1,...,a_k)`, write `s=sum a_i` and

\[
 2^s\operatorname{Aff}_w(N)=3^k N+B_w,\qquad
 B_{\varnothing}=0,\qquad
 B_{a::v}=3^{|v|}+2^a B_v.                                 \tag{1}
\]

Here `|v|` in the last expression is the word length. For an odd
positive integer `M`, the cleared affine equation

\[
                         2^sM=3^kN+B_w                    \tag{2}
\]

with `N` a natural number is equivalent to an actual chain of odd
integers with successive relations `2^(a_i) N_i=3N_(i-1)+1`.
In particular `N` must be odd and positive. The new kernel module
proves this implication, its converse, and uniqueness of the word
and endpoint for a fixed source and length. Its proof extracts the
first quotient using coprimality of powers of two and three, then
continues inductively. No orbit-convergence assumption is used.

Each such step consumes `a_i+1` ordinary Collatz iterations, so

\[
                         C^{k+s}(N)=M.                     \tag{3}
\]

Suppose `M` has first odd passage below `x` after `m` Syracuse steps,
with landing `b` and tail valuation sum `sigma`. Provided the prefix
has no earlier odd passage, the source's first passage has mark

\[
                    (b,I),\qquad I=k+s+m+\sigma.           \tag{4}
\]

This is the formula `I=n+s+S_m(M)` in the preceding note, where
`n=k+m`. Both the ordinary-clock identity and the first-passage splice
are kernel proved. Therefore an arbitrary test `g(b,I)`, bounded by
one, is a function of `(k,s,M)` in the inverse formula; the individual
word need not be retained beyond its residue and sum.

## 3. Earlier crossings really must be excluded

The following exact example rejects an ungated use of (4):

\[
               19\longmapsto29\longmapsto11
                 \longmapsto17\longmapsto13
\]

is an odd-state trajectory. The prefix from `19` to `17` has word
`(1,3,1)`, sum `5`, and ordinary clock `8`. Its partial valuation sums
differ from twice their lengths by at most one. From `17`, first odd
passage below `16` occurs at `13` after three ordinary steps. Yet the
first odd passage from `19` is `11` at ordinary clock six, not clock
eleven. This counterexample is kernel checked. It refutes the formula
**with the prefix passage condition removed**, not the existing note.

Here is a sufficient deterministic condition for the prefix. Suppose
all its partial sums satisfy

\[
              |S_j-2j|\le E\quad(0\le j\le k),             \tag{5}
\]

where `E` is a nonnegative integer. For the suffix after the `j`th
odd state, `S_k-S_j>=2(k-j)-2E`. Its multiplicative coefficient is
at most `4^E(3/4)^(k-j)<=4^E`. Its nonnegative affine offset is at
most `3^(k-j)<=3^k`. Thus every prefix odd state `N_j` satisfies

\[
                           M\le4^E N_j+3^k.                \tag{6}
\]

Consequently the height condition

\[
                           M>4^E x+3^k                     \tag{7}
\]

forces all these states to exceed `x`. The intervening even states
exceed their next odd endpoint, so they cause no earlier odd passage
either. The rational envelope implication in (6)–(7) is kernel proved;
the general suffix-coefficient derivation above is written and is
checked exactly on the enumerated valuation words.

In the analytic application, take `E=ceil((log x)^0.6)`,
`k<=n_0=floor(log x/(10 log 2))`, and
`m=floor((alpha-1)log x/100)`, with `alpha=1001/1000`.
The intermediate height window has lower endpoint

\[
                 x(4/3)^m\exp[-(\log x)^{0.7}].             \tag{8}
\]

For sufficiently large `x`, (8) exceeds (7): the logarithm of its
ratio to `x` has a positive term proportional to `log x`, which
dominates the two sublinear powers; also `3^k/x` decays as a positive
power of `x`. The existing height window therefore supplies the
necessary exclusion. This audit does not give an effective starting
scale for that comparison.

## 4. The interval error counts sources, not words

Let `F_w=B_w/2^s` and put

\[
             N=2^s(M-F_w)/3^k,\qquad U=2^sM/3^k.
\]

Suppose `0<=F_w/M<=eta<1`. Then
`(1-eta)U<=N<=U`. If membership of `N` and `U` in `[y,2y)` differs,
the actual source `N` lies in

\[
        [(1-\eta)y,y)\ \cup\ [2(1-\eta)y,2y).               \tag{9}
\]

This localization is kernel proved, including half-open endpoints.
For fixed length `k`, uniqueness in Section 2 makes the map
`(w,M) -> N` injective among admissible pairs. Thus the total change
in any marked count is bounded by the number of actual sources in
(9). There is no factor equal to the number of valuation words.

For unrestricted odd sources, or odd sources in one fixed class
modulo three, the relevant source lattice has spacing `d=2` or `6`.
The union in (9) contains at most `3 eta y/d+2` such sources. Since
the source count in `[y,2y)` is `K=y/d+O(1)`, the normalized error is
`O(eta+1/y)` for each length. This applies to every bounded mark test
at once, by taking the absolute count of changed pairs.

In the analytic windows, `F_w<=3^k` and (8) give
`F_w/M<=x^(-0.8)` for all sufficiently large `x`.
There are `O((log x)^0.8)` possible passage lengths in the expanded
window. Summing their endpoint errors is still `O(x^(-c))` for a
positive constant `c`. The source congruence changes the lattice
spacing and normalization by the same factor three.

## 5. Exact grouping with the mark retained

Fix `k,s`. Before smoothing, the unrestricted residue condition is
`M=F_w mod 3^k`. The source class `N=r mod 3` instead imposes

\[
                  M=F_w+3^k2^{-s}r\pmod{3^{k+1}}.          \tag{10}
\]

For each residue, sum the bounded marked test over odd `M` satisfying
the tail passage and height conditions and
`3^k y 2^(-s)<=M<2*3^k y 2^(-s)`.
Multiplying by `2^s/K` converts the geometric word weight `2^(-s)`
into the actual uniform source weight `1/K`. This is an exact identity,
also for a restricted word set and for arbitrary clock-dependent tests.

The counting coefficient is bounded by

\[
 \frac{2^s}{K}\left(\frac{3^k y2^{-s}}q+1\right),
 \quad q=3^k\ \hbox{or}\ 3^{k+1}.                         \tag{11}
\]

If any `M` is counted, `2^s/y<2*3^k/M`, which is a negative power
of `x` in the analytic windows. Thus (11) is uniformly bounded.
This permits removal of a rare bad-word indicator before applying
the written joint mixing estimate, even with a mark test inserted.

For the two unit source classes the preceding note encodes (10) by
one fixed endpoint valuation. After smoothing down to `3^m`, the
coarse laws agree jointly with `s`, and the scalar ratio is
`K_y/(3K_(y,r))=1+O(1/y)`. Its error is harmless even with the crude
bound of a constant times the number of retained lengths on the sum
of the unsmoothed main terms. No renewal averaging over the clock is
needed for this same-scale comparison.

## 6. What was tested and what remains analytic

Run `python3 verify_marked_preimage_audit.py`; see its
[verification record](../results/marked-preimage-audit/verification.json).
The checker independently enumerates forward source trajectories and
inverse word/endpoint pairs. It compares their complete finite marked
count tables, including ordinary clocks and source residues. It also
reassembles the unshifted tables from residue/total-sum laws with exact
rational weights, and checks the boundary error against the actual
source layers in (9). Every good word allowed by each finite prefix
condition is enumerated; no unreported valuation truncation is used.

The small experiments use explicit integer height conditions of the
form (7). They do not purport to enter the enormous, unspecified
asymptotic regime of (8). The counterexample in Section 3 checks why
that condition matters. All computational comparison decisions are
exact, and the Lean roots have only standard logical axioms.

This audit supports the finite bridge from joint mixing to marked
passage laws. It does not prove the uniform tilted Fourier decay,
the collision/Plancherel extension, the large-scale good-event errors,
or the asymptotic mixing rate in Lean. It supplies no effective
constants and no new convergence or cycle exclusion. Those limits
remain explicit dependencies of the earlier written consequences.
