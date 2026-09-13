# Global closure and inversions in folded cycles

Let a primitive positive odd Collatz cycle have length \(k\), odd minimum
\(m\), odd maximum \(M\), and total halving count \(H\). The previous
[folded-order argument](FOLDED-CYCLES.md) proves coprimality when \(M<8m\).
Forward closure extends that conclusion:

\[
 \boxed{M<9m+2\quad\Longrightarrow\quad\gcd(k,H)=1.}       \tag{1}
\]

In particular the ratio threshold improves from eight to nine. More
generally, when \(M<16m\), let
\[
 t=\#\{x\text{ in the odd cycle}:8x+1\text{ is also in the odd cycle}\},
 \qquad g=\gcd(k,H).
\]
Then
\[
 \boxed{t\ge g-1,\qquad t\equiv g-1\pmod2.}              \tag{2}
\]
These are necessary conditions on every such integer cycle, with no
period cutoff or logarithm-theorem threshold. They do not exclude the
coprime case with no inversions, or all cycles of greater spread.

The classification of every possible local inversion, its forced orbit
states, and the strict-order consequence of forward closure are kernel
proved in [FoldedCycleNine.lean](../lean/FoldedCycleNine.lean). The finite
sorting argument, permutation cycle count, and assembly of (1)–(2) below
are written proofs. They are not asserted to be a complete Lean theorem
or a new proof of the Collatz conjecture. No novelty claim is made.

## 1. Four layers have only one kind of inversion

Assume \(M<16m\). For each odd cycle state \(x_i\), define
\[
 a_i=\lfloor\log_2(x_i/m)\rfloor\in\{0,1,2,3\},\quad
 c_i=2^{3-a_i},\quad u_i=c_ix_i\in[8m,16m),
 \quad G_i=3u_i+c_i.
\]
The folded integers are distinct because taking their odd parts recovers
the original states. Equal \(G_i\)'s would also give equal accelerated
successors. This is impossible for different members of one primitive
cycle, where the successor map is a permutation.

For \(u=cx<v=dy\), with odd \(x,y\) and
\(c,d\in\{1,2,4,8\}\), the exact inversion criterion is
\[
 \boxed{3v+d<3u+c
 \quad\Longleftrightarrow\quad c=8,\ d=1,\ y=8x+1.}      \tag{3}
\]
Indeed a strict inversion requires \(3(v-u)<c-d\). Scales at most four
cannot satisfy this. With \(c=8,d=1\), the positive difference \(v-u\)
is odd and less than \(7/3\), so it is one. With \(d=2\) the difference
is a positive even integer and \(3(v-u)\ge6=c-d\); with \(d=4\) it is
a positive multiple of four. All other scale cases are immediate.
Lean checks every case under the explicit oddness hypotheses.

Every inverted pair therefore consists of consecutive folded integers
\(8x,8x+1\). Such pairs occupy adjacent positions in the sorted list and
are mutually disjoint: their first entries are divisible by eight and
their second entries are odd. Conversely, every pair \(x,8x+1\) in the
original cycle gives one inversion. Its smaller state satisfies
\(m\le x<2m\), so its scales are precisely eight and one.

Consequently the order of the \(G_i\)'s differs from the order of the
\(u_i\)'s by exactly \(t\) disjoint adjacent transpositions. There are
no further inversions or ties.

## 2. Two further states repair the threshold

For every odd positive \(x\), exact accelerated steps give
\[
 8x+1\longmapsto6x+1\longmapsto9x+2.                     \tag{4}
\]
The first numerator is \(4(6x+1)\), and the second is \(2(9x+2)\);
the displayed terminal factors are odd. Thus a forward-invariant set
containing \(8x+1\), with all its states at most \(M\), satisfies
\[
 M\ge9x+2.                                               \tag{5}
\]
For an inversion in a cycle, \(x\ge m\), so \(M\ge9m+2\).
Hence \(M<9m+2\) rules out every inversion. For \(m\ge1\), this bound
also implies \(M<16m\), as required for the four-layer classification.

This explains the limit of the earlier example at spread \(8+1/m\):
it exhibited two valid edges inside its interval, but did not impose the
next edge in (4). There is no conflict with that local counterexample.
The new theorem uses forward closure, which the example lacked.

There are useful additional restrictions in the larger interval:

- If \(x=4q+1\), the third successor of \(8x+1\) is
  \(54q+17=(27x+7)/2\). Thus an inversion of this type requires
  \(2M\ge27x+7\).
- If \(x=8q+5\), the fourth successor is
  \(162q+107=(81x+23)/4>16x\). Such an inversion is impossible when
  \(M<16m\).

Both exact paths and the last comparison are kernel checked. Other
residue classes are not excluded by these paths alone.

## 3. Successor ranks are a rotation after those swaps

The original cycle edges yield
\[
 G_i=2^{b_i}u_{i+1},\qquad
 b_i=h_i+a_{i+1}-a_i.                                    \tag{6}
\]
Every folded numerator lies in
\[
 24m<G_i\le48m-2.                                        \tag{7}
\]
For the upper bound, \(u_i\) is a multiple of \(c_i\) strictly below
\(16m\), so \(u_i\le16m-c_i\) and
\(G_i\le48m-2c_i\le48m-2\). In particular
\(G_{\max}<2G_{\min}\). Lean checks these range comparisons.

The quotient \(G_i/u_{i+1}\) lies strictly between \(3/2\) and 6.
Since it is a power of two, \(b_i\in\{1,2\}\). The first branch
\(b_i=1\) is characterized by \(G_i<32m\), and the second by
\(G_i\ge32m\). Let \(r\) be the number of second-branch states.

Sort by \(G_i\). Within each branch the successors are increasing, and
every second-branch successor is smaller than every first-branch successor
because \(G_{\max}/4<G_{\min}/2\). The successor rank of a source whose
\(G\)-rank is \(j\) is therefore \(j+r\pmod k\).

Let \(\pi\) send the \(u\)-rank of a state to its \(G\)-rank. Section 1
shows that \(\pi\) is the product of the \(t\) disjoint adjacent swaps.
The actual successor permutation on \(u\)-ranks is
\[
 f=R_r\circ\pi,\qquad R_r(j)=j+r\pmod k.                 \tag{8}
\]
Telescoping (6) gives \(H=\sum b_i=k+r\), so
\(\gcd(k,r)=\gcd(k,H)=g\).

When \(t=0\), the actual successor permutation is exactly the rotation.
Primitivity says it visits all \(k\) ranks, which forces \(g=1\).
The arithmetic implication from a covering rotation to coprimality is
already kernel checked in `FoldedCycleBounds.full_rotation_coprime`.
Together with Section 2 this proves (1).

## 4. Count the cycle mergers

The rotation \(R_r\) has \(g\) cycles: its orbits are the residue classes
modulo \(g\), each of size \(k/g\). Multiplying a permutation on the
right by a transposition exchanges the two outgoing arrows at its
endpoints. If the endpoints belong to different cycles, this joins them;
if they belong to the same cycle, it splits that cycle into two. Every
other cycle is unchanged.

Apply the \(t\) swaps in (8), in any order. If \(a\) joins and \(b\)
splits occur, then
\[
 a+b=t,\qquad 1=g-a+b,
 \qquad t=g-1+2b.                                        \tag{9}
\]
The final cycle count is one because the original odd cycle is primitive.
This proves both assertions in (2). For example, exactly one inversion
forces \(g=2\); two inversions permit only \(g=1\) or \(g=3\).
This proof does not infer that either permitted case actually occurs.

There is also a quantitative integer restriction. If \(t>0\), its \(t\)
distinct smaller states are odd and at least \(m\), so the largest is at
least \(m+2(t-1)\). Applying (5) at that state gives
\[
 M\ge9m+18t-16.
\]
Consequently, for \(g\ge2\) and \(M<16m\),
\[
 \boxed{M\ge9m+18g-34.}                                 \tag{10}
\]
The earlier packing estimates can also bound the number of these smaller
states in \([m,\lfloor(M-2)/9\rfloor+1)\); (10) itself uses only odd
integer spacing. No analytic estimate is needed for (1), (2), or (10).

## 5. Remaining obstruction and verification scope

When there are no inversions and the counts are coprime, folded ranks
still follow a mechanical rotation, but the four scale layers leave many
actual halving words. Integrality of the corresponding ordered numerator
remains necessary. Neither sorted ranks nor (2) proves that every such
divisibility test fails. The unrestricted mechanical-mask families from
the preceding work lie in the already coprime, narrow-spread regime and
are not eliminated by this extension.

At spread at least sixteen, larger scales allow further inversion types;
the classification (3) must not be applied there. Divergent trajectories
are also not addressed by the finite-cycle permutation argument.

Reproduce the kernel checks with the pinned Lean 4.33.1 compiler:

```sh
mkdir -p /tmp/collatz-folded-nine
lean -o /tmp/collatz-folded-nine/CollatzCycleCriterion.olean CollatzCycleCriterion.lean
LEAN_PATH=/tmp/collatz-folded-nine lean -o /tmp/collatz-folded-nine/FoldedCycleBounds.olean lean/FoldedCycleBounds.lean
LEAN_PATH=/tmp/collatz-folded-nine lean lean/FoldedCycleNine.lean
```

The verification record is in
[results/folded-inversions/verification.json](../results/folded-inversions/verification.json).
It distinguishes the kernel lemmas from the written sorting and permutation
arguments. The new module uses no native evaluation or admitted proofs.
