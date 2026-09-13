# A geometric restriction on mask positions improves the cycle span

**Written theorem.** Every nontrivial positive integer Collatz cycle, with
odd minimum \(m\) and odd maximum \(M\), satisfies
\[
 \boxed{20M>49m.}                                      \tag{1}
\]
Thus \(M/m>2.45\). This strengthens the earlier all-period bound
\(4M\ge9m+5\) for the possible large minima; that earlier inequality remains
valid as well.

The proof uses the [narrow-cycle classification](NARROW-CYCLE-MASKS.md),
the [explicit logarithm estimate and finite exclusion](EXPLICIT-LOG-GAP.md),
and a new restriction on the positions where an integer mask can be edited.
The finite cover and the published small-period input are reused, not rerun.
The complete theorem remains a written argument: the real logarithms,
circle counting, and assembly with those earlier results are not formalized
in Lean.

[MaskSpanBounds.lean](../lean/MaskSpanBounds.lean) kernel checks the exact
power comparisons, the residue identity locating edit centers, the integer
grid-spacing lemma, the passage from fixed block counts to arbitrary
windows, and the cutoff arithmetic. It uses no native evaluation.

## 1. Reduce a possible exception to the narrow mask family

It suffices to consider the primitive underlying cycle. Write \(k\) for
its number of odd members and \(N=\sum h_i\) for its shortcut period:
\[
 2^{h_i}x_{i+1}=3x_i+1,\qquad x_0=m.
\]
A nontrivial cycle has \(m\ge5\), because 1 and 3 reach the known cycle.
Suppose, towards a contradiction, that \(20M\le49m\). Then
\[
 3M+1<8m.
\]
This implication is kernel proved already for \(m\ge2\).

The narrow-cycle classification supplies
\[
 N=\lceil k\log_2 3\rceil,\quad \gcd(k,N)=1,\quad
 b_i=\lfloor(i+1)N/k\rfloor-\lfloor iN/k\rfloor,
\]
and layers
\[
 a_i=\mathbf1_{\{x_i\ge2m\}},\qquad
 h_i=b_i+a_i-a_{i+1}.
\]
Each \(a_i=1\) selects a disjoint \(21\to12\) edit of the base word.
At the minimum cut \(a_0=a_k=0\).

The existing finite exclusion handles every such nontrivial cycle with
\(N\le10^{4000}\), including the smaller range supplied by the documented
external input. Consequently an exception to (1) must have
\[
 N>10^{4000},\qquad t=\log_2 N>12000.                    \tag{2}
\]
Throughout the remaining proof put
\[
 \rho=k/N,\quad \alpha=\log_3 2,\quad
 \lambda=N\log2-k\log3.
\]
The earlier full-mask catalog argument gives
\[
 0<\lambda<4/N^2                                      \tag{3}
\]
for a hypothetical integer realization once \(N\ge2^{64}\).
This is the pre-division height estimate in
[MASK-FOLDED-ORDER.md, Section 4](MASK-FOLDED-ORDER.md#4-the-surviving-integer-mask-range-already-satisfies-the-condition).
It uses the unrestricted catalog, so it does not assume the new position
restriction or the result being proved here.

## 2. The maximum confines every selected edit to a short phase interval

Let
\[
 c_i=2^{1-a_i},\qquad u_i=c_i x_i,\qquad
 S_i=\lfloor iN/k\rfloor,\qquad j_i=iN\bmod k.
\]
The folded equations are
\[
 2^{b_i}u_{i+1}=3u_i+c_i,\qquad u_0=2m.
\]
Iterating their strict positive-forcing inequalities gives, for
\(1\le i<k\),
\[
 2^{S_i}u_i>3^i(2m).                                  \tag{4}
\]
The general integer iterate behind (4) is already kernel proved as
`MaskFoldedOrder.scaled_iterate_lt`.

When \(a_i=1\), the folded value is \(u_i=x_i\le M\le49m/20\).
Taking logarithms in (4), and using
\(iN=kS_i+j_i\), yields
\[
 \frac{j_i}{k}\log2
 <\log(49/40)+\frac{i}{k}\lambda
 <\log(49/40)+\lambda.                                 \tag{5}
\]
There is no selected edit at \(i=0\). At every other index,
coprimality gives \(0<j_i<k<N\).

In the binary encoding \(h\mapsto10^{h-1}\), this edit moves the base
one at position \(S_i\) one place to the left. Its base phase is
\[
 \{S_i\rho\}=1-\frac{j_i}{N}
            =1-\rho\frac{j_i}{k}.                      \tag{6}
\]
Indeed \(S_i k+j_i=iN\), so
\((S_i k)\bmod N=N-j_i\). The residue statement is kernel checked.
It also handles centers near the cyclic seam when positions are interpreted
modulo \(N\).

Since \(\rho/\log2<1/\log3\), (5) gives
\[
 \rho\frac{j_i}{k}
 <\frac{\log(49/40)+\lambda}{\log3}
 <\frac{37}{200}+\frac1{10^6}
 =:W=\frac{185001}{10^6}.                              \tag{7}
\]
The first constant follows from the exact kernel-checked inequality
\[
 49^{200}<40^{200}3^{37}.
\]
For the second, (3), \(N>10^8\), and \(\log3>\log2>1/2\) give
\(\lambda/\log3<8/N^2<10^{-6}\).

Equations (6)–(7) prove the new restriction:
\[
 \boxed{\text{a selected center at binary position }s
        \text{ must satisfy }\{s\rho\}\in[1-W,1).}       \tag{8}
\]
This restricts the positions where choices can be made, rather than merely
their total number. It is necessary for the assumed maximum bound, not a
sufficient condition for an integer cycle.

## 3. Every 1054 consecutive positions have at most 196 allowed centers

The following exact comparisons are kernel checked:
\[
 3^{15601}<2^{24727},\quad 2^{1054}<3^{665},\quad
 665\cdot24727-15601\cdot1054=1.
\]
They imply
\[
 \frac{15601}{24727}<\alpha<\frac{665}{1054}.
\]
Also
\[
 0<\alpha-\rho=\frac{\lambda}{N\log3}<\frac1N<10^{-8},
\]
where even the elementary bound \(\lambda<\log2\) suffices.
Therefore, with \(p=665,q=1054,\varepsilon=10^{-7}\),
\[
 0<\frac pq-\rho
 <\frac1{1054\cdot24727}+10^{-8}<\varepsilon.            \tag{9}
\]
The final rational comparison is checked after clearing denominators.

For any starting phase \(\theta\), compare the \(q\) points
\(\{\theta+r\rho\}\), \(0\le r<q\), with
\(\{\theta+rp/q\}\). Their distances on the circle are less than
\(q\varepsilon\). Since \(\gcd(p,q)=1\), the second collection is an
equally spaced grid of \(q\) distinct points.

Every point of the first collection lying in the arc from (8) corresponds
to a grid point in the enlarged arc of length
\[
 \ell=W+2q\varepsilon<1.
\]
An arc of length \(\ell\) contains at most \(\lfloor q\ell\rfloor+1\)
points of a \(q\)-grid. To see this, lift that arc to the real line and
sort the included grid points; successive points differ by at least
\(1/q\). The corresponding statement for integer grid labels, including
lifts across the seam, is kernel proved in `integer_grid_count`.

Here the exact arithmetic gives
\[
 q\ell=qW+2q^2\varepsilon
      =195.2132372<196.
\]
Thus every block of 1054 consecutive positions contains at most 196
allowed centers. Partitioning any \(L>0\) window into whole blocks and a
possibly shorter final block gives
\[
 \#\{\text{allowed centers in the window}\}
 \le196(\lfloor L/1054\rfloor+1)
 <\frac3{16}L+196,                                    \tag{10}
\]
using \(16\cdot196<3\cdot1054\).
The block-count implication holds for any Boolean sequence and is
kernel proved; it does not require a periodic sequence or aligned windows.

The rotation argument covers every starting phase and every slope
satisfying (9). The independent Python checks of particular slopes are
sanity checks of this argument, not a substitute for its quantifiers.

## 4. The restricted factor catalog is too small for an integer cycle

Let \(P_w(r)\) count distinct length-\(r\) factors of the actual binary
cycle word. The base binary word is mechanical and has at most \(r+1\)
length-\(r\) factors.

A resulting length-\(r\) factor depends on its base factor and the selected
centers in the \(r+1\) positions from its first position through one after
its last. Centers move a one from \(s\) to \(s-1\), which explains both
endpoints of this window.

For fixed \(\rho,W\), the allowed-center pattern
\[
 (\mathbf1_{[1-W,1)}(\{\theta+j\rho\}))_{j=0}^{r}
\]
has at most \(2(r+1)+1\) possibilities as \(\theta\) varies. Each coordinate
has two change points on the circle; the half-open endpoint convention
introduces no isolated extra pattern at a boundary. The additional one
is a harmless allowance for coincident boundaries or an empty list.

We can bound the number of joint base and allowed-center patterns by
the product of their separate bounds, whether or not all combinations
are realizable. On each pattern, (10) bounds the number of binary edit
choices. Allowing choices at ineligible base centers only increases this
upper bound. Consequently the following convenient, conservative bound
holds for every \(r>0\):
\[
 \boxed{
 P_w(r)\le2(r+4)^2
          2^{196(\lfloor(r+1)/1054\rfloor+1)}.          } \tag{11}
\]
The argument is uniform in the period and in the mask. It counts all
cyclic cuts, including windows that cross the minimum cut.

The explicit logarithm estimate gives the earlier full-mask height bound
\[
 \text{every shortcut state}<6N^{26/5}
       \qquad(N\ge10^{4000}).
\]
Choose
\[
 r=\lceil\log_2(6N^{26/5})\rceil<\tfrac{26}{5}t+4.
\]
The primitive cycle has \(N\) distinct shortcut states. Since two states
with the same first \(r\) parity bits agree modulo \(2^r\), the height
bound forces their parity factors to be distinct:
\[
 N\le P_w(r).                                         \tag{12}
\]
This is the existing kernel-checked finite parity-collision argument.

For \(t>12000\), we have \(r+4<6t\). Equations (10)–(12) would imply
\[
 N<72t^2\,2^{197}\,N^{39/40},
 \qquad\text{hence}\qquad
 2^{t/40}<72\,2^{197}t^2.                              \tag{13}
\]
At \(t=12000\), the left side is \(2^{300}\), whereas the right side is
less than \(2^{231}\), because
\[
 72\cdot12000^2<2^{34},\qquad197+34<300.
\]
The ratio \(2^{t/40}/t^2\) increases for \(t\ge12000\):
its logarithmic derivative is \(\log2/40-2/t>0\), using \(\log2>1/2\).
Thus (13) is impossible throughout (2). This excludes the last possible
range and proves (1).

## 5. Scope, evidence, and the remaining problem

The small-period external dependency and the prime estimates are exactly
those identified in [EXPLICIT-LOG-GAP.md](EXPLICIT-LOG-GAP.md). The earlier
extended finite cover uses native evaluation, with an independent Python
replay. This new argument introduces no additional external theorem and
does not rerun the published convergence computation.

Reproduce the new finite arithmetic checks from the repository root:

    lean lean/MaskSpanBounds.lean
    python3 verify_mask_span.py

The [verification record](../results/mask-span/verification.json) records
source hashes and identifies reused evidence. The new Lean module is
entirely kernel checked, but it is not a formal proof of the full statement
(1). Its logarithmic and factor-catalog bridges, and the complete
cycle-classification argument it uses, remain written proofs.

The stronger bound is still compatible with positive rational mask cycles
and with wider hypothetical integer cycles. It leaves the unrestricted
mask divisibility problem, arbitrary wider cycles, and aperiodic divergence
unresolved. It is not a proof or disproof of the Collatz conjecture.
