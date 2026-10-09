# A smaller exponential bound for inverse-fibre multiplicity

**Collatz remains unresolved.** A parity-prefix argument improves the
previous universal bound \(2^e\), where \(e\) counts even steps, to

\[
              N_{k,j}(y)\le B(e,0)\le 2\alpha^e,
       \qquad e=k-j,\quad \alpha=2^\delta=1.726541\ldots,       \tag{1}
\]

where \(2^{-\delta}+3^{-\delta}=1\) and
\(\delta=0.787884\ldots\). The finite recurrence \(B\), its applicability
at **every** depth and target, and the sharp two-even-step bound are
kernel checked in [FibrePrefixBound.lean](../lean/FibrePrefixBound.lean).
The real exponential estimate and the coefficient-moment consequences
below are written deductions, not Lean theorems. No novelty is claimed.

Here
\[
 N_{k,j}(y)=\#\{n\ge0:U^k(n)=y,\ w_k(n)=j\}.
\]
Restricting to positive sources can only reduce this number. At a fixed
depth, every fibre is finite by the earlier endpoint cap. The theorem
also directly bounds any finite list of distinct fibre members.

## 1. Width and spacing must be used together

The two [shifted affine envelopes](EQUAL-WEIGHT-FIBRES.md) imply, for two
members \(m,n\) of one fibre with \(e>0\),
\[
                         m+1<n+2^e.                       \tag{2}
\]
Indeed, the envelopes give
\[
 3^j(m+1)\le2^k y+2^j
             <2^k(y+1)\le3^j(n+2^e),
\]
since \(j<k\). For \(e=0\), the existing injectivity lemma applies.
In particular, an arithmetic progression of spacing \(q\ge2^e-1\)
contains at most one member of the fibre.

Consider source values on a grid \(3^a x+r\), with distinct natural
indices \(x\). Partition this grid by source parity. Since \(3^a\) is
odd, one part has \(x\) of each parity. Writing \(x=2z+b\),
an even Collatz step sends that part to a grid of spacing \(3^a\),
and an odd step sends the other part to a grid of spacing \(3^{a+1}\).
The respective grid offsets are
\[
 \frac{3^a b+r}{2},\qquad
 \frac{3(3^a b+r)+1}{2},
\]
with the appropriate parity \(b\in\{0,1\}\); these quotients are integers
on their corresponding parts. The map \(x\mapsto x/2\) is injective
within either part.

The even branch consumes one of the remaining \(e\) even steps. The odd
branch preserves \(e\) and increases \(a\) by one. This proves the bound
given by the recurrence
\[
 B(e,a)=
 \begin{cases}
  1,&3^a+1\ge2^e,\\
  B(e-1,a)+B(e,a+1),&3^a+1<2^e.
 \end{cases}                                               \tag{3}
\]
The second case implies \(a<e\), so both recursive calls decrease
\(e-a\). No infinite recursion or assumption about eventual orbit
behaviour is involved. Lean proves the grid version first and then
sets \(a=r=0\).

For two even steps, \(B(2,0)=2\). This is sharp at arbitrarily large
targets: for every natural \(q\), the two sources \(8q+4\) and \(8q+5\)
have exactly one odd step among their first three steps and both reach
\(3q+2\). These formulas are kernel checked for all \(q\).

Some recurrence values, independently computed in the Python replay,
are:

| Even steps \(e\) | \(B(e,0)\) | Previous bound \(2^e\) |
|---:|---:|---:|
| 2 | 2 | 4 |
| 6 | 31 | 64 |
| 10 | 341 | 1024 |
| 16 | 9389 | 65536 |
| 20 | 80386 | 1048576 |
| 30 | 18721780 | 1073741824 |

These are universal upper bounds, **not** asserted exact fibre maxima.

## 2. Written exponential estimate

Use the larger stopping tree that splits while
\(T=2^e/3^a>1\), with children \(T/2,T/3\). It can only have more leaves
than (3), which may stop earlier. Its leaf count is
\[
 L(T)=1\quad(T\le1),\qquad
 L(T)=L(T/2)+L(T/3)\quad(T>1).
\]
For \(T\ge1\),
\[
                            L(T)\le2T^\delta.             \tag{4}
\]
To prove this, \(L(1)=1\), \(L(T)=2\) for \(1<T\le2\), and
\(L(T)=3\) for \(2<T\le3\). The last case satisfies (4) because
\(2^\delta>3/2\): the defining equation and \(\delta<1\) give
\(2^{-\delta}=1-3^{-\delta}<2/3\). For \(T>3\), both children exceed
one, and induction on the finite tree gives
\[
 L(T)\le2(T/2)^\delta+2(T/3)^\delta=2T^\delta.
\]
Applying this at \(T=2^e\) proves (1).

For an explicit rational exponent without relying on a numerical root,
the kernel checks
\[
 1000^{24}<2^{19}579^{24},\quad
 1000^{24}<3^{19}421^{24},\quad
 2^{19}2000^{24}<3^{12}1999^{24}.                           \tag{5}
\]
The first two comparisons show
\(2^{-19/24}+3^{-19/24}<579/1000+421/1000=1\), hence
\(\delta<19/24\). The third gives
\[
            \frac{2^{19/24}}{\sqrt3}<\frac{1999}{2000}<1.  \tag{6}
\]
The extraction of positive real roots in these deductions is written
analysis; only the displayed integer comparisons are kernel checked.

## 3. The square-root coefficient moment is now covered

For positive sources, define the same coefficient moment used in the
earlier note:
\[
 Z_{k,s}(y)=\sum_{U^k(n)=y,\ n>0}
                     \left(\frac{3^{w_k(n)}}{2^k}\right)^s.
\]
For
\[
 s>\log_3\alpha=0.497100\ldots,
\]
grouping by \(e=k-j\) in (1) yields
\[
 Z_{k,s}(y)\le
 \frac{2}{1-\alpha/3^s}\left(\frac32\right)^{sk}.          \tag{7}
\]
The bound is uniform in the target \(y\). In particular, (5)–(6) give
the explicit, deliberately loose bound
\[
              \boxed{Z_{k,1/2}(y)\le4000(3/2)^{k/2}.}     \tag{8}
\]
The previous \(2^e\) argument only supplied (7) above
\(s>\log_3 2=0.630929\ldots\). The all-odd source
\(n=2^k q-1>0\), with \(q\ge1\), reaches \(3^k q-1\) and contributes
\((3/2)^{sk}\) by itself. Thus this exponential rate in \(k\) remains
optimal as a **uniform-target coefficient-moment** rate in the stated
range. The target in this witness varies with \(k\).

There is also a lower obstruction to extending the same rate to every
\(s>0\). Average over a complete target-residue interval of length
\(3^k\), chosen above \(3^k\) so all corresponding sources are positive.
Parity words bijectively label residues modulo \(2^k\), and the
weight-\(j\) group has \(\binom{k}{j}\) sources in its canonical block.
The exact affine lifts and canonical image bound therefore give
\[
 \operatorname{average}_y Z_{k,s}(y)
       =2^{-sk}\sum_{j=0}^k\binom{k}{j}3^{(s-1)j}
       =\left(\frac{1+3^{s-1}}{2^s}\right)^k.             \tag{9}
\]
When \(s<\log_3(3/2)=0.369070\ldots\), this average grows faster than
\((3/2)^{sk}\). Consequently no constant uniform in \(k,y\) can give
(7) in that range. The interval between this obstruction and the
proved threshold remains a gap; no optimal threshold is claimed.

## 4. What the enumeration checks

For a word with \(j\) odd steps and \(e\) even steps at positions
\(0\le i_0<\cdots<i_{e-1}<k=j+e\), the exact shifted identity is
\[
 2^k(y+1)=3^j(n+1)+E,
 \qquad E=\sum_{r=0}^{e-1}2^{i_r}3^{j-i_r+r}.              \tag{10}
\]
Thus words have the same canonical target exactly when their values
of \(E\bmod3^j\) agree. Canonical source reconstruction uses
\(n+1\equiv-E(3^j)^{-1}\pmod{2^k}\), taking \(1\le n+1\le2^k\).
The independent verifier compares this word algorithm with direct
Collatz trajectories, then uses it for selected larger odd counts.

The maximum found with nine even steps is 25 at seven odd steps
(depth 16), but rises to 26 at eight odd steps (depth 17). Finite
plateaus are not treated as all-index maxima. The all-index bound comes
from (3), not from extrapolation of any enumeration.

Run `python3 verify_fibre_prefix_bound.py` for fresh sequential kernel
builds, complete canonical residue windows through depth 18, selected
complete parity-word classes, grids of several spacings and offsets,
large affine lifts, and exact rational interval checks of (8) over
complete target-residue intervals through depth 9. See
[the manifest](../results/fibre-prefix-bound/verification.json) for the
precise counts and scopes. No external theorem is a proof input.

## 5. Remaining obstruction

Equation (8) bounds coefficients \(3^j/2^k\), not actual source weights
\(n^{-s}\), and it does not assert contraction of the actual survivor
sets. Its right side grows with time. Applying it unchanged to a
killed transfer operator gives no decay or pointwise descent.

This result also gives an **upper** bound on equal-weight fibre sizes.
It supplies no lower bound forcing a particular forward orbit to
acquire new merging starts. The earlier conditional stabilization
argument under divergence therefore does not become a contradiction.
Nontrivial positive cycles, divergent positive orbits, and the full
Collatz conjecture remain unresolved.
