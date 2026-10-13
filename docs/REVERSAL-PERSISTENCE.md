# Long persistence after a count reversal

The positive-integer Collatz conjecture remains unresolved. This note rules
out two ways of extending the parent-loss argument from
[ordered weight drift](ORDERED-WEIGHT-DRIFT.md): allowing a fixed number of
future parent steps does not repair its pointwise failure, and charging a
cell's accumulated negative drift to all its future parent losses also
fails. Averaging over source intervals remains a possible route.

The endpoint inequalities and the all-parameter persistence statements
below have kernel proofs in [ReversalPersistence.lean](../lean/ReversalPersistence.lean).
The passage to real weights, limits, and sums is a written argument.
No new external theorem is used.

## 1. Weight retention at a large endpoint

Use the shortcut map \(U\), and let \(a_h(x)\) count its odd inputs in the
first \(h\) steps. Define
\[
 W_h(x)=\frac{x3^{a_h(x)}}{2^hU^h(x)},\qquad
 z_h(x)=\frac{3^{a_h(x)}}{2^h(U^h(x)+1)}.
\]
For every positive integer \(x\) and \(h\ge0\), the kernel proves
\[
 3\,2^hU^h(x)+3^{a_h(x)}
       \le3^{a_h(x)}(3x+2^h),\qquad
 2^h(U^h(x)+1)\le3^{a_h(x)}(x+2^h).                 \tag{1}
\]
Both are inductions on the actual orbit; no parity randomness or terminal
behavior is assumed. Consequently
\[
 W_h(x)\ge\frac{3x}{3x+2^h-1},\qquad
 z_h(x)\ge\frac1{x+2^h}.                            \tag{2}
\]

Suppose a normalized parent value at the current clock is \(P\) and its
endpoint is \(X\). Write \(P_h,Z_h\) for its original and shifted values
after another \(h\) steps, so \(P_0=P\),
\(Z_0=PX/(X+1)\). Weight factorization and (2) give
\[
\begin{split}
0\le P-P_h&\le\frac{P(2^h-1)}{3X},\\
0\le Z_0-Z_h&\le
 \frac{PX(2^h-1)}{(X+1)(X+2^h)}
 \le\frac{P(2^h-1)}X.
\end{split}                                                       \tag{3}
\]
Thus the same combination of losses used in the ordered argument obeys
\[
 3(P-P_h)+2(Z_0-Z_h)\le\frac{3P(2^h-1)}X.           \tag{4}
\]
The right side tends to zero whenever \(2^h/X\to0\), including every
fixed lookahead \(h\).

## 2. A downward refinement lasting linearly many steps

Take an even integer \(j\ge2\), and set
\[
 n_j=\frac{8(64^j-1)}9,\quad k_j=6j-1,\quad
 R_j=3^{3j-1},\quad X_j=\frac{R_j+1}4,\quad H_j=3j-5.
\]
The source lies in \([2^{k_j},2^{k_j+1})\). The earlier kernel family
theorem gives, at parent clock \(t=k_j+6\),
\[
 U^t(n_j)=X_j,\quad a_t(n_j)=3j+1,\qquad
 U^t(3n_j+2)=1,\quad a_t(3n_j+2)=2.
\]
The even/odd refinement pair has already reversed its odd-count order.
Its normalized parent and odd-child values at offset six are
\[
 P=\frac{9R_j}{16(R_j+1)},\qquad B=\frac{27}{64}.     \tag{5}
\]
At offset \(6+h\), denote these values by \(P_h,B_h\). The kernel
proves, for **every** \(0\le h\le H_j\), the cross-multiplied statements
\[
 P_h\ge\frac12,\qquad B_h\le\frac{27}{64},           \tag{6}
\]
and also proves that the history still includes a count reversal.
For the first inequality, it verifies
\(4\,2^h\le X_j\), uses (1), and uses \(R_j\ge26\).
For the second, the child starts at one and its weight cannot increase.
This does not require knowing the parent's future orbit.

It follows, as a written rational comparison, that throughout this interval
\[
 P_h(P_h-B_h)_+\ge\frac5{128},\qquad
 (P_h-B_h)^2\ge\frac{25}{4096}.                     \tag{7}
\]
There are \(H_j+1=3j-4\) such offsets. The unaveraged negative drift
accumulated by this one cell is therefore at least
\[
 \sum_{h=0}^{H_j}P_h(P_h-B_h)_+
       \ge\frac5{128}(3j-4).                        \tag{8}
\]
This grows without bound. Its horizon is proportional to the source's
binary length: \(k_j=6j-1\).

## 3. Two parent-loss charges that cannot work

First, the initial negative product in (5) tends to \(81/1024>0\),
whereas (4) tends to zero for fixed \(h\). Hence no universal multiplier
can charge every reversed downward cell to the next \(h\) parent steps.
More generally, this fails along any horizons satisfying
\(2^{h_j}/X_j\to0\). In particular it fails even for
\(h_j=H_j\), since \(2^{H_j}/X_j\to0\).

Second, allowing *all* future parent losses cannot pay for the sum of a
cell's negative drift over offsets. Both parent weights decrease and are
nonnegative, so their limits exist and telescoping gives
\[
\begin{split}
\sum_{h\ge0}\{3(P_h-P_{h+1})+2(Z_h-Z_{h+1})\}
 &\le3P+2Z_0\\
 &<5P<\frac{45}{16}.                               \tag{9}
\end{split}
\]
Combining (8) and (9), any multiplier for that cell must exceed
\((3j-4)/72\). There is no multiplier uniform over the family.
These statements are unconditional obstructions, not claims of divergent
Collatz trajectories.

Each odd half-cell has length \(2^{-(k_j+1)}\). The guaranteed persistence
rectangles in source/offset space have finite total measure:
\[
 \sum_{m\ge0}\frac{6m+2}{2^{12m+12}}
   =\frac{2q(1+2q)}{(1-q)^2}<\infty,
 \qquad q=2^{-12},\quad j=2m+2.                    \tag{10}
\]
Thus these rectangles do not refute an integrated estimate. Equation (10)
concerns only the displayed finite horizons; it makes no assertion about
the all-time contribution of the entire family.

## 4. A precise averaging question

Retain \(A_{s,k}(n),Z_{s,k}(n),B_{s,k}(n)\) from the earlier note. Define
the whole-annulus parent-loss average
\[
 L_{s,k}=\frac1{2^{k+1}}\sum_{2^k\le n<2^{k+1}}
 \{3(A_{s,k}(n)-A_{s+1,k}(n))
       +2(Z_{s,k}(n)-Z_{s+1,k}(n))\}.              \tag{11}
\]
The factor \(2^{-(k+1)}\) matches the odd half-cell measure. An open,
sufficient estimate is
\[
             N^{\rm rev}_{s,k}\le C L_{s,k}
             \quad\hbox{for all }s,k.             \tag{12}
\]
It allows other source cells to supply the loss. Neither the pointwise
obstructions above nor the finite computations prove or disprove (12)
for an arbitrary fixed \(C\).

To check precisely why (12) would suffice, let
\(J(S)=\lceil121S/50\rceil\). The earlier deficit bounds telescope to
\[
 \sum_{s<S,k\ge0}L_{s,k}\le\frac52J(S)+\frac{27}4.
\]
Together with \(\sum_sN_s^{\rm ord}\le14\) and the existing energy
identity, (12) would yield
\[
 \limsup_{S\to\infty}\frac1S\sum_{s<S}E_s
       \le\frac12+\frac{121}{10}C.                \tag{13}
\]
This is a conditional deduction. The earlier packing/rigidity/positive
predecessor-density route would then exclude escape. Other cycles would
still have to be excluded separately.

The independent rational replay checks (12) with \(C=8\) only on the
finite rectangle \(0\le k\le10\), \(0\le s\le96\). It also certifies
that \(C=6\) already fails at \((k,s)=(5,46)\), where
\(N^{\rm rev}_{46,5}/L_{46,5}\) is approximately \(6.607568\).
All comparison decisions use exact fractions or rational enclosures;
the decimal is for display. There is no extrapolation to larger clocks
or levels, and no claim that eight is a valid universal constant.

## 5. Reproduction and scope

Run `python3 verify_reversal_persistence.py`. The
[verification record](../results/reversal-persistence/verification.json)
records fresh sequential builds of the five local modules, the eight
new kernel roots and their standard-axiom audit, exact independent
endpoint and family checks, finite annulus comparisons, and source/log
hashes. The previous ordered-drift record is revalidated without
rewriting it.

The real-weight factorization, inequalities (3)--(10), and the conditional
averaged-energy implication are written deductions from kernel inputs.
The finite annulus checks do not settle (12). No escape exclusion,
additional-cycle exclusion, or full Collatz proof is claimed.
