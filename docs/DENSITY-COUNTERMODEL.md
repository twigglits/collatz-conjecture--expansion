# An escaping map with positive predecessor densities

**This is a comparison map, not the Collatz map or a Collatz counterexample.**
It keeps even halving and the cycle \(1\to4\to2\to1\), but changes the
odd branch. Exactly half its positive starts converge to that cycle;
the other half escape to infinity. Nevertheless it has positive
predecessor densities, a target-uniform density limit, small first-passage
atoms, and sparse orbit values. These properties therefore do not by
themselves close the [branch-density argument](DENSITY-BRANCH-LEAKAGE.md).
The missing comparison must use additional arithmetic of \(3n+1\).

The explicit escaping family and the known cycle are kernel checked in
[DensityCountermodel.lean](../lean/DensityCountermodel.lean). The density,
passage, and packing results below have elementary written proofs and
separate finite checks. They do not use the project's unformalized
analytic first-passage proposition.

## 1. Definition and complete orbit classification

For a positive integer \(m\), put \(p(m)=2^{\lfloor\log_2m\rfloor}\).
There are two types of odd states:
\[
       g_m=4m-3,\qquad d_m=4m-1.
\]
Their accelerated odd maps are
\[
 G(m)=\begin{cases}
 1&m=1,\\ m/2&m>1\text{ is a power of two},\\
 m-p(m)&m\text{ is not a power of two},
 \end{cases}\qquad
 D(m)=\begin{cases}
 2m&m\text{ is a power of two},\\
 m-p(m)&\text{otherwise}.
 \end{cases}                                             \tag{1}
\]
Thus the first map reaches index one. The second removes leading binary
ones until only the lowest set bit remains, then repeatedly doubles.

Define an ordinary map \(F\) as follows. Set \(F(n)=n/2\) for even
\(n\), and \(F(1)=4\). At any other odd state with a power-of-two
index, set
\[
 F(g_m)=2g_{m/2}\quad(m>1),\qquad F(d_m)=2d_{2m}.
\]
For a non-power index, let \(L=\lfloor\log_2m\rfloor\),
\(r=m-2^L>0\), and \(k=\lfloor\log_2r\rfloor\). Set
\[
 F(g_m)=\begin{cases}2^{L+2}&r=1,\\2^{L-k+1}g_r&r>1,\end{cases}
 \qquad F(d_m)=2^{L-k+1}d_r.                              \tag{2}
\]
All these images are positive and even. Removing their powers of two
gives exactly (1). The special exponent at \(g_m\) with \(r=1\)
reserves the edge \(1\to4\), keeping at most two ordinary parents
per target.

Every start whose odd part is \(1\pmod4\) reaches the cycle
\(1,4,2\). Every start whose odd part is \(3\pmod4\) escapes. Both
sets have natural density \(1/2\): the sets with a specified initial
valuation \(t\) and either odd residue have density \(2^{-t-2}\).

In particular, with \(b_k=4\cdot2^k-1\),
\[
            F(b_k)=2b_{k+1},\qquad F^2(b_k)=b_{k+1}.     \tag{3}
\]
The kernel proves these identities for every \(k\), the formulas for
every even and odd iterate, nonarrival at one, and unboundedness. It
also checks \(F(3)=14\ne10=C(3)\), making the changed map explicit.

## 2. Binary predecessor trees and exact density formulas

There is always the even parent \(2a\). An odd target has no other
parent. Write an even target as \(a=2^v q\), where \(v\ge1\),
\(q=4m-c\), \(c\in\{1,3\}\), and \(k=\lfloor\log_2m\rfloor\).
There is at most one odd parent:

| Target case | Odd parent, when it exists |
| --- | --- |
| \(v=1,c=3,m\) a power of two | \(g_{2m}\) |
| \(v=1,c=1,m\ge2\) a power of two | \(d_{m/2}\) |
| \(q=1,v=2\) | \(1\) |
| \(q=1,v\ge3\) | \(2^v+1\) |
| \(q\ne1,v\ge2\) | \(4(2^{k+v-1}+m)-c\) |

In all remaining cases there is none. These cases follow directly from
(2) and the power-index clauses. Every listed parent is at most \(3a\).
Thus the map also has the same elementary binary bound on bounded-time
inverse fibres as ordinary Collatz.

Let \(r_a\) denote its natural predecessor density. For odd targets,
\[
\begin{array}{c|c}
\text{target}&r_a\\\hline
g_{2^k}&2^{-k-1}\\
d_{2^k}&\tfrac12-2^{-k-2}\\
4m-c,\quad 2^k<m<2^{k+1}&2^{-k-2}.
\end{array}                                               \tag{4}
\]
For even targets \(a=2^v q\), with \(q\) odd,
\[
 r_{2q}=r_q,\qquad r_4=\tfrac12,\qquad
 r_{2^v}=2^{1-v}\ (v\ge3),\qquad
 r_{2^v q}=2^{-k-v}\ (v\ge2,q\ne1),                     \tag{5}
\]
where \(k\) is the binary level of the index of \(q\).

Here is a direct counting proof, including the infinite branches. Among
odd sources of the same type, a non-power index \(m\) is hit precisely
by indices congruent to \(m\pmod{2^{k+1}}\). A power index \(2^k\)
is hit by indices divisible by \(2^k\) in the good component, and by
indices not divisible by \(2^{k+1}\) in the escaping component. This
proves (4) for uniform odd sources.

For \(v\ge2,q\ne1\), an odd source hits \(2^v q\) exactly when its
index is congruent to \(m\pmod{2^{k+v-1}}\) and is larger than \(m\).
Its next higher set bit specifies the last odd parent before \(q\).
For \(q=1,v\ge3\), the corresponding good indices are
\(1\pmod{2^{v-2}}\), excluding index one. These single residue classes
prove (5) without exchanging a density limit with an infinite union.
The equality at \(2q\) only removes the possible starting point \(q\)
from the odd-source predecessor set. The cyclic cases are immediate.

Conditioning general sources on their initial power of two transfers
the same limits to natural density. An initial halving segment adds
only possible sources \(2^j a\), which have density zero. These explicit
formulas give the stronger, target-uniform lower bound
\[
                    \boxed{r_a\ge\frac1{2a}\quad(a\ge1).} \tag{6}
\]
They also give uniform convergence, with an explicit coarse error:
\[
 \sup_{a\ge1}\left|\frac{\#\{1\le n\le X:n\to^*a\}}X-r_a\right|
        \le\frac{8(1+\lfloor\log_2X\rfloor)}X
                  \quad(X\text{ a positive integer}).    \tag{7}
\]
Indeed each odd-source count is a residue count, a difference of two
such counts, or one of these with a single index excluded. Its error
against \(r_a\) times the number of odd sources is at most three,
uniformly in the modulus and target. There are at most
\(1+\lfloor\log_2X\rfloor\) initial-valuation groups; the additional
initial-halving sources cost at most that many counts. The constant
eight in (7) leaves room for all rounding conventions.

## 3. Diffuse first passage with an explicit error

Let \(F_H^*(n)\) be the first **odd** orbit value at most \(H\), or
\(\infty\) if none occurs. Take integer \(H\ge7\). For type
\(c\in\{1,3\}\), put
\[
 h_c=\left\lfloor\frac{H+c}{4}\right\rfloor,\quad
 q_c=2^{\lfloor\log_2h_c\rfloor},\quad Q_c=2q_c.
\]
For an odd source \(4m-c>H\), write \(z=m\bmod Q_c\). Its landing
index is
\[
 \begin{cases}
 q_c&z=0,\ c=3,\\
 \infty&z=0,\ c=1,\\
 z&1\le z\le h_c,\\
 z-q_c&z>h_c.
 \end{cases}                                             \tag{8}
\]
Deleting leading ones proves this formula; in the zero-residue case a
good power descends, whereas an escaping power never returns. Convert
a finite index \(z'\) back to the odd value \(4z'-c\).

The mark is therefore periodic among odd sources above \(H\), with
period \(P=4\max(Q_1,Q_3)\le4H\). Let \(\nu_H\) be its law for a
uniform odd residue in a period. Each finite landing has at most two
index residues in its component. Consequently
\[
 \|\nu_H\|_\infty\le\frac8H,\qquad
 \nu_H(\infty)=\frac1{2Q_1}.                              \tag{9}
\]
For uniform odd \(\mathbf U_Y\) in \([Y,2Y)\), with integer \(Y>H\),
counting residues gives
\[
 d_{\rm TV}(F_H^*(\mathbf U_Y),\nu_H)
                            \le\frac{4H}{Y}.             \tag{10}
\]
The elementary residue error is at most \(P/Y\); pushing a law through
a deterministic mark cannot increase total variation. In particular
for any fixed \(\alpha>1\) this is a power saving at
\(Y\ge H^\alpha\), stronger than the logarithmic error used in the
Collatz density notes. Initial halving changes no mark; conditioning
on its valuation gives the same limiting law for all positive sources.

The minimum distribution is also explicit:
\[
 p_1=\tfrac12,\qquad p_{4\cdot2^k-1}=2^{-k-2}\ (k\ge0),
 \qquad p_m=0\text{ otherwise}.                          \tag{11}
\]
It is a countably additive probability law, despite escape having
positive density. Its geometric tail also gives almost-bounded minima.

## 4. Sparse paths and decay inside fixed basins

During the descent part of either odd-index path, the binary level of
the odd value decreases at each step. Its ordinary image is less than
four times that odd value. In a band \([2^j,2^{j+1})\), at most one
descent block can first cross down from above the band; after that only
the two odd levels immediately below the band can produce a spike back
into it. Each halving block contains at most one even value in the band.

Adding the initial halving segment, the odd values themselves, and the
terminal cycle or explicit escaping tail gives at most ten distinct
values per dyadic band. An integer interval of length \(L\ge1\) either
lies above \(L\) and crosses at most two bands, or lies below \(2L\).
Hence every orbit has at most \(10(\log_2L+2)\) distinct values in it.
This is stronger than a sublinear power packing bound. In particular
reciprocal values on the escaping orbit are summable.

The formulas also give \(r_a\le8/a\), except on the odd escaping spine
and its single-doubling targets. Only finitely many of those exceptional
targets can reach any fixed target. Thus predecessor densities tend to
zero uniformly at large values **within each fixed predecessor basin**.
This still coexists with \(r_{b_k}\uparrow1/2\) along escape.

## 5. The relative comparison really fails

At the merge \(2b_{k+1}\), the two parents are \(b_k\) and
\(u_k=4b_{k+1}\). Equations (4)–(5) give
\[
 r_{u_k}=2^{-k-3},\qquad
 \frac{r_{u_k}}{r_{b_k}}=\frac1{2^{k+2}-2}
                       =\frac1{b_k-1}.                  \tag{12}
\]
These strictly positive relative contributions are summable, and their
product by \(1+\log b_k\) tends to zero. Even the explicit global bound
(6) cannot make them nonsummable.

This is a counterexample to deriving a logarithmic relative branch
bound from the listed density, passage, halving, cycle, and packing
properties alone. It does **not** satisfy the Collatz odd-step identity
\(F(n)=3n+1\), or every consequence of that identity. For example its
predecessor densities at multiples of three need not vanish. The actual
Collatz conjecture and the proposed relative comparison remain open.

## Verification

[The verification record](../results/density-countermodel/verification.json)
separates the kernel escape calculation from the written infinite
density formulas and the exact finite checks. The latter compare
symbolic-tail trajectories with the residue membership formulas, check
the inverse-parent formula, and check finite passage histograms and
their rational error bounds. Infinite tails are represented by (3),
not truncated and declared convergent or nonentering on a timeout.

```sh
python3 verify_density_countermodel.py
```

An optional `--reuse-build-dir` validates the existing standalone Lean
dependency; the new module is compiled afresh. No finite check here is
reported as a proof or disproof for ordinary Collatz.
