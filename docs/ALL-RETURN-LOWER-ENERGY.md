# Smaller-endpoint energy including every count return

**Collatz remains unresolved.** The previous smaller-endpoint estimate
omitted the one-step returns between odd-separation excursions. This
note includes them. Under the coherent binary residue law, let \(P_j\)
be the smaller formal endpoint at the \(j\)th count return, and kill at
balanced fusion, whose return index is \(N\). Then the new written bound is

\[
 \boxed{\mathbb E\sum_{1\le j<N}P_j
       \le A_*:=2100000+281000000C_*,\qquad C_*=540\,2^{5180}.} \tag{1}
\]

Consequently the lower-endpoint image components, now defined using
**all** nonfused returns, satisfy

\[
 \boxed{\sum_{t,a}\|\kappa^{\mathrm{low,all}}_{t,a}\|_2^2
                  \le2A_*<\infty.}                         \tag{2}
\]

Each component includes all its internal image overlaps. Products
between different components remain an additional issue. Neither (2)
nor the preceding nested-source bound proves a full \(L^2\) norm bound.
The endpoint choice still differs from the original fixed-endpoint
density \(K^*_0\). Actual forward-gradient control remains unproved.

The new input is a finite \(b\log b\) moment of the initially odd
endpoint's correction. Thirteen kernel arithmetic roots support the
argument. Probability, entropy, mixed moments, and infinite Haar sums
remain **written proofs**, using earlier local written results. No
external analytic theorem is used.

## 1. Two correction budgets before a fresh odd-separation return

Condition on either initial parity at a fresh odd separation. Label
the initially odd endpoint \(F\), the initially even endpoint \(S\),
and let \(\tau\) be the first positive count return. Until that return,
\(F\)'s count lead is positive. Write its correction as

\[
 b_F=\sum_{j<\tau}w_j,\qquad
 w_j=\tfrac12\mathbf1_{\{F\text{ odd at }j\}}
                     \lambda^{F}_{j+1,\tau}.                \tag{3}
\]

The [slope-tilt argument](RETURN-SLOPE-TILT.md) gives the remaining
mean slope \(3^{-k}\) from positive lead \(k\). The
[clock potential](RETURN-ANCESTRAL-OVERLAP.md) gives mean remaining
physical time at most \(V(k)=6k^2+20k\) under that tilt, conditional
on a return. Both statements hold after every finite prefix.

For the original fair active walk started at \(k\ge1\), the expected
number of visits to level \(l\ge1\) before zero is \(2\min(k,l)\).
For completeness, kill at \(0,K\), with \(K>k,l\). Its finite Green
row is
\[
 g_K(k,l)=\frac{2\min(k,l)(K-\max(k,l))}{K}.
\]
The source and homogeneous equations verify this formula. Increasing
\(K\) gives the asserted row by monotone convergence. In particular it
is at most \(2l\), uniformly in the starting lead.

Put \(v(l)=v_2(3^l-1)<2l\). A visit to lead \(l\) has mean at most
\(v(l)+1\) holding steps. Each odd holding step contributes mean
remaining correction \(3^{-l}/2\); an odd outward active step
contributes \(3^{-(l+1)}/2\). Predictability of holding and fairness
of the fresh parity give the per-visit bound
\[
           \tfrac14 3^{-l}\{v(l)+4/3\}.
\]
Thus the mean **new** correction accumulated from any finite prefix
with positive lead, through its subsequent return, is at most
\[
 \sum_{l\ge1}\tfrac l2 3^{-l}(2l+4/3)=2.                    \tag{4}
\]
This is a restart bound for the new correction, not for the existing
correction multiplied by the remaining slope.

Also weight each contribution in (3) by its remaining physical age.
The conditional tilted clock bound gives
\[
 \begin{aligned}
 \mathbb E\sum_{j<\tau}w_j(\tau-j-1)
 &\le \tfrac16 V(1)
   +\tfrac12\sum_{l\ge1}
      \bigl[(2l+1)3^{-l}V(l)+3^{-(l+1)}V(l+1)\bigr]\\
 &=\frac{315}{4}.                                         \tag{5}
 \end{aligned}
\]
Here the Green row from one is two at each level. The first term is
the initial odd contribution. Every conditioning is at a finite
prefix; no independence of a holding duration and its direction is
assumed. The kernel checks geometric sums with explicit nonnegative
remainders and the recurrence for the actual age-weighted numerator.

## 2. An entropy moment of the fast correction

The existing clock tail is \(7/\sqrt h\) before conditioning on the
first parity, so \(14/\sqrt h\) is a valid bound after either such
conditioning. For integer \(h\ge1\), split (3) after physical clock
\(h\). Contributions already made have remaining age greater than
\(h\) on \(\{\tau>2h\}\). Equation (5) bounds their total restricted
mean by \(315/(4h)\). The contributions made later have conditional
mean at most two by (4), and occur only if \(\tau>h\). Hence
\[
 \mathbb E[b_F\mathbf1_{\{\tau>2h\}}]
       \le\frac{315}{4h}+\frac{28}{\sqrt h}
       \le\frac{107}{\sqrt h}.                            \tag{6}
\]

The elementary dyadic bound
\(\log_2\tau\le1+\sum_{j\ge1}\mathbf1_{\{\tau>2^j\}}\),
the prior \(\mathbb E b_F\le5/4\), and \(2^{-1/2}<3/4\) show that
\[
                      \mathbb E[b_F\log_2\tau]<430.         \tag{7}
\]
For any finite nonnegative list with sum \(b\), the entropy inequality
gives \(b\log_+b\le\sum w_j\log_+w_j+b\log\tau\) when the list
has at most \(\tau\) entries. Interpret \(0\log_+0=0\). Since
\(w_j\le(3/2)^{\tau-j-1}\), (5), (7), and
\(\log_2(3/2)<3/5\) give
\[
 \boxed{\mathbb E[b_F\log_{2,+}b_F]\le480.}                 \tag{8}
\]

This does not assert a moment of order greater than one. In particular
the corresponding initially even correction still has infinite mean.
All infinite sums above have nonnegative terms. Finite cutoffs followed
by Tonelli or monotone convergence justify their ordering.

## 3. A mixed minimum/separation drift at odd separation

Use \(P,D\) from [the grouped minimum argument](LOWER-RETURN-ENERGY.md),
and put \(L=\ell(D)=\log_2(D+1)\). At an odd-separation return,
\[
 P'=\lambda P+c,\qquad
 c=\min(b_L,\lambda D+b_H)\le b_F+\min(b_S,\lambda D).
                                                               \tag{9}
\]
Also \(D'\le\lambda D+b_F+b_S\). The existing tilted clock estimates
therefore supply
\[
 \mathbb E[\lambda\ell(D')]
       \le\tfrac12L+\tfrac{81}{10},\qquad
 \mathbb E[\lambda\tau^2]\le\tfrac{6369}{2}.               \tag{10}
\]

Here is a detailed bound on the correction term. Let
\(Y=1+\lambda+b_F+b_S\). Conditioning the prior unconditioned
quarter-moment bound on either initial parity gives
\(\mathbb E b_S^{1/4}\le9\); we allow the factor two explicitly.
Thus \(\mathbb E Y^{1/4}\le1+1+5/4+9<13\). Young's entropy inequality,
with \(1/\ln2\le2\), and (8) give
\[
 \mathbb E[b_F\log_2Y]
       \le4\{\mathbb E[b_F\log_{2,+}b_F]+2\mathbb EY^{1/4}\}
       \le2024.
\]
Since \(1+D'\le(D+1)Y\) and \(L\le8D^{1/4}\),
\[
                  \mathbb E[b_F\ell(D')]\le2034D^{3/4}.   \tag{11}
\]

For \(Q=\min(b_S,\lambda D)\), the previous reciprocal perpetuity
bound at exponent \(1/2\) gives, under the \(S\) slope tilt after the
initial even step, \(\widehat{\mathbb E}R_\infty^{1/2}<14\).
At return \(b_S/\lambda=2R_{\tau-1}\); the initial slope is \(1/2\).
Thus finite-cylinder change of measure gives
\[
 \mathbb E\frac{Q^2}{\lambda}
   =\tfrac12\widehat{\mathbb E}\min(2R_{\tau-1},D)^2
   \le10D^{3/2}.
\]
Indeed \(\min(x,D)^2\le D^{3/2}x^{1/2}\) and \(14\sqrt2<20\).
Cauchy--Schwarz and (10) imply
\(\mathbb E[Q\tau]\le179D^{3/4}\). The earlier clipped mean is
\(\mathbb EQ\le12L\), while the pathwise separation cap gives
\(\ell(D')\le L+(3/5)\tau\). Therefore
\[
 \mathbb E[Q\ell(D')]
       \le12L^2+(3/5)179D^{3/4}
       \le(768+108)D^{3/4}.                                \tag{12}
\]
We used \(L^2\le64D^{1/2}\le64D^{3/4}\). These bounds hold
conditional on either initial parity and every incoming finite prefix.
Combining (9)--(12) proves
\[
 \boxed{\mathbb E[P'\ell(D')]
       \le\tfrac12PL+\tfrac{81}{10}P+3000D^{3/4}.}         \tag{13}
\]

## 4. Include the common-parity runs

At a group start put \(v=v_2(D)\le L\). For the following \(v\)
common-parity steps, write \((\bar P,\bar D)\) for their final state.
The original fair law has
\[
 \mathbb E\bar P=P+v/4,\qquad
 \mathbb E\bar D^{3/4}\le D^{3/4}.
\]
To retain the correlation with the logarithm, write
\(\bar P=M_vP+B_v\). Slope tilting and the earlier logarithmic
one-step drift give
\(\mathbb E[M_v\ell(\bar D)]\le L+v/5\le6L/5\).
For the other term use the deterministic bound
\(\ell(\bar D)\le L+3v/5\) and \(\mathbb EB_v=v/4\). Thus
\[
             \mathbb E[\bar P\ell(\bar D)]
                         \le\tfrac65PL+\tfrac25L^2.         \tag{14}
\]
Apply (13) to the subsequent odd excursion. Equations (14) and
\(L\le8D^{3/4},\ L^2\le64D^{3/4}\) give
\[
 \mathbb E[P_{\rm next}\ell(D_{\rm next})]
       \le\tfrac35PL+\tfrac{81}{10}P+3030D^{3/4}.          \tag{15}
\]

Kill at fusion. Let \(m_j,p_j,z_j\) denote the group-start means
of \(P\ell(D),P,D^{3/4}\), including the indicator that the group
exists. Initially \(m_0=1\). The previous minimum budget and
the [all-return fractional separation budget](RETURN-SLOPE-TILT.md)
give
\[
 \sum p_j\le B_*:=4100+36000C_*,\qquad
 \sum z_j\le Z_*:=257+36864C_*.
\]
For the second inequality, apply its equation (19) at \(\eta=3/4\)
and add one for time zero; group starts are a subset of these returns.
Finite telescoping of (15), then monotone convergence, yields
\[
 \sum m_j\le\tfrac52+\tfrac{81}{4}B_*+7575Z_*.             \tag{16}
\]

Within a group, the exact expected sum of the formal minima at the
completed common-parity returns is
\[
 \mathbb E\sum_{h=1}^vP_h
       =vP+\frac{v(v+1)}8
       \le PL+9D^{3/4}.                                    \tag{17}
\]
The all-depth finite mean and occupation identities underlying (17)
are kernel proved. Add these costs over groups and include the
nonfused odd-excursion ends, whose total minimum cost is at most
\(B_*\). Equations (16)--(17) bound the complete sum by
\[
 \tfrac52+\tfrac{85}{4}B_*+7584Z_*
      =\frac{4072431}{2}+280341576C_*<A_*,
\]
proving (1). No one-step return has been discarded.

## 5. Component energy and the precise remaining overlap

For every even-source nonfused return prefix \(i\), retain its clock
\(t_i\), common count \(a_i\), and smaller actual image \(y_i\).
Define
\[
 \kappa^{\mathrm{low,all}}_{t,a}(z)
 =\sum_{i:t_i=t,\,a_i=a}2^{-t}3^a
                   \mathbf1_{\{z=y_i\pmod{3^a}\}}.
\]
The preceding selected-endpoint injection and fibre-rank proof applies
to every such return, without a grouping restriction. Consequently
\[
 \|\kappa^{\mathrm{low,all}}_{t,a}\|_2^2
       \le2\sum_{i:t_i=t,\,a_i=a}2^{-t}P_i.
\]
Sum and use (1) to obtain (2).

The earlier nested-source estimate also applies to these lower-image
columns: its bound on an ancestor pair was only
\(p_ip_j\int F_iF_j\le\Lambda_i p_j\), independent of which
ternary residues were selected. Changing the endpoint labels changes
compatibility but preserves this upper bound, the binary source
prefixes, the slopes and the separations.

In the full squared norm, separate: (i) all within-component products;
(ii) proper nested-source products; (iii) disjoint-source products
between distinct components. These classes are exhaustive and disjoint.
The first two have total at most
\[
                 2A_*+88C_*+2476820.
\]
Thus finiteness of the full lower-image \(L^2\) norm is equivalent to
finiteness of class (iii). Its finiteness or divergence remains unproved.
This is also not an ordinary-integer sampling result or a bound on
the actual future gradients paired with these densities. Criterion Q,
escape exclusion and additional-cycle exclusion remain open.

## Verification

Run `python3 verify_all_return_lower_energy.py`. The
[record](../results/all-return-lower-energy/verification.json) separates
thirteen kernel arithmetic roots, exact finite checks, and the written
infinite argument. Finite checks independently evaluate suffix correction
ages, actual positive-gap correction restarts, entropy and clipped mixed
costs, common-parity blocks, actual group-start mixed drift and every
lower-return image component. They
retain unfinished paths and use rational logarithm/power enclosures.
The finite data do not prove any infinite stopping or energy assertion.
