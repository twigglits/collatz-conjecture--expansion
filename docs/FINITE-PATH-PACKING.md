# Finite trajectories and a time-independent first-entry correction

The interval-packing argument extends to every finite trajectory with
distinct states, including a trajectory that later converges. Consequently,
the total relative correction caused by the odd-step `+1` terms before
first entry below a large floor tends to zero uniformly in the entry time.

These are **written theorems** supported by kernel-checked finite transport
lemmas. They do not establish that first entry occurs. Collatz and the
weighted-survivor contraction problem remain unresolved.

Write
\[
 U(n)=\begin{cases}n/2&n\text{ even},\\(3n+1)/2&n\text{ odd},\end{cases}
 \qquad \alpha=\log_3 2,\qquad \sigma=H_2(\alpha)<19/20.
\]
The entropy exponent and its rational upper bound are those of
[ORBIT-PACKING-BOOTSTRAP.md](ORBIT-PACKING-BOOTSTRAP.md).

## 1. Packing before a first repetition

Let \(x_i=U^i(n)\), and suppose \(x_0,\ldots,x_N\) are distinct.
For every integer interval with \(a\ge0,L\ge1\),
\[
 \boxed{\#(\{x_0,\ldots,x_N\}\cap[a,a+L))\le256L^\sigma.}     \tag{1}
\]
The constant is independent of the start, the prefix length, and the
interval location. In particular, this does not assume that the infinite
trajectory is injective or that the finite set is forward invariant.

Here is the modification needed in the earlier strong induction. Fix
\(L>1\) and \(\ell=\lceil\log_2L\rceil\). Discard the final
\(\min(\ell,N+1)\) positions of the prefix. Every remaining position
has its \(\ell\)-step image inside this same finite prefix, and these
images are distinct. The discarded positions cost at most \(\ell\)
in total, across both aligned blocks meeting the source interval.

As in the earlier proof, split the parity weights at
\[
 J=\max(0,\lfloor\alpha\ell\rfloor-3),\qquad
 z=\alpha/(1-\alpha).
\]
A weight-\(j\) group in an aligned block of length \(2^\ell\)
maps into an interval of length \(3^j\). For \(j<J\), this length
is strictly smaller than \(L\). The induction hypothesis applies to
the original finite prefix at that shorter image interval. It does not
assume closure of the prefix or apply the theorem at the original length.

The estimates in Sections 2–3 of the earlier proof therefore give,
with \(C=256\),
\[
 \#\{\text{retained low weights}\}<\tfrac12 CL^\sigma,
 \qquad
 \#\{\text{retained high weights}\}<64L^\sigma.                \tag{2}
\]
For the high weights, distinct source states in one aligned block have
distinct parity words; no assertion about their later trajectories is
needed. For the low weights, the images belong to the original prefix,
and injectivity follows from distinctness of its positions.

The elementary inequality \(\ell^2\le2^{\ell+1}\), valid for every
integer \(\ell\ge1\), gives
\[
 \ell<2\sqrt L\le2L^\sigma.
\]
One can check the squared inequality at \(\ell=1,2,3\), then use
\((1+1/\ell)^2<2\) for \(\ell\ge3\). Adding the three contributions
gives less than \(194L^\sigma\), closing the induction with constant
256. The case \(L=1\) is immediate.

This also bounds the **distinct value set of any individual orbit**.
If a first repetition occurs, the prefix preceding it contains every
distinct value of the orbit. If no repetition occurs, apply (1) to a
prefix containing any chosen finite collection of values. This extension
does not apply to a branching ancestor basin.

The kernel lemmas `terminal_positions_bound`, `prefix_fixed_injective`,
and `finite_prefix_local_packing` in
[FinitePathPacking.lean](../lean/FinitePathPacking.lean) check the finite
step of this extension. Entropy, real powers, and the induction assembling
(1) remain written analysis.

## 2. The correction sum is bounded independently of elapsed time

Let \(V\) be a subset of the distinct values in a finite simple prefix,
all at least the positive integer \(Y\). Dyadic intervals in (1) give
\[
 \sum_{v\in V}\frac1v
 \le \frac{256}{1-2^{\sigma-1}}Y^{\sigma-1}
 <8192Y^{-1/20}.                                             \tag{3}
\]
Indeed, the shell \([2^rY,2^{r+1}Y)\) contributes at most
\(256(2^rY)^{\sigma-1}\). The shell bounds sum geometrically.
The rational constant follows from \(\sigma<19/20\) and
\[
 32^{20}<2\,31^{20},\qquad
 2^{-1/20}<31/32,\qquad
 (1-2^{\sigma-1})^{-1}<32.
\]
The first comparison is kernel checked in `reciprocal_constant`;
the entropy comparison is supported by the existing
[PackingExponent.lean](../lean/PackingExponent.lean). Their interpretation
using real powers and the geometric summation are written.

Now suppose \(h=\tau_Y(n)\) is a finite first entry, with \(n>Y\):
\[
 x_0,\ldots,x_{h-1}>Y,\qquad y=x_h\le Y.
\]
All \(h+1\) values are distinct. Otherwise equality at positions
\(i<j\le h\), followed for another \(h-j\) steps, would give an
entry at time \(h-(j-i)<h\). The last step is even, since an odd
shortcut step cannot decrease a positive integer. Hence
\[
 Y/2<y\le Y.
\]
Both statements are kernel checked by `first_entry_simple` and
`first_entry_landing`.

Let \(j\) be the number of odd steps before entry. Inverting each step
and multiplying gives the exact identity
\[
 n=\frac{2^hy}{3^j}R,\qquad
 R=\prod_{\substack{0\le i<h\\x_i\text{ odd}}}
       \left(1-\frac1{2x_{i+1}}\right).                       \tag{4}
\]
Every successor in this product is strictly above \(Y\), because the
last step is even, and these successors are distinct. Define
\[
 \Lambda=\sum_{\substack{0\le i<h\\x_i\text{ odd}}}
                  \frac1{2x_{i+1}},\qquad
 \varepsilon(Y)=4096Y^{-1/20}.
\]
Applying (3), and the finite product inequality
\(\prod(1-u_i)\ge1-\sum u_i\) for \(0\le u_i\le1\), proves
\[
 \boxed{\Lambda<\varepsilon(Y),\qquad
  1-\varepsilon(Y)<R\le1.}                                 \tag{5}
\]
Unlike the elementary bound \(\Lambda\le j/[2(Y+1)]\), this estimate
does not grow with \(h\) or \(j\). Either bound can be used when it is
smaller. The explicit constant is loose: (5) first guarantees the useful
margin \(R>2/3\) at \(Y\ge12288^{20}\). No useful small-floor margin
is claimed from that constant.

The reciprocal estimate concerns distinct states. Repeated traversal of
a cycle would repeatedly add its positive correction; (3) cannot be
applied to such a sum with multiplicities. First entry supplies exactly
the needed distinctness.

## 3. A fixed-time first-entry fibre

The reverse-product fibre argument in Section 4 of
[Shaik's first-passage draft](https://raw.githubusercontent.com/shaikidris/FirstPassageLinearTransport/main/paper/collatz_first_passage_natural_density.md)
motivates this step. We use the elementary argument below, not the draft's
claimed global density theorem or its formalization.

Fix positive integers \(h,y,X\), and retain sources \(n\in[X,2X)\) first entering at
\((h,y)\), with \(R\ge1-\delta\) for \(0\le\delta\le1/3\).
They have the same odd count. Otherwise their values of \(2^hy/3^j\)
differ by at least three, so the sources differ by at least two, impossible
inside this half-open interval. `shell_weight_unique` kernel checks this
integer implication.

Writing the common value as \(B=2^hy/3^j\), every retained source lies
in \([(1-\delta)B,B]\). Nonemptiness implies \(B<3X\). Therefore
\[
 \boxed{\#\{\text{retained sources}\}\le1+\delta B
                                      \le1+3\delta X.}       \tag{6}
\]
The count uses only the length of an interval containing distinct integers.

Combining the new time-independent estimate (5) with (6) gives, whenever
\(Y\ge12288^{20}\), for every \(h\ge1\) and \(Y/2<y\le Y\),
\[
 \#\{n\in[X,2X):\tau_Y(n)=h,\ U^h(n)=y\}
 \le1+12288X Y^{-1/20}.                                     \tag{7}
\]
There is no bound on \(h\) in (7). This is a bound for each fixed time,
not for the union over all times. The real interval count and (7) remain
written; the Lean module proves the odd-count uniqueness implication.

## 4. What remains missing

For the weighted survivor sequence, the exact loss layer at horizon
\(k\) is
\[
 S_k\setminus S_{k+1}=P^kD_0,\qquad
 D_0=\{n:\ H<n\le2H,\ n\text{ even}\},
\]
where \(PA=\{n>H:U(n)\in A\}\). Thus each layer consists of sources
whose first entry occurs at the specified common time \(k+1\).
The first-entry analysis above applies to those paths.

However, the sum of the layer masses may still be strictly less than
the initial mass. Equations (5)–(7) bound paths that **do** enter; they
do not force entry for a remaining start. Nor can (7) be summed over
an unrestricted set of times without another estimate. Its dependence
on the floor is also much weaker than a uniform distribution among the
landing values. No recurrent weighted contraction, universal hitting-time
bound, or contradiction for an eternal survivor follows here.

The extension removes a time-dependent error from one part of exact
first-entry transport. Controlling the possible entry times and the
unabsorbed mass remains necessary. Both nontrivial cycles and divergent
orbits remain unresolved.

## 5. Verification and scope

[The verification manifest](../results/finite-path-packing/verification.json)
separates the kernel lemmas, independent exact Python replay, and written
analytic claims. The verifier builds its Lean dependencies sequentially
in a fresh temporary directory. It checks complete finite source shells,
first-entry products and correction sums with rational arithmetic,
fixed-time fibres, and finite-path image transfers. These finite checks
do not establish the analytic induction or first entry for arbitrary starts.

Reproduce from the repository root:

```sh
python3 verify_finite_path_packing.py
```
