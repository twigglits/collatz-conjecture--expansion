# What an escaping orbit would require of predecessor densities

**Status: written deductions from the earlier density and packing arguments,
with a separate exact finite replay. Collatz remains unresolved.** The density
limits use the written first-passage estimates, and positivity uses the
[independently replayed external predecessor theorem](PREDECESSOR-DENSITY-REVIEW.md).
No new analytic input or kernel theorem is asserted here.

The [inverse density flow](PREDECESSOR-DENSITY-FLOW.md) and
[uniform predecessor approximation](UNIFORM-PREDECESSOR-APPROXIMATION.md)
do not yet exclude a divergent component. This note identifies a sufficient
relative branch estimate, and explains why even a stronger absolute
predecessor lower bound of order \(1/a\) would not supply it.

## 1. Summable mass in the unused branches

Suppose \(b_0,b_1,\ldots\) is a divergent Syracuse orbit. Discard its
first state if necessary so that every \(b_j\) is positive, odd, and not
divisible by three. The ordinary orbit has no repeated state and leaves
every finite set. Define
\[
 v_j=3b_j+1,\qquad u_j=2v_j=6b_j+2.
\]
The two ordinary parents of \(v_j\) are \(b_j\) and \(u_j\). Since
\(v_j\) is nonperiodic, their predecessor basins are disjoint. The
one-point contribution of \(v_j\) has density zero, so
\[
 r_{v_j}=r_{b_j}+r_{u_j}.
\]
Here \(r_a\) is the natural density of starts eventually reaching \(a\),
not the frequency of the value \(a\) in time. Since \(v_j\) reaches
\(b_{j+1}\),
\[
                    r_{b_{j+1}}\ge r_{b_j}+r_{u_j}.       \tag{1}
\]
Other branches may join during the intervening halving steps, so (1)
need not be an equality. Both displayed densities on its right are
strictly positive by the external theorem. The local basin partition
used here is among the kernel results in
[BoundedHitFibres.lean](../lean/BoundedHitFibres.lean).

The earlier component argument gives \(r_{b_j}\uparrow\lambda\), where
\(0<\lambda\le1\) is this component's density. Telescoping (1) gives
\[
 \boxed{\sum_{j\ge0}r_{u_j}\le\lambda-r_{b_0}<\infty.}    \tag{2}
\]
Set \(\rho_j=r_{u_j}/r_{b_j}>0\). Then, for every \(N\),
\[
 \prod_{j<N}(1+\rho_j)\le\frac{r_{b_N}}{r_{b_0}}
                            \le\frac\lambda{r_{b_0}},
 \qquad
 \sum_{j\ge0}\rho_j\le\frac{\lambda-r_{b_0}}{r_{b_0}}.  \tag{3}
\]
Thus mere strict increase of predecessor density cannot rule out escape.
The relative increases would have to be summable.

## 2. A sufficient logarithmic branch estimate

One estimate that **would** exclude divergent orbits is: for some
\(\kappa>0\) and \(K\), every nonperiodic odd \(b\ge K\) with
\(3\nmid b\) satisfies
\[
 \boxed{\frac{r_{2(3b+1)}}{r_b}\ge
                         \frac\kappa{1+\log b}.}         \tag{4}
\]
This estimate has not been proved. The logarithm is natural.

Indeed, \(\operatorname{Syr}(b)\le(3b+1)/2\le2b\), so
\(b_j\le2^j b_0\). On a divergent orbit, all sufficiently late states
exceed \(K\). Equation (4) would then give
\[
 \sum_j\rho_j\ge\kappa\sum_{j\text{ sufficiently large}}
            \frac1{1+\log b_0+j\log2}=\infty,
\]
contradicting (3). In particular a hypothetical divergent orbit must obey
\[
            \liminf_{j\to\infty}(1+\log b_j)\rho_j=0.   \tag{5}
\]
No uniform positive bound on the unscaled ratios is needed for this
criterion. Conversely, the existing positivity theorem supplies no
bound like (4). Proving (4) would still leave nontrivial cycles to be
excluded: the nonperiodic basin partition does not apply at cycle nodes.

## 3. Why an absolute lower bound of order \(1/a\) is insufficient here

A recent [preprint on Wirsching's predecessor-density program](https://arxiv.org/html/2608.27617)
describes a target-uniform lower bound \(r_a\ge c/a\), for admissible
targets, as the objective of that program. Its remaining condition is
explicitly unproved. This note does not adopt that lower bound, or the
preprint's other new results, as established inputs.

Even granting that bound would only give \(r_{u_j}\ge c/u_j\).
The [finite-path packing estimate](FINITE-PATH-PACKING.md) shows why
summing these lower bounds would not contradict (2). Let
\(\sigma=H_2(\log_3 2)<19/20\). For an integer \(R\ge1\), the distinct
odd values of any orbit in \([2^kR,2^{k+1}R)\) number at most
\(256(2^kR)^\sigma\). Thus for every \(s>\sigma\),
\[
 \boxed{\sum_{j:b_j\ge R}b_j^{-s}
       \le\frac{256}{1-2^{\sigma-s}}R^{\sigma-s}.}         \tag{6}
\]
This follows by applying the finite packing bound in each interval and
summing a geometric series. The interval is finite, so its orbit values
are all covered by some finite prefix; no infinite-time packing premise
is added. Also \(u_j\ge6b_j\), hence \(\sum_j u_j^{-s}<\infty\).
In particular the proposed \(c/u_j\) contributions are summable.

There is a simple scalar consistency check. On a sufficiently late tail,
\(c\sum_j1/u_j\) is as small as desired. Choose \(d_0>0\) with
\(d_0+c\sum_j1/u_j<1\), and define
\[
 d_j=d_0+c\sum_{i<j}\frac1{u_i},\qquad q_j=\frac c{u_j}.
\]
Then \(d_{j+1}=d_j+q_j\), all \(q_j>0\), and \(d_j\) increases to a
positive limit below one. These scalar values satisfy precisely the
bounded-growth and lower-bound conditions being compared. They are
**not** claimed to be actual Collatz densities or a counterexample.
They show that this proposed contradiction from summing lower bounds
does not follow. The same summability issue applies to polynomial
relative lower bounds \(\rho_j\ge\kappa u_j^{-s}\) when \(s>\sigma\).

The unresolved task is therefore a relative comparison such as (4), or
another estimate whose cumulative contribution must diverge. Improving
the absolute positivity theorem to \(c/a\) alone would not do that by
this argument.

## 4. Exact finite branch counts

[The replay record](../results/density-branch-leakage/verification.json)
uses a complete forward graph of the starts up to \(524288\), with their
known terminal cycle. It counts each source once per reachable target,
by aggregating weights through the acyclic part of the graph. A separate
direct trajectory replay checks the aggregation for all starts through
4096. Every noncyclic vertex is also checked against its exact ordinary
parent partition at each stated cutoff.

For the particular nonperiodic branch \(b=3077\), \(v=9232\),
\(u=18464\), the count at \(X=524288\) is
\[
 \#(P_b\cap[1,X])=206048,\qquad
 \#(P_u\cap[1,X])=39,\qquad
 \#(P_v\cap[1,X])=206088.
\]
The last count includes the source \(v\) itself. The unused/used ratio
is exactly \(39/206048\), below \(1/1000\) for this finite population.
The orbit of 3077 reaches the known cycle. Small branch ratios therefore
also occur on a convergent path.

These counts neither determine \(r_u/r_b\) nor refute every possible
constant in (4). The analytic convergence rate currently has no usable
explicit error constant at these cutoffs. The replay does not convert
the finite ratios into certified asymptotic ratios.

```sh
python3 verify_density_branch_leakage.py
```

The verifier records source and dependency hashes and the exact finite
scope. It does not recompile Lean or certify the written limiting
arguments. No density-one convergence, exclusion of all cycles, or
positive divergent orbit is established.
