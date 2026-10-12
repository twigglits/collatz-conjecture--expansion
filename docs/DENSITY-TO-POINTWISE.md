# What uniform first-passage stabilisation says about exceptions

**Status: written deduction from Proposition 4.1 of
[NATURAL-DENSITY-ALMOST-BOUNDED.md](NATURAL-DENSITY-ALMOST-BOUNDED.md).
Not kernel checked. Collatz remains unresolved; no novelty is asserted.**

The proposition is a written adaptation of Tao's argument, with the
external dependencies identified in that note. The results below do not
independently validate it. They strengthen its consequences and identify
the estimate still missing for an individual counterexample.

## 1. Total variation of the entire minimum distribution

Write \(M(n)=\operatorname{Col}_{\min}(n)\). This minimum exists for
every positive integer, including a hypothetical divergent orbit, by
well-ordering. Let \(\mu_y\) be the law of \(M(\mathbf U_y)\), where
\(\mathbf U_y\) is uniform on odd integers in \([y,2y)\). There is a
probability distribution \(p=(p_m)_{m\ge1}\) such that
\[
 d_{\rm TV}(\mu_y,p)\ll(\log y)^{-c}.
 \tag{1}
\]
In particular the bound is uniform over **all** sets of possible minima,
not only the sets \(\{1,\ldots,B\}\).

*Proof.* If \(T_x(n)<\infty\) and \(n>x\), then
\[
 M(n)=M(\operatorname{Pass}_x(n)).
 \tag{2}
\]
All states before passage exceed \(x\), whereas the passage state is
at most \(x\). Applying the same function \(M\) to both passage laws
cannot increase their total variation. The infinite-passage events cost
\(O(x^{-c})\). Proposition 4.1 therefore implies
\[
 \sup_{Y\le Z\le Y^\alpha}d_{\rm TV}(\mu_Y,\mu_Z)
 \ll(\log Y)^{-c}
 \tag{3}
\]
by taking \(x=Y^{1/\alpha}\).

For arbitrary \(Z\ge Y\), telescope along
\(Y,Y^\alpha,\ldots,Y^{\alpha^J},Z\), with
\(Y^{\alpha^J}\le Z\le Y^{\alpha^{J+1}}\). The sum of the errors is
\[
 \ll\sum_{j\ge0}(\alpha^j\log Y)^{-c}
 \ll(\log Y)^{-c}.
 \tag{4}
\]
Thus the laws are Cauchy in total variation. Here one can prove that
the limit has mass one without a compactness assumption: for any
\(\varepsilon>0\), choose \(Y\) so that (4) is less than
\(\varepsilon\). The finite support of \(\mu_Y\) then has mass at
least \(1-\varepsilon\) under every \(\mu_Z\), \(Z\ge Y\).
Coordinatewise limits exist by (4), their sum is at most one, and this
finite-support bound forces their sum to be one. Finite truncation now
gives total-variation convergence, and (4) gives (1). \(\square\)

Let \(\eta_X\) be the law of \(M(\mathbf{Unif}\{1,\ldots,\lfloor X\rfloor\})\).
Then also
\[
 d_{\rm TV}(\eta_X,p)\ll(\log X)^{-c}.
 \tag{5}
\]
For odd starts up to \(X\), partition into dyadic intervals and
discard the part below \(\sqrt X\), which has relative size
\(O(X^{-1/2})\). Every remaining interval uses (1) at
\(y\gg\sqrt X\), so the same error bounds their mixture. For general
starts, condition on \(a=\nu_2(n)\). Their odd parts are uniform among
odd integers up to \(X/2^a\), and \(M(n)=M(n/2^a)\). The groups with
\(2^a>\sqrt X\) have combined relative size \(O(X^{-1/2})\);
the others again have error \(O((\log X)^{-c})\). Endpoint rounding
does not change these bounds.

This gives a direct proof of Theorem ND from Proposition 4.1, without
the separate transfer of Tao's Section 3 iteration. For large \(B\),
the law \(\mu_{B/2}\) is supported below \(B\), so (1) gives
\(\sum_{m>B}p_m\ll(\log B)^{-c}\). If \(X\ge B\), (5) then gives
\[
 \frac1{\lfloor X\rfloor}\#\{n\le X:M(n)>B\}
 \ll(\log B)^{-c}+(\log X)^{-c}
 \ll(\log B)^{-c}.
\]
If \(X<B\) the set is empty. Bounded \(B\) are absorbed into the
constant. The distribution agrees with Section 6 of the earlier note:
\(p_m=d_m-d_{m-1}\).

## 2. Coalescence components and countable additivity

Let \(\pi(n)\) be the smallest positive integer whose Collatz orbit
eventually meets the orbit of \(n\), allowing different meeting times.
It labels the entire coalescence component, and
\(\pi(M(n))=\pi(n)\). Pushing (5) through \(\pi\) gives a probability
distribution on component labels,
\[
 \lambda_b=\sum_{m:\pi(m)=b}p_m,
 \qquad
 \sup_A\left|\frac{\#\{n\le X:\pi(n)\in A\}}{\lfloor X\rfloor}
                  -\sum_{b\in A}\lambda_b\right|
 \ll(\log X)^{-c}.
 \tag{6}
\]
The supremum includes arbitrary unions of components. Each component
therefore has a natural density, the component densities sum to one,
and the union of all zero-density components has density zero. That
last assertion would not follow merely by taking an arbitrary countable
union of zero-density subsets; (6) supplies the needed countable
probability distribution. At least one component has positive density.

Similarly, the set of divergent starts and the basin of each specified
cycle have natural densities: membership is a function of \(M(n)\).
Their numerical densities are not determined by this argument.

## 3. The unresolved density-one premise

Nothing in the written first-passage argument alone proves \(p_1=1\),
or even \(p_1>0\). The external positive lower predecessor-density
theorem has now passed an
[independent 389-module source replay](PREDECESSOR-DENSITY-REVIEW.md).
Together with the written limit (5), it gives \(p_1>0\), and more
substantially
\[
 \boxed{\text{every positive integer reaches one}\quad\Longleftrightarrow\quad p_1=1.}
 \tag{7}
\]
Indeed, any positive counterexample would force its nonconvergent set to
have positive lower natural density. If \(p_1=1\), (5) makes that set
have density zero, a contradiction. No improved error rate is required.
The external theorem already proves that upper natural density one of
the convergent set suffices, without using our written minimum law.
Neither it nor this note establishes that remaining premise.

The earlier [inverse-basin comparison](../APERIODIC-ATTEMPT.md#16-inverse-basin-counts-do-not-supply-an-injective-orbit-packing-contradiction)
used only the published \(c_bX^{0.84}\) bound of
[Krasikov–Lagarias](https://arxiv.org/pdf/math/0205002), whose computational
dependency was not replayed here. With that older input alone,
\(X(\log X)^{-c}\) could still exceed the predecessor lower bound even
if \(p_1=1\); an \(o(X^{0.84})\) exceptional count would have sufficed.
The verified linear lower bound removes that extra rate requirement.
It does not determine the mass \(p_1\).

## 4. Densities of odd-target predecessor sets

There is a further written consequence of Proposition 4.1. For every
fixed **odd** positive integer \(a\), the predecessor set
\[
 P_a=\{n\ge1:\text{the ordinary Collatz orbit of }n\text{ reaches }a\}
\]
has a natural density \(r_a\). Its existence does not require the
external positive predecessor-density theorem. The verified external
theorem additionally makes \(r_a>0\) for every odd \(a\) not divisible
by three.

To see existence, more generally fix a nonempty finite set \(A\) of odd targets
and record which of its members an orbit visits. For a floor
\(x\ge\max A\) and an odd start above \(x\), this finite visitation
profile is exactly the profile of its Syracuse first-passage location.
If passage never occurs, the profile is empty. No target in \(A\) can
have been visited before passage, since those prior odd states exceed
\(x\). Pushing the passage laws through this profile gives the same
Cauchy estimate as (3) for \(Y\ge(\max A)^\alpha\). The telescoping
argument therefore gives a limiting law on the finitely many profiles.
Dyadic decomposition and removal of initial factors of two, as in
Section 1, give the same limit for uniform positive starts up to \(X\).
Taking \(A=\{a\}\) proves existence of \(r_a\).

The odd-target restriction matters to this proof. An even target may be
visited during the final halving segment before Syracuse first passage,
and need not be visited again from the odd landing value. The argument
above alone does not assert an even-target density theorem. Section 5
supplies the additional overshoot estimate needed for even targets.

### Summed density bound from finite orbit packing

Let \(\sigma=H_2(\log_3 2)<19/20\), as in the
[finite-path packing argument](FINITE-PATH-PACKING.md). For every integer
interval \(I=[A,A+L)\), with \(A\ge0,L\ge1\),
\[
              \sum_{\substack{a\in I\\a\ge1\text{ odd}}}r_a
                         \le256L^\sigma.                 \tag{8}
\]
Indeed, the odd values on an ordinary orbit are exactly those on its
shortcut orbit. For each start \(n\), finite-path packing bounds the
number of distinct visited odd targets in \(I\) by \(256L^\sigma\),
whether or not the orbit converges. Average this inequality over starts
up to \(X\), interchange the two **finite** sums, and then let
\(X\to\infty\). Only finitely many targets are involved, so no
interchange of an infinite sum and a density limit occurs.

In particular, for every \(\eta>0\),
\[
 \#\{a\in I:a\ge1\text{ odd},\ r_a\ge\eta\}
                    \le256\eta^{-1}L^\sigma.             \tag{9}
\]
Thus a uniform positive lower bound for the predecessor densities of
all eligible odd targets is impossible under these written arguments:
there are \(L/3+O(1)\) odd targets not divisible by three up to \(L\),
while \(\sigma<1\). Root dependence in a positive-density theorem
cannot simply be discarded.

### Density increases along a forward orbit to its component mass

Fix an odd \(a_0\), put \(a_j=\operatorname{Syr}^j(a_0)\), and let
\(\lambda\) be the natural density of its coalescence component.
Then
\[
                         r_{a_j}\uparrow\lambda.         \tag{10}
\]
The predecessor sets increase with \(j\) and lie in that component,
so their densities are nondecreasing and at most \(\lambda\).
For a fixed \(B\), every possible minimum \(m\le B\) in the component
eventually reaches the orbit \((a_j)\). There are finitely many such
\(m\), so for all sufficiently large \(j\), every start in the
component with minimum at most \(B\) reaches \(a_j\). Therefore
\[
 r_{a_j}\ge\lambda-\sum_{m>B}p_m
\]
for those \(j\). The tail of the probability law \(p\) tends to zero,
which proves (10). This uses the established minimum-law tightness;
it does not infer countable additivity of natural density for an
arbitrary union of predecessor sets.

By the verified positive predecessor-density theorem, a hypothetical
divergent component has \(\lambda>0\), and its unbounded forward orbit
must satisfy (10). An upper bound forcing \(r_{a_j}\to0\)
along every unbounded forward orbit would consequently exclude
divergence. No such upper bound is proved here. Equations (8)–(9)
control the sum over target intervals and do not imply decay along a
single sparse forward orbit. Nontrivial cycles also remain to be
excluded. All results in this section are written deductions, not
additional Lean certificates.

## 5. Extension to every fixed positive target

The valuation estimate used to prove Proposition 4.1 also controls the
landing size. With its notation, uniformly for
\(y\in[x^\alpha,x^{\alpha^2}]\),
\[
 \mathbf P\bigl(T_x(\mathbf U_y)\le n_0,\quad
          x^{7/10}<\operatorname{Pass}_x(\mathbf U_y)\le x\bigr)
       =1-O(x^{-c}),\qquad n_0=\lfloor\log_2x/10\rfloor.
                                                               \tag{11}
\]
This coarse overshoot estimate uses only the early valuation law, not
the fine-scale mixing argument.

Indeed, uniform odd residues modulo \(2^{3n_0}\) have error
\(O(2^{3n_0}/y)\ll2^{-3n_0}\). Apply
[Tao's Proposition 1.9 and Chernoff bound](https://arxiv.org/html/1909.03562v7)
to the total valuation \(S\) in the first \(n_0\) Syracuse steps.
Except on an event of probability \(O(x^{-c})\),
\[
                   19n_0/10\le S\le3n_0.                 \tag{12}
\]
The affine iteration formula, \(F_{n_0}<3^{n_0}\), and
\(N<2x^{\alpha^2}\) give
\[
 \operatorname{Syr}^{n_0}(N)
 \le 2x^{\alpha^2}(3/2^{19/10})^{n_0}+3^{n_0}<x
\]
for sufficiently large \(x\). To check the exponent without numerical
logarithms, \(3^5<2^8\) gives \(\log_2 3<8/5\); the first term is
\(O(x^{\alpha^2-3/100})\), where
\(\alpha^2-3/100=972001/10^6<1\), and the second is at most
\(x^{4/25}\). Thus \(1\le T_x\le n_0\).
At the last step its previous odd value \(u\) exceeds \(x\), while
the last valuation is at most \(S\le3n_0\). Consequently
\[
 \operatorname{Pass}_x(N)=(3u+1)2^{-a_{T_x}}
                     >3x\,2^{-3n_0}>x^{7/10}.
\]
This proves (11).

Now let \(A\) be any nonempty finite set of positive targets and put
\(B=\max A\). If \(x^{7/10}>B\), then on the event in (11) every
ordinary state before the odd landing exceeds \(B\): before each
Syracuse step the odd value exceeds \(x\), and the intervening even
states are larger than that step's odd endpoint. The visitation profile
of \(A\) is therefore unchanged by passage. The profile laws differ
from the corresponding pushforwards of the passage laws by at most
\(O(x^{-c})\). Adding this error to (3), then telescoping over scales,
gives a limiting visitation-profile law for **every** finite \(A\).

For uniform positive starts, removal of initial powers of two can change
the profile only when the initial halving segment itself visits a target.
Such starts lie in \(\bigcup_{a\in A}\{2^j a:j\ge0\}\), which contains
\(O_A(\log X)\) integers up to \(X\). This error has density zero;
the remaining dyadic and valuation decomposition is the one in Section 1.
In particular, **every fixed positive target has a predecessor density
\(r_a\)** under these written analytic arguments.

The summed bound extends to all ordinary targets with constant 512:
\[
                   \sum_{a\in I\cap\mathbb N_{>0}}r_a
                              \le512L^\sigma.             \tag{13}
\]
If \(V\) is the shortcut orbit's distinct value set, every ordinary
orbit value belongs to \(V\cup2V\). The integer preimage of a length-\(L\)
interval under doubling has length at most \(L\), so finite-path
packing bounds these two contributions by \(256L^\sigma\) each.
Average over starts and pass through the finite target sum as before.
The proof of (10) likewise gives
\(r_{C^j(n)}\uparrow\lambda_{\pi(n)}\) for the ordinary forward orbit.

If \(3\mid a\), every ordinary predecessor of \(a\) is of the form
\(2^j a\): the only one-step predecessor is \(2a\), and the same
observation iterates. Hence \(r_a=0\) directly. If \(3\nmid a\), the
verified external PLD theorem gives \(r_a>0\). This classifies which
fixed-target densities vanish; it does not identify the density of
convergence to one or exclude an unbounded orbit with positive limiting
predecessor density.

The [written-review record](../results/density-to-pointwise/written-review.json)
identifies the source versions and the separate written, kernel-replayed,
and previously computed evidence used here. Section 5 is also written
analysis; no new kernel certificate is claimed for (11)–(13).
