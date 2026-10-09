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

## 3. The unresolved pointwise estimate

Nothing above proves \(p_1=1\), or even \(p_1>0\). If \(p_1=1\)
were proved, (5) would give only
\[
 \#\{n\le X:M(n)>1\}\ll X(\log X)^{-c}.
 \tag{7}
\]
A nonempty exceptional component remains compatible with (7).
The existing [inverse-basin analysis](../APERIODIC-ATTEMPT.md#16-inverse-basin-counts-do-not-supply-an-injective-orbit-packing-contradiction)
cites the external lower bound \(c_bX^{0.84}\) for ancestors of an
eligible fixed root, with a positive root-dependent constant; see
[Krasikov–Lagarias, abstract and introduction](https://arxiv.org/pdf/math/0205002).
This bound retains its published computational dependency, which is not
replayed here. Every
exceptional component has a root coprime to three: an ordinary step
from an odd multiple of three lands at a number congruent to one
modulo three. Its ancestors remain exceptional.

Even after assuming \(p_1=1\), the current bounds do not conflict:
\[
 c_bX^{0.84}\le\#\{n\le X:M(n)>1\}
 \ll X(\log X)^{-c}
\]
can hold for arbitrarily large \(X\). A sufficient replacement would be
\(o(X^{0.84})\) for the **entire exceptional set**, not just for its
orbit minima or a single injective orbit. Equivalently, \(p_1=1\)
together with an \(o(X^{-0.16})\) total-variation rate in (5) would
exclude every exceptional component by that external lower bound.
Neither premise is established here. This specifies a quantitative
gap; it is not an assertion that this is the only possible proof route.
