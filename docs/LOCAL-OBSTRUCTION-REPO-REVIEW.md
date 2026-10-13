# Review of the local two-coordinate-obstruction repository

**Collatz remains unresolved.** The local clone contains useful results,
including a direct connection to our binary image densities. Its remaining
arithmetic estimates are open; the existence of Lean proofs of its conditional
criteria does not discharge those conditions.

Reviewed on 2026-10-13 at commit
`a7275d5a73814d3d9a400c6fe6577de9542b03a3`, dated 2026-10-08, in
`/Users/jean/Personal/collatz-two-coordinate-obstruction`. The checkout was
clean and was read without modification. The author is Lucas Valbuena.

This review reads the papers, theorem maps, selected endpoint statements,
and their relevant proofs. It independently authenticates the distributed
files against the published manifests. **It does not freshly compile or
kernel replay the external developments.** Their analytic results remain
external dependencies, distinct from this project's previous 389-module
predecessor-density replay and its local standalone kernel proofs.

## 1. What is useful to this project

| Result in the clone | Concrete use | Remaining limitation |
| --- | --- | --- |
| Positive stationary envelope, equal to the actual trace at every positive integer | A pointwise majorant for our full binary image law, uniform in time; see Section 2 | The majorant depends on the target integer and is unbounded over integers |
| Stationary density in every `L^p`, `1<=p<2`, and not in `L^2` | Uniform subcritical norms for that full image law; an alternative derivation of our existing `p<6/5` unweighted return range | Selected returns and actual integer sampling still require estimates |
| Exact first-hit coefficient bound, including periodic targets | Uniform control at each positive odd depth, without a cycle-return factor | It is bounded in terms of the unknown actual weighted basin density |
| Masked cylinder-energy decomposition and equivalence | A precise finite criterion for excluding escape, with the no-small-ancestor part already controlled | The small-ancestor part is equivalent to the unresolved escape question; additional cycles remain possible |
| Strict raw-occupation excess from a divergent orbit | A second precise upper-bound target whose proof would exclude escape | The matching upper bound is absent |
| Fourier decay after conditioning on total exponent | Potential input for unselected or total-exponent-selected affine words | It does not directly cover a path-dependent return event |

The quotient-injection argument in the sharp-density paper has already
helped: [BINARY-IMAGE-ENERGY.md](BINARY-IMAGE-ENERGY.md) credits it and gives
our independent finite-binary adaptation. The new connection below goes
beyond that earlier use of the paper.

A later [integer return Cesaro deduction](INTEGER-RETURN-CESARO.md) makes
another concrete use of the clone: its periodic weighted first-hit means
and elapsed-clock theorem imply `K*_(0,H)(n)/H -> 0` for each fixed
positive target. The argument treats periodic targets and explicitly
removes the odd-source clock restriction; it does not assume that the
clone's odd-unit marked theorem applies to our masks. Nine local kernel
inputs and exact finite checks support this written external deduction.
Finite total occupation and uniformity for moving targets remain open.

The later [harmonic trace proof](HARMONIC-RETURN-TRACE.md) independently
strengthens that vanishing conclusion to
`K*_(0,H)(n)<=350 C_star n G_n sqrt(H)`, with no external analytic input.
Its constant is uniform after the displayed target normalization. The
clone's marked full-image identification remains a separate external
result; unrestricted moving-target estimates and Collatz remain open.

## 2. A direct stationary majorant for our full binary image law

This section is a **written deduction from external results**, with exact
finite checks of the transfer identity. It is not a new locally replayed
kernel theorem.

Use `b_t` for the density called `rho_t` in our binary-image note:

\[
 b_t(z)=2^{-t}\sum_{0\le r<2^t}
  3^{a_t(r)}\mathbf1_{z\equiv U^t(r)\pmod{3^{a_t(r)}}}.
 \tag{1}
\]

The external stationary cylinder density `rho^S_k` has a different index:
`k` is its ternary conductor/Syracuse depth. It is not `b_k`.

Let `H(x)=x/2`, `J(x)=(3x+1)/2` on the ternary integers. Their equally
weighted transfer operator on densities is

\[
 (Lf)(z)=\tfrac12 f(2z)+\tfrac32\mathbf1_{z\equiv2\pmod3}
                         f((2z-1)/3).                       \tag{2}
\]

The second branch is evaluated only on its indicated domain. Haar
measure is the full additive probability measure, not renormalized on units.

Every binary parity word of length `t` occurs once in the full source period.
Its affine map has slope `3^a/2^t` and correction `N/2^t`. It pushes Haar
measure to density `3^a` on its image cylinder, whose residue is `U^t(r)`.
Averaging the words therefore proves

\[
                       b_0=1,\qquad b_{t+1}=Lb_t.             \tag{3}
\]

This identification concerns the full parity-word law. No independence
between the two endpoints of an adjacent pair is asserted.

The clone supplies an extended nonnegative envelope `E` and a finite
constant `c>0` such that

\[
 LE\le E\ \text{pointwise},\qquad
 E\ge c\ \text{on ternary units},\qquad E(n)=g(n)\ (n>0).
 \tag{4}
\]

Here `g(n)=delta G_n n D_n`, `delta=log(4/3)/2`, `D_n` is the actual
weighted first-hit density, and `G_n` is its periodic Green factor, equal
to one at nonperiodic targets. The envelope is a stationary density of
integral one. Together with the sharp-density theorem this gives
`E in L^p` for `1<=p<2`, interpreted up to its null set of infinite values.

The crucial statement is genuinely pointwise:
[`canonicalIntegerEnvelope_transfer_le`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/PadicBinaryEnvelopeTransfer.lean).
The floor is
[`canonicalIntegerEnvelope_uniform_unit_floor`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/PadicIntegerEnvelopeIntegral.lean),
the integer identity is in
[`CanonicalEnvelopePeriodicExtension.lean`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/CanonicalEnvelopePeriodicExtension.lean),
and the sharp integrability endpoint is in
[`CanonicalHaarNotL2.lean`](../../collatz-two-coordinate-obstruction/formal-sharp-haar/source/CanonicalHaarNotL2.lean).

Set `h=(3/2)1_(z=2 mod 3)`. Since `L1=1/2+h`, positivity and linearity
give the exact finite expansion

\[
 b_t=2^{-t}+\sum_{j=0}^{t-1}2^{-(t-1-j)}L^j h.
\]

By (4), `h<=(3/(2c))E` and `L^j E<=E`. Summing the geometric coefficients
proves the useful comparison

\[
 \boxed{b_t(z)\le2^{-t}+\frac3c(1-2^{-t})E(z).}              \tag{5}
\]

Consequently,

\[
 \sup_{t\ge0}\|b_t\|_p\le1+\frac3c\|E\|_p<\infty
       \quad(1\le p<2),                                    \tag{6}
\]

and at **every fixed positive integer**,

\[
               b_t(n)\le2^{-t}+\frac3c g(n).                 \tag{7}
\]

Thus the external arithmetic floor supplies a stronger full-image estimate
than our polynomial-in-time subcritical bound. It supplies no numerical
value for `c`, no uniform upper bound for `g(n)` as `n` varies, and no
summable-in-time bound for the selected return densities.
Indeed,
[`actual_trace_unbounded_in_unit_cylinder`](../../collatz-two-coordinate-obstruction/formal-stationary-envelope/source/CanonicalEnvelopeDenseInfinity.lean)
proves that `g` is unbounded even in each fixed unit residue class.
The fixed-integer Cesaro absolute-error theorem does not give a rate
uniform over growing integer intervals.

The endpoint `p=2` cannot be restored as a uniform full-image bound using
these inputs. Couple a chain started from Haar measure to a stationary
chain, using the same independent choices of `H,J`. After `t` steps their
difference is `3^a/2^t` times their initial difference, where
`a~Binomial(t,1/2)`. For each fixed `k`, `Pr(a<k)->0`; their depth-`k`
projections consequently agree with probability tending to one. Hence
`b_t` tends weakly to the stationary measure. A uniform `L^2` bound would
bound the `L^2` norm of every stationary cylinder density, and martingale
convergence/Fatou would give an `L^2` stationary density, contradicting the
external non-`L^2` theorem. This is also a written, externally dependent
deduction, not a statement about the optimal integrability of our return law.

For an all-return dyadic block `Delta_H=sum_(H<=t<2H) kappa_t`, we have
`kappa_t<=b_t`, so (6) gives `||Delta_H||_q=O_q(H)` for `1<q<2`.
Our existing clock tail gives `||Delta_H||_1=O(H^(-1/2)log H)`.
Interpolation has a decaying power exactly when

\[
 p<\frac{3q}{2q+1};\qquad q\uparrow2\ \Longrightarrow\ p<\frac65.
 \tag{8}
\]

This recovers the unweighted range in
[RETURN-AFFINE-BUDGET.md](RETURN-AFFINE-BUDGET.md); it does **not** improve
that range or prove the actual-gradient pairing. Our existing proof of
that range remains independent of these new external dependencies.

## 3. The strongest concrete escape-exclusion target

The finite mask in the clone is

\[
 \mathcal F_K=\{N:1\le N<3^K,\ N\text{ odd},\
             S^j(N)\ne N\ (1\le j\le K)\},\qquad
 \mathcal E_K=\sum_{N\in\mathcal F_K}(\rho^S_K(N)/N)^2.
 \tag{9}
\]

Here `S` is the accelerated odd Syracuse map. Membership uses finitely
many return checks; a cycle with odd period greater than `K` is still
included. The public endpoint
[`masked_energy_sublinear_iff_universal_eventual_periodicity`](../../collatz-two-coordinate-obstruction/formal-cylinder-energy/source/MaskedEnergyPeriodicityEquivalence.lean)
states the exact equivalence

\[
 \mathcal E_K/(K+1)\longrightarrow0
 \quad\Longleftrightarrow\quad
 \text{every positive orbit is eventually periodic}.         \tag{10}
\]

Its two directions are proved, while neither side is asserted outright.
This permits additional cycles. Its energy is also different from our
dyadic actual-weight energy; our `O(sqrt(s))` bound does not imply (10).

There is useful partial progress on the left side. Split targets according
to whether any positive seed at most `M` reaches them. The source proves

\[
 \mathcal E_K\le\mathcal E_K^{\rm small}(M)
       +L\varepsilon(M)\mathfrak B_K,\qquad
 \mathfrak B_K\le5(K+1),\qquad\varepsilon(M)\to0.             \tag{11}
\]

See
[`exists_uniform_maskedEnergy_decomposition`](../../collatz-two-coordinate-obstruction/formal-cylinder-energy/source/MaskedCylinderNoSmallAncestorEnergy.lean).
For any `M_K->infinity`, the normalized no-small-ancestor contribution
therefore vanishes. The entire remaining term lies on actual forward
orbits of small seeds. Assuming those orbits are finite to bound this
term would assume the desired conclusion.

A reusable ingredient is
[`exists_uniform_odd_exact_firstHit_coefficient_bound`](../../collatz-two-coordinate-obstruction/formal-cylinder-energy/source/GammaFreeFirstHitCoefficient.lean).
It bounds each positive odd-depth first-hit coefficient by `L N D_N`,
including periodic targets. Its proof replaces each predecessor fan by
a unit, nonperiodic predecessor using at most six shortcut divisions,
and then uses disjoint basins and the external reciprocal density floor.
The public endpoint discharges that floor; its helper theorem takes it
explicitly. This is useful source structure, not an unexplained assumed
uniform coefficient estimate.

The other precise target is the raw occupation sum
`A(R)=sum_(N<=R, N odd) D_N`. The endpoint
[`actual_raw_occupation_strict_baseline_excess_of_unit`](../../collatz-two-coordinate-obstruction/formal-raw-divergent-excess/source/RawOccupationDivergentExcess.lean)
proves that an injective positive odd unit orbit forces

\[
 \liminf_{R\to\infty}\frac{A(R)}{\log R}
 \ge\frac1{\log(4/3)}+
       \frac{D_u}{P_\infty(u)\log(3/2)}
 >\frac1{\log(4/3)}.                                       \tag{12}
\]

Thus a matching upper bound with coefficient `1/log(4/3)` would exclude
escape. The clone does not prove it. Its actual inverse-path height law,
[`actual_inverse_height_clock_ae`](../../collatz-two-coordinate-obstruction/formal-inverse-doob-clock/source/ActualInverseHeightClock.lean),
is almost sure at a fixed positive odd nonperiodic unit root. It supplies
no uniform integrability that would turn that clock into the needed
expected occupation upper bound.

## 4. What the stronger Fourier theorem does and does not select

The public statements in
[`TrapMicrocanonicalDeficit.lean`](../../collatz-two-coordinate-obstruction/formal-growing-deficit/source/TrapMicrocanonicalDeficit.lean)
are uniform over affine seeds and unit-modulus functions of the **total
exponent**. At conductor `n`, length `k<=n`, primitive coefficients are
bounded by `C_A((n-k+2)/n)^A`. The conditioned theorem divides by the
positive mass of an exact total-exponent slice. The further mass-floor
theorem yields every inverse polynomial rate when `n-k<=k^beta`, `beta<1`,
and the slice has polynomially bounded reciprocal probability.

Our first-return and nonfusion events depend on the entire paired parity
history. They are not specified by the total exponent alone. Even a
large probability for such an event would not justify applying the slice
theorem: a uniform law modulo `3^n` has zero nontrivial Fourier
coefficients, but conditioning on its first third of residues has mass
`1/3` and a primitive coefficient of modulus at least `1/2`. Rotate that
coefficient by `exp(-i*pi/3)`; every term then has real part at least
`1/2`. Thus arbitrary selection can destroy Fourier decay even for a
perfectly uniform initial law.

A usable application would need an additional proof controlling the
correlation between our return event and the affine image. Seed uniformity
and the total-exponent mass floor alone do not provide that proof.

## 5. Verification and continuation

Run from this project:

```sh
python3 verify_two_coordinate_review.py
```

The [record](../results/two-coordinate-review/verification.json) records:

- 7,493 distinct distributed files matching their published hashes across
  eight package inventories and four paper/source/theorem-map sets;
- 2,457 selected source-module entries rechecked against their execution
  manifests; the wider inventories include 2,522 `.lean` files, including
  audits and provenance copies;
- 2,047 full binary residue rows and 2,047 independently generated affine
  words through depth ten;
- 88,572 exact transfer comparisons covering every ternary residue at each
  positive depth through ten, and 2,816 independent actual positive-integer
  inverse-tree comparisons;
- four exact rational exponent checks for (8).

These are source-authentication and independent finite checks. No external
Lean compilation, local kernel proof of (5), stationary numerical
approximation, or asymptotic verification is claimed. The retained upstream
records report successful kernel checks with standard axioms, but their
external library objects were reused; this local review does not replay or
authenticate those compiled dependencies. The density bundles target
Lean 4.30.0-rc2, while the Fourier bundle targets 4.35.0-rc3; our standalone
project currently uses 4.33.1.

The practical next steps are to use (5) as an explicitly external comparison
when designing a weighted gradient estimate, and to seek a proved connection
from our actual-weight dissipation to (11) or the upper bound complementary
to (12). Neither connection is established here. This review alone does
not improve the then-established local `6/5` result. A subsequent independent
[active-gap potential argument](ACTIVE-GAP-POTENTIAL.md) gives `p<5/4`
without adopting the external stationary-law theorems; the actual-gradient
and infinite-cutoff sampling gaps remain.
