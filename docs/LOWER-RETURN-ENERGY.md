# Finite coefficient and component energy for lower returned endpoints

**Collatz remains unresolved.** At a count return, the two endpoint
slopes agree. Labeling the smaller endpoint first preserves the squared
difference of the future weights. This choice avoids one critical first
moment that is infinite when the original endpoint label is retained.

This note proves a finite first-moment budget for the smaller formal
endpoint at **grouped returns**, and consequently bounds all image
overlaps within each fixed clock and common odd count:

\[
 \boxed{\sum_{t,a}\|\kappa^{\rm low}_{t,a}\|_2^2
                  \le8200+72000C_*<\infty,\qquad
                         C_*=540\,2^{5180}.}                 \tag{1}
\]

These components include their internal cross terms, not just the
individual-column diagonal. Their definition selects the nonfused ends
of odd-separation excursions. It omits the intervening one-step returns
at even separation. Equation (1) does **not** control cross terms between
different components, the original all-return density, or actual future
gradients. Omitting the one-step returns is not asserted to preserve
the entire earlier energy estimate.

Eleven kernel arithmetic roots support the argument. The fractional
perpetuity estimate, probability, logarithms, and infinite Haar sums
remain written proofs. No external analytic theorem is used.

## 1. The smaller formal endpoint

At an equal-count prefix from the original adjacent pair, write

\[
 X=\Lambda n+B_0,\qquad Y=\Lambda(n+1)+B_1.
\]

Its positive integer separation \(D=|X-Y|\) does not depend on the
unread source bits. Define

\[
 P=\min\{\Lambda+B_0,\,2\Lambda+B_1\}.
\]

These are the images of formal real starting values one and two under
the selected parity words. They need not be actual iterates of one and
two. Their difference has absolute value \(D\), so the two formal
values are exactly \(P,P+D\). The endpoint minimizing them is also the
smaller actual endpoint, because both actual values add the same
quantity \(\Lambda(n-1)\).

For a fresh continuation from these formal values, at its next equal
count let \(\lambda\) be the common new slope and \(b_L,b_H\) its
corrections for the initially lower and higher endpoint. Then

\[
                 P'=\lambda P+\min\{b_L,\lambda D+b_H\}.
                                                               \tag{2}
\]

The integer version of the formal identity and the cost of selecting
either endpoint are kernel checked.

## 2. A clipped slow correction costs only a logarithm

Let \(D\) be odd and label the initially odd endpoint \(F\), and the
initially even endpoint \(S\). The
[slope-tilt result](RETURN-SLOPE-TILT.md) gives, conditional on either
initial parity,

\[
             \mathbb E\lambda=\tfrac12,\qquad
             \mathbb E b_F\le\tfrac54.
                                                               \tag{3}
\]

The untruncated mean of \(b_S\) is infinite. The relevant clipped
quantity has a different bound:

\[
 \boxed{\mathbb E\min\{b_S,\lambda D\}
                         \le12\log_2(D+1).}                  \tag{4}
\]

Here and below a fresh return is almost surely finite under the
original binary law.

To prove (4), condition on the first parity and tilt the continuation
by the slope of \(S\). Its initial multiplier is \(1/2\); subsequent
endpoint parities are independent with odd probability \(3/4\).
Under this tilt the active gap moves inward with probability \(3/4\),
and the return has probability one. Thus summation over finite return
cylinders gives

\[
 \mathbb E[\lambda f(b_S/\lambda)]
       =\tfrac12\widehat{\mathbb E}_S[f(2R_{\tau-1})].
                                                               \tag{5}
\]

For a continuation parity sequence \(\epsilon_j\), set
\(m_j=3^{\epsilon_j}/2\) and

\[
 R_h=\frac13\sum_{j=1}^h
        \mathbf1_{\{\epsilon_j=1\}}\prod_{i<j}m_i^{-1}.
\]

This is the continuation correction divided by its slope. It increases
to \(R_\infty\), and \(b_S/\lambda=2R_{\tau-1}\); the factor two comes
from the initial even step. For \(1/2\le\eta<1\), subadditivity and
independence of each fresh parity imply

\[
 \widehat{\mathbb E}_S R_\infty^\eta
 \le \frac{3^{1-\eta}}{4(1-r_{1-\eta})},\qquad
 r_u=\tfrac12(2^{-u}+(3/2)^u).
                                                               \tag{6}
\]

Indeed the expected inverse-slope multiplier to power \(\eta\) is
\(\frac14 2^\eta+\frac34(2/3)^\eta=r_{1-\eta}\).
The geometric series is finite. This also proves that the perpetuity
is finite almost surely; its first moment is not used.

Convexity of \(r_u\), \(r_0=1\), and \(r_{1/2}<31/32\) give
\(1-r_u\ge u/16\) for \(0\le u\le1/2\). The strict endpoint follows
from the kernel integer comparisons
\(\sqrt{1/2}<91/128\) and \(\sqrt{3/2}<157/128\).

Since \(\min(x,D)\le D^{1-\eta}x^\eta\), equations (5)--(6) give

\[
 \mathbb E\min(b_S,\lambda D)
 \le \frac{3}{8}(2/3)^\eta
          \frac{D^{1-\eta}}{1-r_{1-\eta}}
 \le \frac{6D^{1-\eta}}{1-\eta}.                            \tag{7}
\]

For odd \(D\ge3\), put \(L=\log_2(D+1)\) and
\(\eta=1-1/L\). Then \(\eta\ge1/2\) and
\(D^{1-\eta}\le2\), proving (4). For \(D=1\), the simpler bound
\(\min(b_S,\lambda D)\le\lambda\) gives mean at most \(1/2\).
All unbounded identities use nonnegative cylinder sums, not an
unverified optional-stopping equality.

## 3. Grouped drift of the minimum

If the lower endpoint is initially odd, (2) costs at most
\(\lambda P+b_F\). If it is initially even, use

\[
 \min(b_S,\lambda D+b_F)
                   \le b_F+\min(b_S,\lambda D).
\]

The two cases have probability \(1/2\), so (3)--(4) prove

\[
 \boxed{\mathbb E[P'\mid P,D]
       \le\tfrac12P+\tfrac54+6\log_2(D+1)
                               \quad(D\text{ odd}).}        \tag{8}
\]

For the first return from adjacent formal values one and two there is
also the sharper bound \(\mathbb E P'\le2\). In the two initial parity
cases simply select \(F\): the respective bounds are \(7/4\) and \(9/4\).
This does not contradict the infinite mean of the fixed initially even
endpoint's correction.

At any positive equal-count separation \(D\), exactly \(v=v_2(D)\)
one-step returns occur before separation becomes odd. Under the original
fair law a common step sends

\[
 (P,D)\mapsto(P/2,D/2)
       \quad\text{or}\quad((3P+1)/2,3D/2).
\]

Its mean minimum increases by \(1/4\). Its mean separation stays \(D\),
so concavity of \(\ell(D)=\log_2(D+1)\) makes the mean logarithm
nonincreasing. After these \(v\) steps,

\[
       \mathbb E\bar P=P+v/4,\qquad
       \mathbb E\ell(\bar D)\le\ell(D),\qquad v\le\ell(D).
\]

A group consists of this run and the following odd-separation excursion.
Apply (8) conditionally at its departure. The complete grouped transition
satisfies

\[
       \mathbb E P_{\rm next}
       \le\tfrac12P+\tfrac{49}{8}\ell(D)+\tfrac54.           \tag{9}
\]

Kill the process at fusion. Let \(q_j,l_j,p_j\) be respectively the
probability of starting group \(j\), its logarithmic separation mass,
and its minimum-coefficient mass. Initially \(p_0=1\).
Then \(8p_{j+1}\le4p_j+49l_j+10q_j\).

The number of groups is at most the number \(N\) of count returns
to fusion, hence \(\sum q_j\le C_*\). Every group starts at one of the
original nonfused returns or at time zero. The earlier
[fourth-root occupation budget](RETURN-CORRECTION-MOMENTS.md) is
\(\mathbb E\sum_{j<N}D_j^{1/4}\le40(1+9C_*)\), including \(D_0=1\).
The elementary integral bound
\(\log_2(D+1)\le8D^{1/4}\) therefore gives, allowing a harmless slack,

\[
                       \sum_jl_j\le328+2880C_*.
\]

Finite telescoping of (9), then monotone convergence, yields

\[
 \sum_jp_j
 \le2+\tfrac{49}{4}\sum_jl_j+\tfrac52\sum_jq_j
 \le4020+\tfrac{70565}{2}C_*
 <4100+36000C_*=:B_* .                                    \tag{10}
\]

Thus the sum of \(P\) over the nonfused ends of all these excursions
has mean at most \(B_*\). This statement concerns the selected grouped
returns. Multiplying the group-start cost by the number of intervening
one-step returns would require an additional mixed-moment estimate.

## 4. Entire fixed-clock, fixed-count components have finite energy

Restrict to even original source residues, and let \(\mathcal G\) contain
their nonfused grouped-return prefixes. For \(i\in\mathcal G\), use
clock \(t_i\), common count \(a_i\), residue \(r_i<2^{t_i}\), and smaller
image \(y_i=\min\{U^{t_i}(r_i),U^{t_i}(r_i+1)\}\). Define

\[
 \kappa^{\rm low}_{t,a}(z)
  =\sum_{\substack{i\in\mathcal G\\t_i=t,\ a_i=a}}
       2^{-t}3^a\mathbf1_{\{z=y_i\pmod{3^a}\}}.             \tag{11}
\]

At fixed \(t,a\), the selected input for the smaller endpoint is
\(r_i+\epsilon_i\), with \(\epsilon_i\in\{0,1\}\). Because all \(r_i\)
are even, these inputs are distinct and stay in the same full binary
period. These two assertions are kernel checked.

The [numerator quotient injection](BINARY-IMAGE-ENERGY.md) therefore
applies to their entire selected set. Write
\(C_i^{\rm low}=(3^a+N_t(r_i+\epsilon_i))/2^t\). The formal minimum
identity gives \(C_i^{\rm low}\le P_i\): equality holds if the original
first endpoint is smaller, and the difference is \(\Lambda_i\) otherwise.
The fixed-fibre quadratic bound consequently gives

\[
 \|\kappa^{\rm low}_{t,a}\|_2^2
       \le2\sum_{\substack{i\in\mathcal G\\t_i=t,\ a_i=a}}
                        2^{-t}C_i^{\rm low}
       \le2\sum_{\substack{i\in\mathcal G\\t_i=t,\ a_i=a}}
                        2^{-t}P_i.                         \tag{12}
\]

Summing (12), and using (10), proves (1). Distinct source prefixes at
the same clock are disjoint. Thus (1) really controls a collection of
disjoint-source image overlaps, including every collision inside each
component (11).

It does not bound
\(\|\sum_{t,a}\kappa^{\rm low}_{t,a}\|_2^2\), which also contains
products between different clocks or counts. Nor does changing the
endpoint label preserve the original one-endpoint image density.
What is preserved exactly is the pairwise cost:

\[
 [f_h(x)-f_h(y)]^2
        =[f_h(\min(x,y)+D)-f_h(\min(x,y))]^2 .
\]

Using this in a complete transport estimate still requires the missing
cross-component and future-gradient control, together with treatment
of the omitted one-step returns.

## Verification and scope

Run `python3 verify_lower_return_energy.py`. The
[record](../results/lower-return-energy/verification.json) distinguishes
eleven kernel arithmetic roots, exact finite checks, and written limits.
Finite checks use outward rational power and logarithm enclosures,
retain unfinished paths, and compare the full component energy with
its individual-column diagonal and the full truncated density energy.

This result addresses part of the overlap problem after an explicit
change of endpoint convention and return grouping. It proves neither
criterion Q, a bound for actual forward gradients, nor exclusion of
escape or additional positive cycles.
