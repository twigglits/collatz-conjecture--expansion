# Infinite nonfusion occupation at the known cycle

**Collatz remains unresolved.** The larger inverse occupation used in
the [harmonic trace bound](HARMONIC-RETURN-TRACE.md) is not finite at
the positive integer targets 1 and 2. In fact, a subseries consisting
entirely of even sources already known to converge has infinite mass:

\[
 \boxed{Z_H(1)\longrightarrow\infty,\qquad
        Z_H(2)\longrightarrow\infty.}                         \tag{1}
\]

These are the sums over **all nonfused clocks**, not just equal-count
returns. The preceding bounds still give \(Z_H(a)=O_a(\sqrt H)\).
Thus a vanishing Cesaro average does not imply a finite undiscounted
integer trace, even inside the known basin. Finiteness of the selected
return traces \(K^*_0(a)\) and \(K^{\rm low}_0(a)\) remains open.

The infinite argument is **written**. It uses positive lower natural
density of the basin of one from the already replayed external
[predecessor theorem](PREDECESSOR-DENSITY-REVIEW.md), the local written
simple-path reciprocal packing bound, and the local written count of
balanced descendants. It uses no natural-passage premise, natural
density limit, or assumption of universal convergence. Eight new kernel
roots check the finite grade and refinement logic and a geometric identity.

## 1. Restrict the defects to parents in the known basin

Let \(\mathcal B\) be the positive integers reaching one under the
shortcut map \(U\), and put
\[
 \mathcal D=\{n\in\mathcal B:
       (2n,2n+1)\text{ never has both equal endpoints and equal
       cumulative odd counts}\}.
\]
The second endpoint need not be known to converge. Every selected first
endpoint \(2n\), however, belongs to \(\mathcal B\).

The earlier [dyadic defect argument](DYADIC-COALESCENCE-DEFECTS.md)
counted defects with arbitrary parents. The needed strengthening is
\[
 \boxed{\sum_{n\in\mathcal D}\frac1n=\infty.}                 \tag{2}
\]
It is not legitimate to infer (2) merely by restricting that earlier
divergent sum to a subset. Here is the argument for this subset.

For uniform \(x\in[1,2)\), write \(n_k(x)=\lfloor2^kx\rfloor\).
Let \(A_k\) be the event that \(n_k\in\mathcal D\) and the next
binary child is odd. With
\[
 d_k=2^{-k}\#(\mathcal D\cap[2^k,2^{k+1})),\qquad
 q_k=2^{-k}\#(\mathcal B\cap[2^k,2^{k+1})),
\]
we have \(|A_k|=d_k/2\). Put \(S=\{x:A_k\text{ occurs only
finitely often}\}\).

After the last marked edge, any visit to a known-basin parent starts
an uninterrupted chain of balanced refinements. Indeed an even child
always remains in that basin. An odd child from a known parent must
be balanced, since otherwise this would be another marked edge.
Balanced coalescence transfers convergence to the odd child.
The new kernel theorem `unmarked_known_chain` verifies this propagation
without assuming that the odd child's convergence was given in advance.

For each fixed convergent root, the earlier bounded-odd-count argument
shows that the probability of an infinite balanced refinement chain is
zero. Its depth-\(j\) population is at most a polynomial in \(j\),
inside \(2^j\) possible descendants. Take the countable union over
possible starting levels and roots. Consequently, for almost every
\(x\in S\), the prefixes \(n_k(x)\) eventually all leave \(\mathcal B\).
Dominated convergence on \(S\) gives
\[
 \limsup_k q_k\le |S^c|=\Pr(A_k\text{ infinitely often}).     \tag{3}
\]

If \(\delta=\underline d(\mathcal B)>0\), then
\(\limsup_k q_k\ge\delta\): a smaller upper limit on all late
dyadic bands would, after summing their geometric lengths, contradict
that lower density. The replayed external theorem supplies this
positivity, but no value of \(\delta\) is needed. Therefore
\[
 \Pr(A_k\text{ infinitely often})\ge\delta>0,
 \qquad \sum_k d_k=\infty,                                  \tag{4}
\]
where the second conclusion is the first Borel--Cantelli lemma.
Finally,
\[
 \sum_{\substack{n\in\mathcal D\\2^k\le n<2^{k+1}}}\frac1n
       \ge\frac{d_k}{2}
\]
proves (2). Neither independence between different levels nor a natural
density for \(\mathcal D\) is asserted.

## 2. A uniform positive first-hit weight

Let \(\tau(n)\) be the first shortcut arrival at one for
\(n\in\mathcal B\), and let \(a_t(n)\) count the odd inputs.
Define
\[
 w_1(n)=\frac{n3^{a_{\tau(n)}(n)}}{2^{\tau(n)}}.
\]
This is the product of \(3u/(3u+1)\) over the odd inputs strictly
before that arrival. The prefix has no repeated state; a repetition
before the first visit to one would prevent that visit. Its odd inputs
are the same in ordinary and shortcut time.

The existing [simple-path packing argument](FINITE-PATH-PACKING.md)
therefore gives the same first-hit floor used in
[weighted dissipation](WEIGHTED-DISSIPATION.md):
\[
 \sum_{u\text{ odd before first hit}}\frac1u\le8192,
 \qquad
 \boxed{c_0:=e^{-8192/3}\le w_1(n)\le1.}                    \tag{5}
\]
For (5), use \(\log(1+1/(3u))\le1/(3u)\) and the finite product.
At \(n=1\) the product is empty and equals one. No density or
mixing hypothesis is used for this floor. This applies before first
arrival, not to the weight after arbitrarily many cycle repetitions.

## 3. The exact subseries at targets one and two

Write \(\lambda_t(m)=3^{a_t(m)}2^{-t}\), and let \(p_t(m)\)
indicate nonfusion of \((m,m+1)\) by clock \(t\). Thus
\[
 Z_H(a)=\sum_{t=0}^H\sum_{\substack{m>0\\U^t(m)=a}}
                      \lambda_t(m)p_t(m).
\]
At each finite clock the source sum is finite, since \(m\le2^t a\).
For \(n\in\mathcal D\), the source \(m=2n\) has
\(p_t(m)=1\) at every clock. Its first arrival at one has coefficient
\[
 \lambda_{\tau(2n)}(2n)=\frac{w_1(n)}{2n},
 \qquad \tau(2n)=\tau(n)+1.
\]
After that, visits to one occur every two shortcut steps. Each pair
of steps has one odd input, so the coefficient ratio is \(3/4\).
Consequently
\[
 \sum_{t:U^t(2n)=1}\lambda_t(2n)
      =4\lambda_{\tau(2n)}(2n)=\frac{2w_1(n)}n.             \tag{6}
\]
The first visit to two is exactly one step before the first visit to
one. Its coefficient is twice as large, and its subsequent visits have
the same geometric ratio. Hence
\[
 \sum_{t:U^t(2n)=2}\lambda_t(2n)=\frac{4w_1(n)}n.           \tag{7}
\]

Nonnegative summation, (2), and (5)--(7) give the stronger identities
for the restricted extended sums:
\[
 \boxed{
  Z^{\mathcal D}_\infty(1)
       =2\sum_{n\in\mathcal D}\frac{w_1(n)}n=\infty,
  \qquad
  Z^{\mathcal D}_\infty(2)
       =4\sum_{n\in\mathcal D}\frac{w_1(n)}n=\infty.}        \tag{8}
\]
These subseries use only even first sources reaching the known cycle.
They are dominated by the corresponding even-source versions of
\(Z_H\), and then by \(Z_H\) itself. Monotone convergence proves (1).
No hypothetical escaping source is used to obtain the divergent mass.

## 4. What this rules out

Combine (1) with the earlier local written estimate
\(Z_H(a)\le350C_*aG_a\sqrt H\), where \(G_1=G_2=4\).
At these two fixed targets the trace diverges while
\(Z_H(a)/H\to0\). The same conclusions hold for the restricted
even-source subseries in (8). No lower growth rate in \(H\) is claimed.

For the per-clock summand \(z_t(a)\), the upper bound also gives
\(\sum_{t\ge1}t^{-\sigma}z_t(a)<\infty\) for every
\(\sigma>1/2\), whereas the undiscounted series diverges at 1 and 2.
The behavior for \(0<\sigma\le1/2\) is not determined here.

This closes a possible shortcut in the integer-sampling problem:
one cannot prove finiteness of a selected return trace by first proving
finiteness of this larger nonfusion majorant. The equal-count restriction
must be retained or a suitable time discount supplied. The new
[lower-return Haar powers](LOWER-RETURN-CLOCK-MOMENTS.md) concern a
different selected density, and are unchanged by (8).

In particular, (8) does not prove divergence of either selected return
trace, failure of any finite power bound for actual gradients, or
failure of criterion Q. Escape, additional cycles, and Collatz remain
unresolved.

## Verification

Run `python3 verify_known_basin_nonfusion_trace.py`. The
[record](../results/known-basin-nonfusion-trace/verification.json)
separates eight new kernel roots from exact finite checks and the written
infinite proof. The kernel verifies propagation from an unmarked known
visit, the grade test when both arrivals are supplied, perpetual
nonfusion of a defective pair, and the finite linear Green identity.

The finite census certifies the first arrivals of every endpoint it
uses. It compares grade classification with direct paired trajectories,
computes complete geometric tails for finite source subsets, and
independently enumerates finite inverse traces. It does not infer
divergence or an asymptotic density from those finite values. Prior local
records and the retained objects and build logs of all 389 external PLD
modules are authenticated. Their recorded source hashes agree with the
retained archive-authentication inventory. The old temporary source files
are now absent, so this is reuse of the completed replay, not fresh
authentication of those source files or a new external build.
