# Why predecessor closure cannot force weighted contraction

**Status: a written obstruction to a proposed proof method, not a proof or
disproof of Collatz.** Backward closure alone cannot imply a uniform
weighted contraction, even for cofinite sets whose entire complement
provably reaches the chosen floor. The same obstruction applies at every
fixed block length and after any fixed amount of survival information.
The specific time history of the actual survivor sets remains available
to a different argument. No novelty is asserted.

The all-index arithmetic family, its convergence, and the exact single
exit of its ancestor basins are kernel checked in
[WeightedBasinBarrier.lean](../lean/WeightedBasinBarrier.lean). Infinite
weighted sums and the cofinite construction below are written arguments.
They do not certify the missing recurrent contraction in
[WEIGHTED-SURVIVORS.md](WEIGHTED-SURVIVORS.md).

## 1 The proposed closure argument and its obstruction

Fix \(H\ge1\), \(s>1\), and use the shortcut map \(U\). For a set of
positive integers define its killed preimage and weight by
\[
 P A=\{n>H:U(n)\in A\},\qquad \mu(A)=\sum_{n\in A}n^{-s}.
\]
The actual survivor sets \(S_k=\{n:\tau_H(n)>k\}\) satisfy
\(P S_k=S_{k+1}\subset S_k\). Each \(S_k\) is cofinite, and every
removed positive integer reaches the floor by time \(k\).

One possible proof attempt would derive a contraction from these
structural properties. The following stronger negative statement rules
out such a uniform estimate.

**Theorem.** Given \(H\ge1\), \(s>1\), integers \(k\ge0,r\ge1\),
and \(0<\rho<1\), there is a cofinite set \(A\subseteq\{n>H\}\)
with all the following properties:

- \(P A\subseteq A\).
- For a finite integer \(T\), \(S_T\subseteq A\subseteq S_k\).
  In particular every positive integer outside \(A\) provably reaches
  the floor within a common finite bound.
- Nevertheless \(\mu(P^r A)>\rho\mu(A)\).

These sets need not equal any \(S_j\). The theorem does **not** refute
contraction for the actual survivor sequence, or the claim that adequate
contraction might recur infinitely often along that sequence.

## 2 Explicit convergent paths with arbitrarily large expansion

For any integer \(K\ge1\), set
\[
 a=3^{K-1},\qquad b=2^a,\qquad
 q=\frac{b+1}{3^K},\qquad x=2^Kq-1.
\]
The quotient \(q\) is a positive integer. Indeed,
\(3^{j+1}\mid2^{3^j}+1\) for every \(j\ge0\). Starting from
\(3\mid2+1\), cubing a number congruent to \(-1\pmod{3^{j+1}}\)
adds another factor of three to its cube plus one. The Lean proof uses
an explicit polynomial factorization and induction; it does not import
an external lifting theorem.

The first \(K\) steps from \(x\) are odd steps, with
\[
 U^j(x)=2^{K-j}3^jq-1\quad(0\le j\le K),\qquad U^K(x)=b.
\]
The path increases through this prefix, then \(b=2^a\) halves to one
in \(a\) further steps. Thus the entire family converges. Moreover
\[
 3^Kx\le2^Kb,\qquad x/b\le(2/3)^K.\tag{1}
\]
The inequality includes the additive minus-one terms: after multiplication
the common leading terms cancel, leaving \(2^K\le3^K\).
Since \(x\ge2^K-1\), the whole rising prefix is above any fixed floor
once \(K\) is sufficiently large.

## 3 An infinite convergent basin with only one exit

For \(b>H\), define the killed ancestor basin
\[
 B_b=\{n:\exists t\ge0,\ U^t(n)=b,\ U^j(n)>H\ (0\le j\le t)\}.
\]
Take the power-of-two targets above with \(b\ge4\). Their forward
orbits never return to \(b\). Consequently
\[
 P B_b=B_b\setminus\{b\}.\tag{2}
\]
Every nonroot member has a positive-length path to \(b\), so its next
state is still in \(B_b\). The root leaves the basin; returning would
give a positive-time return to \(b\). These statements, and convergence
of **every** member of \(B_b\), are kernel checked.

The basin is infinite, since it contains all \(2^j b\). Its mass is
finite because \(s>1\), and it contains the rising-path source \(x\).
Therefore (1) and (2) give
\[
 1-\frac{\mu(PB_b)}{\mu(B_b)}
   =\frac{b^{-s}}{\mu(B_b)}
   \le(x/b)^s\le(2/3)^{sK}.\tag{3}
\]
The relative loss tends to zero along these explicitly convergent basins.
Thus even knowing that every member converges cannot give a uniform
one-step contraction for all backward-closed sets.

For the concrete parameters \(H=64,s=3/2,K=9\), the root is
\(2^{6561}\) and the source has 6,556 bits. The source reaches one
after 6,570 shortcut steps. The kernel verifies the parameters, path,
basin boundary, convergence, and integer inequality
\[
 1000^2 2^{27}<7^2 3^{27}.
\]
In particular this basin has \(\mu(PB_b)/\mu(B_b)>0.993\).
Applying the exact transport identity for an arbitrary set shows that
its eligible residue share exceeds \(69/200\); otherwise the previous
note's contraction estimate would give a ratio below \(0.993\).
This is a counterexample to a bound over all such populations, not a
counterexample at any actual survivor horizon.

## 4 Cofinite populations with a provably absorbed complement

Choose an integer \(R>b\). Let \(F_R\) consist of starts whose orbit
reaches \([1,H]\) before visiting \(b\) or any integer at least \(R\).
The endpoint in \([1,H]\) is allowed; all preceding states must belong
to \(\{H+1,\ldots,R-1\}\setminus\{b\}\). Put
\[
 A_R=\mathbb N_{>0}\setminus F_R.
\]
Here \(F_R\subset[1,R)\) is finite and all its members reach the
floor. Before that first entry no state can repeat, since a repetition
would prevent any later first entry. Thus every member reaches the
floor within \(R\) steps. Membership is decidable by finite simulation:
stop at the floor, a target, or a repeated state. A trapped cycle is
kept in \(A_R\), never mislabeled as convergent.

The set \(A_R\) contains every integer at least \(R\), is contained
in \(\{n>H\}\), and satisfies \(P A_R\subseteq A_R\). An integer
removed from \(A_R\) has an allowed path to the floor; any preceding
nontarget state can be prepended to that path. This also shows that its
exit set \(D_R=A_R\setminus P A_R\) obeys
\[
 D_R\subseteq\{b\}\cup\{n\in[R,2R):n\text{ even}\}.\tag{4}
\]
Outside the two targets, an exit would contradict the definition of
\(F_R\). An odd integer at least \(R\) increases, and an even integer
at least \(2R\) stays at least \(R\), so neither can exit. The root
\(b\) does exit: its remaining halving path stays below \(b<R\).

Every member of \(B_b\) belongs to \(A_R\): it either reaches the
upper target first, or reaches \(b\), while staying above the floor.
In particular \(x\in A_R\), whereas
\[
 \mu(D_R)\le b^{-s}+\sum_{n\ge R}n^{-s}.\tag{5}
\]
Choose \(R\) so large that the tail is at most \(b^{-s}\). For
\(s=3/2\), the explicit choice \(R=4b^3+1\) works by the integral
bound \(\sum_{n\ge R}n^{-3/2}\le2/\sqrt{R-1}\).
Equations (1) and (5) then give relative one-step loss at most
\(2(2/3)^{sK}\). Taking \(K\) large proves the cofinite obstruction.
For \(s=3/2,K=10\), the kernel comparison
\(2000\,2^{15}<7\,3^{15}\) again puts the ratio above \(0.993\).
The enormous finite complement at these parameters is defined and
proved absorbed by the written construction; it is not explicitly
enumerated by the verifier.

## 5 Fixed blocks and any fixed amount of survival history

For any set \(E\subseteq\{n>H\}\), the two inverse branches give
\[
 \mu(PE)\le\Gamma_s\mu(E),\qquad
 \Gamma_s=2^{-s}+2^s.\tag{6}
\]
The even branch contributes exactly \(2^{-s}\). If an odd predecessor
of \(y\) exists, then \(y\ge2\) and
\((2y-1)/3\ge y/2\), giving at most \(2^s\). Retaining the cutoff
can only reduce that upper bound.

For any backward-closed \(A\), let \(D=A\setminus PA\). Killed
preimages preserve set differences. The disjoint loss layers yield
\[
 \mu(P^kA)-\mu(P^{k+r}A)
   =\sum_{j=k}^{k+r-1}\mu(P^jD)
   \le\Gamma_s^k\left(\sum_{j<r}\Gamma_s^j\right)\mu(D).\tag{7}
\]
Apply this to \(A_R\). Choose \(K\ge k\), so the explicit source
\(x\) remains in \(P^kB_b\subseteq P^kA_R\). With the tail choice
in Section 4,
\[
 1-\frac{\mu(P^{k+r}A_R)}{\mu(P^kA_R)}
 \le2\Gamma_s^k\left(\sum_{j<r}\Gamma_s^j\right)(2/3)^{sK}.\tag{8}
\]
For fixed \(k,r\) the right side tends to zero. Finally put
\(A=P^kA_R\). It is cofinite, since every \(n>2^kR\) stays above
\(R\) for \(k\) steps. It is backward closed and
\[
 S_{k+R}\subseteq A\subseteq S_k.\tag{9}
\]
For the left inclusion, failure to lie in \(A\) means either hitting
the floor during the first \(k\) steps or landing in \(F_R\), from
which another \(R\) steps suffice. The right inclusion follows from
the definition of killed preimages. Choosing \(K\) large in (8)
proves the theorem in Section 1.

## 6 A lower limit on a possible power loss estimate

Allowing a smaller loss as the mass decreases is a different possible
route. However, the same construction excludes every proposed uniform
bound
\[
 \mu(A\setminus PA)\ge c\,\mu(A)^p\qquad(c>0)
 \tag{10}
\]
over all cofinite backward-closed populations with absorbed complements,
whenever \(1\le p<\log_2 3\).

Fix \(q=H+2\), and this time use
\(x=2^Kq-1\), \(b=3^Kq-1\). The first \(K\) odd steps still take
\(x\) to \(b\), above the floor. No convergence assumption about
this unbounded family is needed. The construction of \(F_R,A_R\) works
for an arbitrary target \(b>H\); (4) is an upper bound even if the
root does not exit. Choose \(R\) with the tail at most \(b^{-s}\).
Then
\[
 \frac{\mu(A_R\setminus PA_R)}{\mu(A_R)^p}
 \le2b^{-s}x^{sp}
 \le2^{s+1}q^{s(p-1)}(2^p/3)^{sK}\longrightarrow0.\tag{11}
\]
Here \(x\le q2^K\) and \(b\ge q3^K/2\). Every omitted start still
has its bounded absorption certificate, by definition of \(F_R\).
Thus (11) contradicts every fixed \(c>0\) in (10). An estimate with
\(p\ge\log_2 3\) is not ruled out by this argument; none is proved.

There is also a manageable exact witness against (10) with
\(H=64,s=p=3/2,c=1\). Take \(K=64,q=66\), giving
\[
 x=1217485108864830406655,\qquad
 b=226623132139305823987418039892545.
\]
The kernel verifies \(16x^9<b^6\), hence
\(2b^{-3/2}<x^{-9/4}\). With \(R=4b^3+1\), (5) and
\(\mu(A_R)\ge x^{-3/2}\) imply
\(\mu(A_R\setminus PA_R)<\mu(A_R)^{3/2}\).
Both this source and its target themselves reach one: the kernel checks
560 and 496 shortcut steps respectively. They are not counterexamples to
Collatz. The finite complement at this enormous \(R\) is again handled
by the written construction, not by explicit enumeration.

## 7 Verification and the remaining proof requirement

The [verifier](../verify_weighted_basin_barrier.py) checks the arithmetic
family independently, replays selected full convergent trajectories,
and constructs moderate cofinite examples with a separate finite-state
classification. It checks every omitted start's absorption, every exit,
and the exact disjoint inverse loss layers. Directed integer-square-root
enclosures also compute the masses, using the previous written integral
tail bounds. These numerical examples check the construction; the
arbitrary-parameter obstruction is a written theorem using the universal
kernel results, not an extrapolation from those examples.

The [verification record](../results/weighted-basin-barrier/verification.json)
records fresh Lean builds, exact scopes, logs, and hashes. There are no
admitted proofs, foreign axioms, or native finite checks in the new Lean
module. Run `python3 verify_weighted_basin_barrier.py` to reproduce it.

The weighted survivor identity and its finite mass bounds remain valid.
The results here rule out a proposed uniform static closure principle and
the indicated power refinements. A successful
argument must use additional information, such as the exact common clock
defining \(S_k=P^kS_0\) from \(S_0=\{n>H\}\), or prove a weaker
state-dependent loss estimate that still forces the mass to zero. Neither
such estimate nor any complete proof or counterexample has been obtained.
