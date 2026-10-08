# The mask congruence in mechanical rank order

At coprime counts, the eligible edit coefficients form a geometric progression
modulo the cycle denominator when ordered by mechanical rank. Its sum is a unit.
The unrestricted mask equation therefore has the simpler equivalent form
\[
 \boxed{(1-z)\sum_{j=0}^{s-1}\varepsilon_jz^j\equiv1\pmod D,
 \qquad \varepsilon_j\in\{0,1\}.}                         \tag{1}
\]
This is an exact reformulation, **not an exclusion of arbitrary masks**.
It preserves the dependence on the full denominator.

The modular algebra, coefficient exponent identity, unit implication, and
equivalence are kernel checked in
[MaskRankArithmetic.lean](../lean/MaskRankArithmetic.lean).
The mechanical floor/permutation bridge and the consequences in Sections 5–6
are written proofs. The [verification record](../results/mask-rank-arithmetic/verification.json)
distinguishes these from the independent finite Python checks.

## 1. Counts, cut, and rank

Assume
\[
 k>1,\quad \gcd(k,N)=1,\quad 3k\le2N<4k,\quad
 D=2^N-3^k>0,\quad s=2k-N.
\]
These hypotheses include every coprime critical count pair with \(k>1\).
No small logarithmic-gap hypothesis is needed here.
Since \(k,N>0\), the denominator is coprime to six.

Let \(a_u=\lfloor(u+1)N/k\rfloor-\lfloor uN/k\rfloor\).
Use the common cut
\[
 b=(a_1,a_2,\ldots,a_{k-1},a_0).
\]
The first symbol is 2, the last is 1, and no cyclic \(11\) occurs. Write
\[
 S_i=\lfloor(i+1)N/k\rfloor-1,\qquad
 j_i=(i+1)N\bmod k,\qquad 0\le i<k.
\]
Then
\[
 kS_i+j_i+k=N(i+1).                                    \tag{2}
\]
The ranks \(j_i\) are a permutation of \(0,\ldots,k-1\), by coprimality.

Put \(r=N-k\), so \(s=k-r\le r\). At phase \(j_i\), the next halving
symbol is 1 exactly when \(j_i<s\). Its preceding phase is
\(j_i-r\bmod k=j_i+s\ge s\), so the preceding symbol is 2.
Thus the eligible disjoint \(21\) pairs have midpoint ranks exactly
\[
 0,1,\ldots,s-1.
\]
The cut has rank \(r\ge s\), so no eligible midpoint crosses it.
In rank order, denote the edit coefficients by
\[
 c_{j_i}=3^{k-1-i}2^{S_i-1}.
\]
Rank zero occurs at \(i=k-1\), hence
\[
 \kappa:=c_0=2^{N-2}.                                   \tag{3}
\]
This fixed cut makes the normalizing coefficient explicit.

## 2. One modular generator for both counts

Choose \(1\le q<k\) with \(qN\equiv1\bmod k\), and write
\[
 qN=kt+1.
\]
Here \(t\ge0\). Since \(3\) is invertible modulo \(D\), define
\[
 z\equiv2^t(3^q)^{-1}\pmod D.                            \tag{4}
\]
Using \(3^k\equiv2^N\), raising (4) to powers \(k\) and \(N\) gives
\[
 \boxed{2z^k\equiv1,\qquad 3z^N\equiv1\pmod D.}          \tag{5}
\]
For example, the first identity follows from
\(3^{qk}z^k\equiv2^{tk}\) and
\(3^{qk}\equiv2^{qN}=2^{kt+1}\), cancelling the unit \(2^{kt}\).
The second uses \(qN=kt+1\) and cancels \(3^{kt}\).
Both cancellations are explicit in `count_roots`.

For nonnegative \(A,B\), (5) implies
\[
 (3^A2^B)z^{NA+kB}\equiv1\pmod D.
\]
Equation (2) gives
\[
 N(k-1-i)+k(S_i-1)+j_i=k(N-2).
\]
Comparing this monomial inverse with that of \(\kappa\) proves
\[
 \boxed{c_j\equiv\kappa z^j\pmod D\qquad(0\le j<s).}    \tag{6}
\]
The nonnegative exponent argument, including its exact integer phase
hypothesis, is checked by `monomial_rank` and `cut_one_coefficient`.
Identifying the floor phases and permuting the finite coefficient list remain
the written bridge in Section 1.

## 3. The total coefficient is coprime to the denominator

Since \(N+s=2k\), the two identities in (5) imply
\[
 4z^s\equiv3\pmod D.                                    \tag{7}
\]
One division-free verification multiplies both sides by \(3z^N\equiv1\):
the left side becomes \(3(2z^k)^2\equiv3\).

Let \(G_s(z)=1+z+\cdots+z^{s-1}\). The ordinary polynomial identity
\((1-z)G_s(z)=1-z^s\), followed by (7), gives
\[
 \boxed{4(1-z)G_s(z)\equiv1\pmod D.}                     \tag{8}
\]
In particular \(G_s(z)\) and \(1-z\) are both units. As
\[
 C=\sum_{j=0}^{s-1}c_j\equiv\kappa G_s(z)\pmod D
\]
and \(\kappa\) is a power of two, we obtain
\[
 \boxed{\gcd(C,D)=1.}                                    \tag{9}
\]
The unit proof and its conversion to the natural-number gcd statement are
kernel checked. Coprimality of the counts matters; repeated words are treated
separately in Section 5.

## 4. The target-one equation

For the chosen mask, set
\[
 E(z)=\sum_{j=0}^{s-1}\varepsilon_jz^j,\qquad
 P(z)=\sum_{j=0}^{s-1}(4-\varepsilon_j)z^j=4G_s(z)-E(z).
\]
The earlier [exact mask arithmetic](MASK-CYCLE-OBSTRUCTIONS.md) gives
\[
 W_{\rm mask}=D+4C-X,\qquad X=\sum_j\varepsilon_jc_j.
\]
By (6),
\[
 W_{\rm mask}\equiv\kappa P(z)\pmod D.
\]
Both \(\kappa\) and \(1-z\) are units, and (8) gives
\[
 \begin{aligned}
 D\mid W_{\rm mask}
 &\iff P(z)\equiv0\pmod D\\
 &\iff (1-z)E(z)\equiv1\pmod D.
 \end{aligned}
\]
The kernel theorem `mask_equation_iff` takes the reindexed \(C,X\)
congruences as explicit hypotheses. It neither assumes nor proves that the
binary equation has no solutions.

Large multiplicative order is insufficient to reject a short polynomial.
At \(k=11,N=18\), the denominator is \(D=84997\), divisible by 11.
The generator reduces to \(z=6\bmod11\), of order 10, yet
\[
 4+3z+4z^2+3z^3=814\equiv0\pmod{11}.
\]
Thus the degree-three mask with selected ranks 1 and 3 passes this prime.
It fails divisibility by the full \(D\), as the independent replay verifies.
The concrete congruences and the checks of the proper divisors of 10 are
kernel checked without native evaluation. Multiplicative order controls
equalities between individual powers; it does not give linear independence
of several powers over a finite field.

## 5. Exact cancellation for repeated mechanical words

The gcd result gives a direct arithmetic exclusion of unedited mechanical
cycles, without a logarithm bound or a finite period cutoff.

Allow \(g=\gcd(k,N)>1\), keeping the other count and positivity hypotheses.
Put \(k_0=k/g,\ N_0=N/g,\ D_0=2^{N_0}-3^{k_0}>0\). The lower mechanical
word is the \(g\)-fold repetition of its coprime block. Cutting after its
first symbol retains this repetition. Affine composition gives
\[
 D=RD_0,\qquad W_{\rm base}=RW_0,\qquad C=RC_0,\qquad
 R=\sum_{\ell=0}^{g-1}2^{N_0(g-1-\ell)}3^{k_0\ell}.
\]
For \(C\), this also follows by subtracting the two identities
\(W_{\rm base}=D+4C\) and \(W_0=D_0+4C_0\).
The coprime block satisfies (9), and \(D_0\) is odd, so
\[
 \gcd(C,D)=\gcd(W_{\rm base},D)=R.                       \tag{10}
\]
Consequently the unedited word could be integral only if \(D_0=1\).
But \(2^{N_0}=3^{k_0}+1\) forces \(N_0=2,k_0=1\):
for \(N_0\ge3\), reduction modulo eight would require
\(3^{k_0}\equiv7\), whereas its residues are 1 and 3.
The smaller exponents give the stated single solution.
That solution has slope two, outside the strict upper count bound here.

This also covers all slopes for positive integer cycles following a
mechanical halving word. A positive denominator forces \(N/k>\log_2 3>3/2\).
If \(N/k<2\), the preceding argument applies. If \(N/k\ge2\), every halving
exponent is at least two, so each positive odd state \(x\) maps to at most
\((3x+1)/4\le x\). A cycle then forces equality everywhere, giving only
the state 1 with halving exponent two. This recovers an already excluded
class; it does not handle the independently edited masks.

## 6. Why a fixed collection of small divisors cannot exclude every mask

There is a separate elementary limit on modular sieves for the whole family.
In \(\mathbb Z/M\mathbb Z\), let \(u_1,\ldots,u_s\) all be units, and let
\(A_j\) be the residues of subset sums of the first \(j\) coefficients.
Then
\[
 A_0=\{0\},\qquad A_{j+1}=A_j\cup(A_j+u_{j+1}).
\]
If \(A_j\) is proper, this union increases its size. Otherwise
\(A_j+u_{j+1}=A_j\); repeated translation by the unit would put every
residue in \(A_j\), contradicting properness. Hence
\[
 |A_j|\ge\min(M,j+1),\qquad
 \boxed{s\ge M-1\Longrightarrow A_s=\mathbb Z/M\mathbb Z.} \tag{11}
\]
The threshold is sharp: \(M-2\) coefficients all equal to one miss \(M-1\).
This proof works for composite moduli as well as primes, provided each
coefficient is a unit.

For any divisor \(M\mid D\), the mask coefficients are units modulo \(M\).
If \(M\le s+1\), some mask therefore satisfies \(4C-X\equiv0\bmod M\).
For several tested divisors, the same conclusion applies when their
**least common multiple** is at most \(s+1\). Separate smallness of the
divisors does not imply simultaneous coverage.

In particular a fixed finite collection of divisibility tests cannot exclude
the entire unrestricted family once \(s\) exceeds its fixed common-modulus
bound. This concerns those tests alone; it does not limit tests whose
combined modulus grows with the counts, exact subset decoding, or height
and orbit arguments. It complements the earlier
[local-lift limitation](CYCLE-LOCAL-LIFTS.md): that theorem supplies lifts
for each word modulo powers of two and three, whereas (11) allows the mask
to vary and concerns small divisors of the cycle denominator.

The remaining all-period question is still whether the binary equation (1)
can hold for a nontrivial integer mask cycle at the surviving counts.
Nothing here rules out arbitrary integer cycles or nonperiodic divergence.
