# What finite congruence tests can distinguish about cycle words

**Kernel-checked theorem.** Every nonempty positive halving word with
positive cycle denominator has exact residue-cycle witnesses modulo
\(2^a3^b\), for every \(a>0\) and \(b\ge0\).

Consequently, consistency in these residue graphs cannot by itself
exclude a member of the remaining mask family. This includes arbitrarily
large finite precisions and the exact halving exponents. A test that also
restricts the size of an integer lift has additional information and is
not covered by that limitation.

The complete finite theorem, including its application to every ordered
word, is proved in
[CycleLocalLifts.lean](../lean/CycleLocalLifts.lean). It imports the existing
kernel-checked cycle-numerator identities and uses no native evaluation,
analytic estimate, or external mathematical theorem.

## 1. Precise statement

Let \(h=(h_0,\ldots,h_{k-1})\) be nonempty, with \(h_i\ge1\), and put
\[
 H=\sum_i h_i,\qquad D=2^H-3^k>0.
\]
Let \(W_i\) be the usual numerator of the rotation of \(h\) beginning at
index \(i\). The existing
[complete cycle criterion](../CollatzCycleCriterion.lean) proves
\[
 W_i>0,\quad W_i\text{ odd},\quad W_k=W_0,\quad
 2^{h_i}W_{i+1}=3W_i+D.                                \tag{1}
\]
Also \(D\) is odd and coprime to 3.

Fix \(a>0,b\ge0\), and write
\[
 M=2^a3^b,\qquad L=2^H M.
\]
There are positive odd integers \(x_0,\ldots,x_k<L\) such that
\[
 \boxed{
 \begin{aligned}
 x_k&=x_0,\\
 v_2(3x_i+1)&=h_i,\\
 F(x_i)&\equiv x_{i+1}\pmod M,
 \end{aligned}}                                      \tag{2}
\]
where \(F(n)=(3n+1)/2^{v_2(3n+1)}\) is the accelerated odd map.

The congruence in the final line is essential. The integers \(x_i\) need
not satisfy \(F(x_i)=x_{i+1}\), and therefore (2) does not assert an integer
Collatz cycle. The theorem makes no assumption \(D\mid W_0\).

The Lean theorem `every_word_has_smooth_local_lifts` proves all of (2),
the positivity and range of every lift, and its stated quantifiers.
The more general `cyclic_local_lifts` works at any even precision \(L\)
coprime to \(D\), provided \(2^{h_i}M\mid L\) for every edge.

## 2. Construction, including the precision lost during division

Since \(\gcd(D,L)=1\), choose integers \(z,v\) with
\[
 Dz+Lv=1.
\]
The new Lean module proves this Bezout identity by the Euclidean
algorithm; it does not assume a supplied inverse is correct. Set
\[
 x_i=(zW_i)\bmod L
\]
using the least nonnegative residue. Then \(Dx_i\equiv W_i\pmod L\).
Because \(L\) is even and \(D,W_i\) are odd, \(x_i\) is odd, hence positive.
Equation (1) gives
\[
 2^{h_i}x_{i+1}\equiv3x_i+1\pmod L.                    \tag{3}
\]

Division by \(2^{h_i}\) loses \(h_i\) bits of precision. It is not valid
to divide an arbitrary congruence modulo \(M\) and keep the same modulus.
Here \(h_i\le H\), so \(2^{h_i}M\mid L\); reducing (3) first gives
\[
 2^{h_i}x_{i+1}\equiv3x_i+1\pmod{2^{h_i}M}.
\]
It follows that \(2^{h_i}\mid3x_i+1\), and
\[
 \frac{3x_i+1}{2^{h_i}}\equiv x_{i+1}\pmod M.
\]
The quotient is odd because \(M\) is even and \(x_{i+1}\) is odd.
Thus \(h_i\) is the exact valuation, and the quotient is the actual
accelerated successor. This proves (2).

`branch_of_congruence` checks the division and exact-valuation step for
arbitrary parameters. The word theorem also discharges the positivity,
coprimality, rotation, and \(h_i\le H\) hypotheses.

## 3. A concrete nontrivial closed walk

The word \((1,2,2)\) has \(D=5\) and cyclic numerators \(23,37,29\).
Its positive rational cycle is
\[
 23/5\longmapsto37/5\longmapsto29/5\longmapsto23/5.
\]
It is nonintegral. Nevertheless the following positive odd integer
edge witnesses give a closed walk modulo 64:

| Integer witness | Its residue modulo 64 | Actual successor | Successor residue | Exact halving |
|---:|---:|---:|---:|---:|
| 107 | 43 | 161 | 33 | 1 |
| 161 | 33 | 121 | 57 | 2 |
| 57 | 57 | 43 | 43 | 2 |

The residue walk is \(43\to33\to57\to43\). Its vertices are distinct
and none is the residue 1. The integer witnesses themselves do not close:
for example \(F(57)=43\ne107\).
Both the rational numerator values and the displayed modular edges are
kernel checked.

A sound residue graph puts an edge \(r\xrightarrow{h}s\) when some
positive odd integer \(n\equiv r\pmod M\) has exact valuation \(h\) and
\(F(n)\equiv s\pmod M\). Every integer cycle projects to a closed walk in
this graph, possibly with repeated vertices. The theorem constructs
such a walk for every positive-denominator word, including every critical
independent mask.

Computing the successor of only the smallest representative \(r\)
does not construct this graph: other lifts of \(r\) can have different
successor residues after division. Requiring the projected vertices to
be distinct likewise needs an additional justification, such as a bound
on the actual cycle's height.

## 4. A fixed height bound recovers the integer obstruction

The same module proves a complementary statement. If
\[
 0\le x\le B,\qquad D B<L,\qquad W<L,\qquad
 Dx\equiv W\pmod L,
\]
then
\[
 \boxed{Dx=W,\quad\text{and hence }D\mid W.}             \tag{4}
\]
Both sides of the congruence lie below \(L\), so they are equal.
`bounded_lift_forces_divisibility` kernel checks this deduction.

For a nonintegral rational cycle, the lifts at increasing precision
therefore cannot stay below one fixed bound \(B\). Compatible residues
at every precision do not supply one positive integer realizing them all.
Their compatibility describes a rational point in the relevant local
number systems.

This identifies the information that a useful arithmetic obstruction must
retain: a fixed integer lift or a sufficiently strong common size bound,
or divisibility at primes in the cycle denominator. The existing residue
sieve proves strict descent inequalities for integer classes; it is not
merely a consistency check on a finite residue graph and is unaffected.

## 5. A claimed exclusion found during the literature check

Theorem 6.2 of [Chachev, *Algebraic Obstructions and Perturbation Identities
for Collatz Cycle Uniqueness*, version dated 1 April 2026](https://vixra.org/pdf/2604.0007v1.pdf)
asserts a size inequality for binary halving words when
\(\alpha=2^H/3^k\ge2\). Its stated inequality fails for the primitive word
\[
 h=(1,2,2,2,2,1,2,2).
\]
Here
\[
 k=8,\quad H=14,\quad W=23413,\quad D=9823,\quad
 2^{14}\ge2\cdot3^8,\quad W-D=13590>D.
\]
These arithmetic values are kernel checked. In the displayed ratio
calculation, \(3^{k-1}/(1-1/\alpha)\) is incorrectly replaced by
\(\alpha/[3(\alpha-1)]\). The example refutes the claimed size estimate,
not the Collatz conjecture. That preprint's asserted binary-cycle
exclusion is therefore not used as a result here.

## 6. Verification and research consequence

The [verification record](../results/cycle-local-lifts/verification.json)
records the compiler, source hashes, kernel dependencies, and independent
Python checks. Those checks exercise words with larger halving exponents,
several precisions, the concrete graph, and mechanical masks. They provide
finite corroboration; the theorem for arbitrary words and precisions is
proved in Lean.

Reproduce the kernel proof by first compiling its dependency into a
temporary import directory, then checking the new file with that
directory in `LEAN_PATH`. Exact commands are in the record. The independent
script is:

    python3 verify_cycle_local_lifts.py

The immediate research consequence is that imposing more consistency
conditions modulo powers of 2 and 3 on otherwise unrestricted cycle
words cannot supply the missing mask exclusion. The next obstruction
must combine this local arithmetic with global integer information.
Full mask divisibility, wider integer cycles, and aperiodic divergence
remain unresolved.
