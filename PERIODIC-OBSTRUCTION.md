# Exact obstructions to prescribed divergent Collatz itineraries

This note proves restrictions on possible counterexamples. It does **not**
prove the Collatz conjecture or produce a counterexample. The main periodicity
result is classical in the parity-conjugacy framework; the contribution here
is a self-contained integer proof and a checked Lean implementation, not a
claim of mathematical novelty. Bernstein and Lagarias describe the parity
conjugacy and distinguish the known direction from the conjectural converse
in [*The 3x+1 Conjugacy Map*, §1](https://websites.umich.edu/~lagarias/doc/bernstein.pdf).

Write the accelerated positive odd orbit as

\[
 2^{h_i}n_{i+1}=3n_i+1,\qquad h_i=\nu_2(3n_i+1)\ge1.
\]

## 1. A repeated growth block cannot diverge on the integers

**Affine rigidity theorem.** Let \(P,Q\) be nonnegative integers with
\(Q>1\) and \(\gcd(P,Q)=1\), and let \(W\in\mathbb Z\). If an infinite
integer sequence satisfies

\[
 Qx_{j+1}=Px_j+W\qquad(j\ge0),
\]

then \(x_j=x_0\) for every \(j\). No boundedness assumption is required.

**Proof.** Set \(d_j=x_{j+1}-x_j\). Subtract adjacent recurrence equations:
\(Qd_{j+1}=Pd_j\). Induction gives

\[
 Q^r d_r=P^r d_0.
\]

Since \(P^r\) and \(Q^r\) are coprime, \(Q^r\mid d_0\) for every \(r\).
A nonzero integer cannot be divisible by these arbitrarily large positive
integers. Thus \(d_0=0\), and the same argument at every index proves the
claim. ∎

The hypotheses matter: with \(P=Q=2\), \(W=2\), the sequence \(x_j=x_0+j\)
is an unbounded integer orbit. Coprimality rules out this cancellation of the
denominator.

For a finite halving word \(w=(h_0,\ldots,h_{k-1})\), where every \(h_i\ge1\)
and \(k\ge1\), set

\[
 H=\sum_{i=0}^{k-1}h_i,\quad P=3^k,\quad Q=2^H,\quad
 W=\sum_{i=0}^{k-1}3^{k-1-i}2^{h_0+\cdots+h_{i-1}}.
\]

The empty prefix sum in the \(i=0\) term is zero. Composing the prescribed
steps gives \(Qn_k=Pn_0+W\). If the same word repeats forever, its successive
block boundaries satisfy the affine rigidity theorem. Consequently the orbit
is already a cycle at the start of the repeated tail.

This covers both \(P<Q\) and \(P>Q\). In the latter case the required fixed
value \(W/(Q-P)\) is negative, so no positive integer can follow that word
forever. An expanding real affine map is therefore not by itself a
construction of a divergent integer Collatz orbit.

**Consequence.** A divergent positive Collatz orbit must have a halving
sequence that is not eventually periodic. This leaves all possible
aperiodic tails open, and it also leaves possible nontrivial cycles open.

## 2. Stronger uniqueness for arbitrary infinite itineraries

Suppose two integer sequences \(x_i,y_i\) obey the same positive halving
exponents. Their differences satisfy

\[
 2^{h_i}(x_{i+1}-y_{i+1})=3(x_i-y_i).
\]

Every power of two divides every difference. One can prove this directly by
induction on the power: divisibility by \(2^m\) at index \(i+1\), together
with \(h_i\ge1\), gives divisibility of \(3(x_i-y_i)\) by \(2^{m+1}\);
coprimality removes the factor three. Thus \(x_i=y_i\) at every index.

This proves that an infinite prescribed halving sequence has **at most one**
integer realization, even when the sequence is aperiodic. It does not prove
that it has any positive integer realization. In particular, constructing
compatible finite prefixes is insufficient to construct a positive integer
counterexample.

Applying uniqueness to \(x_i=n_{s+i+k}\) and \(y_i=n_{s+i}\) proves the full
eventual-periodicity statement directly when
\(h_{s+i+k}=h_{s+i}\) for all \(i\).

## 3. A finite bound on how long a word can repeat

Keep \(P,Q,W\) for a fixed halving word, and define its integer defect at a
block boundary by

\[
 E_j=(Q-P)x_j-W.
\]

The block equation implies

\[
 QE_{j+1}=PE_j,\qquad Q^mE_m=P^mE_0.
\]

Here \(P\), \(W\), and every accelerated orbit value \(x_j\) are odd,
whereas \(Q\) is even. Therefore every \(E_j\) is even. If the word occurs
\(m\) consecutive times, then

\[
 2^{mH+1}\mid E_0.
\]

For \(E_0\ne0\), this yields the explicit bound

\[
 m\le\left\lfloor\frac{\nu_2(|E_0|)-1}{H}\right\rfloor.
\]

Thus a proposed noncyclic starting value has a finite, computable limit on
the number of exact repetitions of any chosen word. If \(E_0=0\) and the
first block is actually followed, the block returns to its starting value
and determinism makes the orbit cyclic.

## 4. Excluding a concrete nonperiodic divergence construction

There is also a restriction on very long growing runs, even when the whole
itinerary is nonperiodic. Suppose \(L\) consecutive exponents equal one,
starting at odd-step time \(t\). Along such a run,

\[
 2^L(n_{t+L}+1)=3^L(n_t+1).
\]

Since \(n_{t+L}\) is odd and \(3^L\) is odd,
\(2^{L+1}\mid(n_t+1)\), and hence \(2^{L+1}\le n_t+1\).
Every accelerated step also satisfies

\[
 n_{i+1}+1\le\frac32(n_i+1),
\]

because \(h_i\ge1\). Combining these inequalities gives the necessary
condition

\[
 \boxed{\quad 2^{L+t+1}\le3^t(n_0+1).\quad}
\]

In logarithmic form,
\(L+1-t\log_2(3/2)\le\log_2(n_0+1)\). Therefore a proposed itinerary with
runs \((t_r,L_r)\) for which the left side tends to infinity cannot be
realized by **any** positive integer.

For example, concatenate the blocks

\[
 (2,1),\quad(2,1,1),\quad(2,1,1,1,1),\quad
 (2,\underbrace{1,\ldots,1}_{8}),\quad\ldots,
\]

with \(2^r\) ones in block \(r\), indexed from zero. This is nonperiodic
and has increasingly long runs of growing steps. The \(r\)-th run starts
at \(t_r=2^r+r\) and has length \(L_r=2^r\). The boxed inequality forces

\[
 n_0+1\ge 2\left(\frac43\right)^{2^r}
                  \left(\frac23\right)^r
 \qquad\text{for every }r.
\]

The right side tends to infinity, a contradiction for every fixed \(n_0\).
This rules out a genuinely nonperiodic family of apparent growth patterns.
It does not rule out schedules with shorter growth runs, irregular mixtures,
or other forms of aperiodic divergence.

## 5. What the cycle divisibility equation does and does not settle

For a positive halving word, put \(D=2^H-3^k\). It generates a positive
integer cycle if and only if

\[
 D>0\quad\text{and}\quad D\mid W.
\]

Necessity follows from \(Dn_0=W\). For sufficiency, let \(W_i\) be the
weight of the cyclic rotation starting at position \(i\). Direct expansion
gives

\[
 2^{h_i}W_{i+1}=3W_i+D,
\]

with indices modulo \(k\). Since \(D\) is odd, divisibility by \(D\)
propagates from \(W_i\) to \(W_{i+1}\). Every \(W_i\) is positive and odd,
so \(n_i=W_i/D\) are positive odd integers. The displayed identity gives
\(3n_i+1=2^{h_i}n_{i+1}\); because \(n_{i+1}\) is odd, the exponent is
exactly \(h_i\), as required. The resulting period can divide \(k\).

The cycle-equation method is classical; see Lagarias's discussion of the
Böhm–Sontacchi parametrization in [*The 3x+1 Problem and Its Generalizations*,
§2](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/htmlo/anhtml/node8-an2.shtml).
The proof of sufficiency above is included explicitly so that the use of the
criterion does not depend on an unchecked search filter.

For the known accelerated cycle \(1\to1\), every exponent is two and
\(W=D\). Proving that every positive word with \(D\mid W\) produces only
this cycle remains unproved here. Even that result would address cycles
only; aperiodic divergence would still need to be excluded.

## Verification scope

[`CollatzPeriodic.lean`](CollatzPeriodic.lean) formalizes:

- affine rigidity and denominator-power divisibility;
- the exact block formula from individual prescribed step equations;
- constancy at boundaries of an infinitely repeated block;
- uniqueness of integer realizations of arbitrary positive halving schedules;
- eventual periodicity of integer values from eventual periodicity of the
  actual halving schedule.

The finite repetition bound, nonperiodic long-run exclusion, and cycle
sufficiency proof above are written mathematical proofs; they are not claimed
to be Lean-checked in this file. The Lean file was checked with:

```sh
lean CollatzPeriodic.lean
```

All printed theorem dependencies are `[propext, Quot.sound]`. The file has no
`sorry`, additional axioms, Mathlib dependency, or `native_decide` proof.

The unresolved step is substantial: none of these results proves that every
positive integer's actual halving itinerary is eventually periodic, or that
every positive cycle is the known cycle. The original conjecture therefore
remains unsettled by this work.
