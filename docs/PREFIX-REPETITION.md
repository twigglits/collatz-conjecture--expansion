# Long repeated parity prefixes force a return

This note gives an exact finite obstruction to a nonrepeating positive-integer
Collatz trajectory. It applies without a density, complexity, or height
assumption about the entire itinerary. It does not cover arbitrary itineraries,
and a return can still be a hypothetical nontrivial cycle.

The finite results are kernel checked in
[PrefixRepetition.lean](../lean/PrefixRepetition.lean), using the parity-collision
lemma from [CollatzRepetition.lean](../CollatzRepetition.lean). The limiting and
word-theoretic consequences below are written deductions. No novelty is claimed:
this specializes the same congruence-and-growth argument used in
[STURMIAN-ATTEMPT.md](../STURMIAN-ATTEMPT.md) and
[CYCLE-WORDS.md, Section 4](../CYCLE-WORDS.md).

## 1. Exact criterion

Let \(U(n)=(3n+1)/2\) for odd \(n\), and \(U(n)=n/2\) for even \(n\).
Suppose the length-\(m\) parity prefixes starting at \(n\) and at
\(x=U^\ell(n)\) agree. Then
\[
 2^m\mid x-n.                                                   \tag{1}
\]
The one-step inequality \(2(U(n)+1)\le3(n+1)\) gives, by induction,
\[
 2^\ell(U^\ell(n)+1)\le3^\ell(n+1).                             \tag{2}
\]

**Finite theorem.** If the prefixes agree and
\[
 \boxed{3^\ell(n+1)\le2^{m+\ell},}                              \tag{3}
\]
then \(U^\ell(n)=n\).

Indeed, (2) and (3) imply \(x+1\le2^m\).
Also \(2^\ell(n+1)\le3^\ell(n+1)\le2^{m+\ell}\), hence
\(n+1\le2^m\). Thus both values lie below \(2^m\), and (1) forces
equality. In particular, equality in (3) is sufficient. Lean checks the
growth inequality, cancellation, congruence implication, and resulting
periodicity. Taking \(\ell>0\) makes this a nonzero return time.

Equivalently, every matching prefix at a nonreturning positive shift satisfies
\[
 \boxed{2^{m+\ell}<3^\ell(n+1).}                                \tag{4}
\]
This is an exact integer condition, so it needs no floating-point comparison.

## 2. Squares and fractional repetitions

If the parity word begins with a square \(ww\), with \(|w|=\ell\),
take \(m=\ell\). A nonreturning occurrence must obey
\[
 (4/3)^\ell<n+1,\qquad
 \ell<\frac{\log(n+1)}{\log(4/3)}.                              \tag{5}
\]
Consequently a nonrepeating positive-integer trajectory cannot have prefix
squares of unbounded block length. The statement applies separately to
every fixed tail of the trajectory.

More generally, a prefix of length \(L=\ell+m\) with period \(\ell\)
means exactly that its first \(m\) bits agree with the shift by \(\ell\).
Equation (4) gives
\[
 L-\ell\log_2 3<\log_2(n+1).                                  \tag{6}
\]
Therefore a nonrepeating itinerary cannot have such prefixes along a sequence
with \(L-\ell\log_2 3\) unbounded above. In particular, it cannot have unbounded
block lengths and repetition ratios \(L/\ell\ge\log_2 3+\varepsilon\)
for one fixed \(\varepsilon>0\).

The uniform gap matters: saying only \(L/\ell>\log_2 3\) at each length
does not ensure that the additive excess in (6) grows.

For a repetition beginning at time \(a\), apply (6) at \(U^a(n)\), and use
\(U^a(n)+1\le(3/2)^a(n+1)\). Every nonreturning shifted repetition obeys
\[
 L-\ell\log_2 3
 <\log_2(n+1)+a\log_2(3/2).                                  \tag{7}
\]
For squares this becomes
\(\ell\log_2(4/3)<\log_2(n+1)+a\log_2(3/2)\).
Thus occurrences far along a rapidly growing orbit need not be excluded.

## 3. Scope

An aperiodic word with arbitrarily large prefix squares cannot be a
positive-integer Collatz itinerary: one sufficiently large square would
force an exactly periodic trajectory. This also rules out an aperiodic
tail with that property.

This reaches beyond low factor complexity. For an explicit symbolic example,
let \(B_j\) concatenate all binary words of length \(j\), and define
\[
 W_1=1,\qquad W_{j+1}=W_jW_j\,1^{|W_j|^2}B_j.
\]
These nested prefixes define
an infinite word with arbitrarily large prefix squares. It contains every
binary word of every length, so its factor complexity is exactly \(2^m\) and it
is not eventually periodic. At the end of each inserted one-run, its one
density is at least \(|W_j|/(|W_j|+2)\), tending to 1. Thus neither small factor
complexity nor a low upper one-density explains its exclusion; (5) does.
This is a constructed word, not an asserted Collatz trajectory.

A further sufficient condition is an aperiodic fixed point of a nonerasing
morphism whose prolongable letter a has an image beginning aa. Iterating the
morphism produces square prefixes with unbounded root length, so the same
obstruction applies. It asserts a condition on the morphism, not a theorem
about all morphic words.

The argument does not assert that every aperiodic binary word has large
prefix squares. Nor does it bound arbitrary nonrepeating trajectories,
exclude every substitution-generated word, or prove that an eventual cycle
must be the known \(1,2\) shortcut cycle.

Reproduce the kernel check with the pinned Lean toolchain:

```sh
mkdir -p /tmp/collatz-prefix-lean
lean -o /tmp/collatz-prefix-lean/CollatzRepetition.olean CollatzRepetition.lean
LEAN_PATH=/tmp/collatz-prefix-lean lean lean/PrefixRepetition.lean
```

All five printed theorem dependencies contain only the standard logical
axioms `propext` and `Quot.sound`. There is no `native_decide` or admitted
proof in this module.
