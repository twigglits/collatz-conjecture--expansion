# The source interval matters at a logarithmic Collatz clock

**Status: an audit of a proposed route to the missing convergence-density
estimate, not a proof or disproof of Collatz.** Seven kernel lemmas verify
the reflection identities and the explicit comparison cycle below. The
counting limits are written deductions using earlier kernel bounds and,
where stated, the unformalized passage estimates. No novelty is claimed.

The [minimum-clock result](CLOCKED-MINIMUM.md) leaves one numerical value
unidentified: the limiting proportion of starts through \(X\) reaching 1
within \(11\log X\) ordinary steps is \(p_1\), but \(p_1=1\) has not
been proved. This turn tested whether coalescence statistics over complete
parity-residue periods could supply that missing estimate. Two exact
facts prevent a direct inference from those statistics.

## 1. Complete periods and initial intervals give different limits

Use the shortcut map \(U(n)=n/2\) for even \(n\), and
\(U(n)=(3n+1)/2\) for odd \(n\). Define
\[
 F_X(k)=\frac1X\#\{1\le n\le X:U^k(n)\in\{1,2\}\}.
\]
The set \(\{1,2\}\) is the shortcut cycle, so this counts starts that
have entered it by shortcut time \(k\).

The existing [ordinary inverse-fibre bound](DENSITY-TIME-TRUNCATION.md)
gives fewer than \(195\,38^{T/12}\) distinct sources hitting any one
target by ordinary time \(T\), uniformly in the target. Every shortcut
step consists of one or two ordinary steps. Thus \(U^{6q}(n)\in\{1,2\}\)
implies an ordinary hit of one of those two targets by time \(12q\).
Consequently
\[
 \boxed{F_{2^{6q}}(6q)\le390\left(\frac{19}{32}\right)^q
                      \longrightarrow0.}                 \tag{1}
\]
This limit is unconditional. It is a written union-and-count consequence
of the earlier kernel fibre bound; it is not a new kernel theorem about
infinite limits. The upper bound becomes informative only at larger
\(q\); a bound exceeding one at a small \(q\) causes no difficulty.

In contrast, under the preceding written density and clock results,
\[
 \boxed{F_X(\lceil11\log X\rceil)\longrightarrow p_1>0.} \tag{2}
\]
For the limit, sandwich this proportion between the proportion reaching
1 by \(\lfloor11\log X\rfloor\) **ordinary** steps and the eventual
predecessor proportion at 1. Both tend to \(p_1\). The strict positivity
uses external PLD. We have not identified the value with one.

There is no contradiction between (1) and (2). At the clock in (2), a
complete parity period has length
\[
 P_X=2^{\lceil11\log X\rceil},\qquad
 X^{11\log2}\le P_X<2X^{11\log2}.
\]
The actual source interval occupies only
\(\Theta(X^{1-11\log2})\) of that period; the exponent is approximately
\(-6.62462\). A count averaged over the full period does not estimate
the count on this much shorter initial interval. In particular the
vanishing full-period proportion is not an upper bound tending to zero
for the proportion in (2).

More generally, (1) along multiples of six extends to full periods at
every shortcut depth: if \(k=6q+s\), \(0\le s<6\), the same argument
with ordinary time \(2k\) gives a constant times
\((19/32)^q\) after division by \(2^k\). Thus the difference is about
the sampling intervals, not the choice of a subsequence of depths.

## 2. Exact adjacent coalescence is unchanged by reversing the odd offset

Write \(U_+=U\) and let \(U_-(n)=(3n-1)/2\) on odd positive inputs,
with the same even-halving rule. Both send zero to zero. Let
\(w_\pm(k,n)\) count the odd inputs in the first \(k\) shortcut steps.
For \(0\le r\le2^k\), the kernel proves
\[
 \begin{aligned}
 w_-(k,r)&=w_+(k,2^k-r),\\
 U_-^k(r)+U_+^k(2^k-r)&=3^{w_-(k,r)}.                  \tag{3}
 \end{aligned}
\]
The induction proves the more general statement with initial sum
\(n+m=2^kq\) and final sum \(3^{w_-(k,n)}q\). Before the last step
the sum is even, so the two current states have the same parity. An even
step halves their sum; an odd step multiplies it by \(3/2\), since the
two additive offsets cancel. This also proves equality of their odd
counts. Natural-number subtraction is only used with the required
nonnegativity conditions.

Define a residue \(r\in\{0,\ldots,2^k-1\}\) to be a *coalescing
adjacent residue* when
\[
 U_+^k(r)=U_+^k(r+1),\qquad w_+(k,r)=w_+(k,r+1).        \tag{4}
\]
Both equalities matter. The exact affine-lift theorem then makes the
pair \((2^kq+r,2^kq+r+1)\) coalesce for every \(q\ge0\).
Endpoint agreement only at the representatives, with unequal odd
counts, would not give that identity on the entire progression.

Equation (3) gives the all-depth equivalence
\[
 r\text{ satisfies (4) for }U_+
 \quad\Longleftrightarrow\quad
 2^k-1-r\text{ satisfies (4) for }U_-.                  \tag{5}
\]
The reflection is a bijection. The two maps therefore have identical
counts at **every** depth, not merely in the finite experiment.
Our independent enumeration through depth 20 agrees with the known
sequence [OEIS A398792](https://oeis.org/A398792), which also records
this sign symmetry. For example the counts at depths 3, 10, and 20 are
1, 351, and 421643. The depth-20 proportion is about 0.4021101.

Nevertheless \(U_-\) has the cycle \(5\to7\to10\to5\); the kernel
proves that its start 5 never reaches 1. In the actual \(U_+\) map,
the kernel checks \(U_+^4(5)=1\). Thus identical complete-period
coalescence counts do not select the component containing 1. This is
a limitation of that proposed statistic, not a counterexample to
positive-integer Collatz. No predecessor-density theorem for the minus
map is assumed or inferred from the plus-map source replay.

The target-sensitive information changes under reflection. An endpoint
\(b\) of odd count \(w\) is reflected to \(3^w-b\), not generally to
1 or 2. Likewise the initial interval near zero is reflected to the
opposite end of the residue period. Those locations are information a
proof of the missing density estimate must retain.

## 3. Verification scope and the remaining estimate

[`ReflectedCoalescence.lean`](../lean/ReflectedCoalescence.lean) imports
the local affine module and proves seven theorems with standard axioms
only. It does not formalize a probability limit, or prove that the
coalescing-residue proportions tend to one. Both the imported module and
the new module are compiled afresh by the verifier.

[`verify_prefix_coalescence.py`](../verify_prefix_coalescence.py) checks
the reflection identities, both adjacent masks, and full-period cycle
counts by direct exact iteration through depth 20. It also checks exact
ordinary and shortcut entry times for a separate finite initial interval.
Logarithmic clocks for the latter use rational upper and lower bounds
on \(\log2\); floating-point numbers do not decide membership. No finite
proportion is promoted to an asymptotic density estimate.

The [record](../results/prefix-coalescence/verification.json) separates
the fresh kernel checks, reused fibre proof, finite replay, and written
deductions. Reproduce with:

```sh
python3 verify_prefix_coalescence.py
```

The required estimate still concerns the actual initial interval:
\(\#\{n\le X:U^{\lceil11\log X\rceil}(n)>2\}=o(X)\).
Together with the existing inputs it would give \(p_1=1\) and full
Collatz. Neither this audit nor its positive finite coalescence counts
prove it. Further work on this route needs control of those initial
intervals or component masses, not a replacement by whole-period counts.
