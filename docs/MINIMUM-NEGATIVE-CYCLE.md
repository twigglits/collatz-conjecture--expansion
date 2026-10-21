# Positive detours from the negative seventeen cycle

Every odd positive n with `3^118 | n+6` has a positive predecessor p<n
satisfying `C^307(p)=C^2(n)`. For the return-ladder sources
`N=8^R-5`, this applies to the infinite progression
`R=3^116*(2h+1)`. At each target `b_i=C^(5i+2)(N)`, the construction
uses i+69 even and 2i+119 odd inverse shortcut operations.
These sources cannot be least counterexamples.

The [Lean module](../lean/MinimumNegativeCycle.lean) has 26 audited roots.
Paths, divisibility, quantitative improvement and least-source exclusions
are kernel proofs. Three finite roots are axiom-free. No native reduction
axiom or external mathematical premise is used. Independent Python replay
has a separate scope. **The positive-integer Collatz conjecture remains
unresolved.** Universal convergence of either new family is not proved.

## 1. A negative cycle supplies a legal positive word

The magnitude map for negative shortcut inputs has the cycle

    17 -> 25 -> 37 -> 55 -> 82 -> 41 -> 61 -> 91
       -> 136 -> 68 -> 34 -> 17.

Odd magnitudes use `(3m-1)/2`; even ones use `m/2`. Its forward word
is `OOOOEOOOEEE`, with seven odd and four even inputs. This negative
cycle was already checked in the preceding module; it is not a positive
counterexample. The new consequence is a separately proved positive lift.
For q>=1 the actual shortcut path is

    2048q-17 -> 3072q-25 -> 4608q-37 -> 6912q-55
      -> 10368q-82 -> 5184q-41 -> 7776q-61 -> 11664q-91
      -> 17496q-136 -> 8748q-68 -> 4374q-34 -> 2187q-17.

All states are positive and every parity guard holds. The inverse word
is `W=EEEOOOEOOOO`. Composition gives the parameterized kernel identities

    Backtrack(4k,7k,2187^k*q-17,2048^k*q-17),
    C^(18k)(2048^k*q-17) = 2187^k*q-17.                  (1)

Backtrack is the complete legal-word relation from the
[return-ladder module](MINIMUM-RETURN-LADDER.md). The relation also holds
at k=0 using natural subtraction; positivity of the displayed source is
asserted here for k>=1 and q>=1.

## 2. Smaller sources and unbounded improvement factors

For odd n, `2*C^2(n)=3n+1`. If q>0 and

    2187^k*q = 3n+18,     P = 2048^k*q-17,

prefixing one inverse E to W^k gives the kernel identities

    Backtrack(4k+1,7k,C^2(n),P),
    C^(18k+1)(P) = C^2(n).                              (2)

The exact inequality `3*2048^17 < 2187^17` and power monotonicity
prove `0<P<n` for k>=17. The additive corrections are included:
`3P=3*2048^k*q-51`, whereas `3n=2187^k*q-18`.

For 1<=k<=16 the kernel checks `2187^k+33 < 3*2048^k`, which
implies P>n for every q>=1 satisfying (2). The k=0 case is proved
separately. Thus seventeen repetitions are the first successful choice
**within this particular E W^k construction**. This does not optimize
over other inverse words or other meeting points.

For any k>=1 and odd q>=1, explicit sources are

    n = 3^(7k-1)*q-6,     P = 2^(11k)*q-17.

At k=17 this covers every odd n with `3^118 | n+6`. Such an n cannot
be a least counterexample, because the smaller positive P has the same
future tail. The meeting clocks are 307 and 2, not equal clocks.

The kernel also proves

    3^a * 2048^(17a) <= 2187^(17a).

For k=17(a+1), it follows that

    3^a*(P+17) <= n+6,     3^a*P < n.                    (3)

The second strict inequality is a separate kernel root. Hence improvement
factors for actual smaller sources are unbounded as the source and its
divisibility condition vary. This does not give arbitrarily small
predecessors of one fixed source.

## 3. An infinite progression of return-ladder sources

The kernel proves elementary ternary lifting

    3^(s+2) | 8^(3^s)+1.

The induction uses `x^3+1+3x(x+1)=(x+1)^3`. If d divides x+1
and 3 divides d, both terms after rearrangement are divisible by 3d.
A second kernel induction proves that d dividing x+1 implies d dividing
`x^(2h+1)+1`. With s=116 this gives

    R_h = 3^116*(2h+1),     N_h = 8^R_h-5,
    3^118 | 8^R_h+1 = N_h+6.                            (4)

For every h>=0 the kernel constructs p with `0<p<N_h` and
`C^307(p)=C^2(N_h)`. The earlier `hit_to_initial` theorem joins b_i
to `C^2(N_h)` with i even and 2i odd inverse operations. Therefore,
for **every** `0<=i<R_h`,

    Backtrack(i+69,2i+119,b_i,p),
    C^(5i+307)(p) = b_i.                                (5)

The kernel also proves `h<N_h`. The visits to 20 modulo 27 are the
previously established indices 1<=i<R_h; b_0 is the initial two-step
image and is not a residue-20 visit.

This progression is disjoint from the preceding `R=85 mod162` escape
progression, because R_h is divisible by three. Its sources are 723
modulo 729; the earlier sufficient detour required 273 modulo 729.
Combining (5) with the preceding **written** sharp-budget classification
therefore gives

    M_(i+3)(b_i)=N_h,     M_(i+69)(b_i)<N_h.

The first equality retains its written-proof dependency. The new
construction and strict upper bound are kernel. The exact first useful
budget between these values remains unknown.

The smallest R_h is `3^116`. Its source N_h has `3^117` binary digits,
more than 10^55 bits. No such integer was materialized. The kernel proof
handles these sources symbolically; Python tests of (4) use modular
exponentiation. Proof elaboration keeps enormous exponents and symbolic
iterate expressions unexpanded where arithmetic is not being evaluated.

## 4. Concrete positive witnesses

The k=17, q=1 residue-class example is much smaller than the family (4):

    n = 3^118-6
      = 199667811101603467823686647723289448859052847504205678483,
    p = 2^187-17
      = 196159429230833773869868419475239575503198607639501078511.

These have 188 and 187 bits, respectively. The kernel checks p<n,
`C^307(p)=C^2(n)`, and arrivals at one at ordinary clocks 1,247 and
1,552. Python independently checks first-arrival minimality. The clock
difference 305 agrees with the meeting clocks in (2).

These examples prove convergence only for the two displayed sources.
They do not numerically instantiate (4) or establish convergence of an
infinite residue class.

## 5. Verification and the remaining question

Run `python3 verify_minimum_negative_cycle.py`, optionally with
`--lean /path/to/lean` when the pinned compiler is outside PATH. The
[verifier](../verify_minimum_negative_cycle.py) authenticates all 62 hashes
in the preceding inverse-escape manifest, freshly builds 30 modules
sequentially with Lean 4.33.1, and audits all 26 new roots. Historical
verification records are preserved.

Independent checks include:

- The signed negative cycle, 1,024 positive single-block lifts, and all
  2,048 pairs k=1..64, odd q=1..63, with full positive path replay.
- Fifteen additional full detours at k=17,34,68,136,272 and q=1,3,17,
  plus exact improvement arithmetic for a=0..128.
- Materialized ternary lifts s=0..9, modular lifts s=0..256, and all
  1,025 progression parameters h=0..1024, without constructing N_h.
- Both kernel arrival witnesses, independently replayed over 2,799
  ordinary steps.

The [manifest](../results/minimum-negative-cycle/verification.json)
records exact hashes, commands, compiler identity, logs and replay scope.
The [replay](../results/minimum-negative-cycle/replay.json) separates
actual integer paths from arithmetic and modular-only checks.

The new construction answers one concrete larger-budget case left open
by the three-step classification. It does not determine an optimal inverse
budget, settle whether one fixed extra budget works for every return-ladder
source, or force a useful predecessor on every possible least-counterexample
orbit. The earlier cap/residual bounds and both nontrivial-cycle and
divergence problems remain open.

