# A Machine-Verified Study of the Generalized Collatz Family f(x) = ax + c

**Current attempt at the original conjecture:** see [ATTEMPT.md](ATTEMPT.md).
This study supplies structural results and bounded computations; it does not
prove or disprove convergence for every positive integer. The September 2026
audit corrects earlier scope claims about undecidability, probabilistic drift,
and escape from a finite arithmetic window.

**Method constraint (repo hard rule):** every computational claim below is backed by either
(i) CUDA runs on an RTX 5090 (source: `collatz.cu`, raw output: `results/raw.jsonl`), or
(ii) Lean 4.31 machine-checked proofs/certificates (`CollatzTheory.lean`, `CollatzCerts.lean`).
Python (`analyze.py`) only cross-checks the GPU output with exact big-integer arithmetic and
generates the Lean certificate file; it is not a source of trust.

---

## 1. The problem and what "solving the general case" can mean

The Collatz map is `T(n) = 3n + 1` for odd `n`, `n/2` for even `n`; the conjecture says every
positive integer eventually reaches the cycle `1 → 4 → 2 → 1`. We study the natural two-parameter
family

```
T_{a,c}(n) = a·n + c   if n odd
           = n / 2     if n even          (a, c integers, default a=3, c=1)
```

Two relevant facts set the context:

1. **The base case is open.** Despite verification of all `n < 2^71` ([Barina 2025, J. of
   Supercomputing](https://link.springer.com/article/10.1007/s11227-025-07337-0)) and Tao's 2019
   result that almost all orbits attain almost bounded values, no proof of full convergence is
   known even for (3,1).
2. **A broader class of generalized Collatz maps has an undecidable uniform problem.**
   [Kurtz–Simon (2007)](https://doi.org/10.1007/978-3-540-72504-6_49), building on Conway,
   prove Π⁰₂-completeness for a class with residue-dependent affine rules.
   This does **not** establish undecidability for the two-parameter family studied here,
   nor for the single map (3,1), nor impossibility of a proof by elementary methods.
   Structural theorems and finite searches remain partial progress toward the original
   all-positive-integers objective; they do not replace that objective.

### Literature anchors (deep-research phase)

- Terras (1976), Everett (1977): almost every `n` has finite stopping time.
- Korec (1994): almost every orbit dips below `n^θ`, θ > ln3/ln4 ≈ 0.7925.
- Tao (2019): almost all orbits attain almost bounded values (logarithmic density).
- Steiner (1977), Simons–de Weger (2005), [Hercher (2023)](https://arxiv.org/abs/2201.00406):
  a nontrivial (3,1)-cycle must have at least 92 descent segments; combined with the 2^71
  verification its length exceeds ~10^11.
- Lagarias (1985, 1990, 2010): surveys; integer cycles of 3x+d ↔ rational cycles of 3x+1.
- [Belaga–Mignotte (1998, 2000)](https://projecteuclid.org/journals/experimental-mathematics/volume-7/issue-2/Embedding-the-3x1-conjecture-in-a-3xd-context/em/1048515662.pdf):
  experimental catalogues of known primitive cycles for 3x+d, d < 20000, and the conjecture that every 3x+d
  orbit is eventually periodic.
- Crandall (1978): the qx+1 problem, q ≥ 5 — conjectured existence of divergent orbits.
- Conway (1972), Kurtz–Simon (2007): undecidability of the generalized problem.
- The [Collatz Conjecture Challenge](https://ccchallenge.org/) is formalizing the literature in
  Lean — the same proof assistant used here.

---

## 2. Machine-verified general theorems (Lean, kernel-only, zero `sorry`)

`CollatzTheory.lean` type-checks under Lean 4.31.0 using **only** the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no Mathlib, no `native_decide`, no trust in
compiled code. These theorems hold for **all** parameters, not just tested ones:

| Theorem | Statement (informal) | Consequence |
|---|---|---|
| `step_growth_evenC`, `step_growth_evenA`, `orbit_diverges_evenC` | if `a` odd & `c` positive even (or `a ≥ 2` even & `c` odd), every odd start maps to a strictly larger odd number, forever: `iterN k n ≥ n + k` | excludes these opposite-parity cases; says nothing about the both-even case. The sweep focuses on odd×odd. |
| `scaling_step`, `scaling_orbit` | for odd `m`: `T_{a,mc}(m·n) = m·T_{a,c}(n)`, hence orbits of (a, mc) on mℤ are exactly m× orbits of (a, c) | `cycles(a, m·c) ⊇ m·cycles(a, c)`; classification reduces to primitive c |
| `absorb_entry`, `absorb_step`, `absorb_orbit` | if odd p divides both a and c, every orbit lands in pℤ after one odd step and never leaves | WLOG `gcd(a,c) = 1`; e.g. every (9,3) orbit is 3×an (9,1) orbit |
| `halve_iter`, `universal_cycle` | **if `a + 1 = 2^k`, then for every odd `c`: `T^{k+1}(c) = c`** | the Collatz cycle `{1,4,2}` generalizes: **every** system with a ∈ {3, 7, 15, 31, …} has the "trivial" cycle through c itself (`trivial_cycle_3/7/15` instantiate this with c universally quantified) |

The last theorem is the cleanest "general case" result of the study: the famous 1→4→2→1 loop is
not special to 3x+1 — it is the k=2 instance of a one-line theorem true for all c simultaneously,
and the sweep data shows it live in all 19 tested positive-c (3,c), (7,c), (15,c) systems.

## 3. Machine-verified certificates (Lean, generated from CUDA output)

`CollatzCerts.lean` (generated by `analyze.py`, checked by Lean) contains:

- **89 cycle certificates** — for every cycle found by the GPU, a kernel-checked (`decide`)
  proof that `iterN (T a c) len min = min`. These are unconditional theorems; `#print axioms`
  reports **no axioms at all** for them (the Lean kernel evaluates the orbit itself).
- **38 range certificates** (`native_decide`) — for every variant: *every* `n ∈ [1, 100000]
  either enters the certified cycle inventory or exceeds the u64 window τ within the fuel bound.
  Corollary: **the cycle inventories are complete** for cycles whose minimum is < 10^5 and whose
  elements stay below τ (τ = 2^62 for a ≤ 3, else ≈ 2^64/a). These use `native_decide`, i.e.
  they additionally trust Lean's compiler (`Lean.ofReduceBool`) — the standard trade-off for
  large finite checks; the theory file and cycle certificates do not.

## 4. CUDA sweeps (RTX 5090, sm_120 via compute_90 PTX JIT)

Per variant (a,c), two kernels (`collatz.cu`):

- **Pass A (inventory):** Brent cycle-detection on the accelerated odd→odd map
  `F(n) = (an+c) >> ctz(an+c)` from every odd start < 2^22, fuel 16384, escape window τ.
- **Pass B (classification):** every odd start < N (N = 2^32 for the 3x+c family, 2^30
  otherwise; 38,117,834,752 odd starts total in the committed output) iterated until it hits a certified cycle minimum, exceeds τ, or runs out
  of fuel (8192 accelerated steps). Aggregates: per-cycle basin counts, escapes, odd-steps,
  halvings, max excursion. Sampled window-escapees were re-run in exact Python
  big-integer arithmetic; **all a ≤ 3 samples reconverged** (e.g. n = 3,735,036,913 under 3x+15 exits the
  2^62 window and returns to the cycle with minimum 57). Fuel-outs: zero across all variants.

Whole grid: 38 variants, ≈ 38.12 × 10^9 odd starts, ≈ 10 seconds of recorded GPU time.
These are historical committed CUDA results, not a new GPU run on this machine.

## 5. Results

Full table: `results/summary.md`; raw JSON: `results/raw.jsonl`. Highlights (all inventories
below are certified in Lean; "conv." = fraction of odd starts converging within the window):

| a | c | N | cycles (odd minima) | conv. % | drift/odd-step meas. | pred. ln a − 2 ln 2 |
|---|---|---|---|---|---|---|
| 1 | 1 | 2^30 | {1} | 100 | −1.3863 | −1.3863 |
| 3 | −1 | 2^32 | {1}, {5,7}, {17,…} (3 cycles) | 100 | −0.3045 | −0.2877 |
| 3 | 1 | 2^32 | {1} | 100 | −0.2845 | −0.2877 |
| 3 | 5 | 2^32 | 6 cycles: 1, 5, 19, 23, 187, 347 | 100 | −0.2919 | −0.2877 |
| 3 | 13 | 2^32 | **10 cycles**: 1, 13, 131, 211, 227, 251, 259, 283, 287, 319 | 100 | −0.3013 | −0.2877 |
| 3 | 15 | 2^32 | 6 cycles = 3 × cycles(3,5) exactly | 100 | −0.2921 | −0.2877 |
| 5 | 1 | 2^30 | {1,3}, {13,33,83}, {17,43,27} | 0.085 | +0.2228 | +0.2231 |
| 5 | 3 | 2^30 | 7 cycles (five share signature k=3,H=7) | 0.075 | +0.2233 | +0.2231 |
| 7 | 1 | 2^30 | {1} (universal cycle) | 0.0001 | +0.5596 | +0.5596 |
| 9 | 1 | 2^30 | **none** | 0.0000 | +0.8109 | +0.8109 |
| 9 | 7 | 2^30 | {1} (because 2^4 − 9 = 7) | ~0 | +0.8109 | +0.8109 |
| 11 | 5 | 2^30 | {1} (because 2^4 − 11 = 5) | ~0 | +1.0116 | +1.0116 |
| 13 | 3 | 2^30 | {1} (because 2^4 − 13 = 3) | ~0 | +1.1787 | +1.1787 |
| 15 | 1..5 | 2^30 | {c} each (universal cycle) | ~0 | +1.3218 | +1.3218 |

Key facts:

- **Every a=3 variant converged for 100.0000% of ~2.1 billion odd starts each** (window escapes
  bignum-verified). Zero exceptions across c ∈ {−1, 1, 3, …, 19}.
- **Every a ≥ 5 variant escapes for ≈ 100% of starts**; the convergent fraction (0.36% at best,
  0 at worst) is the union of tiny cycle basins.
- (9,1), (9,3), (9,5), (9,9), (9,11), (11,1), (11,3), (13,1) have **empty inventories** — no
  positive cycle whose minimum is < 10^5 (Lean-certified) resp. < 2^22 (GPU), with all elements
  below ≈ 2^61. Even the orbit of 1 climbs beyond the window.

## 6. The general laws (the "general calculations")

### 6.1 Drift dichotomy — why a = 3 is the only hard multiplier

For a uniformly sampled odd residue and odd a,c, the halving exponent has limiting
distribution Pr(h=j)=2^-j and mean 2. Treating successive exponents like such samples
suggests the following drift for large values. This is a probabilistic model, not a
proved law for every individual orbit; measured aggregate means range from
1.9948 to 2.0263 in the committed grid. The model's log-drift per odd step is

```
δ(a) = ln a − 2 ln 2      δ(1) < 0,  δ(3) = ln(3/4) < 0,  δ(a≥5) > 0
```

The GPU measurements approximately match this for a ≥ 5 (maximum absolute
drift discrepancy about 0.000614 in the committed grid), and the mean
escape time matches quantitatively: exiting the window τ ≈ 2^61.2 from a mean start of 2^28.6
under (7,1) needs (61.2 − 28.6)·ln2/0.5596 ≈ 40 odd steps — measured k̄ = 41.39; for (5,1)
(61.7 − 28.6)·ln2/0.2228 ≈ 103 — measured 104.66.
For a = 3 the exact finite-orbit identity also contains the additive correction:
`H/k = log₂3 + (log₂ n_start − log₂ n_end)/k + (1/k) Σ_i log₂(1 + c/(3n_i))`,
where n_i are its odd members and all logarithms exist. Omitting this correction
gives only an approximation.

**Consequence:** the family splits into a *contracting* regime (a ≤ 3: everything should
converge — generalized Collatz/Belaga–Mignotte conjecture) and an *expanding* regime (a ≥ 5:
almost every orbit should diverge — generalized Crandall conjecture). Our data supports both at
scale 10^9–10^10 per variant.

### 6.2 The cycle equation — all 89 cycles obey one identity

A cycle with odd members n₀ → n₁ → … → n_{k−1} → n₀, halving hᵢ times after step i, satisfies
the exact identity (verified in exact arithmetic for all 89 discovered cycles):

```
n₀ · (2^H − a^k) = c · W,   W = Σ_{i=0}^{k−1} a^{k−1−i} · 2^{h₀+…+h_{i−1}},   H = Σ hᵢ
```

This single equation *organizes every inventory we found*:

- **k=1 (one odd step):** n·(2^h − a) = c. A 1-step cycle exists iff some 2^h − a divides c.
  - 2^h − a = 1 (i.e. a = 2^h − 1: a = 3, 7, 15): n = c — the **universal cycle**, provable for
    all c at once (`universal_cycle`, §2) and observed in all 19 positive-c variants.
  - 2^4 − 9 = 7, 2^4 − 11 = 5, 2^4 − 13 = 3: precisely the (9,7), (11,5), (13,3) systems — the
    *only* a ∈ {9,11,13} systems in the grid with any cycle at all, each with the predicted
    single fixed point n = 1. The empty inventories are the systems where no 2^h − a divides c.
- **Multiplets share a signature (k, H):** cycles come in families with the same (k,H) because
  the number of cycles with that signature is governed by how many parity-vectors make
  c·W ≡ 0 (mod 2^H − a^k):
  - (3,13): D = 2^8 − 3^5 = **13 = c** → a seven-cycle multiplet (211, 227, 251, 259, 283, 287, 319), all k=5, H=8.
  - (3,5) and (3,7): D = 2^5 − 3^3 = 5 and D = 2^4 − 3^2 = 7 equal to c → the 19/23-pair and the {5,11} cycle.
  - (5,c): D = 2^7 − 5^3 = **3** → every c divisible by 3 is cycle-rich: five (k=3,H=7)-cycles
    each for (5,3) and (5,9); and D = 2^5 − 5^2 = 7 gives the {7,21},{9,13} pair in (5,7).
  - The deep 3x+1 results are the same law run in reverse: Steiner/Simons–de Weger/Hercher
    bound how close 2^H/3^k can be to 1 (continued fractions of log₂3) to kill small k — here
    that appears as |D| exploding unless (k,H) hugs the line H/k = log₂a.
- **Scaling law live:** cycles(3,15) = 3 × cycles(3,5) element-by-element with identical
  signatures — the Lean `scaling_orbit` theorem realized in data.

### 6.3 The synthesis — status of the general case f(x) = ax + c

For a, c positive odd, gcd(a,c) = 1 (Lean theorems reduce everything else to this case):

| Claim | Status |
|---|---|
| a odd and c positive even, or a ≥ 2 even and c odd ⇒ every odd orbit diverges monotonically | **PROVED** (Lean, this repo); the both-even case is not included |
| a = 2^k − 1 ⇒ cycle through c exists for every odd c | **PROVED** (Lean, this repo) |
| scaling + gcd-absorption reductions | **PROVED** (Lean, this repo) |
| every specific cycle/inventory-completeness claim in §5 | **MACHINE-CERTIFIED** (Lean `decide` / `native_decide`) |
| cycle structure ⇔ arithmetic of 2^H − a^k (cycle equation) | **EXACT IDENTITY**, verified on all 89 cycles |
| a ≤ 3: every orbit eventually periodic ("generalized Collatz") | **OPEN** for a=3; finite evidence from 11 (3,c) variants and one (1,1) variant. Tao proves almost-bounded minima for (3,1), not almost-everywhere eventual periodicity |
| a ≥ 5: divergent orbits exist, convergence density 0 ("generalized Crandall") | **OPEN** (no single orbit provably divergent — this would itself be a breakthrough); supported at ≈100% escape rate over 10^9 starts × 25 variants |
| a uniform decision procedure for arbitrary residue-dependent affine maps | **IMPOSSIBLE** (Conway; Kurtz–Simon); this statement does not classify the narrower (a,c) family |

The structure proved here (under the explicit hypotheses in the Lean statements)
does not settle the remaining convergence and divergence questions. No equivalence
in difficulty between those family-wide questions and (3,1) has been proved here.
Finite inventories and reductions are evidence and intermediate results, not a
proof that a full solution is impossible.

## 6b. Addendum (2026-07-03): the universal cycle is an *iff*, and it transports

The Theorem-4 mechanism sharpened into one identity, Lean-proved (`CollatzTheory.lean` §5) and
machine-verified at scale (`universal.cu` + `verify_universal.py`): for odd c and all a, y

```
F_{a,c}(c·y) = c · F_{a,1}(y)        (accelerated map; the point c factors out)
⇒ F_{a,c}(c) = odd(a+1) · c          (master formula)
⇒ F_{a,c}(c) = c  ⇔  a = 2^k − 1     (converse of Thm 4: Mersenne is necessary)
⇒ F_{a,c}(x) = x  ⇔  x = c/d for a divisor d | c with a + d a power of 2
                                      (complete one-step cycle law)
⇒ every ax+1 cycle is a universal cycle family of ax+c, for EVERY odd c
```

Verified: rigidity + formula on all 2.75×10^11 odd pairs a,c < 2^20 (0 violations); census of all
1.37×10^11 (a,c,x) triples (a,c < 512, x < 2^22) finds 5477 fixed points, set-equal to the law's
predictions; the identity fuzzed on 2^33 random instances (0 violations); everything re-derived
exactly in Python at up to 350-digit parameters. The catalog sweep of all odd a < 2^24
**found 25** multipliers with a universal cycle through the seed c — the 24 Mersennes
(period 1, forced by the iff) and **a = 5** (period 2: {c, 3c}, transport of the 5x+1 cycle
{1,3}). The other 8,388,583 seed orbits escaped the finite window and are unresolved
by this experiment; zero fuel-outs does not imply zero unresolved orbits. This is not
a completeness proof for cycles through the seed.
Cycles not through 1 transport too: every 181x+c contains {27c, 611c}. Details: paper §4.1 and
§6.1; data in `results/universal.jsonl`, `results/universal_summary.md`.

## 6c. Addendum (2026-07-04): four further angles, machine-verified (`CollatzFrontier.lean`)

Continuing the program from angles the repo had not yet formalized. Each is proved in Lean for
**all** parameters (kernel-only; only the two counting certificates use `native_decide`), and
cross-checked in exact arithmetic by `verify_frontier.py`:

1. **Böhm–Sontacchi is now a theorem, not a data check.** §6.2's cycle equation was verified on
   the 89 discovered cycles; `orbit_formula` proves the underlying identity
   `F^n(x)·2^S = a^n·x + c·W` for every (a, c ≥ 1, x, n), giving the cycle equation
   (`cycle_equation`, and `cycle_equation_sub` — exactly Proposition 5 of the paper) for every
   cycle of every system. Corollary `cycle_expansion`: **every cycle satisfies 2^H > a^k** —
   cycles are forced above the drift line H/k = log₂a of §6.1, for all parameters at once.
2. **Repulsion (dual of absorption).** Absorption (§2) traps orbits in pℤ when p | a, p | c.
   `repel_orbit` proves the complement: if p | a but p ∤ c, every orbit is *expelled* from pℤ at
   its first odd step and never returns. Instance `collatz_avoids_3Z`: no Collatz iterate after
   the first odd step is divisible by 3. Together the two theorems settle the mod-p fate of
   every orbit for every p | a.
3. **Coset confinement.** From 2^h·F(x) = ax + c: every accelerated iterate lies in the coset
   c·⟨2⟩ (mod a) (`orbit_coset`). When ⟨2⟩ ⊊ (ℤ/a)ˣ this is a new constraint invisible to
   parity/divisibility: `sevenX1_iterates_mod7` proves every 7x+1 orbit occupies only the
   index-2 subgroup {1,2,4} mod 7 — and the committed (7,c) inventories obey it (checked:
   all cycle members of (7,5) are ≡ 5·{1,2,4}, of (7,11) ≡ 11·{1,2,4} mod 7).
4. **Finite Terras descent — the first density-of-all-integers statement in the repo.** For the
   shortcut map U, `U_affine` proves U^k(2^k·q + s) = 3^(wt k s)·q + U^k(s): the first k steps
   depend only on n mod 2^k. Calling a residue *good* when 3^(wt k s) < 2^k, `descent` proves
   every n ≥ 8^k in a good class dips below itself within k shortcut steps. The certified
   counts (`countGood_8/16/20`): **219/256, 58651/65536, 910596/1048576 (86.84%)** of residue
   classes are good at levels 8, 16, 20 — each count also equals the binomial tail
   Σ_{3^w<2^k} C(k,w), witnessing the Terras residue↔parity-vector bijection. Terras (1976)
   is the k → ∞ limit; unlike the range certificates (finitely many n), each finite level here
   quantifies over *all* n ≥ 8^k in the counted classes.

Scope: descent for selected starting values does not give full convergence.
However, descent for **every** n > 1 is equivalent to the original Collatz conjecture,
as now proved in `CollatzContradiction.lean`. These finite-level density results leave
uncovered starting values. Neither this gap nor the generalized undecidability theorem
establishes that closing the conjecture is impossible.

## 7. Reproduction

```
nvcc -O3 -gencode arch=compute_90,code=compute_90 collatz.cu -o collatz_gpu
./collatz_gpu > results/raw.jsonl        # ~10 s on an RTX 5090 (driver ≥ CUDA 12)
python3 analyze.py                       # bignum rechecks + asserts + generates CollatzCerts.lean
lean CollatzTheory.lean                  # general theorems  (Lean 4.31.0, no deps)
lean CollatzCerts.lean                   # 127 certificates  (a few minutes, native_decide)

nvcc -O3 -gencode arch=compute_90,code=compute_90 universal.cu -o universal_gpu
./universal_gpu > results/universal.jsonl   # universal-cycle laws S1-S4, ~2 s
python3 verify_universal.py                 # exact big-integer layer V1-V8

lean CollatzFrontier.lean                   # frontier theorems §6c (kernel + 2 native_decide counts)
python3 verify_frontier.py                  # exact big-integer layer F1-F5
```

Sources: [Barina 2025](https://link.springer.com/article/10.1007/s11227-025-07337-0) ·
[Hercher 2023](https://arxiv.org/abs/2201.00406) ·
[Belaga–Mignotte 1998](https://projecteuclid.org/journals/experimental-mathematics/volume-7/issue-2/Embedding-the-3x1-conjecture-in-a-3xd-context/em/1048515662.pdf) ·
[Barina's project page](https://pcbarina.fit.vutbr.cz/) ·
[ccchallenge.org](https://ccchallenge.org/)
