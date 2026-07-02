<div align="justify">

# The Collatz map inside its family: machine-verified structure of $f(x)=ax+c$

### GPU-scale certified dynamics, a universal-cycle law characterizing $a=2^k-1$, and the arithmetic $2^H-a^k$ that organizes every cycle

**J. Naude**, with derivations, engines, and analyses produced in human–AI collaboration (Claude, Anthropic; see the repository commit trailers). Computational artifacts, datasets, and machine proofs accompany this paper: the CUDA engine [`collatz.cu`](collatz.cu), the Lean 4 developments [`CollatzTheory.lean`](CollatzTheory.lean) and [`CollatzCerts.lean`](CollatzCerts.lean), the exact-arithmetic cross-checker [`analyze.py`](analyze.py), and the raw sweep data in [`results/`](results/).

*Working paper, revision of 2026-07-03. The Collatz conjecture is **open**; nothing here proves or disproves it, and §10 argues that no route of this kind can. The contribution is a machine-verified structural account of the two-parameter family containing it: every theorem is checked by the Lean 4 kernel, every finite claim is certified, and every empirical law is measured on $\approx 3.76\times10^{10}$ GPU-computed orbits.*

---

## Abstract

For odd $a,c$ we study the generalized Collatz map
$$
T_{a,c}(n)=\begin{cases} a\,n+c & n \text{ odd},\\[2pt] n/2 & n \text{ even},\end{cases}
$$
the classical conjecture being the case $(a,c)=(3,1)$. We combine a CUDA sweep of $38$ parameter pairs — every odd start below $2^{32}$ for the $3x+c$ family and below $2^{30}$ otherwise, $\approx 3.76\times 10^{10}$ orbits in about $7$ seconds on one RTX 5090 — with a Lean 4 development in which (i) the structural theorems are proved for *all* parameters with kernel-only proofs and no extra axioms, and (ii) the sweep's finite claims are exported as $127$ machine-checked certificates ($89$ cycle certificates, axiom-free by kernel evaluation; $38$ range-classification certificates via `native_decide`). A second engine (`universal.cu`) verifies the sharpened universal-cycle laws of §4.1 on a further $\approx4.1\times10^{11}$ instances with zero violations, and `verify_universal.py` re-derives them in exact arithmetic up to $350$-digit parameters.

The verified structure is: **(1)** if $a$ or $c$ is even, every odd start diverges monotonically, so the family is dynamically interesting only for $a,c$ odd; **(2)** for odd $m$, $T_{a,mc}(mn)=m\,T_{a,c}(n)$, so cycle sets scale, and a common odd prime factor of $a$ and $c$ traps all orbits in $p\mathbb{Z}$ — reducing the classification to $\gcd(a,c)=1$; **(3)** if $a=2^k-1$ then for *every* odd $c$ the point $c$ itself is periodic, $T^{\,k+1}(c)=c$: the famous loop $1\to4\to2\to1$ is the $k=2$ instance of a one-line theorem. Sharpened (§4.1): the accelerated map $F$ satisfies $F_{a,c}(c)=\mathrm{odd}(a{+}1)\cdot c$, so the universal fixed point at $c$ *characterizes* $a=2^k-1$; the fixed points of any $(a,c)$ are exactly $x=c/d$ for divisors $d\mid c$ with $a+d$ a power of two; and the master identity $F_{a,c}(cy)=c\,F_{a,1}(y)$ transports every $ax+1$ cycle into every $ax+c$ — a sweep of all odd $a<2^{24}$ finds exactly $25$ multipliers with a universal cycle through $c$: the $24$ Mersenne numbers (period $1$) and $a=5$ (period $2$, the family $\{c,3c\}$). Empirically, the halving count after an odd step has mean $2$ (measured $2.0000$–$2.0009$ on escape-dominated ensembles), giving per-odd-step drift $\delta(a)=\ln a-2\ln 2$, which the sweep reproduces to four decimals for every $a\ge5$ together with the implied mean escape times. Consequently the family splits into a contracting regime — all twelve $3x+c$ systems tested converge for $100.0000\%$ of $\approx 2.1\times10^9$ odd starts each — and an expanding regime, where convergence density is $\le 0.36\%$ and often exactly the cycle basins. Every one of the $89$ cycles found satisfies the exact identity $n_0(2^H-a^k)=c\,W$ with $W=\sum_i a^{k-1-i}2^{h_0+\cdots+h_{i-1}}$, and the inventories are organized by the divisors of $D=2^H-a^k$: one-step cycles exist iff $(2^h-a)\mid c$, which simultaneously explains the universal cycles ($D=1$), the isolated fixed points of $(9,7)$, $(11,5)$, $(13,3)$ ($2^4-a=c$), the seven-cycle multiplet of $3x+13$ ($2^8-3^5=13$), and the emptiness of the $(9,1)$, $(11,1)$, $(13,1)$ inventories. We state the two conjectures this evidence supports and record why they — and by Conway-type undecidability, the general family — remain beyond computational and elementary methods.

---

## 1. Introduction

### 1.1 The conjecture and its family

The Collatz (3x+1) conjecture asserts that iterating $T_{3,1}$ from any positive integer reaches the cycle $1\to4\to2\to1$. It has been verified for all $n<2^{71}$ (Barina 2020, 2025) and holds for "almost all" orbits in the strong sense of Tao (2019), yet remains open. We embed it in the two-parameter family $T_{a,c}$ above, asking what *can* be settled about the family as a whole — by proof, by machine-checked certificate, and by exhaustive measurement — and where exactly the residual hardness lives.

Two classical facts calibrate the ambition. First, the base case is open despite half a century of effort; the strongest general results are density statements (Terras 1976; Everett 1977; Korec 1994; Tao 2019). Second, Conway (1972) showed that generalized Collatz-type functions simulate arbitrary computation, and Kurtz–Simon (2007) made the generalized problem $\Pi^0_2$-complete: **no uniform decision procedure for the family exists.** "Solving the general case" can therefore only mean: prove every structural theorem that is provable, certify every finite claim, and reduce the remainder to sharply-stated conjectures with quantitative evidence. That is the shape of this paper.

### 1.2 Contribution

1. **Machine-verified general theorems** (§4): parity reduction, scaling conjugacy, prime absorption, and a universal-cycle theorem for $a=2^k-1$ — sharpened in §4.1 to an iff, with a complete one-step-cycle law and a transport principle for cycles — each proved in Lean 4.31 with kernel-only proofs, no Mathlib, no `native_decide`, quantified over all parameters.
2. **A certified computational pipeline** (§5): a two-pass CUDA engine (cycle inventory by Brent detection; mass classification of every odd start) whose output is cross-checked in exact big-integer arithmetic and *re-proved* as $127$ Lean certificates (§5.3). The GPU finds; the proof assistant certifies.
3. **Quantitative laws** (§6–§8): the drift dichotomy $\delta(a)=\ln a-2\ln2$ measured to four decimals; the cycle equation verified exactly on all discovered cycles; the signature/divisor mechanism $D=2^H-a^k$ that predicts which $(a,c)$ have rich, sparse, or empty cycle inventories.
4. **An honest synthesis** (§9–§10): the two open conjectures the data supports, and a precise account of why this route — any computational route — cannot close them.

## 2. Related work

Terras (1976) and Everett (1977) proved almost every $n$ has finite stopping time; Korec (1994) lowered the a.e. dip to $n^{\theta}$, $\theta=\ln3/\ln4\approx0.7925$. Tao (2019) proved almost all Collatz orbits attain almost bounded values (logarithmic density). Computational verification reached $2^{68}$ (Barina 2020) and $2^{71}$ (Barina 2025), which also feeds cycle bounds: Steiner (1977) excluded 1-circuits; Simons–de Weger (2005) excluded $m$-cycles for $m\le68$; Hercher (2023) for $m\le91$, so any nontrivial $(3,1)$-cycle has length exceeding $\approx10^{11}$. Lagarias (1985, 2010) surveys the field; Lagarias (1990) identified integer cycles of $3x+d$ with rational cycles of $3x+1$. Belaga–Mignotte (1998, 2000) catalogued the primitive cycles of $3x+d$ for $d<20000$ and conjectured every such orbit is eventually periodic. Crandall (1978) formulated the $qx+1$ problem and conjectured divergent orbits exist for $q\ge5$. Conway (1972; FRACTRAN 1987) and Kurtz–Simon (2007) supply the undecidability ceiling. The cycle identity of §7 is classical (Böhm–Sontacchi 1978). A community effort to formalize the Collatz literature in Lean is underway at ccchallenge.org; the present development is independent but uses the same proof assistant.

## 3. Notation

For odd $n$, one *odd step* $n\mapsto an+c$ is followed by $h=\nu_2(an+c)\ge1$ halvings ($a,c$ odd makes $an+c$ even); the *accelerated map* is
$$
F(n)=\frac{a\,n+c}{2^{\nu_2(a n+c)}},
$$
an odd-to-odd map. A cycle with $k$ odd members $n_0,\dots,n_{k-1}$ and halving exponents $h_0,\dots,h_{k-1}$ has *signature* $(k,H)$, $H=\sum h_i$, and length $k+H$ as a $T$-cycle. Computations classify odd iterates against a *window* $\tau$: $\tau=2^{62}$ for $a\le3$ and $\tau=\lfloor(2^{64}-1024)/a\rfloor$ otherwise, chosen so $an+c$ never overflows 64-bit arithmetic. An orbit *escapes* when an odd iterate exceeds $\tau$; even peaks may lawfully exceed $\tau$ without escaping. The one negative constant swept, $c=-1$, is the classical $3x-1$ system (equivalently, Collatz on the negative integers).

## 4. Machine-verified structural theorems

All results in this section are proved in [`CollatzTheory.lean`](CollatzTheory.lean) for **all** parameters (not merely tested values), type-checked by the Lean 4.31 kernel. `#print axioms` reports only the standard `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, no Mathlib, and no compiled-code trust. Proof sketches follow the formal proofs.

**Theorem 1 (parity reduction).** *Let $n$ be odd and positive. If $a$ is odd and $c$ even ($c>0$), or $a$ is even ($a\ge2$) and $c$ odd, then $T_{a,c}(n)$ is odd and $T_{a,c}(n)>n$; consequently the orbit is strictly increasing forever:*
$$
T^{\,j}_{a,c}(n)\ \ge\ n+j \qquad (j\ge0).
$$
*(Lean: `step_growth_evenC`, `step_growth_evenA`, `orbit_diverges_evenC`.)*

*Proof.* $an$ has the parity of $a\cdot n$; in both hypothesis regimes $an+c$ is odd, and $an+c>n$ since $a\ge1,c>0$ resp. $a\ge2$. The even branch is never taken, so growth iterates. $\square$

Thus the family is dynamically nontrivial **only for $a,c$ both odd**, which fixes the sweep grid.

**Theorem 2 (scaling conjugacy).** *For odd $m$ and all $a,c,n,j$:*
$$
T_{a,\,mc}(m\,n)=m\;T_{a,c}(n), \qquad T^{\,j}_{a,\,mc}(m\,n)=m\;T^{\,j}_{a,c}(n).
$$
*(Lean: `scaling_step`, `scaling_orbit`.) In particular $m\cdot\mathrm{Cycles}(a,c)\subseteq\mathrm{Cycles}(a,mc)$.*

*Proof.* $mn$ has the parity of $n$; on the odd branch $a(mn)+mc=m(an+c)$, on the even branch $(mn)/2=m(n/2)$. Induct. $\square$

**Theorem 3 (prime absorption).** *If an odd $p$ divides both $a$ and $c$, then $p\mid T_{a,c}(n)$ for every odd $n$, and $p\mid n$ implies $p\mid T_{a,c}(n)$ unconditionally; hence after one odd step every orbit lies in $p\mathbb{Z}$ forever. (Lean: `absorb_entry`, `absorb_step`, `absorb_orbit`.)*

With Theorem 2 this reduces the classification to $\gcd(a,c)=1$: e.g. every $(9,3)$-orbit is $3\times$ a $(9,1)$-orbit after its first odd step.

**Theorem 4 (universal trivial cycle).** *Let $a+1=2^k$ (i.e. $a=3,7,15,31,\dots$). Then for* every *odd $c$,*
$$
T^{\,k+1}_{a,c}(c)=c,
$$
*realized as $c\ \mapsto\ (a+1)c=2^k c\ \mapsto\ \cdots\ \mapsto\ c$. (Lean: `halve_iter`, `universal_cycle`, instantiated as `trivial_cycle_3/7/15` with $c$ universally quantified.)*

*Proof.* $c$ odd gives $T(c)=ac+c=(a+1)c=2^kc$; then $k$ even steps halve $2^kc$ back to $c$. $\square$

The Collatz loop $\{1,4,2\}$ is the $k=2$, $c=1$ instance; the theorem asserts its analogue in *every* $3x+c$, $7x+c$, $15x+c$ system simultaneously, and the sweep observes it in all $21$ such variants (§6).

### 4.1 The universal cycle, sharpened: formula, converse, classification, transport

Sketching the sweep of Theorem 4 exposed a stronger mechanism, which one identity carries entirely. Write $\mathrm{odd}(n)=n/2^{\nu_2(n)}$ for the odd part, so the accelerated map of §3 is $F_{a,c}(x)=\mathrm{odd}(ax+c)$. For **odd $c$** and *all* $a,y$:

$$
\boxed{\;F_{a,c}(c\,y)\;=\;c\cdot F_{a,1}(y)\;}
\qquad\text{in particular}\qquad
F_{a,c}(c)\;=\;\frac{a+1}{2^{\nu_2(a+1)}}\;c\;=\;\mathrm{odd}(a+1)\cdot c .
$$

The proof is the observation itself: $a(cy)+c=c\,(ay+1)$, and an odd factor passes through the odd part — the point $c$ *factors out of its own orbit*. Everything below is this identity read three ways, each Lean-proved for all parameters (kernel-only, as in §4).

**Theorem 4b (master formula and Mersenne rigidity).** *For every odd $c$ and every $a$: $F_{a,c}(c)=\mathrm{odd}(a+1)\cdot c$. Consequently*
$$
F_{a,c}(c)=c \;\iff\; \mathrm{odd}(a+1)=1 \;\iff\; a=2^k-1 ,
$$
*so the sufficient condition of Theorem 4 is also necessary — and already for a single odd $c$, hence simultaneously for all of them. (Lean: `F_formula`, `universal_fixed_iff`, `F_universal_cycle`; T-form `generalized_universal_step`: if $a+1=2^k m$, $m$ odd, then $T^{\,k+1}(c)=mc$.)*

**Theorem 4c (one-step cycle law).** *For odd $c$: $x$ is a fixed point of $F_{a,c}$ iff $d\,x=c$ and $a+d=2^k$ for some divisor $d$ of $c$ — fixed points correspond exactly to the divisors $d\mid c$ with $a+d$ a power of two, via $x=c/d$ — and every such $x$ is a genuine $T$-cycle of length $k+1$. (Lean: `fix_classification`, `F_fix_realizes_T`.)*

The two $k{=}1$ rows of Table 2 are the extreme divisors, now theorems rather than observations: $d=1$ forces $a$ Mersenne and gives the universal fixed point $x=c$; $d=c$ forces $a+c\in2^{\mathbb N}$ and gives the isolated fixed point $x=1$ of $(9,7),(11,5),(13,3)$. The law also *proves* the eight empty inventories of §6 have no one-step cycles: none of those $(a,c)$ admits a divisor $d\mid c$ with $a+d$ a power of two.

**Theorem 4d (orbit transport: universal cycle families).** *For odd $c$ and all $a,y,n$:*
$$
F^{\,n}_{a,c}(c\,y)=c\cdot F^{\,n}_{a,1}(y),
\qquad\text{and}\qquad
F^{\,n}_{a,c}(cy)=cy \iff F^{\,n}_{a,1}(y)=y .
$$
*The $ax+1$ system embeds in every $ax+c$ system, rescaled by $c$, and periodicity transports in both directions. (Lean: `F_scaling` — proved in the general form $F_{a,\,de}(du)=d\,F_{a,e}(u)$ for odd $d$ — `F_orbit_scaling`, `F_periodic_transport`.)*

Theorem 4d reframes Theorem 4: the universal cycle at $c$ is the transported trivial fixed point of $ax+1$, and **every** cycle of $ax+1$ is a *universal cycle family* of the whole column $\{(a,c):c \text{ odd}\}$. Two consequences the original theorem could not see:

- $a=5$ is not Mersenne, yet every $5x+c$ system has the two-cycle $\{c,3c\}$ — the transport of the $5x+1$ cycle $\{1,3\}$ (Lean: `five_universal_two_cycle`);
- every $181x+c$ system has the two-cycle $\{27c,\,611c\}$ — the transport of the classical $181x+1$ cycle $\{27,611\}$, a cycle *not through* $1$ (Lean: `oneEightyOne_universal_two_cycle`).

It also poses a sharp finite question: *which multipliers have a universal cycle through the seed $c$ itself?* By Theorem 4d that set is exactly $\{a : 1\text{ is periodic under } F_{a,1}\}$, which §6.1 sweeps to $2^{24}$.

## 5. Computational methodology

### 5.1 CUDA engine

`collatz.cu` runs two kernels per variant on an NVIDIA RTX 5090 (Blackwell, `sm_120`, driver CUDA 13.2; compiled as `compute_90` PTX and JIT-compiled by the driver, since the installed `nvcc` 12.0 predates the architecture):

- **Pass A — inventory.** Brent cycle detection on the accelerated map $F$ from every odd start $<2^{22}$ (fuel $2^{14}$ accelerated steps, window $\tau$). Detected cycles are canonicalized by their odd minimum; $(k,H)$, the cycle maximum, and members are recomputed on the host.
- **Pass B — classification.** Every odd start $<N$ ($N=2^{32}$ for the $3x+c$ family, $2^{30}$ otherwise) is iterated (fuel $8192$) until its odd value hits an inventory minimum (basin attribution), exceeds $\tau$ (escape), or fuel exhausts. Aggregates per variant: per-cycle basin counts, escape count, total odd steps, total halvings, maximum excursion; per-thread tallies are reduced through shared memory. Grid total: $38$ variants, $\approx3.76\times10^{10}$ orbits, $\approx7$ s of GPU time.

A second engine, [`universal.cu`](universal.cu), verifies the §4.1 theorems at scale (RTX 5090, run of 2026-07-03; raw output `results/universal.jsonl`):

- **S1 — rigidity grid.** All $2.75\times10^{11}$ odd pairs $(a,c)$, $a,c<2^{20}$: the master formula $F_{a,c}(c)=\mathrm{odd}(a{+}1)\,c$ and the Mersenne iff hold with **zero** violations; the fixed-point count is exactly $20\cdot 2^{19}$ ($20$ Mersenne $a$ below $2^{20}$ times $2^{19}$ odd $c$) — $1.0$ s.
- **S2 — fixed-point census.** All $1.37\times10^{11}$ triples ($a,c<512$, $x<2^{22}$): brute enumeration finds $5477$ fixed points; the set coincides *exactly* with the divisor-law prediction of Theorem 4c, enumerated independently on the host — $0.5$ s.
- **S3 — universal-family catalog.** Every odd $a<2^{24}$: is $1$ periodic under $F_{a,1}$? (§6.1.)
- **S4 — identity fuzz.** $2^{33}$ pseudorandom instances of $F_{a,\,de}(du)=d\,F_{a,e}(u)$ ($d,e$ odd, $a,u$ arbitrary): zero violations.

[`verify_universal.py`](verify_universal.py) then re-derives every S1–S4 claim in exact big-integer arithmetic (V1–V8): set-level equality of the census with the law, exact re-iteration of the whole catalog with the $n_0=1$ cycle equation, and stress instances of the formula, rigidity, transport, and one-step law at $80$–$350$-digit parameters. All pass (`results/universal_verify.log`).

### 5.2 Exact-arithmetic cross-checks

`analyze.py` re-runs, in Python big-integer arithmetic (no windows, no overflow), every sampled orbit that left the u64 window or exhausted fuel. Fuel-outs: zero across all variants. **Every sampled window-escapee of the $a\le3$ systems reconverges** — e.g. $n=3{,}735{,}036{,}913$ under $3x+15$ exits the $2^{62}$ window and returns to the cycle with minimum $57$. The script further asserts the literature anchors ($3x+1\Rightarrow\{1\}$; $3x-1\Rightarrow\{1,5,17\}$; $5x+1\Rightarrow\{1,13,17\}$; $3x+5\supseteq\{1,5,19,23\}$), the scaling identities of Theorem 2 on the data ($\mathrm{mins}(3,15)=3\cdot\mathrm{mins}(3,5)$ elementwise, etc.), and the cycle equation of §7 exactly on all $89$ cycles.

### 5.3 Lean certificates

`analyze.py` exports the sweep's finite claims to [`CollatzCerts.lean`](CollatzCerts.lean):

- **89 cycle certificates** — for each discovered cycle, `iterN (T a c) len min = min`, proved by kernel `decide`: the Lean kernel itself evaluates the orbit. `#print axioms` reports **no axioms whatsoever** for these.
- **38 range certificates** — for each variant, *every* $n\in[1,10^5]$ either reaches the certified inventory or exceeds $\tau$ within the fuel bound (`native_decide`, which additionally trusts Lean's compiler via `Lean.ofReduceBool` — the standard trade-off for large finite checks). Corollary: **inventory completeness** below the window — any missed cycle must have minimum $>10^5$ (indeed $>2^{22}$ by Pass A) or an odd element above $\tau$.

All $127$ certificates check ($\approx6$ minutes; long cycles need `maxRecDepth` raised, as `decide` unfolds roughly ten elaborator frames per step).

## 6. Results

Table 1 condenses `results/summary.md` (full raw data: `results/raw.jsonl`). "conv." is the fraction of odd starts below $N$ that reach the certified inventory inside the window; for $a=3$ the window escapees were individually re-verified to reconverge (§5.2), making the convergence rows exact.

| $a$ | $c$ | $N$ | cycles (odd minima) | conv. % | drift meas. | drift pred. |
|----:|----:|:---:|:--------------------|--------:|------------:|------------:|
| 1 | 1 | $2^{30}$ | $\{1\}$ | 100 | $-1.3863$ | $-1.3863$ |
| 3 | $-1$ | $2^{32}$ | 3: $1,\,5,\,17$ | 100 | $-0.3045$ | $-0.2877$ |
| 3 | 1 | $2^{32}$ | 1: $\{1\}$ | 100 | $-0.2845$ | $-0.2877$ |
| 3 | 3 | $2^{32}$ | 1: $\{3\}$ | 100 | $-0.2843$ | $-0.2877$ |
| 3 | 5 | $2^{32}$ | 6: $1,5,19,23,187,347$ | 100 | $-0.2919$ | $-0.2877$ |
| 3 | 7 | $2^{32}$ | 2: $5,7$ | 100 | $-0.3059$ | $-0.2877$ |
| 3 | 9 | $2^{32}$ | 1: $\{9\}$ | 100 | $-0.2841$ | $-0.2877$ |
| 3 | 11 | $2^{32}$ | 3: $1,11,13$ | 100 | $-0.2994$ | $-0.2877$ |
| 3 | 13 | $2^{32}$ | 10: $1,13,131,211,227,251,259,283,287,319$ | 100 | $-0.3013$ | $-0.2877$ |
| 3 | 15 | $2^{32}$ | 6: $3,15,57,69,561,1041$ | 100 | $-0.2921$ | $-0.2877$ |
| 3 | 17 | $2^{32}$ | 3: $1,17,23$ | 100 | $-0.2996$ | $-0.2877$ |
| 3 | 19 | $2^{32}$ | 2: $5,19$ | 100 | $-0.3037$ | $-0.2877$ |
| 5 | 1 | $2^{30}$ | 3: $1,13,17$ | 0.0851 | $+0.2228$ | $+0.2231$ |
| 5 | 3 | $2^{30}$ | 7: $1,3,39,43,51,53,61$ | 0.0749 | $+0.2233$ | $+0.2231$ |
| 5 | 5 | $2^{30}$ | 3: $5,65,85$ | 0.1489 | $+0.2225$ | $+0.2231$ |
| 5 | 7 | $2^{30}$ | 6: $1,7,9,57,91,119$ | 0.2877 | $+0.2228$ | $+0.2231$ |
| 5 | 9 | $2^{30}$ | 10: $1,3,9,29,89,117,129,153,159,183$ | 0.3594 | $+0.2232$ | $+0.2231$ |
| 5 | 11 | $2^{30}$ | 5: $1,11,141,143,187$ | 0.1474 | $+0.2228$ | $+0.2231$ |
| 7 | 1 | $2^{30}$ | 1: $\{1\}$ | 0.0001 | $+0.5596$ | $+0.5596$ |
| 7 | 3 | $2^{30}$ | 1: $\{3\}$ | 0.0001 | $+0.5596$ | $+0.5596$ |
| 7 | 5 | $2^{30}$ | 3: $3,5,27$ | 0.0012 | $+0.5596$ | $+0.5596$ |
| 7 | 7 | $2^{30}$ | 1: $\{7\}$ | 0.0004 | $+0.5596$ | $+0.5596$ |
| 7 | 9 | $2^{30}$ | 2: $1,9$ | 0.0001 | $+0.5596$ | $+0.5596$ |
| 7 | 11 | $2^{30}$ | 2: $11,23$ | 0.0009 | $+0.5596$ | $+0.5596$ |
| 9 | 1 | $2^{30}$ | **none** | 0.0000 | $+0.8109$ | $+0.8109$ |
| 9 | 3 | $2^{30}$ | **none** | 0.0000 | $+0.8109$ | $+0.8109$ |
| 9 | 5 | $2^{30}$ | **none** | 0.0000 | $+0.8109$ | $+0.8109$ |
| 9 | 7 | $2^{30}$ | 1: $\{1\}$ | $\sim0$ | $+0.8109$ | $+0.8109$ |
| 9 | 9 | $2^{30}$ | **none** | 0.0000 | $+0.8109$ | $+0.8109$ |
| 9 | 11 | $2^{30}$ | **none** | 0.0000 | $+0.8109$ | $+0.8109$ |
| 11 | 1 | $2^{30}$ | **none** | 0.0000 | $+1.0116$ | $+1.0116$ |
| 11 | 3 | $2^{30}$ | **none** | 0.0000 | $+1.0116$ | $+1.0116$ |
| 11 | 5 | $2^{30}$ | 1: $\{1\}$ | $\sim0$ | $+1.0116$ | $+1.0116$ |
| 13 | 1 | $2^{30}$ | **none** | 0.0000 | $+1.1787$ | $+1.1787$ |
| 13 | 3 | $2^{30}$ | 1: $\{1\}$ | $\sim0$ | $+1.1787$ | $+1.1787$ |
| 15 | 1 | $2^{30}$ | 1: $\{1\}$ | $\sim0$ | $+1.3218$ | $+1.3218$ |
| 15 | 3 | $2^{30}$ | 1: $\{3\}$ | $\sim0$ | $+1.3218$ | $+1.3218$ |
| 15 | 5 | $2^{30}$ | 1: $\{5\}$ | $\sim0$ | $+1.3218$ | $+1.3218$ |

**Table 1.** The 38-variant sweep. Drift is per odd step: measured $\ln a - (\text{halvings}/\text{odd steps})\ln2$ vs. predicted $\delta(a)=\ln a-2\ln2$ (§8).

Headlines: **(i)** every $a=3$ variant converged for $100.0000\%$ of its $\approx2.1\times10^{9}$ odd starts (window escapes bignum-verified); **(ii)** every $a\ge5$ variant escapes for essentially all starts, the convergent share being the union of tiny cycle basins; **(iii)** eight variants — $(9,1),(9,3),(9,5),(9,9),(9,11),(11,1),(11,3),(13,1)$ — have *empty* inventories: no positive cycle with minimum below $2^{22}$ (GPU) resp. certified below $10^5$ (Lean) and odd elements below $\tau\approx2^{61}$; even the orbit of $1$ climbs beyond the window; **(iv)** the universal cycle of Theorem 4 appears in all $21$ variants with $a\in\{3,7,15\}$, with signature $k=1$, $H=k_{2}$ where $a+1=2^{k_2}$ — and the catalog sweep of §6.1 shows the Mersennes and $a=5$ are the *only* multipliers below $2^{24}$ whose universal family passes through the seed $c$ itself; **(v)** $\mathrm{Cycles}(3,15)=3\cdot\mathrm{Cycles}(3,5)$ element-by-element with identical signatures — Theorem 2 live in data.

### 6.1 The universal-cycle catalog

Theorem 4d converts "which multipliers give a cycle through $c$ in *every* $ax+c$?" into a one-parameter question: for which odd $a$ is $1$ periodic under the $ax+1$ accelerated map? Pass S3 answers it for all $8{,}388{,}608$ odd $a<2^{24}$ (fuel $4096$ odd steps, values windowed at $\approx2^{64}/a$; **zero** fuel-outs, so every orbit either returned to $1$ or left the window — no undecided cases):

| verdict for the orbit of $1$ under $F_{a,1}$ | count | members |
|:---|---:|:---|
| periodic, period $1$ | $24$ | exactly $a=2^k-1$, $k=1,\dots,24$ — forced by Theorem 4b |
| periodic, period $2$ | $1$ | $a=5$: $1\to3\to1$, transporting to $\{c,3c\}$ in every $5x+c$ |
| escaped the $2^{64}/a$ window | $8{,}388{,}583$ | everything else |

**Table 1b.** The universal-cycle catalog for $a<2^{24}$. Every entry was re-iterated in exact big-integer arithmetic, satisfies the $n_0=1$ cycle equation $2^H-a^k=W$ (§7), and was re-verified as a live cycle of $F_{a,c}$ at $100$-digit $c$ (transport in action). Completeness caveat, stated honestly: an escaping orbit could in principle return to $1$ from above the window; the sweep excludes periodicity only within the $2^{64}/a$, $4096$-step bounds (drift $\delta(a)>0$ makes a return implausible, but that is §8 heuristics, not proof.)

The period-$2$ row is itself an arithmetic law. A two-cycle through $1$ must be $\{1,\ \mathrm{odd}(a{+}1)\}$, and it closes iff $a\cdot\mathrm{odd}(a+1)+1$ is a power of two ($a=5$: $5\cdot3+1=16$; Mersenne $a$ degenerate with $\mathrm{odd}(a{+}1)=1$). The sweep says no other $a<2^{24}$ manages this — or any longer return — inside the window. Note the catalog does **not** exhaust universal families: $a=181$'s orbit of $1$ escapes, yet $\{27c,611c\}$ is universal for the $181$-column by transport of the cycle $\{27,611\}$, which avoids $1$. The catalog enumerates families through the seed $c$; families through $c\,y$, $y>1$, correspond to the full cycle inventories of the $ax+1$ systems (e.g. $5x+1$'s $\{13,33,83\}$ and $\{17,43,27\}$ give $\{13c,33c,83c\}$ and $\{17c,43c,27c\}$ in every $5x+c$ — visible in Table 1 as the $c$-multiples populating the $a=5$ rows).

## 7. The cycle equation organizes every inventory

**Proposition 5 (cycle identity; classical, cf. Böhm–Sontacchi 1978).** *Let $n_0\to n_1\to\cdots\to n_{k-1}\to n_0$ be a cycle of the accelerated map with halving exponents $h_i$, $H=\sum h_i$. Then, exactly,*
$$
n_0\,\bigl(2^{H}-a^{k}\bigr)\;=\;c\,W,\qquad
W=\sum_{i=0}^{k-1} a^{\,k-1-i}\,2^{\,h_0+\cdots+h_{i-1}} .
$$

The identity was verified in exact arithmetic for all $89$ discovered cycles (`analyze.py`), which simultaneously cross-checks the GPU's $(k,H)$ bookkeeping. Its arithmetic content: writing $D=2^H-a^k$ for the *signature denominator*, integer cycles with signature $(k,H)$ exist iff $D$ divides $c\,W$ for some admissible parity vector, so inventories are governed by the divisors of $D$ — that is, by how well powers of $2$ approximate powers of $a$. Observed instances:

| mechanism | $D=2^H-a^k$ | consequence (observed) |
|:---|:---|:---|
| $k=1$, $2^h-a=1$ ($a=2^h-1$) | $D=1$ | universal cycle at $n=c$, all $21$ variants with $a\in\{3,7,15\}$ (Theorem 4; an **iff** by Theorem 4b) |
| $k=1$, $2^h-a=c$ | $D=c$ | fixed point $n=1$: exactly the systems $(9,7)$, $(11,5)$, $(13,3)$ via $2^4-a=c$ — the *only* $a\in\{9,11,13\}$ systems with any cycle (the $d=c$ case of Theorem 4c) |
| $k=1$, $(2^h-a)\nmid c$ for all $h$ | — | no one-step cycles — a theorem by 4c; combined with sparse higher signatures: the eight **empty** inventories of §6 |
| $(k,H)=(5,8)$, $a=3$ | $D=2^8-3^5=13$ | $c=13$: a seven-cycle multiplet $211,227,251,259,283,287,319$, all of signature $(5,8)$ |
| $(k,H)=(3,5)$, $a=3$ | $D=2^5-3^3=5$ | $c=5$: the cycle pair $19,23$ (and, scaled by $3$: $57,69$ in $c=15$) |
| $(k,H)=(2,4)$, $a=3$ | $D=2^4-3^2=7$ | $c=7$: the cycle $\{5,11\}$ |
| $(k,H)=(3,7)$, $a=5$ | $D=2^7-5^3=3$ | five signature-$(3,7)$ cycles each for $(5,3)$ and $(5,9)$; the classical pair $\{13,33,83\},\{17,43,27\}$ of $5x+1$ |
| $(k,H)=(2,5)$, $a=5$ | $D=2^5-5^2=7$ | one such cycle in *every* $5x+c$ swept; two for $c=7$ |

**Table 2.** Signature denominators explain rich, sparse, and empty inventories.

The deep $3x+1$ cycle results are this mechanism run in reverse: Steiner, Simons–de Weger, and Hercher bound how close $2^{H}/3^{k}$ can approach $1$ (continued fractions of $\log_2 3$, Baker-type bounds), forcing $|D|$ so large that small nontrivial cycles are impossible. In our data the same principle appears as: signatures cluster on the line $H/k\approx\log_2 a$, and inventories are nonempty exactly when the resulting $D$ has the right divisors relative to $c$.

## 8. The drift law, measured

After an odd step, the exponent $h=\nu_2(an+c)$ of a "random" orbit behaves geometrically with mean $2$ ($\Pr[h=j]=2^{-j}$), giving expected per-odd-step drift
$$
\delta(a)\;=\;\ln a-2\ln2:\qquad \delta(1),\delta(3)<0<\delta(5)\le\delta(7)\le\cdots
$$
The sweep measures $\text{halvings}/\text{odd steps}\in[1.9948,\,2.0263]$ across all $38$ variants, and exactly $2.0000$–$2.0009$ on escape-dominated ensembles; measured drift matches $\delta(a)$ to *four decimals* for every $a\ge5$ (Table 1). For the convergent $a=3$ family the small deviations are exactly the finite-orbit boundary term
$$
\frac{H_{\mathrm{tot}}}{k_{\mathrm{tot}}}\;=\;\log_2 3\;+\;\frac{\overline{\log_2 n_{\mathrm{start}}}-\overline{\log_2 n_{\mathrm{end}}}}{\bar k}.
$$
The law is also *kinetic*, not merely a sign: mean escape times obey $\bar k\approx(\log_2\tau-\overline{\log_2 n_0})\ln 2/\delta(a)$ — predicted $\approx103$ vs. measured $104.66$ odd steps for $(5,1)$, and $\approx40$ vs. $41.39$ for $(7,1)$.

**Consequence.** $a=3$ is the unique odd multiplier $>1$ with negative drift: the *only* member of the family that is both nontrivial and (heuristically) globally convergent. The family thus splits into a contracting regime $a\le3$ and an expanding regime $a\ge5$, and the data supports the split at $10^9$–$10^{10}$ starts per variant.

## 9. Synthesis: the status of the general case

For $a,c$ odd, positive, $\gcd(a,c)=1$ — Theorems 1–3 reduce everything else to this case:

| claim | status |
|:---|:---|
| $a$ or $c$ even $\Rightarrow$ monotone divergence of every odd orbit | **proved** (Thm 1, Lean) |
| $a=2^k-1$ $\Rightarrow$ cycle through $c$, for every odd $c$ | **proved** (Thm 4, Lean) |
| $F_{a,c}(c)=\mathrm{odd}(a{+}1)\,c$; fixed point at $c$ **iff** $a=2^k-1$ | **proved** (Thm 4b, Lean); zero violations on $2.75\times10^{11}$ pairs |
| one-step cycles $\leftrightarrow$ divisors $d\mid c$ with $a+d\in2^{\mathbb N}$ | **proved** (Thm 4c, Lean); census of $1.37\times10^{11}$ triples matches the law set-exactly |
| $ax+1$ cycles transport to every $ax+c$ (universal families) | **proved** (Thm 4d, Lean); catalog: exactly $25$ families through $c$ for $a<2^{24}$ (24 Mersennes + $a{=}5$) |
| scaling and absorption reductions | **proved** (Thms 2–3, Lean) |
| each cycle/inventory-completeness claim of §6 | **machine-certified** (89 `decide` + 38 `native_decide`) |
| cycle structure $\Leftrightarrow$ arithmetic of $2^H-a^k$ | exact identity, verified on all 89 cycles |
| **Conjecture A** (generalized Collatz; Belaga–Mignotte): $a\le3$ $\Rightarrow$ every orbit eventually periodic | **open**; supported at $100.0000\%$ over $\approx2.1\times10^9$ starts $\times$ 12 variants; "almost all" known for $(3,1)$ (Tao) |
| **Conjecture B** (generalized Crandall): $a\ge5$ $\Rightarrow$ divergent orbits exist and convergence density is $0$ | **open**; supported at $\approx100\%$ escape over 26 variants; *no single orbit* (e.g. $n=7$ under $5x+1$) is provably divergent |
| uniform decision procedure for the family | **impossible** (Conway; Kurtz–Simon, $\Pi^0_2$-complete) |

**Table 3.** What is proved, what is certified, what is open, what is impossible.

## 10. Why this route cannot close the conjecture — and what it did instead

Three separate walls, in increasing order of finality. **(1) Finite verification proves nothing asymptotic:** our $2^{32}$, like Barina's $2^{71}$, leaves the next integer unconstrained. **(2) The drift argument is probabilistic:** $\delta(3)<0$ says orbits contract *on average over parity vectors*; the conjecture quantifies over *every* orbit, and no ergodic statement excludes a measure-zero parity sequence conspiring forever. The best unconditional result — Tao's "almost all orbits attain almost bounded values" — is precisely the strongest sentence this kind of argument seems able to produce; the gap "almost all $\to$ all" *is* the conjecture. **(3) Undecidability:** by Conway and Kurtz–Simon, no theorem schema can uniformly settle the generalized family; hardness is not an artifact of technique.

What survives these walls is exactly what a compute-plus-proof pipeline can deliver, and did: the provable general structure of the family (Theorems 1–4), certified at the kernel level; complete certified cycle inventories below explicit bounds for $38$ systems; and two quantitative laws — drift $\delta(a)=\ln a-2\ln2$ and the signature mechanism $D=2^H-a^k$ — that turn the family's phenomenology (why $3x+13$ has ten cycles, why $9x+1$ has none, why $a=3$ alone converges) from folklore into measured, machine-checked fact. The Collatz conjecture, so embedded, stops looking like an isolated curiosity: it is the unique negative-drift member of a family whose cycles are governed by the Diophantine proximity of $2^H$ to $a^k$ — and both of its remaining questions are transcendence-hard.

## 11. Reproducibility

```text
nvcc -O3 -gencode arch=compute_90,code=compute_90 collatz.cu -o collatz_gpu
./collatz_gpu > results/raw.jsonl        # ~10 s on an RTX 5090
python3 analyze.py                       # exact rechecks + asserts + generates CollatzCerts.lean
lean CollatzTheory.lean                  # general theorems incl. §4.1 (Lean 4.31.0, no dependencies)
lean CollatzCerts.lean                   # 127 certificates (~6 min, native_decide)

nvcc -O3 -gencode arch=compute_90,code=compute_90 universal.cu -o universal_gpu
./universal_gpu > results/universal.jsonl   # S1-S4 theorem verification, ~2 s
python3 verify_universal.py                 # exact-arithmetic layer V1-V8 + catalog summary
```

Hardware: NVIDIA RTX 5090 (32 GB), driver 595.71.05 (CUDA 13.2), `nvcc` 12.0 via PTX JIT. All raw output, logs, and the generated certificate file are committed alongside this paper.

## References

1. D. Barina, *Convergence verification of the Collatz problem*, J. Supercomputing **77** (2020), 2681–2688; *Improved verification limit for the convergence of the Collatz conjecture*, J. Supercomputing (2025). Project: pcbarina.fit.vutbr.cz.
2. E. Belaga, M. Mignotte, *Embedding the 3x+1 conjecture in a 3x+d context*, Experiment. Math. **7** (1998), 145–151; *Cyclic structure of dynamical systems associated with 3x+d extensions of Collatz problem* (2000).
3. C. Böhm, G. Sontacchi, *On the existence of cycles of given length in integer sequences like $x_{n+1}=x_n/2$ if $x_n$ even, and $x_{n+1}=3x_n+1$ otherwise*, Atti Accad. Naz. Lincei **64** (1978), 260–264.
4. J. H. Conway, *Unpredictable iterations*, Proc. 1972 Number Theory Conf., Boulder, 49–52; *FRACTRAN: a simple universal programming language for arithmetic*, in Open Problems in Communication and Computation (1987).
5. R. E. Crandall, *On the "3x+1" problem*, Math. Comp. **32** (1978), 1281–1292.
6. C. J. Everett, *Iteration of the number-theoretic function $f(2n)=n$, $f(2n+1)=3n+2$*, Adv. Math. **25** (1977), 42–45.
7. C. Hercher, *There are no Collatz m-cycles with $m\le91$*, J. Integer Seq. **26** (2023), 23.3.5.
8. I. Korec, *A density estimate for the 3x+1 problem*, Math. Slovaca **44** (1994), 85–89.
9. S. A. Kurtz, J. Simon, *The undecidability of the generalized Collatz problem*, TAMC 2007, LNCS 4484, 542–553.
10. J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly **92** (1985), 3–23; *The set of rational cycles for the 3x+1 problem*, Acta Arith. **56** (1990), 33–53; (ed.) *The Ultimate Challenge: The 3x+1 Problem*, AMS, 2010.
11. J. Simons, B. de Weger, *Theoretical and computational bounds for m-cycles of the 3n+1 problem*, Acta Arith. **117** (2005), 51–70.
12. R. P. Steiner, *A theorem on the Syracuse problem*, Proc. 7th Manitoba Conf. Numer. Math. (1977), 553–559.
13. T. Tao, *Almost all orbits of the Collatz map attain almost bounded values*, Forum Math. Pi **10** (2022), e12 (arXiv:1909.03562, 2019).
14. R. Terras, *A stopping time problem on the positive integers*, Acta Arith. **30** (1976), 241–252.
15. The Collatz Conjecture Challenge (Lean formalization effort), ccchallenge.org.

</div>
