#!/usr/bin/env python3
"""Exact big-integer verification layer for the frontier theorems
(CollatzFrontier.lean) and cross-check against the committed sweep data.

Everything here is exact Python int arithmetic: no windows, no overflow.
Sections:
  F1  orbit formula  F^n(x)*2^S = a^n*x + c*W  (S,W by the Lean recursions),
      fuzzed over small, even-a, a=0, and 60-digit parameters
  F2  cycle equation (additive + subtractive) and the expansion corollary
      2^H > a^k re-verified on ALL cycles committed in results/raw.jsonl,
      with (k,H) recomputed from scratch
  F3  repulsion: p|a, p∤c  =>  no iterate divisible by p after first odd step
  F4  coset confinement: every F-iterate lies in c*<2> (mod a); the (7,c)
      inventories in raw.jsonl respect the index-2 subgroup constraint
  F5  finite Terras: U-affine identity fuzz, descent fuzz, and EXACT
      recomputation of the good-residue counts certified in Lean
      (countGood 8/16/20 = 219/58651/910596), plus the binomial identity
      that witnesses the Terras residue<->parity-vector bijection
Writes results/frontier_summary.md.  Exit 0 iff every assert passes."""
import json, random

random.seed(20260704)

v2 = lambda n: (n & -n).bit_length() - 1
def F(a, c, x): t = a*x + c; return t >> v2(t)
def Tmap(a, c, n): return a*n + c if n % 2 == 1 else n // 2

# ---- F1: orbit formula ----
def SW(a, c, x, n):
    """The Lean recursions: S(0)=0, S(n+1)=h0+S(n,Fx); W(0)=0, W(n+1)=a^n+2^h0*W(n,Fx)."""
    if n == 0: return 0, 0
    h0 = v2(a*x + c)
    S1, W1 = SW(a, c, F(a, c, x), n - 1)
    return h0 + S1, a**(n-1) + 2**h0 * W1

def iterF(a, c, x, n):
    for _ in range(n): x = F(a, c, x)
    return x

for _ in range(500):
    a = random.randrange(0, 10**6)                      # any a: even, zero, ...
    c = random.randrange(1, 10**6) | 1
    x = random.randrange(0, 10**6)
    n = random.randrange(0, 60)
    Sn, Wn = SW(a, c, x, n)
    assert iterF(a, c, x, n) * 2**Sn == a**n * x + c*Wn, (a, c, x, n)
for _ in range(20):
    a = random.randrange(10**50, 10**60); c = random.randrange(10**50, 10**60) | 1
    x = random.randrange(10**50, 10**60)
    Sn, Wn = SW(a, c, x, 15)
    assert iterF(a, c, x, 15) * 2**Sn == a**15 * x + c*Wn
print("F1 PASS  orbit formula exact on 500 random + 20 sixty-digit instances (incl. even a, a=0)")

# ---- F2: cycle equation on all committed cycles ----
rows = [json.loads(l) for l in open("results/raw.jsonl")]
ncyc = 0
for r in rows:
    a, c = r["a"], r["c"]
    if c < 0: continue                                   # Nat development: positive c
    for cy in r["cycles"]:
        n0 = cy["min"]; hs = []; x = n0
        while True:
            m = a*x + c; h = v2(m); hs.append(h); x = m >> h
            if x == n0: break
        k, H = len(hs), sum(hs)
        assert (k, H) == (cy["k"], cy["H"]), (a, c, n0)
        Sn, Wn = SW(a, c, n0, k)
        assert Sn == H
        assert n0 * 2**H == a**k * n0 + c*Wn             # additive cycle equation
        assert 2**H > a**k                               # expansion corollary
        assert n0 * (2**H - a**k) == c*Wn                # subtractive (Prop 5) form
        ncyc += 1
print(f"F2 PASS  cycle equation + 2^H > a^k exact on all {ncyc} committed positive-c cycles")

# ---- F3: repulsion ----
for _ in range(300):
    p = random.choice([2, 3, 5, 7, 11, 13, 101])
    a = p * random.randrange(1, 1000)
    c = random.randrange(1, 1000)
    if c % p == 0: c += 1
    n = 2*random.randrange(1, 10**6) + 1
    m = Tmap(a, c, n)
    for _ in range(200):
        assert m % p != 0, (p, a, c, n)
        m = Tmap(a, c, m)
print("F3 PASS  repulsion (p|a, p∤c ⇒ orbit leaves pZ forever) on 300 systems x 200 steps")

# ---- F4: coset confinement ----
for _ in range(200):
    a = random.randrange(3, 10**4) | 1
    c = random.randrange(1, 10**4) | 1
    x = random.randrange(1, 10**6) | 1
    for _ in range(50):
        x = F(a, c, x)
        assert any(x * pow(2, j, a) % a == c % a for j in range(70)), (a, c, x)
subgroup7 = {1, 2, 4}
for r in rows:
    if r["a"] != 7 or r["c"] < 0: continue
    c = r["c"]
    allowed = {c * g % 7 for g in subgroup7}
    for cy in r["cycles"]:
        for mem in cy["members"]:
            assert mem % 7 in allowed, (c, mem)
print("F4 PASS  coset confinement fuzzed on 200 systems; all committed (7,c) cycle members lie in c*<2> mod 7")

# ---- F5: finite Terras ----
def U(n): return (3*n + 1)//2 if n % 2 == 1 else n//2
def wt(k, s):
    w = 0
    for _ in range(k): w += s % 2; s = U(s)
    return w
def Uk(k, n):
    for _ in range(k): n = U(n)
    return n

for _ in range(500):
    k = random.randrange(0, 30); q = random.randrange(0, 10**9); s = random.randrange(0, 10**9)
    assert Uk(k, 2**k * q + s) == 3**wt(k, s) * q + Uk(k, s)
for _ in range(300):
    k = random.randrange(1, 22); s = random.randrange(0, 2**k)
    if 3**wt(k, s) >= 2**k: continue
    q = 4**k + random.randrange(0, 10**6)
    n = 2**k * q + s
    assert Uk(k, n) < n
print("F5a PASS  U-affine identity (500 fuzz) + descent theorem (300 fuzz) exact")

from math import comb
LEAN_CERTIFIED = {8: 219, 16: 58651, 20: 910596}
counts = {}
for k in (8, 16, 20):
    cnt = sum(1 for s in range(2**k) if 3**wt(k, s) < 2**k)
    wmax = max(w for w in range(k+1) if 3**w < 2**k)
    assert cnt == LEAN_CERTIFIED[k], (k, cnt)
    assert cnt == sum(comb(k, w) for w in range(wmax+1))   # Terras bijection witness
    counts[k] = (cnt, wmax)
print("F5b PASS  countGood(8,16,20) == Lean-certified 219/58651/910596 == binomial tails "
      "(residue<->parity-vector bijection witnessed)")

# ---- summary ----
with open("results/frontier_summary.md", "w") as f:
    f.write("# Frontier verification summary (CollatzFrontier.lean x verify_frontier.py)\n\n")
    f.write("| angle | Lean theorem(s) | exact-arithmetic cross-check |\n|---|---|---|\n")
    f.write("| Bohm-Sontacchi for all parameters | `orbit_formula`, `cycle_equation`, "
            "`cycle_equation_sub` | 520 fuzz instances incl. 60-digit params; "
            f"exact on all {ncyc} committed positive-c cycles |\n")
    f.write("| cycles above the drift line | `cycle_expansion` (2^H > a^k) | "
            f"holds on all {ncyc} committed cycles |\n")
    f.write("| repulsion (dual of absorption) | `repel_orbit`, `collatz_avoids_3Z` | "
            "300 systems x 200 steps, 0 violations |\n")
    f.write("| coset confinement mod a | `orbit_coset`, `sevenX1_iterates_mod7` | "
            "200 systems fuzzed; all committed (7,c) cycle members in c*<2> mod 7 |\n")
    f.write("| finite Terras descent | `U_affine`, `descent`, `descent_all`, "
            "`countGood_8/16/20` | 800 fuzz instances; counts recomputed exactly |\n\n")
    f.write("## Certified good-residue densities (descent within k shortcut steps, n >= 8^k)\n\n")
    f.write("| level k | good residues | of 2^k | density | max weight |\n|---:|---:|---:|---:|---:|\n")
    for k in (8, 16, 20):
        cnt, wmax = counts[k]
        f.write(f"| {k} | {cnt} | {2**k} | {cnt/2**k:.4%} | {wmax} |\n")
    f.write("\nDensity -> 1 as k -> infinity is Terras (1976); each finite level above is a\n")
    f.write("machine-certified theorem about ALL n >= 8^k in the counted classes.\n")
print("wrote results/frontier_summary.md")
print("== ALL FRONTIER EXACT-ARITHMETIC VERIFICATIONS PASS ==")
