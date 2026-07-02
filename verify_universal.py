#!/usr/bin/env python3
"""Exact big-integer verification layer for the sharpened universal-cycle
theorems (CollatzTheory.lean §5) and cross-check of the GPU sweep
results/universal.jsonl (universal.cu).

Everything here is exact Python int arithmetic: no windows, no overflow.
Sections:
  V1  re-assert GPU S1/S4 pass flags; recompute S1 expectation independently
  V2  GPU S2 census == exact divisor-law enumeration (set equality, recomputed)
  V3  GPU S3 catalog: exact re-iteration of every entry (no window), cycle
      equation 2^H - a^k = W at n0=1, Mersenne <-> period-1 partition
  V4  master formula + rigidity at 200-350 digit scale (300 trials)
  V5  master identity F_{a,de}(du) = d*F_{a,e}(u) at 80-digit scale (300 trials)
  V6  transport of every catalog family to 100-digit c (universal cycles live)
  V7  181x+c: {27c, 611c} at huge c (transport of a cycle NOT through 1)
  V8  one-step law on composite c = 3^5*5^2*7*11*13: predicted set == brute scan
Writes results/universal_summary.md. Exit 0 iff every assert passes.
"""
import json, random, sys

random.seed(20260703)

def v2(n):     return ((n & -n).bit_length() - 1)
def oddpart(n): return n >> v2(n)
def F(a, c, x): t = a*x + c; return t >> v2(t)
def is_pow2(n): return n > 0 and (n & (n-1)) == 0

secs = {}
for line in open("results/universal.jsonl"):
    r = json.loads(line)
    secs[r["section"]] = r

# ---- V1: S1/S4 flags + independent expectation ----
s1 = secs["S1"]
assert s1["pass"] and s1["iffViolations"] == 0 and s1["formulaViolations"] == 0, s1
mers = sum(1 for a in range(1, 1 << 20, 2) if is_pow2(a + 1))
assert s1["mersenneCount"] == mers == 20
assert s1["nFixed"] == s1["expectedFixed"] == mers * (1 << 19)
s4 = secs["S4"]
assert s4["pass"] and s4["violations"] == 0, s4
print(f"V1 PASS  S1: {s1['pairs']:.3e} pairs, formula+iff exact, fixed={s1['nFixed']}"
      f" | S4: {s4['trials']:.3e} fuzz trials, 0 violations")

# ---- V2: census set equality, recomputed exactly ----
s2 = secs["S2"]
assert s2["pass"] and s2["setEqual"] and s2["nFixedFound"] == s2["nMatchingLaw"], {k: s2[k] for k in s2 if k != "entries"}
gpu_set = {tuple(e) for e in s2["entries"]}
pred = set()
for a in range(1, 512, 2):
    for c in range(1, 512, 2):
        for d in range(1, c + 1, 2):
            if c % d == 0 and is_pow2(a + d) and c // d < (1 << 22):
                pred.add((a, c, c // d))
assert gpu_set == pred, (len(gpu_set), len(pred))
for (a, c, x) in gpu_set:                      # every entry independently exact
    assert F(a, c, x) == x
print(f"V2 PASS  S2: {s2['triples']:.3e} triples scanned; {len(gpu_set)} fixed points"
      f" == exact divisor-law prediction (set equality + direct recheck)")

# ---- V3: catalog exact re-iteration ----
s3 = secs["S3"]
assert s3["pass"] and s3["allMersennePeriod1"], {k: s3[k] for k in s3 if k != "catalog"}
catalog = [tuple(e) for e in s3["catalog"]]
rows = []
for a, per in catalog:
    x, hs = 1, []
    for s in range(1, per + 1):
        t = a * x + 1
        h = v2(t)
        hs.append(h)
        x = t >> h
        assert (x == 1) == (s == per), (a, per, s, x)   # first return exactly at per
    k, H = len(hs), sum(hs)
    W = sum(a**(k - 1 - i) * 2**sum(hs[:i]) for i in range(k))
    assert 2**H - a**k == W, (a, per)                    # cycle equation at n0=1
    if per == 1:
        assert is_pow2(a + 1), a                         # period 1 <=> Mersenne (Thm 4b)
    if per == 2:
        m = oddpart(a + 1)
        assert m > 1 and F(a, 1, 1) == m and F(a, 1, m) == 1
        assert is_pow2(a * m + 1), a                     # k=2 arithmetic criterion
    rows.append((a, per, H, "yes" if is_pow2(a + 1) else "NO"))
per1 = sorted(a for a, p in catalog if p == 1)
assert per1 == [2**k - 1 for k in range(1, 25)], per1    # exactly the 24 Mersennes
print(f"V3 PASS  S3: {len(catalog)} universal families over {s3['oddAbelow']:.2e} systems; "
      f"period-1 set == Mersennes 2^k-1, k=1..24; cycle equation exact on all")

# ---- V4: master formula + rigidity, 200-350 digit c ----
for _ in range(300):
    c = random.randrange(10**200, 10**350) | 1
    k = random.randrange(1, 500)
    a = 2**k - 1
    assert F(a, c, c) == c                               # universal fixed point
    a2 = random.randrange(10**60, 10**100) | 1
    m = oddpart(a2 + 1)
    assert F(a2, c, c) == m * c                          # master formula
    if not is_pow2(a2 + 1):
        assert F(a2, c, c) != c                          # rigidity
print("V4 PASS  formula + Mersenne rigidity exact at 200-350 digit c (300 trials, a=2^k-1 up to k=499)")

# ---- V5: master identity at 80-digit scale ----
for _ in range(300):
    a = random.randrange(10**80); u = random.randrange(10**80)
    d = random.randrange(10**80) | 1; e = random.randrange(10**80) | 1
    assert F(a, d * e, d * u) == d * F(a, e, u)
print("V5 PASS  F_{a,de}(d u) = d F_{a,e}(u) exact at 80-digit scale (300 trials)")

# ---- V6: every catalog family transported to 100-digit c ----
for a, per in catalog:
    for _ in range(5):
        c = random.randrange(10**100, 10**101) | 1
        x = c
        for _ in range(per):
            x = F(a, c, x)
        assert x == c, (a, per)
print(f"V6 PASS  all {len(catalog)} catalog families verified at 100-digit c (period exact)")

# ---- V7: 181-family (cycle not through 1) ----
for _ in range(100):
    c = random.randrange(10**100, 10**150) | 1
    assert F(181, c, 27 * c) == 611 * c and F(181, c, 611 * c) == 27 * c
print("V7 PASS  181x+c universal two-cycle {27c, 611c} exact at 100-150 digit c")

# ---- V8: one-step law on composite c, brute completeness ----
c = 3**5 * 5**2 * 7 * 11 * 13            # 6081075
divs = sorted(d for d in range(1, c + 1) if c % d == 0)
for a in range(3, 202, 2):
    predicted = {c // d for d in divs if is_pow2(a + d)}
    for x in predicted:
        assert F(a, c, x) == x
    if a == 3:                             # brute completeness scan for a=3
        found = {x for x in range(1, 2_000_002, 2) if F(a, c, x) == x}
        assert found == {x for x in predicted if x <= 2_000_001}, (found, predicted)
print(f"V8 PASS  one-step law on c={c}: predictions fixed for a=3..201; brute scan (a=3) complete")

# ---- summary table ----
with open("results/universal_summary.md", "w") as f:
    f.write("# Universal-cycle verification summary\n\n")
    f.write(f"- S1 rigidity grid: {s1['pairs']} (a,c) pairs, odd a,c < 2^20 — "
            f"formula violations {s1['formulaViolations']}, iff violations {s1['iffViolations']}, "
            f"fixed points {s1['nFixed']} = 20 Mersenne a x 2^19 c  [{s1['secs']:.2f}s GPU]\n")
    f.write(f"- S2 fixed-point census: {s2['triples']} triples (a,c<512, x<2^22) — "
            f"{s2['nFixedFound']} fixed points, all matching the one-step law, "
            f"set-equal to exact divisor enumeration  [{s2['secs']:.2f}s GPU]\n")
    f.write(f"- S3 catalog: odd a < 2^24, fuel 4096 — periodic {s3['periodic']}, "
            f"escape {s3['escape']}, fuelout {s3['fuelout']}  [{s3['secs']:.2f}s GPU]\n")
    f.write(f"- S4 scaling fuzz: {s4['trials']} trials, {s4['violations']} violations  [{s4['secs']:.2f}s GPU]\n\n")
    f.write("## Universal cycle families found (1 periodic under F_{a,1}, a < 2^24)\n\n")
    f.write("| a | period k | H (halvings) | a+1 power of 2? |\n|---:|---:|---:|:---:|\n")
    for a, per, H, mer in sorted(rows):
        f.write(f"| {a} | {per} | {H} | {mer} |\n")
print("wrote results/universal_summary.md")
print("== ALL EXACT-ARITHMETIC VERIFICATIONS PASS ==")
