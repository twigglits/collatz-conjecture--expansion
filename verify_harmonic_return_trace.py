"""Kernel arithmetic and exact finite checks for the harmonic trace argument.

The all-depth fusion tail and infinite harmonic estimates remain WRITTEN.
No external analytic theorem or external compiled library is used here.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/harmonic-return-trace"
SOURCES = ["CollatzAffine.lean", "CollatzPacking.lean", "lean/CoalescenceTail.lean",
           "lean/IntegerReturnCesaro.lean", "lean/HarmonicReturnTrace.lean"]
THEOREMS = ["bounded_hit_growth", "hitting_source_span", "dyadic_band_span",
            "nonfusion_antitone", "mask_repeated_periods", "earlier_mask_band",
            "nested_mask_band", "cycle_count_positive", "positive_count_coefficient",
            "cycle_ratio_cap"]
PRIOR = "results/count-return-clock/verification.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def path(n, t):
    states, counts = [n], [0]
    for _ in range(t):
        counts.append(counts[-1]+(states[-1] & 1))
        states.append(step(states[-1]))
    return states, counts


def inverse_layers(n, H):
    layer = {n: 0}
    yield layer
    for _ in range(H):
        nxt = {}
        for x, a in layer.items():
            assert 2*x not in nxt
            nxt[2*x] = a
            if x % 3 == 2:
                m = (2*x-1)//3
                assert m > 0 and m & 1 and step(m) == x and m not in nxt
                nxt[m] = a+1
        layer = nxt
        yield layer


def masks_and_bands(H, counter):
    masks = [[None]*(1 << t) for t in range(H+1)]
    for r in range(1 << H):
        xs, aa = path(r, H)
        ys, bb = path(r+1, H)
        last = 1
        for t in range(H+1):
            alive = int(not (xs[t] == ys[t] and aa[t] == bb[t]))
            assert alive <= last
            last = alive
            if r < (1 << t):
                masks[t][r] = alive
                counter["direct_residue_mask_values"] += 1
            if aa[t] > 0:
                assert 3**aa[t]*(3*r+1) <= 3*(1 << t)*xs[t]
                counter["positive_count_correction_bounds"] += 1
    assert all(v is not None for row in masks for v in row)
    q = [F(sum(row), len(row)) for row in masks]
    assert q[0] == 1
    for T in range(H+1):
        for j in range(11):
            population = sum(masks[T][m % (1 << T)] for m in range(1 << j, 1 << (j+1)))
            assert population <= (1 << j)*q[min(j, T)]
            mass = sum((F(masks[T][m % (1 << T)], m)
                        for m in range(1 << j, 1 << (j+1))), F(0))
            assert mass <= q[min(j, T)]
            counter["nested_binary_band_population_checks"] += 1
            counter["exact_harmonic_binary_band_checks"] += 1
    for T in range(1, 10):
        prefix = [F(0)]
        for m in range(1, 1025):
            prefix.append(prefix[-1]+F(masks[T][m % (1 << T)], m))
        for a in (1, 2, 3, 7, 15, 16, 31, 32, 63, 64, 127, 128, 255, 511):
            for length in (1, 2, 7, 31, 63, 255, 512):
                b = a+length-1
                if b > 1024:
                    continue
                j, k = a.bit_length()-1, b.bit_length()-1
                exact = prefix[b]-prefix[a-1]
                band_cap = sum(q[min(i, T)] for i in range(j, k+1))
                coarse = sum(q[:T])+(k-j+1)*q[T]
                assert exact <= band_cap <= coarse
                counter["exact_harmonic_interval_checks"] += 1
    assert masks[12][1] == 1 and q[12] < 1
    return masks, q, {"T": 12, "source_interval": [1, 1],
                      "actual_harmonic_mass": "1", "incorrect_qT_cap": str(q[12]),
                      "scope": "Finite counterexample to dropping the earlier-mask contribution."}


def trace_checks(H, masks, q, counter):
    examples = []
    targets = list(range(1, 129))+[255, 511, 1023, 65535, (1 << 40)+1, (1 << 80)+17]
    # This coefficient is valid only for the finite q[1:H+1] table.
    # It is not a proposed replacement for the all-depth written constant A.
    cap2 = max([F(1)]+[t*q[t]**2 for t in range(1, H+1)])
    finite_A = math.isqrt(cap2.numerator//cap2.denominator)+1
    assert all(t*q[t]**2 <= finite_A**2 for t in range(1, H+1))
    for n in targets:
        layers = list(inverse_layers(n, H))
        first = {}
        first_mass = [F(0)]*(H+1)
        nonfused_mass = [F(0)]*(H+1)
        selected_mass = [F(0)]*(H+1)
        seen = set()
        for t, layer in enumerate(layers):
            for m, a in layer.items():
                xs, aa = path(m, t)
                ys, bb = path(m+1, t)
                assert xs[-1] == n and aa[-1] == a
                assert m <= (1 << t)*n
                assert (1 << t)*(n+1) <= 3**t*(m+1)
                assert 3**a*m <= (1 << t)*n
                alive = int(not (xs[-1] == ys[-1] and aa[-1] == bb[-1]))
                assert alive == masks[t][m % (1 << t)]
                lam = F(3**a, 1 << t)
                nonfused_mass[t] += lam*alive
                if t > 0 and m % 2 == 0 and aa[-1] == bb[-1] and alive:
                    selected_mass[t] += lam
                if m not in first:
                    assert xs.index(n) == t
                    first[m] = (t, lam, alive)
                    first_mass[t] += lam*alive
                else:
                    tau, _, first_alive = first[m]
                    assert tau < t and alive <= first_alive
                seen.add(m)
                counter["actual_inverse_paths_and_weight_bounds"] += 1
            a0, b0 = min(seen), max(seen)
            assert b0 <= 2*3**t*a0
            assert b0.bit_length()-a0.bit_length()+1 <= 2*t+2
            counter["finite_predecessor_span_bounds"] += 1

        T = 1
        while T <= H:
            h = min(2*T-1, H)
            sources = {m for layer in layers[:h+1] for m in layer}
            a0, b0 = min(sources), max(sources)
            lo, hi = a0.bit_length()-1, b0.bit_length()-1
            assert hi-lo+1 <= 4*T
            block = [(m, data) for m, data in first.items() if T <= data[0] <= h]
            actual = sum((lam*alive/n for _, (_, lam, alive) in block), F(0))
            marked = sum((F(masks[T][m % (1 << T)], m) for m, _ in block), F(0))
            band_bound = sum(q[min(j, T)] for j in range(lo, hi+1))
            cap = sum(q[:T])+4*T*q[T]
            assert actual <= marked <= band_bound <= cap
            assert actual**2 <= 36*finite_A**2*T
            counter["exact_first_hit_clock_blocks"] += 1
            T *= 2

        xs, aa = path(n, H)
        R = next((r for r in range(1, H+1) if xs[r] == n), None)
        if R is not None:
            assert aa[R] > 0
            assert (3*n+1)*3**aa[R] <= 3*n*(1 << R)
            rho = F(3**aa[R], 1 << R)
            G = 1/(1-rho)
            assert 0 < rho < 1 and G <= 3*n+1
            counter["actual_cycle_factor_checks"] += 1
        else:
            # Only the finite window has no repetition; no nonperiodicity claim.
            G = F(1)
        for h in range(1, H+1):
            fh = sum(first_mass[:h+1], F(0))
            zh = sum(nonfused_mass[:h+1], F(0))
            kh = sum(selected_mass[:h+1], F(0))
            assert 0 <= kh <= zh <= G*fh
            if R is None:
                assert zh == fh
            assert (fh/n)**2 <= 625*finite_A**2*h
            assert (zh/(n*G))**2 <= 625*finite_A**2*h
            counter["finite_nonfusion_and_return_trace_bounds"] += 1
        if n in (1, 2, 3, 27, 128, (1 << 40)+1, (1 << 80)+17):
            examples.append({"target": n, "observed_period_through_cap": R,
                             "nonfused_trace_at_cap": str(sum(nonfused_mass)),
                             "selected_return_trace_at_cap": str(sum(selected_mass)),
                             "normalized_first_hit_mass": str(sum(first_mass)/n)})
    return {"targets_checked": len(targets), "finite_table_coefficient": finite_A,
            "coefficient_scope": "Valid only for the finite mask table; not an all-depth fusion-tail claim.",
            "examples": examples}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-harmonic-trace-") as d:
        for source in SOURCES:
            obj = Path(d)/(Path(source).stem+".olean")
            log = OUT/(Path(source).stem+".log")
            command = ["lean", "-o", str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=d, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
            if source == SOURCES[-1]:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {n for n, _ in roots} == {"HarmonicReturnTrace."+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {
                        "propext", "Classical.choice", "Quot.sound"}, name
            builds.append({"source": source, "source_sha256": digest(ROOT/source),
                           "command": command, "returncode": result.returncode,
                           "elapsed_seconds": round(time.monotonic()-start, 3),
                           "fresh_build": True, "native_computation_used": False,
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior["status"] == "passed"
    for path0, expected in prior["sha256"].items():
        assert digest(ROOT/path0) == expected, path0
    version, builds = build()
    H, counter = 16, Counter()
    masks, q, pitfall = masks_and_bands(H, counter)
    print("Exact nested masks and harmonic bands passed.", flush=True)
    traces = trace_checks(H, masks, q, counter)
    finite = {"clock_cap": H, "counts": dict(counter),
              "mask_means": [{"L": L, "qL": str(q[L])} for L in range(H+1)],
              "small_source_pitfall": pitfall, "traces": traces,
              "asymptotic_scope": "None. Infinite tail and harmonic bounds remain written."}
    (OUT/"replay.json").write_text(json.dumps(finite, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "docs/HARMONIC-RETURN-TRACE.md", PRIOR,
             "results/harmonic-return-trace/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": {PRIOR: len(prior["sha256"])},
              "kernel_scope": ["Shifted source growth, target-independent predecessor span and binary band count.",
                               "Nested nonfusion masks and exact complete-period populations.",
                               "Positive odd correction and the cycle factor bound G_n <= 3*n+1."],
              "finite_scope": dict(counter), "floating_scope": "None in verification decisions.",
              "written_scope": ["Harmonic mask mass on binary source bands, including small sources.",
                                "Nonfused first-hit mass is at most 25*A*n*sqrt(H), uniformly in n.",
                                "K*_(0,H)(n) <= Z_H(n) <= 350*C_star*n*G_n*sqrt(H).",
                                "Independent quantitative fixed-target Cesaro decay and normalized moving-target bound.",
                                "Finite time-discounted integer trace for sigma>1/2 and a square-root Abel rate."],
              "external_scope": "None. The existing written local fusion tail is reused; no external analytic result or compiled library is required.",
              "not_proved": ["Finite total occupation at each positive integer.",
                             "Unnormalized uniform decay for arbitrarily growing targets or pointwise decay of individual return layers.",
                             "Actual-gradient criterion Q, exclusion of escape or additional cycles, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counter), "external_analytic_dependencies": False}, indent=2))


if __name__ == "__main__":
    main()
