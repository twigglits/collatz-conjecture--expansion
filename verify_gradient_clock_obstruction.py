"""Exact finite inputs to a conditional obstruction to uniform gradient powers.

Universal convergence is a hypothesis of the written infinite theorem,
not an output of this verifier. All finite arrivals are actually certified.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_known_basin_nonfusion_trace import first_arrivals
from verify_annulus_time_budgets import complete_pair, PRECISION as ENERGY_PRECISION

ROOT = Path(__file__).resolve().parent
OUT = ROOT/"results/gradient-clock-obstruction"
SOURCE = "lean/GradientClockObstruction.lean"
SOURCES = ["CollatzAffine.lean", "CollatzPacking.lean", "lean/CoalescenceTail.lean",
           "lean/EscapeWeightRefinements.lean", "lean/IntegerReturnCesaro.lean",
           "lean/AnnulusTimeBudgets.lean", SOURCE]
THEOREMS = ["first_arrival_unique", "first_arrival_even", "arrival_clock_floor",
            "arrival_remaining_floor", "weight_children_sum", "weight_mass",
            "weight_band_mass", "first_arrival_eq_of_prefix", "fused_child_arrival",
            "clock_telescope", "profile_window", "finite_profile_constants"]
PRIOR = ["results/finite-path-packing/verification.json",
         "results/count-return-clock/verification.json",
         "results/return-correction-moments/verification.json",
         "results/annulus-time-budgets/verification.json",
         "results/known-basin-nonfusion-trace/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(value):
    value = F(value)
    return [value.numerator, value.denominator]


def direct(n, t):
    a = 0
    for _ in range(t):
        a += n & 1
        n = (3*n+1)//2 if n & 1 else n//2
    return n, a


def finite_clocks(counts):
    maximum = 1 << 16
    memo = first_arrivals(maximum, counts)
    minimum = F(1)
    for n in range(1, maximum+1):
        t, a = memo[n]
        w = F(n*3**a, 1 << t)
        assert w >= F(3, 4)
        minimum = min(minimum, w)
        counts["finite_three_quarters_first_hit_floors"] += 1

    rows, sample_set, means, etas = [], set(), [], []
    for k in range(16):
        M = 1 << k
        sum_remaining, sum_odd, positive, negative, nonfused, full_nonfused = 0, 0, 0, 0, 0, 0
        clock_powers = {p: 0 for p in (1, 2, 4, 8, 12)}
        largest, smallest = (0, M), (0, M)
        for n in range(M, 2*M):
            t, _ = memo[n]
            x, a = direct(n, k)
            assert t >= k+a
            assert x >= 3**a
            sum_remaining += t-k
            sum_odd += a
            counts["arrival_remaining_clock_lower_bounds"] += 1
            if k == 15:
                continue
            te, ae = memo[2*n]
            to, _ = memo[2*n+1]
            assert (te, ae) == (t+1, memo[n][1])
            delta = to-t-1
            positive += max(delta, 0)
            negative += max(-delta, 0)
            for p in clock_powers:
                clock_powers[p] += abs(delta)**p
            largest, smallest = max(largest, (delta, n)), min(smallest, (delta, n))

            y, b = direct(3*n+2, k)
            mask = (x, a) != (y, b+1)
            assert mask == (direct(2*n, k+1) != direct(2*n+1, k+1))
            r = 2*(n-M)
            even_mask = direct(r, k+1) != direct(r+1, k+1)
            assert mask == even_mask
            odd_mask = direct(r+1, k+1) != direct(r+2, k+1)
            nonfused += mask
            full_nonfused += even_mask+odd_mask
            if not mask:
                assert delta == 0
                counts["fused_edges_with_equal_arrival_clocks"] += 1
            counts["actual_band_vs_even_residue_masks"] += 1
            if k <= 8:
                sample_set.add((k, n))
        assert 2*sum_odd == k*M
        assert 2*sum_remaining >= k*M
        means.append(F(sum_remaining, M))
        row = {"level": k, "interval": [M, 2*M],
               "mean_remaining_first_arrival": ratio(means[-1]),
               "odd_count_sum": sum_odd}
        if k < 15:
            eta = F(nonfused, M)
            assert nonfused <= full_nonfused
            etas.append(eta)
            row.update({"nonfused_edges_at_prefix": nonfused,
                        "eta": ratio(eta), "full_period_nonfusion_count": full_nonfused,
                        "mean_positive_clock_increment": ratio(F(positive, M)),
                        "mean_negative_clock_increment": ratio(F(negative, M)),
                        "clock_increment_power_means": {
                            str(p): ratio(F(value, M)) for p, value in clock_powers.items()}})
            for n in (M, 2*M-1, M+M//3, M+M//2, M+2*M//3, largest[1], smallest[1]):
                sample_set.add((k, n))
        rows.append(row)
        counts["exact_parity_means_and_arrival_mean_bounds"] += 1
        print("Exact arrival band passed:", k, flush=True)

    sum_positive, sum_negative = F(0), F(0)
    for k in range(15):
        positive = F(*rows[k]["mean_positive_clock_increment"])
        negative = F(*rows[k]["mean_negative_clock_increment"])
        assert 2*means[k+1]+negative == 2*means[k]+positive
        sum_positive += positive
        sum_negative += negative
        assert 2*means[k+1]+sum_negative == sum_positive
        counts["exact_clock_telescope_prefixes"] += 1
    return memo, means, etas, sorted(sample_set), {
        "maximum_certified_source": maximum,
        "minimum_first_hit_weight": ratio(minimum), "bands": rows}


def sampled_profiles(memo, samples, counts):
    rows = []
    for k, n in samples:
        M = 1 << k
        parent = memo[n][0]-k
        child = memo[2*n+1][0]-k-1
        delta = child-parent
        x, a = direct(n, k)
        y, b = direct(3*n+2, k)
        mask = (x, a) != (y, b+1)
        cell = complete_pair(n, 3*n+2, M, k, 1, counts)
        lo, hi = cell["energy"]
        window = max(abs(delta)-12, 0)
        assert 9*window*ENERGY_PRECISION <= 256*lo
        assert abs(delta)*9*ENERGY_PRECISION <= 108*int(mask)*ENERGY_PRECISION+256*lo
        if not mask:
            assert lo == hi == 0
        for s in range(min(parent, child)+12, max(parent, child)):
            xp, ap = direct(n, k+s)
            xc, ac = direct(3*n+2, k+s)
            A = F(M*3**ap, (1 << (k+s))*xp)
            B = F(3*M*3**ac, (1 << (k+s))*xc)
            early, late = (A, B) if parent < child else (B, A)
            assert early <= F(3, 16) and late >= F(3, 8)
            assert (A-B)**2 >= F(9, 256)
            counts["independent_actual_profile_window_terms"] += 1
        counts["complete_cell_energy_vs_arrival_gap_checks"] += 1
        if window > 0 and (k >= 9 or len(rows) < 10):
            rows.append({"level": k, "parent": n, "remaining_parent_arrival": parent,
                         "remaining_odd_child_arrival": child,
                         "window_length": window,
                         "lower_energy_from_clock_gap": ratio(F(9*window, 256)),
                         "certified_full_energy": {"lower": ratio(F(lo, ENERGY_PRECISION)),
                                                   "upper": ratio(F(hi, ENERGY_PRECISION))}})
    print("Exact profile windows and all-future costs passed:", len(samples), "sampled cells", flush=True)
    return {"sampled_cells": len(samples), "witnesses": rows,
            "scope": "Complete future sums only for these sampled cells; their cycle tails are certified."}


def moment_budgets(means, etas, bands, counts):
    old = json.loads((ROOT/"results/annulus-time-budgets/replay.json").read_text())["annuli"]["rows"]
    rows, Q = [], F(0)
    sums_lo = {p: F(0) for p in (1, 2, 4, 8, 12)}
    sums_hi = dict(sums_lo)
    clock_sums = dict(sums_lo)
    for K in range(1, 16):
        row = old[K-1]
        assert row["level"] == K-1
        Q += etas[K-1]
        margin = max(2*means[K]-12*Q, F(0))
        required_first = F(9, 256)*margin
        powers = {}
        for p in sums_lo:
            clock_sums[p] += F(*bands[K-1]["clock_increment_power_means"][str(p)])
            assert (2*means[K])**p <= Q**(p-1)*clock_sums[p]
            counts["finite_clock_increment_moment_lower_bounds"] += 1
            bounds = row["unhalved_cell_energy_moments"][str(p)]
            sums_lo[p] += F(*bounds["lower"])
            sums_hi[p] += F(*bounds["upper"])
            assert required_first**p <= Q**(p-1)*sums_lo[p]
            powers[str(p)] = {
                "lower_bound_from_clocks": ratio(required_first**p/Q**(p-1)),
                "clock_increment_lower_bound": ratio((2*means[K])**p/Q**(p-1)),
                "exact_clock_increment_power_sum": ratio(clock_sums[p]),
                "authenticated_sum_of_moments": {
                    "lower": ratio(sums_lo[p]), "upper": ratio(sums_hi[p])}}
            counts["finite_holder_moment_lower_bounds"] += 1
        rows.append({"K": K, "Q_K": ratio(Q), "mean_remaining_arrival": ratio(means[K]),
                     "positive_clock_margin": ratio(margin), "power_budgets": powers})
        if margin > 0:
            counts["nonzero_finite_clock_margins"] += 1
    assert counts["nonzero_finite_clock_margins"] > 0
    assert 16*3**6 <= 3*4**6
    print("Authenticated finite energy powers satisfy all arrival-clock budgets.", flush=True)
    return {"rows": rows,
            "energy_source": "results/annulus-time-budgets/replay.json",
            "reuse_scope": "Previously certified complete finite-annulus energy moments; authenticated here, not recomputed for every cell."}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-gradient-clock-") as directory:
        for source in SOURCES:
            obj = Path(directory)/(Path(source).stem+".olean")
            log = OUT/(Path(source).stem+".log")
            command = ["lean", "-o", str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   result.stdout, re.M)
                assert {name for name, _ in roots} == {"GradientClockObstruction."+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
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
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT/name).read_text())
        if "status" in record:
            assert record["status"] == "passed", name
        else:
            assert name == "results/finite-path-packing/verification.json"
            assert record["builds"] and all(b["returncode"] == 0 for b in record["builds"])
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    memo, means, etas, samples, clocks = finite_clocks(counts)
    profiles = sampled_profiles(memo, samples, counts)
    moments = moment_budgets(means, etas, clocks["bands"], counts)
    replay = {"first_arrival_clocks": clocks, "profile_windows": profiles,
              "finite_moment_budgets": moments, "counts": dict(counts),
              "infinite_scope": "None. Universal convergence is an explicit hypothesis of the written infinite theorem."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_known_basin_nonfusion_trace.py",
             "verify_dyadic_coalescence_defects.py", "verify_annulus_time_budgets.py",
             "docs/CONDITIONAL-GRADIENT-POWER-OBSTRUCTION.md", "docs/FINITE-PATH-PACKING.md",
             "docs/COUNT-RETURN-CLOCK.md", "docs/RETURN-CORRECTION-MOMENTS.md",
             "docs/ANNULUS-TIME-BUDGETS.md", *PRIOR,
             "results/annulus-time-budgets/replay.json", "results/gradient-clock-obstruction/replay.json",
             *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["First-arrival clocks, doubling, and equality after a matching prefix.",
                               "An arrival from the kth binary band has at least k plus its first k odd-count clocks.",
                               "Exact mean odd count on a binary period and band.",
                               "Finite arrival-clock telescoping and integer profile-window constants."],
              "written_scope": ["A uniform positive first-hit weight controls the width of known-cycle profiles.",
                                "Universal convergence implies the same K^((p+1)/2) lower growth for arrival-clock increment power sums, without a packing input.",
                                "Universal convergence implies sum_(k<K) mean G_k^p >= c_p K^((p+1)/2) for p>1.",
                                "Thus universal convergence is incompatible with uniform complete-interval accumulated-gradient powers above one."],
              "external_scope": "None for the new theorem. Only local written packing and fusion-tail results are used; no external validation routine is called.",
              "not_proved": ["Universal convergence or a positive-integer counterexample.",
                             "Unconditional infinite power growth or growth on a particular returned progression.",
                             "Failure of uniform first moments, density-weighted gradients, reversed negative drift, bounded E_s, or Q.",
                             "Escape or additional-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
