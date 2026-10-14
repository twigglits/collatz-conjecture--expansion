"""Exact finite support for the written comparable-source overlap bound.

Infinite probability and logarithmic arguments remain written. Unfinished
paths are retained; finite energy values are not extrapolated.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from math import comb
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_return_slope_occupation import (
    LOG_PRECISION, SOURCES as OCCUPATION_SOURCES, log2_bounds)
from verify_return_slope_tilt import solve_walk
from verify_return_affine_budget import PRECISION, power_bounds

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/return-ancestral-overlap"
SOURCES = [*OCCUPATION_SOURCES, "lean/ReturnAncestralOverlap.lean"]
THEOREMS = ["clock_potential_curvature", "geometric_second_identity",
            "holding_second_cap", "second_cost_identity",
            "second_clock_series_identity", "second_clock_constants",
            "zero_log_square_cap", "group_square_constants",
            "square_drift_budget", "mixed_occupation_constants",
            "log_count_decay", "comparable_energy_constants"]
PRIOR = ["results/return-slope-occupation/verification.json",
         "results/return-occupation-density/verification.json",
         "results/return-correction-moments/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def clock_potential(k):
    return 6*k*k+20*k


def second_cost(k):
    return 72*k**3+468*k*k+616*k+236


def arithmetic_and_walks(counts):
    geometric, second = 0, 0
    for H in range(257):
        assert geometric+4*(2*H+7)*3**H == 28*4**H
        assert second+144*H**3+1584*H*H+5336*H+6316 == 6316*3**H
        counts["exact_geometric_second_moment_identity_pairs"] += 1
        geometric = 4*geometric+4*(2*H+1)*3**H
        second = 3*second+4*second_cost(H+1)
    for K in range(2, 65):
        mean = solve_walk(K, F(1, 4), 0, 0, [6*k+4 for k in range(1, K)])
        square = solve_walk(K, F(1, 4), 0, 0, [second_cost(k) for k in range(1, K)])
        assert mean[1] <= 26 and square[1] <= 6316
        assert 1+2*mean[1]+square[1] <= 6369
        for k in range(1, K):
            assert 4*clock_potential(k) == (
                3*clock_potential(k-1)+clock_potential(k+1)+4*(6*k+4))
            assert mean[k] <= clock_potential(k)
            assert second_cost(k) == (
                36*k*k+48*k+28+2*(6*k+4)*clock_potential(k+1))
            counts["finite_inward_clock_potential_checks"] += 1
        counts["finite_killed_clock_second_moment_budgets"] += 1
    q = ell = square = F(1)
    sq = sl = sm = F(0)
    for H in range(129):
        assert sq+2*q == 2
        assert 4*sl+10*ell == 10+81*sq
        assert 14*sm+50*square == 50+984*sl+57321*sq
        assert sl <= 43 and sm <= F(78502, 7) < 11215
        assert (11*sm+sl)/10+42 < 12383
        counts["finite_group_square_drift_budgets"] += 1
        sq, sl, sm = sq+q, sl+ell, sm+square
        q, ell, square = q/2, F(3, 5)*ell+F(81, 10)*q, (
            F(18, 25)*square+F(492, 25)*ell+F(57321, 50)*q)
    assert 2*399**400 < 400**400
    for D in (1, 2, 31, 400**4, 400**4+1, 1 << 35, 1 << 64, 1 << 128):
        lo, hi = log2_bounds(D+1)
        n0 = (100*hi+LOG_PRECISION-1)//LOG_PRECISION
        fourth_hi = F(power_bounds(D, 1, F(1, 4))[1], PRECISION)
        tail_hi = fourth_hi*F(399, 400)**n0
        assert tail_hi <= 1
        assert n0+tail_hi <= 100*F(lo, LOG_PRECISION)+2
        counts["exact_logarithmic_restart_tail_checks"] += 1


def zero_gap_moments(counts):
    for v in range(11):
        for odd in (1, 3, 5, 17):
            D = odd*(1 << v)
            population = 1 << v
            final = Counter()
            returned_log_hi = 0
            for r in range(population):
                x, y, a = population+r, population+r+D, 0
                path_logs = []
                for _ in range(v):
                    p = x & 1
                    assert p == y & 1
                    a += p
                    x, y = step(x), step(y)
                    path_logs.append(log2_bounds(y-x+1)[1])
                w = 3**a
                final[a] += 1
                returned_log_hi += w*sum(path_logs)
                counts["direct_zero_gap_second_moment_paths"] += 1
            assert final == Counter({a: comb(v, a) for a in range(v+1)})
            mass = 4**v
            ell_lo = log2_bounds(D+1)[0]
            final_square_hi = sum(
                comb(v, a)*3**a*log2_bounds(odd*3**a+1)[1]**2 for a in range(v+1))
            assert 25*final_square_hi <= (
                36*ell_lo**2+12*ell_lo*LOG_PRECISION)*mass
            assert 10*returned_log_hi*LOG_PRECISION <= (
                11*ell_lo**2+ell_lo*LOG_PRECISION)*mass
            counts["zero_gap_square_and_total_log_cost_bounds"] += 1


def fresh_second_clocks(counts):
    rows = []
    for D in (1, 3, 9, 31):
        for H in (8, 12):
            population = 1 << H
            moments = [0, 0]
            unresolved = [0, 0]
            for r in range(population):
                x, y, a, b, returned = population+r, population+r+D, 0, 0, False
                for t in range(1, H+1):
                    a, b = a+(x & 1), b+(y & 1)
                    x, y = step(x), step(y)
                    if a == b:
                        returned = True
                        break
                if returned:
                    moments[r & 1] += t*t*3**a*(1 << (H-t))
                else:
                    unresolved[r & 1] += 1
                counts["direct_fresh_second_clock_paths"] += 1
            scale = population**2//2
            for first in (0, 1):
                assert 2*moments[first] <= 6369*scale
                counts["partial_slope_clock_square_bounds"] += 1
                rows.append({"D": D, "H": H, "first_parity": first,
                             "unresolved": unresolved[first],
                             "partial_slope_times_clock_square": str(F(moments[first], scale))})
    return rows


def overlap_trees(counts):
    rows = []
    for H in (8, 12, 16):
        population = 1 << H
        scale = population**2
        columns = {}
        groups = [Counter()]
        log_mass = [0, 0]
        even_logs = [0, 0]
        direct_nested = 0
        unmerged = 0
        for r in range(population):
            x, y, a, b, group = population+r, population+r+1, 0, 0, 0
            last_D, last_t = 1, 0
            groups[0][0, 0, 1] += 1
            history = []
            fused = False
            for t in range(1, H+1):
                a, b = a+(x & 1), b+(y & 1)
                x, y = step(x), step(y)
                if a != b:
                    continue
                D = abs(y-x)
                if D == 0:
                    fused = True
                    break
                w = 3**a*(1 << (H-t))
                ll, lh = log2_bounds(D+1)
                log_mass[0] += w*ll
                log_mass[1] += w*lh
                if r % 2 == 0:
                    even_logs[0] += w*ll
                    even_logs[1] += w*lh
                    key = t, r % (1 << t)
                    data = a, x % (3**a), D, t-last_t
                    if key in columns:
                        assert columns[key] == data
                    else:
                        columns[key] = data
                    for ai, xi, wi in history:
                        assert ai <= a
                        if x % (3**ai) == xi:
                            direct_nested += wi
                            counts["actual_source_path_image_intersections"] += 1
                    history.append((a, x % (3**a), w))
                if last_D & 1:
                    group += 1
                    if len(groups) <= group:
                        groups.append(Counter())
                    groups[group][t, a, D] += 1
                last_D, last_t = D, t
                counts["direct_nonfused_logarithmic_return_costs"] += 1
            unmerged += not fused
            counts["direct_all_return_paths"] += 1
        assert log_mass[1] <= 12383*scale*LOG_PRECISION
        q, ell, square = [], [], []
        for group in groups:
            qm = llm = lhm = ml = mh = 0
            for (t, a, D), multiplicity in group.items():
                w = multiplicity*3**a*(1 << (H-t))
                lo, hi = log2_bounds(D+1)
                qm += w
                llm += w*lo
                lhm += w*hi
                ml += w*lo*lo
                mh += w*hi*hi
            q.append(qm)
            ell.append((llm, lhm))
            square.append((ml, mh))
        for j in range(len(q)-1):
            assert 50*square[j+1][1] <= (
                36*square[j][0]+984*ell[j][0]*LOG_PRECISION
                +57321*q[j]*LOG_PRECISION**2)
            counts["capped_actual_group_square_drift_checks"] += 1
        assert sum(q) <= 2*scale
        assert sum(hi for lo, hi in ell) <= 43*scale*LOG_PRECISION
        assert sum(hi for lo, hi in square) <= 11215*scale*LOG_PRECISION**2
        diagonal = nested = 0
        heights = Counter()
        column_logs = [0, 0]
        for (t, r), (a, x, D, age) in columns.items():
            d = 3**a*(1 << (2*H-2*t))
            diagonal += d
            heights[a, x] += 3**a*(1 << (H-t))
            lo, hi = log2_bounds(D+1)
            column_logs[0] += d*lo
            column_logs[1] += d*hi
            for s in range(1, t):
                parent = s, r % (1 << s)
                if parent not in columns:
                    continue
                ai, xi, _, _ = columns[parent]
                assert ai <= a
                counts["actual_binary_ancestor_pairs"] += 1
                if x % (3**ai) == xi:
                    nested += 3**ai*(1 << (2*H-s-t))
                    counts["compatible_binary_ancestor_pairs"] += 1
        assert nested == direct_nested
        assert column_logs == even_logs
        energy = 0
        for (a, x), height in heights.items():
            ancestors = sum(heights[b0, x % (3**b0)] for b0 in range(a))
            assert height % (3**a) == 0
            energy += (height//3**a)*(height+2*ancestors)
        disjoint = energy-diagonal-2*nested
        assert disjoint >= 0
        if H <= 12:
            pair_nested = pair_disjoint = 0
            items = sorted(columns.items())
            for j, ((t, r), (a, x, _, _)) in enumerate(items):
                for (s, u), (b0, y, _, _) in items[:j]:
                    assert s <= t
                    depth = min(a, b0)
                    if (x-y) % (3**depth) != 0:
                        continue
                    contribution = 3**depth*(1 << (2*H-s-t))
                    if s < t and r % (1 << s) == u:
                        pair_nested += contribution
                    else:
                        pair_disjoint += contribution
                    counts["independent_positive_column_pair_products"] += 1
            assert pair_nested == nested
            assert 2*pair_disjoint == disjoint
            counts["independent_full_pair_energy_decompositions"] += 1
        assert diagonal <= 44*scale
        assert column_logs[1] <= 12383*scale*LOG_PRECISION
        counts["exact_source_path_and_prefix_overlap_identifications"] += 1
        rows.append({"H": H, "population": population, "unmerged_at_cap": unmerged,
                     "columns": len(columns),
                     "slope_log_cost_interval": [
                         str(F(v, scale*LOG_PRECISION)) for v in log_mass],
                     "diagonal_energy": str(F(diagonal, scale)),
                     "nested_source_cross_energy": str(F(2*nested, scale)),
                     "disjoint_source_cross_energy": str(F(disjoint, scale)),
                     "full_squared_norm": str(F(energy, scale))})
        print("Exact source-path and disjoint-source energy split passed through clock", H, flush=True)
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-ancestral-overlap-") as d:
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
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   result.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {n for n, _ in roots} == {"ReturnAncestralOverlap."+t for t in THEOREMS}
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
    for prior_path in PRIOR:
        prior = json.loads((ROOT/prior_path).read_text())
        assert prior["status"] == "passed"
        for name, expected in prior["sha256"].items():
            assert digest(ROOT/name) == expected, name
        validated[prior_path] = len(prior["sha256"])
    version, builds = build()
    counts = Counter()
    arithmetic_and_walks(counts)
    zero_gap_moments(counts)
    fresh = fresh_second_clocks(counts)
    overlaps = overlap_trees(counts)
    finite = {"counts": dict(counts), "logarithm_precision": LOG_PRECISION,
              "logarithm_method": "Authenticated positive atanh series and rational remainder from the preceding verifier.",
              "fresh_clock_square_checks": fresh, "overlap_trees": overlaps,
              "infinite_scope": "None. The infinite clock moments, logarithmic occupation, restart bound and comparable-source energy are written."}
    (OUT/"replay.json").write_text(json.dumps(finite, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_return_slope_occupation.py",
             "verify_return_slope_tilt.py", "verify_return_affine_budget.py",
             "docs/RETURN-ANCESTRAL-OVERLAP.md", *PRIOR,
             "results/return-ancestral-overlap/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated,
              "kernel_scope": ["Conditional-clock potential, geometric second-moment and cubic cost arithmetic.",
                               "Squared logarithmic drift, finite telescoping and constants 6369, 11215 and 12383.",
                               "Integer geometric decay comparison and the comparable-energy constant."],
              "finite_scope": dict(counts), "floating_scope": "None in verification decisions.",
              "written_scope": ["The return-conditioned tilted fresh clock has second moment at most 6369.",
                                "The cumulative-slope-weighted sum of log2(D+1) over all adjacent-pair count returns is at most 12383.",
                                "Original-law mean fusion count from any fresh D is at most C_star+100 log2(D+1)+2.",
                                "Diagonal plus all cross terms from nested binary source prefixes are at most 88*C_star+2476820.",
                                "The remaining squared-norm term consists exactly of overlaps between disjoint binary source cylinders."],
              "external_scope": "None. Earlier local written conditional clock, slope-tilt and cycle-count arguments are reused.",
              "not_proved": ["Finiteness or divergence of the disjoint-source cross sum, or full Haar L2 of K*_0.",
                             "Necessity of L2 for Collatz, or sufficiency of that norm bound by itself.",
                             "A uniform actual forward-gradient estimate, integer sampling at infinite cutoff, Q, escape or additional-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
