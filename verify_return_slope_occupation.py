"""Kernel arithmetic and exact finite support for slope occupation.

Finite trees never certify infinite stopping or integer convergence beyond
their tested paths. Logarithms use rational series with explicit remainders.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_return_slope_tilt import SOURCES as TILT_SOURCES, solve_walk

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/return-slope-occupation"
SOURCES = [*TILT_SOURCES, "lean/ReturnSlopeOccupation.lean"]
THEOREMS = ["numerator_cap", "common_step", "returned_right_bound",
            "returned_left_bound", "returned_separation_cap",
            "logarithmic_step_polynomial", "logarithmic_constants",
            "tilted_tail_shift", "inward_green_source", "tilted_clock_budget",
            "macro_drift_budget", "macro_mass_budget", "occupation_constants"]
PRIOR = ["results/return-slope-tilt/verification.json",
         "results/return-occupation-density/verification.json"]
LOG_PRECISION = 1 << 40


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def log_series(x, terms=32):
    """Enclose ln(x), for 1<=x<=2, by the positive atanh series."""
    x = F(x)
    assert 1 <= x <= 2
    z = (x-1)/(x+1)
    lo = 2*sum((z**(2*j+1)/(2*j+1) for j in range(terms)), F(0))
    tail = 2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return lo, lo+tail


LN2_LO, LN2_HI = log_series(2)


@lru_cache(None)
def log2_bounds(n):
    assert n >= 1
    e = n.bit_length()-1
    if n == 1 << e:
        return e*LOG_PRECISION, e*LOG_PRECISION
    lo, hi = log_series(F(n, 1 << e))
    lower = (e+lo/LN2_HI)*LOG_PRECISION
    upper = (e+hi/LN2_LO)*LOG_PRECISION
    return lower.numerator//lower.denominator, -(-upper.numerator//upper.denominator)


def green_and_constants(counts):
    for K in range(2, 65):
        # Adjoint of the inward walk's equations: row occupation from 1.
        green = solve_walk(K, F(3, 4), 0, 0, [1]+[0]*(K-2))
        for k in range(1, K):
            assert green[k] == F(4*(3**(K-k)-1), 3**K-1)
            assert green[k] <= F(4, 3**k)
            counts["finite_inward_green_values"] += 1
    for k in range(1, 129):
        assert F(3, 4)*F(1, 3**(k+1))/F(1, 3**k) == F(1, 4)
        assert F(1, 4)*F(1, 3**(k-1))/F(1, 3**k) == F(3, 4)
        counts["exact_return_conditioned_transition_pairs"] += 1
    partial = F(1)
    for k in range(1, 513):
        partial += F(4*(6*k+4), 3**k)
        assert partial <= 27
        counts["finite_tilted_clock_budgets"] += 1
    for v in range(33):
        for h in range(33):
            assert 2**v*3**(3*v+h) <= 4**(3*v)*3**h
            counts["tilted_holding_shift_comparisons"] += 1
    for D in range(1025):
        assert (3*D+2)**3*(D+2)+18*D*D+28*D+11 == 27*(D+1)**4
        counts["logarithmic_drift_polynomial_values"] += 1
    assert 3**5 < 2**8
    for initial in (F(1), F(3, 2), F(5), F(101, 7)):
        q, ell, sq, sl = F(1), initial, F(0), F(0)
        for j in range(129):
            assert sq+2*q == 2
            assert 4*sl+10*ell == 10*initial+81*sq
            assert sl <= F(5, 2)*initial+F(81, 2)
            assert sl+sq/2 <= F(5, 2)*initial+F(83, 2)
            assert sl+27*sq/2 <= F(5, 2)*initial+F(135, 2)
            counts["finite_macro_drift_and_cost_budgets"] += 1
            sq, sl = sq+q, sl+ell
            q, ell = q/2, F(3, 5)*ell+F(81, 10)*q


def conditioned_holds(counts):
    for k in (1, 2, 3, 4, 7, 8, 15, 16):
        v = v2(3**k-1)
        for c in (-9, -1, 0, 1, 2, 17):
            for H in (4, 8, 12):
                population = 1 << H
                mass = clock_mass = 0
                directions = Counter()
                for r in range(population):
                    x0 = 16*population+r
                    y0 = 3**k*x0+c
                    x, y, a, b, active = x0, y0, 0, 0, False
                    for t in range(1, H+1):
                        px, py = x & 1, y & 1
                        a, b = a+px, b+py
                        x, y = step(x), step(y)
                        if px != py:
                            active = True
                            break
                    gap = k+b-a
                    assert gap >= 0
                    slow_weight = F(3**a, 1 << t)
                    conditioned_fast_weight = F(3**b, 1 << t)*F(3**k, 3**gap)
                    assert slow_weight == conditioned_fast_weight
                    weight = 3**a*(1 << (H-t))
                    mass += weight
                    clock_mass += t*weight
                    if active:
                        directions[t, gap-k] += weight
                    counts["direct_conditioned_holding_paths"] += 1
                assert mass == population**2
                assert clock_mass <= (3*v+4)*population**2
                for t in range(1, H+1):
                    assert directions[t, -1] == 3*directions[t, 1]
                    counts["conditioned_active_direction_ratios"] += 1
                counts["bounded_conditioned_wait_moments"] += 1
        print("Exact return-conditioned holding blocks passed at gap", k, flush=True)


def zero_gap_blocks(counts):
    examples = []
    separations = sorted(set(range(1, 129)) | {3*2**v for v in range(1, 10)})
    for D in separations:
        v = v2(D)
        population = 1 << v
        mass = lo_sum = hi_sum = 0
        for r in range(population):
            x0, y0 = population+r, population+r+D
            x, y, a = x0, y0, 0
            for j in range(v):
                px, py = x & 1, y & 1
                assert px == py
                previous = y-x
                x, y = step(x), step(y)
                a += px
                assert 2*(y-x) == 3**px*previous
                assert v2(y-x) == v-j-1
            odd_D = y-x
            assert odd_D & 1
            assert population*odd_D == D*3**a
            w = 3**a
            lo, hi = log2_bounds(odd_D+1)
            mass += w
            lo_sum += w*lo
            hi_sum += w*hi
            counts["direct_zero_gap_paths"] += 1
        assert mass == 4**v
        initial_lo, initial_hi = log2_bounds(D+1)
        assert v*LOG_PRECISION <= initial_lo
        if v:
            assert 5*hi_sum <= 6*initial_lo*mass
        else:
            assert (lo_sum, hi_sum) == (initial_lo, initial_hi)
        counts["tilted_zero_gap_logarithmic_drift_checks"] += 1
        if D in (1, 2, 16, 96, 1536):
            examples.append({"D": D, "even_returns": v, "binary_population": population,
                             "tilted_final_log_upper": str(F(hi_sum, mass*LOG_PRECISION))})
    return examples


def fresh_return_clocks(counts):
    rows = []
    for D in (1, 3, 5, 9, 31, 63):
        for H in (8, 12):
            population = 1 << H
            mass, clock = [0, 0], [0, 0]
            unresolved = [0, 0]
            for r in range(population):
                x0, y0 = population+r, population+r+D
                x, y, a, b, returned = x0, y0, 0, 0, False
                for t in range(1, H+1):
                    a, b = a+(x & 1), b+(y & 1)
                    x, y = step(x), step(y)
                    nx, ny = (1 << t)*x-3**a*x0, (1 << t)*y-3**b*y0
                    assert 0 <= nx <= 3**t-(1 << t)
                    assert 0 <= ny <= 3**t-(1 << t)
                    counts["direct_affine_correction_cap_pairs"] += 1
                    if a == b:
                        returned = True
                        break
                if returned:
                    w = 3**a*(1 << (H-t))
                    mass[r & 1] += w
                    clock[r & 1] += t*w
                    assert (1 << t)*(abs(y-x)+1) <= 3**t*(D+1)
                    counts["fresh_equal_count_separation_caps"] += 1
                else:
                    unresolved[r & 1] += 1
                counts["direct_fresh_return_clock_paths"] += 1
            conditional_denominator = population**2//2
            for first in (0, 1):
                assert 2*mass[first] <= conditional_denominator
                assert 2*clock[first] <= 27*conditional_denominator
                counts["partial_conditional_slope_clock_budgets"] += 1
                rows.append({"D": D, "H": H, "first_parity": first,
                             "unresolved": unresolved[first],
                             "partial_mean_slope": str(F(mass[first], conditional_denominator)),
                             "partial_mean_slope_times_clock": str(F(clock[first], conditional_denominator))})
    return rows


def all_return_trees(counts):
    rows = []
    for H in (8, 12, 16):
        population = 1 << H
        mass, ages, even_mass, even_ages = 0, 0, 0, 0
        groups = [Counter()]
        columns = {}
        unmerged = 0
        for r in range(population):
            x, y, a, b = population+r, population+r+1, 0, 0
            last_t, last_D, group = 0, 1, 0
            groups[0][0, 0, 1] += 1
            fused = False
            for t in range(1, H+1):
                a, b = a+(x & 1), b+(y & 1)
                x, y = step(x), step(y)
                if a != b:
                    continue
                D = abs(y-x)
                h = t-last_t
                w = 3**a*(1 << (H-t))
                assert (1 << h)*(D+1) <= 3**h*(last_D+1)
                if last_D % 2 == 0:
                    assert h == 1 and v2(D) == v2(last_D)-1
                mass += w
                ages += h*w
                counts["completed_return_and_age_contributions"] += 1
                if D == 0:
                    fused = True
                    break
                if r % 2 == 0:
                    even_mass += w
                    even_ages += h*w
                    key = t, r % (1 << t)
                    value = a, x % (3**a), h
                    if key in columns:
                        assert columns[key] == value
                    else:
                        columns[key] = value
                if last_D & 1:
                    group += 1
                    if len(groups) <= group:
                        groups.append(Counter())
                    groups[group][t, a, D] += 1
                last_t, last_D = t, D
            unmerged += not fused
            counts["direct_all_return_paths"] += 1
        scale = population**2
        assert mass <= 44*scale and ages <= 70*scale
        q, logs = [], []
        for group in groups:
            qm = lo = hi = 0
            for (t, a, D), multiplicity in group.items():
                w = multiplicity*3**a*(1 << (H-t))
                ll, lh = log2_bounds(D+1)
                qm += w
                lo += w*ll
                hi += w*lh
            q.append(qm)
            logs.append((lo, hi))
        assert q[0] == scale and logs[0] == (scale*LOG_PRECISION,)*2
        for j in range(len(q)-1):
            assert 2*q[j+1] <= q[j]
            assert 10*logs[j+1][1] <= 6*logs[j][0]+81*q[j]*LOG_PRECISION
            counts["capped_actual_group_drift_pairs"] += 1
        assert sum(q) <= 2*scale
        assert sum(hi for lo, hi in logs) <= 43*scale*LOG_PRECISION
        diagonal = sum((F(3**a, 4**t) for (t, r), (a, x, h) in columns.items()), F(0))
        age_diagonal = sum((F(h*3**a, 4**t) for (t, r), (a, x, h) in columns.items()), F(0))
        assert diagonal == F(even_mass, scale)
        assert age_diagonal == F(even_ages, scale)
        counts["exact_even_column_diagonal_identity_pairs"] += 1
        heights = Counter()
        for (t, r), (a, x, h) in columns.items():
            heights[a, x] += 3**a*(1 << (H-t))
        energy = F(0)
        for (a, x), height in heights.items():
            ancestors = sum(heights[b0, x % (3**b0)] for b0 in range(a))
            energy += F(height*height+2*height*ancestors, 3**a*scale)
            counts["exact_ternary_cylinder_energy_terms"] += 1
        assert energy > diagonal
        if H == 8:
            depth = max(a for a, x in heights)
            dense = sum(sum(height for (a, x), height in heights.items()
                            if z % (3**a) == x)**2 for z in range(3**depth))
            assert F(dense, 3**depth*scale) == energy
            counts["independent_full_ternary_period_energy_checks"] += 1
        witness = None
        seen = {}
        for (t, r), (a, x, h) in sorted(columns.items()):
            for b0 in range(a+1):
                key = b0, x % (3**b0)
                if key in seen:
                    u, s, bb, yy = seen[key]
                    cross = F(3**a, 1 << t)*F(3**bb, 1 << u)/3**max(a, bb)
                    assert cross > 0 and x % (3**bb) == yy
                    witness = {"prefixes": [[u, s, bb, yy], [t, r, a, x]],
                               "positive_cross_inner_product": str(cross)}
                    break
            if witness:
                break
            seen[a, x] = t, r, a, x
        assert witness is not None
        counts["actual_positive_column_overlap_witnesses"] += 1
        rows.append({"H": H, "population": population, "unmerged_at_cap": unmerged,
                     "partial_slope_sum_including_fusion": str(F(mass, scale)),
                     "partial_slope_age_sum_including_fusion": str(F(ages, scale)),
                     "group_start_masses": [str(F(v, scale)) for v in q],
                     "even_nonfused_columns": len(columns),
                     "diagonal_squared_mass": str(diagonal),
                     "age_weighted_diagonal_squared_mass": str(age_diagonal),
                     "full_truncated_density_squared_norm": str(energy),
                     "cross_term_mass": str(energy-diagonal),
                     "overlap_witness": witness})
        print("Exact all-return slope, age and grouping checks passed through clock", H, flush=True)
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-slope-occupation-") as d:
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
                assert {n for n, _ in roots} == {"ReturnSlopeOccupation."+t for t in THEOREMS}
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
        for path0, expected in prior["sha256"].items():
            assert digest(ROOT/path0) == expected, path0
        validated[prior_path] = len(prior["sha256"])
    version, builds = build()
    counts = Counter()
    green_and_constants(counts)
    conditioned_holds(counts)
    zero = zero_gap_blocks(counts)
    fresh = fresh_return_clocks(counts)
    occupation = all_return_trees(counts)
    finite = {"counts": dict(counts), "logarithm_precision": LOG_PRECISION,
              "logarithm_method": "32-term positive atanh series, explicit geometric remainder, then outward rounding; no floating decisions.",
              "selected_zero_gap_blocks": zero, "fresh_clock_budgets": fresh,
              "all_return_trees": occupation,
              "infinite_scope": "None. Unfinished paths remain unfinished; all infinite expectations and stopping arguments are written."}
    (OUT/"replay.json").write_text(json.dumps(finite, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_return_slope_tilt.py",
             "verify_return_affine_budget.py", "docs/RETURN-SLOPE-OCCUPATION.md", *PRIOR,
             "results/return-slope-occupation/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated,
              "kernel_scope": ["All-word affine correction cap, common-parity separation and equal-count separation growth.",
                               "Logarithmic-drift polynomial and exact rational power comparisons.",
                               "Tilted holding/Green arithmetic, finite grouped drift and constants 44 and 70."],
              "finite_scope": dict(counts), "floating_scope": "None in verification decisions.",
              "written_scope": ["Conditioning a tilted odd-separation excursion on return gives the inward 3/4 active walk and mean physical clock at most 27.",
                                "The fresh odd-separation slope-weighted clock mean is at most 27/2, including either conditional initial parity.",
                                "Grouping all consecutive even-separation returns yields a killed logarithmic drift.",
                                "For initially adjacent sources, cumulative slopes over all count returns including fusion sum in expectation to at most 44; slope times each excursion length sums to at most 70.",
                                "Even-source nonfused columns have total individual squared Haar norms at most 44, and excursion-age-weighted diagonal mass at most 70."],
              "external_scope": "None. Previously written local slope-tilt and valuation arguments are reused.",
              "not_proved": ["An improved unweighted return-count or physical fusion-clock bound.",
                             "Control of cross terms between overlapping columns or an L2 bound on their sum.",
                             "A uniform actual accumulated-gradient norm, infinite-cutoff integer sampling, criterion Q, escape or additional-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
