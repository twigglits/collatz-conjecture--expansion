"""Kernel arithmetic and exact finite support for the active-gap potential.

Infinite stopping, real fractional moments, and Haar integrability remain
written arguments. Unfinished finite paths are never declared returned.
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

from verify_return_affine_budget import (
    PRECISION, SOURCES as AFFINE_SOURCES, power_bounds)


ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/active-gap-potential"
SOURCE = "lean/ActiveGapPotential.lean"
SOURCES = [*AFFINE_SOURCES, SOURCE]
THEOREMS = ["min_curvature", "total_diagonal", "green_boundary", "green_cap",
            "green_curvature", "linear_geometric_identity",
            "quadratic_geometric_identity", "geometric_caps",
            "fractional_slope_constants"]
PRIOR = ["results/return-affine-budget/verification.json",
         "results/return-occupation-density/verification.json",
         "results/count-return-clock/verification.json"]
CASES = [(F(1, 2), F(31, 32), F(63, 64), 8577),
         (F(3, 4), F(63, 64), F(127, 128), 33537),
         (F(7, 8), F(127, 128), F(255, 256), 132609)]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(value):
    value = F(value)
    return [value.numerator, value.denominator]


def root(value, eta):
    value = F(value)
    lo, hi = power_bounds(value.numerator, value.denominator, eta)
    return F(lo, PRECISION), F(hi, PRECISION)


@lru_cache(None)
def green(q, d):
    return (8 - 4*q - 2*q**d*((d+4)-(d+2)*q))/(1-q)**3


def valuation_two(value):
    assert value > 0
    return (value & -value).bit_length()-1


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def green_checks(counts):
    for H in range(33):
        for costs in ([1]*H, [j*j+3*j+5 for j in range(H)],
                      [0 if j % 3 else j+1 for j in range(H)]):
            values = [sum(min(d, j+1)*costs[j] for j in range(H))
                      for d in range(H+3)]
            assert values[0] == 0
            cap = sum((j+1)*costs[j] for j in range(H))
            assert all(0 <= value <= cap for value in values)
            for d in range(1, H+1):
                assert 2*values[d] == values[d-1]+values[d+1]+costs[d-1]
                counts["finite_integer_green_curvatures"] += 1
    for a in (0, 1, 2, 5, 63):
        for c in (1, 2, 7):
            b = a+c
            for H in range(25):
                linear = sum((j+4)*a**j*b**(H-1-j) for j in range(H))
                quadratic = sum((j+1)*(j+4)*a**j*b**(H-1-j) for j in range(H))
                assert c*c*linear+a**H*((H+4)*c+a) == (a+4*c)*b**H
                assert c**3*quadratic+a**H*((H+1)*(H+4)*c*c
                       +(2*H+6)*a*c+2*a*a) == (2*a+4*c)*b**(H+1)
                counts["homogeneous_geometric_identity_pairs"] += 1
    for q in (F(1, 3), F(2, 3), F(9, 10), *(case[2] for case in CASES)):
        assert green(q, 0) == 0
        assert green(q, 1) == (8-6*q)/(1-q)**2
        for d in range(1, 65):
            assert 0 <= green(q, d) <= (8-4*q)/(1-q)**3
            assert (green(q, d-1)+green(q, d+1))/2 == green(q, d)-q**(d-1)*(d+3)
            for H in (d, d+1, d+9):
                partial = 2*sum(min(d, j)*q**(j-1)*(j+3) for j in range(1, H+1))
                tail = 2*d*q**H*((H+4)-(H+3)*q)/(1-q)**2
                assert partial+tail == green(q, d)
                counts["exact_green_series_tail_checks"] += 1
            counts["rational_green_curvatures_and_caps"] += 1
    for eta, rcap, q, budget in CASES:
        assert (root(F(1, 2), eta)[1]+root(F(3, 2), eta)[1])/2 < rcap < q < 1
        assert budget == 1+green(q, 1)
        counts["fractional_slope_and_correction_constants"] += 1
    # Check rational instances of the all-eta chord and budget estimates.
    for denominator in (2, 4, 8, 16, 32):
        for numerator in range(denominator//2, denominator):
            eta = F(numerator, denominator)
            eps = 1-eta
            rhi = (root(F(1, 2), eta)[1]+root(F(3, 2), eta)[1])/2
            q = 1-eps/32
            assert 1-rhi >= eps/16 and rhi < q
            assert 1+green(q, 1) <= 8193/eps**2
            counts["near_one_chord_and_budget_checks"] += 1


def bounded_stop_identities(records, H, clock_sum, counts):
    """Every record includes multiplicity, odd count, offset numerator, time."""
    population = 1 << H
    for endpoint in records:
        slope_sum = sum(m*3**a*(1 << (H-t)) for (a, N, t), m in endpoint.items())
        correction_sum = sum(m*N*(1 << (H-t)) for (a, N, t), m in endpoint.items())
        assert sum(endpoint.values()) == population
        assert slope_sum == population*population
        assert 4*correction_sum == clock_sum*population
        counts["bounded_stopping_identity_pairs"] += 1


def active_block_checks(counts):
    rows = []
    for d in (1, 2, 3, 4, 8, 16, 31, 32):
        v = valuation_two(3**d-1)
        assert v < 2*d
        offsets = sorted({0, 1, -1, 2, -2, 2**v, -2**v, 3**d-1, 1-3**d})
        for c in offsets:
            for H in (4, 8, 12):
                population = 1 << H
                cap = [Counter(), Counter()]
                terminal = [Counter(), Counter()]
                signs = Counter()
                clock_sum = unfinished = 0
                shift = (1+abs(c)//population)*population
                for residue in range(population):
                    x0 = shift+residue
                    y0 = 3**d*x0+c
                    assert x0 > 0 and y0 > 0
                    x, y, a, b = x0, y0, 0, 0
                    completed = False
                    for t in range(1, H+1):
                        px, py = x & 1, y & 1
                        a, b = a+px, b+py
                        x, y = step(x), step(y)
                        if px != py:
                            completed = True
                            break
                    nx, ny = (1 << t)*x-3**a*x0, (1 << t)*y-3**b*y0
                    assert nx >= 0 and ny >= 0
                    cap[0][a, nx, t] += 1
                    cap[1][b, ny, t] += 1
                    clock_sum += t
                    if completed:
                        new_gap = d+b-a
                        assert new_gap in (d-1, d+1)
                        signs[t, new_gap] += 1
                        terminal[0][a, nx, t, new_gap] += 1
                        terminal[1][b, ny, t, new_gap] += 1
                    else:
                        unfinished += 1
                    counts["direct_active_block_paths"] += 1
                bounded_stop_identities(cap, H, clock_sum, counts)
                assert clock_sum <= (v+2)*population
                assert unfinished <= min(population, 2**v)
                for t in range(1, H+1):
                    assert signs[t, d-1] == signs[t, d+1]
                    counts["active_time_sign_balance_checks"] += 1
                moment_rows = []
                for eta, rcap, q, budget in CASES:
                    for endpoint, outcomes in enumerate(terminal):
                        slope_hi = sum(m*root(F(3**a, 1 << t), eta)[1]
                                       for (a, N, t, dp), m in outcomes.items())/population
                        correction_hi = sum(m*root(F(N, 1 << t), eta)[1]
                                            for (a, N, t, dp), m in outcomes.items())/population
                        assert slope_hi <= rcap
                        assert correction_hi <= d+3
                        for B in (0, 1, 16):
                            lhs = sum(m*(q**dp*root(F(3**a*B+N, 1 << t), eta)[1]
                                         +green(q, dp))
                                      for (a, N, t, dp), m in outcomes.items())/population
                            rhs = q**d*root(F(B), eta)[0]+green(q, d)
                            assert lhs <= rhs, (d, c, H, eta, endpoint, B, lhs, rhs)
                            counts["partial_terminal_potential_bounds"] += 1
                        counts["partial_active_slope_and_correction_bounds"] += 1
                        if H == 12 and c == 0:
                            moment_rows.append({"eta": rational(eta), "endpoint": endpoint,
                                                "completed_correction_moment_upper": rational(correction_hi)})
                rows.append({"gap": d, "offset": c, "clock_cap": H,
                             "population": population, "unfinished": unfinished,
                             "capped_mean_wait": rational(F(clock_sum, population)),
                             "selected_moments": moment_rows})
        print("Exact active-block law passed at gap", d, flush=True)
    return rows


def fresh_return_checks(counts):
    rows = []
    for D in (1, 2, 3, 5, 17, 32, 257, 1025):
        for H in (8, 12):
            population = 1 << H
            cap, terminal = [Counter(), Counter()], [Counter(), Counter()]
            clock_sum = unfinished = 0
            for residue in range(population):
                x0, y0 = population+residue, population+residue+D
                x, y, a, b = x0, y0, 0, 0
                completed = False
                for t in range(1, H+1):
                    a, b = a+(x & 1), b+(y & 1)
                    x, y = step(x), step(y)
                    if a == b:
                        completed = True
                        break
                nx, ny = (1 << t)*x-3**a*x0, (1 << t)*y-3**b*y0
                assert nx >= 0 and ny >= 0
                cap[0][a, nx, t] += 1
                cap[1][b, ny, t] += 1
                clock_sum += t
                if completed:
                    assert (1 << t)*abs(y-x) <= 3**a*D+nx+ny
                    terminal[0][a, nx, t] += 1
                    terminal[1][b, ny, t] += 1
                else:
                    unfinished += 1
                counts["direct_fresh_return_paths"] += 1
            bounded_stop_identities(cap, H, clock_sum, counts)
            for eta, rcap, q, budget in CASES:
                for outcomes in terminal:
                    correction_hi = sum(m*root(F(N, 1 << t), eta)[1]
                                        for (a, N, t), m in outcomes.items())/population
                    slope_hi = sum(m*root(F(3**a, 1 << t), eta)[1]
                                   for (a, N, t), m in outcomes.items())/population
                    assert correction_hi <= budget and slope_hi <= rcap
                    counts["partial_fresh_return_moment_bounds"] += 1
            rows.append({"separation": D, "clock_cap": H,
                         "population": population, "unfinished": unfinished,
                         "capped_mean_clock": rational(F(clock_sum, population))})
    return rows


def cumulative_return_checks(counts):
    H = 14
    population = 1 << H
    mass = Counter({0: population})
    moments = {(eta, name): defaultdict(lambda: [0, 0])
               for eta, *_ in CASES for name in ("C", "D")}
    for m in moments.values():
        m[0] = [population*PRECISION, population*PRECISION]
    for n in range(population):
        x, y, a, b, j = n, n+1, 0, 0, 0
        last_t, last_x, last_a, last_num = 0, n, 0, 1
        for t in range(1, H+1):
            a, b = a+(x & 1), b+(y & 1)
            x, y = step(x), step(y)
            if a != b:
                continue
            num = 3**a+(1 << t)*x-3**a*n
            correction = (1 << (t-last_t))*x-3**(a-last_a)*last_x
            assert correction >= 0
            assert num == 3**(a-last_a)*last_num+(1 << last_t)*correction
            counts["direct_cumulative_affine_compositions"] += 1
            if x == y:
                break
            j += 1
            last_t, last_x, last_a, last_num = t, x, a, num
            mass[j] += 1
            for eta, *_ in CASES:
                for name, numerator, denominator in (("C", num, 1 << t), ("D", abs(y-x), 1)):
                    lo, hi = power_bounds(numerator, denominator, eta)
                    moments[eta, name][j][0] += lo
                    moments[eta, name][j][1] += hi
                    counts["finite_return_fractional_moments"] += 1
    rows = []
    for eta, rcap, q, budget in CASES:
        for name, additive in (("C", budget), ("D", 2*budget)):
            m = moments[eta, name]
            for j in range(max(mass)+1):
                assert m[j+1][1] <= rcap*m[j][0]+additive*mass[j]*PRECISION
                counts["finite_killed_return_drift_checks"] += 1
            total_lo, total_hi = sum(v[0] for v in m.values()), sum(v[1] for v in m.values())
            assert (1-rcap)*total_hi <= population*PRECISION+additive*sum(mass.values())*PRECISION
            counts["finite_cumulative_moment_budget_checks"] += 1
            rows.append({"eta": rational(eta), "coefficient": name,
                         "moment_sum_lower": rational(F(total_lo, population*PRECISION)),
                         "moment_sum_upper": rational(F(total_hi, population*PRECISION))})
    return {"clock_cap": H, "population": population,
            "return_prefix_mass": rational(F(sum(mass.values()), population)),
            "moments": rows,
            "scope": "Nonfused returns through the physical cutoff, including index zero; no infinite moment is inferred from this finite census."}


def exponent_checks(counts):
    examples, weighted = [], []
    for denominator in range(2, 161):
        for numerator in range(denominator+1, (5*denominator+3)//4):
            p = F(numerator, denominator)
            if p >= F(5, 4):
                continue
            alpha = p-1
            eta = (alpha/(1-3*alpha)+1)/2
            exponent = 3*alpha/2-F(1, 2)+alpha/(2*eta)
            assert 0 < alpha < alpha/(1-3*alpha) < eta < 1
            assert exponent < 0 and (17*alpha-8)/p < -1
            assert exponent-(2*alpha-F(1, 2)) == alpha*(1-eta)/(2*eta)
            counts["exact_dyadic_and_atypical_exponent_checks"] += 1
    for p in (F(6, 5), F(39, 32), F(31, 25), F(1249, 1000)):
        alpha = p-1
        eta = (alpha/(1-3*alpha)+1)/2
        examples.append({"p": rational(p), "eta": rational(eta),
                         "dyadic_exponent": rational(3*alpha/2-F(1, 2)+alpha/(2*eta))})
    for beta in (F(0), F(1, 4), F(1, 2), F(3, 4), F(15, 16)):
        for denominator in (32, 128, 512):
            gamma, p0 = 1-F(1, denominator), F(5, 4)-F(1, denominator)
            theta = beta/gamma
            p = 1/(theta+(1-theta)/p0)
            assert 0 <= theta < 1 and 1 < p < 5/(4+beta)
            weighted.append({"beta": rational(beta), "gamma": rational(gamma),
                             "p0": rational(p0), "p": rational(p)})
            counts["exact_weighted_exponent_checks"] += 1
    return {"unweighted": examples, "weighted": weighted}


def build_lean():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-active-gap-") as directory:
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
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {n for n, _ in roots} == {"ActiveGapPotential."+t for t in THEOREMS}
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
    authenticated = {}
    for prior in PRIOR:
        record = json.loads((ROOT/prior).read_text())
        assert record["status"] == "passed"
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (prior, path)
        authenticated[prior] = len(record["sha256"])
    version, builds = build_lean()
    counts = Counter()
    green_checks(counts)
    print("Exact Green potential and fractional constants passed.", flush=True)
    active = active_block_checks(counts)
    returns = fresh_return_checks(counts)
    cumulative = cumulative_return_checks(counts)
    exponents = exponent_checks(counts)
    replay = {"active_blocks": active, "fresh_returns": returns,
              "cumulative_returns": cumulative, "exponent_examples": exponents,
              "counts": dict(counts), "fractional_enclosure_denominator": PRECISION}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_return_affine_budget.py",
             "docs/ACTIVE-GAP-POTENTIAL.md", *PRIOR,
             "results/active-gap-potential/replay.json", *[b["log"] for b in builds]]
    record = {"verified_at_utc": datetime.now(timezone.utc).isoformat(), "status": "passed",
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": authenticated,
              "kernel_scope": ["Finite half-line Green curvature, zero boundary and cap.",
                               "Two homogeneous geometric identities and nonnegative-remainder caps.",
                               "Exact integer comparisons giving three strict fractional-slope bounds."],
              "written_scope": ["Conditional active-block correction bound and nonnegative potential stopping argument.",
                                "Returned corrections, cumulative coefficients, and separations have moments of every power below one.",
                                "Occupation C and D tails are O((log u)^3/u); fresh correction tail is O((log u)^2/u).",
                                "All-return K*_beta is in Lp for 0<=beta<1 and 1<=p<5/(4+beta).",
                                "Weighted clock-truncation error is O_beta(H^(-(1-beta)/2)(log H)^(1+2*beta))."],
              "finite_scope": dict(counts), "floating_scope": "None in verification decisions.",
              "external_scope": "No new external theorem. Existing written active-wait, return-clock, occupation and fractional-fibre arguments are reused with authenticated records.",
              "not_proved": ["Endpoint moments at eta=1 or endpoint Lp integrability; optimality of the range.",
                             "A finite mean of the physical fusion clock, which has a known infinite mean under this law.",
                             "Infinite-cutoff ordinary-integer trace sampling or complementary actual-gradient power bounds.",
                             "The temporal criterion Q, bounded actual energy, exclusion of escape or additional cycles, or full Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print("PASS: nine kernel roots and exact finite potential checks; infinite analysis remains written and Collatz unresolved.", flush=True)


if __name__ == "__main__":
    main()
