"""Exact finite support for the written return-slope tilt argument.

Infinite hitting laws, stopping, critical moments and Haar integrability
remain written. Capped paths retain their unresolved status. All checks
use integers or fractions, including enclosures of fractional powers.
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

from verify_return_affine_budget import PRECISION, power_bounds

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/return-slope-tilt"
SOURCES = ["CollatzAffine.lean", "lean/CoalescenceTail.lean",
           "lean/EscapeWeightRefinements.lean", "lean/CountReturnControl.lean",
           "lean/CountReturnClock.lean", "lean/ReturnCorrectionMoments.lean",
           "lean/ReturnSlopeTilt.lean"]
THEOREMS = ["biased_boundaries", "away_harmonic", "toward_harmonic",
            "biased_numerator_ratio", "fair_exit_clock", "fast_cost_identity",
            "fast_cost_budget", "root_gap_identity", "root_endpoint_switch"]
PRIOR = ["results/active-gap-potential/verification.json",
         "results/return-correction-moments/verification.json",
         "results/count-return-clock/verification.json",
         "results/return-occupation-density/verification.json"]
ETAS = (F(1, 2), F(3, 4), F(7, 8), F(15, 16))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def power(x, eta):
    x = F(x)
    lo, hi = power_bounds(x.numerator, x.denominator, eta)
    return F(lo, PRECISION), F(hi, PRECISION)


def solve_walk(K, p, left, right, costs):
    """Solve f(j)-p*f(j+1)-(1-p)*f(j-1)=cost(j) by elimination."""
    n = K-1
    lower, upper = -(1-p), -p
    diag = [F(1)]*n
    rhs = [F(c) for c in costs]
    rhs[0] -= lower*left
    rhs[-1] -= upper*right
    for j in range(1, n):
        ratio = lower/diag[j-1]
        diag[j] -= ratio*upper
        rhs[j] -= ratio*rhs[j-1]
    solution = [F(0)]*n
    solution[-1] = rhs[-1]/diag[-1]
    for j in range(n-2, -1, -1):
        solution[j] = (rhs[j]-upper*solution[j+1])/diag[j]
    return [F(left), *solution, F(right)]


def finite_walks(counts):
    for K in range(2, 65):
        away = solve_walk(K, F(3, 4), 1, 0, [0]*(K-1))
        toward = solve_walk(K, F(1, 4), 1, 0, [0]*(K-1))
        clock = solve_walk(K, F(1, 2), 0, 0, [1]*(K-1))
        # Symmetry of the fair tridiagonal inverse: visits from 1 to j
        # equal visits from j to 1. Solve one independent Green column.
        green = solve_walk(K, F(1, 2), 0, 0, [1]+[0]*(K-2))
        for j in range(K+1):
            assert away[j] == F(3**(K-j)-1, 3**K-1)
            assert toward[j] == F(3**K-3**j, 3**K-1)
            assert toward[j] == 3**j*away[j]
            assert clock[j] == j*(K-j)
            if 0 < j < K:
                assert green[j] == F(2*(K-j), K)
                counts["finite_fair_green_values"] += 1
            counts["finite_biased_hitting_and_exit_values"] += 1
    cost = 0
    partial = F(0)
    for H in range(513):
        assert cost == 3**H*partial
        assert 2*cost+6*H+13 == 13*3**H
        assert F(1, 6)+partial/6 <= F(5, 4)
        assert 2*(3**H+cost) <= 15*3**H
        counts["exact_fast_geometric_budget_checks"] += 1
        cost = 3*cost+6*H+10
        partial += F(6*(H+1)+4, 3**(H+1))


def fractional_roots(counts):
    cases, rows = {}, []
    for eta in ETAS:
        ahi = power(F(3, 2), eta)[1]/2
        bhi = power(F(1, 2), eta)[1]/2
        dlo, dhi = power(F(3, 4), eta)
        sqrtlo = power(1-dhi, F(1, 2))[0]
        sqrthi = power(1-dlo, F(1, 2))[1]
        twolo, twohi = power(2, eta)
        zlo, zhi = twolo*(1-sqrthi), twohi*(1-sqrtlo)
        rlo, rhi = power(F(1, 3), eta)
        zflo, zfhi = rlo*zlo, rhi*zhi
        assert 0 < zlo <= zhi < 1
        assert 0 < zflo <= zfhi < 1
        qs, qf = (1+zhi)/2, (1+zfhi)/2
        # These strictly interior rational choices tolerate enclosure
        # error and give exact supermartingale comparisons on real trees.
        assert ahi/qs+bhi*qs <= 1
        assert bhi/qf+ahi*qf <= 1
        assert 1-ahi-bhi >= (1-eta)/16
        assert 1-zhi >= (1-eta)/16
        assert F(9, 2)/(1-zhi) <= 72/(1-eta)
        cases[eta] = (qs, qf)
        rows.append({"eta": str(eta), "z_interval": [str(zlo), str(zhi)],
                     "fast_root_interval": [str(zflo), str(zfhi)],
                     "rational_slow_cap": str(qs), "rational_fast_cap": str(qf),
                     "uniform_correction_budget": str(72/(1-eta))})
        counts["fractional_root_and_simple_pole_checks"] += 1
    return cases, rows


def fresh_trees(cases, counts):
    rows = []
    for D in (1, 3, 5, 9, 31, 63):
        for H in (8, 12, 16):
            denominator, population = 1 << H, 1 << (H-1)
            cap = [Counter(), Counter()]
            clock = [0, 0]
            separation = [0, 0]
            fused = [0, 0]
            for residue in range(denominator):
                x0, y0 = denominator+residue, denominator+residue+D
                initial_parity = x0 & 1
                x, y, a, b = x0, y0, 0, 0
                returned = False
                for t in range(1, H+1):
                    a, b = a+(x & 1), b+(y & 1)
                    x, y = step(x), step(y)
                    if a == b:
                        returned = True
                        break
                nx, ny = (1 << t)*x-3**a*x0, (1 << t)*y-3**b*y0
                assert nx >= 0 and ny >= 0
                slow, fast = ((b, ny), (a, nx)) if initial_parity else ((a, nx), (b, ny))
                sa, sn = slow
                fa, fn = fast
                k = fa-sa
                assert k >= 0 and (k == 0) == returned
                cap[initial_parity][sa, sn, fa, fn, t, k, returned] += 1
                clock[initial_parity] += t
                if returned:
                    dnext = abs(y-x)
                    assert sn <= (1 << t)*dnext+fn+3**sa*D
                    separation[initial_parity] += dnext
                    counts["returned_separation_comparisons"] += 1
                    if dnext == 0:
                        fused[initial_parity] += 1
                        if initial_parity == 0:
                            assert sn == fn+3**sa*D
                            counts["even_source_fusion_correction_identities"] += 1
                counts["direct_fresh_return_paths"] += 1
            for first, outcomes in enumerate(cap):
                assert sum(outcomes.values()) == population
                slopes = [0, 0]
                corrections = [0, 0]
                resolved_slope = resolved_slow = resolved_fast = resolved = 0
                for (sa, sn, fa, fn, t, k, returned), multiplicity in outcomes.items():
                    weight = multiplicity*(1 << (H-t))
                    slopes[0] += weight*3**sa
                    slopes[1] += weight*3**fa
                    corrections[0] += weight*sn
                    corrections[1] += weight*fn
                    if returned:
                        resolved += multiplicity
                        resolved_slope += weight*3**sa
                        resolved_slow += weight*sn
                        resolved_fast += weight*fn
                assert 2*slopes[0] == population*denominator
                assert 2*slopes[1] == 3*population*denominator
                assert 4*corrections[0] == (clock[first]-population)*denominator
                assert 4*corrections[1] == (clock[first]+population)*denominator
                assert 2*resolved_slope <= population*denominator
                assert 4*resolved_fast <= 5*population*denominator
                counts["conditional_bounded_stop_identity_groups"] += 1
                moments = []
                for eta, (qs, qf) in cases.items():
                    partial_b = [F(0), F(0)]
                    potential = [F(0), F(0)]
                    partial_slope = F(0)
                    for (sa, sn, fa, fn, t, k, returned), multiplicity in outcomes.items():
                        sl = power(F(3**sa, 1 << t), eta)[1]
                        fl = power(F(3**fa, 1 << t), eta)[1]
                        potential[0] += multiplicity*sl*qs**k
                        potential[1] += multiplicity*fl*qf**k
                        if returned:
                            partial_slope += multiplicity*sl
                            partial_b[0] += multiplicity*power(F(sn, 1 << t), eta)[1]
                            partial_b[1] += multiplicity*power(F(fn, 1 << t), eta)[1]
                    assert potential[0] <= population*power(F(1, 2), eta)[0]*qs
                    assert potential[1] <= population*power(F(3, 2), eta)[0]*qf
                    assert partial_slope <= population*power(F(1, 2), eta)[0]
                    assert partial_b[0] <= population*72/(1-eta)
                    assert partial_b[1] <= population*power(F(5, 4), eta)[0]
                    counts["stopped_fractional_potential_pairs"] += 1
                    counts["partial_return_fractional_moment_groups"] += 1
                    if H == 16 and D == 1:
                        moments.append({"eta": str(eta),
                                        "slow_moment_upper": str(partial_b[0]/population),
                                        "fast_moment_upper": str(partial_b[1]/population)})
                scale = population*denominator
                rows.append({"separation": D, "clock_cap": H, "first_input_parity": first,
                             "conditional_population": population, "returned": resolved,
                             "unresolved": population-resolved, "fused": fused[first],
                             "partial_mean_slope": str(F(resolved_slope, scale)),
                             "partial_mean_slow_correction": str(F(resolved_slow, scale)),
                             "partial_mean_fast_correction": str(F(resolved_fast, scale)),
                             "partial_mean_separation": str(F(separation[first], population)),
                             "selected_fractional_moments": moments})
        print("Exact conditional first-return trees passed for separation", D, flush=True)
    for D in (2, 4, 16, 32, 128, 1024):
        slopes, corrections, distances = [], [], []
        for n in (2, 3):
            px, py = n & 1, (n+D) & 1
            assert px == py
            slopes.append(F(3**px, 2))
            corrections.append(F(px, 2))
            distances.append(abs(step(n+D)-step(n)))
        assert sum(slopes)/2 == 1
        assert sum(corrections)/2 == F(1, 4)
        assert sum(distances)/2 == D
        counts["even_separation_one_step_laws"] += 1
    return rows


def tilted_holds(counts):
    for k in (1, 2, 3, 4, 7, 8, 15, 16):
        v = v2(3**k-1)
        for c in (-9, -1, 0, 1, 2, 17):
            for h in range(1, 11):
                population = 1 << h
                weight, held_weight = [0, 0], [0, 0]
                held_count = 0
                for residue in range(population):
                    x0 = 16*population+residue
                    y0 = 3**k*x0+c
                    x, y, a, b = x0, y0, 0, 0
                    held = True
                    for _ in range(h):
                        px, py = x & 1, y & 1
                        held = held and px == py
                        a, b = a+px, b+py
                        x, y = step(x), step(y)
                    assert held == ((y0-x0) % population == 0)
                    weight[0] += 3**a
                    weight[1] += 3**b
                    if held:
                        held_count += 1
                        held_weight[0] += 3**a
                        held_weight[1] += 3**b
                    counts["direct_tilted_holding_paths"] += 1
                assert held_count <= min(population, 2**v)
                assert weight == [4**h, 4**h]
                assert all(w <= min(4**h, 2**v*3**h) for w in held_weight)
                counts["tilted_holding_tail_pairs"] += 1
        print("Exact tilted holding cylinders passed at gap", k, flush=True)


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-return-slope-") as d:
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
                assert {n for n, _ in roots} == {"ReturnSlopeTilt."+t for t in THEOREMS}
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
    finite_walks(counts)
    cases, root_rows = fractional_roots(counts)
    print("Exact finite walk systems, correction budgets and root intervals passed.", flush=True)
    tree_rows = fresh_trees(cases, counts)
    tilted_holds(counts)
    finite = {"counts": dict(counts), "fractional_power_precision": PRECISION,
              "root_intervals": root_rows, "first_return_trees": tree_rows,
              "finite_scope": "Completed returns contribute partial moments; unresolved paths are retained in bounded-stop identities.",
              "infinite_scope": "None. Infinite means follow from the written tilt and Green argument, never from these finite partial means."}
    (OUT/"replay.json").write_text(json.dumps(finite, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_return_affine_budget.py",
             "docs/RETURN-SLOPE-TILT.md", *PRIOR,
             "results/return-slope-tilt/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated,
              "kernel_scope": ["Finite biased-walk boundary values and harmonic numerators.",
                               "Fair exit-clock arithmetic and the geometric fast-correction budget.",
                               "Polynomial root-gap and endpoint-switch identities."],
              "finite_scope": dict(counts), "floating_scope": "None in verification decisions.",
              "written_scope": ["Tilted holding times are almost surely finite; slope-weighted return mass equals the biased hitting probability.",
                                "The fresh returned slope has mean 1/2 for odd separation, conditional on either first parity, and mean 1 for even separation.",
                                "The initially odd endpoint correction has mean at most 5/4; the initially even correction and returned separation have infinite means for odd separation.",
                                "Fresh correction eta moments are at most 72/(1-eta), for 1/2<=eta<1.",
                                "Occupation coefficient/separation tails improve to O((log u)^2/u), with the improved weighted clock truncation.",
                                "The even-source return density K*_beta is not Haar L1 for beta>=1; the existing below-one separation range is sharp for L1."],
              "external_scope": "None. Local written conditional return, Green, valuation, and occupation estimates are reused.",
              "not_proved": ["An optimal Haar Lp exponent for beta<1.",
                             "Any infinite-mean statement by finite extrapolation.",
                             "Actual-gradient criterion Q, exclusion of escape or additional cycles, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts), "external_analytic_dependencies": False}, indent=2))


if __name__ == "__main__":
    main()
