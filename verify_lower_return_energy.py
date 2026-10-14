"""Exact support for the written lower-endpoint grouped-return budget.

Finite checks do not settle the infinite moment or cross-component energy.
Unfinished paths remain unfinished; fractional values use rational enclosures.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

from verify_return_affine_budget import SOURCES as AFFINE_SOURCES, PRECISION, power_bounds
from verify_return_slope_occupation import LOG_PRECISION, log2_bounds

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/lower-return-energy"
SOURCES = [*AFFINE_SOURCES, "lean/ReturnSlopeTilt.lean", "lean/LowerReturnEnergy.lean"]
THEOREMS = ["lower_formal_identity", "lower_endpoint_augmented",
            "selected_even_source_injective", "selected_even_source_in_period",
            "lower_continuation_bound", "root_chord_endpoints",
            "geometric_numerator_identity", "grouped_minimum_drift",
            "grouped_minimum_budget", "lower_budget_constants", "component_energy_budget"]
PRIOR = ["results/return-affine-budget/verification.json",
         "results/return-slope-tilt/verification.json",
         "results/return-correction-moments/verification.json"]
ETAS = (F(1, 2), F(3, 4), F(7, 8), F(15, 16))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def power(value, eta):
    value = F(value)
    lo, hi = power_bounds(value.numerator, value.denominator, eta)
    return F(lo, PRECISION), F(hi, PRECISION)


def arithmetic_and_perpetuities(counts):
    assert 128**2 < 2*91**2 and 3*128**2 < 2*157**2
    assert 91+157 == 248
    for p in range(8):
        for d in range(16):
            for slow in range(32):
                for fast in range(16):
                    assert min(p+slow, p+d+fast) <= p+fast+min(slow, d)
                    counts["integer_minimum_continuation_bounds"] += 1
    for r in range(8):
        for s in range(r+1, 10):
            g = 0
            for h in range(65):
                assert s*g+r**h == r*g+s**h
                counts["exact_geometric_identity_checks"] += 1
                g = s*g+r**h
    p, q, ell = F(1), F(1), F(1)
    sp = sq = sl = F(0)
    for h in range(129):
        assert 4*sp+8*p == 8+49*sl+10*sq
        counts["finite_group_minimum_telescoping_checks"] += 1
        sp, sq, sl = sp+p, sq+q, sl+ell
        p, q, ell = p/2+F(49, 8)*ell+F(5, 4)*q, q/2, F(h+2, 2**(h+1))
    rows = []
    for eta in ETAS:
        u = 1-eta
        rhi = (power(F(1, 2), u)[1]+power(F(3, 2), u)[1])/2
        assert rhi <= 1-u/16 < 1
        numerator_hi = power(3, u)[1]/4
        moment_hi = numerator_hi/(1-rhi)
        clipped_coefficient_hi = power(2, eta)[1]*moment_hi/2
        assert clipped_coefficient_hi <= 6/u
        counts["reciprocal_moment_chord_and_clipping_checks"] += 1
        for H in (6, 10):
            # All parity words, enumerated without Collatz source iteration.
            words = [(0, 0)]
            for t in range(H):
                words = [(N, a) for N, a in words] + [
                    (3*N+2**t, a+1) for N, a in words]
            upper = F(0)
            for N, a in words:
                upper += F(3**a, 4**H)*power(F(N, 3**a), eta)[1]
                counts["direct_tilted_perpetuity_words"] += 1
            assert upper <= moment_hi
            rows.append({"eta": str(eta), "H": H, "partial_moment_upper": str(upper),
                         "geometric_moment_upper": str(moment_hi),
                         "clipped_coefficient_upper": str(clipped_coefficient_hi)})
    return rows


def zero_gap_blocks(counts):
    for v in range(11):
        for odd in (1, 3, 5, 17):
            D = odd*2**v
            pop = 2**v
            p_sum = F(0)
            d_sum = 0
            log_sum_hi = 0
            for r in range(pop):
                x0 = pop+r
                x, y, a, N = x0, x0+D, 0, 0
                for t in range(v):
                    eps = x & 1
                    assert eps == y & 1
                    N = 3**eps*N+eps*2**t
                    a += eps
                    x, y = step(x), step(y)
                assert y-x == odd*3**a
                p_sum += F(3**a+N, 2**v)
                d_sum += y-x
                log_sum_hi += log2_bounds(y-x+1)[1]
                counts["direct_zero_gap_minimum_paths"] += 1
            assert p_sum/pop == 1+F(v, 4)
            assert d_sum == pop*D
            if v:
                assert log_sum_hi <= pop*log2_bounds(D+1)[0]
            counts["zero_gap_mean_and_logarithmic_drift_groups"] += 1


def fresh_returns(counts):
    rows = []
    for D in (1, 3, 5, 9, 31, 63):
        ell_lo = F(log2_bounds(D+1)[0], LOG_PRECISION)
        for H in (8, 12, 16):
            pop = 2**H
            scale = pop**2//2
            costs = [Counter(), Counter()]
            for r in range(pop):
                x0 = pop+r
                x, y = x0, x0+D
                a = b = N0 = N1 = 0
                done = False
                for t in range(1, H+1):
                    ep, eq = x & 1, y & 1
                    N0, N1 = 3**ep*N0+ep*2**(t-1), 3**eq*N1+eq*2**(t-1)
                    a, b = a+ep, b+eq
                    x, y = step(x), step(y)
                    if a == b:
                        done = True
                        break
                row = costs[r & 1]
                if not done:
                    row["unfinished"] += 1
                else:
                    assert 2**t*x == 3**a*x0+N0
                    assert 2**t*y == 3**a*(x0+D)+N1
                    slow, fast = (N0, N1) if r % 2 == 0 else (N1, N0)
                    assert slow % 2 == 0
                    clip = min(slow, 3**a*D)
                    multiplier = 2**(H-t)
                    row["clip"] += multiplier*clip
                    row["fast"] += multiplier*fast
                    row["slope"] += multiplier*3**a
                    row["minimum"] += multiplier*min(3**a+N0, (D+1)*3**a+N1)
                    assert F(clip, 3**a) == min(F(slow, 3**a), D)
                    counts["returned_clipping_and_formal_minimum_identities"] += 1
                counts["direct_fresh_return_paths"] += 1
            for parity, row in enumerate(costs):
                assert F(row["clip"], scale) <= 12*ell_lo
                assert 4*row["fast"] <= 5*scale
                assert 2*row["slope"] <= scale
                if D == 1:
                    assert 4*row["minimum"] <= (9 if parity == 0 else 7)*scale
                counts["fresh_conditional_clipping_and_fast_budgets"] += 1
                rows.append({"D": D, "H": H, "initial_lower_parity": parity,
                             "unfinished": row["unfinished"],
                             "partial_clipped_correction": str(F(row["clip"], scale)),
                             "partial_fast_correction": str(F(row["fast"], scale)),
                             "partial_formal_minimum": str(F(row["minimum"], scale))})
            assert F(costs[0]["minimum"]+costs[1]["minimum"], 2*scale) <= (
                F(7, 4)+6*ell_lo)
    return rows


def grouped_components(counts):
    rows = []
    for H in (8, 12, 16):
        pop = 2**H
        scale = pop**2
        groups = [Counter()]
        columns = {}
        unfinished = 0
        for r in range(pop):
            x0 = pop+r
            x, y = x0, x0+1
            a = b = N0 = N1 = j = 0
            last_D = 1
            groups[0][0, 1, 1] += 1
            fused = False
            for t in range(1, H+1):
                ep, eq = x & 1, y & 1
                N0, N1 = 3**ep*N0+ep*2**(t-1), 3**eq*N1+eq*2**(t-1)
                a, b = a+ep, b+eq
                x, y = step(x), step(y)
                if a != b:
                    continue
                D = abs(y-x)
                P = min(3**a+N0, 2*3**a+N1)
                assert 2**t*min(x, y)+3**a == 3**a*x0+P
                counts["actual_equal_count_lower_formal_identities"] += 1
                if D == 0:
                    fused = True
                    break
                if last_D & 1:
                    j += 1
                    if len(groups) <= j:
                        groups.append(Counter())
                    groups[j][t, D, P] += 1
                    if r % 2 == 0:
                        rr = r % 2**t
                        e = int(y < x)
                        endpoint_N = N1 if e else N0
                        assert rr+e < 2**t
                        assert 3**a+endpoint_N <= P
                        data = (a, min(x, y) % 3**a, P, endpoint_N, rr+e, D)
                        key = t, rr
                        if key in columns:
                            assert columns[key] == data
                        else:
                            columns[key] = data
                        counts["even_source_grouped_return_path_visits"] += 1
                last_D = D
            unfinished += not fused
            counts["direct_all_grouped_paths"] += 1
        ps, qs, ls = [], [], []
        for group in groups:
            ps.append(sum(m*P*2**(H-t) for (t, D, P), m in group.items()))
            qs.append(sum(group.values())*pop)
            ls.append(sum(m*pop*log2_bounds(D+1)[0] for (t, D, P), m in group.items()))
        for j in range(len(groups)-1):
            assert 8*ps[j+1]*LOG_PRECISION <= (
                4*ps[j]*LOG_PRECISION+49*ls[j]+10*qs[j]*LOG_PRECISION)
            counts["capped_actual_group_minimum_drift_checks"] += 1
        components = defaultdict(list)
        heights = Counter()
        diag = coefficient_cost = augmented_cost = 0
        for (t, r), (a, y, P, endpoint_N, endpoint, D) in columns.items():
            components[t, a].append((y, endpoint_N, endpoint, P))
            heights[a, y] += 3**a*2**(H-t)
            diag += 3**a*4**(H-t)
            coefficient_cost += P*4**(H-t)
            augmented_cost += (3**a+endpoint_N)*4**(H-t)
        energy = 0
        for (t, a), items in components.items():
            assert len({e for _, _, e, _ in items}) == len(items)
            fibres = defaultdict(list)
            for y, endpoint_N, endpoint, P in items:
                fibres[y].append((endpoint_N, endpoint))
            component_energy = 0
            for y, fibre in fibres.items():
                quotients = [N//3**a for N, _ in fibre]
                assert len(set(quotients)) == len(quotients)
                assert len(fibre)**2*3**a <= 2*sum(3**a+N for N, _ in fibre)
                component_energy += 3**a*len(fibre)**2
                counts["exact_lower_image_fibre_rank_checks"] += 1
            assert component_energy <= 2*sum(3**a+N for _, N, _, _ in items)
            energy += component_energy*4**(H-t)
            counts["entire_clock_count_component_energy_bounds"] += 1
        assert energy <= 2*augmented_cost <= 2*coefficient_cost
        assert coefficient_cost <= sum(ps[1:])
        full = 0
        for (a, y), height in heights.items():
            ancestors = sum(heights[k, y % 3**k] for k in range(a))
            assert height % 3**a == 0
            full += (height//3**a)*(height+2*ancestors)
        assert diag <= energy <= full
        if H <= 12:
            direct = 0
            direct_same_component = 0
            items = list(columns.items())
            for (t, r), (a, x, *_rest) in items:
                for (s, u), (b, y, *_rest2) in items:
                    depth = min(a, b)
                    if (x-y) % 3**depth == 0:
                        value = 3**depth*2**(2*H-t-s)
                        direct += value
                        if (t, a) == (s, b):
                            direct_same_component += value
                        counts["independent_positive_lower_column_products"] += 1
            assert direct == full and direct_same_component == energy
            counts["independent_full_lower_energy_decompositions"] += 1
        rows.append({"H": H, "population": pop, "unfinished_at_cap": unfinished,
                     "selected_columns": len(columns), "clock_count_components": len(components),
                     "all_source_group_start_minimum_sum": str(F(sum(ps), scale)),
                     "even_grouped_minimum_cost": str(F(coefficient_cost, scale)),
                     "even_selected_endpoint_augmented_cost": str(F(augmented_cost, scale)),
                     "individual_column_diagonal": str(F(diag, scale)),
                     "sum_full_component_squared_norms": str(F(energy, scale)),
                     "within_component_disjoint_source_cross": str(F(energy-diag, scale)),
                     "cross_component_energy": str(F(full-energy, scale)),
                     "full_truncated_squared_norm": str(F(full, scale))})
        print("Exact lower-endpoint grouped components passed through clock", H, flush=True)
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-lower-return-energy-") as d:
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
                assert {n for n, _ in roots} == {"LowerReturnEnergy."+t for t in THEOREMS}
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
        prior = json.loads((ROOT/name).read_text())
        assert prior["status"] == "passed", name
        for path, expected in prior["sha256"].items():
            assert digest(ROOT/path) == expected, path
        validated[name] = len(prior["sha256"])
    version, builds = build()
    counts = Counter()
    perpetuities = arithmetic_and_perpetuities(counts)
    zero_gap_blocks(counts)
    fresh = fresh_returns(counts)
    components = grouped_components(counts)
    replay = {"counts": dict(counts), "power_precision": PRECISION,
              "logarithm_precision": LOG_PRECISION, "perpetuity_checks": perpetuities,
              "fresh_return_checks": fresh, "grouped_component_checks": components,
              "infinite_scope": "None. The clipped correction, grouped coefficient sum and infinite component energy remain written."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_return_affine_budget.py",
             "verify_return_slope_occupation.py", "docs/LOWER-RETURN-ENERGY.md",
             *PRIOR, "results/lower-return-energy/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Exact smaller formal endpoint and selected endpoint coefficient.",
                               "Injectivity and full-period retention of chosen endpoints of even sources.",
                               "Minimum continuation, geometric sums, root comparisons and finite grouped drift arithmetic."],
              "written_scope": ["The fresh clipped initially even correction has mean at most 12 log2(D+1).",
                                "The minimum formal coefficient summed over nonfused grouped returns has mean at most 4100+36000*C_star.",
                                "The sum of complete fixed-clock, fixed-count squared norms of the lower grouped-return image components is at most 8200+72000*C_star."],
              "external_scope": "None. Earlier local written slope-tilt and occupation arguments are reused.",
              "not_proved": ["A full L2 norm bound for the sum of these components.",
                             "The same coefficient budget over every intervening one-step return, or the original fixed-endpoint density.",
                             "A complete actual-gradient transport, Q, escape exclusion, exclusion of additional cycles, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
