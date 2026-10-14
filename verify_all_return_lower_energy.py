"""Exact finite support for the all-return lower-endpoint energy argument.

Infinite probability, entropy and Haar statements remain written proofs.
Every finite stopping tree retains its unfinished paths explicitly.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

from verify_lower_return_energy import SOURCES as LOWER_SOURCES, power
from verify_return_slope_occupation import LOG_PRECISION, log2_bounds, step, v2

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/all-return-lower-energy"
SOURCES = [*LOWER_SOURCES, "lean/ReturnSlopeOccupation.lean",
           "lean/ReturnAncestralOverlap.lean", "lean/AllReturnLowerEnergy.lean"]
THEOREMS = ["correction_age_snoc", "correction_age_bound", "fair_green_cap",
            "restart_cost_identity", "age_cost_identity", "correction_cost_caps",
            "entropy_and_clip_constants", "common_mass_identity",
            "common_occupation_identity", "grouped_mixed_drift", "mixed_drift_budget",
            "all_return_budget", "all_component_budget"]
PRIOR = ["results/lower-return-energy/verification.json",
         "results/return-ancestral-overlap/verification.json",
         "results/return-slope-tilt/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@lru_cache(None)
def three_quarters(D):
    return power(D, F(3, 4))


def arithmetic(counts):
    restart = age = 0
    raw_restart = raw_age = F(0)
    V = lambda k: 6*k*k+20*k
    for H in range(129):
        assert 2*restart+3*H*H+11*H+12 == 12*3**H
        assert 2*age+36*H**3+306*H*H+848*H+893 == 893*3**H
        assert raw_restart == F(restart, 3**(H+1)) <= 2
        assert raw_age+F(13, 3) == F(26*3**H+age, 6*3**H) <= F(315, 4)
        counts["exact_restart_and_age_series_pairs"] += 1
        k = H+1
        restart = 3*restart+3*k*k+2*k
        age = 3*age+3*(2*k+1)*V(k)+V(k+1)
        raw_restart += F(k*k, 3**k)+F(2*k, 3**(k+1))
        raw_age += F((2*k+1)*V(k), 2*3**k)+F(V(k+1), 2*3**(k+1))
    for K in range(2, 33):
        for j in range(1, K):
            row = [F(2*min(j, k)*(K-max(j, k)), K) for k in range(K+1)]
            assert row[0] == row[-1] == 0
            for k in range(1, K):
                assert row[k] == (row[k-1]+row[k+1])/2+int(k == j)
                assert row[k] <= 2*min(j, k) <= 2*k
                counts["finite_fair_green_row_values"] += 1
    m = p = z = F(1)
    sm = sp = sz = F(0)
    for j in range(129):
        assert 4*sm+10*m == 10+81*sp+30300*sz
        counts["finite_mixed_drift_telescoping_identities"] += 1
        sm, sp, sz = sm+m, sp+p, sz+z
        m, p, z = F(3, 5)*m+F(81, 10)*p+3030*z, p/2, z/2
    assert F(5, 4)+4*107 < 430
    assert 430+F(3, 5)*F(315, 4) < 480
    assert 6369*20 < 4*179**2
    assert 2034+768+108 < 3000
    assert F(5, 2)+F(85, 4)*4100+7584*257 == F(4072431, 2) < 2100000
    assert F(85, 4)*36000+7584*36864 == 280341576 < 281000000


def common_blocks(counts):
    for v in range(11):
        for odd in (1, 3, 17):
            D, pop = odd*2**v, 2**v
            Llo, Lhi = (F(w, LOG_PRECISION) for w in log2_bounds(D+1))
            Zlo = three_quarters(D)[0]
            for P in (F(1), F(3, 2), F(100)):
                final = occupation = mixed_hi = z_hi = F(0)
                for r in range(pop):
                    x, y, C = pop+r, pop+r+D, P
                    for h in range(v):
                        eps = x & 1
                        assert eps == y & 1
                        C = (3*C+1)/2 if eps else C/2
                        x, y = step(x), step(y)
                        occupation += C
                    assert v2(y-x) == 0
                    final += C
                    mixed_hi += C*F(log2_bounds(y-x+1)[1], LOG_PRECISION)
                    z_hi += three_quarters(y-x)[1]
                    counts["actual_common_parity_paths_with_formal_minimum"] += 1
                assert final/pop == P+F(v, 4)
                assert occupation/pop == v*P+F(v*(v+1), 8)
                assert occupation/pop <= P*Llo+9*Zlo
                if v:
                    assert mixed_hi/pop <= F(6, 5)*P*Llo+F(2, 5)*Llo**2
                    assert z_hi/pop <= Zlo
                counts["common_block_mean_occupation_and_mixed_bounds"] += 1


def prefix_restarts(counts):
    """Test the new correction restart bound at actual nonzero-gap prefixes."""
    prefixes = []
    for t in (1, 3, 5, 7):
        selected = Counter()
        for r in range(2**t):
            x, y, a, b = r, r+1, 0, 0
            alive = True
            for _ in range(t):
                a, b = a+(x & 1), b+(y & 1)
                x, y = step(x), step(y)
                if a == b:
                    alive = False
                    break
            if not alive:
                continue
            k = abs(a-b)
            key = k, r & 1
            if selected[key] >= 2:
                continue
            selected[key] += 1
            fast = (x, a) if r & 1 else (y, b)
            slow = (y, b) if r & 1 else (x, a)
            assert fast[1]-slow[1] == k
            prefixes.append((t, r, k, fast, slow))
    rows = []
    H, pop = 10, 2**10
    for t, r, k, (xf, af), (xs, ass) in prefixes:
        correction = slope = slope_age = unfinished = 0
        for q in range(pop, 2*pop):
            x, y = xf+3**af*q, xs+3**ass*q
            gap, a, N = k, 0, 0
            done = False
            for h in range(1, H+1):
                ep, eq = x & 1, y & 1
                gap, a = gap+ep-eq, a+ep
                N = 3**ep*N+ep*2**(h-1)
                x, y = step(x), step(y)
                if gap == 0:
                    done = True
                    break
            if done:
                correction += N*2**(H-h)
                slope += 3**a*2**(H-h)
                slope_age += h*3**a*2**(H-h)
            else:
                unfinished += 1
            counts["actual_positive_gap_restart_paths"] += 1
        assert correction <= 2*pop*pop
        assert 3**k*slope <= pop*pop
        assert 3**k*slope_age <= (6*k*k+20*k)*pop*pop
        counts["conditional_positive_gap_restart_budgets"] += 1
        rows.append({"prefix_clock": t, "prefix_residue": r, "gap": k,
                     "continuation_cap": H, "unfinished_at_cap": unfinished,
                     "partial_new_fast_correction": str(F(correction, pop*pop)),
                     "partial_remaining_slope_clock": str(F(slope_age, pop*pop))})
    return rows


def fresh_returns(counts):
    rows = []
    audited = set()
    for D in (1, 3, 9, 31):
        Llo = F(log2_bounds(D+1)[0], LOG_PRECISION)
        Zlo = three_quarters(D)[0]
        for H in (8, 12, 16):
            pop, scale = 2**H, 2**(2*H-1)
            costs = [Counter(), Counter()]
            clips = [F(0), F(0)]
            for r in range(pop):
                x, y = pop+r, pop+r+D
                a = b = N0 = N1 = age0 = age1 = 0
                word0, word1 = [], []
                done = False
                for t in range(1, H+1):
                    ep, eq = x & 1, y & 1
                    word0.append(ep)
                    word1.append(eq)
                    age0, age1 = 3**ep*(age0+N0), 3**eq*(age1+N1)
                    N0, N1 = 3**ep*N0+ep*2**(t-1), 3**eq*N1+eq*2**(t-1)
                    a, b = a+ep, b+eq
                    x, y = step(x), step(y)
                    if a == b:
                        done = True
                        break
                row = costs[r & 1]
                counts["direct_fresh_return_paths"] += 1
                if not done:
                    row["unfinished"] += 1
                    continue
                fast, slow = (N0, N1) if r & 1 else (N1, N0)
                fast_age = age0 if r & 1 else age1
                word = word0 if r & 1 else word1
                multiplier = 2**(H-t)
                logfast_hi = max(0, log2_bounds(fast)[1]-t*LOG_PRECISION)
                row["fast"] += fast*multiplier
                row["age"] += fast_age*multiplier
                row["entropy"] += fast*multiplier*logfast_hi
                row["log_clock"] += fast*multiplier*log2_bounds(t)[1]
                row["slope_clock_square"] += 3**a*t*t*multiplier
                clip = min(slow, 3**a*D)
                row["clip_clock"] += clip*t*multiplier
                clips[r & 1] += F(clip*clip*multiplier, 3**a)
                for h in (1, 2, 4, 8):
                    if t > 2*h:
                        row["tail", h] += fast*multiplier
                DD = abs(y-x)
                logD_hi = log2_bounds(DD+1)[1]
                correction = min(N0, 3**a*D+N1)
                for P in (F(1), F(3, 2), F(17)):
                    row["mixed", P] += (3**a*P+correction)*multiplier*logD_hi
                key = D, t, r % 2**t
                if key not in audited:
                    audited.add(key)
                    suffix = a
                    ns = ages = log_sum_lo = 0
                    for j, eps in enumerate(word):
                        suffix -= eps
                        if eps:
                            wn = 3**suffix*2**j
                            ns += wn
                            ages += wn*(t-j-1)
                            log_sum_lo += wn*max(0, log2_bounds(wn)[0]-t*LOG_PRECISION)
                    assert ns == fast and ages == fast_age <= (t-1)*fast
                    assert fast*logfast_hi <= log_sum_lo+fast*log2_bounds(t)[0]
                    counts["independent_suffix_age_and_entropy_checks"] += 1
            for parity, row in enumerate(costs):
                assert F(row["fast"], scale) <= F(5, 4)
                assert F(row["age"], scale) <= F(315, 4)
                assert F(row["entropy"], scale*LOG_PRECISION) <= 480
                assert F(row["log_clock"], scale*LOG_PRECISION) <= 430
                assert F(row["slope_clock_square"], scale) <= F(6369, 2)
                assert clips[parity]/scale <= 10*Zlo**2
                assert F(row["clip_clock"], scale) <= 179*Zlo
                for h in (1, 2, 4, 8):
                    assert F(row["tail", h], scale) <= F(315, 4*h)+28/power(h, F(1, 2))[1]
                    counts["conditional_partial_fast_clock_tail_bounds"] += 1
                for P in (F(1), F(3, 2), F(17)):
                    assert row["mixed", P]/(scale*LOG_PRECISION) <= (
                        P*Llo/2+F(81, 10)*P+3000*Zlo)
                    counts["conditional_partial_fresh_mixed_drift_bounds"] += 1
                counts["conditional_entropy_age_and_clipped_moment_budgets"] += 1
                rows.append({"D": D, "H": H, "lower_initial_parity": parity,
                             "unfinished_at_cap": row["unfinished"],
                             "partial_fast_correction": str(F(row["fast"], scale)),
                             "partial_fast_age_cost": str(F(row["age"], scale)),
                             "partial_fast_entropy_upper": str(F(row["entropy"], scale*LOG_PRECISION)),
                             "partial_clipped_clock_cost": str(F(row["clip_clock"], scale))})
            print("Exact fresh entropy and mixed costs passed:", D, H, flush=True)
    return rows


def all_components(counts):
    rows = []
    for H in (8, 12, 16):
        pop, scale = 2**H, 4**H
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
                counts["actual_equal_count_formal_minimum_identities"] += 1
                if D == 0:
                    fused = True
                    break
                grouped = bool(last_D & 1)
                if grouped:
                    j += 1
                    if len(groups) <= j:
                        groups.append(Counter())
                    groups[j][t, D, P] += 1
                if r % 2 == 0:
                    rr = r % 2**t
                    e = int(y < x)
                    NN = N1 if e else N0
                    assert rr+e < 2**t and 3**a+NN <= P
                    data = (a, min(x, y) % 3**a, P, NN, rr+e, D, grouped)
                    key = t, rr
                    if key in columns:
                        assert columns[key] == data
                    else:
                        columns[key] = data
                    counts["even_source_all_return_path_visits"] += 1
                last_D = D
            unfinished += not fused
            counts["direct_all_return_paths"] += 1
        ps, mslo, mshi, zslo = [], [], [], []
        for group in groups:
            ps.append(F(sum(m*P*2**(H-t) for (t, D, P), m in group.items()), scale))
            mslo.append(F(sum(m*P*2**(H-t)*log2_bounds(D+1)[0]
                              for (t, D, P), m in group.items()), scale*LOG_PRECISION))
            mshi.append(F(sum(m*P*2**(H-t)*log2_bounds(D+1)[1]
                              for (t, D, P), m in group.items()), scale*LOG_PRECISION))
            zslo.append(sum((m*three_quarters(D)[0] for (t, D, P), m in group.items()), F(0))/pop)
        for j in range(len(groups)-1):
            assert 10*mshi[j+1] <= 6*mslo[j]+81*ps[j]+30300*zslo[j]
            counts["capped_actual_group_mixed_drift_bounds"] += 1
        components, heights = defaultdict(list), Counter()
        diagonal = coefficient = augmented = one_step_cost = grouped_cost = 0
        for (t, r), (a, y, P, NN, endpoint, D, grouped) in columns.items():
            components[t, a].append((y, NN, endpoint))
            heights[a, y] += 3**a*2**(H-t)
            diagonal += 3**a*4**(H-t)
            coefficient += P*4**(H-t)
            augmented += (3**a+NN)*4**(H-t)
            if grouped:
                grouped_cost += P*4**(H-t)
            else:
                one_step_cost += P*4**(H-t)
        energy = 0
        for (t, a), items in components.items():
            assert len({e for _, _, e in items}) == len(items)
            fibres = defaultdict(list)
            for y, NN, endpoint in items:
                fibres[y].append(NN)
            piece = 0
            for fibre in fibres.values():
                quotients = [NN//3**a for NN in fibre]
                assert len(set(quotients)) == len(quotients)
                assert 3**a*len(fibre)**2 <= 2*sum(3**a+NN for NN in fibre)
                piece += 3**a*len(fibre)**2
                counts["all_return_lower_fibre_injection_bounds"] += 1
            energy += piece*4**(H-t)
            counts["complete_all_return_component_energy_bounds"] += 1
        assert energy <= 2*augmented <= 2*coefficient
        assert one_step_cost+grouped_cost == coefficient
        full = 0
        for (a, y), height in heights.items():
            ancestors = sum(heights[k, y % 3**k] for k in range(a))
            full += (height//3**a)*(height+2*ancestors)
        nested = 0
        for (t, r), (a, y, *_rest) in columns.items():
            for s in range(1, t):
                ancestor = columns.get((s, r % 2**s))
                if ancestor is not None:
                    b, x, *_rest2 = ancestor
                    assert b <= a
                    if (y-x) % 3**b == 0:
                        nested += 2*3**b*2**(2*H-t-s)
                        counts["compatible_nested_lower_image_pairs"] += 1
        remaining = full-energy-nested
        assert diagonal <= energy and remaining >= 0
        if H <= 12:
            direct = same = ancestor_sum = rest_sum = 0
            for (t, r), (a, x, *_rest) in columns.items():
                for (s, u), (b, y, *_rest2) in columns.items():
                    if (x-y) % 3**min(a, b):
                        continue
                    value = 3**min(a, b)*2**(2*H-t-s)
                    direct += value
                    if (t, a) == (s, b):
                        same += value
                    elif t != s and (r-u) % 2**min(t, s) == 0:
                        ancestor_sum += value
                    else:
                        rest_sum += value
                    counts["independent_positive_all_return_pair_products"] += 1
            assert (direct, same, ancestor_sum, rest_sum) == (full, energy, nested, remaining)
            counts["independent_full_energy_three_way_decompositions"] += 1
        rows.append({"H": H, "population": pop, "unfinished_at_cap": unfinished,
                     "all_return_columns": len(columns), "components": len(components),
                     "common_parity_columns": sum(not d[-1] for d in columns.values()),
                     "group_start_mixed_cost_upper": str(sum(mshi)),
                     "all_return_minimum_cost": str(F(coefficient, scale)),
                     "grouped_minimum_cost": str(F(grouped_cost, scale)),
                     "common_parity_minimum_cost": str(F(one_step_cost, scale)),
                     "chosen_endpoint_augmented_cost": str(F(augmented, scale)),
                     "column_diagonal": str(F(diagonal, scale)),
                     "sum_complete_component_squared_norms": str(F(energy, scale)),
                     "within_component_cross_energy": str(F(energy-diagonal, scale)),
                     "nested_source_cross_energy": str(F(nested, scale)),
                     "disjoint_source_cross_component_energy": str(F(remaining, scale)),
                     "full_truncated_squared_norm": str(F(full, scale))})
        print("Exact all-return lower image decomposition passed through", H, flush=True)
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-all-return-lower-") as d:
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
                assert {n for n, _ in roots} == {"AllReturnLowerEnergy."+t for t in THEOREMS}
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
    arithmetic(counts)
    common_blocks(counts)
    restarts = prefix_restarts(counts)
    fresh = fresh_returns(counts)
    components = all_components(counts)
    replay = {"counts": dict(counts), "logarithm_precision": LOG_PRECISION,
              "positive_gap_restart_checks": restarts,
              "fresh_return_checks": fresh, "all_return_component_checks": components,
              "infinite_scope": "None. Entropy, mixed moments and infinite component energy are written arguments."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_lower_return_energy.py",
             "verify_return_affine_budget.py", "verify_return_slope_occupation.py",
             "docs/ALL-RETURN-LOWER-ENERGY.md", *PRIOR,
             "results/all-return-lower-energy/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Actual correction-age recurrence and finite Green cap.",
                               "All-depth correction/age geometric sums with explicit remainders.",
                               "Exact common-block mean and occupation recurrences.",
                               "Finite mixed-drift telescoping and energy constants."],
              "written_scope": ["The initially odd correction has E[b_F log2_+ b_F] <= 480.",
                                "A summable group-start mixed moment P log2(D+1).",
                                "All nonfused lower formal endpoints, including common-parity returns, have total mean <= 2100000+281000000*C_star.",
                                "The complete clock/count component squared norms sum to at most 4200000+562000000*C_star.",
                                "Only disjoint-source cross-component terms remain in the lower-density L2 decomposition after reusing the nested-source budget."],
              "external_scope": "None. Earlier local written stopping and occupation arguments are reused.",
              "not_proved": ["A full L2 bound for the lower-image density or the original fixed-endpoint density.",
                             "Ordinary-integer sampling at infinite cutoff, actual-gradient control, Q, escape or other-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
