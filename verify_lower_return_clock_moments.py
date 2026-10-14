"""Exact finite support for joint lower-coefficient/total-clock moments.

Probability limits, Holder and infinite Lp conclusions remain written.
Completed prefixes are counted with their exact binary masses.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import comb
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time

from verify_all_return_lower_energy import SOURCES as ALL_SOURCES
from verify_lower_return_energy import power
from verify_return_affine_budget import PRECISION
from verify_return_slope_occupation import LOG_PRECISION, LN2_LO, LN2_HI, log2_bounds, step

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/lower-return-clock-moments"
SOURCES = [*ALL_SOURCES, "lean/LowerReturnClockMoments.lean"]
THEOREMS = ["lower_augmented_le_first", "lower_augmented_lift", "selected_endpoint_count",
            "group_duration_budget", "clocked_minimum_budget", "power_window", "atypical_window"]
PRIOR = ["results/all-return-lower-energy/verification.json",
         "results/return-slope-tilt/verification.json",
         "results/return-occupation-density/verification.json",
         "results/return-affine-budget/verification.json"]
QS = (F(1, 4), F(3, 8), F(7, 16))
PS = (F(9, 8), F(5, 4), F(13, 10))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


@lru_cache(None)
def pw(x, exponent):
    return power(F(x), exponent)


@lru_cache(None)
def lg(D):
    return tuple(F(x, LOG_PRECISION) for x in log2_bounds(D+1))


def fq(q):
    ratio_hi = 1/pw(2, F(1, 2)-q)[0]
    assert ratio_hi < 1
    return F(5, 4)*pw(2, q)[1]+107*pw(2, 2*q)[1]/(1-ratio_hi)


def arithmetic(counts):
    for d in range(1, 129):
        for a in range((d-1)//3+1):
            q = F(d+3*a, 4*d)
            assert F(3*a, 2*d) < q < F(1, 2)
            assert 18*a < 7*d
            assert F(7*d-18*a, d+a) > F(d-3*a, 2*(d+a))
            counts["rational_norm_and_tail_exponent_windows"] += 1
    for q in QS:
        Fq = fq(q)
        ratio_hi = 1/pw(2, F(1, 2)-q)[0]
        partial = F(5, 4)*pw(2, q)[1]
        for j in range(1, 129):
            partial += 107*pw(2, 2*q)[1]*ratio_hi**(j-1)
            assert partial <= Fq
            counts["finite_fast_clock_geometric_sums"] += 1
        R = L = T = M = P = Z = Q = F(1)
        sums = [F(0)]*7
        for j in range(65):
            sr, sl, st, sm, sp, sz, sq = sums
            assert 4*sr+8*R == 8+49*sl+10*st+4*sm+108*sp+4864*sz+8*Fq*sq
            counts["clocked_group_finite_telescoping_checks"] += 1
            sums = [u+v for u, v in zip(sums, (R, L, T, M, P, Z, Q))]
            R = R/2+F(49, 8)*L+F(5, 4)*T+M/2+F(27, 2)*P+608*Z+Fq*Q
            L, T, M, P, Z, Q = (x/2 for x in (L, T, M, P, Z, Q))
    for t in range(1, 257):
        loglo, loghi = log2_bounds(t+2)
        lb = 16*t*F(loglo, LOG_PRECISION)*LN2_LO
        ub = 16*t*F(loghi, LOG_PRECISION)*LN2_HI
        exceptional = 0
        for a in range(t+1):
            diff2 = (2*a-t)**2
            assert diff2 <= lb or diff2 > ub
            if diff2 > ub:
                exceptional += comb(t, a)
        assert exceptional*(t+2)**8 <= 2*2**t
        counts["exact_binomial_exceptional_count_bounds"] += 1


def common_power_blocks(counts):
    for P in (F(1), F(3, 2), F(17)):
        words = [P]
        moments = {theta: [F(0)] for theta in (F(1, 4), F(3, 4))}
        for h in range(1, 9):
            words = [y for x in words for y in (x/2, (3*x+1)/2)]
            assert sum(words)/len(words) == P+F(h, 4)
            for theta in moments:
                moments[theta].append(sum((pw(x, theta)[1] for x in words), F(0))/len(words))
            counts["complete_common_word_mean_checks"] += 1
        for v in range(1, 9):
            Llo = lg(2**v)[0]
            for theta, means in moments.items():
                for q in (QS[0], QS[-1]):
                    for S in (0, 8, 64):
                        lhs = sum((means[h]*pw(1+S+h, q)[1] for h in range(1, v+1)), F(0))
                        rhs = (Llo*pw(P, theta)[0]*pw(1+S, q)[0]
                               +pw(P, theta)[0]*pw(Llo, q+1)[0]
                               +pw(Llo, theta+1)[0]*pw(1+S, q)[0]
                               +pw(Llo, q+theta+1)[0])
                        assert lhs <= rhs
                        counts["fractional_common_block_clock_bounds"] += 1


def enumerate_returns(H, counts):
    pop = 2**H
    starts, ends, columns = [Counter()], [Counter()], {}
    unfinished = 0
    for r in range(pop):
        x0 = pop+r
        x, y, a, b, N0, N1 = x0, x0+1, 0, 0, 0, 0
        j, group_clock, last_D = 0, 0, 1
        starts[0][0, 1, 1] += 1
        fused = False
        for t in range(1, H+1):
            ep, eq = x & 1, y & 1
            N0, N1 = 3**ep*N0+ep*2**(t-1), 3**eq*N1+eq*2**(t-1)
            x, y = step(x), step(y)
            a, b = a+ep, b+eq
            if a != b:
                continue
            D = abs(y-x)
            Pnum = min(3**a+N0, 2*3**a+N1)
            assert Pnum <= 3**a+N0
            assert 2**t*min(x, y)+3**a == 3**a*x0+Pnum
            counts["lower_first_coefficient_and_formal_identities"] += 1
            grouped = bool(last_D & 1)
            if grouped:
                ends[j][t, t-group_clock, Pnum] += 1
            if D == 0:
                assert grouped
                fused = True
                break
            if grouped:
                j += 1
                group_clock = t
                if len(starts) <= j:
                    starts.append(Counter())
                    ends.append(Counter())
                starts[j][t, D, Pnum] += 1
            if r % 2 == 0:
                rr = r % 2**t
                e = int(y < x)
                assert rr+e < 2**t
                chosen_N = N1 if e else N0
                assert 3**a+chosen_N <= Pnum
                key, data = (t, rr), (a, min(x, y) % 3**a, Pnum, chosen_N, rr+e)
                if key in columns:
                    assert columns[key] == data
                else:
                    columns[key] = data
            last_D = D
        unfinished += not fused
        counts["actual_pair_paths"] += 1
    return starts, ends, columns, unfinished


def group_moments(H, starts, ends, counts):
    pop = 2**H
    rows = []
    for q in QS:
        stats = []
        for group in starts:
            row = Counter()
            for (S, D, Pnum), mass in group.items():
                probability, P = F(mass, pop), F(Pnum, 2**S)
                slo, shi = pw(1+S, q)
                llo = lg(D)[0]
                row["probability"] += probability
                row["P"] += probability*P
                row["PL"] += probability*P*llo
                row["Z"] += probability*pw(D, F(3, 4))[0]
                row["Rlo"] += probability*P*slo
                row["Rhi"] += probability*P*shi
                row["clock"] += probability*slo
                row["clock_log"] += probability*slo*llo
            stats.append(row)
        duration_sum = F(0)
        for j, end in enumerate(ends):
            duration = sum((F(mass*Pnum, pop*2**t)*pw(G, q)[1]
                            for (t, G, Pnum), mass in end.items()), F(0))
            row = stats[j]
            budget = row["PL"]/2+F(27, 2)*row["P"]+608*row["Z"]+fq(q)*row["probability"]
            assert duration <= budget
            counts["actual_group_duration_power_budgets"] += 1
            duration_sum += duration
            if j+1 < len(stats):
                rhs = row["Rlo"]/2+F(49, 8)*row["clock_log"]+F(5, 4)*row["clock"]+budget
                assert stats[j+1]["Rhi"] <= rhs
                counts["actual_total_clock_group_drift_bounds"] += 1
        rows.append({"q": str(q), "group_start_clocked_P_upper": str(sum(r["Rhi"] for r in stats)),
                     "completed_group_duration_cost_upper": str(duration_sum)})
    return rows


def heights_from(columns):
    heights = Counter()
    for (t, _), (a, y, *_rest) in columns.items():
        heights[a, y] += F(3**a, 2**t)
    return heights


def norm_bounds(heights, p):
    lo = hi = F(0)
    for (a, y), height in heights.items():
        above = sum((heights.get((b, y % 3**b), F(0)) for b in range(a)), F(0))
        low, high = pw(above+height, p)
        oldlo, oldhi = pw(above, p)
        lo += (low-oldhi)/3**a
        hi += (high-oldlo)/3**a
    return max(F(0), lo), hi


def image_moments(H, columns, counts):
    components = defaultdict(list)
    for (t, _), (a, y, Pnum, NN, endpoint) in columns.items():
        components[t, a].append((y, Pnum, NN, endpoint))
    heights = heights_from(columns)
    rows = []
    for p in PS:
        alpha = p-1
        component_sum_hi = F(0)
        for (t, a), items in components.items():
            assert len({v[3] for v in items}) == len(items)
            fibres = Counter(y for y, *_rest in items)
            lhs = sum((pw(F(m*3**a, 2**t), p)[1]/3**a for m in fibres.values()), F(0))
            rhs = p*sum((pw(F(Pnum, 2**t), alpha)[0]/2**t
                          for _, Pnum, _, _ in items), F(0))
            assert lhs <= rhs
            component_sum_hi += lhs
            counts["entire_fractional_component_fibre_bounds"] += 1
        full_lo, full_hi = norm_bounds(heights, p)
        if H <= 12 and heights:
            A = max(a for a, _ in heights)
            period = 3**A
            values = [sum((heights.get((a, n % 3**a), F(0)) for a in range(A+1)), F(0))
                      for n in range(period)]
            direct_lo = sum((pw(x, p)[0] for x in values), F(0))/period
            direct_hi = sum((pw(x, p)[1] for x in values), F(0))/period
            assert direct_lo <= full_hi and full_lo <= direct_hi
            counts["independent_full_period_power_norms"] += 1
            if H == 8:
                for B, M in ((0, 1), (7, 17), (29, period//2+1), (101, period+3)):
                    actual_hi = sum((pw(values[n % period], p)[1] for n in range(B, B+M)), F(0))/M
                    assert actual_hi <= (1+F(period, M))*full_lo
                    counts["finite_integer_interval_power_comparisons"] += 1
        weighted = {}
        for q in QS:
            cost_lo = cost_hi = F(0)
            for (t, _), (_, _, Pnum, *_rest) in columns.items():
                plo, phi = pw(F(Pnum, 2**t), alpha)
                tlo, thi = pw(1+t, q)
                cost_lo += plo*tlo/2**t
                cost_hi += phi*thi/2**t
            weighted[str(q)] = {"lower": str(cost_lo), "upper": str(cost_hi)}
            counts["finite_joint_clock_lower_coefficient_moments"] += 1
        for start in (1, 2, 4, 8):
            chosen = {key: data for key, data in columns.items() if start <= key[0] < 2*start}
            if not chosen:
                continue
            G = len({(t, data[0]) for (t, _), data in chosen.items()})
            block_hi = norm_bounds(heights_from(chosen), p)[1]
            cost_lo = sum((pw(F(data[2], 2**t), alpha)[0]/2**t
                           for (t, _), data in chosen.items()), F(0))
            assert block_hi <= p*pw(G, alpha)[0]*cost_lo
            counts["full_dyadic_component_sum_power_bounds"] += 1
        rows.append({"p": str(p), "full_power_integral_lower": str(full_lo),
                     "full_power_integral_upper": str(full_hi),
                     "sum_component_power_integrals_upper": str(component_sum_hi),
                     "joint_clock_coefficient_moments": weighted})
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-lower-clock-") as d:
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
                assert {n for n, _ in roots} == {"LowerReturnClockMoments."+t for t in THEOREMS}
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
    common_power_blocks(counts)
    rows = []
    for H in (8, 12, 16):
        starts, ends, columns, unfinished = enumerate_returns(H, counts)
        groups = group_moments(H, starts, ends, counts)
        images = image_moments(H, columns, counts)
        rows.append({"H": H, "population": 2**H, "unfinished_at_cap": unfinished,
                     "lower_image_columns": len(columns), "clocked_group_checks": groups,
                     "full_image_power_checks": images})
        print("Exact total-clock and full image powers passed through", H, flush=True)
    replay = {"counts": dict(counts), "power_precision": PRECISION,
              "logarithm_precision": LOG_PRECISION, "finite_trees": rows,
              "infinite_scope": "None. Joint moments and full Lp bounds remain written arguments."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_all_return_lower_energy.py",
             "verify_lower_return_energy.py", "verify_return_affine_budget.py",
             "verify_return_slope_occupation.py", "docs/LOWER-RETURN-CLOCK-MOMENTS.md", *PRIOR,
             "results/lower-return-clock-moments/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Minimum coefficient domination and lift invariance.",
                               "Selected endpoint odd-count identity.",
                               "Group duration constants and finite total-clock drift telescoping.",
                               "Rational exponent windows."],
              "written_scope": ["The group-start first coefficient moment is integrable with every total-clock power below 1/2.",
                                "All-return mixed moments P^theta (1+S)^q are finite for theta<1 and q<1/2.",
                                "The lower-image density has full Haar Lp bounds for beta<1 and p<4/(3+beta).",
                                "Unweighted Lp clock tails decay at every power delta<(4-3p)/(2p)."],
              "external_scope": "None. The proof reuses local written stopping, occupation and fibre results.",
              "not_proved": ["The same improved norm for the original fixed-endpoint density.",
                             "The boundary p=4/3, full L2, or all-return theta=1 with positive clock power.",
                             "Infinite-cutoff integer sampling, actual-gradient control, Q, escape or other-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
