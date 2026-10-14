"""Exact oriented costs on finite convergent bands, with audited Lean inputs.

Universal convergence is only a hypothesis of the written infinite result.
Every pair in this finite replay is actually checked to reach the known cycle.
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
from verify_gradient_clock_obstruction import SOURCES as CLOCK_SOURCES
from verify_annulus_time_budgets import complete_pair

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/signed-arrival-windows"
SOURCE = "lean/SignedArrivalWindows.lean"
SOURCES = [*CLOCK_SOURCES, SOURCE]
THEOREMS = ["first_arrival_odd", "cycle_after_arrival", "prearrival_endpoint",
            "gap_forces_reversal", "late_parent_reversal", "signed_window_length",
            "prearrival_partition", "finite_gap_floor", "finite_negative_product",
            "positive_clock_budget", "first_arrival_tail_constant"]
PRIOR = ["results/gradient-clock-obstruction/verification.json",
         "results/annulus-time-budgets/verification.json",
         "results/finite-path-packing/verification.json",
         "results/count-return-clock/verification.json",
         "results/return-correction-moments/verification.json"]
PRECISION = 1 << 96
POWERS = (1, 2, 4, 8, 12)
KINDS = ("upward_squared", "downward_squared", "reversed_negative",
         "before_both_arrivals", "late_parent_window", "after_parent_arrival")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    x = F(x)
    return [x.numerator, x.denominator]


def enclosure(lo, hi, denominator=PRECISION):
    return {"lower": ratio(F(lo, denominator)), "upper": ratio(F(hi, denominator))}


def add(bounds, numerator, denominator):
    q, r = divmod(PRECISION * numerator, denominator)
    bounds[0] += q
    bounds[1] += q + bool(r)


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def signed_pair(k, n, memo, counts, exact=False):
    M, q = 1 << k, 3*n+2
    tn, an = memo[n]
    tq, aq = memo[q]
    assert memo[2*n+1] == (tq+1, aq+1)
    assert tn >= k and tq >= k
    assert 4*n*3**an >= 3*(1 << tn)
    assert 4*q*3**aq >= 3*(1 << tq)
    counts["certified_pair_first_hit_floors"] += 2
    plus, minus = max(tq-tn, 0), max(tn-tq, 0)
    terminal = max(k, tn, tq) + 2
    x, y, a, b, p, r, reversed_history = n, q, 0, 1, 1, 3, False
    bounds = {name: [0, 0] for name in KINDS}
    exact_values = {name: F(0) for name in KINDS} if exact else None
    tails, mask, parent_at_arrival = [], None, None
    for t in range(terminal+4):
        reversed_history |= a > b
        if t < tn:
            assert x != 1
        elif t == tn:
            assert x == 1 and a == an
            parent_at_arrival = F(M*p, 1 << t)
        else:
            assert x in (1, 2)
        if t < tq:
            assert y != 1
        elif t == tq:
            assert y == 1 and b == aq+1
        else:
            assert y in (1, 2)
        if t == k:
            mask = (x, a) != (y, b)
            assert mask or plus == minus == 0
        if t >= k:
            delta = p*y-r*x
            denominator = (1 << (2*t))*x*x*y*y
            energy = M*M*delta*delta
            negative = M*M*p*delta*y if reversed_history and delta > 0 else 0
            terms = {"upward_squared": energy if delta < 0 else 0,
                     "downward_squared": energy if delta > 0 else 0,
                     "reversed_negative": negative,
                     "before_both_arrivals": negative if t < min(tn, tq) else 0,
                     "late_parent_window": negative if tq <= t < tn else 0,
                     "after_parent_arrival": negative if t >= tn else 0}
            assert negative == sum(terms[key] for key in KINDS[3:])
            if not mask:
                assert all(value == 0 for value in terms.values())
            if tn+12 <= t < tq:
                assert 16*M*p <= 3*(1 << t)*x
                assert 8*M*r >= 3*(1 << t)*y
                assert delta < 0 and 256*energy >= 9*denominator
                counts["upward_arrival_window_terms"] += 1
            if tq+12 <= t < tn:
                assert 8*M*p >= 3*(1 << t)*x
                assert 16*M*r <= 3*(1 << t)*y
                assert x >= 2 and y in (1, 2) and a > b
                assert reversed_history and delta > 0
                assert 128*negative >= 9*denominator
                assert 256*energy >= 9*denominator
                counts["negative_window_current_reversals"] += 1
            if t < terminal:
                for key, numerator in terms.items():
                    add(bounds[key], numerator, denominator)
                    if exact:
                        exact_values[key] += F(numerator, denominator)
                counts["pre_tail_signed_cost_terms"] += 1
            else:
                assert x in (1, 2) and y in (1, 2)
                tails.append({key: F(value, denominator) for key, value in terms.items()})
        px, py = x & 1, y & 1
        a, b, p, r = a+px, b+py, p*3**px, r*3**py
        x, y = step(x), step(y)
    for key in KINDS:
        for j in (0, 1):
            assert 16*tails[j+2][key] == 9*tails[j][key]
            counts["signed_known_cycle_tail_ratios"] += 1
        tail = F(16, 7)*(tails[0][key]+tails[1][key])
        add(bounds[key], tail.numerator, tail.denominator)
        if exact:
            exact_values[key] += tail
            assert F(bounds[key][0], PRECISION) <= exact_values[key] <= F(bounds[key][1], PRECISION)

    assert 256*bounds["upward_squared"][0] >= 9*max(plus-12, 0)*PRECISION
    assert 256*bounds["downward_squared"][0] >= 9*max(minus-12, 0)*PRECISION
    assert 128*bounds["reversed_negative"][0] >= 9*max(minus-12, 0)*PRECISION
    assert 9*plus*PRECISION <= 108*int(mask)*PRECISION+256*bounds["upward_squared"][0]
    assert 9*minus*PRECISION <= 108*int(mask)*PRECISION+128*bounds["reversed_negative"][0]
    counts["oriented_cell_window_bounds"] += 5
    assert bounds["reversed_negative"] == [sum(bounds[name][i] for name in KINDS[3:]) for i in (0, 1)]
    assert bounds["late_parent_window"][1] <= minus*PRECISION
    assert F(bounds["after_parent_arrival"][1], PRECISION) <= F(25, 7)*parent_at_arrival**2*int(mask)
    counts["exact_prearrival_partitions_and_tail_bounds"] += 1
    counts["pairs_with_independently_certified_arrivals"] += 1
    return {"bounds": bounds, "mask": mask, "plus": plus, "minus": minus,
            "parent_arrival": tn, "child_arrival": tq,
            "exact": {key: ratio(v) for key, v in exact_values.items()} if exact else None}


def census(counts):
    memo = first_arrivals(1 << 16, counts)
    old = json.loads((ROOT/"results/annulus-time-budgets/replay.json").read_text())["annuli"]["rows"]
    clock_replay = json.loads((ROOT/"results/gradient-clock-obstruction/replay.json").read_text())
    clocks = clock_replay["first_arrival_clocks"]["bands"]
    rows, witnesses = [], []
    Q, positive_sum, negative_sum = F(0), F(0), F(0)
    power_sums_lo, power_sums_hi = {p: F(0) for p in POWERS}, {p: F(0) for p in POWERS}
    for k in range(15):
        M = 1 << k
        totals = {key: [0, 0] for key in KINDS}
        powers = {p: [0, 0] for p in POWERS}
        nonfused, plus, minus, equal_clock_positive = 0, 0, 0, 0
        for n in range(M, 2*M):
            exact = n in (1, 37, 823, 925, 1235, 1388, 21845)
            cell = signed_pair(k, n, memo, counts, exact)
            nonfused += cell["mask"]
            plus += cell["plus"]
            minus += cell["minus"]
            for key in KINDS:
                for i in (0, 1):
                    totals[key][i] += cell["bounds"][key][i]
            for p in POWERS:
                for i in (0, 1):
                    powers[p][i] += cell["bounds"]["upward_squared"][i]**p
            equal_clock_positive += cell["plus"] == cell["minus"] == 0 and cell["bounds"]["reversed_negative"][0] > 0
            if exact:
                independent = complete_pair(n, 3*n+2, M, k, 1, counts, exact=True)["exact"]
                values = cell["exact"]
                assert F(*values["upward_squared"])+F(*values["downward_squared"]) == F(*independent["energy"])
                assert values["reversed_negative"] == independent["reversed_negative"]
                counts["independent_exact_signed_sum_comparisons"] += 1
                witnesses.append({"level": k, "parent": n, "other_endpoint": 3*n+2,
                                  "parent_arrival": cell["parent_arrival"], "other_arrival": cell["child_arrival"],
                                  "positive_delay": cell["plus"], "negative_delay": cell["minus"], **values})
        assert nonfused == clocks[k]["nonfused_edges_at_prefix"]
        assert ratio(F(plus, M)) == clocks[k]["mean_positive_clock_increment"]
        assert ratio(F(minus, M)) == clocks[k]["mean_negative_clock_increment"]
        counts["authenticated_clock_band_comparisons"] += 1
        signed_energy = [totals["upward_squared"][i]+totals["downward_squared"][i] for i in (0, 1)]
        for current, previous in ((signed_energy, old[k]["all_time_energy"]),
                                  (totals["reversed_negative"], old[k]["all_time_reversed_negative"])):
            assert F(current[0], 2*M*PRECISION) <= F(*previous["upper"])
            assert F(*previous["lower"]) <= F(current[1], 2*M*PRECISION)
            counts["authenticated_all_time_annulus_enclosure_comparisons"] += 1
        Q += F(nonfused, M)
        positive_sum += F(plus, M)
        negative_sum += F(minus, M)
        assert positive_sum-negative_sum == 2*F(*clocks[k+1]["mean_remaining_first_arrival"])
        assert positive_sum >= k+1
        margin = max(positive_sum-12*Q, F(0))
        required = F(9, 256)*margin
        moment_rows = {}
        for p in POWERS:
            denominator = M*PRECISION**p
            power_sums_lo[p] += F(powers[p][0], denominator)
            power_sums_hi[p] += F(powers[p][1], denominator)
            assert required**p <= Q**(p-1)*power_sums_lo[p]
            counts["upward_clock_holder_bounds"] += 1
            moment_rows[str(p)] = {
                "band_mean": enclosure(*powers[p], denominator),
                "cumulative_mean": {"lower": ratio(power_sums_lo[p]), "upper": ratio(power_sums_hi[p])},
                "cumulative_lower_bound_from_positive_clocks": ratio(required**p/Q**(p-1))}
        if margin > 0:
            counts["positive_clock_margin_prefixes"] += 1
        row = {"level": k, "parent_interval": [M, 2*M],
               "nonfused_at_prefix": nonfused,
               "mean_positive_delay": ratio(F(plus, M)), "mean_negative_delay": ratio(F(minus, M)),
               "equal_arrival_pairs_with_positive_reversed_cost": equal_clock_positive,
               "unhalved_mean_costs": {key: enclosure(*value, M*PRECISION) for key, value in totals.items()},
               "cumulative_nonfusion_mass": ratio(Q), "cumulative_positive_delay": ratio(positive_sum),
               "cumulative_negative_delay": ratio(negative_sum), "positive_clock_margin": ratio(margin),
               "upward_moments": moment_rows}
        rows.append(row)
        print("Exact signed annulus passed:", k, "equal-clock positive costs:", equal_clock_positive, flush=True)
    witness = next(row for row in witnesses if row["parent"] == 823)
    assert witness["parent_arrival"] == witness["other_arrival"] == 86
    assert witness["reversed_negative"] == witness["before_both_arrivals"] == [6289513358589, 491370708992000]
    assert witness["after_parent_arrival"] == [0, 1]
    return {"rows": rows, "exact_witnesses": witnesses,
            "maximum_memoized_source_requirement": 1 << 16,
            "scope": "All 32767 parents in levels 0 through 14; every future offset certified using known-cycle tails. No infinite-source conclusion."}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-signed-arrival-") as directory:
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
                assert {name for name, _ in roots} == {"SignedArrivalWindows."+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}, name
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
        assert record.get("status", "passed") == "passed"
        assert record["builds"] and all(b["returncode"] == 0 for b in record["builds"])
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    replay = {"finite_signed_bands": census(counts), "counts": dict(counts),
              "infinite_scope": "None. Upward power growth is a written theorem conditional on universal convergence."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_gradient_clock_obstruction.py",
             "verify_known_basin_nonfusion_trace.py", "verify_dyadic_coalescence_defects.py",
             "verify_annulus_time_budgets.py", "docs/SIGNED-ARRIVAL-WINDOWS.md",
             "docs/CONDITIONAL-GRADIENT-POWER-OBSTRUCTION.md", "docs/FINITE-PATH-PACKING.md",
             "docs/COUNT-RETURN-CLOCK.md", "docs/RETURN-CORRECTION-MOMENTS.md", *PRIOR,
             "results/annulus-time-budgets/replay.json", "results/gradient-clock-obstruction/replay.json",
             "results/signed-arrival-windows/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Odd first-arrival transfer and known-cycle continuation.",
                               "A late parent with positive downward gap has reversed current count order.",
                               "Oriented clock windows, prearrival partition and denominator-cleared finite product bound.",
                               "The positive clock increment sum pays for mean remaining-clock growth."],
              "written_scope": ["Oriented profile windows and the reversed-negative lower bound from negative arrival advances.",
                                "Conditional on universal convergence, upward accumulated-gradient pth moments have cumulative growth at least K^((p+1)/2), p>1.",
                                "Reversed cost is comparable, up to fixed constants and nonfusion slack, to prearrival cost plus the negative clock advance."],
              "external_scope": "No external analytic theorem or external source replay is used.",
              "not_proved": ["Universal convergence or a counterexample.",
                             "Unconditional infinite upward moment divergence.",
                             "Boundedness or unboundedness of downward powers or reversed budgets on all source bands.",
                             "A uniform bound for prearrival cost or negative clock advances.",
                             "Integer image sampling, Q, escape exclusion or additional-cycle exclusion."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
