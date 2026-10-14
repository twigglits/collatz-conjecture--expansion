"""Verify exact minimum-cap transport and finite actual-Collatz obstructions.

The large census is independent Python integer arithmetic, not a kernel
certificate. A second, source-by-source replay compares every late minimum.
No prefix timeout is used to assert a global minimum or nonconvergence.
"""
from collections import Counter, deque
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import accumulate
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-cap-transport"
SOURCES = ["CollatzContradiction.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean"]
THEOREMS = ["prefix_le_source", "prefix_succ_le", "prefix_clock_mono",
            "even_minimum_transport", "odd_minimum_transport", "tail_value_mono",
            "cap_add_identity", "cap_below_floor", "cap_above_floor", "cap_mono",
            "cap_zero_of_le", "cap_sum_clock_mono", "cap_sum_stays_zero",
            "even_tail_transport", "odd_tail_transport", "source_one_tail_zero",
            "odd_population_transport", "even_population_transport",
            "small_closed_sums", "small_sampling_error_positive",
            "small_future_caps_zero", "small_future_cap_obstruction"]
PRIORS = ["results/minimum-tail-rigidity/verification.json",
          "results/cutoff-descent/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    return [value.numerator, value.denominator]


def g(h, y):
    return y if y > h else 0


def loss(h, s, y):
    return g(h, y) - g(h, min(s, y))


def sums(row, h):
    return [0] + list(accumulate(g(h, y) for y in row[1:]))


def population_record(rows, clock, cutoff, floor):
    """rows contain the prefix minima at clocks T-2, T-1 and T."""
    child, even, parent = rows
    a, x = cutoff // 2, (cutoff - 1) // 2
    c = 3 * x + 2
    parent_sum = sum(g(floor, y) for y in parent[1:cutoff + 1])
    even_sum = sum(g(floor, y) for y in even[1:a + 1])
    child_sum = sum(g(floor, y) for y in child[1:c + 1])
    progression_sum = sum(g(floor, child[3 * n + 2]) for n in range(1, x + 1))
    caps = [loss(floor, 2 * n + 1, child[3 * n + 2]) for n in range(1, x + 1)]
    cap_sum = sum(caps)
    assert parent_sum + cap_sum == even_sum + progression_sum
    delta = F(progression_sum, x) - F(child_sum, c)
    residual = F(parent_sum, cutoff) - (F(even_sum, a) + F(child_sum, c)) / 2
    # Keep the coefficient deficit separate from sampling and cap loss.
    deficit = (F(1, 2) - F(a, cutoff)) * F(even_sum, a)
    deficit += (F(1, 2) - F(x, cutoff)) * F(child_sum, c)
    assert deficit >= 0
    assert residual == F(x, cutoff) * delta - F(cap_sum, cutoff) - deficit
    return {"floor": floor, "parent_clock": clock, "tail_clock": clock - 2,
            "source_cutoff": cutoff, "even_cutoff": a, "odd_sources": x,
            "child_cutoff": c, "parent_tail_sum": parent_sum,
            "even_tail_sum": even_sum, "child_tail_sum": child_sum,
            "progression_tail_sum": progression_sum, "cap_sum": cap_sum,
            "positive_cap_terms": sum(v > 0 for v in caps),
            "prefix_tail_mean": pair(F(parent_sum, cutoff)),
            "sampling_error": pair(delta), "fair_residual": pair(residual),
            "coefficient_deficit": pair(deficit),
            "positive_fair_residual_with_zero_cap": residual > 0 and cap_sum == 0,
            "dyadic_half_budget_passes_here": 2 * parent_sum <= cutoff}


def small_replay(counts):
    maximum, horizon = 3074, 130
    states = list(range(maximum + 1))
    rows = [states.copy()]
    for _ in range(horizon):
        states = [0] + [3 * v + 1 if v & 1 else v // 2 for v in states[1:]]
        row = [min(v, m) for v, m in zip(states, rows[-1])]
        assert all(b <= a for a, b in zip(rows[-1], row))
        rows.append(row)
        counts["small_census_ordinary_steps"] += maximum
        counts["small_prefix_monotonicity_checks"] += maximum
    cutoffs = [1, 2, 3, 4, 7, 8, 15, 16, 31, 32,
               63, 64, 127, 128, 255, 256, 511, 512, 1023, 1024]
    floors = [1, 4, 16, 64, 256]
    samples = []
    for t in range(horizon - 1):
        for n in range(1, 1025):
            assert rows[t + 1][2 * n] == rows[t][n]
            assert rows[t + 2][2 * n + 1] == min(2 * n + 1, rows[t][3 * n + 2])
            counts["individual_even_minimum_transports"] += 1
            counts["individual_odd_minimum_transports"] += 1
        for h in floors:
            parent, even, child = [sums(rows[u], h) for u in [t + 2, t + 1, t]]
            caps, progressions = [0], [0]
            for n in range(1, 1025):
                s, y = 2 * n + 1, rows[t][3 * n + 2]
                d = loss(h, s, y)
                assert d == (g(h, y) if s <= h else max(y - s, 0))
                assert g(h, min(s, y)) + d == g(h, y)
                counts["scalar_cap_formula_checks"] += 1
                if t:
                    assert d <= loss(h, s, rows[t - 1][3 * n + 2])
                    counts["individual_cap_monotonicity_checks"] += 1
                caps.append(caps[-1] + d)
                progressions.append(progressions[-1] + g(h, y))
            for x in cutoffs:
                for n in [2 * x + 1, 2 * (x + 1)]:
                    assert parent[n] + caps[x] == even[n // 2] + progressions[x]
                    counts["small_population_transport_checks"] += 1
            if t == 4 and h == 1:
                sample = population_record(rows[4:7], 6, 3, 1)
                assert sample["sampling_error"] == [1, 1]
                assert sample["fair_residual"] == [1, 6]
                assert sample["cap_sum"] == 0
                samples.append(sample)
    # Layer-cake errors share denominator x*c; calculate them as integers.
    for t in [0, 2, 4, 8, 16, 32, 64, 128]:
        for x in [1, 2, 8, 32, 128, 512, 1024]:
            c = 3 * x + 2
            full = Counter(rows[t][1:c + 1])
            prog = Counter(rows[t][3 * n + 2] for n in range(1, x + 1))
            for h in floors:
                weighted = c * sum(y * v for y, v in prog.items() if y > h)
                weighted -= x * sum(y * v for y, v in full.items() if y > h)
                full_survival = sum(v for y, v in full.items() if y > h)
                prog_survival = sum(v for y, v in prog.items() if y > h)
                integrated = h * (c * prog_survival - x * full_survival)
                for s in range(h, c):
                    integrated += c * prog_survival - x * full_survival
                    full_survival -= full[s + 1]
                    prog_survival -= prog[s + 1]
                assert integrated == weighted
                counts["exact_weighted_layer_cake_checks"] += 1
    return {"maximum_source": maximum, "last_ordinary_clock": horizon,
            "kernel_sized_witness": samples[0],
            "scope": "Actual finite prefixes; no convergence or infinite-minimum inference."}


def large_replay(counts):
    maximum, horizon = 98306, 256
    schedules = {}
    for k in range(4, 17):
        for factor in [4, 6, 8, 10, 12, 16]:
            schedules.setdefault(k * factor, []).append((k, factor))
    states = list(range(maximum + 1))
    minima = states.copy()
    recent = deque([minima], maxlen=3)
    records = []
    for t in range(1, horizon + 1):
        states = [0] + [3 * v + 1 if v & 1 else v // 2 for v in states[1:]]
        minima = [min(v, m) for v, m in zip(states, minima)]
        recent.append(minima)
        counts["large_census_ordinary_steps"] += maximum
        if t in schedules:
            for k, factor in schedules[t]:
                for floor in [1, 16, 64, 256, 1024]:
                    for n in [2 ** k, 2 ** k + 1]:
                        record = population_record(list(recent), t, n, floor)
                        record.update({"k": k, "clock_factor": factor})
                        records.append(record)
                        counts["large_population_transport_checks"] += 1
        if t % 64 == 0:
            print("Actual prefix census reached ordinary clock", t, flush=True)
    late = [r for r in records if r["parent_clock"] == 256 and r["floor"] == 64]
    assert len(late) == 2
    odd = next(r for r in late if r["source_cutoff"] == 65537)
    assert odd["parent_tail_sum"] == 33999 and odd["cap_sum"] == 0
    assert odd["sampling_error"] == [23790617, 1610645504]
    assert odd["fair_residual"] == [778747256741, 105556874395648]
    positive_zero = [r for r in records if r["positive_fair_residual_with_zero_cap"]]
    assert positive_zero
    return {"maximum_source": maximum, "last_ordinary_clock": horizon,
            "rows": records, "late_witnesses": late,
            "positive_fair_residuals_with_zero_cap": len(positive_zero),
            "scope": "780 exact finite rows, not asymptotics; zero cap persists by the separately kernel-proved monotonicity theorem."}, list(recent)


def independent_late_replay(reference, counts):
    """Use separate per-source trajectories; stop only on the absorbing minimum 1."""
    maximum = 98306
    clocks = [254, 255, 256]
    rows = {t: [0] for t in clocks}
    for n in range(1, maximum + 1):
        state, lowest, clock, found = n, n, 0, {}
        while clock < 256 and lowest != 1:
            state = state // 2 if state % 2 == 0 else 3 * state + 1
            clock += 1
            lowest = min(lowest, state)
            counts["independent_late_replay_ordinary_steps"] += 1
            if clock in clocks:
                found[clock] = lowest
        for t in clocks:
            value = found[t] if t in found else 1
            assert t in found or lowest == 1
            assert value == reference[t - 254][n]
            rows[t].append(value)
            counts["independently_compared_late_minima"] += 1
        counts["independently_replayed_sources"] += 1
    records = [population_record([rows[t] for t in clocks], 256, n, 64)
               for n in [65536, 65537]]
    return {"clocks": clocks, "source_cutoff": maximum, "witnesses": records,
            "scope": "Every one of the three late minima is recomputed source by source and compared; no memoized arrivals or future minima."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-minimum-cap-") as directory:
        for source in SOURCES:
            stem = Path(source).stem
            obj = Path(directory) / (stem + ".olean")
            log = OUT / (stem + ".log")
            command = ["lean", "-o", str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("warning:", "error:", "sorryAx", "ofReduceBool"))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == SOURCES[-1]:
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
            builds.append({"source": source, "source_sha256": digest(ROOT / source),
                           "command": command, "returncode": 0, "fresh_build": True,
                           "native_computation_used": False,
                           "elapsed_seconds": round(time.monotonic() - started, 3),
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior_counts = {}
    for path in PRIORS:
        prior = json.loads((ROOT / path).read_text())
        assert prior["status"] == "passed"
        for filename, expected in prior["sha256"].items():
            assert digest(ROOT / filename) == expected, filename
        prior_counts[path] = len(prior["sha256"])
    print("Authenticated prior manifests:", prior_counts, flush=True)
    version, builds = build()
    counts = Counter()
    small = small_replay(counts)
    print("Small exact transport, cap monotonicity and layer-cake checks passed.", flush=True)
    large, late_rows = large_replay(counts)
    independent = independent_late_replay(late_rows, counts)
    print("Independent source-by-source late replay passed.", flush=True)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "small_replay": small, "large_replay": large,
                              "independent_late_replay": independent})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-CAP-TRANSPORT.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": prior_counts,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Finite-prefix minimum monotonicity; even and odd source transport; exact cap formulas and both population parities; zero cap at any clock persists for all later clocks; a closed actual-Collatz witness has positive sampling error and fair recurrence residual despite all future caps being zero.",
        "written_scope": [
            "The normalized recurrence includes the progression sampling error, cap loss and coefficient deficit separately.",
            "The small kernel witness rejects uniform finite bounds of positive sampling error or fair residual by any nonnegative current or future cap charge.",
            "Weighted layer-cake summation of a threshold-uniform bounded-label error loses a factor comparable to the source cutoff; it does not by itself yield a first-moment bound."],
        "external_dependency": "None for the new identities or witnesses. Prior analytic mixing is context only and is not freshly proved or independently validated here.",
        "finite_scope_limit": "The large census and its independent replay use exact Python integers and rationals, not native Lean or kernel finite certificates. The all-future zero-cap conclusion follows from the generic kernel implication applied to the finite zero-cap calculation. No floating-point proof decisions.",
        "not_proved": ["Any uniform linear minimum-tail budget for Collatz.",
                       "Failure of every eventual large-scale error bound, past-cap accounting, or signed time cancellation.",
                       "A claim about uncomputed infinite minima, zero nonconvergent mass, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts), "late_witnesses": large["late_witnesses"]}, indent=2))


if __name__ == "__main__":
    main()
