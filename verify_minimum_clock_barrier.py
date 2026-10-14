"""Audit the all-index obstruction to a fixed additive prefix-clock correction.

The family contains finite ordinary prefixes only. Large residue-population
lower bounds are arithmetic consequences of universal kernel theorems, not
enumerations of huge intervals. Selected complete interval replays and the
four convergent kernel witnesses are kept separate.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-clock-barrier"
PRIOR = "results/minimum-green-kernel/verification.json"
SOURCES = ["CollatzContradiction.lean", "CollatzAffine.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
           "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
           "lean/MinimumGreenKernel.lean", "lean/MinimumClockBarrier.lean"]
THEOREMS = [
    "step_halving_bound", "prefix_concatenation", "halving_buffer", "odd_pair",
    "odd_pair_prefix", "odd_block", "odd_block_with_buffer", "paired_power_buffer",
    "five_clock_no_descent", "buffer_from_power", "exponential_clock_no_descent",
    "sum_length_mono", "prefix_plus_term", "residue_sum_le", "residue_source_sum",
    "residue_tail_budget", "strict_dyadic_budget_requires_clock",
    "dyadic_adaptive_clock", "adaptive_dyadic_population",
    "adaptive_mean_unbounded", "adaptive_budget_failure", "adaptive_mean_below_floor",
    "adaptive_mean_nonnegative", "adaptive_mean_decreasing", "prefix_le_endpoint",
    "prefix_at_global_minimum", "adaptive_pointwise_stabilization", "adaptive_residual_lower",
    "closed_subset_tail_lower", "closed_subset_converges"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    return [value.numerator, value.denominator]


def prefix_checks(counts):
    rows = []
    lengths = list(range(1, 129)) + [256, 512, 1024, 2048, 4096]
    quotients = list(range(1, 9)) + [15, 31, 63, 127]
    for k in lengths:
        clock = (6 ** k).bit_length() - 1
        assert 2 ** clock <= 6 ** k < 2 ** (clock + 1)
        for q in quotients:
            source = 2 ** k * q - 1
            state = minimum = source
            for t in range(clock + 1):
                if t <= 2 * k and t % 2 == 0:
                    j = t // 2
                    if k <= 128 or j in {0, k // 4, k // 2, 3 * k // 4, k}:
                        assert state == 2 ** (k - j) * 3 ** j * q - 1
                        counts["closed_ordinary_even_clock_formula_checks"] += 1
                assert minimum == source
                counts["no_descent_prefix_time_checks"] += 1
                if t == clock:
                    break
                state = state // 2 if state % 2 == 0 else 3 * state + 1
                minimum = min(minimum, state)
                counts["selected_prefix_ordinary_steps"] += 1
            counts["selected_prefix_sources"] += 1
        if k in [1, 2, 4, 16, 64, 128, 1024, 4096]:
            rows.append({"odd_prefix_length": k, "guaranteed_ordinary_clock": clock,
                         "quotients": quotients, "largest_source_bits": (2 ** k * max(quotients) - 1).bit_length()})
    return {"lengths": lengths, "quotients": quotients, "selected_rows": rows,
            "scope": "Every listed source is independently iterated through its certified finite clock. No future convergence is inferred."}


def family_arithmetic(counts):
    rows = []
    shifts = list(range(33)) + [64, 128, 256, 512, 1024]
    indices = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024]
    for l in shifts:
        for j in indices:
            exponent = 5 * j + 2 * l
            period_exponent = 4 * j + 2 * l
            m, q = 2 ** period_exponent, 2 ** j
            n, clock = 2 ** exponent, 10 * j + 5 * l
            assert clock == l + 2 * (n.bit_length() - 1)
            assert m * q == n and period_exponent == 2 * (2 * j + l)
            assert clock == 5 * (2 * j + l) and 2 ** clock <= 6 ** period_exponent
            total = m * q * (q + 1) // 2 - q
            lower = F(total, n)
            assert lower == F(q + 1, 2) - F(1, m) >= F(q, 2)
            counts["all_index_population_arithmetic_checks"] += 1
            if l in [0, 4, 64, 1024] and j in [1, 2, 8, 64, 1024]:
                rows.append({"shift": l, "index": j, "cutoff_power_of_two": exponent,
                             "period_power_of_two": period_exponent, "clock": clock,
                             "number_of_contributing_sources_power_of_two": j,
                             "tail_mean_lower_bound": pair(F(q, 2)),
                             "permitted_floor_strictly_below": "2^" + str(period_exponent) + "-1"})
    for d in range(1, 257):
        clock = (6 ** d).bit_length() - 1
        period = 2 ** d
        cutoff = 2 * period
        subset_sum = (period - 1) + (2 * period - 1)
        assert subset_sum >= cutoff and 2 ** clock <= 6 ** d < 2 ** (clock + 1)
        counts["necessary_dyadic_clock_threshold_checks"] += 1
    return {"shifts": shifts, "indices": indices, "selected_rows": rows,
            "scope": "Exact integer arithmetic for universally kernel-proved residue families; enormous intervals are not enumerated."}


def population_checks(counts):
    parameters = [(l, j) for l in range(4) for j in [1, 2]] + [(0, 3), (1, 3)]
    configurations = [(h, l, j) for h in [1, 64, 1024] for l, j in parameters
                      if h < 2 ** (4 * j + 2 * l) - 1]
    maximum = max(2 ** (5 * j + 2 * l) for _, l, j in configurations)
    clocks = sorted({10 * j + 5 * l for _, l, j in configurations})
    states = list(range(maximum + 1))
    minima = states.copy()
    snapshots = {}
    for t in range(1, max(clocks) + 1):
        for n in range(1, maximum + 1):
            value = states[n]
            value = 3 * value + 1 if value & 1 else value // 2
            states[n] = value
            minima[n] = min(minima[n], value)
            counts["population_time_major_steps"] += 1
        if t in clocks:
            snapshots[t] = minima.copy()
    for n in range(1, maximum + 1):
        value = minimum = n
        for t in range(1, max(clocks) + 1):
            value = value // 2 if value % 2 == 0 else 3 * value + 1
            minimum = min(minimum, value)
            counts["population_source_major_steps"] += 1
            if t in snapshots:
                assert minimum == snapshots[t][n]
                counts["independent_population_minimum_comparisons"] += 1
    rows = []
    for h, l, j in configurations:
        exponent = 5 * j + 2 * l
        n, m, q, clock = 2 ** exponent, 2 ** (4 * j + 2 * l), 2 ** j, 10 * j + 5 * l
        snapshot = snapshots[clock]
        sources = [m * b - 1 for b in range(1, q + 1)]
        for source in sources:
            assert h < source < n and snapshot[source] == source
            counts["enumerated_residue_source_checks"] += 1
        subtotal = sum(sources)
        assert subtotal == m * q * (q + 1) // 2 - q
        total = sum(v for v in snapshot[1:n + 1] if v > h)
        assert total >= subtotal and F(total, n) >= F(q, 2)
        counts["complete_population_lower_bound_checks"] += 1
        rows.append({"floor": h, "shift": l, "index": j, "cutoff": n, "clock": clock,
                     "residue_sources": sources, "residue_tail_sum": subtotal,
                     "complete_tail_sum": total, "complete_tail_mean": pair(F(total, n)),
                     "class_mean": pair(F(subtotal, n)), "kernel_lower_bound": pair(F(q, 2))})
    return {"maximum_actual_source": maximum, "retained_clocks": clocks,
            "rows": rows, "scope": "Complete actual prefix-minimum censuses and independent source-major replay, separate from the all-index symbolic proof."}


def stabilization_checks(counts):
    sources = [255, 511, 767, 1023]
    expected_times = [47, 61, 59, 62]
    certified = []
    for n, expected in zip(sources, expected_times):
        value = minimum = n
        trajectory = [n]
        for t in range(1, expected + 1):
            value = value // 2 if value % 2 == 0 else 3 * value + 1
            trajectory.append(value)
            minimum = min(minimum, value)
            if t <= 20:
                assert minimum == n
            assert value != 1 or t == expected
            counts["kernel_witness_independent_steps"] += 1
        assert value == 1
        certified.append({"source": n, "first_one_clock": expected,
                          "trajectory": trajectory, "prefix_minimum_at_20": n})
    assert sum(sources) == 2556
    # A small complete convergent population illustrates fixed-cutoff settling.
    shifts = [0, 4, 16, 32, 64, 128, 256]
    cutoffs = [32, 128, 512, 1024]
    query_clocks = {l + 2 * (n.bit_length() - 1) for l in shifts for n in cutoffs}
    retained = {t: [0] * 1025 for t in query_clocks}
    arrivals = []
    for n in range(1, 1025):
        value = minimum = n
        first = 0 if n == 1 else None
        for t in range(1, max(query_clocks) + 1):
            value = 3 * value + 1 if value & 1 else value // 2
            minimum = min(minimum, value)
            if value == 1 and first is None:
                first = t
            if t in retained:
                retained[t][n] = minimum
            counts["fixed_population_settling_steps"] += 1
        assert first is not None
        arrivals.append(first)
    rows = []
    for h in [1, 64]:
        for n in cutoffs:
            previous = None
            profile = []
            for l in shifts:
                t = l + 2 * (n.bit_length() - 1)
                mean = F(sum(v for v in retained[t][1:n + 1] if v > h), n)
                assert previous is None or mean <= previous
                if l == 256:
                    assert mean == 0
                profile.append({"shift": l, "clock": t, "tail_mean": pair(mean)})
                previous = mean
                counts["fixed_cutoff_monotonicity_and_settling_checks"] += 1
            rows.append({"floor": h, "cutoff": n, "profile": profile})
    return {"four_kernel_certified_sources": certified, "certified_subset_sum": 2556,
            "complete_settling_population": 1024, "maximum_first_one_clock": max(arrivals),
            "first_one_clocks": arrivals, "rows": rows,
            "scope": "Four hitting statements are also kernel checked. The larger complete settling census is Python evidence only, not a new kernel interval certificate."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-clock-barrier-") as directory:
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
            if stem == "MinimumClockBarrier":
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
    prior = json.loads((ROOT / PRIOR).read_text())
    assert prior["status"] == "passed"
    for filename, expected in prior["sha256"].items():
        assert digest(ROOT / filename) == expected, filename
    print("Authenticated prior files:", len(prior["sha256"]), flush=True)
    version, builds = build()
    counts = Counter()
    prefixes = prefix_checks(counts)
    arithmetic = family_arithmetic(counts)
    print("Selected finite prefixes and all-index population arithmetic passed.", flush=True)
    populations = population_checks(counts)
    print("Complete population census and independent replay passed.", flush=True)
    settling = stabilization_checks(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts), "prefixes": prefixes,
                              "family_arithmetic": arithmetic, "complete_populations": populations,
                              "fixed_cutoff_settling": settling})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-CLOCK-BARRIER.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": len(prior["sha256"]),
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Exact ordinary all-odd blocks and halving buffers; all-quotient no-descent prefixes under 2^T<=6^K; residue-population sums; a necessary dyadic clock lower bound for the strict budget; unbounded adaptive prefix means at every fixed additive shift; failure of that prescribed budget; pointwise eventual stabilization; conditional finite residual lower bound; four convergent sources supporting a closed tail-sum obstruction.",
        "written_scope": [
            "For every 0<c<log2(6) and fixed L,H, clocks floor(c*log2 N)+L give tail means growing at least as a positive power along dyadic cutoffs.",
            "Combining the prior elementary majorant and Green-kernel argument gives unbounded expected signed and positive residual occupation for each adaptive prefix profile.",
            "Under full Collatz the global tail mean is zero at H>=1, so the pointwise settling cannot be upgraded to uniform convergence for these prefix clocks."],
        "external_dependency": "None for the new proof. No claim of novelty for the elementary growing-block mechanism.",
        "finite_scope_limit": "Huge population bounds use universal kernel implications plus exact arithmetic, not enormous interval enumeration. The complete Python census and the four kernel hitting examples are reported separately. No finite surviving prefix is called a divergent orbit.",
        "not_proved": ["Failure of a global-minimum residual estimate.", "Failure of all logarithmic clock coefficients or all cutoff-dependent clocks.",
                       "A counterexample, uniform integrability of actual minima, vanishing nonconvergent mass, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts), "maximum_complete_source": populations["maximum_actual_source"],
                      "complete_settling_maximum_first_one": settling["maximum_first_one_clock"]}, indent=2))


if __name__ == "__main__":
    main()
