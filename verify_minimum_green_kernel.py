"""Verify a rational Green-kernel bound for the auxiliary cutoff chain.

Finite Collatz data use an explicit, cutoff-dependent PREFIX clock. They are
never identified with unknown global minima. The infinite expectation and
all-population parity argument are written, distinct from the Lean roots.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-green-kernel"
PRIOR = "results/minimum-linear-boundary/verification.json"
SOURCES = ["CollatzContradiction.lean", "CollatzAffine.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
           "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
           "lean/MinimumGreenKernel.lean"]
THEOREMS = [
    "constants", "gauge_block", "gauge_nonnegative", "low_cell_arithmetic",
    "high_cell_arithmetic", "block_contraction", "gauge_contraction",
    "parity_majorant_to_gauge", "gauge_sublinear_envelope", "gauge_at_least_one",
    "geometric_nonnegative", "geometric_identity", "geometric_upper",
    "killed_nonnegative", "killed_gauge_bound", "survival_bound",
    "occupation_gauge_bound", "residual_magnitude_bound", "magnitude_nonnegative",
    "terminal_eq_killed", "clockless_exact_unroll", "residual_truncation_bound",
    "occupation_below_floor", "occupation_nonnegative", "occupation_split",
    "absolute_tail_bound", "global_mean_below_floor", "global_mean_nonnegative",
    "minimum_of_reaches", "least_minimum", "least_diagonal_tail", "least_diagonal_mean",
    "finite_positive_residual_diagnostic", "least_counterexample_residual_diagnostic"]
Q, RHO = F(29, 30), F(1704, 1711)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > 8192:
        scale = 10 ** 12
        lower = value.numerator * scale // value.denominator
        numerator = abs(value.numerator).to_bytes((abs(value.numerator).bit_length() + 7) // 8, "big")
        denominator = value.denominator.to_bytes((value.denominator.bit_length() + 7) // 8, "big")
        encoded = bytes([value.numerator < 0]) + len(numerator).to_bytes(8, "big") + numerator + denominator
        return {"encoding": "outward_rational_interval", "lower": [lower, scale],
                "upper": [lower + 1, scale], "exact_binary_sha256": hashlib.sha256(encoded).hexdigest(),
                "exact_numerator_bits": abs(value.numerator).bit_length(),
                "exact_denominator_bits": value.denominator.bit_length()}
    return [value.numerator, value.denominator]


def children(n):
    return n // 2, 3 * (max(n - 1, 0) // 2) + 2


@lru_cache(None)
def gauge(n):
    if n == 0:
        return F(0)
    k = n.bit_length() - 1
    return Q ** k * F(2 ** k + 14 * n, 15)


def geometric(k):
    return (1 - RHO ** k) / (1 - RHO)


def arithmetic_checks(counts):
    assert 1 - RHO == F(7, 1711) and 3 / (1 - RHO) == F(5133, 7)
    worst = (F(0), 0)

    def check(n):
        nonlocal worst
        a, b = children(n)
        k = n.bit_length() - 1
        p = 2 ** (k - 1)
        assert 2 * p <= n < 4 * p
        assert p <= a < 2 * p and 2 * p <= b < 8 * p
        if b < 4 * p:
            assert 295 * (88 * p + 420 * a + 406 * b) <= 17040 * (2 * p + 14 * n)
            counts["low_cell_integer_inequalities"] += 1
        else:
            assert 295 * (2132 * p + 6300 * a + 5887 * b) <= 255600 * (2 * p + 14 * n)
            counts["high_cell_integer_inequalities"] += 1
        v = gauge(n)
        ratio = (gauge(a) + gauge(b)) / (2 * v)
        assert ratio <= RHO
        assert 1 <= v <= n * Q ** k
        assert Q ** k * (n + 2 * 2 ** k) <= 3 * v
        assert n * Q ** k + (2 * Q) ** k + F(3, 2) ** k <= 3 * v
        if ratio > worst[0]:
            worst = ratio, n
        counts["exact_gauge_and_contraction_checks"] += 1

    for n in range(2, 65537):
        check(n)
    for k in list(range(3, 129)) + [256, 512, 1024]:
        for center in [2 ** k, (4 * 2 ** k) // 3, 2 ** (k + 1)]:
            for offset in [-1, 0, 1]:
                check(center + offset)
                counts["large_dyadic_and_breakpoint_arithmetic_checks"] += 1
    for k in range(257):
        assert 0 <= geometric(k) <= F(1711, 7)
        assert geometric(k + 1) == 1 + RHO * geometric(k)
        counts["geometric_sum_checks"] += 1
    return {"continuous_cutoff_range": [2, 65536],
            "large_exponents": list(range(3, 129)) + [256, 512, 1024],
            "large_centers": ["2^k", "floor(4*2^k/3)", "2^(k+1)"], "offsets": [-1, 0, 1],
            "largest_observed_ratio": pair(worst[0]), "at_cutoff": str(worst[1]),
            "scope": "Exact auxiliary cutoff arithmetic, not Collatz orbit checks at enormous cutoffs."}


def collect_queries(configurations):
    queries = {0, 1}
    for h, depth, n in configurations:
        frontier = {n}
        for _ in range(depth + 1):
            queries.update(frontier)
            frontier = {child for source in frontier if source > h for child in children(source)}
    return queries


def prefix_profiles(queries, floors, counts):
    maximum = max(queries)
    max_clock = 2 * (maximum.bit_length() - 1)
    states = list(range(maximum + 1))
    minima = states.copy()
    snapshots = {0: minima.copy()}
    for t in range(1, max_clock + 1):
        for n in range(1, maximum + 1):
            state = states[n]
            state = state // 2 if state % 2 == 0 else 3 * state + 1
            states[n] = state
            minima[n] = min(minima[n], state)
            counts["time_major_ordinary_steps"] += 1
        if t % 2 == 0:
            snapshots[t] = minima.copy()
    # Independent source-major replay checks every retained minimum snapshot.
    for n in range(1, maximum + 1):
        state = minimum = n
        assert snapshots[0][n] == minimum
        counts["independent_prefix_minimum_comparisons"] += 1
        for t in range(1, max_clock + 1):
            state = 3 * state + 1 if state & 1 else state // 2
            minimum = min(minimum, state)
            counts["source_major_ordinary_steps"] += 1
            if t % 2 == 0:
                assert snapshots[t][n] == minimum
                counts["independent_prefix_minimum_comparisons"] += 1
    values = {h: {0: F(0)} for h in floors}
    for t, snapshot in snapshots.items():
        k = t // 2
        sums = {h: 0 for h in floors}
        for n in range(1, maximum + 1):
            for h in floors:
                sums[h] += snapshot[n] if snapshot[n] > h else 0
            if n.bit_length() - 1 == k:
                for h in floors:
                    value = F(sums[h], n)
                    assert 0 <= value <= n * Q ** k + (2 * Q) ** k + F(3, 2) ** k <= 3 * gauge(n)
                    if n <= h:
                        assert value == 0
                    counts["actual_variable_clock_mean_majorant_checks"] += 1
                    if n in queries:
                        values[h][n] = value
    assert all(set(values[h]) == queries for h in floors)
    return values, {"maximum_actual_source": maximum, "maximum_ordinary_clock": max_clock,
                    "queried_cutoffs": len(queries), "floors": floors,
                    "clock_rule": "T(N)=2*floor(log2(N)) for N>=1",
                    "scope": "Actual finite PREFIX minima, recomputed in two traversal orders. No global minimum is assigned to an unresolved prefix."}


def tree_checks(counts):
    configurations = [(h, 12, n) for h in [1, 4, 16] for n in [7, 31, 64, 127]]
    queries = collect_queries(configurations)
    prefix, prefix_scope = prefix_profiles(queries, [1, 4, 16], counts)
    rows = []
    for h, depth, n in configurations:
        profiles = {
            "gauge_saturated_synthetic": lambda m, hh=h: F(0) if m <= hh else 3 * gauge(m),
            "oscillating_synthetic": lambda m, hh=h: F(0) if m <= hh else 2 * gauge(m) * F((17 * m + 3) % 19, 19),
            "actual_variable_clock_prefix_mean": lambda m, hh=h: prefix[hh][m]}
        for name, f in profiles.items():
            @lru_cache(None)
            def residual(m):
                a, b = children(m)
                return f(m) - (f(a) + f(b)) / 2

            @lru_cache(None)
            def backward(k, m):
                if m <= h:
                    return F(0), F(0), F(0), F(0)
                if k == 0:
                    return f(m), F(0), F(0), F(1)
                a, b = children(m)
                lower, upper = backward(k - 1, a), backward(k - 1, b)
                return ((lower[0] + upper[0]) / 2,
                        residual(m) + (lower[1] + upper[1]) / 2,
                        abs(residual(m)) + (lower[2] + upper[2]) / 2,
                        (lower[3] + upper[3]) / 2)

            frontier = {n: F(1)} if n > h else {}
            signed = absolute = F(0)
            absolute_history = []
            negative_states = positive_states = 0
            for j in range(depth + 1):
                terminal = sum((mass * f(m) for m, mass in frontier.items()), F(0))
                survival = sum(frontier.values(), F(0))
                assert (terminal, signed, absolute, survival) == backward(j, n)
                assert signed + terminal == f(n)
                assert 0 <= terminal <= 3 * RHO ** j * gauge(n)
                assert survival <= RHO ** j * gauge(n)
                assert 0 <= absolute <= 3 * geometric(j) * gauge(n)
                absolute_history.append(absolute)
                counts["forward_backward_tree_depth_comparisons"] += 1
                if j == depth:
                    break
                following = defaultdict(F)
                for m, mass in frontier.items():
                    assert 0 <= f(m) <= 3 * gauge(m)
                    r = residual(m)
                    assert abs(r) <= 3 * gauge(m)
                    negative_states += int(r < 0)
                    positive_states += int(r > 0)
                    signed += mass * r
                    absolute += mass * abs(r)
                    counts["active_state_residual_checks"] += 1
                    for child in children(m):
                        if child > h:
                            following[child] += mass / 2
                frontier = following
            for j in range(depth + 1):
                for k in range(depth + 1 - j):
                    tail = absolute_history[j + k] - absolute_history[j]
                    assert 0 <= tail <= F(5133, 7) * RHO ** j * gauge(n)
                    counts["absolute_tail_window_checks"] += 1
            counts["independent_recursive_states"] += backward.cache_info().currsize
            counts["cutoff_profile_trees"] += 1
            rows.append({"profile": name, "floor": h, "initial_cutoff": n, "depth": depth,
                         "initial_value": pair(f(n)), "terminal": pair(terminal),
                         "signed_occupation": pair(signed), "absolute_occupation": pair(absolute),
                         "survival_probability": pair(survival),
                         "negative_active_states": negative_states, "positive_active_states": positive_states})
    return {"prefix_census": prefix_scope, "rows": rows,
            "scope": "Exact forward mass propagation and independent memoized backward recurrences. Synthetic profiles are explicitly separate from finite Collatz population means."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-green-kernel-") as directory:
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
            if stem == "MinimumGreenKernel":
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
    arithmetic = arithmetic_checks(counts)
    print("All exact gauge, integer-cell and breakpoint checks passed.", flush=True)
    trees = tree_checks(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "arithmetic": arithmetic, "cutoff_trees": trees})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-GREEN-KERNEL.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": len(prior["sha256"]),
        "finite_replay_counts": dict(counts),
        "kernel_scope": "All-cutoff rational gauge contraction; finite killed-terminal and occupation bounds; absolute residual tail and signed truncation bounds under an explicit majorant; exact least-counterexample diagonal mean; conditional finite residual diagnostic.",
        "written_scope": [
            "Elementary parity counting bounds the actual global-minimum mean by 3V, independently of prior analytic mixing.",
            "The finite bounds imply almost-sure floor absorption and absolute integrability of the infinite residual occupation, with explicit geometric tails.",
            "A least counterexample A requires sup over n>=A of max(R_(A-1)(n),0)/V(n) >= 7/(1711*V(A))."],
        "external_dependency": "None for the new argument; infinite probabilistic assembly remains written, not formalized in a measure-theory library.",
        "finite_scope_limit": "Python exact integer/rational checks are independent evidence, not new Lean population certificates. The Collatz census uses only finite prefix minima with T(N)=2*floor(log2 N). Enormous cutoff tests are auxiliary arithmetic. Large fractions use tagged outward enclosures and binary digests for output only.",
        "not_proved": ["A uniform subunit global-minimum tail budget.", "An independent positive residual bound contradicting the least-counterexample diagnostic.",
                       "Uniform integrability of actual minima, vanishing nonconvergent mass, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts), "prefix_census": trees["prefix_census"]}, indent=2))


if __name__ == "__main__":
    main()
