"""Finite support for the WRITTEN minimum-log-moment deduction.

Infinite floor survival is only a predicate in the Lean proofs. Python
checks bounded actual prefixes and a separate auxiliary cutoff chain.
Neither finite checks nor manifest authentication certify analytic mixing.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/cutoff-descent"
SOURCES = ["lean/CensoredProgressionTransport.lean", "lean/CutoffDescent.lean"]
THEOREMS = ["never_below_even", "never_below_odd", "below_floor_zero",
            "odd_cell_upper", "population_odd_upper", "population_even_upper",
            "fair_mean_bound", "cutoff_product_bound", "reciprocal_cross_bound",
            "boundary_overshoot", "finite_unroll", "finite_potential_budget",
            "terminal_upper", "terminal_mono", "stopped_comparison", "tangent_drift"]
PRIORS = ["results/clocked-progression-mixing/verification.json",
          "results/censored-progression-transport/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + "\n")


def ratio(value):
    return [value.numerator, value.denominator]


def fraction_record(value):
    """Record large exact fractions without multi-thousand-digit JSON fields."""
    sizes = [abs(value.numerator).bit_length(), value.denominator.bit_length()]
    if max(sizes) <= 1024:
        return {"fraction": ratio(value)}
    def integer_bytes(n):
        return n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")
    return {"sign": 1 if value > 0 else -1 if value < 0 else 0,
            "numerator_denominator_bits": sizes,
            "numerator_sha256": hashlib.sha256(integer_bytes(abs(value.numerator))).hexdigest(),
            "denominator_sha256": hashlib.sha256(integer_bytes(value.denominator)).hexdigest()}


def ordinary(n):
    return 3 * n + 1 if n & 1 else n // 2


def finite_prefixes(counts):
    """Every source prefix is generated directly, without tail memoization."""
    extent, horizon = 2048, 128
    maximum = 3 * extent + 2
    minima = [[0] * (maximum + 1) for _ in range(horizon + 3)]
    for source in range(1, maximum + 1):
        state = minimum = source
        minima[0][source] = source
        for t in range(1, horizon + 3):
            state = ordinary(state)
            minimum = min(minimum, state)
            minima[t][source] = minimum
        counts["direct_ordinary_prefixes"] += 1
        counts["direct_ordinary_steps"] += horizon + 2

    floors = [1, 2, 3, 4, 8, 16, 64, 256, 1024]
    cutoffs = [3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 127, 128,
               255, 256, 511, 512, 1023, 1024, 2047, 2048]
    sample_times = [0, 1, 2, 4, 8, 16, 32, 64, 96, 128]
    live_rows, killed_witnesses = [], []
    for h in floors:
        for t in range(horizon + 1):
            for n in range(1, extent + 1):
                assert (minima[t + 1][2 * n] > h) == (minima[t][n] > h)
                assert (minima[t + 2][2 * n + 1] > h) == (
                    2 * n + 1 > h and minima[t][3 * n + 2] > h)
                counts["finite_even_survival_identities"] += 1
                counts["finite_killed_odd_survival_identities"] += 1
                if 2 * n + 1 <= h < minima[t][3 * n + 2]:
                    counts["nontrivial_killed_boundary_cases"] += 1
                    if len(killed_witnesses) < 12:
                        killed_witnesses.append({"floor": h, "tail_horizon": t,
                                                "source": 2 * n + 1,
                                                "child": 3 * n + 2})
            if t not in sample_times:
                continue
            indicators = [[int(v > h) for v in minima[t + shift]] for shift in (0, 1, 2)]
            sums = []
            for values in indicators:
                cumulative = [0]
                for value in values[1:]:
                    cumulative.append(cumulative[-1] + value)
                sums.append(cumulative)
            for n in cutoffs:
                a, ell = n // 2, (n - 1) // 2
                b = 3 * ell + 2
                odd = sum(indicators[0][3 * j + 2] for j in range(1, ell + 1))
                killed_odd = sum(indicators[0][3 * j + 2] for j in range(1, ell + 1)
                                 if 2 * j + 1 > h)
                assert sums[2][n] == sums[1][a] + killed_odd
                assert sums[2][n] <= sums[0][a] + odd
                delta = F(odd, ell) - F(sums[0][b], b)
                right = (F(sums[0][a], a) + F(sums[0][b], b) + abs(delta)) / 2
                assert F(sums[2][n], n) <= right
                counts["shifted_population_splits_and_bounds"] += 1
        live = sum(minima[horizon][n] > h for n in range(1, maximum + 1))
        live_rows.append({"floor": h, "ordinary_horizon": horizon,
                          "sources": maximum, "finite_live_prefixes": live})
    assert counts["nontrivial_killed_boundary_cases"] > 0
    assert 0 < live_rows[0]["finite_live_prefixes"] < maximum
    return {"extent": extent, "maximum_source": maximum, "maximum_clock": horizon + 2,
            "floors": floors, "finite_live_counts": live_rows,
            "killed_boundary_examples": killed_witnesses,
            "population_clock_convention": "Left clock t+2; even right clock t+1; killed odd right clock t. The upper bound uses right clock t for both.",
            "limitation": "A live finite prefix is not an infinite-survival instance. No future arrival decision is used."}


def minimum_record_replay(counts):
    rows = []
    for floor in [8, 16, 64, 256]:
        passages, longest = 0, 0
        for source in range(floor + 1, 4 * floor, 2):
            state, prefix = source, []
            for _ in range(1024):
                if state <= floor and state & 1:
                    break
                prefix.append(state)
                state = ordinary(state)
            else:
                raise AssertionError((source, floor, "bounded first passage not found"))
            landing = state
            assert prefix and landing < min(prefix)
            counts["first_odd_strict_records"] += 1
            longest = max(longest, len(prefix))
            passages += 1
            # Compute the source prefix anew; this checks the record transfer
            # without using an assumption about the unknown infinite tail.
            state, source_minimum = source, source
            for _ in prefix:
                state = ordinary(state)
                source_minimum = min(source_minimum, state)
            assert state == landing
            tail, tail_minimum = landing, landing
            thresholds = sorted({1, floor // 2, floor, source, 4 * floor})
            for t in range(65):
                assert source_minimum == tail_minimum
                for h in thresholds:
                    assert (source_minimum > h) == (tail_minimum > h)
                    counts["record_threshold_transfer_checks"] += 1
                counts["record_finite_minimum_equalities"] += 1
                if t < 64:
                    state, tail = ordinary(state), ordinary(tail)
                    source_minimum = min(source_minimum, state)
                    tail_minimum = min(tail_minimum, tail)
        rows.append({"floor": floor, "odd_sources": passages,
                     "longest_checked_passage_clock": longest,
                     "tail_horizon": 64, "thresholds_include_above_passage_floor": True})
    return rows


def children(n):
    return n // 2, 3 * ((n - 1) // 2) + 2


def cutoff_arithmetic(counts):
    for n in range(3, 100001):
        a, b = children(n)
        correction = 2 * n + (n % 2)
        assert 4 * a * b + correction == 3 * n * n
        assert 4 * a * b < 3 * n * n
        assert 8 * a * b <= 3 * n * (a + b)
        assert (F(1, a) + F(1, b)) / 2 - F(1, n) >= F(1, 3 * n)
        counts["cutoff_product_and_reciprocal_checks"] += 1
        for h in [3, 4, 8, 17, 64, 257, 1024]:
            if h < n:
                assert h <= 2 * a and h <= 2 * b and n < b
                counts["cutoff_boundary_overshoot_checks"] += 1


def auxiliary_chain(counts):
    """Forward integer tree weights versus backward rational recursion."""
    rows = []
    depth = 12
    for h in [3, 8, 17, 64, 257]:
        cap = F(2, h)
        def f(n):
            return F(max(0, n - h), n + h)
        def v(n):
            return min(F(1, n), cap)
        def recursive_children(n):
            if n % 2:
                return (n - 1) // 2, (3 * n + 1) // 2
            return n // 2, 3 * n // 2 - 1
        @cache
        def backward(k, n):
            if k == 0 or n <= h:
                return f(n), v(n), F(0), F(0), F(0)
            a, b = recursive_children(n)
            lower, upper = backward(k - 1, a), backward(k - 1, b)
            average = tuple((x + y) / 2 for x, y in zip(lower, upper))
            residual = f(n) - (f(a) + f(b)) / 2
            return (average[0], average[1], F(1, n) + average[2],
                    residual + average[3], max(F(0), residual) + average[4])

        for start in [h + 1, 3 * h + 1, 31 * h + 7]:
            distribution = Counter({start: 1})
            reciprocal_cost = residual_cost = positive_cost = F(0)
            for k in range(depth + 1):
                denominator = 1 << k
                assert sum(distribution.values()) == denominator
                assert all(2 * n >= h for n in distribution)
                terminal_f = sum((F(w, denominator) * f(n) for n, w in distribution.items()), F(0))
                terminal_v = sum((F(w, denominator) * v(n) for n, w in distribution.items()), F(0))
                survival = F(sum(w for n, w in distribution.items() if n > h), denominator)
                assert (terminal_f, terminal_v, reciprocal_cost, residual_cost, positive_cost) == backward(k, start)
                assert f(start) == terminal_f + residual_cost
                assert f(start) <= terminal_f + positive_cost
                assert terminal_f <= survival
                assert reciprocal_cost / 3 <= terminal_v - v(start) <= cap - v(start)
                assert reciprocal_cost <= F(6, h)
                counts["auxiliary_distribution_recursion_agreements"] += 1
                counts["exact_finite_unroll_and_budget_checks"] += 1
                if k == depth:
                    break
                following = Counter()
                for n, w in distribution.items():
                    if n <= h:
                        following[n] += 2 * w
                    else:
                        a, b = children(n)
                        residual = f(n) - (f(a) + f(b)) / 2
                        reciprocal_cost += F(w, denominator * n)
                        residual_cost += F(w, denominator) * residual
                        positive_cost += F(w, denominator) * max(F(0), residual)
                        following[a] += w
                        following[b] += w
                        counts["auxiliary_active_state_expansions"] += 1
                distribution = following
            rows.append({"floor": h, "start_cutoff": start, "depth": depth,
                         "terminal_states": len(distribution), "survival_probability": ratio(survival),
                         "reciprocal_occupation": fraction_record(reciprocal_cost),
                         "reciprocal_upper_bound": ratio(F(6, h)),
                         "all_exact_checks_passed": True})
        backward.cache_clear()
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-cutoff-descent-") as directory:
        for source in SOURCES:
            stem = Path(source).stem
            obj, log = Path(directory) / (stem + ".olean"), OUT / (stem + ".log")
            command = ["lean", "-o", str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("warning:", "error:", "sorryAx", "ofReduceBool"))
            if source == SOURCES[-1]:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
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
    prefixes = finite_prefixes(counts)
    print("Bounded ordinary-prefix survival checks passed.", flush=True)
    records = minimum_record_replay(counts)
    cutoff_arithmetic(counts)
    chains = auxiliary_chain(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "bounded_actual_prefixes": prefixes,
                              "record_minimum_transfer": records,
                              "auxiliary_cutoff_chains": chains})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-LOG-MOMENTS.md",
                      "docs/CLOCKED-PROGRESSION-MIXING.md", "docs/CLOCKED-MINIMUM.md",
                      "docs/NATURAL-DENSITY-ALMOST-BOUNDED.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": prior_counts,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Actual noncomputable floor-survival predicate, even/odd implications and finite population bounds; exact cutoff product, reciprocal drift cross-multiplication and overshoot; finite rational stopping, potential and tangent-drift inequalities. No infinite survival instance is asserted.",
        "written_scope": [
            "The preceding same-scale marked coupling compares global-minimum laws, with every fixed inverse-logarithmic power and constants uniform in the minimum threshold.",
            "The auxiliary fair cutoff chain has negative logarithmic drift and finite expected absorption time, independently of actual orbit termination.",
            "Convex logarithmic potentials give sup_N Pr_(n<=N)(minimum(n)>H) <= C_r (log H)^(-r) for every fixed r>0.",
            "Every fixed logarithmic power of the global minimum is uniformly integrable; using the earlier written minimum law, its source moments converge."],
        "analytic_dependencies": {
            "tail_and_moments": "The local WRITTEN same-scale progression-mixing extension using Tao's published Fourier/collision and valuation inputs; exact first-odd-record property; written real convexity, probability telescoping and limit arguments.",
            "moment_limit_identification_only": "Earlier WRITTEN existence of the global-minimum limiting law.",
            "external_predecessor_density_used": False,
            "new_external_theorem_claimed": False},
        "finite_scope_limit": "Exact bounded-prefix and auxiliary-chain checks only. No floating-point proof decisions, infinite-orbit decisions, effective analytic constants, fresh external Lean replay, or asymptotic mixing certification.",
        "not_proved": ["The analytic mixing premise in Lean.", "Effective constants or thresholds.",
                       "Uniform integrability of lifetime deficit or arrival clocks.",
                       "Positive power moments of the minimum value itself.",
                       "Minimum one almost surely, the all-source zero limit, escape or other-cycle exclusion, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
