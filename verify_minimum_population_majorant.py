"""Audit universal population bounds and their actual-minimum applications.

Python evaluates actual finite prefixes only. The global-minimum statements
are universal kernel consequences, not values inferred from unfinished orbits.
The infinite Green expansion remains a written limiting argument.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-population-majorant"
PRIORS = ["results/minimum-critical-clock-lift/verification.json",
          "results/binary-image-energy/verification.json"]
SOURCES = ["CollatzAffine.lean", "lean/CoalescenceTail.lean",
           "lean/EscapeWeightRefinements.lean", "lean/CountReturnControl.lean",
           "lean/CountReturnClock.lean", "lean/ReturnCorrectionMoments.lean",
           "lean/OrderedWeightDrift.lean", "lean/ReversalPersistence.lean",
           "lean/ReturnImageBounds.lean", "lean/BinaryImageEnergy.lean",
           "CollatzContradiction.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
           "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
           "lean/MinimumGreenKernel.lean", "lean/MinimumClockBarrier.lean",
           "lean/MinimumPopulationMajorant.lean"]
THEOREMS = ["word_weight_positive", "word_weight_lift", "word_weight_snoc",
            "word_weight_children", "word_weight_mass", "word_weight_square",
            "square_to_minimum", "shortcut_orbit_eq", "prefix_le_shortcut",
            "prefix_word_majorant", "sum_pos_total", "total_shift", "periodic_positive_mass",
            "two_period_weight_bound", "two_period_numerator_bound", "prefix_sum_word",
            "prefix_population_integer", "dyadic_population_integer", "scale_rate_identity",
            "rate_dyadic_identity", "linear_correction_bound", "correction_absorbed",
            "scaled_mean_bound", "prefix_population_bound", "dyadic_population_bound",
            "gauge_rate_lower", "prefix_mean_majorant", "global_le_prefix_mean",
            "global_mean_majorant", "global_population_bound", "global_dyadic_bound",
            "adaptive_mean_majorant", "adaptive_occupation_lower", "actual_residual_truncation",
            "actual_absolute_tail", "actual_least_residual_diagnostic"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    value = F(value)
    return [value.numerator, value.denominator]


def shortcut_data(k, n):
    x = n
    odd = 0
    for _ in range(k):
        odd += x & 1
        x = (3 * x + 1) // 2 if x & 1 else x // 2
    return x, odd


def period_checks(counts):
    rows = []
    for k in range(17):
        m, scale = 2 ** k, 120 ** k
        weights = []
        numerators = []
        for n in range(m):
            endpoint, odd = shortcut_data(k, n)
            weight = 85 ** (k - odd) * 147 ** odd
            numerator = m * endpoint - 3 ** odd * n
            assert numerator >= 0
            assert 3 ** odd * scale ** 2 <= m * weight ** 2
            weights.append(weight)
            numerators.append(numerator)
            counts["full_period_sources"] += 1
            counts["full_period_shortcut_steps"] += k
            counts["pointwise_square_comparisons"] += 1
        assert sum(weights) == 232 ** k
        assert 4 * sum(numerators) == k * m * m
        counts["full_period_weight_mass_checks"] += 1
        counts["full_period_numerator_mass_checks"] += 1
        # A separate last-bit branch construction checks the full weight law.
        mass_by_count = sum(math.comb(k, j) * 85 ** (k - j) * 147 ** j for j in range(k + 1))
        assert mass_by_count == sum(weights)
        counts["binomial_mass_cross_checks"] += 1
        if k in [0, 1, 2, 4, 8, 12, 16]:
            rows.append({"shortcut_depth": k, "period": m, "integer_weight_mass": 232 ** k,
                         "mean_affine_correction": pair(F(k, 4)),
                         "dyadic_tail_mean_upper_bound": pair(F(29, 15) ** k + F(k, 4))})
    for k in list(range(257)) + [512, 1024, 2048, 4096]:
        assert (k + 2) * 120 ** k <= 2 * 232 ** k
        assert F(120 ** k) * F(29, 15) ** k == 232 ** k
        counts["large_index_scale_and_correction_checks"] += 1
    return {"depths": [0, 16], "rows": rows,
            "scope": "Complete residue periods and actual shortcut computations. Large-index checks concern only exact integer/rational constants, not source censuses."}


def population_checks(counts):
    maximum, max_k = 65536, 16
    floors = [0, 1, 16, 64]
    states = list(range(maximum + 1))
    minima = states.copy()
    snapshots = {0: minima.copy()}
    for t in range(1, 2 * max_k + 1):
        for n in range(1, maximum + 1):
            value = states[n]
            value = 3 * value + 1 if value & 1 else value // 2
            states[n] = value
            minima[n] = min(minima[n], value)
            counts["population_time_major_ordinary_steps"] += 1
        if t % 2 == 0:
            snapshots[t] = minima.copy()
    for n in range(1, maximum + 1):
        value = minimum = n
        for t in range(2 * max_k + 1):
            if t % 2 == 0:
                assert minimum == snapshots[t][n]
                counts["independent_prefix_minimum_comparisons"] += 1
            if t == 2 * max_k:
                break
            value = value // 2 if value % 2 == 0 else 3 * value + 1
            minimum = min(minimum, value)
            counts["population_source_major_ordinary_steps"] += 1
    profiles = {h: [0] * (maximum + 1) for h in floors}
    rows = []
    for k in range(max_k + 1):
        m, scale, mass = 2 ** k, 120 ** k, 232 ** k
        upper = min(maximum, 2 * m - 1)
        snapshot = snapshots[2 * k]
        # Pointwise integer majorants use independent shortcut endpoints.
        for n in range(1, upper + 1):
            endpoint, odd = shortcut_data(k, n)
            counts["pointwise_shortcut_steps"] += k
            weight = 85 ** (k - odd) * 147 ** odd
            numerator = m * endpoint - 3 ** odd * n
            assert m * scale * snapshot[n] <= m * n * weight + scale * numerator
            counts["actual_prefix_word_majorant_checks"] += 1
        for h in floors:
            total = 0
            for n in range(1, upper + 1):
                value = snapshot[n]
                if value > h:
                    total += value
                if n < m:
                    continue
                profiles[h][n] = total
                assert 2 * scale * total <= 4 * n * mass + scale * k * m
                assert 5 * 30 ** k * total <= n * 29 ** k * (m + 14 * n)
                counts["adaptive_population_integer_bounds"] += 1
                counts["adaptive_population_gauge_bounds"] += 1
                if n == m:
                    assert 4 * scale * total <= 4 * m * mass + scale * k * m
                    counts["dyadic_population_sharp_bounds"] += 1
                if k in [0, 1, 4, 8, 12, 16] and n in {m, upper}:
                    rows.append({"floor": h, "cutoff": n, "ordinary_clock": 2 * k,
                                 "actual_prefix_tail_mean": pair(F(total, n)),
                                 "general_upper_bound": pair(2 * F(29, 15) ** k + F(k, 2)),
                                 "dyadic_upper_bound": pair(F(29, 15) ** k + F(k, 4)) if n == m else None})
    return profiles, {"maximum_complete_source": maximum, "maximum_ordinary_clock": 32,
                      "floors": floors, "selected_rows": rows,
                      "scope": "Actual finite-prefix minima at every even clock through32 are compared in two traversal orders for all65536 positive sources. The population clock is2 floor(log2 N). No uncomputed global minimum is assigned."}


def green_checks(profiles, counts):
    rho = F(1704, 1711)

    def gauge(n):
        if n == 0:
            return F(0)
        k = n.bit_length() - 1
        return F(29, 30) ** k * F(2 ** k + 14 * n, 15)

    rows = []
    for h in [1, 16, 64]:
        @lru_cache(None)
        def mean(n):
            assert n < len(profiles[h])
            return F(profiles[h][n], n) if n else F(0)

        @lru_cache(None)
        def residual(n):
            return mean(n) - (mean(n // 2) + mean(3 * ((n - 1) // 2) + 2)) / 2

        @lru_cache(None)
        def backward(depth, n):
            if n <= h:
                return F(0), F(0), F(0)
            if depth == 0:
                return mean(n), F(0), F(0)
            lower = backward(depth - 1, n // 2)
            upper = backward(depth - 1, 3 * ((n - 1) // 2) + 2)
            return ((lower[0] + upper[0]) / 2,
                    residual(n) + (lower[1] + upper[1]) / 2,
                    abs(residual(n)) + (lower[2] + upper[2]) / 2)

        for root in [1, 2, 3, 8, 17, 64, 255, 1024]:
            distribution = {root: F(1)}
            signed = absolute = F(0)
            abs_depths = []
            for depth in range(9):
                terminal = sum((prob * mean(n) for n, prob in distribution.items() if n > h), F(0))
                expected = backward(depth, root)
                assert expected == (terminal, signed, absolute)
                assert mean(root) == terminal + signed
                assert 0 <= terminal <= 3 * rho ** depth * gauge(root)
                abs_depths.append(absolute)
                counts["prefix_profile_green_depth_checks"] += 1
                next_distribution = {}
                for n, prob in distribution.items():
                    if n <= h:
                        continue
                    signed += prob * residual(n)
                    absolute += prob * abs(residual(n))
                    for child in [n // 2, 3 * ((n - 1) // 2) + 2]:
                        next_distribution[child] = next_distribution.get(child, F(0)) + prob / 2
                distribution = next_distribution
            for j in range(6):
                for length in range(4):
                    difference = abs_depths[j + length] - abs_depths[j]
                    assert 0 <= difference <= F(5133, 7) * rho ** j * gauge(root)
                    counts["prefix_profile_absolute_tail_windows"] += 1
            rows.append({"floor": h, "root": root, "mean": pair(mean(root)),
                         "depth8_terminal": pair(backward(8, root)[0]),
                         "depth8_signed_occupation": pair(backward(8, root)[1])})
    return {"rows": rows,
            "scope": "Finite Green bounds are independently compared forward and backward for computable adaptive PREFIX profiles. These values are not substituted for the actual global-minimum residual in the universal Lean theorems."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-population-majorant-") as directory:
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
            if stem == "MinimumPopulationMajorant":
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
    authenticated = {}
    for prior in PRIORS:
        record = json.loads((ROOT / prior).read_text())
        assert record["status"] == "passed"
        for filename, expected in record["sha256"].items():
            assert digest(ROOT / filename) == expected, filename
        authenticated[prior] = len(record["sha256"])
    print("Authenticated prior manifests:", authenticated, flush=True)
    version, builds = build()
    counts = Counter()
    periods = period_checks(counts)
    print("Complete period arithmetic passed.", flush=True)
    profiles, populations = population_checks(counts)
    print("Complete ordinary prefix census and independent replay passed.", flush=True)
    green = green_checks(profiles, counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "periods": periods, "populations": populations,
                              "finite_green_checks": green})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-POPULATION-MAJORANT.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": authenticated,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Exact periodic integer word weights and their complete-period mass; square domination of the affine slope; ordinary-prefix pointwise and population bounds retaining the exact mean affine correction; sharper dyadic bounds; actual global-minimum upper bounds; the previously explicit G<=3V and adaptive-prefix majorants; unconditional finite global-residual truncation and absolute-tail bounds; the least-counterexample diagnostic retains only its positive-residual majorant premise.",
        "written_scope": ["The exponent log2(29/15)<1 gives sublinearity, not a uniform subunit mean.",
                          "The prior infinite Green representation follows by the written monotone/L1 limiting argument, now with its actual-minimum majorant fully kernel proved."],
        "external_dependency": "None for the proof. Tao's paper is cited only to explain why its density theorem is not the required uniform linear-tail estimate.",
        "finite_scope_limit": "All Python minima are finite prefixes. No unknown global minimum or global residual is assigned a numerical value. The finite Green replays use separately identified computable prefix profiles.",
        "not_proved": ["A uniform subunit tail budget, uniform integrability of actual minima, or an independent sufficiently small positive-residual bound.",
                       "A fully formal infinite measure-theoretic assembly, convergence of every positive source, or a counterexample."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
