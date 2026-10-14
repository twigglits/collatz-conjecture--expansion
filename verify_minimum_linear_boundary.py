"""Audit the finite-clock linear boundary in the auxiliary cutoff recurrence.

Cutoff paths are not Collatz orbits. Actual finite prefix values, exact cutoff
averages, the ideal change of measure, and kernel-certified paths have separate
scopes. No asymptotic Collatz conclusion is inferred from finite samples.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import lru_cache
from math import comb
import ast
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-linear-boundary"
SOURCES = ["CollatzContradiction.lean", "CollatzAffine.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
           "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
           "lean/MinimumLinearBoundaryFinite.lean"]
THEOREMS = {
    "MinimumLinearBoundary": [
        "three_step_bits_drift", "potential_nonnegative", "potential_upper", "potential_drift",
        "size_drift", "clocked_exact_unroll", "clock_terminal_nonnegative",
        "duration_potential_budget", "duration_dyadic_bound", "stopped_size_balance",
        "rounding_loss_le_duration", "retained_size_lower", "short_boundary_lower",
        "linear_boundary_lower", "signed_cancellation_bound", "one_step_even_sum",
        "one_step_odd_sum", "one_step_sum_lower", "raw_sum_le_tail_plus_floor",
        "short_tail_sum_lower", "tail_mean_nonnegative", "tail_mean_short_lower",
        "tail_mean_below_floor", "actual_linear_boundary", "every_clock_boundary_256",
        "checks_floor_path_sound", "checks_floor_range_sound"],
    "MinimumLinearBoundaryFinite": ["closed_prefix_tail_zero", "closed_prefix_tail_stays_zero",
                                    "all_late_signed_cancellation"]}
PRIORS = ["results/minimum-cap-transport/verification.json",
          "results/cutoff-descent/verification.json",
          "results/critical-clock-window/verification.json"]


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


def four_potential(n):
    a, b = children(n)
    grandchildren = children(a) + children(b)
    return 4 * n.bit_length() + 2 * (a.bit_length() + b.bit_length()) + sum(
        x.bit_length() for x in grandchildren)


def potential(n):
    return F(four_potential(n), 4)


def leading_coefficient(t):
    return F(3, 7) + F(1, 14) * F(-3, 4) ** t


def profile_and_parity_checks(counts):
    even_weight, odd_weight, contraction = F(17, 24), F(49, 40), F(29, 30)
    assert even_weight ** 2 >= F(1, 2) and odd_weight ** 2 >= F(3, 2)
    assert (even_weight + odd_weight) / 2 == contraction < 1
    for t in range(257):
        coefficient = leading_coefficient(t)
        assert F(3, 8) <= coefficient <= F(1, 2)
        if t >= 2:
            previous, before = leading_coefficient(t - 1), leading_coefficient(t - 2)
            assert coefficient == (previous + 3 * before) / 4
            for n in list(range(1, 257)) + [2 ** 64 - 1, 2 ** 64, 2 ** 64 + 1]:
                a, b = children(n)
                residual = coefficient * n - (previous * a + before * b) / 2
                expected = before / 2 if n % 2 == 0 else (previous - before) / 4
                assert residual == expected and -F(1, 4) <= residual <= F(1, 4)
                counts["exact_leading_profile_rounding_checks"] += 1
        counts["exact_leading_coefficient_checks"] += 1
    parity_rows = []
    for k in range(15):
        words, histogram = set(), Counter()
        for source in range(2 ** k):
            state, odd_count, word = source, 0, 0
            for j in range(k):
                bit = state % 2
                odd_count += bit
                word += bit * 2 ** j
                state = (3 * state + 1) // 2 if bit else state // 2
                counts["parity_residue_shortcut_steps"] += 1
            assert word not in words
            words.add(word)
            histogram[odd_count] += 1
            correction = 2 ** k * state - 3 ** odd_count * source
            assert 0 <= correction <= 3 ** k - 2 ** k
            counts["parity_word_and_affine_correction_checks"] += 1
        assert len(words) == 2 ** k
        assert histogram == {j: comb(k, j) for j in range(k + 1)}
        weighted = F(0)
        for j, amount in histogram.items():
            weight = even_weight ** (k - j) * odd_weight ** j
            slope = F(3 ** j, 2 ** k)
            assert weight ** 2 >= slope and min(F(1), slope) <= weight
            weighted += amount * weight
            counts["rational_word_majorant_checks"] += 1
        assert weighted == (2 * contraction) ** k
        parity_rows.append({"shortcut_length": k, "all_residue_words_checked": len(words),
                            "mean_rational_word_majorant": pair(weighted / 2 ** k)})
    return {"leading_coefficient": "3/7 + (-3/4)^T/14", "even_majorant": pair(even_weight),
            "odd_majorant": pair(odd_weight), "contraction": pair(contraction),
            "parity_rows": parity_rows,
            "scope": "Exact finite checks of the written uniform boundary profile and elementary finite-parity mean bound; their all-scale and limiting assembly is not newly kernel formalized."}


def dyadic_checks(counts):
    def check(n):
        a, b = children(n)
        assert a + b + int(n % 2 == 0) == 2 * n
        assert a.bit_length() + b.bit_length() <= 2 * n.bit_length()
        counts["cutoff_size_and_rank_checks"] += 1
        if n >= 2:
            assert four_potential(n) <= 12 * n.bit_length()
            counts["dyadic_potential_upper_checks"] += 1
        if n >= 4:
            descendants = [n]
            for _ in range(3):
                descendants = [y for x in descendants for y in children(x)]
            assert sum(x.bit_length() for x in descendants) + 1 <= 8 * n.bit_length()
            assert four_potential(a) + four_potential(b) + 1 <= 2 * four_potential(n)
            counts["three_step_rank_and_potential_drift_checks"] += 1
    for n in range(1, 65537):
        check(n)
    large = []
    for k in list(range(3, 129)) + [256, 512, 1024]:
        for offset in [-2, -1, 0, 1, 2]:
            check(2 ** k + offset)
            counts["large_dyadic_arithmetic_checks"] += 1
        if k >= 128:
            large.append({"base": "2^" + str(k), "offsets": [-2, -1, 0, 1, 2]})
    return {"continuous_cutoff_range": [1, 65536], "large_cutoffs": large,
            "scope": "Auxiliary cutoff arithmetic only; no Collatz orbit census at these large dyadic cutoffs."}


def short_mean(h, t, n):
    assert n >= 1
    if n <= h:
        return F(0)
    assert t <= 1
    if t == 0:
        low = min(n, h)
        return F(n * (n + 1) - low * (low + 1), 2 * n)
    a, odd_count = n // 2, (n + 1) // 2
    even_low = min(a, h)
    odd_low = (min(n, h) + 1) // 2
    return F(odd_count ** 2 - odd_low ** 2, n) + F(
        a * (a + 1) - even_low * (even_low + 1), 2 * n)


def short_and_certificate_checks(counts):
    # Read the supplied literal certificate data, rather than regenerate it silently.
    source = (ROOT / SOURCES[-1]).read_text()
    encoded = source.split("private def paths : List (List Nat) := ", 1)[1].split(
        "\n\nset_option", 1)[0]
    paths = ast.literal_eval(encoded)
    assert len(paths) == 256
    maximum_hit = 0
    for n, path in zip(range(256, 0, -1), paths):
        state = n
        assert len(path) <= 128
        for following in path:
            assert following == (state // 2 if state % 2 == 0 else 3 * state + 1)
            state = following
            counts["literal_certificate_edge_checks"] += 1
        assert state <= 4
        maximum_hit = max(maximum_hit, len(path))
        # A distinct full-prefix traversal does not use certificate values.
        current = minimum = n
        for _ in range(128):
            current = 3 * current + 1 if current & 1 else current // 2
            minimum = min(minimum, current)
            counts["independent_closed_witness_steps"] += 1
        assert minimum <= 4
        counts["independent_closed_witness_sources"] += 1
    for h in [0, 1, 3, 4, 16, 64]:
        sums = [0, 0]
        raw_one = 0
        for n in range(1, 1025):
            one = min(n, n // 2 if n % 2 == 0 else 3 * n + 1)
            raw_one += one
            sums[0] += n if n > h else 0
            sums[1] += one if one > h else 0
            assert 8 * raw_one >= 3 * n * n
            for t in [0, 1]:
                assert F(sums[t], n) == short_mean(h, t, n)
                assert F(sums[t], n) >= F(3 * n, 8) - h
                counts["short_clock_formula_and_lower_checks"] += 1
    return {"certified_sources": 256, "floor": 4, "clock": 128,
            "maximum_supplied_floor_hit": maximum_hit,
            "tail_sum": 0, "all_clock_terminal_lower_bound": [103, 2],
            "scope": "The supplied finite paths are also checked in Lean; persistence and signed cancellation for all later clocks are generic kernel consequences."}


def collect_queries(configurations):
    queries = set()
    for h, t, n in configurations:
        stack = [(h, t, n)]
        while stack:
            state = stack.pop()
            if state in queries:
                continue
            queries.add(state)
            hh, tt, nn = state
            if nn > hh and tt > 1:
                a, b = children(nn)
                stack.extend([(hh, tt - 1, a), (hh, tt - 2, b)])
    return queries


def actual_prefix_values(queries, counts):
    maximum = max(n for _, _, n in queries)
    horizon = max(t for _, t, _ in queries)
    wanted = defaultdict(lambda: defaultdict(set))
    for h, t, n in queries:
        wanted[t][h].add(n)
    states = list(range(maximum + 1))
    minima = states.copy()
    values = {}
    for t in range(horizon + 1):
        for h, cutoffs in wanted[t].items():
            total = 0
            for n in range(1, max(cutoffs) + 1):
                value = minima[n]
                total += value if value > h else 0
                if n in cutoffs:
                    values[(h, t, n)] = F(total, n)
                    counts["actual_prefix_population_values"] += 1
        if t < horizon:
            states = [0] + [3 * n + 1 if n & 1 else n // 2 for n in states[1:]]
            minima = [min(n, m) for n, m in zip(states, minima)]
            counts["actual_prefix_census_ordinary_steps"] += maximum
    return values, {"maximum_source": maximum, "ordinary_horizon": horizon,
                    "scope": "Direct ordinary Collatz prefixes for every source, independent of the cutoff recurrence."}


@lru_cache(None)
def recursive_tree(h, t, n):
    # size, steps, rounding loss, clock-boundary probability, tail boundary, potential
    if n <= h or t <= 1:
        return (F(n), F(0), F(0), F(n > h), short_mean(h, t, n), potential(n))
    a, b = children(n)
    left, right = recursive_tree(h, t - 1, a), recursive_tree(h, t - 2, b)
    row = [(x + y) / 2 for x, y in zip(left, right)]
    row[1] += 1
    row[2] += F(int(n % 2 == 0), 2)
    return tuple(row)


def forward_tree(h, t, n, values, counts):
    frontier = {(t, n): 1}
    size = steps = rounding = clock_probability = boundary = terminal_potential = F(0)
    signed = positive = negative = total_probability = F(0)
    profile_occupation = terminal_difference = F(0)
    for depth in range(t + 1):
        following = defaultdict(int)
        for (remaining, cutoff), amount in frontier.items():
            probability = F(amount, 2 ** depth)
            if cutoff <= h or remaining <= 1:
                total_probability += probability
                size += probability * cutoff
                clock_probability += probability * (cutoff > h)
                endpoint = values[(h, remaining, cutoff)]
                assert endpoint == short_mean(h, remaining, cutoff)
                boundary += probability * endpoint
                terminal_difference += probability * (endpoint - leading_coefficient(remaining) * cutoff)
                terminal_potential += probability * potential(cutoff)
                counts["clock_tree_terminal_states"] += 1
                continue
            a, b = children(cutoff)
            error = values[(h, remaining, cutoff)] - (
                values[(h, remaining - 1, a)] + values[(h, remaining - 2, b)]) / 2
            signed += probability * error
            profile_error = leading_coefficient(remaining) * cutoff - (
                leading_coefficient(remaining - 1) * a + leading_coefficient(remaining - 2) * b) / 2
            assert abs(profile_error) <= F(1, 4)
            profile_occupation += probability * profile_error
            positive += probability * max(error, F(0))
            negative += probability * min(error, F(0))
            steps += probability
            rounding += probability * F(int(cutoff % 2 == 0), 2)
            following[(remaining - 1, a)] += amount
            following[(remaining - 2, b)] += amount
            counts["clock_tree_active_states"] += 1
        frontier = following
        if not frontier:
            break
    assert not frontier and total_probability == 1
    summary = (size, steps, rounding, clock_probability, boundary, terminal_potential)
    assert summary == recursive_tree(h, t, n)
    root = values[(h, t, n)]
    assert boundary + signed == root and signed == positive + negative
    assert size + rounding == n and 2 * rounding <= steps
    assert steps <= 8 * (potential(n) - terminal_potential)
    assert steps <= 24 * n.bit_length()
    assert boundary >= F(3, 8) * size - h
    lower = F(3 * n, 8) - F(9 * n.bit_length(), 2) - h
    assert boundary >= lower
    assert boundary - leading_coefficient(t) * n == terminal_difference - profile_occupation
    assert abs(terminal_difference) <= h + 1
    assert abs(profile_occupation) <= steps / 4
    assert abs(boundary - leading_coefficient(t) * n) <= h + 1 + 6 * n.bit_length()
    for k in range(t // 2 + 1):
        upper = (1 + F(2 ** k, n)) * F(29, 30) ** k + F(3, 2) ** k / n
        assert root / n <= upper
        counts["actual_normalized_prefix_majorant_checks"] += 1
    counts["independent_clocked_tree_comparisons"] += 1
    return {"floor": h, "initial_clock": t, "initial_cutoff": n,
            "actual_prefix_tail_mean": pair(root), "terminal_tail_mean": pair(boundary),
            "signed_residual_occupation": pair(signed),
            "positive_residual_occupation": pair(positive),
            "negative_residual_occupation": pair(negative),
            "terminal_cutoff_mean": pair(size), "expected_active_steps": pair(steps),
            "expected_rounding_loss": pair(rounding),
            "clock_boundary_probability": pair(clock_probability),
            "terminal_dyadic_potential": pair(terminal_potential),
            "leading_boundary_profile": pair(leading_coefficient(t) * n),
            "profile_error_occupation": pair(profile_occupation),
            "terminal_profile_difference": pair(terminal_difference),
            "all_clock_kernel_lower_bound": pair(lower)}


def rounded_trees(counts):
    configurations = [(h, t, n) for h in [3, 4, 16] for n in [8, 16, 32, 64, 128]
                      for t in [2, 4, 8, 16, 24, 32] if n > h]
    queries = collect_queries(configurations)
    values, census = actual_prefix_values(queries, counts)
    records = [forward_tree(h, t, n, values, counts) for h, t, n in configurations]
    longer = []
    for t in [8, 16, 24, 32, 40, 48, 56, 64]:
        size, steps, loss, probability, boundary, endpoint_potential = recursive_tree(4, t, 64)
        assert size + loss == 64
        assert steps <= 8 * (potential(64) - endpoint_potential)
        assert boundary >= F(3, 8) * size - 4
        assert abs(boundary - leading_coefficient(t) * 64) <= 4 + 1 + 6 * (64).bit_length()
        longer.append({"floor": 4, "clock": t, "initial_cutoff": 64,
                       "clock_boundary_probability": pair(probability),
                       "terminal_cutoff_mean": pair(size), "terminal_tail_mean": pair(boundary)})
        counts["longer_arithmetic_cutoff_tree_checks"] += 1
    cache = recursive_tree.cache_info().currsize
    recursive_tree.cache_clear()
    return {"actual_prefix_census": census, "rows": records, "longer_cutoff_trees": longer,
            "memoized_exact_cutoff_states": cache,
            "longer_tree_scope": "Cutoff averaging and proved clock-zero/one arithmetic only; no census of long Collatz trajectories at the largest leaf cutoffs."}


def ideal_tilt(counts):
    rows = []
    for level in [4, 8, 16]:
        initial = 2 ** level
        for clock in [32, 64, 128, 256]:
            frontier = {0: 1}  # upper-branch count at the current total branch depth
            fair_clock = tilted_clock = terminal_size = F(0)
            for depth in range(clock + 1):
                following = defaultdict(int)
                for upper_count, amount in frontier.items():
                    current = F(initial * 3 ** upper_count, 2 ** depth)
                    remaining = clock - depth - upper_count
                    fair = F(amount, 2 ** depth)
                    tilted = F(amount * 3 ** upper_count, 4 ** depth)
                    assert fair * current == initial * tilted
                    if current <= 1 or remaining <= 1:
                        terminal_size += fair * current
                        if current > 1:
                            fair_clock += fair
                            tilted_clock += tilted
                    else:
                        following[upper_count] += amount
                        following[upper_count + 1] += amount
                    counts["ideal_exact_tilted_state_checks"] += 1
                frontier = following
                if not frontier:
                    break
            assert not frontier and terminal_size == initial
            assert tilted_clock >= 1 - F(1, initial)
            rows.append({"initial_cutoff": initial, "floor": 1, "clock": clock,
                         "fair_clock_boundary_probability": pair(fair_clock),
                         "size_tilted_clock_boundary_probability": pair(tilted_clock),
                         "terminal_cutoff_mean": pair(terminal_size)})
    return {"rows": rows, "fair_branch_probabilities": [[1, 2], [1, 2]],
            "tilted_branch_probabilities": [[1, 4], [3, 4]],
            "scope": "Ideal unrounded real cutoff chain, not actual Collatz or the rounded integer chain; exact rational change-of-measure checks."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-linear-boundary-") as directory:
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
            if stem in THEOREMS:
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS[stem]}
                assert len(roots) == len(THEOREMS[stem])
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
    dyadic = dyadic_checks(counts)
    closed = short_and_certificate_checks(counts)
    profile = profile_and_parity_checks(counts)
    print("Dyadic potential and independent certificate checks passed.", flush=True)
    trees = rounded_trees(counts)
    print("Exact rounded cutoff trees and actual signed recurrence checks passed.", flush=True)
    tilted = ideal_tilt(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "dyadic_potential": dyadic, "closed_collatz_witness": closed,
                              "boundary_profile_and_finite_parity": profile,
                              "rounded_cutoff_trees": trees, "ideal_size_tilt": tilted})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-LINEAR-BOUNDARY.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": sum(map(len, THEOREMS.values())),
        "prior_hashes_validated": prior_counts, "finite_replay_counts": dict(counts),
        "kernel_scope": "Three-step binary-rank drift and a rational occupation potential; exact clock-stopped unrolling and size balance; a linear terminal lower bound for actual prefix-minimum means at every clock; literal edge certificates for sources 1..256, their all-later-clock floor bound, and the resulting necessary negative signed residual occupation.",
        "written_scope": [
            "Almost-sure auxiliary cutoff absorption follows from the finite occupation bound, but its linear terminal size is not uniformly integrable.",
            "The ideal size change of measure reverses logarithmic drift; rounded cutoffs instead give a substochastic size-weighted kernel.",
            "Uniformly in finite clock, the boundary is [3/7+(-3/4)^T/14]*N with absolute error at most H+1+6*bits(N).",
            "An elementary finite-parity majorant with rational contraction 29/30 proves F_T(N)/N -> 0 for every clock function T(N) -> infinity, and therefore the signed occupation divided by N tends to -3/7 at a fixed floor.",
            "The same elementary estimate gives sublinearity for the actual global-minimum mean, so its clockless boundary vanishes without an analytic mixing premise."],
        "external_dependency": "None for the new arguments. Elementary finite-parity counting uses the existing exact affine identity, freshly rebuilt here; the population and limit assembly remains written. Earlier analytic mixing is context only.",
        "finite_scope_limit": "Python uses exact integers and rational probabilities. Large rational outputs have explicitly tagged outward rational enclosures and exact binary digests. The ideal chain is separate. Its largest leaf values and large dyadic drift tests are arithmetic, not orbit censuses. Only the supplied finite literal paths are kernel-certified as a population calculation.",
        "not_proved": ["A signed residual estimate implying the all-cutoff linear-tail budget.",
                       "Any uniform first-moment tail bound, vanishing nonconvergent mass or full Collatz.",
                       "That a global-minimum boundary remains large; its treatment is explicitly different."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": sum(map(len, THEOREMS.values())),
                      "counts": dict(counts), "closed_witness": closed}, indent=2))


if __name__ == "__main__":
    main()
