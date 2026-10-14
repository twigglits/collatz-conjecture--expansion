"""Check minimum-tail rigidity and an explicitly NON-Collatz gauge barrier.

Kernel implications do not establish their uniform Collatz budget premise.
The comparison map's infinite escaping spine has an existing kernel proof;
no fuel timeout is treated as escape. Infinite moment conclusions are written.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_density_countermodel import step as comparison_step, spine, spine_index

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-tail-rigidity"
SOURCES = ["CollatzContradiction.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean"]
THEOREMS = ["minimum_attained", "minimum_le", "minimum_positive", "minimum_idempotent",
            "term_le_sum", "sum_mono", "diagonal_tail_lower", "tail_budget_rigidity",
            "minimum_budget_iff_bounded", "prefix_lower_bound", "minimum_le_prefix",
            "tail_term_mono", "finite_prefix_budget", "bounded_minimum_verified_floor",
            "finite_prefix_verified_floor", "comparison_spine_minimum", "dyadic_budget_bound",
            "progression_count_weight", "uniform_atom_majorant"]
PRIORS = ["results/critical-clock-window/verification.json",
          "results/cutoff-descent/verification.json",
          "results/density-countermodel/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    return [value.numerator, value.denominator]


def tail_sum(values, floor):
    return sum(n for n in values if n > floor)


def finite_maps(counts):
    """Exhaust all maps on four positive states, including other cycles."""
    examples = []
    for word in itertools.product(range(1, 5), repeat=4):
        transition = (0,) + word
        minima, prefixes = [0], [[]]
        for n in range(1, 5):
            state, seen = n, set()
            while state not in seen:
                seen.add(state)
                state = transition[state]
            minima.append(min(seen))
            state, minimum, sequence = n, n, []
            for _ in range(9):
                minimum = min(minimum, state)
                sequence.append(minimum)
                state = transition[state]
            assert sequence[4] == minima[n]
            prefixes.append(sequence)
        for n in range(1, 5):
            assert minima[minima[n]] == minima[n]
            counts["finite_map_minimum_idempotence_checks"] += 1
        for h in range(5):
            budgets = [tail_sum(minima[1:n + 1], h) for n in range(1, 5)]
            bounded = max(minima) <= h
            assert all(total < n for n, total in enumerate(budgets, 1)) == bounded
            counts["exhaustive_finite_map_budget_equivalences"] += 1
            if not bounded:
                a = next(m for m in minima[1:] if m > h)
                assert budgets[a - 1] >= a
                counts["finite_map_diagonal_witnesses"] += 1
                if len(examples) < 8:
                    examples.append({"map_on_1_through_4": word, "floor": h,
                                     "attained_minimum": a, "diagonal_sum": budgets[a - 1]})
            for t in [0, 1, 2, 4, 8]:
                sums = [tail_sum([prefixes[j][t] for j in range(1, n + 1)], h)
                        for n in range(1, 5)]
                assert all(b <= s for b, s in zip(budgets, sums))
                assert not all(s < n for n, s in enumerate(sums, 1)) or bounded
                counts["finite_map_prefix_budget_implications"] += 1
        counts["complete_four_state_maps"] += 1
    return examples


def collatz_prefixes(counts):
    clocks = [0, 1, 2, 8, 16, 32, 64, 128]
    maximum = 8192
    rows = {t: [0] for t in clocks}
    for n in range(1, maximum + 1):
        state = minimum = n
        for t in range(clocks[-1] + 1):
            minimum = min(minimum, state)
            if t in rows:
                rows[t].append(minimum)
            if t < clocks[-1]:
                state = 3 * state + 1 if state & 1 else state // 2
                counts["actual_ordinary_collatz_steps"] += 1
        counts["actual_collatz_prefixes"] += 1
    sample = []
    for h in [1, 4, 16, 64, 256]:
        for n in [32, 64, 128, 256, 512, 1024, 2048, 4096, 8192]:
            previous = None
            for t in clocks:
                total = tail_sum(rows[t][1:n + 1], h)
                if previous is not None:
                    assert total <= previous
                    counts["actual_prefix_tail_monotonicity_checks"] += 1
                previous = total
                sample.append({"source_cutoff": n, "floor": h, "ordinary_clock": t,
                               "prefix_minimum_tail_sum": total,
                               "strict_budget_at_this_cutoff": total < n})
    assert any(row["strict_budget_at_this_cutoff"] for row in sample)
    assert any(not row["strict_budget_at_this_cutoff"] for row in sample)
    return {"maximum_source": maximum, "clocks": clocks, "rows": sample,
            "scope": "Finite-prefix minima only. No future minimum or convergence decision; no assertion for all cutoffs."}


def minimum_formula(n):
    odd = n // (n & -n)
    if odd % 4 == 1:
        return 1
    index = (odd + 1) // 4
    return 4 * (index & -index) - 1


def classified_minimum(n, counts):
    """Follow actual comparison steps to 1 or the already proved escaping spine."""
    state, minimum, seen = n, n, set()
    while True:
        minimum = min(minimum, state)
        if state == 1:
            return minimum, False
        if spine_index(state) is not None:
            # The existing all-time formulas and new lower-bound theorem
            # certify that the continuation never falls below this state.
            return minimum, True
        assert state not in seen and len(seen) < 1024, (n, state, "unclassified")
        seen.add(state)
        state = comparison_step(state)
        counts["comparison_map_direct_steps"] += 1


def atom_count(n, k):
    v, total, scaled = spine(k), 0, n
    while scaled >= v:
        total += (scaled - v) // (2 * (v + 1)) + 1
        scaled //= 2
    return total


def gauge_weight(v, q):
    assert v == 1 or spine_index(v) is not None
    level = (v + 1).bit_length() - 1
    assert 2 ** level == v + 1
    return F(v, level ** q)


def comparison_gauges(counts):
    maximum = 32768
    histogram, sample, diagonal = Counter(), [], []
    gauges = [0, 1, 2, 3]
    selected = {64, 256, 1024, 4096, 16384, maximum}
    floors = [1, 3, 7, 15, 31, 63, 255, 1023, 4095]
    escaping = 0
    linear_sum = 0
    for n in range(1, maximum + 1):
        actual, escape = classified_minimum(n, counts)
        assert actual == minimum_formula(n)
        assert escape == (actual != 1)
        assert minimum_formula(actual) == actual
        histogram[actual] += 1
        escaping += escape
        linear_sum += actual
        counts["comparison_map_minimum_classifications"] += 1
        for v, amount in histogram.items():
            if v == 1:
                continue
            assert v * amount <= 2 * n
            assert (v + 1) * amount <= 3 * n
            counts["uniform_finite_atom_majorant_checks"] += 1
        k = spine_index(n)
        if k is not None:
            assert histogram[n] == 1
            total = sum(v * amount for v, amount in histogram.items() if v > n - 1)
            assert total >= n
            diagonal.append({"minimum": n, "floor": n - 1, "source_cutoff": n,
                             "linear_tail_sum": total, "normalized_tail": pair(F(total, n))})
            counts["explicit_escaping_diagonal_witnesses"] += 1
        if n not in selected:
            continue
        for k in range(n.bit_length() + 2):
            assert histogram[spine(k)] == atom_count(n, k)
            counts["complete_exact_atom_count_comparisons"] += 1
        row = {"source_cutoff": n, "escaping_sources": escaping,
               "linear_minimum_mean": pair(F(linear_sum, n)), "gauges": []}
        for q in gauges:
            mean = sum((amount * gauge_weight(v, q) for v, amount in histogram.items()), F(0)) / n
            level = n.bit_length() - 1
            assert n == 2 ** level
            exact_dyadic = F(1, 2) + F(1, n) + sum(
                (gauge_weight(spine(k), q) / (spine(k) + 1) for k in range(level - 1)), F(0))
            assert mean == exact_dyadic
            counts["exact_dyadic_gauge_mean_checks"] += 1
            tails = []
            for h in floors:
                k = 0
                while spine(k) <= h:
                    k += 1
                tail = sum((amount * gauge_weight(v, q) for v, amount in histogram.items() if v > h), F(0)) / n
                if q > 1:
                    bound = F(3, (q - 1) * (k + 1) ** (q - 1))
                    assert tail <= bound
                    counts["nearly_linear_uniform_tail_checks"] += 1
                else:
                    bound = None
                tails.append({"floor": h, "least_spine_index_above_floor": k,
                              "weighted_mean_tail": pair(tail),
                              "uniform_bound_when_q_greater_than_one": pair(bound) if bound is not None else None})
            row["gauges"].append({"q": q, "weight": "v/[log_2(v+1)]^q", "mean": pair(mean), "tails": tails})
        sample.append(row)

    large_dyadic = []
    for level in list(range(1, 65)) + [128, 256, 512, 1024]:
        n = 2 ** level
        bad_count = weighted = 0
        for k in range(level):
            actual = atom_count(n, k)
            expected = 2 ** (level - k - 2) if k <= level - 2 else 0
            assert actual == expected
            bad_count += actual
            weighted += spine(k) * actual
            counts["large_dyadic_exact_atom_formulas"] += 1
        assert bad_count == n // 2 - 1
        weighted += n - bad_count
        assert weighted == (level - 1) * n + 2
        counts["exact_dyadic_linear_mean_formulas"] += 1
        if level >= 64:
            large_dyadic.append({"source_cutoff": "2^" + str(level),
                                 "exact_linear_mean": pair(F(weighted, n))})

    limiting_brackets = []
    for q in [2, 3]:
        terms = 64
        partial = F(1, 2) + sum((F(spine(k), (spine(k) + 1) * (k + 2) ** q)
                                for k in range(terms)), F(0))
        remainder = F(1, (q - 1) * (terms + 1) ** (q - 1))
        limiting_brackets.append({"q": q, "spine_terms": terms,
                                  "written_limiting_mean_lower": pair(partial),
                                  "written_limiting_mean_upper": pair(partial + remainder),
                                  "remainder_bound": pair(remainder)})
    for k in range(1, 257):
        assert F(1, (k + 1) ** 2) <= F(1, k * (k + 1)) == F(1, k) - F(1, k + 1)
        counts["exact_rational_square_tail_comparisons"] += 1
    return {"map": "DensityCountermodel.step, explicitly different from Collatz",
            "maximum_source": maximum, "population_rows": sample,
            "linear_diagonal_witnesses": diagonal,
            "large_dyadic_count_formula_checks": large_dyadic,
            "gauge_limit_brackets_from_written_series": limiting_brackets,
            "scope": "All source classifications end at 1 or the previously kernel-proved infinite spine. Gauge series and infinite uniformity are written deductions, not inferred from the samples."}


def bounded_mean_comparison(counts):
    """The second altered map J doubles powers of two >1 and sends others to 1."""
    total, rows = 0, []
    for n in range(1, 32769):
        is_spine = n > 1 and n & (n - 1) == 0
        minimum = n if is_spine else 1
        total += minimum
        assert total < 3 * n
        counts["bounded_first_mean_comparison_checks"] += 1
        if is_spine:
            assert total == 3 * n - (n.bit_length() - 1) - 2
            rows.append({"source_cutoff": n, "minimum_sum": total,
                         "mean": pair(F(total, n)), "diagonal_tail_at_floor_n_minus_one": [1, 1]})
    return {"map": "J(2^k)=2^(k+1) for k>=1; J(n)=1 otherwise. Not Collatz; does not retain even halving.",
            "written_conclusion": "Uniform first means are bounded by 3 and their supremum is 3, but minimum tails are not uniformly integrable. The limiting minimum law is delta_1.",
            "power_of_two_rows": rows}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-minimum-tail-") as directory:
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
    finite = finite_maps(counts)
    actual = collatz_prefixes(counts)
    print("Finite-map rigidity and actual Collatz prefix checks passed.", flush=True)
    comparison = comparison_gauges(counts)
    bounded = bounded_mean_comparison(counts)
    print("Exact comparison-map classifications, atom counts and gauge checks passed.", flush=True)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "finite_map_diagonal_examples": finite,
                              "actual_collatz_finite_prefixes": actual,
                              "escaping_comparison_gauges": comparison,
                              "bounded_mean_comparison": bounded})
    files = SOURCES + [Path(__file__).name, "verify_density_countermodel.py",
                      "docs/MINIMUM-TAIL-RIGIDITY.md", "docs/DENSITY-COUNTERMODEL.md",
                      "docs/MINIMUM-LOG-MOMENTS.md", "docs/CRITICAL-CLOCK-WINDOW.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": prior_counts,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Attained actual Collatz minimum and its idempotence; diagonal lower bound and uniform linear-tail rigidity; finite-prefix sufficient budget and verified-floor implication; the explicitly altered map's all-time spine minimum; finite counting and dyadic-budget arithmetic.",
        "written_scope": [
            "Uniform integrability of the actual minimum itself is equivalent to a finite global minimum bound, hence to a finite collection of eventual cycles. A verified floor would select the known cycle.",
            "In the escaping comparison map, all finite-population minimum atoms are bounded by three times their limiting mass.",
            "For every nonnegative finite weight w, uniform minimum-level weighted-tail decay in that comparison map is equivalent to summability of w(2^(k+2)-1)/2^(k+2).",
            "Consequently all powers p<1, all logarithmic powers and weights m/[log_2(m+1)]^q for q>1 have vanishing uniform tails despite positive-density escape.",
            "A separate map with zero-density escape has uniformly bounded first means and limiting minimum law delta_1, but fails first-moment uniform integrability."],
        "external_dependency": "None for the new implications or comparison-map moment deductions. Prior Collatz mixing is context only, not a premise of the rigidity theorem.",
        "source_review": {
            "date": "2026-10-14",
            "urls": ["https://www.proofatlas.ai/formalizations/natural-density-log-time-collatz/",
                     "https://www.proofatlas.ai/proofs/artifact.collatz.predecessors_positive_lower_density.v001.html"],
            "scope": "Checked advertised growing-threshold and target-dependent quantifiers; no new external theorem or fresh external Lean replay used."},
        "finite_scope_limit": "Actual Collatz work uses bounded prefixes only. Comparison-map escape uses the prior all-time kernel formulas, not timeouts. Exact rational gauge checks are finite; infinite moment statements have separate written proofs. No floating-point proof decisions.",
        "not_proved": ["A uniform linear minimum-tail budget for Collatz, even at one verified floor.",
                       "First-moment uniform integrability of the Collatz minimum.",
                       "Vanishing nonconvergent mass, exclusion of all escapes or additional cycles, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
