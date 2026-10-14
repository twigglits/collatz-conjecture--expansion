"""Finite support for the WRITTEN critical-clock Gaussian window.

Actual censored prefixes, rational population identities and stopped cutoff
trees are checked independently. A separate exact ideal-chain illustration
is not an orbit census or an asymptotic normality certificate.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as F
from functools import cache
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/critical-clock-window"
SOURCES = ["lean/CensoredProgressionTransport.lean", "lean/CutoffDescent.lean",
           "lean/CriticalClockWindow.lean"]
THEOREMS = ["cell_bounds", "cell_increment", "scaled_cell", "even_cell_transport",
            "odd_cell_transport", "odd_cell_correction_bounds", "even_population_transport",
            "fair_residual_bound", "timed_upper_unroll", "timed_lower_unroll",
            "timed_cost_majorant", "remaining_clock_composition", "ideal_clock_balance",
            "stopped_sign_mean", "stopped_sign_second"]
PRIORS = ["results/cutoff-descent/verification.json",
          "results/marked-preimage-audit/verification.json",
          "results/clocked-progression-mixing/verification.json",
          "results/censored-deficit-clock/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + "\n")


def ratio(value):
    return [value.numerator, value.denominator]


def fraction_record(value):
    sizes = [abs(value.numerator).bit_length(), value.denominator.bit_length()]
    if max(sizes) <= 1024:
        return {"fraction": ratio(value)}
    def integer_hash(n):
        return hashlib.sha256(n.to_bytes(max(1, (n.bit_length() + 7) // 8), "big")).hexdigest()
    return {"sign": 1 if value > 0 else -1 if value < 0 else 0,
            "numerator_denominator_bits": sizes,
            "numerator_sha256": integer_hash(abs(value.numerator)),
            "denominator_sha256": integer_hash(value.denominator)}


def lower(n):
    return n // 2


def upper(n):
    return 3 * ((n - 1) // 2) + 2


def actual_prefixes(counts):
    maximum, horizon = 1024, 26
    cells = [[F(0)] * (maximum + 1) for _ in range(horizon + 1)]
    deficits = [[F(0)] * (maximum + 1) for _ in range(horizon + 1)]
    live = [[0] * (maximum + 1) for _ in range(horizon + 1)]
    live_time = [[0] * (maximum + 1) for _ in range(horizon + 1)]
    for source in range(1, maximum + 1):
        state, weight, accumulated, spent, arrived = source, F(1), F(0), 0, False
        for t in range(horizon + 1):
            arrived = arrived or state == 1
            live[t][source] = int(not arrived)
            live_time[t][source] = spent
            cells[t][source] = 1 - weight if not arrived else F(0)
            deficits[t][source] = accumulated
            assert 0 <= cells[t][source] <= live[t][source] <= 1
            assert 0 <= accumulated <= spent <= t
            if t == horizon:
                break
            accumulated += cells[t][source]
            spent += int(not arrived)
            if state & 1:
                weight *= F(3 * state, 3 * state + 1)
                state = 3 * state + 1
            else:
                state //= 2
            counts["direct_ordinary_steps"] += 1
        counts["direct_source_prefixes"] += 1

    for t in range(25):
        for n in range(1, maximum + 1):
            assert deficits[t + 1][n] - deficits[t][n] == cells[t][n]
            counts["cell_deficit_increment_checks"] += 1
        for n in range(1, 257):
            q = 3 * n + 2
            r = F(2 * q - 1, 2 * q)
            assert cells[t + 1][2 * n] == cells[t][n]
            assert cells[t + 2][2 * n + 1] == r * cells[t][q] + (1 - r) * live[t][q]
            assert 0 <= cells[t + 2][2 * n + 1] - cells[t][q] <= F(1, 2 * q)
            assert deficits[t + 1][2 * n] == deficits[t][n]
            correction = (1 + live_time[t][q] - deficits[t][q]) / (2 * q)
            assert deficits[t + 2][2 * n + 1] == deficits[t][q] + correction
            counts["even_cell_transport_checks"] += 1
            counts["odd_cell_transport_and_correction_checks"] += 1
            counts["even_and_odd_deficit_transport_checks"] += 1

    prefix = {}
    progressions = {}
    corrections = {}
    extent = (maximum - 2) // 3
    harmonic = [F(0)]
    for n in range(1, extent + 1):
        harmonic.append(harmonic[-1] + F(1, n))
    for kind, values in [("cell", cells), ("deficit", deficits)]:
        prefix[kind], progressions[kind], corrections[kind] = [], [], []
        for t in range(horizon + 1):
            row = [F(0)]
            for value in values[t][1:]:
                row.append(row[-1] + value)
            prefix[kind].append(row)
            sampled, corrected = [F(0)], [F(0)]
            for j in range(1, extent + 1):
                q = 3 * j + 2
                sampled.append(sampled[-1] + values[t][q])
                excess = ((live[t][q] - cells[t][q]) if kind == "cell" else
                          (1 + live_time[t][q] - deficits[t][q])) / (2 * q)
                corrected.append(corrected[-1] + excess)
            progressions[kind].append(sampled)
            corrections[kind].append(corrected)

    @cache
    def mean(kind, t, n):
        assert 0 <= t <= horizon and 1 <= n <= maximum
        return prefix[kind][t][n] / n

    @cache
    def residual(kind, t, n):
        return mean(kind, t, n) - (mean(kind, max(0, t - 1), lower(n)) +
                                  mean(kind, max(0, t - 2), upper(n))) / 2

    @cache
    def error(kind, t, n):
        ell = (n - 1) // 2
        assert 1 <= ell <= extent
        if t == 0 or kind == "deficit" and t == 1:
            return F(0)
        if t == 1:
            return harmonic[ell] / (6 * n)
        delta = progressions[kind][t - 2][ell] / ell - mean(kind, t - 2, upper(n))
        cap = 1 if kind == "cell" else t
        return abs(delta) / 2 + cap * (harmonic[ell] / (6 * n) + F(1, n))

    @cache
    def common_error(n):
        # A finite observed majorant, NOT the analytic g_R or a fitted constant.
        return max(max(error("cell", t, n), error("deficit", t, n) / max(1, t))
                   for t in range(25))

    population_cutoffs = [3, 4, 7, 8, 15, 16, 31, 32, 63, 64, 95, 96, 127, 128]
    for n in population_cutoffs:
        a, ell, c = lower(n), (n - 1) // 2, upper(n)
        for t in range(25):
            for kind in ("cell", "deficit"):
                if t >= 2:
                    delta = progressions[kind][t - 2][ell] / ell - mean(kind, t - 2, c)
                    correction = corrections[kind][t - 2][ell]
                    exact = (a * mean(kind, t - 1, a) + ell * mean(kind, t - 2, c) +
                             ell * delta + correction) / n
                    assert exact == mean(kind, t, n)
                    cap = 1 if kind == "cell" else t - 1
                    assert 0 <= correction <= cap * harmonic[ell] / 6
                    counts["exact_both_parity_population_identities"] += 1
                assert abs(residual(kind, t, n)) <= error(kind, t, n)
                counts["two_sided_population_residual_bounds"] += 1
    record = {"maximum_source": maximum, "ordinary_horizon": horizon,
              "population_cutoffs": population_cutoffs, "tested_population_clocks": [0, 24],
              "alive_at_horizon": sum(live[horizon]),
              "future_arrivals_used": False,
              "scope": "All prefixes generated independently through a fixed ordinary clock; alive is not nonconvergent."}
    return record, mean, residual, error, common_error


def timed_trees(counts, mean, residual, error, common_error):
    rows = []
    for n, h in itertools.product([8, 16, 32], [3, 8]):
        if n <= h:
            continue
        for depth in range(6):
            distribution = Counter({(n, 0): 1})
            clocks = [0, 1, 2, 8, 16, 24]
            signed = {(kind, t): F(0) for kind in ("cell", "deficit") for t in clocks}
            bounded = dict(signed)
            occupation = F(0)
            for j in range(depth):
                following = Counter()
                for (state, consumed), multiplicity in distribution.items():
                    if state <= h:
                        following[state, consumed] += 2 * multiplicity
                        continue
                    probability = F(multiplicity, 2 ** j)
                    occupation += probability * common_error(state)
                    for kind, t in signed:
                        s = max(0, t - consumed)
                        value = residual(kind, s, state)
                        bound = error(kind, s, state)
                        assert abs(value) <= bound
                        assert bound <= (1 if kind == "cell" else s) * common_error(state)
                        signed[kind, t] += probability * value
                        bounded[kind, t] += probability * bound
                        counts["timed_tree_node_residual_checks"] += 1
                    following[lower(state), consumed + 1] += multiplicity
                    following[upper(state), consumed + 2] += multiplicity
                distribution = following
            assert sum(distribution.values()) == 2 ** depth
            for kind, t in signed:
                terminal = sum((F(mult, 2 ** depth) * mean(kind, max(0, t - j), state)
                                for (state, j), mult in distribution.items()), F(0))
                cap_terminal = sum((F(mult, 2 ** depth) *
                                    (int(t > j) if kind == "cell" else max(0, t - j))
                                    for (_, j), mult in distribution.items()), F(0))
                assert 0 <= terminal <= cap_terminal
                assert mean(kind, t, n) == terminal + signed[kind, t]
                assert abs(signed[kind, t]) <= bounded[kind, t]
                assert bounded[kind, t] <= (1 if kind == "cell" else t) * occupation
                counts["exact_clocked_unroll_and_cost_checks"] += 1
            rows.append({"start": n, "floor": h, "depth": depth,
                         "terminal_states_and_clocks": len(distribution),
                         "sampled_clocks": clocks,
                         "finite_observed_error_occupation": fraction_record(occupation)})
    return rows


def stopped_signs(counts):
    rows = []
    for n, h in itertools.product([8, 16, 32, 64], [3, 8, 16]):
        if n <= h:
            continue
        distribution = Counter({(n, 0, 0, 0): 1})
        for depth in range(13):
            assert sum(distribution.values()) == 2 ** depth
            sign_mean = sum(mult * s for (_, _, s, _), mult in distribution.items())
            sign_second = sum(mult * s * s for (_, _, s, _), mult in distribution.items())
            steps = sum(mult * k for (_, _, _, k), mult in distribution.items())
            consumed = sum(mult * j for (_, j, _, _), mult in distribution.items())
            assert sign_mean == 0 and sign_second == steps and 2 * consumed == 3 * steps
            counts["stopped_sign_mean_and_second_moment_checks"] += 1
            following = Counter()
            for (state, j, s, k), mult in distribution.items():
                assert 2 * j == 3 * k + s
                counts["branch_clock_sign_balance_checks"] += 1
                if state <= h:
                    assert F(h, 2) <= state <= h
                    following[state, j, s, k] += 2 * mult
                else:
                    following[lower(state), j + 1, s - 1, k + 1] += mult
                    following[upper(state), j + 2, s + 1, k + 1] += mult
            if depth < 12:
                distribution = following
        rows.append({"start": n, "floor": h, "maximum_depth": 12,
                     "terminal_states_with_marks": len(distribution),
                     "expected_stopped_steps": ratio(F(steps, 2 ** 12))})

    # Continue the iid signs after absorption when comparing with fixed time.
    for n in [8, 16]:
        for h in [3, 8]:
            for fixed in [0, 3, 6, 10]:
                squared, duration = 0, 0
                for word in itertools.product([-1, 1], repeat=10):
                    state, stopped, sign = n, 0, 0
                    for xi in word:
                        if state > h:
                            state = lower(state) if xi == -1 else upper(state)
                            stopped += 1
                            sign += xi
                    squared += (sign - sum(word[:fixed])) ** 2
                    duration += abs(stopped - fixed)
                    counts["bounded_isometry_paths"] += 1
                assert squared == duration
                counts["bounded_stopping_fixed_time_isometries"] += 1
    return rows


def log_bounds(a, b, terms=48):
    assert a > b > 0
    z = F(a - b, a + b)
    lo = 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(terms)), F(0))
    return lo, lo + 2 * z ** (2 * terms + 1) / ((2 * terms + 1) * (1 - z * z))


def ideal_chain(counts):
    """Exact iid branch DP on the real multiplicative chain, compared by integers."""
    log2, log43 = log_bounds(2, 1), log_bounds(4, 3)
    rows = []
    for k in [8, 16, 32, 64, 128]:
        tlo = 3 * k * log2[0] / log43[1]
        thi = 3 * k * log2[1] / log43[0]
        horizon = tlo.numerator // tlo.denominator
        assert horizon == thi.numerator // thi.denominator
        counts["exact_critical_clock_log_brackets"] += 1
        active = Counter({0: 1})
        hit_numerator = payoff_numerator = 0
        powers3 = [3 ** u for u in range(horizon + 1)]
        for j in range(horizon):
            following = Counter()
            for u, multiplicity in active.items():
                for upper_branch in [0, 1]:
                    j2, u2 = j + 1, u + upper_branch
                    consumed = j2 + u2
                    if consumed > horizon:
                        continue
                    counts["ideal_chain_exact_dp_transitions"] += 1
                    hit = j2 >= k and powers3[u2] <= 2 ** (j2 - k)
                    if hit:
                        mass = multiplicity * 2 ** (horizon - j2)
                        hit_numerator += mass
                        payoff_numerator += mass * (horizon - consumed)
                    elif consumed < horizon:
                        following[u2] += multiplicity
            active = following
        cdf = F(hit_numerator, 2 ** horizon)
        payoff = F(payoff_numerator, 2 ** horizon)
        assert 0 < cdf < 1 and 0 < payoff <= horizon * cdf
        rows.append({"source_floor_ratio": "2^" + str(k), "ordinary_clock": horizon,
                     "probability_absorbed_by_clock": ratio(cdf),
                     "remaining_probability": ratio(1 - cdf),
                     "expected_positive_remaining_clock": ratio(payoff),
                     "squared_payoff_divided_by_k": ratio(payoff * payoff / k)})
    return {"chain": "Ideal real cutoffs n/2 and 3n/2 with equal probabilities, floor 1, branch clocks 1 and 2.",
            "method": "All contributing words grouped exactly by length and upper-branch count; integer comparisons decide first absorption.",
            "critical_clock_method": "48-term rational atanh brackets for log 2 and log(4/3); both endpoints have the same floor.",
            "limitation": "Illustration only; not actual Collatz trajectories, the rounded cutoff chain, or a Gaussian-limit proof.",
            "rows": rows}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-critical-clock-") as directory:
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
    prefixes, mean, residual, error, common_error = actual_prefixes(counts)
    print("Actual ordinary prefixes and both-parity population checks passed.", flush=True)
    trees = timed_trees(counts, mean, residual, error, common_error)
    print("Exact clocked finite unroll and error-majorant checks passed.", flush=True)
    signs = stopped_signs(counts)
    ideal = ideal_chain(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "actual_prefixes": prefixes, "clocked_cutoff_trees": trees,
                              "stopped_sign_trees": signs, "ideal_chain_illustration": ideal})
    files = SOURCES + [Path(__file__).name, "docs/CRITICAL-CLOCK-WINDOW.md",
                      "docs/CENSORED-DEFICIT-CLOCK.md", "docs/CLOCKED-MINIMUM.md",
                      "docs/CLOCKED-PROGRESSION-MIXING.md", "docs/MINIMUM-LOG-MOMENTS.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": prior_counts,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Actual censored cell bounds, deficit increments and even/odd transport; even population transport; fair-coefficient error bound; finite clocked upper/lower unrolling and cost majorant; clock algebra and stopped-sign mean/second moments.",
        "written_scope": [
            "For T=floor(kappa log N+u sqrt(log N)), mean censored cell tends to b Phi(u/sigma).",
            "The mean censored deficit divided by sqrt(log N) tends to b [u Phi(u/sigma)+sigma phi(u/sigma)].",
            "kappa=3/log(4/3), sigma^2=2 (log 6)^2/[log(4/3)]^3; b is the unknown nonconvergent lost-weight mass.",
            "The moving cutoff floor exp((log N)^(1/4)), summable recurrence errors, stopped-sign CLT, and uniform super-logarithmic boundary settling justify these deductions."],
        "analytic_dependencies": {
            "critical_order_upper_bound": "Local WRITTEN uniform-in-time progression mixing plus the written cutoff drift, potentials and stopping estimates.",
            "limit_identification": "Additionally the earlier WRITTEN minimum-clock concentration, minimum tightness and limiting mean nonconvergent lost weight.",
            "external_predecessor_density": "Used only to turn the unproved zero-amplitude criterion into full pointwise Collatz, as in the earlier censored-clock note.",
            "external_source_replayed": False},
        "finite_scope_limit": "Exact rational bounded-prefix and finite auxiliary-chain checks. The ideal multiplicative chain is separately labeled. No floating-point proof decisions, future arrival decisions, or finite certification of analytic mixing or asymptotic normality.",
        "not_proved": ["The local analytic mixing premise or Gaussian limit in Lean.",
                       "Effective asymptotic constants or convergence rates.",
                       "Uniform integrability of lifetime deficit or arrival clocks.",
                       "Zero nonconvergent lost-weight mass, either critical zero limit, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
