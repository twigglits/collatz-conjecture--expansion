"""Audit actual minimum roots and distinguish global from finite cap budgets.

Python evaluates global minima only for paths with an explicit arrival at one.
Unfinished paths supply finite-prefix data, never numerical global minima.
The infinite reciprocal-sum consequence remains a written limiting argument.
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
OUT = ROOT / "results/minimum-root-spine"
PRIOR = "results/minimum-population-majorant/verification.json"
SOURCES = [
    "CollatzAffine.lean", "lean/CoalescenceTail.lean",
    "lean/EscapeWeightRefinements.lean", "lean/CountReturnControl.lean",
    "lean/CountReturnClock.lean", "lean/ReturnCorrectionMoments.lean",
    "lean/OrderedWeightDrift.lean", "lean/ReversalPersistence.lean",
    "lean/ReturnImageBounds.lean", "lean/BinaryImageEnergy.lean",
    "CollatzContradiction.lean", "lean/ClockedMinimum.lean",
    "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
    "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
    "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
    "lean/MinimumGreenKernel.lean", "lean/MinimumClockBarrier.lean",
    "lean/MinimumPopulationMajorant.lean", "lean/MinimumRootSpine.lean",
]
THEOREMS = ["minimum_le_source","minimum_suffix","minimum_bellman","minimum_self_iff","minimum_even","minimum_odd","global_odd_cap","self_minimum_odd","self_minimum_mod16","next_root_self","next_root_ge","next_root_upper","next_root_fixed_iff","step_not_zero_mod3","iterate_not_zero_mod3","next_root_not_zero_mod3","step_cap_add","step_cap_positive_iff","step_cap_even","orbit_caps_telescope","root_self","root_positive","root_clock_attained","root_clock_strict","root_monotone","root_fixed_eventual","root_strict","root_lower","bounded_tail_iff_eventual","bounded_caps_iff_eventual","root_gt_one","root_spacing","root_growth","root_upper","root_successor_mod48","aperiodic_caps_unbounded","convergent_caps_zero","finite_caps_telescope","finite_caps_one","global_caps_one","one_cycle_iterate","finite_caps_cycle","high_self_count_weighted","root_shell_le_prefix","prefix_root_shell_integer","prefix_root_shell_bound","root_shell_bound","rate_half_identity","shell_tail_identity","shell_tail_nonnegative","shell_harmonic_with_tail","shell_harmonic_bound"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def pair(value):
    value = F(value)
    return [value.numerator, value.denominator]


def ordinary_path(n, clock):
    path = [n]
    for _ in range(clock):
        x = path[-1]
        path.append(3 * x + 1 if x & 1 else x // 2)
    return path


def blocked_prefix(n, clock, counts):
    """Independent exact-clock replay, taking odd+even pairs together."""
    value = minimum = n
    remaining = clock
    while remaining:
        if value % 2 == 0:
            value //= 2
            remaining -= 1
            counts["independent_even_shortcut_steps"] += 1
        elif remaining == 1:
            value = 3 * value + 1
            remaining = 0
            counts["independent_final_odd_steps"] += 1
        else:
            value = (3 * value + 1) // 2
            remaining -= 2
            counts["independent_odd_shortcut_pairs"] += 1
        minimum = min(minimum, value)
    return minimum, value


def finite_cap_data(path, counts):
    """Backward suffix minima versus a forward prefix minimum and endpoint."""
    suffix = [0] * len(path)
    suffix[-1] = path[-1]
    for i in range(len(path) - 2, -1, -1):
        suffix[i] = min(path[i], suffix[i + 1])
    cap_total = 0
    positive = 0
    for i in range(len(path) - 1):
        delta = suffix[i + 1] - suffix[i]
        assert delta >= 0
        assert delta == max(suffix[i + 1] - path[i], 0)
        if delta:
            assert suffix[i] == path[i]
            positive += 1
        if path[i] % 2 == 0:
            assert delta == 0
        cap_total += delta
        counts["finite_suffix_cap_edges"] += 1
    assert suffix[0] == min(path)
    assert cap_total == path[-1] - min(path)
    counts["finite_cap_telescope_checks"] += 1
    return cap_total, positive


def shell_checks(counts):
    rows = []
    weighted_counts = F(0)
    weighted_envelopes = F(0)
    for k in range(16):
        clock = 2 * (k + 1)
        roots = 0
        cap_sum = 0
        for n in range(2 ** k + 1, 2 ** (k + 1) + 1):
            path = ordinary_path(n, clock)
            counts["complete_shell_sources"] += 1
            counts["complete_shell_ordinary_steps"] += clock
            minimum, endpoint = blocked_prefix(n, clock, counts)
            assert minimum == min(path) and endpoint == path[-1]
            counts["independent_exact_clock_comparisons"] += 1
            roots += minimum == n
            cap, _ = finite_cap_data(path, counts)
            cap_sum += cap
        scale, mass = 120 ** (k + 1), 232 ** (k + 1)
        assert 2 * scale * roots <= 4 * mass + scale * (k + 1)
        upper = 2 * F(29, 15) ** (k + 1) + F(k + 1, 2)
        assert roots <= upper
        weighted_counts += F(roots, 2 ** k)
        weighted_envelopes += upper / 2 ** k
        tail = 116 * F(29, 30) ** (k + 1) + F(k + 3, 2 ** (k + 1))
        assert weighted_counts <= weighted_envelopes
        assert weighted_envelopes + tail == 118
        counts["prefix_root_shell_bounds"] += 1
        counts["prefix_weighted_shell_budget_checks"] += 1
        rows.append({
            "shell": [2 ** k + 1, 2 ** (k + 1)],
            "ordinary_clock": clock,
            "finite_no_descent_sources": roots,
            "root_count_upper_bound": pair(upper),
            "weighted_prefix_root_count_through_shell": pair(weighted_counts),
            "sum_of_finite_orbit_caps": cap_sum,
        })
    return {
        "complete_source_interval": [2, 65536],
        "clock_rule": "2*(k+1) on 2^k < n <= 2^(k+1)",
        "rows": rows,
        "scope": "These are finite no-descent counts, which bound the unknown global root counts from above. Positive finite caps are not global cap values.",
    }


def extra_prefix_checks(counts):
    starts = [1, 2, 3, 7, 27, 97, 837799, 2 ** 31 - 1, 2 ** 63 - 1]
    clocks = [0, 1, 2, 3, 6, 16, 32, 64, 128, 256]
    rows = []
    for n in starts:
        for clock in clocks:
            path = ordinary_path(n, clock)
            counts["extra_prefix_ordinary_steps"] += clock
            minimum, endpoint = blocked_prefix(n, clock, counts)
            assert minimum == min(path) and endpoint == path[-1]
            counts["extra_prefix_comparisons"] += 1
            cap, positive = finite_cap_data(path, counts)
            if n == 1:
                assert cap == [0, 3, 1][clock % 3]
                counts["finite_cycle_cap_comparisons"] += 1
            if (n == 1 and clock <= 3) or (n in [27, 2 ** 63 - 1] and clock in [32, 128, 256]):
                rows.append({"source": n, "ordinary_clock": clock,
                             "prefix_minimum": minimum, "endpoint": endpoint,
                             "finite_cap_sum": cap, "positive_finite_cap_edges": positive})
    assert finite_cap_data([1, 4], counts)[0] == 3
    return {"sources": starts, "clocks": clocks, "rows": rows,
            "scope": "Exact finite prefixes. A cap of three at source one, clock one, coexists with identically zero global caps."}


def convergence_checks(counts):
    rows = []
    longest = (0, 0)
    for n in range(1, 4097):
        path = [n]
        while path[-1] != 1:
            assert len(path) <= 10000
            x = path[-1]
            path.append(x // 2 if x % 2 == 0 else 3 * x + 1)
            counts["convergence_ordinary_steps"] += 1
        steps = len(path) - 1
        # A separate shortcut traversal reconstructs the exact ordinary path.
        paired = [n]
        while paired[-1] != 1:
            x = paired[-1]
            if x & 1:
                paired.extend([3 * x + 1, (3 * x + 1) // 2])
                counts["convergence_odd_shortcut_pairs"] += 1
            else:
                paired.append(x // 2)
                counts["convergence_even_shortcut_steps"] += 1
        assert paired == path
        assert all(x > 0 for x in path)
        counts["independent_convergence_path_comparisons"] += 1
        counts["verified_convergent_sources"] += 1
        # Arrival at one and positivity prove every suffix's global minimum.
        witnessed = path + [4, 2, 1]
        suffix = 1
        for i in range(len(witnessed) - 2, -1, -1):
            next_min = suffix
            suffix = min(witnessed[i], suffix)
            assert suffix == next_min == 1
            assert next_min - suffix == 0
            counts["witnessed_zero_global_cap_edges"] += 1
        assert witnessed[steps] == witnessed[steps + 3] == 1
        counts["explicit_eventual_cycle_witnesses"] += 1
        if steps > longest[1]:
            longest = (n, steps)
        if n in [1, 2, 3, 7, 27, 97, 4096]:
            rows.append({"source": n, "first_arrival_at_one": steps,
                         "global_minimum": 1, "eventual_cycle_period": 3})
    return {"complete_source_interval": [1, 4096], "fuel_per_source": 10000,
            "longest_first_arrival": {"source": longest[0], "ordinary_steps": longest[1]},
            "rows": rows,
            "scope": "Independent Python convergence witnesses only, not kernel certificates for this interval. The first arrival supplies an attainment witness; it does not evaluate Lean's noncomputable chosen minimumClock."}


def envelope_checks(counts):
    partial = F(0)
    for k in range(257):
        envelope = 2 * F(29, 15) ** (k + 1) + F(k + 1, 2)
        tail = 116 * F(29, 30) ** k + F(k + 2, 2 ** k)
        next_tail = 116 * F(29, 30) ** (k + 1) + F(k + 3, 2 ** (k + 1))
        assert envelope / 2 ** k + next_tail == tail
        assert partial + tail == 118
        assert 0 <= partial <= 118
        partial += envelope / 2 ** k
        counts["consecutive_shell_envelope_checks"] += 1
    for k in [512, 1024, 4096]:
        envelope = 2 * F(29, 15) ** (k + 1) + F(k + 1, 2)
        tail = 116 * F(29, 30) ** k + F(k + 2, 2 ** k)
        next_tail = 116 * F(29, 30) ** (k + 1) + F(k + 3, 2 ** (k + 1))
        assert envelope / 2 ** k + next_tail == tail
        assert 0 <= next_tail <= tail <= 118
        counts["large_index_envelope_checks"] += 1
    return {"consecutive_indices": [0, 256], "extra_indices": [512, 1024, 4096],
            "scope": "Exact rational constants and finite envelope identities only, not source counts at these larger indices."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-minimum-root-spine-") as directory:
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
            if stem == "MinimumRootSpine":
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                text = (ROOT / source).read_text()
                assert set(re.findall(r"^theorem (\w+)", text, re.M)) == set(THEOREMS)
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
    record = json.loads((ROOT / PRIOR).read_text())
    assert record["status"] == "passed"
    for filename, expected in record["sha256"].items():
        assert digest(ROOT / filename) == expected, filename
    authenticated = len(record["sha256"])
    print("Authenticated prior manifest:", authenticated, "hashes", flush=True)
    version, builds = build()
    counts = Counter()
    shells = shell_checks(counts)
    print("Complete finite shell census and independent exact-clock replay passed.", flush=True)
    prefixes = extra_prefix_checks(counts)
    convergents = convergence_checks(counts)
    print("Finite cap identities and explicit convergence witnesses passed.", flush=True)
    envelopes = envelope_checks(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "finite_shells": shells, "extra_prefixes": prefixes,
                              "convergence_witnesses": convergents, "envelopes": envelopes})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-ROOT-SPINE.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": {PRIOR: authenticated},
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Actual global minimum Bellman/parity transport; positive cap support and exact orbit telescoping; successive attained self-minima at strictly increasing ordinary clocks; their monotonicity, conditional spacing/growth/residues, and upper growth; bounded tail minima or cumulative caps iff eventual repetition; zero global caps for convergent sources; finite caps telescope to the terminal value; finite-prefix and actual-global root shell bounds; finite weighted shell budget at most 118.",
        "written_scope": ["Partition and comparison convert the weighted shell bounds into the convergent reciprocal sum over all positive self-minimal integers, at most 119 including one.",
                          "The root count has sublinear power growth with exponent log2(29/15)."],
        "external_dependency": "None. No novelty claim.",
        "finite_scope_limit": "Finite no-descent counts overapproximate global root counts. Global minima equal to one are assigned only after an explicit convergence witness. No uncomputed global root, cap, or residual is assigned a numerical value.",
        "not_proved": ["Bounded actual cap accumulation for every orbit, absence of nontrivial cycles, or exclusion of a nonrepeating orbit.",
                       "A uniform subunit minimum-tail budget or an independently small actual positive residual.",
                       "The full Collatz conjecture or a counterexample."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
