"""Fresh kernel audit and independent finite checks of minimum-root ancestry.

No finite prefix is labelled as an unknown global minimum root. The only
convergence claims added here are the three explicit kernel witnesses.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-root-predecessors"
PRIOR = "results/minimum-root-spine/verification.json"
NEW_SOURCE = "lean/MinimumRootPredecessors.lean"
THEOREMS = ["minimum_cut","all_odd_prefix_transport","all_odd_global_transport","all_odd_root_predecessor","contracting_parent","contracting_parent_smallest","contracting_parent_divisible_three","root_index_mono","contracting_parent_off_spine","least_coalescing_predecessor","contracting_parent_off_orbit","least_root_predecessor","least_successor_alternative","least_ternary_power_excluded","least_saturated_ternary_block","least_saturated_binary_divisibility","least_successor_strict","least_odd_predecessor_bound","odd_ancestor_height_compare","all_odd_height_barrier","finite_branch_witness"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def path(n, clock, stop_at_one=False):
    values = [n]
    for _ in range(clock):
        if stop_at_one and values[-1] == 1:
            break
        x = values[-1]
        values.append(3 * x + 1 if x % 2 else x // 2)
    return values


def paired_path(n, clock):
    values = [n]
    while len(values) <= clock:
        x = values[-1]
        if x % 2:
            values.append(3 * x + 1)
            if len(values) <= clock:
                values.append((3 * x + 1) // 2)
        else:
            values.append(x // 2)
    return values


def odd_block_checks(counts):
    rows = []
    clocks = [0, 1, 2, 4, 8, 16, 32, 64]
    cases = [(k, q) for k in range(33) for q in range(1, 129) if 2 ** k * q > 1]
    large_cases = [(k, q) for k in [64, 128, 256, 512, 1024] for q in [1, 2, 3, 17]]
    for k, q in cases + large_cases:
        a, b = 2 ** k * q - 1, 3 ** k * q - 1
        values = path(a, 2 * k + 64)
        target = path(b, 64)
        paired = paired_path(a, 2 * k)
        assert values[:2 * k + 1] == paired
        assert values[2 * k] == b
        assert values[2 * k:] == target
        assert min(values[:2 * k + 1]) == a
        assert all(values[2 * j] % 2 == 1 for j in range(k))
        counts["all_odd_source_pairs"] += 1
        counts["source_path_ordinary_steps"] += len(values) - 1
        counts["target_path_ordinary_steps"] += 64
        counts["independent_initial_shortcut_pairs"] += k
        counts["all_odd_affine_endpoint_checks"] += 1
        for t in clocks:
            left = min(values[:2 * k + t + 1])
            right_min = min(target[:t + 1])
            assert left == min(a, right_min)
            counts["finite_all_odd_transport_checks"] += 1
            if right_min == b:
                assert left == a
                counts["finite_root_ancestor_implications"] += 1
        if (k, q) in [(1, 2), (4, 2), (16, 17), (32, 128), (1024, 2)]:
            rows.append({"odd_steps": k, "quotient": q, "source_bits": a.bit_length(),
                         "target_bits": b.bit_length(),
                         "prefix_minimum_through_block_equals_source": True,
                         "target_prefix_minimum_64_bits": min(target).bit_length()})
    return {"complete_parameter_range": {"odd_steps": [0, 32], "quotients": [1, 128],
                                        "positive_sources_only": True},
            "extra_odd_steps": [64, 128, 256, 512, 1024],
            "extra_quotients": [1, 2, 3, 17], "suffix_clocks": clocks,
            "rows": rows,
            "scope": "Exact finite-prefix transport and conditional finite no-descent ancestry; not global-root assignments or an interval convergence claim."}


def suffix_records(values):
    records = []
    current = values[-1] + 1
    for i in range(len(values) - 1, -1, -1):
        if values[i] < current:
            records.append((i, values[i]))
            current = values[i]
    return list(reversed(records))


def selected_records(values):
    records = []
    cursor = 0
    while cursor < len(values):
        i = min(range(cursor, len(values)), key=values.__getitem__)
        records.append((i, values[i]))
        cursor = i + 1
    return records


def branch_checks(counts):
    rows = []
    distinct = set()
    clocks = [4, 8, 16, 32, 64, 128]
    for n in range(1, 8193):
        values = path(n, 128, stop_at_one=True)
        assert len(values) == len(set(values))
        assert paired_path(n, len(values) - 1) == values
        counts["branch_source_paths"] += 1
        counts["branch_ordinary_steps"] += len(values) - 1
        counts["independent_branch_path_comparisons"] += 1
        for clock in clocks:
            prefix = values[:clock + 1]
            records = suffix_records(prefix)
            assert records == selected_records(prefix)
            counts["independent_suffix_record_comparisons"] += 1
            for (i, a), (j, b) in zip(records, records[1:]):
                counts["finite_successor_edges"] += 1
                assert a < b and i < j
                if b % 3 != 2:
                    continue
                q = b // 3
                p = 2 * q + 1
                assert 2 * b <= 3 * a + 1
                assert p <= a
                assert (p % 3 == 0) == (b % 9 == 5)
                assert path(p, 2) == [p, 2 * b, b]
                witness = [p, 2 * b] + prefix[j:]
                assert min(witness) == p
                assert min(witness[1:]) == b
                counts["finite_contracting_parent_checks"] += 1
                if p < a:
                    assert p not in prefix
                    assert j - i > 2
                    counts["finite_off_path_parent_checks"] += 1
                    counts["off_path_parent_divisible_by_three" if p % 3 == 0 else "off_path_parent_unit_modulo_three"] += 1
                    distinct.add((a, b, p))
                    if len(rows) < 12:
                        rows.append({"source": n, "terminal_clock": len(prefix) - 1,
                                     "earlier_suffix_minimum": a, "next_suffix_minimum": b,
                                     "new_parent": p, "earlier_clock": i, "next_clock": j})
    counts["distinct_finite_off_path_parent_triples"] = len(distinct)
    return {"complete_source_interval": [1, 8192], "maximum_ordinary_clock": 128,
            "clocks": clocks, "rows": rows,
            "scope": "Simple finite prefixes stopped at one or the stated horizon. Their increasing suffix-record minima are finite-horizon analogues, not unknown global root sequences."}


def arithmetic_checks(counts):
    for k in range(129):
        for q in range(1, 129):
            p = 2 ** k * q - 1
            b = 3 ** k * q - 1
            for a in sorted({max(1, p - 1), max(1, p), p + 1}):
                low = a + 1 <= 2 ** k * q
                high = 2 ** k * (b + 1) <= 3 ** k * (a + 1)
                if low and high:
                    assert a == p
                    assert (a + 1) % 2 ** k == 0
                    counts["saturation_equality_cases"] += 1
                counts["saturation_arithmetic_comparisons"] += 1
            p_next = 2 ** (k + 1) * q - 1
            b_next = 3 ** (k + 1) * q - 1
            for a in [max(1, p_next - 1), p_next, p_next + 1]:
                assert not (a + 1 <= 2 ** (k + 1) * q and
                            2 ** k * (b_next + 1) <= 3 ** k * (a + 1))
                counts["excluded_next_power_arithmetic_comparisons"] += 1
    for d in range(129):
        for j in range(129):
            threshold = 3 ** max(0, d - j)
            for q in sorted({max(1, threshold - 1), threshold, threshold + 1}):
                if 3 ** d <= 3 ** j * q:
                    assert 2 ** d <= 2 ** j * q
                    assert 2 ** d - 1 <= 2 ** j * q - 1
                counts["ancestor_height_barrier_comparisons"] += 1
    return {"indices": [0, 128], "quotients": [1, 128],
            "height_barrier_depths": [0, 128],
            "height_barrier_quotients": "The exact threshold and its positive neighbours",
            "scope": "Exact integer compatibility checks for the two inequalities used by the kernel proof. No numerical least counterexample is assumed or exhibited."}


def witness_checks(counts):
    values = path(27, 111)
    assert values[26] == 155 and values[44] == 167
    assert min(values[26:65]) == 155
    assert min(values[27:65]) == 167
    assert 111 not in values[:65]
    assert path(111, 2) == [111, 334, 167]
    assert (26, 155) in suffix_records(values[:65])
    assert (44, 167) in suffix_records(values[:65])
    witnesses = []
    for n, clock in [(155, 85), (167, 67), (111, 69)]:
        direct = path(n, clock)
        paired = paired_path(n, clock)
        assert direct == paired and direct[-1] == 1 and 1 not in direct[:-1]
        counts["kernel_convergence_witnesses_replayed"] += 1
        counts["kernel_witness_ordinary_steps"] += clock
        witnesses.append({"source": n, "first_arrival_at_one": clock})
    return {"finite_source": 27, "terminal_clock": 64, "first_suffix_minimum": 155,
            "next_suffix_minimum": 167, "parent_absent_from_prefix": 111,
            "parent_path": [111, 334, 167], "convergence_witnesses": witnesses,
            "scope": "The kernel proves the finite prefix data, absence of 111 through clock64, and all three arrivals at one. Python additionally checks first-arrival minimality."}


def build(sources):
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-root-predecessors-") as directory:
        for source in sources:
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
            if source == NEW_SOURCE:
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                assert set(re.findall(r"^theorem (\w+)", (ROOT / source).read_text(), re.M)) == set(THEOREMS)
                assert "'MinimumRootPredecessors.finite_branch_witness' does not depend on any axioms" in result.stdout
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
    sources = [b["source"] for b in record["builds"]] + [NEW_SOURCE]
    assert len(sources) == 23 and sources[-2] == "lean/MinimumRootSpine.lean"
    authenticated = len(record["sha256"])
    print("Authenticated prior manifest:", authenticated, "hashes", flush=True)
    version, builds = build(sources)
    counts = Counter()
    odd = odd_block_checks(counts)
    print("All-odd finite transport and ancestry checks passed.", flush=True)
    branches = branch_checks(counts)
    print("Complete finite branch census and independent record selection passed.", flush=True)
    arithmetic = arithmetic_checks(counts)
    witness = witness_checks(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "all_odd_transport": odd, "finite_branches": branches,
                              "power_arithmetic": arithmetic, "kernel_example": witness})
    files = sources + [Path(__file__).name, "docs/MINIMUM-ROOT-PREDECESSORS.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS),
        "prior_hashes_validated": {PRIOR: authenticated}, "finite_replay_counts": dict(counts),
        "kernel_scope": "Global prefix/suffix minimum splitting; all-odd finite and global transport; inverse preservation of minimum roots; the smallest contracting parent, its divisibility by three, and its exclusion from a nonrepeating orbit when it lies below the preceding root; minimality throughout the least-counterexample component; first-successor alternative; exclusion of ternary power k+1 at root index k; depth-k saturation forces a source all-odd block and binary divisibility; an explicit target-height barrier beyond which all-odd ancestors cannot lie below the original source; an axiom-free finite branch example whose three values reach one.",
        "written_scope": ["Interpretation of the divisibility restriction as a ternary valuation bound.",
                          "Assessment of why the new root counts do not close the previous branch-density or cylinder-energy estimates."],
        "external_dependency": "None for the new kernel proofs. The Wirsching preprint and the existing external energy development are reviewed for research direction only; no missing estimate is imported as a premise.",
        "finite_scope_limit": "All parameter sweeps and suffix-record censuses use finite horizons. The least-counterexample statements retain that hypothesis in Lean and have no numerical instantiation. Only the three explicit convergent witnesses are global trajectory claims.",
        "not_proved": ["A contradiction from the necessary ternary restrictions, a useful relative branch-density lower bound, or sublinear masked cylinder energy.",
                       "A universal actual cap budget, absence of nontrivial cycles or divergence, or the full Collatz conjecture."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
