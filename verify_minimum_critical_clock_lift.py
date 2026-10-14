"""Audit a second growing block at a sequence of positive Mersenne sources.

Universal integer statements are kernel proofs. Modular tests at very large
indices do not enumerate or even construct the corresponding huge sources.
Selected ordinary orbit replays and convergence checks are reported separately.
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
OUT = ROOT / "results/minimum-critical-clock-lift"
PRIOR = "results/minimum-clock-barrier/verification.json"
SOURCES = ["CollatzContradiction.lean", "CollatzAffine.lean", "lean/ClockedMinimum.lean",
           "lean/DensityCountermodel.lean", "lean/MinimumTailRigidity.lean",
           "lean/MinimumCapTransport.lean", "lean/CensoredProgressionTransport.lean",
           "lean/CutoffDescent.lean", "lean/MinimumLinearBoundary.lean",
           "lean/MinimumGreenKernel.lean", "lean/MinimumClockBarrier.lean",
           "lean/MinimumCriticalClockLift.lean"]
THEOREMS = [
    "scaled_endpoint_buffer", "nine_power_top_bit", "lift_exponent_spec",
    "block_length_bounds", "block_length_log2", "second_block_congruence",
    "three_halves", "three_halves_safe", "odd_endpoint_scale", "two_growing_blocks",
    "two_block_clock", "source_growth", "family_no_descent", "family_tail_diagonal",
    "strict_budget_requires_clock", "critical_clock_at_source", "shifted_critical_power",
    "shifted_critical_no_descent", "critical_budget_failure", "closed_block_lengths",
    "closed_sources_converge"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def modular_checks(counts):
    """Use modular exponentiation, independently of Lean's full-power quotient."""
    exponents = {}
    selected = []
    a = 0
    for j in range(1025):
        modulus = 1 << (j + 3)
        assert 0 <= a < 1 << j
        assert (pow(9, a, modulus) + 7) % modulus == 0
        counts["lift_residue_checks"] += 1
        assert pow(9, 1 << j, 2 * modulus) == 1 + modulus
        counts["power_nine_top_bit_checks"] += 1
        k = 2 * (a + (1 << j))
        assert 1 << (j + 1) <= k < 1 << (j + 2)
        assert k.bit_length() - 1 == j + 1
        counts["block_length_bound_checks"] += 1
        assert (pow(3, k, modulus) + 7) % modulus == 0
        counts["second_block_modular_checks"] += 1
        exponents[j] = (a, k)
        if j <= 16 or j in [32, 64, 128, 256, 512, 1024]:
            row = {"index": j, "exponent_k_bits": k.bit_length(),
                   "modulus_power_of_two": j + 3,
                   "source_bit_length_is_k": True,
                   "source_constructed_for_this_modular_check": False}
            if j <= 16:
                row.update({"lift_exponent": a, "block_length_k": k})
            else:
                row["block_length_k_hex_sha256"] = hashlib.sha256(hex(k).encode()).hexdigest()
            selected.append(row)
        if j <= 12:
            # Enumerate the entire small residue range, rather than repeat the lift.
            value = 1
            hits = []
            for candidate in range(1 << j):
                if (value + 7) % modulus == 0:
                    hits.append(candidate)
                value = value * 9 % modulus
                counts["small_exponent_residues_enumerated"] += 1
            assert hits == [a]
            counts["small_exponent_full_range_comparisons"] += 1
        top_bit = (pow(9, a, 2 * modulus) + 7) % (2 * modulus)
        assert top_bit in [0, modulus]
        if top_bit:
            a += 1 << j
    return exponents, {"indices": [0, 1024], "selected_rows": selected,
                       "scope": "Modular arithmetic only at the large indices; no double-exponential source or population is enumerated. Small uniqueness tests cover only the listed finite exponent ranges."}


def prefix_checks(exponents, counts):
    rows = []
    for j in range(2, 15):
        a, k = exponents[j]
        source = (1 << k) - 1
        q, remainder = divmod(3 ** k + 7, 1 << (j + 3))
        assert q > 0 and remainder == 0
        bridge = (1 << j) * q - 1
        endpoint = 3 ** j * q - 1
        block_clock = 2 * k + 3 + 2 * j
        clock = (6 ** (k + j)).bit_length() - 1
        old_clock = (6 ** k).bit_length() - 1
        assert block_clock <= clock
        assert 3 ** k - 1 == 8 * bridge
        assert source <= bridge
        assert 3 ** (k + j) * source <= (1 << (k + j + 3)) * endpoint
        assert 1 << clock <= 6 ** (k + j) < 1 << (clock + 1)
        assert (source + 1).bit_length() - 1 == k
        counts["exact_two_block_arithmetic_cases"] += 1
        first_indices = {0, k // 4, k // 2, 3 * k // 4, k}
        checkpoints = {2 * i: (1 << (k - i)) * 3 ** i - 1 for i in first_indices}
        checkpoints.update({2 * k + r: (3 ** k - 1) // (1 << r) for r in [1, 2, 3]})
        checkpoints.update({2 * k + 3 + 2 * i: (1 << (j - i)) * 3 ** i * q - 1
                            for i in range(j + 1)})
        value = minimum = source
        for t in range(clock + 1):
            assert minimum == source
            counts["selected_prefix_time_checks"] += 1
            if t in checkpoints:
                assert value == checkpoints[t]
                counts["exact_block_endpoint_comparisons"] += 1
            if t == clock:
                break
            value = value // 2 if value % 2 == 0 else 3 * value + 1
            minimum = min(minimum, value)
            counts["selected_prefix_ordinary_steps"] += 1
        assert value >= source
        counts["selected_prefix_sources"] += 1
        for shift in range(j + 1):
            shifted_clock = old_clock + shift
            assert shifted_clock <= clock
            assert (1 << shifted_clock) <= 6 ** (k + j)
            counts["critical_shift_power_checks"] += 1
        rows.append({"index": j, "lift_exponent": a, "source_bits": k,
                     "forced_two_block_ordinary_clock": block_clock,
                     "old_guaranteed_clock": old_clock,
                     "new_guaranteed_clock": clock, "clock_gain": clock - old_clock,
                     "source_hex_sha256": hashlib.sha256(hex(source).encode()).hexdigest(),
                     "guaranteed_tail_mean_at_own_cutoff": 1,
                     "permitted_floor": "any H < 2^" + str(k) + "-1"})
    return {"indices": [2, 14], "rows": rows,
            "scope": "These 13 individual positive sources are actually iterated through every ordinary step of the claimed finite clock. The diagonal population consequence uses the kernel sum theorem; the intervals up to these sources are not enumerated."}


def convergence_checks(exponents, counts):
    rows = []
    for j in range(2, 11):
        _, k = exponents[j]
        source = (1 << k) - 1
        value = source
        first_descent = first_one = None
        peak_bits = source.bit_length()
        for t in range(1, 300001):
            value = 3 * value + 1 if value & 1 else value >> 1
            peak_bits = max(peak_bits, value.bit_length())
            if value < source and first_descent is None:
                first_descent = t
            counts["selected_convergence_ordinary_steps"] += 1
            if value == 1:
                first_one = t
                break
        assert first_one is not None
        assert (6 ** (k + j)).bit_length() - 1 < first_descent < first_one
        if j in [2, 3]:
            assert first_one == {2: 159, 3: 449}[j]
            counts["kernel_witness_replay_steps"] += first_one
        counts["selected_convergent_sources"] += 1
        rows.append({"index": j, "source_bits": k, "first_descent": first_descent,
                     "first_one": first_one, "peak_bits": peak_bits,
                     "hitting_one_also_kernel_checked": j in [2, 3]})
    return {"rows": rows, "scope": "Selected finite convergence checks only. Two hitting statements are separately kernel checked by reduction; their first-arrival and first-descent minimality are Python checks. No convergence theorem for the infinite family is claimed."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-critical-clock-lift-") as directory:
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
            if stem == "MinimumCriticalClockLift":
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                axiom_map = dict(roots)
                assert axiom_map[stem + ".closed_block_lengths"] == ""
                assert axiom_map[stem + ".closed_sources_converge"] == ""
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
    exponents, modular = modular_checks(counts)
    print("Modular lifts through index 1024 passed.", flush=True)
    prefixes = prefix_checks(exponents, counts)
    print("Selected ordinary prefix replays passed.", flush=True)
    convergence = convergence_checks(exponents, counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "modular_arithmetic": modular, "actual_prefixes": prefixes,
                              "selected_convergence": convergence})
    files = SOURCES + [Path(__file__).name, "docs/MINIMUM-CRITICAL-CLOCK-LIFT.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": len(prior["sha256"]),
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Constructive one-bit lift for powers of nine; block lengths between 2^(j+1) and 2^(j+2); two exact ordinary growing blocks separated by three safe halvings; finite no-descent through 2^T<=6^(K_j+j); diagonal tail-sum lower bound; necessary clock inequality; failure at arbitrarily large cutoffs for every fixed floor and additive shift of the specified integer critical clock; two explicit sources reach one.",
        "written_scope": [
            "With gamma=log2(6), the strict budget forces T(N_j)>gamma log2 N_j + gamma log2 log2 N_j - 2 gamma at these cutoffs.",
            "For every fixed real c<gamma and fixed integer L>=0, clocks floor(gamma log2 N+c log2 log2 N)+L fail the strict budget at infinitely many large family cutoffs.",
            "The case c=0 excludes every fixed additive shift at the leading coefficient gamma. Real-logarithm comparison and the asymptotic assembly are written, not additional Lean statements."],
        "external_dependency": "None for the new argument; no claim of mathematical novelty.",
        "finite_scope_limit": "Large-index modular tests never construct their enormous sources. Actual orbit replays cover 13 selected sources, not a continuous interval. Nine selected sources reach one in Python; two hitting statements also have axiom-free kernel proofs. No future behavior of a surviving finite prefix is inferred.",
        "not_proved": ["Unbounded critical-clock tail means, as opposed to a diagonal lower bound of one.",
                       "Failure of every leading logarithmic coefficient above gamma, or of the full gamma log-log correction with every additive constant.",
                       "A bound for actual global minima or residuals, convergence of the infinite constructed family, a counterexample, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "counts": dict(counts),
                      "largest_replayed_source_bits": prefixes["rows"][-1]["source_bits"]}, indent=2))


if __name__ == "__main__":
    main()
