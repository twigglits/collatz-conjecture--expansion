"""Exact audit of finite marked first-passage preimage counting.

The source is generated forward and independently recovered from affine
word equations. Analytic Fourier decay and asymptotic error rates are
not certified by this finite computation.
"""
from collections import Counter, defaultdict
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
OUT = ROOT / "results/marked-preimage-audit"
SOURCES = ["CollatzContradiction.lean", "lean/ClockedMinimum.lean",
           "lean/MarkedPreimageAudit.lean"]
THEOREMS = ["affine_iff_chain", "odd_power_unique", "chain_unique",
            "affine_inverse_unique", "halve_power", "chain_clock",
            "first_odd_splice", "marked_chain_splice",
            "interval_mismatch_localization", "backward_envelope_gate",
            "ungated_preimage_witness"]
PRIORS = ["results/cutoff-descent/verification.json",
          "results/clocked-progression-mixing/verification.json"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2) + "\n")


def ratio(value):
    return [value.numerator, value.denominator]


def syracuse(n):
    assert n > 0 and n & 1
    q, a = 3 * n + 1, 0
    while q % 2 == 0:
        q //= 2
        a += 1
    return q, a


def trace(n, length):
    states, word, clocks = [n], [], [0]
    for _ in range(length):
        n, a = syracuse(n)
        states.append(n)
        word.append(a)
        clocks.append(clocks[-1] + a + 1)
    return states, tuple(word), clocks


def ordinary(n):
    return 3 * n + 1 if n & 1 else n // 2


def affine(word):
    """Forward composition, independent of the Lean cons recurrence."""
    s, b, p = 0, 0, 1
    for a in word:
        b = 3 * b + (1 << s)
        s += a
        p *= 3
    return p, s, b


def good_words(length, tolerance):
    """All positive words with |S_j-2j|<=tolerance, with no extra cutoff."""
    def extend(word, total):
        if len(word) == length:
            yield word
            return
        j = len(word) + 1
        for a in range(max(1, 2 * j - tolerance - total), 2 * j + tolerance - total + 1):
            yield from extend(word + (a,), total + a)
    return list(extend((), 0))


def is_good(word, tolerance):
    total = 0
    for j, a in enumerate(word, 1):
        total += a
        if abs(total - 2 * j) > tolerance:
            return False
    return True


def l1(left, right):
    return sum(abs(left[key] - right[key]) for key in left.keys() | right.keys())


def population(h, tolerance, tail_length, counts, source_floor=None):
    max_length = 4
    low = (2 * 4 ** tolerance) * h
    high, y = 2 * low, F(2 * low if source_floor is None else source_floor)
    assert low > 4 ** tolerance * h + 3 ** max_length
    classes = ["all", "0", "1", "2"]
    source_counts = Counter()
    forward = {r: Counter() for r in classes}
    start = -(-y.numerator // y.denominator)
    start += (start % 2 == 0)
    end = -(-(2 * y).numerator // (2 * y).denominator)
    for source in range(start, end, 2):
        source_counts["all"] += 1
        source_counts[str(source % 3)] += 1
        states, word, clocks = trace(source, max_length + tail_length)
        counts["forward_source_prefixes"] += 1
        counts["forward_syracuse_steps"] += max_length + tail_length
        hits = [j for j, value in enumerate(states) if value <= h]
        if not hits:
            continue
        first = hits[0]
        k = first - tail_length
        if not (1 <= k <= max_length and is_good(word[:k], tolerance)
                and low <= states[k] < high):
            continue
        mark = states[first], clocks[first]
        for r in ["all", str(source % 3)]:
            forward[r][mark] += 1
        counts["selected_forward_sources"] += 1

    endpoints = {}
    for m in range(low + 1, high, 2):
        states, word, clocks = trace(m, tail_length)
        counts["tail_source_prefixes"] += 1
        if all(v > h for v in states[:-1]) and states[-1] <= h:
            endpoints[m] = states[-1], sum(word), clocks[-1]
    assert endpoints
    old = {r: Counter() for r in classes}
    unshifted = {r: Counter() for r in classes}
    changes = {k: {r: set() for r in classes} for k in range(1, max_length + 1)}
    laws = defaultdict(Counter)
    seen = {}
    word_sizes = {}
    word_lists = {k: good_words(k, tolerance) for k in range(1, max_length + 1)}
    offsets = [F(b, 1 << s) for words in word_lists.values()
               for word in words for _, s, b in [affine(word)]]
    eta = max(offsets) / low
    coarse_eta = F(3 ** max_length, low)
    assert 0 < eta <= coarse_eta < 1
    for k in range(1, max_length + 1):
        words = word_lists[k]
        word_sizes[str(k)] = len(words)
        for word in words:
            assert is_good(word, tolerance)
            p, s, b = affine(word)
            assert F(b, 1 << s) < p
            inv_low, inv_high = pow(2, -s, p), pow(2, -s, 3 * p)
            residues = {"all": b * inv_low % p}
            residues.update({str(r): (b + p * r) * inv_high % (3 * p) for r in range(3)})
            for r, residue in residues.items():
                laws[k, s, r][residue] += 1
            for m, (landing, tail_sum, tail_clock) in endpoints.items():
                number = (1 << s) * m - b
                assert number > 0
                integral = number % p == 0
                assert integral == (m % p == residues["all"])
                counts["inverse_integrality_tests"] += 1
                for r in range(3):
                    assert (number % (3 * p) == p * r) == (m % (3 * p) == residues[str(r)])
                    counts["inverse_source_residue_tests"] += 1
                if not integral:
                    continue
                source = number // p
                assert source % 2 == 1
                assert (k, source) not in seen
                seen[k, source] = (word, m)
                states, actual_word, clocks = trace(source, k)
                assert actual_word == word and states[-1] == m
                assert clocks[-1] == k + s
                assert all(v > h for v in states)
                assert m > 4 ** tolerance * h + p
                for j, state in enumerate(states):
                    suffix_p, suffix_s, suffix_b = affine(word[j:])
                    assert F(suffix_p, 1 << suffix_s) <= 4 ** tolerance
                    assert F(suffix_b, 1 << suffix_s) < p
                    assert F(suffix_p * state + suffix_b, 1 << suffix_s) == m
                    assert m <= 4 ** tolerance * state + p
                    counts["exact_suffix_envelope_checks"] += 1
                # Independently walk the ordinary map to check the full mark.
                mark = landing, k + s + tail_clock
                value, first_clock, first_landing = source, None, None
                for t in range(mark[1] + 1):
                    if first_clock is None and value % 2 and value <= h:
                        first_clock, first_landing = t, value
                    if t < mark[1]:
                        value = ordinary(value)
                        counts["ordinary_mark_replay_steps"] += 1
                assert (first_landing, first_clock) == mark
                assert mark[1] == (k + tail_length) + s + tail_sum
                counts["inverse_word_and_mark_checks"] += 1

                actual_in = y <= source < 2 * y
                shifted_in = y * p <= (1 << s) * m < 2 * y * p
                u = F((1 << s) * m, p)
                assert (1 - eta) * u <= source <= u
                for r in ["all", str(source % 3)]:
                    if actual_in:
                        old[r][mark] += 1
                    if shifted_in:
                        unshifted[r][mark] += 1
                    if actual_in != shifted_in:
                        assert ((1 - eta) * y <= source < y
                                or 2 * (1 - eta) * y <= source < 2 * y)
                        changes[k][r].add(source)
                if actual_in != shifted_in:
                    counts["actual_interval_membership_changes"] += 1

    assert old == forward
    counts["complete_forward_inverse_marked_law_agreements"] += len(classes)
    grouped = {r: Counter() for r in classes}
    for (k, s, r), histogram in laws.items():
        q = 3 ** k * (1 if r == "all" else 3)
        coefficient = F(1 << s, source_counts[r])
        for m, (landing, tail_sum, _) in endpoints.items():
            if not y * 3 ** k <= (1 << s) * m < 2 * y * 3 ** k:
                continue
            mark = landing, k + tail_length + s + tail_sum
            geometric_mass = F(histogram[m % q], 1 << s)
            grouped[r][mark] += coefficient * geometric_mass
            counts["fixed_sum_residue_reassembly_terms"] += 1
    rows = []
    for r in classes:
        target = Counter({mark: F(weight, source_counts[r]) for mark, weight in unshifted[r].items()})
        assert +grouped[r] == target
        counts["complete_grouped_marked_law_agreements"] += 1
        boundary_sources = {n for n in range(1, end, 2)
                            if (r == "all" or n % 3 == int(r))
                            and ((1 - eta) * y <= n < y or 2 * (1 - eta) * y <= n < 2 * y)}
        lattice = 2 if r == "all" else 6
        assert len(boundary_sources) <= 3 * eta * y / lattice + 2
        changed = 0
        for k in changes:
            assert changes[k][r] <= boundary_sources
            changed += len(changes[k][r])
            counts["boundary_source_injection_checks"] += 1
        discrepancy = l1(old[r], unshifted[r])
        assert discrepancy <= changed <= max_length * len(boundary_sources)
        rows.append({"source_class": r, "normalizing_sources": source_counts[r],
                     "selected_sources": sum(old[r].values()),
                     "unshifted_pair_count": sum(unshifted[r].values()),
                     "complete_marked_L1_error": ratio(F(discrepancy, source_counts[r])),
                     "changed_pairs": changed, "single_length_boundary_sources": len(boundary_sources),
                     "source_layer_bound": ratio(F(max_length * len(boundary_sources), source_counts[r]))})
    return {"floor": h, "prefix_tolerance": tolerance, "tail_syracuse_length": tail_length,
            "prefix_lengths": [1, max_length], "source_interval": [ratio(y), ratio(2 * y)],
            "intermediate_interval": [low, high], "eligible_tail_endpoints": len(endpoints),
            "complete_good_word_counts": word_sizes, "relative_offset_bound": ratio(eta),
            "coarse_relative_offset_bound": ratio(coarse_eta),
            "classes": rows}


def witness():
    states, word, clocks = trace(19, 4)
    assert states == [19, 29, 11, 17, 13]
    assert word[:3] == (1, 3, 1) and is_good(word[:3], 1)
    assert clocks[2] == 6 and clocks[3] == 8 and clocks[4] == 11
    p, s, b = affine(word[:3])
    assert (1 << s) * 17 == p * 19 + b
    return {"floor": 16, "odd_states": states, "valuation_word": list(word),
            "ordinary_clocks": clocks, "actual_first_clock": 6,
            "ungated_splice_clock": 11,
            "scope": "Refutes omitting the prefix first-passage condition, not the existing height-buffered argument."}


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-marked-preimage-") as directory:
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
    version, builds = build()
    counts, rows = Counter(), []
    for h in [32, 64, 128]:
        for tolerance in [1, 2]:
            for tail_length in [1, 2]:
                rows.append(population(h, tolerance, tail_length, counts))
                print("Exact marked population passed:", h, tolerance, tail_length, flush=True)
    # The inverse pair w=(3), M=341 has source 909 and unshifted source
    # 909+1/3. This band deliberately straddles its lower endpoint.
    rows.append(population(32, 1, 1, counts, F(5455, 6)))
    print("Exact fractional-endpoint boundary population passed.", flush=True)
    assert counts["actual_interval_membership_changes"] > 0
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "ungated_witness": witness(), "finite_populations": rows})
    files = SOURCES + [Path(__file__).name, "docs/MARKED-PREIMAGE-AUDIT.md",
                      "docs/CLOCKED-PROGRESSION-MIXING.md", "docs/MINIMUM-LOG-MOMENTS.md",
                      "docs/NATURAL-DENSITY-ALMOST-BOUNDED.md"] + PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    save(OUT / "verification.json", {
        "status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
        "collatz_status": "unresolved", "lean_version": version, "builds": builds,
        "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": prior_counts,
        "finite_replay_counts": dict(counts),
        "kernel_scope": "Positive-word affine equations iff actual odd-integer chains; unique inversion; exact ordinary clocks and first-odd-passage splice; interval boundary localization and rational envelope gate; a closed counterexample to deleting the prefix passage condition.",
        "written_audit_scope": [
            "The ordinary-clock mark is a bounded function of length, total valuation and intermediate endpoint in the preimage formula.",
            "The existing asymptotic intermediate-height window ensures no earlier crossing; a finite explicit envelope explains why.",
            "Uniform-source interval replacement counts boundary sources injectively at each word length, avoiding a factor equal to the number of words.",
            "Fixed-total residue grouping and source-class normalization preserve arbitrary bounded marked tests."],
        "external_source_review": {"url": "https://arxiv.org/html/1909.03562v7",
                                   "checked_date": "2026-10-14", "sections": ["2", "5", "6", "7"],
                                   "scope": "Published inversion and event-equivalence arguments, collision factorization and paired product structure. The uniform-source marked extension remains a local written deduction."},
        "audit_conclusion": "No contradiction found in the retained-clock bridge. The prefix passage condition is necessary and is supplied by the existing height window. This is not a complete formalization or independent peer review of analytic mixing.",
        "finite_scope_limit": "Exact finite marked distributions on selected good sources and inverse pairs. Every word satisfying the finite prefix condition is enumerated, without unreported truncation. Small integer parameters do not test the unspecified asymptotic regime. No floating-point proof decisions.",
        "not_proved": ["Uniform tilted Fourier decay or joint/fixed-endpoint mixing in Lean.",
                       "Effective large-scale good-event or mixing constants.",
                       "The all-source zero limit, exclusion of divergent or additional periodic orbits, or full Collatz."],
        "sha256": {p: digest(ROOT / p) for p in files}})
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
