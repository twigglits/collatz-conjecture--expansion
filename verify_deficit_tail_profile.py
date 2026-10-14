"""Exact finite checks for the WRITTEN c_0 tail-profile argument.

Finite replay does not prove the analytic coupling inputs, sequence-space
convergence, an integrable tail, or universal Collatz convergence.
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

from verify_deficit_limit_law import independent_path
from verify_prearrival_deficit_transfer import Deficits, prearrival, ratio

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/deficit-tail-profile"
SOURCES = ["lean/DeficitLimitLaw.lean", "lean/DeficitClockMoment.lean",
           "lean/DeficitTailProfile.lean"]
THEOREMS = ["age_tail_is_shorter_clock", "age_tail_is_prefix",
            "cutoff_in_tail", "cutoff_in_front", "simultaneous_common_tail",
            "scalar_tail_below_clock_tail", "tail_uniform_integrability_split",
            "sparse_support_split"]
PRIOR = ["results/deficit-clock-moment/verification.json",
         "results/deficit-limit-law/verification.json",
         "results/prearrival-deficit-transfer/verification.json",
         "results/signed-arrival-windows/verification.json"]
PRECISION = 1 << 96
CUTOFFS = (0, 1, 4, 16, 32, 64, 128, 256)
LIMIT = 4096


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def add_enclosure(pair, value):
    lo, rem = divmod(value.numerator * PRECISION, value.denominator)
    pair[0] += lo
    pair[1] += lo + bool(rem)


def interval(pair, count):
    return {"lower": ratio(F(pair[0], count * PRECISION)),
            "upper": ratio(F(pair[1], count * PRECISION))}


def overlaps(a, b):
    return F(*a["lower"]) <= F(*b["upper"]) and F(*b["lower"]) <= F(*a["upper"])


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-tail-profile-") as directory:
        for source in SOURCES:
            obj = Path(directory) / (Path(source).stem + ".olean")
            log = OUT / (Path(source).stem + ".log")
            command = ["lean", "-o", str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("warning:", "error:", "sorryAx", "ofReduceBool"))
            if source == SOURCES[-1]:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   result.stdout, re.M)
                assert {name for name, _ in roots} == {"DeficitTailProfile." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                for _, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
            builds.append({"source": source, "source_sha256": digest(ROOT / source),
                           "command": command, "returncode": 0, "fresh_build": True,
                           "native_computation_used": False, "elapsed_seconds": round(time.monotonic() - start, 3),
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def tail(path, cutoff):
    return path["profile"][cutoff] if cutoff < len(path["profile"]) else F()


def profiles(counts):
    memo = Deficits(counts)
    paths = {}
    bands = [{l: [0, 0] for l in CUTOFFS} for _ in range(12)]
    prefix = {l: [[0, 0]] for l in CUTOFFS}
    for n in range(1, LIMIT):
        path = independent_path(n, counts)
        T, D = path["T"], path["D"]
        assert memo.get(n) == (T, D)
        accumulated = [F()]
        for weight in path["weights"][:-1]:
            accumulated.append(accumulated[-1] + 1 - weight)
        assert accumulated[-1] == D
        # Sum losses from the odd-state formula, independently of prefix sums.
        masses = [F() for _ in range(T + 2)]
        for j, v in enumerate(path["values"][:-1]):
            loss = path["weights"][j] / (3 * v + 1) if v & 1 else F()
            assert loss == path["weights"][j] - path["weights"][j + 1]
            masses[T - j - 1] += loss
            counts["independent_loss_terms"] += 1
        remaining = sum(masses[1:], F())
        age_tail = sum((age * mass for age, mass in enumerate(masses)), F())
        profile = []
        for l in range(T + 2):
            q = accumulated[max(T - l, 0)]
            assert q == age_tail
            assert 0 <= q <= D and 0 <= D - q <= l
            if profile:
                assert q <= profile[-1]
            profile.append(q)
            age_tail -= remaining
            if l + 1 < len(masses):
                remaining -= masses[l + 1]
            assert age_tail >= 0 and remaining >= 0
            counts["exact_all_cutoff_loss_age_identities"] += 1
            counts["exact_profile_shape_and_cap_checks"] += 1
        assert age_tail == remaining == 0
        path["prefix_deficit"] = accumulated
        path["profile"] = profile
        paths[n] = path
        for l in CUTOFFS:
            q = tail(path, l)
            assert max(D - l, 0) <= q
            counts["exact_scalar_excess_tail_bounds"] += 1
            for k in (F(1), F(2), F(4)):
                for epsilon in (F(1, 16), F(1, 2)):
                    assert q <= epsilon + k * (q > epsilon) + max(D - k, 0)
                    counts["exact_uniform_integrability_splits"] += 1
            add_enclosure(bands[n.bit_length() - 1][l], q)
            pair = prefix[l][-1].copy()
            add_enclosure(pair, q)
            prefix[l].append(pair)
        if n in (1023, 2047, 4095):
            print("All exact tail cutoffs through source", n, "passed.", flush=True)

    for n in range(1, LIMIT // 2):
        assert paths[2 * n]["T"] == paths[n]["T"] + 1
        for l in range(paths[2 * n]["T"] + 2):
            assert tail(paths[n], l) == tail(paths[2 * n], l)
        counts["exact_whole_profile_halving_invariances"] += 1

    prior = json.loads((ROOT / "results/deficit-clock-moment/replay.json").read_text())["bands"]
    rows = []
    for k, row in enumerate(bands):
        M = 1 << k
        current = {str(l): interval(pair, M) for l, pair in row.items()}
        assert current["0"] == prior[k]["mean_deficit"]
        for l, old in prior[k]["remaining_clock_tail_moments"].items():
            assert overlaps(current[l], old)
            counts["authenticated_prior_clock_tail_comparisons"] += 1
        rows.append({"level": k, "source_interval": [M, 2 * M],
                     "mean_tail_profiles": current,
                     "probabilities_tail_exceeds_one_sixteenth":
                     {str(l): ratio(F(sum(tail(paths[n], l) > F(1, 16) for n in range(M, 2 * M)), M))
                      for l in CUTOFFS}})
    return paths, prefix, rows


def passages(paths, counts):
    rows = []
    for floor in (1, 3, 7, 31, 127, 511):
        groups = defaultdict(list)
        marks = {}
        for n, path in paths.items():
            i = next(j for j, x in enumerate(path["values"]) if x & 1 and x <= floor)
            b, p = path["values"][i], path["weights"][i]
            base = paths[b]
            t, e, A = base["T"], 1 - p, path["prefix_deficit"][i]
            assert path["T"] == i + t
            assert all(x > b for x in path["values"][:i])
            assert all(x > floor for x in path["values"][:i] if x & 1)
            assert all(1 - e <= w <= 1 for w in path["weights"][:i + 1])
            for l in range(path["T"] + 2):
                q, qb = tail(path, l), tail(base, l)
                if l <= t:
                    assert q == A + p * qb + (1 - p) * (t - l)
                    counts["exact_cutoffs_after_landing"] += 1
                else:
                    assert qb == 0
                    assert q == path["prefix_deficit"][max(i + t - l, 0)]
                    assert q <= e * i
                    counts["exact_cutoffs_before_landing"] += 1
                assert 0 <= q - qb <= e * (i + t)
            counts["exact_whole_profile_landing_bounds"] += 1
            groups[b].append(n)
            marks[n] = (i, b, p)
        for b, sources in groups.items():
            # Use a long prefix as reference, rather than always the landing b.
            m = max(sources, key=lambda n: (marks[n][0], n))
            q = marks[m][2]
            for n in sources:
                p = marks[n][2]
                e = max(1 - p, 1 - q)
                clock = max(paths[n]["T"], paths[m]["T"])
                norm = max(abs(tail(paths[n], l) - tail(paths[m], l)) for l in range(clock + 2))
                assert norm <= e * clock
                counts["exact_whole_profile_common_landing_comparisons"] += 1
                if p < 1 and q < 1:
                    counts["common_landings_with_loss_on_both_prefixes"] += 1
        rows.append({"floor": floor, "sources": len(paths), "landing_groups": len(groups)})
        print("Simultaneous common-landing profile checks passed at floor", floor, flush=True)
    return rows


def sparse_prearrival(paths, prefix, counts):
    old = json.loads((ROOT / "results/signed-arrival-windows/replay.json").read_text())["finite_signed_bands"]["rows"]
    rows = []
    factor = F(23, 3)
    for k in range(10):
        M, nonfused = 1 << k, 0
        hsum, qsum = [0, 0], {l: [0, 0] for l in CUTOFFS}
        for n in range(M, 2 * M):
            q = 3 * n + 2
            parent, child = paths[n], paths[q]
            assert min(parent["T"], child["T"]) >= k
            a = sum(v & 1 for v in parent["values"][:k])
            b = 1 + sum(v & 1 for v in child["values"][:k])
            event = parent["values"][k] != child["values"][k] or a != b
            nonfused += event
            H = prearrival(n, counts)["H"]
            if not event:
                assert H == 0
                counts["exact_zero_prearrival_cost_off_nonfusion"] += 1
            assert H <= factor * child["D"] + 1
            for l in CUTOFFS:
                tail_value = tail(child, l)
                assert H <= event * (factor * l + 1 + factor * tail_value)
                add_enclosure(qsum[l], tail_value)
                counts["exact_sparse_prearrival_tail_bounds"] += 1
            add_enclosure(hsum, H)
            counts["exact_prearrival_support_checks"] += 1
        assert nonfused == old[k]["nonfused_at_prefix"]
        hmean, eta = interval(hsum, M), F(nonfused, M)
        prior = old[k]["unhalved_mean_costs"]["before_both_arrivals"]
        assert overlaps(hmean, prior)
        bounds = {}
        for l in CUTOFFS:
            # All q are distinct and below 6M. Include the unused sources too.
            assert qsum[l][0] <= prefix[l][6 * M][0]
            band_bound = (factor * l + 1) * eta + factor * F(qsum[l][1], M * PRECISION)
            prefix_bound = (factor * l + 1) * eta + 46 * F(prefix[l][6 * M][1], 6 * M * PRECISION)
            assert F(*hmean["upper"]) <= band_bound <= prefix_bound
            bounds[str(l)] = {"child_tail_mean": interval(qsum[l], M),
                              "prefix_tail_mean_at_six_M": interval(prefix[l][6 * M], 6 * M),
                              "certified_child_bound_upper": ratio(band_bound),
                              "certified_prefix_bound_upper": ratio(prefix_bound)}
            counts["exact_sparse_band_and_prefix_transfers"] += 1
        rows.append({"parent_interval": [M, 2 * M], "nonfusion_fraction": ratio(eta),
                     "prearrival_mean": hmean, "cutoff_bounds": bounds})
        counts["authenticated_prior_prearrival_band_comparisons"] += 1
        print("Sparse prearrival band passed:", k, flush=True)
    return rows


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT / name).read_text())
        for path, expected in record["sha256"].items():
            assert digest(ROOT / path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    paths, prefix, bands = profiles(counts)
    landing_rows = passages(paths, counts)
    sparse_rows = sparse_prearrival(paths, prefix, counts)
    replay = {"source_interval": [1, LIMIT], "tail_profile_bands": bands,
              "first_odd_passages": landing_rows, "sparse_prearrival_bands": sparse_rows,
              "counts": dict(counts),
              "scope": "All sampled sources actually reach one. No finite run establishes uniform tail decay over all source sizes."}
    (OUT / "replay.json").write_text(json.dumps(replay, indent=2) + "\n")
    files = [*SOURCES, Path(__file__).name, "verify_deficit_limit_law.py",
             "verify_prearrival_deficit_transfer.py", "docs/DEFICIT-TAIL-PROFILE.md",
             "docs/DEFICIT-CLOCK-MOMENT.md", "docs/DEFICIT-LIMIT-LAW.md",
             "docs/PREARRIVAL-DEFICIT-TRANSFER.md", "docs/SIGNED-ARRIVAL-WINDOWS.md",
             "docs/WEIGHTED-DISSIPATION.md", *PRIOR,
             "results/deficit-clock-moment/replay.json", "results/signed-arrival-windows/replay.json",
             "results/deficit-tail-profile/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version, "builds": builds,
              "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": validated,
              "finite_scope": dict(counts),
              "kernel_scope": ["Finite rational loss-age tails equal shorter prefix deficits.",
                               "Cutoff cases, simultaneous common-tail comparison, scalar-tail and sparse-support inequalities."],
              "written_scope": ["Joint convergence of the global minimum, the entire deficit tail profile in c_0, and terminal weight.",
                                "Uniform vanishing of profile tails in probability, not in mean.",
                                "The limiting deficit law's first moment equals the weighted remaining-clock series as an extended value, possibly infinite.",
                                "Equivalence of source-deficit uniform integrability, uniform mean clock-tail decay, and convergence of source means to the finite common moment.",
                                "Under these unproved equivalent conditions, the known-child prearrival mean tends to zero."],
              "analytic_scope": "The sequence-space and density deductions use the earlier local WRITTEN first-passage, packing and coalescence arguments. No external reciprocal density floor or new external build is used.",
              "floating_scope": "No floating-point verification decisions; aggregate intervals use exact directed integer rounding at scale 2^96.",
              "not_proved": ["Finiteness of the limiting mean, bounded source means, uniform integrability or uniform mean tail decay.",
                             "A bound for negative arrival advances, postarrival drift or unknown-child pairs.",
                             "A new arrival-clock bound, escape exclusion, other-cycle exclusion or full Collatz."],
              "sha256": {str(p): digest(ROOT / p) for p in files}}
    (OUT / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
