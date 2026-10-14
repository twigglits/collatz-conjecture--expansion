"""Exact finite replay of the remaining-clock loss identity.

The uniform tail estimate, density moment limits and optional reciprocal
density floor remain written/external inputs, not finite-check conclusions.
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
from verify_prearrival_deficit_transfer import Deficits, ratio, step

ROOT = Path(__file__).resolve().parent
OUT = ROOT/"results/deficit-clock-moment"
SOURCES = ["lean/DeficitLimitLaw.lean", "lean/DeficitClockMoment.lean"]
THEOREMS = ["loss_age_identity", "normalized_loss_age", "total_nonneg",
            "total_mono", "total_scaled", "weighted_total_bounds", "capped_moment_split"]
PRIOR = ["results/deficit-limit-law/verification.json",
         "results/prearrival-deficit-transfer/verification.json",
         "results/weighted-dissipation/verification.json"]
PRECISION = 1 << 96
FLOORS = (31, 127, 511, 2047, 8191)
CLOCKS = (0, 4, 16, 64, 128, 256)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def add_enclosure(pair, numerator, denominator):
    lo, rem = divmod(numerator*PRECISION, denominator)
    pair[0] += lo
    pair[1] += lo+bool(rem)


def interval(pair, count):
    return {"lower": ratio(F(pair[0], count*PRECISION)),
            "upper": ratio(F(pair[1], count*PRECISION))}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-clock-moment-") as directory:
        for source in SOURCES:
            obj = Path(directory)/(Path(source).stem+".olean")
            log = OUT/(Path(source).stem+".log")
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
                assert {name for name, _ in roots} == {"DeficitClockMoment."+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                for _, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
            builds.append({"source": source, "source_sha256": digest(ROOT/source),
                           "command": command, "returncode": 0, "fresh_build": True,
                           "native_computation_used": False, "elapsed_seconds": round(time.monotonic()-start, 3),
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def replay(counts):
    data = Deficits(counts)
    bands = [{"D": [0, 0], "moment": [0, 0], "tail_targets": {h: [0, 0] for h in FLOORS},
              "tail_clocks": {l: [0, 0] for l in CLOCKS},
              "capped_clocks": {l: [0, 0] for l in CLOCKS}, "terms": 0} for _ in range(13)]
    by_target = defaultdict(lambda: [0, 0])
    prefix_lo, prefix_hi = [0], [0]
    for n in range(1, 8192):
        path = independent_path(n, counts)
        T, D, P = path["T"], path["D"], path["P"]
        assert data.get(n) == (T, D)
        k = n.bit_length()-1
        row = bands[k]
        moment, wrong_moment, lost_mass = F(), F(), F()
        exact_caps = [F() for _ in CLOCKS]
        exact_tails = [F() for _ in CLOCKS]
        for j, v in enumerate(path["values"][:-1]):
            loss = path["weights"][j]-path["weights"][j+1]
            if v % 2 == 0:
                assert loss == 0
                continue
            assert v > 1
            age = T-j-1
            assert loss == path["weights"][j]/(3*v+1)
            assert age == data.get(step(v))[0]
            term = age*loss
            moment += term
            wrong_moment += (age+1)*loss
            lost_mass += loss
            add_enclosure(row["moment"], term.numerator, term.denominator)
            for h in FLOORS:
                if v > h:
                    add_enclosure(row["tail_targets"][h], term.numerator, term.denominator)
            for i, L in enumerate(CLOCKS):
                capped, tail = min(age, L), max(age-L, 0)
                assert capped+tail == age
                add_enclosure(row["capped_clocks"][L], capped*loss.numerator, loss.denominator)
                add_enclosure(row["tail_clocks"][L], tail*loss.numerator, loss.denominator)
                if n <= 1024:
                    exact_caps[i] += capped*loss
                    exact_tails[i] += tail*loss
            if k == 12:
                add_enclosure(by_target[v], term.numerator, term.denominator)
            row["terms"] += 1
            counts["exact_odd_loss_and_remaining_clock_identities"] += 1
        assert moment == D and wrong_moment == D+1-P
        assert lost_mass+P == 1
        counts["exact_loss_age_moments"] += 1
        counts["exact_off_by_one_diagnostics"] += 1
        counts["exact_loss_probability_masses"] += 1
        if n <= 1024:
            for L, capped, tail in zip(CLOCKS, exact_caps, exact_tails):
                assert capped+tail == D and 0 <= capped <= min(F(L), D)
                assert 0 <= tail <= D
                counts["independent_exact_capped_moment_decompositions"] += 1
        add_enclosure(row["D"], D.numerator, D.denominator)
        lo, rem = divmod(D.numerator*PRECISION, D.denominator)
        prefix_lo.append(prefix_lo[-1]+lo)
        prefix_hi.append(prefix_hi[-1]+lo+bool(rem))
        if n in (1023, 2047, 4095, 8191):
            print("Exact clock-moment sources through", n, "passed.", flush=True)

    previous = json.loads((ROOT/"results/deficit-limit-law/replay.json").read_text())["finite_bands"]
    rows = []
    for k, row in enumerate(bands):
        M = 1 << k
        assert row["D"][0] <= row["moment"][1] and row["moment"][0] <= row["D"][1]
        assert interval(row["D"], M) == previous[k]["mean_deficit"]
        for L in CLOCKS:
            cap, tail = row["capped_clocks"][L], row["tail_clocks"][L]
            assert cap[0]+tail[0] <= row["D"][1]
            assert row["D"][0] <= cap[1]+tail[1]
        rows.append({"level": k, "source_interval": [M, 2*M], "odd_loss_terms": row["terms"],
                     "mean_deficit": interval(row["D"], M), "clock_moment": interval(row["moment"], M),
                     "target_tail_moments": {str(h): interval(p, M) for h, p in row["tail_targets"].items()},
                     "remaining_clock_tail_moments": {str(l): interval(p, M) for l, p in row["tail_clocks"].items()},
                     "capped_clock_moments": {str(l): interval(p, M) for l, p in row["capped_clocks"].items()}})
        counts["authenticated_prior_band_mean_comparisons"] += 1

    old_h = json.loads((ROOT/"results/signed-arrival-windows/replay.json").read_text())["finite_signed_bands"]["rows"]
    progression_rows = []
    for k in range(11):
        M = 1 << k
        qsum = [0, 0]
        for n in range(M, 2*M):
            d = data.get(3*n+2)[1]
            add_enclosure(qsum, d.numerator, d.denominator)
        h = old_h[k]["unhalved_mean_costs"]["before_both_arrivals"]
        assert F(*h["upper"]) <= F(23, 3)*F(qsum[0], M*PRECISION)+1
        assert F(*h["upper"]) <= 46*F(prefix_lo[6*M], 6*M*PRECISION)+1
        assert qsum[0] <= prefix_hi[6*M]
        progression_rows.append({"parent_band": [M, 2*M], "child_deficit_mean": interval(qsum, M),
                                 "prearrival_mean": h,
                                 "prefix_deficit_mean_at_six_M": interval([prefix_lo[6*M], prefix_hi[6*M]], 6*M)})
        counts["finite_progression_and_prefix_mean_transfers"] += 1

    leaders = sorted(by_target, key=lambda v: by_target[v][0], reverse=True)[:20]
    return {"bands": rows, "progressions": progression_rows,
            "largest_displayed_target_contributions_in_last_band":
                [{"target": v, "contribution": interval(by_target[v], 1 << 12)} for v in leaders],
            "ranking_scope": "Ordered by certified lower endpoints; no asymptotic ranking is asserted.",
            "counts": dict(counts)}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT/name).read_text())
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    data = replay(counts)
    (OUT/"replay.json").write_text(json.dumps(data, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_deficit_limit_law.py",
             "verify_prearrival_deficit_transfer.py", "docs/DEFICIT-CLOCK-MOMENT.md",
             "docs/DEFICIT-LIMIT-LAW.md", "docs/WEIGHTED-DISSIPATION.md",
             "docs/PREARRIVAL-DEFICIT-TRANSFER.md", "docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md",
             *PRIOR, "results/deficit-limit-law/replay.json",
             "results/signed-arrival-windows/replay.json", "results/deficit-clock-moment/replay.json",
             *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version, "builds": builds,
              "kernel_theorems_audited": len(THEOREMS), "prior_hashes_validated": validated,
              "finite_scope": dict(counts),
              "kernel_scope": ["Finite rational loss-age summation identity, including the T-1-j coefficient.",
                               "Nonnegative sums, weighted comparison and the capped moment/tail split."],
              "written_scope": ["The known-basin lifetime deficit is the remaining-clock moment of the existing weight-loss measure.",
                                "The limiting weighted clock series is a lower bound for liminf source means.",
                                "Uniform vanishing of clock-moment tails is equivalent to convergence of source moments to the finite limiting moment.",
                                "A bounded prefix mean would bound known-child prearrival means by 46A+1.",
                                "With the separately external reciprocal weighted-density floor, a bounded mean would force a summable quadratic-normalized stopping-clock series and tau(v)=o(v^2) on the known basin."],
              "analytic_scope": "Density conclusions depend on the previous WRITTEN first-passage and packing arguments. The optional reciprocal floor remains an external premise; no new external source audit or Lean replay was performed.",
              "literature_scope": "Inselmann arXiv:2402.03276v3 was consulted as primary-source context only; none of its claims is a proof input here.",
              "floating_scope": "None in verification decisions; all recorded intervals use exact directed integer rounding at scale 2^96.",
              "not_proved": ["A finite limiting clock moment, bounded source means, uniform integrability or the required uniform tail estimate.",
                             "Equality between this moment series and the first moment of the separate deficit limiting law.",
                             "A stopping-time bound without the bounded-mean and stated external-floor hypotheses.",
                             "Negative arrival advances, postarrival drift, escape exclusion, other-cycle exclusion or full Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
