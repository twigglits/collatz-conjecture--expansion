"""Exact finite ordinary-clock replay for the censored deficit criterion.

The limiting phase law and its zero value are different claims: only the
former is deduced in the written note, under its stated analytic inputs.
No finite population here settles an asymptotic limit or Collatz.
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

from verify_prearrival_deficit_transfer import Deficits, ratio
from verify_weighted_dissipation import ordinary, path_to_one

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/censored-deficit-clock"
SOURCES = ["lean/DeficitLimitLaw.lean", "lean/DeficitClockMoment.lean",
           "lean/CensoredDeficitClock.lean"]
THEOREMS = ["cell_accounting", "cell_bounds", "censored_sum_accounting",
            "censored_sum_bounds", "stopped_is_shorter_prefix",
            "cell_truncation_bound", "one_odd_loss_floor",
            "positive_density_forces_loss", "bad_mass_partition",
            "integer_clock_above_transition"]
PRIOR = ["results/weighted-dissipation/verification.json",
         "results/clocked-minimum/verification.json",
         "results/deficit-tail-profile/verification.json",
         "results/known-basin-nonfusion-trace/verification.json"]
PRECISION = 1 << 96
EXPONENTS = (6, 8, 10, 12, 14)
MULTIPLIERS = (0, 2, 4, 8, 12, 16)
FIELDS = ("weight", "censored_cell", "censored_deficit", "uncensored_deficit", "arrived_weight")


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def add(pair, value):
    lo, rem = divmod(value.numerator * PRECISION, value.denominator)
    pair[0] += lo
    pair[1] += lo + bool(rem)


def interval(pair, denominator):
    return {"lower": ratio(F(pair[0], denominator * PRECISION)),
            "upper": ratio(F(pair[1], denominator * PRECISION))}


def overlaps(a, b):
    return F(*a["lower"]) <= F(*b["upper"]) and F(*b["lower"]) <= F(*a["upper"])


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-censored-clock-") as directory:
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
                assert {name for name, _ in roots} == {"CensoredDeficitClock." + t for t in THEOREMS}
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


def clock_values(t, weights, deficits):
    arrival = len(weights) - 1
    if t < arrival:
        w, raw, censored, hit = weights[t], deficits[t], deficits[t], False
    else:
        age = t - arrival
        q, r = divmod(age, 3)
        factor = F(3, 4) ** q
        cycle_weight = factor * (F(3, 4) if r else 1)
        cycle_sum = 10 * (1 - factor) + factor * (F(0), F(1), F(7, 4))[r]
        w = weights[-1] * cycle_weight
        censored, raw, hit = deficits[-1], deficits[-1] + age - weights[-1] * cycle_sum, True
    z = F() if hit else 1 - w
    post = w if hit else F()
    assert z == 1 - hit - w + post
    assert 0 <= z <= 1 and 0 <= censored <= t
    assert censored <= raw and censored <= deficits[-1]
    return {"weight": w, "censored_cell": z, "censored_deficit": censored,
            "uncensored_deficit": raw, "arrived_weight": post, "hit": hit}


def bounded_censored_deficit(n, horizon):
    """Compute A_horizon with bounded work, without needing a later arrival."""
    assert n > 0 and horizon >= 0
    x, w, deficit = n, F(1), F()
    for t in range(horizon):
        if x == 1:
            return deficit, t
        deficit += 1 - w
        if x & 1:
            w *= F(3 * x, 3 * x + 1)
        x = ordinary(x)
    return deficit, horizon if x == 1 else None


def replay(counts):
    previous = json.loads((ROOT / "results/weighted-dissipation/replay.json").read_text())["finite_clock_checks"]["rows"]
    old = {(r["source_cutoff"], r["ordinary_clock"]): r for r in previous if r["source_cutoff"] <= 1 << max(EXPONENTS)}
    populations = {}
    for k in EXPONENTS:
        X = 1 << k
        clocks = {b * k for b in MULTIPLIERS} | {t for x, t in old if x == X}
        populations[k] = {t: {**{f: [0, 0] for f in FIELDS}, "hit": 0} for t in sorted(clocks)}
    memo = Deficits(counts)
    maximum_clock = max(t for pop in populations.values() for t in pop)
    for n in range(1, (1 << max(EXPONENTS)) + 1):
        states = path_to_one(n)
        weights, deficits = [F(1)], [F()]
        odd, extra = 0, F()
        for t, x in enumerate(states[:-1]):
            deficits.append(deficits[-1] + 1 - weights[-1])
            w = weights[-1] * F(3 * x, 3 * x + 1) if x & 1 else weights[-1]
            if x & 1:
                odd += 1
                extra += 1 - w
            weights.append(w)
            assert w == F(n * 3 ** odd, 2 ** (t + 1 - odd) * states[t + 1])
            counts["independent_ordinary_weight_steps"] += 1
        T = len(states) - 1
        shortcut_t, shortcut_d = memo.get(n)
        assert T == shortcut_t + odd
        assert deficits[-1] == shortcut_d + extra
        assert shortcut_d <= deficits[-1] <= 2 * shortcut_d
        counts["independent_complete_first_arrivals"] += 1
        counts["exact_ordinary_shortcut_clock_and_deficit_comparisons"] += 1

        finite_clock = 8 * max(EXPONENTS)
        bounded, found_arrival = bounded_censored_deficit(n, finite_clock)
        assert bounded == clock_values(finite_clock, weights, deficits)["censored_deficit"]
        assert found_arrival == (T if T <= finite_clock else None)
        counts["independent_bounded_prefix_computations"] += 1
        if found_arrival is None:
            counts["alive_at_cutoff_not_classified_as_nonconvergent"] += 1

        # An independently advanced bounded prefix checks the closed cycle
        # formulas and the first-arrival cutoff at every clock, not just samples.
        if n <= 128:
            x, w, raw, censored, hit = n, F(1), F(), F(), n == 1
            for t in range(maximum_clock + 1):
                current = clock_values(t, weights, deficits)
                assert current == {"weight": w, "censored_cell": F() if hit else 1 - w,
                                   "censored_deficit": censored, "uncensored_deficit": raw,
                                   "arrived_weight": w if hit else F(), "hit": hit}
                raw += 1 - w
                if not hit:
                    censored += 1 - w
                if x & 1:
                    w *= F(3 * x, 3 * x + 1)
                x = ordinary(x)
                hit |= x == 1
                counts["independent_every_clock_censor_and_cycle_checks"] += 1

        for k, pop in populations.items():
            if n > 1 << k:
                continue
            for t, sums in pop.items():
                values = clock_values(t, weights, deficits)
                for field in FIELDS:
                    add(sums[field], values[field])
                sums["hit"] += values["hit"]
                counts["exact_population_source_clock_checks"] += 1
        if n in (1024, 4096, 16384):
            print("Exact ordinary paths and censored clocks through", n, "passed.", flush=True)

    rows = []
    for k, pop in populations.items():
        X = 1 << k
        for t, sums in pop.items():
            row = {"source_cutoff": X, "binary_exponent": k, "ordinary_clock": t,
                   "clock_per_binary_exponent": ratio(F(t, k)),
                   "hit_fraction": ratio(F(sums["hit"], X)),
                   **{field: interval(sums[field], X) for field in FIELDS},
                   "censored_deficit_per_binary_exponent": interval(sums["censored_deficit"], k * X),
                   "uncensored_deficit_per_binary_exponent": interval(sums["uncensored_deficit"], k * X)}
            z, w, post, hit = row["censored_cell"], row["weight"], row["arrived_weight"], F(*row["hit_fraction"])
            accounting = {"lower": ratio(1 - hit - F(*w["upper"]) + F(*post["lower"])),
                          "upper": ratio(1 - hit - F(*w["lower"]) + F(*post["upper"]))}
            assert overlaps(z, accounting)
            counts["exact_population_accounting_enclosures"] += 1
            if (X, t) in old:
                earlier = old[X, t]
                assert overlaps(w, {"lower": earlier["mean_weight_lower"], "upper": earlier["mean_weight_upper"]})
                counts["authenticated_prior_weight_mean_comparisons"] += 1
            rows.append(row)

    assert 4 ** 8 > 2 ** 3 * 3 ** 8
    return {"source_interval_inclusive": [1, 1 << max(EXPONENTS)], "rows": rows,
            "counts": dict(counts), "integer_clock_margin": 4 ** 8 - 2 ** 3 * 3 ** 8,
            "scope": "Finite exact source means only. All sample arrivals are independently reached; an alive flag at a finite cutoff never asserts nonconvergence. No asymptotic error or limiting mass is estimated."}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT / name).read_text())
        assert record["status"] == "passed"
        for path, expected in record["sha256"].items():
            assert digest(ROOT / path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    data = replay(counts)
    (OUT / "replay.json").write_text(json.dumps(data, indent=2) + "\n")
    files = [*SOURCES, Path(__file__).name, "verify_prearrival_deficit_transfer.py",
             "verify_weighted_dissipation.py", "docs/CENSORED-DEFICIT-CLOCK.md",
             "docs/WEIGHTED-DISSIPATION.md", "docs/CLOCKED-MINIMUM.md",
             "docs/DEFICIT-TAIL-PROFILE.md", "docs/PREDECESSOR-DENSITY-REVIEW.md",
             *PRIOR, "results/weighted-dissipation/replay.json",
             "results/censored-deficit-clock/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "map_scope": "Ordinary Collatz; all clocks in the new note and replay are ordinary.",
              "lean_version": version, "builds": builds, "kernel_theorems_audited": len(THEOREMS),
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "kernel_scope": ["Finite censored-cell accounting, bounds and a finite stopped-prefix identity.",
                               "Positive odd-step loss, a positive-density/loss comparison, mass partition and the exact 8k-clock comparison."],
              "written_scope": ["The censored instantaneous mean at c log X tends to zero below kappa and to b=1-r_B-d above it.",
                                "The integrated deficit mean divided by log X tends locally uniformly in c to b(c-kappa)_+, including at the critical coefficient.",
                                "Zero b is equivalent to natural density one of the basin of one.",
                                "With external positive predecessor density, vanishing of the all-source mean A_(8k)/(k 2^k) is equivalent to full positive-integer Collatz."],
              "analytic_scope": "The clock and total-variation inputs remain the earlier local WRITTEN arguments. Bounded integration needs no lifetime-deficit uniform integrability.",
              "external_scope": "Only the pointwise equivalence uses external predecessor-density positivity. Prior local records and their retained provenance are authenticated; no new external build or missing-source replay is claimed.",
              "literature_scope": "Inselmann arXiv:2402.03276v3 was rechecked as context: its mean-clock upper conclusion assumes O(log n) total stopping times. It is not an input to the new argument.",
              "floating_scope": "No floating-point verification decisions. Population intervals use directed integer rounding at scale 2^96; all replay clocks are exact integers.",
              "not_proved": ["The required all-source zero limit, b=0, or any effective asymptotic error bound.",
                             "Uniform integrability or a finite limiting mean of the known-basin lifetime deficit.",
                             "A direct bound for the rare-pair prearrival cost, negative arrival advances, or postarrival drift.",
                             "Escape exclusion, exclusion of other positive cycles, or full Collatz."],
              "sha256": {str(p): digest(ROOT / p) for p in files}}
    (OUT / "verification.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
