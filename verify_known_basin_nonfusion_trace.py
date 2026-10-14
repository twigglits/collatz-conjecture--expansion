"""Finite verification for the known-basin nonfusion trace obstruction.

All infinite divergence, density, packing and measure arguments remain
written. No finite computation is treated as an asymptotic estimate.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_dyadic_coalescence_defects import SOURCES as GRADE_SOURCES

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/known-basin-nonfusion-trace"
SOURCE = "lean/KnownBasinNonfusionTrace.lean"
SOURCES = [*GRADE_SOURCES, SOURCE]
THEOREMS = ["known_double", "same_grade_mate", "unmarked_known_step",
            "unmarked_known_chain", "defect_even_known", "defect_never_fused",
            "grade_detects_defect", "linear_green_identity"]
PRIOR = ["results/dyadic-coalescence-defects/verification.json",
         "results/weighted-dissipation/verification.json",
         "results/harmonic-return-trace/verification.json",
         "results/annulus-time-budgets/verification.json",
         "results/lower-return-clock-moments/verification.json"]
PRECISION = 1 << 80


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(value):
    value = Fraction(value)
    return [value.numerator, value.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, t):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def first_arrivals(maximum, counts):
    memo = {1: (0, 0)}
    for n in range(2, maximum+1):
        x, trail, seen = n, [], set()
        while x not in memo:
            assert x not in seen, ("unexpected cycle", n, x)
            assert len(trail) < 10000, "Unresolved source; not a divergence certificate."
            seen.add(x)
            trail.append(x)
            x = step(x)
        t, a = memo[x]
        for x in reversed(trail):
            t, a = t+1, a+(x & 1)
            memo[x] = t, a
            counts["certified_first_arrival_links"] += 1
    for n in range(1, maximum+1):
        t, a = memo[n]
        assert n*3**a <= 2**t
        if n <= 2048 or n & (n-1) == 0:
            x, odds, clock = n, 0, 0
            while x != 1:
                odds += x & 1
                x, clock = step(x), clock+1
                assert clock <= t
            assert (clock, odds) == (t, a)
            counts["independent_first_arrival_replays"] += 1
        counts["certified_sources_and_first_hit_weights"] += 1
    return memo


def census(counts):
    maximum = 1 << 17
    memo = first_arrivals(maximum, counts)
    max_clock = max(memo[2*n][0] for n in range(1, maximum//2))
    denominator = 1 << max_clock
    rows, defective, cumulative_green = [], set(), 0
    minimum_weight = Fraction(1)
    for k in range(16):
        lo, hi = 1 << k, 1 << (k+1)
        bad, harmonic_lo, harmonic_hi, green = 0, 0, 0, 0
        for n in range(lo, hi):
            tn, an = memo[n]
            tx, ax = memo[2*n]
            ty, ay = memo[2*n+1]
            assert (tx, ax) == (tn+1, an)
            is_bad = ty-2*ay != tn-2*an+1

            # Independently follow both endpoints to the known cycle.
            x, y, a, b, p, clock = 2*n, 2*n+1, 0, 0, 1, 0
            ever_balanced = False
            sums = [0, 0]  # Common denominator 2**clock after each visit.
            terminal = max(tx, ty)
            while True:
                ever_balanced |= x == y and a == b
                for target in (1, 2):
                    sums[target-1] = 2*sums[target-1] + (p if x == target else 0)
                if clock == terminal:
                    break
                px, py = x & 1, y & 1
                a, b, p = a+px, b+py, p*3**px
                x, y, clock = step(x), step(y), clock+1
                counts["independent_paired_steps"] += 1
            assert x in (1, 2) and y in (1, 2)
            assert ever_balanced == (not is_bad)
            assert (x == y and a == b) == (not is_bad)
            counts["grade_vs_direct_pair_classifications"] += 1

            # Complete the linear coefficient Green sums, including all
            # future visits, by the exact ratio 3/4 every two clocks.
            tail_factors = (3, 6) if x == 1 else (2, 3)
            complete_one = sums[0]+tail_factors[0]*p
            complete_two = sums[1]+tail_factors[1]*p
            expected_one = 4*3**ax*(1 << (terminal-tx))
            assert complete_one == expected_one
            assert complete_two == 2*expected_one
            counts["exact_all_future_source_green_identities"] += 2

            if is_bad:
                bad += 1
                defective.add(n)
                q, rem = divmod(PRECISION, n)
                harmonic_lo += q
                harmonic_hi += q+bool(rem)
                green += 4*3**ax*(1 << (max_clock-tx))
                weight = Fraction(n*3**an, 1 << tn)
                minimum_weight = min(minimum_weight, weight)
        assert harmonic_lo*hi >= bad*PRECISION
        assert harmonic_hi*lo <= bad*PRECISION+lo*bad
        assert green >= 0
        cumulative_green += green
        rows.append({"level": k, "parent_interval": [lo, hi],
                     "known_basin_defective_parents": bad,
                     "defective_fraction": ratio(Fraction(bad, lo)),
                     "harmonic_mass_enclosure": {
                         "lower": ratio(Fraction(harmonic_lo, PRECISION)),
                         "upper": ratio(Fraction(harmonic_hi, PRECISION))},
                     "complete_target_one_subseries": ratio(Fraction(green, denominator)),
                     "complete_target_two_subseries": ratio(Fraction(2*green, denominator)),
                     "cumulative_target_one_subseries": ratio(Fraction(cumulative_green, denominator))})
        counts["harmonic_band_lower_bounds"] += 1
        print("Known-basin defect band passed:", k, "defective parents:", bad, flush=True)

    # Independent exact harmonic sums for the initial small bands.
    for row in rows[:8]:
        lo, hi = row["parent_interval"]
        actual = sum((Fraction(1, n) for n in range(lo, hi) if n in defective), Fraction(0))
        bounds = row["harmonic_mass_enclosure"]
        assert Fraction(*bounds["lower"]) <= actual <= Fraction(*bounds["upper"])
        counts["independent_exact_harmonic_sums"] += 1

    return {"maximum_certified_endpoint": maximum, "rows": rows,
            "minimum_first_hit_weight_on_selected_parents": ratio(minimum_weight),
            "scope": "Finite source sets, every future visit certified by exact cycle tails. No asymptotic inference."}, defective


def inverse_traces(counts, defective):
    rows = []
    for target in (1, 2):
        layer = {target: 0}
        cumulative, even_cumulative, marked_cumulative = Fraction(0), Fraction(0), Fraction(0)
        target_rows = []
        for t in range(33):
            z, ze, zd = 0, 0, 0
            for m, a in layer.items():
                assert direct(m, t) == (target, a)
                y, b = direct(m+1, t)
                nonfused = (y, b) != (target, a)
                if nonfused:
                    z += 3**a
                    if m % 2 == 0:
                        ze += 3**a
                        if m//2 in defective:
                            zd += 3**a
                elif m % 2 == 0:
                    assert m//2 not in defective
                assert m <= (1 << t)*target
                counts["inverse_source_forward_and_mask_checks"] += 1
            assert 0 <= zd <= ze <= z
            if t <= 8:
                brute = {}
                for m in range(1, (1 << t)*target+1):
                    x, a = direct(m, t)
                    if x == target:
                        brute[m] = a
                assert brute == layer
                counts["independent_exhaustive_inverse_layers"] += 1
            cumulative += Fraction(z, 1 << t)
            even_cumulative += Fraction(ze, 1 << t)
            marked_cumulative += Fraction(zd, 1 << t)
            if t in (0, 1, 2, 4, 8, 12, 16, 20, 24, 28, 32):
                target_rows.append({"H": t, "last_layer_sources": len(layer),
                                    "Z_H": ratio(cumulative),
                                    "even_source_Z_H": ratio(even_cumulative),
                                    "finite_census_defect_subseries_through_H": ratio(marked_cumulative)})
            if t == 32:
                break
            nxt = {}
            for n, a in layer.items():
                assert 2*n not in nxt
                nxt[2*n] = a
                if n % 3 == 2:
                    m = (2*n-1)//3
                    assert m > 0 and m & 1 and step(m) == n and m not in nxt
                    nxt[m] = a+1
            layer = nxt
        rows.append({"target": target, "rows": target_rows})
        print("Exact inverse nonfusion trace passed: target", target, "through clock 32", flush=True)

    for j in range(129):
        numerator = sum(3**i*4**(j-1-i) for i in range(j))
        assert numerator+3**j == 4**j
        counts["independent_finite_green_sums"] += 1
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-known-basin-trace-") as directory:
        for source in SOURCES:
            obj = Path(directory)/(Path(source).stem+".olean")
            log = OUT/(Path(source).stem+".log")
            command = ["lean", "-o", str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   result.stdout, re.M)
                assert {name for name, _ in roots} == {"KnownBasinNonfusionTrace."+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {
                        "propext", "Classical.choice", "Quot.sound"}, name
            builds.append({"source": source, "source_sha256": digest(ROOT/source),
                           "command": command, "returncode": result.returncode,
                           "elapsed_seconds": round(time.monotonic()-started, 3),
                           "fresh_build": True, "native_computation_used": False,
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def validate_external_replay():
    """Reuse the completed replay, distinguishing retained objects from sources.

    The old temporary source tree may have been cleaned. Its absence is
    recorded explicitly; a retained inventory is not a fresh source audit.
    """
    record = json.loads((ROOT/"results/predecessor-density-review/verification.json").read_text())
    archive = json.loads((ROOT/"results/predecessor-density-review/archive-authentication.json").read_text())
    assert record["status"] == "passed" and record["modules_total"] == 389
    assert len(record["builds"]) == 389 and len(record["axiom_lines"]) == 3
    assert archive["status"] == "passed_archive_and_assembled_source_identity"
    assert archive["assembly_sha256"] == record["assembly_sha256"]
    inventory = {row["path"]: row["sha256"] for row in archive["files"]}
    assert inventory["lake-manifest.json"] == record["lake_manifest_sha256"]
    sources_present, sources_missing = 0, 0
    for build in record["builds"]:
        command = build["command"]
        source_name = command[-1]
        assert inventory[source_name] == build["source_sha256"]
        source = Path(record["assembled"])/source_name
        if source.exists():
            assert digest(source) == build["source_sha256"]
            sources_present += 1
        else:
            sources_missing += 1
        obj = Path(command[command.index("-o")+1])
        assert digest(obj) == build["olean_sha256"], obj
        assert digest(ROOT/build["log"]) == build["log_sha256"], build["log"]
        assert build["returncode"] == 0
    for line in record["axiom_lines"]:
        assert "sorryAx" not in line and "ofReduceBool" not in line
        match = re.search(r"depends on axioms: \[([^\]]*)\]", line)
        assert match and {a.strip() for a in match[1].split(",")} <= {
            "propext", "Classical.choice", "Quot.sound"}
    return {"reused_completed_replay": True,
            "retained_project_object_hashes_revalidated": 389,
            "retained_project_build_log_hashes_revalidated": 389,
            "recorded_source_hashes_matched_to_retained_archive_inventory": 389,
            "live_project_source_hashes_revalidated": sources_present,
            "temporary_project_source_files_missing": sources_missing,
            "new_external_source_replay": False,
            "full_third_party_source_rebuild": False,
            "premise_used": "Positive lower natural density of predecessors of 1 only.",
            "natural_passage_or_density_one_premise_used": False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validated = {}
    for name in PRIOR:
        prior = json.loads((ROOT/name).read_text())
        assert prior["status"] == "passed", name
        for path, expected in prior["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(prior["sha256"])
    external = validate_external_replay()
    print("Authenticated prior local records and completed external PLD replay.", flush=True)
    version, builds = build()
    counts = Counter()
    finite, defective = census(counts)
    traces = inverse_traces(counts, defective)
    replay = {"finite_source_census": finite, "finite_inverse_traces": traces,
              "counts": dict(counts), "harmonic_enclosure_precision": PRECISION,
              "infinite_scope": "None. Divergence uses the written measure and packing argument and external PLD."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_dyadic_coalescence_defects.py",
             "docs/KNOWN-BASIN-NONFUSION-TRACE.md", "docs/FINITE-PATH-PACKING.md",
             "docs/WEIGHTED-DISSIPATION.md", "docs/DYADIC-COALESCENCE-DEFECTS.md",
             "docs/HARMONIC-RETURN-TRACE.md", *PRIOR,
             "results/predecessor-density-review/verification.json",
             "results/predecessor-density-review/archive-authentication.json",
             "results/known-basin-nonfusion-trace/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "external_input": external,
              "finite_scope": dict(counts), "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Unmarked binary tails from a known visit stay balanced and in the known basin.",
                               "Defective parents have known even children and never-balanced adjacent pairs.",
                               "Grade classification given both arrivals, and the finite linear Green identity."],
              "written_scope": ["Known-basin defective parents have divergent harmonic mass, using external PLD at one.",
                                "Simple-path packing gives a uniform positive first-hit weight.",
                                "The full nonfusion integer Green traces at 1 and 2 diverge even on the selected known-basin even sources.",
                                "The prior square-root upper bound remains compatible with this divergence."],
              "not_proved": ["Divergence or finiteness of either selected equal-count return trace.",
                             "A quantitative lower growth rate in clock H, or the critical discount range.",
                             "An actual-gradient power estimate, Q, escape or other-cycle exclusion, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
