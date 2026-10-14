"""Finite ordinary-Collatz transport and exact progression counterbounds.

The native census uses propagated rational intervals. The independent Python
census reconstructs each weight directly from its affine numerator. Neither
algorithm needs an arrival after the prescribed finite clock. Closed Lean
certificates check the aggregate comparisons, not the native census itself.
"""
import argparse
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
OUT = ROOT / "results/censored-progression-transport"
SCALE = 1 << 64
SOURCES = ["lean/CensoredProgressionTransport.lean",
           "lean/CensoredProgressionCertificates.lean"]
THEOREMS = {
    "CensoredProgressionTransport": ["scaled_deficit", "even_transport",
        "odd_transport", "odd_loss_identity", "odd_correction_identity",
        "deficit_bounds", "correction_bounds", "population_transport"],
    "CensoredProgressionCertificates": ["native_k17_gt_two",
        "native_k20_gt_nine", "native_k20_gt_eight_corrections"],
}
PRIOR = "results/censored-deficit-clock/verification.json"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def ratio(value):
    return [value.numerator, value.denominator]


def authenticate(record):
    for path, expected in record["sha256"].items():
        assert digest(ROOT / path) == expected, path
    return len(record["sha256"])


def native_censuses():
    """Fresh checked-overflow native runs, sequentially, at two cutoffs."""
    version = subprocess.check_output(["rustc", "--version"], text=True).strip()
    rows = {}
    with tempfile.TemporaryDirectory(prefix="collatz-censored-progression-rust-") as directory:
        binary = Path(directory) / "census"
        command = ["rustc", "-O", "-C", "overflow-checks=yes",
                   "censored_progression_census.rs", "-o", str(binary)]
        subprocess.run(command, cwd=ROOT, check=True)
        binary_hash = digest(binary)
        for k in (17, 20):
            start = time.monotonic()
            run = [str(binary), str(k)]
            result = subprocess.run(run, cwd=ROOT, text=True, capture_output=True)
            assert result.returncode == 0, result.stderr
            assert not result.stderr, result.stderr
            row = json.loads(result.stdout)
            assert row["X"] == 1 << k and row["Y"] == 3 * (1 << k) + 2
            assert row["ordinary_clock"] == 8 * k and int(row["scale"]) == SCALE
            assert row["progression_sources"] == row["X"]
            path = OUT / f"native-k{k}.json"
            if path.exists():
                assert json.loads(path.read_text()) == row, "Native result changed"
            save(path, row)
            save(OUT / f"native-k{k}-provenance.json", {
                "source": "censored_progression_census.rs",
                "source_sha256": digest(ROOT / "censored_progression_census.rs"),
                "rustc_version": version, "compile_command": command,
                "binary_sha256": binary_hash, "run_command": run,
                "verified_at_utc": datetime.now(timezone.utc).isoformat(),
                "fresh_native_run": True, "returncode": result.returncode,
                "elapsed_seconds": round(time.monotonic() - start, 3),
                "census_sha256": digest(path)})
            rows[k] = row
            print(f"Native census k={k}: {row['ordinary_steps']} ordinary steps", flush=True)
    return rows


def independent_census(k):
    """Round the EXACT weight n*3^odd/(2^even*state) at each clock.

    This does not propagate the native algorithm's weight intervals. All
    states and affine numerators are unbounded Python integers.
    """
    x_cut, horizon = 1 << k, 8 * k
    y_cut = 3 * x_cut + 2
    all_lo = all_hi = prog_lo = prog_hi = corr_lo = corr_hi = 0
    steps = odd_steps = alive = prog_count = 0
    start = time.monotonic()
    for n in range(1, y_cut + 1):
        state, elapsed, numerator, two_power = n, 0, n, 1
        a_lo = a_hi = 0
        while elapsed < horizon and state != 1:
            lo, remainder = divmod(numerator * SCALE, two_power * state)
            hi = lo + bool(remainder)
            assert 0 <= lo <= hi <= SCALE
            a_lo += SCALE - hi
            a_hi += SCALE - lo
            if state & 1:
                numerator *= 3
                state = 3 * state + 1
                odd_steps += 1
            else:
                two_power *= 2
                state //= 2
            elapsed += 1
            steps += 1
        alive += state != 1
        assert 0 <= a_lo <= a_hi <= horizon * SCALE
        all_lo += a_lo
        all_hi += a_hi
        if n >= 5 and n % 3 == 2:
            prog_count += 1
            prog_lo += a_lo
            prog_hi += a_hi
            cap = (elapsed + 1) * SCALE
            denominator = 2 * n
            corr_lo += (cap - a_hi) // denominator
            high, remainder = divmod(cap - a_lo, denominator)
            corr_hi += high + bool(remainder)
        if n % 65536 == 0:
            print(f"Independent affine census: {n}/{y_cut} sources", flush=True)
    assert prog_count == x_cut
    row = dict(binary_exponent=k, X=x_cut, Y=y_cut, ordinary_clock=horizon,
               scale=str(SCALE), prefix_sum_lower=str(all_lo), prefix_sum_upper=str(all_hi),
               progression_sum_lower=str(prog_lo), progression_sum_upper=str(prog_hi),
               correction_sum_lower=str(corr_lo), correction_sum_upper=str(corr_hi),
               ordinary_steps=steps, odd_steps=odd_steps, alive_at_cutoff=alive,
               progression_sources=prog_count)
    return row, round(time.monotonic() - start, 3)


def compare_censuses(native, independent):
    for name in ("binary_exponent", "X", "Y", "ordinary_clock", "scale", "ordinary_steps",
                 "odd_steps", "alive_at_cutoff", "progression_sources"):
        assert native[name] == independent[name], name
    for field in ("prefix_sum", "progression_sum", "correction_sum"):
        assert int(native[field + "_lower"]) <= int(independent[field + "_lower"])
        assert int(independent[field + "_upper"]) <= int(native[field + "_upper"])


def comparisons(row, multiplier):
    x, y, t, s = (int(row[key]) for key in ("X", "Y", "ordinary_clock", "scale"))
    sl, sh, pl, ph, el, eh = (int(row[key]) for key in (
        "prefix_sum_lower", "prefix_sum_upper", "progression_sum_lower",
        "progression_sum_upper", "correction_sum_lower", "correction_sum_upper"))
    lo, hi = F(pl, x * s) - F(sh, y * s), F(ph, x * s) - F(sl, y * s)
    assert 0 < lo <= hi
    assert lo > F(multiplier * t, x)
    assert y * pl > x * sh + multiplier * t * y * s
    if row["binary_exponent"] == 20:
        assert x * lo > 8 * F(eh, s)
        assert y * pl > x * sh + 8 * y * eh
    return {"binary_exponent": row["binary_exponent"], "clock": t,
            "delta_lower": ratio(lo), "delta_upper": ratio(hi),
            "correction_lower": ratio(F(el, s)), "correction_upper": ratio(F(eh, s)),
            "delta_X_over_T_lower": ratio(lo * x / t),
            "delta_X_over_correction_upper": ratio(lo * x / F(eh, s)),
            "strictly_rejected_T_over_X_multiplier": multiplier}


def run_census_stage():
    rows = native_censuses()
    independent, seconds = independent_census(17)
    compare_censuses(rows[17], independent)
    checks = [comparisons(rows[17], 2), comparisons(rows[20], 9), comparisons(independent, 2)]
    save(OUT / "independent-k17.json", independent)
    paths = ["censored_progression_census.rs", Path(__file__).name]
    paths += [str(p.relative_to(ROOT)) for p in sorted(OUT.glob("native-k*.json"))]
    paths += [str((OUT / "independent-k17.json").relative_to(ROOT))]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "independent_python_seconds": seconds,
              "independent_method": "Direct exact affine weights, directed rounding at every alive ordinary clock.",
              "independent_interval_containment": True, "comparisons": checks,
              "sha256": {p: digest(ROOT / p) for p in paths}}
    save(OUT / "census.json", record)
    return record


def rational_prefix(n, horizon, counts):
    """Separate Fraction-product implementation, stopped within the clock."""
    state, w, deficit, elapsed = n, F(1), F(), 0
    numerator, two_power = n, 1
    deficits, times, arrived = [deficit], [0], [state == 1]
    for _ in range(horizon):
        if state != 1:
            deficit += 1 - w
            if state & 1:
                w *= F(3 * state, 3 * state + 1)
                numerator *= 3
                state = 3 * state + 1
            else:
                state //= 2
                two_power *= 2
            elapsed += 1
            counts["fraction_weight_steps"] += 1
            assert w == F(numerator, two_power * state)
        deficits.append(deficit)
        times.append(elapsed)
        arrived.append(state == 1)
    counts["bounded_fraction_prefixes"] += 1
    return deficits, times, arrived


def replay():
    counts = Counter()
    horizon = 128
    for n in range(1, 1025):
        q = 3 * n + 2
        dn, _, _ = rational_prefix(n, horizon, counts)
        de, _, _ = rational_prefix(2 * n, horizon + 1, counts)
        do, _, _ = rational_prefix(2 * n + 1, horizon + 2, counts)
        dq, lq, arrived = rational_prefix(q, horizon, counts)
        loss = F(1, 2 * q)
        for t in range(horizon + 1):
            assert de[t + 1] == dn[t]
            error = loss * (1 + lq[t] - dq[t])
            assert do[t + 2] == dq[t] + error
            assert loss <= error <= (t + 1) * loss
            counts["exact_even_transport_checks"] += 1
            counts["exact_odd_transport_and_correction_checks"] += 1
            counts["arrived_child_checks" if arrived[t] else "alive_child_checks"] += 1
    populations = {n: rational_prefix(n, 66, counts) for n in range(1, 195)}
    for x in (1, 2, 4, 8, 16, 32, 64):
        for t in (0, 1, 2, 8, 32, 64):
            left = sum(populations[n][0][t + 2] for n in range(1, 2 * x + 2))
            even = sum(populations[n][0][t + 1] for n in range(1, x + 1))
            odd = sum(populations[3 * n + 2][0][t] for n in range(1, x + 1))
            correction = sum(F(1 + populations[3 * n + 2][1][t] -
                               populations[3 * n + 2][0][t], 2 * (3 * n + 2))
                             for n in range(1, x + 1))
            assert left == even + odd + correction
            counts["exact_population_transport_checks"] += 1
    return dict(counts)


def write_certificates():
    rows = {k: json.loads((OUT / f"native-k{k}.json").read_text()) for k in (17, 20)}
    statements = []
    for k, c, name in ((17, 2, "native_k17_gt_two"), (20, 9, "native_k20_gt_nine")):
        r = rows[k]
        statements.append(f"theorem {name} :\n    ({r['Y']} : Nat) * {r['progression_sum_lower']} >\n"
                          f"      {r['X']} * {r['prefix_sum_upper']} +\n"
                          f"      {c} * {r['ordinary_clock']} * {r['Y']} * {r['scale']} := by decide\n")
    r = rows[20]
    statements.append(f"theorem native_k20_gt_eight_corrections :\n"
                      f"    ({r['Y']} : Nat) * {r['progression_sum_lower']} >\n"
                      f"      {r['X']} * {r['prefix_sum_upper']} +\n"
                      f"      8 * {r['Y']} * {r['correction_sum_upper']} := by decide\n")
    text = ("/- Generated by verify_censored_progression_transport.py.\n"
            "   Kernel arithmetic on recorded interval endpoints only.\n"
            "   The finite population census is a separate native computation. -/\n"
            "import Std\n\nnamespace CensoredProgressionCertificates\n\n" +
            "\n".join(statements) + "\n" +
            "\n".join("#print axioms " + name for name in THEOREMS["CensoredProgressionCertificates"]) +
            "\n\nend CensoredProgressionCertificates\n")
    (ROOT / SOURCES[1]).write_text(text)


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-censored-progression-lean-") as directory:
        for source in SOURCES:
            stem = Path(source).stem
            obj, log = Path(directory) / (stem + ".olean"), OUT / (stem + ".log")
            command = ["lean", "-o", str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("warning:", "error:", "sorryAx", "ofReduceBool"))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                               result.stdout, re.M)
            assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS[stem]}
            assert len(roots) == len(THEOREMS[stem])
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
                if stem.endswith("Certificates"):
                    assert not axioms
            builds.append({"source": source, "source_sha256": digest(ROOT / source),
                           "command": command, "returncode": 0, "fresh_build": True,
                           "native_computation_used": False, "elapsed_seconds": round(time.monotonic() - start, 3),
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census-only", action="store_true", help="Save the costly native and independent census stage.")
    parser.add_argument("--reuse-census", action="store_true", help="Authenticate the saved census stage instead of rerunning it.")
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    prior = authenticate(json.loads((ROOT / PRIOR).read_text()))
    if args.reuse_census:
        census = json.loads((OUT / "census.json").read_text())
        assert census["status"] == "passed"
        authenticate(census)
        compare_censuses(json.loads((OUT / "native-k17.json").read_text()),
                         json.loads((OUT / "independent-k17.json").read_text()))
        for k, c in ((17, 2), (20, 9)):
            comparisons(json.loads((OUT / f"native-k{k}.json").read_text()), c)
    else:
        census = run_census_stage()
    if args.census_only:
        print("Census stage passed; no final verification manifest was written.", flush=True)
        return
    write_certificates()
    version, builds = build()
    counts = replay()
    save(OUT / "replay.json", {"status": "passed", "counts": counts})
    files = SOURCES + [Path(__file__).name, "censored_progression_census.rs",
                       "docs/CENSORED-PROGRESSION-TRANSPORT.md", "docs/CENSORED-DEFICIT-CLOCK.md", PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "map_scope": "Ordinary Collatz and clocks stopped at first arrival at one.",
              "lean_version": version, "builds": builds,
              "kernel_theorems_audited": sum(map(len, THEOREMS.values())),
              "prior_hashes_validated": {PRIOR: prior},
              "census_stage_reused_after_authentication": args.reuse_census,
              "census_verified_at_utc": census["verified_at_utc"],
              "native_scope": "Checked-overflow Rust finite censuses through 393218 and 3145730 at ordinary clocks 136 and 160; not kernel certified.",
              "independent_scope": "Python unbounded integers reconstruct exact affine weights through 393218 at clock 136; direct intervals lie inside native intervals and all step/alive counts match. No full independent replay at the larger cutoff.",
              "finite_replay_counts": counts,
              "kernel_scope": "Finite stopped-weight transport and bounds for actual ordinary-map recursion; finite population parity splitting; three closed integer comparisons of recorded census endpoints. The census endpoints themselves are not kernel derived.",
              "written_scope": "The summed correction is at most (t+1) H_X/6. The exact population recurrence separates progression sampling error from the positive affine correction.",
              "external_scope": "No external theorem or asymptotic input is needed for this transport or its finite counterbounds. The earlier proposed zero-limit criterion retains its separate written and external assumptions.",
              "floating_scope": "No floating-point verification decisions; interval scale 2^64 and all comparisons are exact integers or Fractions.",
              "not_proved": ["Failure of every constant in an O(t/X) or O(t log X/X) progression estimate.",
                             "Failure of every constant multiple of the explicit correction.",
                             "Any effective asymptotic bound on the progression sampling error or the all-source censored mean.",
                             "The all-source zero limit, escape exclusion, other-cycle exclusion, or full Collatz."],
              "sha256": {p: digest(ROOT / p) for p in files}}
    save(OUT / "verification.json", record)
    print(json.dumps({"status": "passed", "kernel_roots": record["kernel_theorems_audited"],
                      "finite_replay_counts": counts}, indent=2))


if __name__ == "__main__":
    main()
