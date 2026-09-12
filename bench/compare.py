#!/usr/bin/env python3
"""Verify identical results and benchmark Python against the Rust release CLI.

Prerequisites (run separately): build target/release/collatz-search and produce
verified Python/Rust manifests and Lean certificates. This driver never builds,
exports search data, or invokes Lean. It writes results/rust_benchmark.json only.

    python3 bench/compare.py --repeats 5 --threads 8
    python3 bench/compare.py --check-only
    python3 bench/compare.py --self-test

Each implementation receives the same deterministic seeds and ordinary-step
fuel. One warmup is discarded per configuration. Timed work includes tracing
and collecting copied seed/result rows. Imports, seed generation, comparisons,
serialization, process startup, compilation, and Lean are outside those timers.
Elapsed times are measurements; Lean/native_decide does not certify clocks.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "results/counterexample_search.json"
RUST_MANIFEST = ROOT / "results/counterexample_search_rust.json"
RUST_BINARY = ROOT / "target/release/collatz-search"
OUTPUT = ROOT / "results/rust_benchmark.json"
WARMUPS = 1
SEED_FIELDS = ("family", "label", "start", "lean_expression",
               "prescribed_shortcut_steps", "prescribed_standard_steps")


class VerificationError(RuntimeError):
    """A result, artifact, or benchmark configuration failed verification."""


def assert_equal(actual, expected, label: str) -> None:
    """Require every field, value, type, and row position to agree."""
    if type(actual) is not type(expected):
        raise VerificationError(f"{label}: type {type(actual).__name__} differs from "
                                f"{type(expected).__name__}")
    if isinstance(expected, dict):
        if actual.keys() != expected.keys():
            missing = sorted(expected.keys() - actual.keys())
            extra = sorted(actual.keys() - expected.keys())
            raise VerificationError(f"{label}: missing fields {missing}, extra fields {extra}")
        for key in expected:
            assert_equal(actual[key], expected[key], f"{label}.{key}")
    elif isinstance(expected, list):
        if len(actual) != len(expected):
            raise VerificationError(f"{label}: {len(actual)} rows/items, expected {len(expected)}")
        for index, (got, want) in enumerate(zip(actual, expected)):
            assert_equal(got, want, f"{label}[{index}]")
    elif actual != expected:
        raise VerificationError(f"{label}: {str(actual)[:160]!r} differs from "
                                f"{str(expected)[:160]!r}")


def load_json(path: Path) -> dict:
    with path.open() as stream:
        data = json.load(stream)
    if not isinstance(data, dict):
        raise VerificationError(f"{path}: expected a JSON object")
    return data


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def load_python():
    spec = importlib.util.spec_from_file_location("collatz_python_baseline",
                                                ROOT / "search_counterexample.py")
    if spec is None or spec.loader is None:
        raise VerificationError("could not import the Python search implementation")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def serialized_rows(rows: list[dict]) -> list[dict]:
    # The search timer excludes this JSON-facing conversion of large integers.
    return [{**row, "start": str(row["start"])} for row in rows]


def verify_certificate_manifest(data: dict, path: Path, certificate: Path) -> None:
    assert_equal(data.get("certificate_status"), "verified", f"{path.name}.certificate_status")
    assert_equal(sha256(certificate), data.get("certificate_sha256"),
                 f"{path.name}.certificate_sha256")
    if not isinstance(data.get("rows"), list) or not data["rows"]:
        raise VerificationError(f"{path.name}: missing or empty row dataset")


def prepare():
    """Read/validate artifacts and construct seeds, without tracing any orbit."""
    python_module = load_python()
    baseline = load_json(BASELINE)
    rust = load_json(RUST_MANIFEST)
    py_certificate = ROOT / "CollatzSearchCerts.lean"
    rust_certificate = Path(rust.get("certificate_file", ROOT / "CollatzSearchCertsRust.lean"))
    if not rust_certificate.is_absolute():
        rust_certificate = ROOT / rust_certificate
    verify_certificate_manifest(baseline, BASELINE, py_certificate)
    verify_certificate_manifest(rust, RUST_MANIFEST, rust_certificate)
    for field in ("map", "fuel_ordinary_steps", "coverage", "rows", "summary", "families"):
        assert_equal(rust[field], baseline[field], f"rust_manifest.{field}")
    fuel = baseline["fuel_ordinary_steps"]
    if type(fuel) is not int or not 0 <= fuel <= 2**64 - 1:
        raise VerificationError("manifest fuel must be a nonnegative u64 integer")
    inputs = python_module.seeds()
    expected_inputs = [{key: row[key] for key in SEED_FIELDS} for row in baseline["rows"]]
    assert_equal(serialized_rows(inputs), expected_inputs, "generated_seeds")
    # Recompute summaries from the actual manifest rows, not from copied totals.
    baseline_rows = [{**row, "start": int(row["start"])} for row in baseline["rows"]]
    assert_equal(python_module.summary(baseline_rows), baseline["summary"], "baseline.summary")
    families = {family: python_module.summary([row for row in baseline_rows if row["family"] == family])
                for family in python_module.FAMILIES}
    assert_equal(families, baseline["families"], "baseline.families")
    if not RUST_BINARY.is_file():
        raise VerificationError(f"release binary is missing: {RUST_BINARY}; build it separately")
    return python_module, baseline, inputs, [py_certificate, rust_certificate]


def source_hashes(certificates: list[Path]) -> dict[str, str]:
    paths = [ROOT / "search_counterexample.py", ROOT / "Cargo.toml", ROOT / "Cargo.lock",
             Path(__file__).resolve(), BASELINE, RUST_MANIFEST, RUST_BINARY,
             *sorted((ROOT / "src").rglob("*.rs")), *certificates]
    result = {}
    for path in paths:
        try:
            name = str(path.relative_to(ROOT))
        except ValueError:
            name = str(path)
        result[name] = sha256(path)
    return result


def run_python_rows(module, inputs: list[dict], fuel: int) -> list[dict]:
    rows = []
    for seed in inputs:
        # Include copying the seed dictionary and collecting the result, as
        # Rust includes Seed::clone and Vec<Row> collection in its timer.
        row = dict(seed)
        row.update(module.trace(seed["start"], fuel))
        rows.append(row)
    return rows


def benchmark_python(module, inputs: list[dict], baseline: dict, repeats: int) -> dict:
    times = []
    rows = []
    for index in range(WARMUPS + repeats):
        started = time.perf_counter()
        rows = run_python_rows(module, inputs, baseline["fuel_ordinary_steps"])
        elapsed = time.perf_counter() - started
        # These checks and conversions happen after the elapsed time is read.
        assert_equal(serialized_rows(rows), baseline["rows"], f"python_run_{index}.rows")
        assert_equal(module.summary(rows), baseline["summary"], f"python_run_{index}.summary")
        times.append(elapsed)
        kind = "warmup" if index < WARMUPS else f"sample {index}"
        print(f"Python {kind}: {elapsed:.6f} s; all rows match", file=sys.stderr, flush=True)
    return timing_summary(times[:WARMUPS], times[WARMUPS:])


def verify_rust_payload(data: dict, baseline: dict, repeats: int, threads: int) -> list[float]:
    assert_equal(data.get("implementation"), "Rust", "rust_bench.implementation")
    assert_equal(data.get("profile"), "release", "rust_bench.profile")
    assert_equal(data.get("threads"), threads, "rust_bench.threads")
    assert_equal(data.get("fuel_ordinary_steps"), baseline["fuel_ordinary_steps"], "rust_bench.fuel")
    assert_equal(data.get("summary"), baseline["summary"], "rust_bench.summary")
    assert_equal(data.get("families"), baseline["families"], "rust_bench.families")
    times = data.get("search_seconds")
    if not isinstance(times, list) or len(times) != WARMUPS + repeats:
        raise VerificationError("Rust benchmark returned the wrong number of timing samples")
    if any(type(t) not in (int, float) or not math.isfinite(t) or t <= 0 for t in times):
        raise VerificationError("Rust benchmark returned a nonpositive or nonfinite duration")
    return [float(t) for t in times]


def benchmark_rust(baseline: dict, repeats: int, threads: int) -> dict:
    command = [str(RUST_BINARY), "--bench", str(WARMUPS + repeats),
               "--threads", str(threads), "--fuel", str(baseline["fuel_ordinary_steps"])]
    print(f"Rust release: {threads} worker(s), one warmup and {repeats} samples",
          file=sys.stderr, flush=True)
    # Rust reports its internal search timer. Subprocess/seed generation/export
    # overhead is not silently substituted for that timer. Stderr stays visible.
    completed = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, text=True, check=True)
    data = json.loads(completed.stdout)
    times = verify_rust_payload(data, baseline, repeats, threads)
    result = timing_summary(times[:WARMUPS], times[WARMUPS:])
    result.update({"threads": threads, "command": command,
                   "seed_generation_seconds_excluded": data.get("seed_generation_seconds"),
                   "reported_scope": data.get("scope")})
    return result


def timing_summary(warmup: list[float], measured: list[float]) -> dict:
    return {"warmup_seconds": warmup, "search_seconds": measured,
            "median_seconds": statistics.median(measured),
            "min_seconds": min(measured), "max_seconds": max(measured)}


def version(command: list[str]) -> str:
    return subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE, text=True,
                          check=True).stdout.strip()


class VerificationTests(unittest.TestCase):
    """Small negative controls; these never execute a Collatz benchmark."""

    def test_row_value_field_and_order_mismatches_are_rejected(self):
        expected = [{"label": "a", "steps": 111}, {"label": "b", "steps": 5}]
        corruptions = [
            [{"label": "a", "steps": 110}, expected[1]],
            [{"label": "a", "steps": 111, "extra": 0}, expected[1]],
            list(reversed(expected)),
            [{"label": "a", "steps": "111"}, expected[1]],
        ]
        for rows in corruptions:
            with self.subTest(rows=rows), self.assertRaises(VerificationError):
                assert_equal(rows, expected, "rows")
        assert_equal(expected, expected, "rows")

    def test_wrong_summaries_and_invalid_clock_samples_are_rejected(self):
        baseline = {"fuel_ordinary_steps": 300000, "summary": {"cases": 1257}, "families": {}}
        payload = {"implementation": "Rust", "profile": "release", "threads": 1,
                   "fuel_ordinary_steps": 300000, "summary": {"cases": 1257},
                   "families": {}, "search_seconds": [0.1, 0.2]}
        self.assertEqual(verify_rust_payload(payload, baseline, 1, 1), [0.1, 0.2])
        corruptions = [
            {**payload, "summary": {"cases": 1256}},
            {**payload, "profile": "debug"},
            {**payload, "threads": 8},
            {**payload, "search_seconds": [0.1]},
            {**payload, "search_seconds": [0.1, float("nan")]},
            {**payload, "search_seconds": [0.1, 0]},
        ]
        for data in corruptions:
            with self.subTest(data=data), self.assertRaises(VerificationError):
                verify_rust_payload(data, baseline, 1, 1)


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return parsed


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repeats", type=positive_int, default=5)
    parser.add_argument("--threads", type=positive_int, default=8,
                        help="additional Rust worker count (default 8); single-worker Rust always runs")
    parser.add_argument("--check-only", action="store_true", help="verify saved artifacts/seeds, without tracing")
    parser.add_argument("--self-test", action="store_true", help="run small verification negative controls only")
    args = parser.parse_args()
    if args.self_test:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(VerificationTests)
        if not unittest.TextTestRunner(verbosity=2).run(suite).wasSuccessful():
            raise SystemExit(1)
        return
    module, baseline, inputs, certificates = prepare()
    hashes = source_hashes(certificates)
    if args.check_only:
        print(json.dumps({"verification": "passed", "cases": len(inputs),
                          "checks": "certificate hashes, all saved rows/metrics, generated seed order",
                          "benchmarks_run": False}, indent=2))
        return
    environment = {"platform": platform.platform(), "machine": platform.machine(),
                   "processor": platform.processor(), "logical_cpus": os.cpu_count(),
                   "python": sys.version, "python_implementation": platform.python_implementation(),
                   "python_executable": sys.executable, "rustc": version(["rustc", "--version"]),
                   "cargo": version(["cargo", "--version"])}
    # Sequential batches prevent this driver from making the implementations
    # compete for CPU; their order is recorded rather than hidden.
    python = benchmark_python(module, inputs, baseline, args.repeats)
    rust_single = benchmark_rust(baseline, args.repeats, 1)
    rust_parallel = benchmark_rust(baseline, args.repeats, args.threads) if args.threads != 1 else None
    assert_equal(source_hashes(certificates), hashes, "artifacts_changed_during_benchmark")
    ratios = {"python_over_rust_single": python["median_seconds"] / rust_single["median_seconds"]}
    if rust_parallel is not None:
        ratios.update({"python_over_rust_parallel": python["median_seconds"] / rust_parallel["median_seconds"],
                       "rust_single_over_rust_parallel": rust_single["median_seconds"] / rust_parallel["median_seconds"]})
    data = {"schema": 1, "recorded_at_utc": datetime.now(timezone.utc).isoformat(),
            "environment": environment, "repeats": args.repeats, "warmups_per_configuration": WARMUPS,
            "scope": "ordinary-step trajectory search and copied row collection on identical ordered seeds",
            "excluded_from_search_times": ["imports", "seed generation", "result comparison", "serialization/export",
                                           "process startup", "compilation", "Lean verification"],
            "measurement_notes": [
                "Python uses time.perf_counter; Rust CLI uses std::time::Instant around its search.",
                "Both timers include row collection and replacement of previous results.",
                "Python copies seed dictionaries; Rust clones owned Seed fields.",
                "Sequential batches on this machine; no CPU affinity or thermal controls were applied.",
                "The parallel result includes multiple workers and is reported separately from one-worker Rust.",
                "Wall-clock measurements are empirical; native_decide does not certify timings or speed ratios."],
            "execution_order": ["Python", "Rust single worker"] +
                               ([f"Rust {args.threads} workers"] if rust_parallel else []),
            "fuel_ordinary_steps": baseline["fuel_ordinary_steps"], "summary": baseline["summary"],
            "families": baseline["families"], "python": python, "rust_single": rust_single,
            "rust_parallel": rust_parallel, "median_speed_ratios": ratios,
            "verification": {"saved_rust_and_python_rows_identical": True,
                             "generated_python_seeds_match_saved_rows": True,
                             "each_python_warmup_and_measured_row_matches_baseline": True,
                             "rust_timed_batch_summaries_and_families_match_baseline": True,
                             "both_saved_manifests_have_verified_matching_certificate_hashes": True,
                             "sources_and_binary_unchanged_during_measurement": True},
            "sha256": hashes}
    OUTPUT.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({"output": str(OUTPUT), "python": python, "rust_single": rust_single,
                      "rust_parallel": rust_parallel, "median_speed_ratios": ratios,
                      "verification": "passed"}, indent=2))


if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, ValueError, VerificationError, subprocess.CalledProcessError) as error:
        print(f"error: {error}", file=sys.stderr)
        raise SystemExit(1)
