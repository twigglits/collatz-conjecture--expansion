"""Read-only source authentication and exact checks for the local repo review.

This is NOT a Lean replay. Upstream manifests and recorded proof executions
remain external evidence. The new local checks concern finite binary image
laws and their exact transfer recurrence, not convergence of Collatz orbits.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parent
REVISION = "a7275d5a73814d3d9a400c6fe6577de9542b03a3"
OUT = ROOT / "results/two-coordinate-review/verification.json"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def authenticate(repo):
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True).strip()
    assert revision == REVISION, (revision, REVISION)
    status = subprocess.check_output(
        ["git", "status", "--porcelain=v1"], cwd=repo, text=True)
    assert not status, "The reviewed checkout must be clean."
    checked = {}
    inventories = []

    def check(base, name, expected):
        path = (base / name).resolve()
        relative = str(path.relative_to(repo))
        actual = digest(path)
        assert actual == expected, relative
        if relative in checked:
            assert checked[relative] == expected
        checked[relative] = actual

    for bundle in ("formal-stationary-envelope", "formal-sharp-haar"):
        base = repo / bundle
        manifest = base / "publication-manifest.json"
        data = json.loads(manifest.read_text())
        for name, entry in data["files"].items():
            check(base, name, entry["sha256"])
            assert (base / name).stat().st_size == entry["bytes"]
        assert len(data["files"]) == data["file_count"]
        inventories.append({"path": str(manifest.relative_to(repo)),
                            "sha256": digest(manifest),
                            "entries_checked": len(data["files"])})

    for bundle in ("formal-growing-deficit", "formal-periodic-census",
                   "formal-cylinder-energy", "formal-raw-occupation",
                   "formal-raw-divergent-excess", "formal-inverse-doob-clock"):
        base = repo / bundle
        manifest = base / "SHA256SUMS.json"
        data = json.loads(manifest.read_text())
        for name, expected in data.items():
            check(base, name, expected)
        inventories.append({"path": str(manifest.relative_to(repo)),
                            "sha256": digest(manifest),
                            "entries_checked": len(data)})

    source_bundles = []
    for bundle in ("formal-stationary-envelope", "formal-sharp-haar",
                   "formal-growing-deficit", "formal-periodic-census",
                   "formal-cylinder-energy", "formal-raw-occupation",
                   "formal-raw-divergent-excess", "formal-inverse-doob-clock"):
        base = repo / bundle
        manifest = base / "source-manifest.json"
        if not manifest.exists():
            manifest = base / "bundle-manifest.json"
        data = json.loads(manifest.read_text())
        for module, entry in data["modules"].items():
            name = entry.get("source", "source/" + module.replace(".", "/") + ".lean")
            check(base, name, entry.get("sha256", entry.get("source_sha256")))
        source_bundles.append({"bundle": bundle,
                               "source_entries_checked": len(data["modules"])})

    paper_manifest = repo / "paper/artifact-manifest.json"
    paper_data = json.loads(paper_manifest.read_text())
    for paper in paper_data["papers"]:
        for key in ("source", "pdf", "theorem_map"):
            check(repo, paper[key], paper[key + "_sha256"])
    assert paper_data["proves_collatz_conjecture"] is False

    # Authenticate the specifically linked execution reports, while keeping
    # their status separate from this local, non-kernel check.
    reports = []
    for bundle, name in (
        ("formal-stationary-envelope", "evidence/reference-replay/replay-record.json"),
        ("formal-sharp-haar", "evidence/reference-replay/replay-record.json"),
        ("formal-growing-deficit", "recorded/replay-record.json"),
        ("formal-cylinder-energy", "recorded/replay-record.json"),
        ("formal-raw-occupation", "recorded/replay-record.json"),
        ("formal-raw-divergent-excess", "recorded/replay-record.json"),
        ("formal-inverse-doob-clock", "recorded/replay-record.json"),
    ):
        path = repo / bundle / name
        assert str(path.relative_to(repo)) in checked
        data = json.loads(path.read_text())
        reports.append({"path": str(path.relative_to(repo)),
                        "sha256": digest(path), "upstream_status": data["status"],
                        "locally_recompiled": False})

    return {"revision": revision, "worktree_clean": True,
            "publication_inventories": inventories,
            "source_bundles": source_bundles,
            "unique_files_matching_published_hashes": len(checked),
            "unique_lean_sources_matching_hashes": sum(p.endswith(".lean") for p in checked),
            "paper_manifest_sha256": digest(paper_manifest),
            "upstream_execution_records": reports,
            "limitations": ["No local compilation or kernel replay of these bundles.",
                            "Published hashes authenticate consistency, not proof correctness.",
                            "No external compiled libraries were acquired or checked."]}


def step(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def direct(n, depth):
    count = 0
    for _ in range(depth):
        count += n & 1
        n = step(n)
    return n, count


@lru_cache(None)
def predecessor_mass(depth, target):
    """Sum 3^odd_count over actual positive depth-t predecessors of target."""
    assert target > 0
    if depth == 0:
        return 1
    total = predecessor_mass(depth - 1, 2 * target)
    if target % 3 == 2:
        parent = (2 * target - 1) // 3
        assert parent > 0 and parent & 1 and step(parent) == target
        total += 3 * predecessor_mass(depth - 1, parent)
    return total


def finite_transfer_checks():
    counts = Counter()
    rows = []
    previous_values = None
    # Integers only: values are 2^t times the density.
    for depth in range(11):
        period = 3 ** depth
        values = [0] * period
        affine_pairs = set()
        for residue in range(2 ** depth):
            endpoint, odd_count = direct(residue, depth)
            slope_numerator = 3 ** odd_count
            offset_numerator = 2 ** depth * endpoint - slope_numerator * residue
            assert offset_numerator >= 0
            assert (odd_count, offset_numerator) not in affine_pairs
            affine_pairs.add((odd_count, offset_numerator))
            for z in range(endpoint % slope_numerator, period, slope_numerator):
                values[z] += slope_numerator
            counts["binary_residue_rows"] += 1

        # A separately generated collection of formal affine words has the
        # same coefficients as the genuine full binary residue period.
        words = [(0, 0)]
        for length in range(depth):
            words = [(a + bit, 3 ** bit * offset + 2 ** length * bit)
                     for a, offset in words for bit in (0, 1)]
        assert len(set(words)) == 2 ** depth
        assert set(words) == affine_pairs
        counts["formal_word_coefficients"] += len(words)

        assert sum(values) == period * 2 ** depth
        if depth > 0:
            old_period = 3 ** (depth - 1)
            for z, value in enumerate(values):
                transferred = previous_values[(2 * z) % old_period]
                if z % 3 == 2:
                    transferred += 3 * previous_values[((2 * z - 1) // 3) % old_period]
                assert value == transferred
                counts["full_ternary_transfer_values"] += 1

        for target in range(1, 257):
            assert values[target % period] == predecessor_mass(depth, target)
            counts["positive_integer_inverse_checks"] += 1
        previous_values = values
        rows.append({"depth": depth, "binary_period": 2 ** depth,
                     "ternary_period": period,
                     "scaled_total_mass": sum(values),
                     "scaled_maximum_density": max(values)})

    # Exact exponent algebra for the alternative external route: an L1
    # clock tail H^(-1/2) and a uniform per-clock Lq image bound yield
    # summed Lp increments iff p < 3q/(2q+1), hence only p < 6/5.
    from fractions import Fraction
    for q in (Fraction(5, 4), Fraction(3, 2), Fraction(7, 4), Fraction(31, 16)):
        boundary = 3 * q / (2 * q + 1)
        p = (1 + boundary) / 2
        theta = (1 - 1 / p) / (1 - 1 / q)
        assert 0 < theta < Fraction(1, 3)
        assert -(1 - theta) / 2 + theta < 0
        assert boundary < Fraction(6, 5)
        counts["external_route_exponent_checks"] += 1
    return {"counts": dict(counts), "depth_rows": rows,
            "scope": "Exact finite identities through depth 10; not an all-depth kernel proof."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path,
                        default=ROOT.parent / "collatz-two-coordinate-obstruction")
    args = parser.parse_args()
    repo = args.repo.resolve()
    authentication = authenticate(repo)
    finite = finite_transfer_checks()
    local_files = ["verify_two_coordinate_review.py",
                   "docs/LOCAL-OBSTRUCTION-REPO-REVIEW.md",
                   "docs/BINARY-IMAGE-ENERGY.md", "docs/RETURN-AFFINE-BUDGET.md"]
    record = {"status": "PASS", "kind": "source-review-and-exact-finite-checks",
              "finished_utc": datetime.now(timezone.utc).isoformat(),
              "external_checkout": str(repo), "authentication": authentication,
              "finite_checks": finite,
              "local_sha256": {p: digest(ROOT / p) for p in local_files},
              "new_local_kernel_theorems": 0,
              "external_results_adopted_as_locally_replayed": False,
              "collatz_resolved": False}
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"status": record["status"],
                      "files_authenticated": authentication["unique_files_matching_published_hashes"],
                      "finite_counts": finite["counts"],
                      "record": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
