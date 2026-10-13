"""Finite integer inputs for a WRITTEN, externally dependent Cesaro result.

The external clock/density limits are not locally compiled or finite-tested.
This script does not decide Collatz and never infers nonperiodicity from fuel.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/integer-return-cesaro"
CLONE = ROOT.parent / "collatz-two-coordinate-obstruction"
REVISION = "a7275d5a73814d3d9a400c6fe6577de9542b03a3"
SOURCES = ["CollatzAffine.lean", "CollatzPacking.lean",
           "lean/CoalescenceTail.lean", "lean/IntegerReturnCesaro.lean"]
THEOREMS = ["residue_endpoint_bound", "positive_column_iff",
            "column_quotient_unique", "source_residue", "source_bound",
            "bounded_hit_source", "balanced_persists_le",
            "nonfused_backwards", "nonfused_mask_lift"]
PRIOR = ["results/count-return-clock/verification.json",
         "results/two-coordinate-review/verification.json"]
EXTERNAL = ["WeightedSourcePeriodicMean.lean", "FirstHitWordWeights.lean",
            "ActualUnconditionalCanonicalTrace.lean", "FirstHitClockDensity.lean",
            "FirstHitClockConversion.lean", "ActualCycleWeights.lean",
            "ActualGreenSeries.lean", "ActualGreenDensityLimit.lean",
            "PeriodicMarkedFirstHitMeanFromSources.lean"]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rat(x):
    return str(F(x))


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def path(n, depth):
    states, counts = [n], [0]
    for _ in range(depth):
        counts.append(counts[-1]+(states[-1] & 1))
        states.append(step(states[-1]))
    return states, counts


def predecessors(depth, target):
    layer = {target: 0}
    for _ in range(depth):
        next_layer = {}
        for n, a in layer.items():
            assert 2*n not in next_layer
            next_layer[2*n] = a
            if n % 3 == 2:
                m = (2*n-1)//3
                assert m > 0 and m & 1 and step(m) == n
                assert m not in next_layer
                next_layer[m] = a+1
        layer = next_layer
    return layer


def finite_checks():
    H, target_cap = 12, 128
    counter = Counter()
    rows, masks = {}, {}
    for t in range(H+1):
        row = []
        for r in range(1 << t):
            xs, aa = path(r, t)
            ys, bb = path(r+1, t)
            x, y, a, b = xs[-1], ys[-1], aa[-1], bb[-1]
            assert x < 3**a
            fused = x == y and a == b
            selected = t > 0 and r % 2 == 0 and a == b and not fused
            row.append((x, a, fused, selected))
            counter["residue_endpoint_bounds"] += 1
        rows[t] = row
        masks[t] = [int(not x[2]) for x in row]
    mark_depths = (1, 2, 3, 4, 6, 8, 10, 12)
    markers = [("all", lambda m: 1), ("even", lambda m: int(m % 2 == 0)),
               ("multiples_three", lambda m: int(m % 3 == 0)),
               ("first_two_mod_five", lambda m: int(m % 5 < 2))]
    markers += [(f"nonfused_{L}", lambda m, L=L: masks[L][m % (1 << L)])
                for L in mark_depths]
    diagnostics = []
    for n in range(1, target_cap+1):
        first = {}
        visit = {name: [] for name, _ in markers}
        first_by_clock = {name: [] for name, _ in markers}
        selected_by_clock = []
        for t in range(H+1):
            inv = predecessors(t, n)
            columns = {}
            selected_mass = 0
            for r, (x, a, _, selected) in enumerate(rows[t]):
                A = 3**a
                if n % A != x:
                    continue
                q = n//A
                m = (1 << t)*q+r
                assert m > 0 and m <= (1 << t)*n and m % (1 << t) == r
                assert x+A*q == n and m not in columns
                xx, ac = path(m, t)
                yy, bc = path(m+1, t)
                assert xx[-1] == n and ac[-1] == a
                actual_selected = (t > 0 and m % 2 == 0 and ac[-1] == bc[-1]
                                   and xx[-1] != yy[-1])
                assert selected == actual_selected
                columns[m] = a
                counter["positive_column_preimages"] += 1
                for L in mark_depths:
                    if L <= t:
                        actual_mask = int(not (xx[L] == yy[L] and ac[L] == bc[L]))
                        assert actual_mask == masks[L][r % (1 << L)]
                        assert actual_mask == masks[L][m % (1 << L)]
                        assert not selected or actual_mask == 1
                        counter["lifted_nonfusion_and_selection_checks"] += 1
                if selected:
                    selected_mass += A
                if m not in first:
                    tau = xx.index(n)
                    assert tau == t
                    weight = F(1)
                    for v in xx[:tau]:
                        if v & 1:
                            weight *= F(3*v, 3*v+1)
                    lam = F(3**ac[tau], 1 << tau)
                    assert lam == n*weight/m and 0 < weight <= 1
                    first[m] = (tau, lam)
                    counter["exact_first_hit_weight_identities"] += 1
            assert columns == inv
            counter["complete_residue_inverse_bijections"] += 1
            selected_by_clock.append(F(selected_mass, 1 << t))
            for name, mark in markers:
                numerator = sum(3**a*mark(m) for m, a in inv.items())
                visit[name].append(F(numerator, 1 << t))
                first_by_clock[name].append(sum((lam*mark(m) for m, (tau, lam)
                                                 in first.items() if tau == t), F(0)))
                if name.startswith("nonfused_") and int(name.split("_")[1]) <= t:
                    assert selected_mass <= numerator
                    counter["marked_integer_selection_inequalities"] += 1

        nx, na = path(n, H)
        observed_period = next((t for t in range(1, H+1) if nx[t] == n), None)
        if observed_period is not None:
            rho = F(3**na[observed_period], 1 << observed_period)
            assert 0 < rho < 1
            counter["actual_periodic_targets_checked"] += 1
        for name, _ in markers:
            for h in range(H+1):
                cumulative = sum(visit[name][:h+1], F(0))
                if observed_period is None:
                    # This only excludes repeat visits through this finite h.
                    rhs = sum(first_by_clock[name][:h+1], F(0))
                else:
                    rhs = sum((rho**j*sum(first_by_clock[name][:h-j*observed_period+1], F(0))
                               for j in range(h//observed_period+1)), F(0))
                assert cumulative == rhs
                counter["marked_finite_visit_reconstructions"] += 1
        if n in (1, 2, 3, 5, 27, 97, 128):
            diagnostics.append({"target": n, "observed_period_through_cap": observed_period,
                                "rows": [{"H": h, "return_occupation": rat(sum(selected_by_clock[:h+1])),
                                          "return_time_average": rat(sum(selected_by_clock[:h+1])/h),
                                          "full_time_average": rat(sum(visit['all'][:h+1])/h)}
                                         for h in (4, 8, 12)]})

    # The valuation-layer clock transport is exact where the finite initial
    # halving exception is absent; no asymptotic clock estimate is tested.
    for q in range(1, 258, 2):
        xs, counts = path(q, 32)
        for n in set(xs):
            if not 0 < n < q:
                continue
            tau = xs.index(n)
            for ell in range(7):
                xx, aa = path((1 << ell)*q, tau+ell)
                assert xx.index(n) == ell+tau and aa[-1] == counts[tau]
                counter["dyadic_first_hit_clock_transports"] += 1
    harmonic = [F(0)]
    for x in range(1, 258):
        harmonic.append(harmonic[-1]+F(1, x))
    for J in range(9):
        for X in range(258):
            lhs = sum((F(1, m) for m in range(1 << J, X+1, 1 << J)), F(0))
            assert lhs == F(1, 1 << J)*harmonic[X//(1 << J)]
            counter["exact_dyadic_harmonic_tail_identities"] += 1
    return {"clock_cap": H, "target_cap": target_cap, "counts": dict(counter),
            "nonfusion_mask_means": [{"L": L, "mean": rat(F(sum(masks[L]), 1 << L))}
                                      for L in range(H+1)],
            "illustrative_finite_averages": diagnostics,
            "asymptotic_scope": "None: finite averages are diagnostics, not evidence certifying a limit or rate."}


def authenticate():
    prior = {}
    for name in PRIOR:
        record = json.loads((ROOT/name).read_text())
        assert record["status"].lower() in ("pass", "passed")
        hashes = record.get("sha256", record.get("local_sha256"))
        for file, expected in hashes.items():
            assert digest(ROOT/file) == expected, (name, file)
        prior[name] = len(hashes)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=CLONE, text=True).strip()
    assert revision == REVISION
    assert not subprocess.check_output(["git", "status", "--porcelain=v1"], cwd=CLONE, text=True)
    bundle = CLONE / "formal-stationary-envelope"
    inventory = json.loads((bundle/"source-manifest.json").read_text())["modules"]
    external = {}
    for name in EXTERNAL:
        entry = inventory[Path(name).stem]
        source = entry.get("source", "source/"+name)
        expected = entry.get("sha256", entry.get("source_sha256"))
        assert digest(bundle/source) == expected, name
        external[str((bundle/source).relative_to(CLONE))] = expected
    return prior, {"revision": revision, "worktree_clean": True,
                   "locally_recompiled": False, "source_sha256": external,
                   "source_inventory_sha256": digest(bundle/"source-manifest.json")}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-integer-return-") as d:
        for source in SOURCES:
            obj = Path(d)/(Path(source).stem+".olean")
            log = OUT/(Path(source).stem+".log")
            start = time.monotonic()
            command = ["lean", "-o", str(obj), source]
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=d, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
            if source == SOURCES[-1]:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {n for n, _ in roots} == {"IntegerReturnCesaro."+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {
                        "propext", "Classical.choice", "Quot.sound"}, name
            builds.append({"source": source, "source_sha256": digest(ROOT/source),
                           "command": command, "returncode": result.returncode,
                           "elapsed_seconds": round(time.monotonic()-start, 3),
                           "fresh_build": True, "native_computation_used": False,
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior, external = authenticate()
    version, builds = build()
    finite = finite_checks()
    (OUT/"replay.json").write_text(json.dumps(finite, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "docs/INTEGER-RETURN-CESARO.md", *PRIOR,
             "results/integer-return-cesaro/replay.json", *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": prior, "external_dependencies": external,
              "kernel_scope": ["Exact positive-column preimages, uniqueness and source cutoff.",
                               "Persistence of balanced fusion, backward nonfusion and periodic masks."],
              "finite_scope": finite["counts"], "floating_scope": "None in verification decisions.",
              "written_external_scope": ["Full-source first-hit elapsed clock obtained from the external odd-source clock.",
                                         "Periodic marked physical-time first-hit and all-visit Cesaro limits.",
                                         "K*_(0,H)(n)/H tends to zero at each fixed positive integer."],
              "not_proved": ["Finite K*_0 at each integer or pointwise decay of individual kappa_t.",
                             "Uniformity on growing target intervals or periods, or a convergence rate.",
                             "Actual-gradient bounds, temporal criterion Q, exclusion of escape or other cycles, or Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS),
                      "finite_checks": finite["counts"],
                      "analytic_proof": "Written; external dependencies not locally replayed."}, indent=2))


if __name__ == "__main__":
    main()
