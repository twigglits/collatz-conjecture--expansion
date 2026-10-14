"""Finite exact inputs to the WRITTEN deficit limiting-law argument.

No finite run certifies the analytic mixing or packing premises, tightness,
a limiting law, a uniform mean, or universal Collatz convergence.
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

from verify_prearrival_deficit_transfer import Deficits, enclose, ratio, step

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/deficit-limit-law"
SOURCE = "lean/DeficitLimitLaw.lean"
THEOREMS = ["deficit_append", "deficit_scaled", "deficit_splice", "deficit_range",
            "deficit_prefix_bound", "splice_increase_bound", "common_tail_bound",
            "shared_terminal_weight_bound", "deficit_chain", "clock_chain"]
PRIOR = ["results/prearrival-deficit-transfer/verification.json",
         "results/clocked-minimum/verification.json",
         "results/finite-path-packing/verification.json",
         "results/natural-density/verification.json"]
PRECISION = 1 << 96


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def fresh_build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    with tempfile.TemporaryDirectory(prefix="collatz-deficit-law-") as directory:
        obj = Path(directory)/"DeficitLimitLaw.olean"
        command = ["lean", "-o", str(obj), SOURCE]
        start = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT,
                                env=dict(os.environ, LEAN_NUM_THREADS="1"))
        log = OUT/"DeficitLimitLaw.log"
        log.write_text(result.stdout)
        assert result.returncode == 0, result.stdout
        assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
        roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                           result.stdout, re.M)
        assert {name for name, _ in roots} == {"DeficitLimitLaw."+t for t in THEOREMS}
        assert len(roots) == len(THEOREMS)
        for _, axioms in roots:
            assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
        build = {"source": SOURCE, "source_sha256": digest(ROOT/SOURCE), "command": command,
                 "returncode": 0, "fresh_build": True, "native_computation_used": False,
                 "elapsed_seconds": round(time.monotonic()-start, 3),
                 "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                 "olean_sha256": digest(obj)}
    print("Ten finite rational kernel roots passed.", flush=True)
    return version, build


def independent_path(n, counts):
    x, w, odd, peak = n, F(1), 0, n
    values, weights, seen = [], [], set()
    while True:
        assert x not in seen, ("Unexpected cycle; no certificate emitted", n, x)
        seen.add(x)
        values.append(x)
        weights.append(w)
        if x == 1:
            break
        assert len(values) < 100000, ("Unresolved fuel; not a divergence proof", n)
        if x & 1:
            w *= F(3*x, 3*x+1)
            odd += 1
        x = step(x)
        peak = max(peak, x)
    assert w == F(n*3**odd, 1 << (len(values)-1))
    counts["independent_known_first_arrivals"] += 1
    counts["independent_shortcut_steps"] += len(values)-1
    return {"values": values, "weights": weights, "T": len(values)-1,
            "D": sum((1-u for u in weights[:-1]), F()), "P": weights[-1],
            "peak": peak}


def finite_paths(counts):
    data = Deficits(counts)
    paths = {n: independent_path(n, counts) for n in range(1, 4096)}
    for n, path in paths.items():
        assert data.get(n) == (path["T"], path["D"])
        a, loss_sum = F(), F()
        for i, (x, p) in enumerate(zip(path["values"], path["weights"])):
            t, d = data.get(x)
            assert path["T"] == i+t
            assert path["D"] == a+p*d+(1-p)*t
            assert path["D"] == d+a+(1-p)*(t-d)
            assert 0 <= a <= i*(1-p)
            assert 0 <= path["D"]-d <= (1-p)*path["T"]
            assert 0 <= 1-p <= loss_sum
            counts["exact_prefix_splice_and_increment_checks"] += 1
            counts["exact_finite_product_loss_bounds"] += 1
            if i < path["T"]:
                a += 1-p
                if x & 1:
                    loss_sum += F(1, 3*x+1)
        if 2*n < 4096:
            other = paths[2*n]
            assert (other["D"], other["P"], other["T"]) == (path["D"], path["P"], path["T"]+1)
            counts["exact_initial_halving_invariances"] += 1

    passages = {}
    for H in (1, 3, 7, 31, 127, 511):
        marks = {}
        groups = defaultdict(list)
        for n, path in paths.items():
            i = next(j for j, x in enumerate(path["values"]) if x & 1 and x <= H)
            b, p = path["values"][i], path["weights"][i]
            assert all(x > b for x in path["values"][:i])
            assert all(x > H for x in path["values"][:i] if x & 1)
            assert path["T"] == i+paths[b]["T"]
            assert path["P"] == p*paths[b]["P"]
            assert 0 <= path["D"]-paths[b]["D"] <= (1-p)*path["T"]
            marks[n] = (i, b, p)
            groups[b].append(n)
            counts["exact_odd_passage_record_checks"] += 1
        for sources in groups.values():
            m = sources[0]
            j, b, q = marks[m]
            for n in sources:
                i, _, p = marks[n]
                e = max(1-p, 1-q)
                assert paths[n]["T"]+j == paths[m]["T"]+i
                assert abs(paths[n]["D"]-paths[m]["D"]) <= e*max(paths[n]["T"], paths[m]["T"])
                assert abs(paths[n]["P"]-paths[m]["P"]) <= e
                counts["exact_common_landing_comparisons"] += 1
        passages[H] = marks
    # Earlier even values can lie below the floor, but above the odd landing.
    i, b, _ = passages[31][85]
    assert (i, b) == (8, 1)
    assert paths[85]["values"][4] == 16 < 31
    print("Exact prefixes and common odd landings passed.", flush=True)
    return data, paths, passages


def maximal_coupling(left, right, marks, counts):
    """Exact maximal coupling for power-of-two population sizes."""
    denom = max(len(left), len(right))
    assert denom % len(left) == denom % len(right) == 0
    ll, rr = defaultdict(list), defaultdict(list)
    for n in left:
        ll[marks[n][1]].append([n, denom//len(left)])
    for n in right:
        rr[marks[n][1]].append([n, denom//len(right)])
    edges, unmatched_l, unmatched_r = [], [], []

    def match(a, b):
        i = j = 0
        while i < len(a) and j < len(b):
            w = min(a[i][1], b[j][1])
            edges.append((a[i][0], b[j][0], F(w, denom)))
            a[i][1] -= w
            b[j][1] -= w
            i += a[i][1] == 0
            j += b[j][1] == 0
        return a[i:], b[j:]

    p = Counter(marks[n][1] for n in left)
    q = Counter(marks[n][1] for n in right)
    keys = sorted(set(p) | set(q))
    for b in keys:
        a, z = match(ll[b], rr[b])
        unmatched_l.extend(a)
        unmatched_r.extend(z)
    assert match(unmatched_l, unmatched_r) == ([], [])
    lp, rp = defaultdict(F), defaultdict(F)
    for n, m, w in edges:
        lp[n] += w
        rp[m] += w
    assert all(lp[n] == F(1, len(left)) for n in left)
    assert all(rp[n] == F(1, len(right)) for n in right)
    tv = sum((abs(F(p[b], len(left))-F(q[b], len(right))) for b in keys), F())/2
    bad = sum((w for n, m, w in edges if marks[n][1] != marks[m][1]), F())
    assert sum((w for _, _, w in edges), F()) == 1 and bad == tv
    counts["exact_maximal_couplings_and_marginals"] += 1
    return edges, tv


def finite_couplings(paths, passages, counts):
    rows, maps, link_bounds, link_bad = [], {}, {}, {}
    for Y in (128, 256, 512, 1024, 2048):
        Z = Y//2
        left, right = list(range(Y+1, 2*Y, 2)), list(range(Z+1, 2*Z, 2))
        for H in (1, 3, 7, 31, 127):
            marks = passages[H]
            edges, tv = maximal_coupling(left, right, marks, counts)
            if H == 31:
                assert len(edges) == len(left) and all(w == F(1, len(left)) for _, _, w in edges)
                maps[Y] = {n: m for n, m, _ in edges}
                link_bounds[Y] = max(marks[n][0] for n in left+right)
                link_bad[Y] = tv
            checks = 0
            for L in (0, 8, 32, 128):
                good = [(n, m, w) for n, m, w in edges
                        if marks[n][1] == marks[m][1] and max(marks[n][0], marks[m][0]) <= L]
                bad = 1-sum((w for _, _, w in good), F())
                slow_l = F(sum(marks[n][0] > L for n in left), len(left))
                slow_r = F(sum(marks[n][0] > L for n in right), len(right))
                assert bad <= tv+slow_l+slow_r
                for R in (1, 2, 5, 8):
                    lhs = abs(sum((min(paths[n]["D"], F(R)) for n in left), F())/len(left)
                              -sum((min(paths[m]["D"], F(R)) for m in right), F())/len(right))
                    rhs = R*bad
                    for n, m, w in good:
                        e = max(1-marks[n][2], 1-marks[m][2])
                        bound = e*max(paths[n]["T"], paths[m]["T"])
                        assert abs(paths[n]["D"]-paths[m]["D"]) <= bound
                        rhs += w*min(F(R), bound)
                    assert lhs <= rhs
                    checks += 1
                    counts["exact_truncated_moment_transport_checks"] += 1
                counts["exact_coupled_clock_failure_union_bounds"] += 1
            rows.append({"larger_odd_band": [Y, 2*Y], "smaller_odd_band": [Z, 2*Z],
                         "floor": H, "landing_total_variation": ratio(tv),
                         "coupling_edges": len(edges), "truncated_moment_checks": checks})

    base = list(range(65, 128, 2))
    TB = max(paths[n]["T"] for n in base)
    bad_chains, good_chains = 0, 0
    for n in range(2049, 4096, 2):
        chain = [n]
        for Y in (2048, 1024, 512, 256, 128):
            chain.append(maps[Y][chain[-1]])
        good = all(passages[31][a][1] == passages[31][b][1] for a, b in zip(chain, chain[1:]))
        if not good:
            bad_chains += 1
            continue
        budget = F()
        weights_budget = F()
        for j, Y in enumerate((2048, 1024, 512, 256, 128)):
            clock_bound = TB+sum(link_bounds[V] for V in (2048, 1024, 512, 256, 128)[j:])
            a, b = chain[j:j+2]
            assert paths[a]["T"] <= clock_bound and paths[b]["T"] <= clock_bound
            e = max(1-passages[31][a][2], 1-passages[31][b][2])
            budget += e*clock_bound
            weights_budget += e
        assert abs(paths[chain[0]]["D"]-paths[chain[-1]]["D"]) <= budget
        assert abs(paths[chain[0]]["P"]-paths[chain[-1]]["P"]) <= weights_budget
        good_chains += 1
        counts["exact_glued_five_link_chain_bounds"] += 1
    assert F(bad_chains, 1024) <= sum(link_bad.values(), F())
    assert good_chains > 0
    print("Exact maximal couplings, moment transport and glued chains passed.", flush=True)
    return {"rows": rows, "five_link_chain": {"source_count": 1024, "good": good_chains,
             "bad": bad_chains, "base_minimum_clock": TB,
             "failure_union_bound": ratio(sum(link_bad.values(), F()))}}


def certified_bands(data, counts):
    rows = []
    for k in range(14):
        M = 1 << k
        lo = hi = lo2 = hi2 = 0
        for n in range(M, 2*M):
            _, d = data.get(n)
            a, r = divmod(d.numerator*PRECISION, d.denominator)
            lo += a
            hi += a+bool(r)
            dd = d*d
            a, r = divmod(dd.numerator*PRECISION, dd.denominator)
            lo2 += a
            hi2 += a+bool(r)
            counts["exact_enclosed_band_deficits"] += 1
        assert 0 <= hi-lo <= M and 0 <= hi2-lo2 <= M
        rows.append({"level": k, "source_interval": [M, 2*M],
                     "mean_deficit": {"lower": ratio(F(lo, M*PRECISION)), "upper": ratio(F(hi, M*PRECISION))},
                     "mean_squared_deficit": {"lower": ratio(F(lo2, M*PRECISION)), "upper": ratio(F(hi2, M*PRECISION))}})
    print("Fourteen exact enclosed deficit bands passed.", flush=True)
    return rows


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT/name).read_text())
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, build = fresh_build()
    counts = Counter()
    data, paths, passages = finite_paths(counts)
    couplings = finite_couplings(paths, passages, counts)
    bands = certified_bands(data, counts)
    replay = {"scope": "Exact finite rational computations; all sampled trajectories independently reached one.",
              "global_minimum_scope": "No unknown orbit minimum is inferred from finite fuel.",
              "counts": dict(counts), "couplings": couplings, "finite_bands": bands}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [SOURCE, Path(__file__).name, "verify_prearrival_deficit_transfer.py",
             "docs/DEFICIT-LIMIT-LAW.md", "docs/PREARRIVAL-DEFICIT-TRANSFER.md",
             "docs/CLOCKED-MINIMUM.md", "docs/FINITE-PATH-PACKING.md",
             "docs/NATURAL-DENSITY-ALMOST-BOUNDED.md", *PRIOR,
             "results/deficit-limit-law/replay.json", build["log"]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": [build],
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "kernel_scope": ["Rational finite-list deficit concatenation, scaling, range and prefix bounds.",
                               "Nonnegative splice increments, common-tail and terminal-weight comparisons.",
                               "Finite telescoping of deficit differences and clock inequalities."],
              "written_scope": ["Joint limiting law of global minimum, deficit to first minimum, and terminal weight under uniform integer sampling.",
                                "Uniform tightness on all integer bands; restriction to the known basin yields lifetime-deficit tightness.",
                                "Uniform tightness of prearrival cost on pairs whose child 3n+2 is known to converge."],
              "analytic_dependencies": ["Local WRITTEN natural first-passage stabilization; not a published natural-density theorem of Tao.",
                                        "Early marginal passage-clock bound from local valuation estimates.",
                                        "Local WRITTEN finite simple-path packing and its reciprocal tail bound.",
                                        "Finite-marginal gluing, geometric scale sums, tightness and weak convergence; these are written."],
              "external_scope": "Tao arXiv:1909.03562v7 was reread as a primary source. No new external Lean build or source archive audit.",
              "floating_scope": "None in verification decisions. A separate terminal floating scout below 2^26 is recorded only in the written note and memory.",
              "not_proved": ["Kernel verification of the infinite analytic statements or their analytic premises.",
                             "A uniform first moment, uniform integrability, pointwise bounded deficit or a numerical limiting mean.",
                             "An effective bound on finite-population minimum clocks T_B.",
                             "A mean bound for prearrival cost, the negative arrival advance, postarrival reversed drift, or criterion Q.",
                             "Exclusion of escape or other cycles, or universal Collatz convergence."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
