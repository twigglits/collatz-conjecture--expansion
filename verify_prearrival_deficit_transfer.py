"""Finite exact replay for the written prearrival/lifetime-deficit transfer.

No universal convergence, uniform lifetime deficit or averaged drift bound
is inferred. Every finite arrival used here is actually certified.
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

from verify_signed_arrival_windows import SOURCES as SIGNED_SOURCES

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/prearrival-deficit-transfer"
SOURCE = "lean/PrearrivalDeficitTransfer.lean"
SOURCES = [*SIGNED_SOURCES, "lean/OrderedWeightDrift.lean", "lean/ReversalPersistence.lean", SOURCE]
THEOREMS = ["lifted_one_multiple", "clone_common_clock", "clone_seed_equation",
            "clone_shell", "clone_current_reversal", "large_endpoint_no_arrival",
            "unit_doubling_to_one", "first_arrival_ten", "ten_window",
            "clone_retained_seven_eighths", "halving_clock_bound",
            "odd_output_unit", "positive_hits_unit"]
PRIOR = ["results/signed-arrival-windows/verification.json",
         "results/reversal-persistence/verification.json"]
PRECISION = 1 << 96


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    x = F(x)
    return [x.numerator, x.denominator]


def enclose(x):
    x = F(x)
    lo, rem = divmod(x.numerator*PRECISION, x.denominator)
    return {"lower": ratio(F(lo, PRECISION)), "upper": ratio(F(lo+bool(rem), PRECISION))}


def exact_large_summary(x):
    """Keep exact checks reproducible without printing 48000-bit fractions."""
    x = F(x)
    def integer_hash(n):
        assert n >= 0
        return hashlib.sha256(n.to_bytes(max(1, (n.bit_length()+7)//8), "big")).hexdigest()
    return {"enclosure": enclose(x), "numerator_bits": x.numerator.bit_length(),
            "denominator_bits": x.denominator.bit_length(),
            "numerator_unsigned_big_endian_sha256": integer_hash(x.numerator),
            "denominator_unsigned_big_endian_sha256": integer_hash(x.denominator)}


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct_arrival(n, counts, weights=False):
    x, t, a, peak, seen = n, 0, 0, n, set()
    w, deficit, history = F(1), F(0), []
    while x != 1:
        assert x not in seen, ("Unexpected cycle", n, x)
        assert t < 100000, "Unresolved fuel limit; not a divergence certificate."
        seen.add(x)
        if weights:
            history.append(w)
            deficit += 1-w
            assert 6*(t+1) <= 20*n*deficit+3*n
            counts["finite_prefix_deficit_clock_bounds"] += 1
            if x & 1:
                w *= F(3*x, 3*x+1)
        a += x & 1
        x, t = step(x), t+1
        peak = max(peak, x)
    if weights:
        assert w == F(n*3**a, 1 << t)
    counts["independent_first_arrival_steps"] += t
    counts["independent_first_arrivals"] += 1
    return {"clock": t, "odd_count": a, "peak_bits": peak.bit_length(),
            "deficit": deficit, "weights": history}


class Deficits:
    def __init__(self, counts):
        self.memo = {1: (0, F(0))}
        self.counts = counts

    def get(self, n):
        x, trail, seen = n, [], set()
        while x not in self.memo:
            assert x not in seen, ("Unexpected cycle", n, x)
            assert len(trail) < 100000, "Unresolved source, not a divergence certificate."
            seen.add(x)
            trail.append(x)
            x = step(x)
        t, d = self.memo[x]
        for x in reversed(trail):
            if x & 1:
                d = (3*x*d+t)/(3*x+1)
            t += 1
            self.memo[x] = (t, d)
            self.counts["certified_deficit_recursion_links"] += 1
        return self.memo[n]


def prearrival(n, counts, clone=None):
    k, M = n.bit_length()-1, 1 << (n.bit_length()-1)
    q, x, y, a, b, t = 3*n+2, n, 3*n+2, 0, 1, 0
    A, B, H = F(M, n), F(3*M, q), F(0)
    reversed_history, initial_budget, prefix_costs = False, None, {}
    while True:
        reversed_history |= a > b
        assert A == F(M*3**a, (1 << t)*x)
        assert B == F(M*3**b, (1 << t)*y)
        if t == k:
            initial_budget = 3*A+2*A*x/(x+1)
        if clone and t >= k:
            prefix_costs[t-clone["T"]] = H
        if x == 1 or y == 1:
            assert t >= k
            break
        if clone and t == clone["T"]:
            assert (x, a, y, b) == (clone["X"], clone["a"]+2, clone["v"], 2)
            counts["direct_clone_endpoint_identities"] += 1
        if t >= k:
            if clone and clone["a"] >= clone["tau"]:
                assert x > 1 and a > b and reversed_history
                counts["clone_current_reversal_terms"] += 1
            if reversed_history and A > B:
                H += A*(A-B)
            counts["exact_prearrival_cost_terms"] += 1
        if x & 1:
            A *= F(3*x, 3*x+1)
        if y & 1:
            B *= F(3*y, 3*y+1)
        a, b = a+(x & 1), b+(y & 1)
        x, y, t = step(x), step(y), t+1
        assert t < 100000, "Unresolved finite prefix."
    end_budget = 3*A+2*A*x/(x+1)
    assert initial_budget is not None and initial_budget >= end_budget
    return {"H": H, "budget": initial_budget, "window_loss": initial_budget-end_budget,
            "stop": t, "parent_endpoint": x, "child_endpoint": y, "level": k,
            "prefix_costs": prefix_costs}


def finite_deficits(counts, data):
    samples = []
    for n in range(1, (1 << 14)+1):
        t, d = data.get(n)
        assert 6*t <= 20*n*d+3*n
        counts["finite_lifetime_clock_bounds"] += 1
        if n <= 1024 or n in (6171, 10971, 16384):
            direct = direct_arrival(n, counts, weights=True)
            assert (t, d) == (direct["clock"], direct["deficit"])
            counts["independent_deficit_sum_checks"] += 1
        if n <= 8192:
            assert data.get(2*n) == (t+1, d)
            counts["exact_doubling_deficits"] += 1
        if n > 1 and n & 1:
            tu, du = data.get(step(n))
            assert (3*n+1)*d == 3*n*du+tu and t == tu+1
            assert t <= (3*n+1)*d+1
            counts["exact_odd_deficit_and_clock_identities"] += 1
        if n <= 4096 and n % 3:
            e = next(e for e in range(6) if (2**e*n) % 9 == 1)
            assert data.get(2**e*n) == (t+e, d)
            counts["exact_unit_doubling_transfers"] += 1
    old = json.loads((ROOT/"results/signed-arrival-windows/replay.json").read_text())["finite_signed_bands"]["rows"]
    band_totals = [[0, 0] for _ in range(12)]
    for n in range(1, 1 << 12):
        q = 3*n+2
        tq, dq = data.get(q)
        cell = prearrival(n, counts)
        assert cell["stop"] <= tq
        assert cell["H"] <= dq+F(2*tq, q) <= F(23, 3)*dq+1
        counts["finite_one_trajectory_upper_bounds"] += 1
        lo, rem = divmod(cell["H"].numerator*PRECISION, cell["H"].denominator)
        band_totals[cell["level"]][0] += lo
        band_totals[cell["level"]][1] += lo+bool(rem)
    for k, (lo, hi) in enumerate(band_totals):
        previous = old[k]["unhalved_mean_costs"]["before_both_arrivals"]
        assert F(lo, (1 << k)*PRECISION) <= F(*previous["upper"])
        assert F(*previous["lower"]) <= F(hi, (1 << k)*PRECISION)
        counts["authenticated_prearrival_band_comparisons"] += 1
    for n in (1, 5, 7, 10, 27, 55, 82, 109, 597484, 1021741, 4086964):
        t, d = data.get(n)
        direct = direct_arrival(n, counts, weights=True)
        assert (t, d) == (direct["clock"], direct["deficit"])
        counts["independent_deficit_sum_checks"] += 1
        samples.append({"source": n, "first_arrival": t, "exact_deficit": ratio(d)})
    assert data.get(10) == (5, F(3, 16))
    print("Finite deficit recurrences and prearrival upper bounds passed.", flush=True)
    return {"clock_bound_source_maximum": 1 << 14,
            "upper_bound_parent_interval": [1, 1 << 12], "samples": samples}


def clone_replays(counts, data):
    cases = {(10, j) for j in (2, 3, 4, 8, 16, 32, 64, 128)}
    for v in (10, 19, 28, 37, 55, 82, 109, 597484, 4086964):
        tau, _ = data.get(v)
        j = max(64, (tau+3)//3)
        cases.add((v, j))
        cases.add((v, j+2))
    rows = []
    for v, j in sorted(cases):
        assert v > 1 and v % 9 == 1
        tau, deficit = data.get(v)
        path = direct_arrival(v, counts, weights=True)
        ell = (8*v//9).bit_length()-1
        assert ell >= 3 and 9*(1 << ell) <= 8*v < 9*(1 << (ell+1))
        h0 = ell-3
        assert h0 < tau
        prefix = sum((1-w for w in path["weights"][:h0]), F(0))
        assert prefix < F(1, 27)
        counts["exact_omitted_prefix_bounds"] += 1
        bv = F(9*(1 << ell), 8*v)
        assert F(1, 2) < bv <= 1
        a, T = 3*j-1, 6*j+3
        X = 3**a*v+1
        n = 8*(64**j*v-1)//9
        assert 9*(n//8)+1 == 64**j*v
        assert n.bit_length()-1 == 6*j+ell
        assert a >= tau and X > (1 << tau)
        cell = prearrival(n, counts, {"T": T, "X": X, "v": v, "a": a, "tau": tau})
        assert cell["stop"] == T+tau and cell["child_endpoint"] == 1
        assert cell["parent_endpoint"] > 1
        limit = bv*bv*(deficit-prefix)
        error = F(2, 3)*bv*bv*((1 << tau)+2*tau)/X
        assert 0 <= limit-cell["H"] <= error
        counts["exact_clone_limit_error_bounds"] += 1
        partial = F(0)
        for L in range(h0, tau+1):
            if L > h0:
                partial += 1-path["weights"][L-1]
            partial_limit = bv*bv*partial
            partial_error = F(2, 3)*bv*bv*((1 << L)+2*L)/X
            assert 0 <= partial_limit-cell["prefix_costs"][L] <= partial_error
            counts["exact_finite_prefix_clone_error_bounds"] += 1
        # This finite convergence replay is independent of the transfer theorem,
        # which does not assume the parent's eventual convergence.
        parent = direct_arrival(n, counts)
        other = direct_arrival(3*n+2, counts)
        assert other["clock"] == T+tau and parent["clock"] > other["clock"]
        record = {"target": v, "j": j, "source": str(n), "source_bits": n.bit_length(),
                  "level": cell["level"], "clone_clock": T, "target_arrival": tau,
                  "parent_first_arrival": parent["clock"], "child_first_arrival": other["clock"],
                  "parent_peak_bits": parent["peak_bits"], "exact_target_deficit": ratio(deficit),
                  "omitted_prefix_deficit": ratio(prefix), "normalization": ratio(bv),
                  "H": exact_large_summary(cell["H"]), "parent_complete_loss_cap": enclose(cell["budget"]),
                  "prearrival_parent_loss": enclose(cell["window_loss"]),
                  "limiting_prearrival_cost": ratio(limit), "limit_error_upper_bound": ratio(error)}
        if v == 10:
            R = 3**a
            assert limit == F(243, 1600)
            assert cell["H"] >= F(21, 256)
            assert 0 < cell["window_loss"] <= F(93, X)
            assert cell["H"] / cell["window_loss"] >= F(7*X, 7936)
            counts["finite_small_suffix_loss_obstructions"] += 1
            record["prearrival_charge_ratio"] = enclose(cell["H"]/cell["window_loss"])
            record["analytic_prearrival_loss_upper_bound"] = ratio(F(93, X))
        if (v, j) == (597484, 64):
            assert n.bit_length() == 404 and cell["level"] == 403
            assert parent["clock"] == 1863 and other["clock"] == 538
            assert cell["H"] > cell["budget"]+F(1, 200)
            record["complete_budget_failure_margin"] = enclose(cell["H"]-cell["budget"])
            counts["exact_complete_future_charge_counterexamples"] += 1
        rows.append(record)
        print("Exact clone passed:", v, j, "parent bits:", n.bit_length(), flush=True)
    assert counts["exact_complete_future_charge_counterexamples"] == 1
    return {"rows": rows, "scope": "Finite clone and arrival checks. The all-j loss obstruction and supremum equivalence are written arguments using the kernel inputs."}


def build():
    version = subprocess.check_output(["lean", "--version"], cwd=ROOT, text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-deficit-transfer-") as directory:
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
            assert not any(s in result.stdout for s in ("error:", "warning:", "sorryAx", "ofReduceBool"))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert {name for name, _ in roots} == {"PrearrivalDeficitTransfer."+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}, name
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
    validated = {}
    for name in PRIOR:
        record = json.loads((ROOT/name).read_text())
        assert record["status"] == "passed"
        for path, expected in record["sha256"].items():
            assert digest(ROOT/path) == expected, (name, path)
        validated[name] = len(record["sha256"])
    version, builds = build()
    counts = Counter()
    data = Deficits(counts)
    deficits = finite_deficits(counts, data)
    clones = clone_replays(counts, data)
    replay = {"finite_deficits": deficits, "clones": clones, "counts": dict(counts),
              "infinite_scope": "None in the finite replay. The all-parameter transfer and loss obstruction are written arguments."}
    (OUT/"replay.json").write_text(json.dumps(replay, indent=2)+"\n")
    files = [*SOURCES, Path(__file__).name, "verify_signed_arrival_windows.py",
             "verify_gradient_clock_obstruction.py", "verify_known_basin_nonfusion_trace.py",
             "verify_dyadic_coalescence_defects.py", "verify_annulus_time_budgets.py",
             "docs/PREARRIVAL-DEFICIT-TRANSFER.md", "docs/SIGNED-ARRIVAL-WINDOWS.md",
             "docs/REVERSAL-PERSISTENCE.md", *PRIOR,
             "results/signed-arrival-windows/replay.json", "results/prearrival-deficit-transfer/replay.json",
             *[b["log"] for b in builds]]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version,
              "kernel_theorems_audited": len(THEOREMS), "builds": builds,
              "prior_hashes_validated": validated, "finite_scope": dict(counts),
              "floating_scope": "None in verification decisions.",
              "kernel_scope": ["Parametric affine clone endpoints, counts, seeds and source bands.",
                               "Current count reversal and finite no-arrival conditions at large endpoints.",
                               "Doubling a unit into one modulo nine and finite halving clock comparison.",
                               "The five-step target-ten suffix and a uniform parent-retention lower bound.",
                               "Every positive orbit reaches a unit modulo three, without assuming convergence."],
              "written_scope": ["Exact lifetime-deficit recursion and its linear-clock implication.",
                                "Uniform pointwise prearrival cost is equivalent to uniform lifetime deficit on the known unit basin, with explicit constants.",
                                "The unrestricted finite-prefix prearrival supremum is finite exactly when universal convergence and a uniform known-unit lifetime deficit both hold; neither condition is proved.",
                                "An infinite affine family has positive prearrival cost but vanishing parent losses during that interval.",
                                "A finite 404-bit convergent witness exceeds the complete future parent-loss budget with multiplier one."],
              "external_scope": "None. No external analytic theorem, packing hypothesis or universal convergence premise is used.",
              "not_proved": ["Finiteness or infinitude of either supremum D_star or H_star.",
                             "Uniform pointwise or averaged prearrival bounds.",
                             "Failure of every multiplier when all future parent losses are available for prearrival cost.",
                             "Universal convergence of the constructed parent family.",
                             "Reversed drift, Q, escape exclusion, additional-cycle exclusion or full Collatz."],
              "sha256": {str(p): digest(ROOT/p) for p in files}}
    (OUT/"verification.json").write_text(json.dumps(record, indent=2)+"\n")
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "finite_counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
