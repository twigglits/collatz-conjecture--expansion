"""Finite support for the WRITTEN clocked progression-mixing argument.

Checks exact residue/seed laws, finite conditional pair convolutions,
and all-cutoff transfer on actual matched ordinary-clock landings.
No finite check here certifies asymptotic Fourier decay, mixing, or Collatz.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/clocked-progression-mixing"
SOURCES = ["lean/DeficitLimitLaw.lean", "lean/DeficitClockMoment.lean",
           "lean/ClockedProgressionMixing.lean"]
THEOREMS = ["preimage_residue_transfer", "seed_one_cleared", "seed_two_cleared",
            "prepend_affine_offset", "matched_window_interval", "matched_window_pair",
            "matched_alive_cell", "weighted_error_sum", "coupling_mean_error",
            "neutral_bulk_balance"]
PRIOR = "results/censored-progression-transport/verification.json"


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(value):
    return [value.numerator, value.denominator]


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def affine(word):
    """2^s * Aff_word(u) = 3^len(word) * u + b, computed integrally."""
    s, b, power = 0, 0, 1
    for a in word:
        b = 3 * b + (1 << s)
        s += a
        power *= 3
    return power, s, b


def offset_mod(word, modulus):
    """Independent modular composition of x -> (3x+1)/2^a, from x=0."""
    x = 0
    for a in word:
        x = (3 * x + 1) * pow(2, -a, modulus) % modulus
    return x


def reverse_mod(word, modulus):
    s, result = 0, 0
    for i, a in enumerate(word):
        s += a
        result = (result + 3 ** i * pow(2, -s, modulus)) % modulus
    return result


def seed_checks(counts):
    rows = []
    limit = 5
    for n in range(1, 7):
        modulus, low = 3 ** (n + 1), 3 ** min(2, n)
        scale = 1 << (limit * n)
        laws = {r: defaultdict(Counter) for r in (0, 1, 2)}
        for word in product(range(1, limit + 1), repeat=n):
            p, s, b = affine(word)
            f = offset_mod(word, modulus)
            assert f == b * pow(2, -s, modulus) % modulus
            assert f == reverse_mod(tuple(reversed(word)), modulus)
            counts["affine_modular_and_reversal_checks"] += 1
            weight = 1 << (limit * n - s)
            laws[0][s][f] += weight
            for r, c in ((1, 2), (2, 1)):
                seeded = (f + p * pow(2, -s, modulus) * r) % modulus
                augmented = offset_mod((c,) + word, modulus)
                assert seeded == augmented
                assert seeded % (3 ** n) == f % (3 ** n)
                laws[r][s][seeded] += weight
                counts["seeded_offset_and_low_marginal_checks"] += 1
            # A representative of every initial source class, odd and positive.
            for u in (1, 3, 5):
                z = p * u + b
                for r in (0, 1, 2):
                    assert ((z - b - p * r) % modulus == 0) == (u % 3 == r)
                    counts["cleared_inverse_congruence_checks"] += 1
        mass = F(sum(sum(v.values()) for v in laws[0].values()), scale)
        assert mass == F((1 << limit) - 1, 1 << limit) ** n
        oscillations = {}
        for r in (0, 1, 2):
            numerator = 0
            factor = modulus // low
            for s, full in laws[r].items():
                coarse = Counter()
                for residue, value in full.items():
                    coarse[residue % low] += value
                base = Counter()
                for residue, value in laws[0][s].items():
                    base[residue % low] += value
                assert coarse == base
                counts["exact_joint_low_marginal_checks"] += 1
                numerator += sum(abs(factor * full[y] - coarse[y % low]) for y in range(modulus))
            oscillations[str(r)] = ratio(F(numerator, factor * scale))
        rows.append({"random_word_length": n, "valuation_cutoff": limit,
                     "ambient_modulus": modulus, "smoothing_modulus": low,
                     "retained_mass": ratio(mass), "omitted_mass": ratio(1 - mass),
                     "truncated_joint_L1_oscillation": oscillations})
    return rows


def pair_convolutions(counts):
    """Exact conditional laws underlying the odd-length paired product.

    Given pair totals, all positive splits are equally likely. Counts
    avoid complex floating point; convolution is the Fourier factorization.
    """
    for pairs in range(1, 4):
        length = 2 * pairs + 1
        modulus = 3 ** length
        for totals in product(range(2, 6), repeat=pairs):
            for fixed in (1, 2):
                total_sum = sum(totals) + fixed
                direct = Counter()
                for splits in product(*(range(1, b) for b in totals)):
                    word = tuple(a for b, j in zip(totals, splits) for a in (b - j, j)) + (fixed,)
                    assert sum(word) == total_sum
                    direct[reverse_mod(word, modulus)] += 1
                law, cumulative = Counter({0: 1}), 0
                for j, b in enumerate(totals):
                    cumulative += b
                    coefficient = 3 ** (2 * j) * pow(2, -cumulative, modulus) % modulus
                    piece = Counter(coefficient * (2 ** a + 3) % modulus for a in range(1, b))
                    combined = Counter()
                    for u, wu in law.items():
                        for v, wv in piece.items():
                            combined[(u + v) % modulus] += wu * wv
                    law = combined
                last = 3 ** (length - 1) * pow(2, -total_sum, modulus) % modulus
                assert Counter({(u + last) % modulus: w for u, w in law.items()}) == direct
                counts["conditional_pair_convolution_identities"] += 1
                # For even length, remove its first coordinate; the fixed last
                # coordinate is then unpaired at the reduced odd length.
                for first in (1, 2, 3):
                    for splits in product(*(range(1, b) for b in totals)):
                        tail = tuple(a for b, j in zip(totals, splits) for a in (b - j, j)) + (fixed,)
                        ambient = 3 * modulus
                        left = reverse_mod((first,) + tail, ambient)
                        right = pow(2, -first, ambient) * (1 + 3 * reverse_mod(tail, modulus)) % ambient
                        assert left == right
                        counts["even_length_head_removal_checks"] += 1


def first_odd_passage(n, floor, counts, fuel=1024):
    state, clock, weight = n, 0, F(1)
    while state > floor or state % 2 == 0:
        assert clock < fuel, (n, floor, state)
        if state & 1:
            weight *= F(3 * state, 3 * state + 1)
            state = 3 * state + 1
        else:
            state //= 2
        clock += 1
        counts["ordinary_passage_steps"] += 1
    counts["independent_first_odd_passages"] += 1
    return (state, clock), weight


def prefix(n, horizon, counts):
    state, w, a = n, F(1), F()
    deficits, cells, hits = [], [], []
    for t in range(horizon + 1):
        hit = state == 1
        z = F() if hit else 1 - w
        deficits.append(a)
        cells.append(z)
        hits.append(hit)
        if t < horizon and not hit:
            a += z
            if state & 1:
                w *= F(3 * state, 3 * state + 1)
                state = 3 * state + 1
            else:
                state //= 2
            counts["bounded_prefix_weight_steps"] += 1
    counts["bounded_prefixes"] += 1
    return deficits, cells, hits


def tv(a, na, b, nb):
    return sum(abs(F(a[k], na) - F(b[k], nb)) for k in a.keys() | b.keys()) / 2


def passage_replay(counts):
    rows = []
    for y in (256, 1024, 4096):
        floor = y // 4
        groups, weights = defaultdict(list), {}
        whole, classes = Counter(), {r: Counter() for r in (0, 1, 2)}
        for n in range(y | 1, 2 * y, 2):
            mark, w = first_odd_passage(n, floor, counts)
            groups[mark].append(n)
            weights[n] = w
            whole[mark] += 1
            classes[n % 3][mark] += 1
        unmarked = Counter()
        for (landing, _), mass in whole.items():
            unmarked[landing] += mass
        tv_rows = {}
        for r in (1, 2):
            law = classes[r]
            reduced = Counter()
            for (landing, _), mass in law.items():
                reduced[landing] += mass
            marked_tv = tv(whole, sum(whole.values()), law, sum(law.values()))
            unmarked_tv = tv(unmarked, sum(unmarked.values()), reduced, sum(reduced.values()))
            assert 0 <= unmarked_tv <= marked_tv <= 1
            tv_rows[str(r)] = {"marked": ratio(marked_tv), "unmarked": ratio(unmarked_tv)}
        paired = 0
        for (landing, clock), sources in groups.items():
            left = next((n for n in sources if n % 3 == 2), None)
            right = next((n for n in sources if n % 3 != 2), None)
            if left is None or right is None:
                continue
            assert left != right
            epsilon = 1 - min(weights[left], weights[right])
            horizon = clock + 96
            a, z, hit = prefix(left, horizon, counts)
            b, zz, hh = prefix(right, horizon, counts)
            child, _, _ = prefix(landing, 96, counts)
            for t in range(horizon + 1):
                reference = F() if t < clock else child[t - clock]
                assert 0 <= a[t] - reference <= epsilon * t
                assert 0 <= b[t] - reference <= epsilon * t
                assert abs(a[t] - b[t]) <= epsilon * t
                assert abs(z[t] - zz[t]) <= epsilon
                assert hit[t] == hh[t]
                counts["matched_clock_all_cutoff_checks"] += 1
                counts["after_landing_checks" if t >= clock else "before_landing_checks"] += 1
                if t == clock:
                    counts["exact_landing_boundary_checks"] += 1
            counts["distinct_matched_clock_pairs"] += 1
            paired += 1
        rows.append({"odd_source_interval": [y, 2 * y], "floor": floor,
                     "sources": sum(whole.values()), "distinct_matched_pairs": paired,
                     "exact_finite_total_variation": tv_rows,
                     "scope": "Finite identities and exact finite laws only; these small scales are not an asymptotic rate test."})
    assert counts["distinct_matched_clock_pairs"] > 0
    return rows


def build():
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.33.1" in version and "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" in version
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-clocked-progression-") as directory:
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
            if source == SOURCES[-1]:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
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


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT / PRIOR).read_text())
    for path, expected in prior["sha256"].items():
        assert digest(ROOT / path) == expected, path
    version, builds = build()
    counts = Counter()
    seeds = seed_checks(counts)
    pair_convolutions(counts)
    passages = passage_replay(counts)
    save(OUT / "replay.json", {"status": "passed", "counts": dict(counts),
                              "seeded_finite_laws": seeds, "finite_passage_rows": passages})
    files = SOURCES + [Path(__file__).name, "docs/CLOCKED-PROGRESSION-MIXING.md",
        "docs/NATURAL-DENSITY-ALMOST-BOUNDED.md", "docs/CENSORED-PROGRESSION-TRANSPORT.md",
        "docs/WEIGHTED-DISSIPATION.md", "docs/FINITE-PATH-PACKING.md", PRIOR,
        "results/natural-density/verification.json"]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != "verification.json"]
    record = {"status": "passed", "verified_at_utc": datetime.now(timezone.utc).isoformat(),
              "collatz_status": "unresolved", "lean_version": version, "builds": builds,
              "kernel_theorems_audited": len(THEOREMS),
              "prior_hashes_validated": {PRIOR: len(prior["sha256"])},
              "finite_replay_counts": dict(counts),
              "kernel_scope": "Finite inverse residue and seed arithmetic, matched-clock window and cell bounds, finite coupling-mean inequalities, and neutral bulk algebra. No analytic decay or mixing theorem is kernel formalized.",
              "written_scope": ["Conditioning one endpoint valuation preserves the paired Fourier bound and joint fine-scale mixing.",
                  "Same-scale uniform source classes 1 and 2 modulo three have joint first-passage landing/ordinary-clock laws within O_R((log y)^(-R)), for every fixed R.",
                  "For every R, the progression deficit error is O_R(t/(log X)^R), uniformly over finite t; the analogous cell and survivor errors are O_R((log X)^(-R)).",
                  "At t=8k, X=2^k, the absolute deficit discrepancy tends to zero faster than any fixed inverse power of k."],
              "analytic_provenance": "Local WRITTEN extension of the joint-mixing and uniform-preimage portions of the natural-density note, using Tao's published Fourier-decay/collision and valuation inputs. The same-scale comparison does not use the renewal lemma or its irrationality input.",
              "external_source": {"url": "https://arxiv.org/html/1909.03562v7", "title": "Almost all orbits of the Collatz map attain almost bounded values", "author": "Terence Tao", "version_date": "2026-07-16", "rechecked_date": "2026-10-14", "sections": ["5", "6", "7.1"], "scope": "Published inputs and proof structure only; the new marked progression assertion is a local written deduction, not a theorem attributed to Tao."},
              "finite_scope_limit": "Exact arithmetic only. Truncated geometric laws retain and report their omitted mass. Finite convolutions and trajectory laws do not verify the asymptotic bound or provide effective constants. No fresh external Lean replay.",
              "not_proved": ["Effective values of the progression-error constants or thresholds.",
                  "Any O(t/X) error estimate.", "The all-source zero limit, b=0, escape or other-cycle exclusion, or full Collatz."],
              "sha256": {p: digest(ROOT / p) for p in files}}
    save(OUT / "verification.json", record)
    print(json.dumps({"status": "passed", "kernel_roots": len(THEOREMS), "counts": dict(counts)}, indent=2))


if __name__ == "__main__":
    main()
