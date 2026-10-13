"""Replay exact finite loss accounting for the ordinary Collatz map.

The natural-density, total-variation, and infinite-product conclusions are
written mathematics, with dependencies stated in the companion note. No
finite sample is used as an asymptotic error certificate.
"""

from collections import Counter, defaultdict
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/weighted-dissipation'
SOURCE = 'lean/WeightedDissipation.lean'
THEOREMS = [
    'conservation', 'numerator_positive', 'denominator_positive',
    'numerator_le_denominator', 'numerator_add', 'denominator_add',
    'loss_add', 'loss_zero_iff', 'loss_positive_of_odd_visit',
    'positive_return_has_odd', 'cycle_loss_positive', 'cycle_weight_strict',
    'affine_product', 'cycle_slope_weight', 'repeated_return',
    'cycle_numerator_power', 'cycle_denominator_power', 'known_cycle_weights',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(value):
    return [value.numerator, value.denominator]


def ordinary(n):
    return 3 * n + 1 if n % 2 else n // 2


def path_to_one(n):
    path, seen = [], set()
    while n != 1:
        assert n not in seen, ('unexpected cycle', n)
        seen.add(n)
        path.append(n)
        n = ordinary(n)
        assert len(path) < 100000, 'unresolved path, not a divergence certificate'
    path.append(1)
    return path


def reverse_certificate(states):
    """The first-step recursion used in Lean, evaluated independently."""
    a, b, loss = 1, 1, 0
    for n in reversed(states):
        if n % 2:
            a, b, loss = 3 * n * a, (3 * n + 1) * b, b + 3 * n * loss
    return a, b, loss


def tv(p, q):
    return sum((abs(p.get(n, 0) - q.get(n, 0)) for n in p.keys() | q.keys()),
               Fraction()) / 2


def finite_checks():
    totals = Counter()
    paths, weights, laws = {}, {}, {}
    for n in range(1, 2049):
        path = path_to_one(n)
        paths[n] = path
        w, lost, odd, even = Fraction(1), Fraction(), 0, 0
        a, b, loss_integer = 1, 1, 0
        law = defaultdict(Fraction)
        prefix = [w]
        for j, x in enumerate(path[:-1]):
            if x % 2:
                increment = w / (3 * x + 1)
                law[x] += increment
                lost += increment
                w *= Fraction(3 * x, 3 * x + 1)
                a, b, loss_integer = (3 * x * a, (3 * x + 1) * b,
                                      (3 * x + 1) * loss_integer + a)
                odd += 1
            else:
                even += 1
            assert ordinary(x) == path[j + 1]
            assert a + loss_integer == b
            assert w == Fraction(a, b) == Fraction(n * 3 ** odd, 2 ** even * path[j + 1])
            assert lost == Fraction(loss_integer, b) == 1 - w
            prefix.append(w)
            totals['exact_forward_prefix_checks'] += 1
            if n <= 128 and (j < 8 or j + 1 == len(path) - 1):
                assert reverse_certificate(path[:j + 1]) == (a, b, loss_integer)
                totals['independent_reverse_integer_certificates'] += 1
        assert path[-1] == 1
        law[1] += w  # All remaining loss is at the known odd cycle state.
        assert sum(law.values(), Fraction()) == 1
        assert law[1] == w == prefix[-1]
        weights[n], laws[n] = prefix, dict(law)
        totals['complete_known_cycle_source_laws'] += 1

    # Exact concatenation and repeated-cycle checks, retaining multiplicity.
    for n in range(1, 257):
        path, pref = paths[n], weights[n]
        for s in sorted({0, 1, len(path) // 2, len(path) - 1}):
            s = min(s, len(path) - 1)
            a, b, loss = reverse_certificate(path[:s])
            aa, bb, ll = reverse_certificate(path[s:-1])
            af, bf, lf = reverse_certificate(path[:-1])
            assert (af, bf) == (a * aa, b * bb)
            assert lf == loss * bb + a * ll
            assert pref[-1] == pref[s] * Fraction(aa, bb)
            totals['exact_concatenation_checks'] += 1
        w_entry = pref[-1]
        for cycles in range(17):
            states = path[:-1] + [1, 4, 2] * cycles
            a, b, loss = reverse_certificate(states)
            assert Fraction(a, b) == w_entry * Fraction(3, 4) ** cycles
            assert Fraction(loss, b) == 1 - w_entry * Fraction(3, 4) ** cycles
            assert w_entry * sum((Fraction(3, 4) ** j / 4 for j in range(cycles)),
                                 Fraction()) == w_entry * (1 - Fraction(3, 4) ** cycles)
            totals['known_cycle_geometric_checks'] += 1

    # Check the full measure cocycle and its TV inequality exactly.
    passage_rows = []
    for h in (1, 7, 31, 127, 511):
        maximum = Fraction()
        cases = 0
        for n in range(1, 1025):
            path, pref = paths[n], weights[n]
            i = next(j for j, x in enumerate(path) if x % 2 and x <= h)
            landing = path[i]
            assert all(x > h for x in path[:i] if x % 2)
            zeta = defaultdict(Fraction)
            for j, x in enumerate(path[:i]):
                if x % 2:
                    zeta[x] += pref[j] / (3 * x + 1)
            for x in laws[n].keys() | laws[landing].keys() | zeta.keys():
                assert laws[n].get(x, 0) == zeta.get(x, 0) + pref[i] * laws[landing].get(x, 0)
                totals['measure_cocycle_coordinate_checks'] += 1
            dist = tv(laws[n], laws[landing])
            loss = 1 - pref[i]
            reciprocal = sum((Fraction(1, 3 * x + 1) for x in path[:i] if x % 2), Fraction())
            assert dist <= loss <= reciprocal
            assert sum(zeta.values(), Fraction()) == loss
            maximum = max(maximum, dist)
            cases += 1
            totals['passage_tv_and_product_checks'] += 1
        passage_rows.append({'floor': h, 'sources': cases, 'largest_exact_tv': ratio(maximum)})

    # Coordinate averaging, including the cycle factor B_1=4.
    coordinate_rows = []
    for cutoff in (32, 128, 512, 2048):
        charges, first = defaultdict(Fraction), defaultdict(Fraction)
        for n in range(1, cutoff + 1):
            for x, value in laws[n].items():
                charges[x] += value / cutoff
            for j, x in enumerate(paths[n]):
                if x % 2:
                    first[x] += weights[n][j] / cutoff
        for x, value in charges.items():
            factor = 4 if x == 1 else 1
            assert value == factor * first[x] / (3 * x + 1)
            totals['finite_first_hit_charge_coordinates'] += 1
        assert sum(charges.values(), Fraction()) == 1
        cut_rows = []
        for r in (1, 7, 31, 127, 511, 2047, 8191):
            low = sum((v for x, v in charges.items() if x <= r), Fraction())
            high = sum((v for x, v in charges.items() if x > r), Fraction())
            assert low + high == 1
            cut_rows.append({'odd_target_cutoff': r, 'charge_through_cutoff': ratio(low),
                             'charge_above_cutoff': ratio(high)})
            totals['exact_finite_charge_partitions'] += 1
        coordinate_rows.append({'source_cutoff': cutoff, 'odd_target_support': len(charges),
                                'charge_at_one': ratio(charges[1]), 'partitions': cut_rows})

    return {'scope': 'Exact finite rational identities and complete paths into 1,4,2; no density limit inferred.',
            'counts': dict(totals), 'passage_rows': passage_rows,
            'finite_charge_means': coordinate_rows}


def clock_checks():
    """Certified rational intervals for finite means, not asymptotic bounds."""
    jmax = 16
    log_low = 2 * sum((Fraction(1, (2 * j + 1) * 3 ** (2 * j + 1))
                       for j in range(jmax)), Fraction())
    remainder = Fraction(2, (2 * jmax + 1) * 3 ** (2 * jmax + 1)) / (1 - Fraction(1, 9))
    log_high = log_low + remainder
    scale = 1 << 48
    rows, checked, clock_pairs = [], 0, 0
    for exponent in (6, 8, 10, 12, 14, 16):
        cutoff = 1 << exponent
        clocks = {}
        for coefficient in (0, 4, 8, 11, 16):
            lo = coefficient * exponent * log_low
            hi = coefficient * exponent * log_high
            t = lo.numerator // lo.denominator
            assert t == hi.numerator // hi.denominator
            clocks[t] = coefficient
        sums = {t: 0 for t in clocks}
        positive_remainders = {t: 0 for t in clocks}
        maximum = max(clocks)
        pow3 = [3 ** j for j in range(maximum + 1)]
        for n in range(1, cutoff + 1):
            x, odd = n, 0
            direct = Fraction(1) if n <= 64 else None
            for t in range(maximum + 1):
                if t in clocks:
                    a, b = n * pow3[odd], (1 << (t - odd)) * x
                    assert 0 < a <= b
                    if direct is not None:
                        assert Fraction(a, b) == direct
                        checked += 1
                    q, remainder_int = divmod(scale * a, b)
                    sums[t] += q
                    positive_remainders[t] += bool(remainder_int)
                    clock_pairs += 1
                if t < maximum:
                    if x % 2:
                        if direct is not None:
                            direct *= Fraction(3 * x, 3 * x + 1)
                        odd += 1
                    x = ordinary(x)
        for t, coefficient in sorted(clocks.items()):
            lo = Fraction(sums[t], cutoff * scale)
            hi = Fraction(sums[t] + positive_remainders[t], cutoff * scale)
            assert 0 <= lo <= hi <= 1 and hi - lo <= Fraction(1, scale)
            rows.append({'source_cutoff': cutoff, 'ordinary_clock': t,
                         'logarithmic_coefficient': coefficient,
                         'mean_weight_lower': ratio(lo), 'mean_weight_upper': ratio(hi),
                         'mean_weight_decimal_for_orientation': float((lo + hi) / 2)})
        print('Finite clock population passed:', cutoff, flush=True)
    return {'scope': 'Finite ordinary clocks only; exact integer enclosures with width at most 2^-48.',
            'log_two_interval': {'lower': ratio(log_low), 'upper': ratio(log_high),
                                 'basis': 'Positive atanh series and a geometric bound on its remaining terms.'},
            'direct_fraction_clock_comparisons': checked,
            'source_clock_pairs': clock_pairs, 'rows': rows}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-weighted-dissipation-') as directory:
        build = Path(directory)
        for source in ('CollatzContradiction.lean', SOURCE):
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            command = ['lean', '-o', str(obj), source]
            started = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT,
                                  env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(proc.stdout)
            assert proc.returncode == 0, proc.stdout
            assert not any(s in proc.stdout for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                found = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   proc.stdout, re.M)
                assert len(found) == len(THEOREMS)
                assert {name for name, _ in found} == {'WeightedDissipation.' + t for t in THEOREMS}
                for name, axioms in found:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': proc.returncode,
                           'elapsed_seconds': round(time.monotonic() - started, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Lean passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = ['results/finite-path-packing/verification.json',
             'results/clocked-minimum/verification.json',
             'results/density-to-pointwise/written-review.json']
    prior_counts = {}
    for record in prior:
        data = json.loads((ROOT / record).read_text())
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (record, path)
        prior_counts[record] = len(data['sha256'])
    version, builds = build_lean()
    finite = finite_checks()
    print('Exact path and measure checks passed:', finite['counts'], flush=True)
    clocks = clock_checks()
    replay = {'finite_path_checks': finite, 'finite_clock_checks': clocks}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = ['CollatzContradiction.lean', SOURCE, Path(__file__).name,
             'docs/WEIGHTED-DISSIPATION.md', 'docs/FINITE-PATH-PACKING.md',
             'docs/NATURAL-DENSITY-ALMOST-BOUNDED.md', 'docs/DENSITY-TO-POINTWISE.md',
             'docs/CLOCKED-MINIMUM.md', 'results/predecessor-density-review/verification.json',
             *prior, 'results/weighted-dissipation/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'map_scope': 'Actual ordinary positive-integer Collatz.',
        'lean_version': version, 'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': prior_counts,
        'kernel_scope': ['Integer finite loss conservation and concatenation.',
                         'Exact affine weight identity using odd and even ordinary step factors.',
                         'Positive loss on every positive return and geometric cycle repetition.'],
        'written_scope': ['Using prior written packing, the infinite weight is positive exactly on divergent orbits.',
                          'Conditional on prior written passage mixing, complete loss laws converge in total variation for natural source averages.',
                          'Their mass at infinity is d, and d plus the cycle-corrected first-hit charge series is one.',
                          'External PLD makes d=0 equivalent to universal eventual periodicity; this premise remains unproved.',
                          'Under the prior written clock theorem, finite mean weight at c log X tends to one below 3/log(4/3) and d above it.'],
        'python_scope': replay,
        'external_source_review': {
            'url': 'https://raw.githubusercontent.com/x1xhlol/collatz-two-coordinate-obstruction/main/paper/tao-basin-densities.tex',
            'scope': 'Read as related work only. No new external theorem, uniform reciprocal bound, or public Lean audit is adopted.'},
        'not_proved': ['d=0 or equality of the finite-target charge series to one.',
                       'Any effective asymptotic error bound at the sampled source or clock cutoffs.',
                       'Exclusion of additional positive cycles or proof/disproof of full Collatz.'],
        'sha256': {str(path): digest(ROOT / path) for path in files},
    }
    external_path = Path('/tmp/collatz-tao-basin-densities.tex')
    if external_path.exists():
        record['external_source_review']['downloaded_source_sha256'] = digest(external_path)
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: weighted dissipation; Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
