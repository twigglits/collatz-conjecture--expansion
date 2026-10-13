"""Audit reflected coalescence and distinguish full periods from source prefixes.

The density conclusions remain written arguments. Finite population counts
are exact checks, not estimates of an uncomputed asymptotic density.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/prefix-coalescence'
SOURCE = 'lean/ReflectedCoalescence.lean'
THEOREMS = ['reflected_pair', 'reflected_residue', 'reflected_adjacent_coalescence',
            'minus_cycle_closed', 'minus_cycle_trapped', 'minus5_no_one', 'plus5_hits_one']
PUBLISHED_COUNTS = [0, 0, 1, 3, 8, 18, 39, 82, 170, 351, 721, 1476,
                    3012, 6130, 12450, 25241, 51105, 103358, 208840, 421643]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def plus(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def minus(n):
    return (3 * n - 1) // 2 if n & 1 else n // 2


def ordinary(n):
    return 3 * n + 1 if n & 1 else n // 2


def qjson(value):
    return [value.numerator, value.denominator]


def period_checks():
    depth = 20
    endpoint_plus = list(range((1 << depth) + 1))
    endpoint_minus = endpoint_plus.copy()
    weight_plus = [0] * len(endpoint_plus)
    weight_minus = [0] * len(endpoint_minus)
    counts = Counter()
    rows = []
    for k in range(1, depth + 1):
        for r, value in enumerate(endpoint_plus):
            if value & 1:
                endpoint_plus[r] = (3 * value + 1) // 2
                weight_plus[r] += 1
            else:
                endpoint_plus[r] = value // 2
        for r, value in enumerate(endpoint_minus):
            if value & 1:
                endpoint_minus[r] = (3 * value - 1) // 2
                weight_minus[r] += 1
            else:
                endpoint_minus[r] = value // 2
        period = 1 << k
        power_three = [3 ** j for j in range(k + 1)]
        for r in range(period + 1):
            reflected = period - r
            assert weight_minus[r] == weight_plus[reflected], (k, r)
            assert endpoint_minus[r] + endpoint_plus[reflected] == power_three[weight_minus[r]], (k, r)
            counts['reflected_weight_and_endpoint_identities'] += 1
        adjacent = 0
        for r in range(period):
            mirror = period - 1 - r
            good_plus = (endpoint_plus[r] == endpoint_plus[r + 1] and
                         weight_plus[r] == weight_plus[r + 1])
            good_minus = (endpoint_minus[mirror] == endpoint_minus[mirror + 1] and
                          weight_minus[mirror] == weight_minus[mirror + 1])
            assert good_plus == good_minus, (k, r)
            adjacent += good_plus
            counts['reflected_adjacent_mask_comparisons'] += 1
        assert adjacent == PUBLISHED_COUNTS[k - 1]
        if rows:
            assert adjacent >= 2 * rows[-1]['coalescing_adjacent_residues']
        terminal = sum(endpoint_plus[r] in (1, 2) for r in range(1, period + 1))
        rows.append({'shortcut_depth': k, 'period': period,
                     'coalescing_adjacent_residues': adjacent,
                     'coalescing_adjacent_proportion': qjson(Fraction(adjacent, period)),
                     'full_positive_period_cycle_sources': terminal,
                     'full_positive_period_cycle_proportion': qjson(Fraction(terminal, period))})
        print('Exact period passed:', k, 'adjacent classes:', adjacent, flush=True)
    assert [minus(n) for n in (5, 7, 10)] == [7, 10, 5]
    x = 5
    for _ in range(4):
        x = plus(x)
    assert x == 1
    decay = []
    for q in (0, 6, 12, 24, 48, 96):
        upper = Fraction(390 * 38 ** q, 64 ** q)
        assert upper == 390 * Fraction(19, 32) ** q
        if q >= 12:
            assert upper < 1
        decay.append({'q': q, 'shortcut_depth': 6 * q,
                      'written_full_period_upper_bound': qjson(upper)})
    return {'counts': dict(counts), 'periods': rows, 'decay_bound_arithmetic': decay,
            'minus_cycle': [5, 7, 10], 'plus5_first_one_time': 4,
            'published_sequence_comparison': 'https://oeis.org/A398792',
            'scope': 'Exhaustive finite arithmetic through depth 20; the all-depth reflection is separately kernel proved, and the decay limit is written.'}


def entry_times(step, terminal, cutoff):
    times = {n: 0 for n in terminal}
    for n in range(1, cutoff + 1):
        x, path, seen = n, [], set()
        while x not in times:
            assert x not in seen, ('unclassified cycle', n, x)
            assert len(path) < 100000, ('unresolved trajectory', n)
            seen.add(x)
            path.append(x)
            x = step(x)
        t = times[x]
        for x in reversed(path):
            t += 1
            times[x] = t
    for n, t in times.items():
        if n in terminal:
            assert t == 0
        else:
            assert t == 1 + times[step(n)], (n, t)
    # Direct full replay uses no previously computed hitting-time entry.
    direct_steps = 0
    for n in range(1, 4097):
        x, t = n, 0
        while x not in terminal:
            x = step(x)
            t += 1
            assert t < 100000
        assert t == times[n]
        direct_steps += t
    return times, {'source_cutoff': cutoff, 'certified_time_rows': len(times),
                   'direct_sources': 4096, 'direct_steps': direct_steps,
                   'maximum_time_on_initial_interval': max(times[n] for n in range(1, cutoff + 1))}


def prefix_checks():
    cutoff = 1 << 16
    raw, raw_scope = entry_times(ordinary, {1}, cutoff)
    shortcut, shortcut_scope = entry_times(plus, {1, 2}, cutoff)
    terms = 24
    low = 2 * sum((Fraction(1, (2 * j + 1) * 3 ** (2 * j + 1))
                   for j in range(terms)), Fraction())
    high = low + Fraction(9, 4 * (2 * terms + 1) * 3 ** (2 * terms + 1))
    assert Fraction(693, 1000) < low < high < Fraction(694, 1000)
    rows = []
    for j in range(4, 17):
        X = 1 << j
        lower_clock, upper_clock = 11 * j * low, 11 * j * high
        floor_clock = lower_clock.numerator // lower_clock.denominator
        assert floor_clock < lower_clock < upper_clock < floor_clock + 1
        ceil_clock = floor_clock + 1
        raw_good = sum(raw[n] <= floor_clock for n in range(1, X + 1))
        shortcut_good = sum(shortcut[n] <= ceil_clock for n in range(1, X + 1))
        assert raw_good <= shortcut_good
        for n in range(1, X + 1):
            if raw[n] <= floor_clock:
                assert shortcut[n] <= ceil_clock
        rows.append({'source_cutoff': X, 'ordinary_clock_floor_11_log_X': floor_clock,
                     'shortcut_clock_ceil_11_log_X': ceil_clock,
                     'ordinary_one_hits_within_clock': raw_good,
                     'shortcut_cycle_hits_within_clock': shortcut_good,
                     'source_fraction_of_shortcut_parity_period': qjson(Fraction(X, 1 << ceil_clock))})
    return {'ordinary_first_one': raw_scope, 'shortcut_first_cycle_entry': shortcut_scope,
            'log_two_enclosure': {'positive_series_terms': terms, 'lower': qjson(low), 'upper': qjson(high)},
            'populations': rows,
            'scope': 'Finite known-cycle populations only. No asymptotic density or error rate is inferred.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-reflected-coalescence-') as directory:
        build = Path(directory)
        for source in ['CollatzAffine.lean', SOURCE]:
            started = time.monotonic()
            obj = build / (Path(source).stem + '.olean')
            log = OUT / (Path(source).stem + '.log')
            command = ['lean', '-o', str(obj), source]
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(bad in result.stdout for bad in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            reports = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            assert reports
            for name, axioms in reports:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
                    'propext', 'Classical.choice', 'Quot.sound'}, name
            if source == SOURCE:
                assert len(reports) == len(THEOREMS)
                assert {name for name, _ in reports} == {'ReflectedCoalescence.' + t for t in THEOREMS}
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': result.returncode,
                           'fresh_build': True, 'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic() - started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Lean passed:', source, '(fresh)', flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = ['results/clocked-minimum/verification.json',
             'results/density-time-truncation/verification.json']
    prior_counts = {}
    for name in prior:
        data = json.loads((ROOT / name).read_text())
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (name, path)
        prior_counts[name] = len(data['sha256'])
    version, builds = build_lean()
    replay = {'complete_periods': period_checks(), 'initial_intervals': prefix_checks()}
    replay_path = OUT / 'replay.json'
    replay_path.write_text(json.dumps(replay, indent=2) + '\n')
    files = [SOURCE, 'CollatzAffine.lean', Path(__file__).name, 'docs/PREFIX-COALESCENCE-AUDIT.md',
             'docs/CLOCKED-MINIMUM.md', 'docs/DENSITY-TIME-TRUNCATION.md',
             'lean/DensityTimeTruncation.lean', *prior, str(replay_path.relative_to(ROOT)),
             *[b['log'] for b in builds]]
    record = {'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
              'new_kernel_theorems': len(THEOREMS), 'prior_hashes_validated': prior_counts,
              'kernel_scope': ['All-depth endpoint and odd-count reflection between the plus and minus shortcut maps.',
                               'Exact equivalence of reflected adjacent weighted coalescence residues.',
                               'The minus map has the cycle 5,7,10 and its start 5 never reaches 1; the plus start 5 reaches 1.'],
              'reused_kernel_input': 'The separately checked ordinary twelve-step bound of 38 predecessors and its all-depth extension.',
              'written_scope': ['The full-period shortcut-cycle proportion tends to zero; at depth 6q it is bounded by 390*(19/32)^q.',
                                'Under the prior written density and clock inputs, the initial-interval proportion at ceil(11 log X) tends instead to p_1.',
                                'Whole-period coalescence counts alone do not select the component of one or control that initial interval.'],
              'finite_scope': {'periods': replay['complete_periods']['counts'],
                               'ordinary_prefix': replay['initial_intervals']['ordinary_first_one'],
                               'shortcut_prefix': replay['initial_intervals']['shortcut_first_cycle_entry']},
              'primary_comparison': 'https://oeis.org/A398792',
              'not_proved': ['That p_1 equals one, absence of divergence, absence of nontrivial plus-map cycles, or full Collatz.',
                             'An asymptotic upper bound on the actual logarithmic-clock initial-interval failures.',
                             'That adjacent coalescence proportions tend to one.',
                             'Positive predecessor density or any component-density theorem for the minus map.'],
              'sha256': {name: digest(ROOT / name) for name in files}}
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': record['status'], 'new_kernel_theorems': len(THEOREMS),
                      'finite_scope': record['finite_scope'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
