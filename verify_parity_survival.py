"""Exact finite replay of survivor parity bounds and linear credit certificates.

The all-index implications are Lean theorems. No universal credit or
individual-orbit frequency estimate is inferred from these finite checks.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/parity-survival'
SOURCES = ('CollatzPacking.lean', 'CollatzContradiction.lean',
           'lean/FirstPassagePacking.lean', 'lean/FinitePathPacking.lean',
           'lean/EqualWeightFibres.lean', 'lean/CoalescenceGrades.lean',
           'lean/WeightedSurvivors.lean', 'lean/ParitySurvival.lean')


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def growth_checks(n, k, y, j, avoids_one, avoids64):
    assert n > 0 and y > 0
    b = (n - 1).bit_length()
    assert n <= 1 << b
    if avoids_one:
        assert 3 ** j * (1 << k) * y <= 10 ** j * n
        assert 4 * k <= 7 * j + 4 * b
    if avoids64:
        assert 65 ** j * (1 << k) * y <= 196 ** j * n
        assert 5 * k <= 8 * j + 5 * b


def build_lean():
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-parity-survival-') as build:
        for source in SOURCES:
            command = ['lean', '-o', str(Path(build) / (Path(source).stem + '.olean')), source]
            run = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                                 stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            log = OUT / (Path(source).stem + '.log')
            log.write_text(run.stdout)
            assert run.returncode == 0, run.stdout
            assert not any(s in run.stdout for s in ('sorryAx', 'ofReduceBool', 'warning:'))
            builds.append({'source': source, 'command': command, 'returncode': run.returncode,
                           'log': str(log.relative_to(ROOT))})
            print(f'Lean passed: {source}', flush=True)
    return builds


def complete_prefix_windows():
    rows = []
    totals = {'positive_source_depth_pairs': 0, 'avoid_one_cases': 0, 'avoid64_cases': 0}
    for k in range(17):
        one_cases = floor_cases = 0
        for n in range(1, 1 << k):
            x, j = n, 0
            one = floor = True
            for _ in range(k):
                one &= x > 1
                floor &= x > 64
                j += x % 2
                x = step(x)
            growth_checks(n, k, x, j, one, floor)
            one_cases += int(one)
            floor_cases += int(floor)
        rows.append({'depth': k, 'positive_canonical_sources': (1 << k) - 1,
                     'avoid_one_cases': one_cases, 'avoid64_cases': floor_cases})
        totals['positive_source_depth_pairs'] += (1 << k) - 1
        totals['avoid_one_cases'] += one_cases
        totals['avoid64_cases'] += floor_cases
    print('Complete positive residue-window checks passed through depth 16.', flush=True)
    return {'depth_interval': [0, 16], 'rows': rows, 'totals': totals,
            'scope': 'Complete positive canonical sources 1..2^k-1 at each depth; no all-lift claim from enumeration.'}


def trace_to_one(n, guard=100000):
    x, j, k = n, 0, 0
    states, weights = [], []
    one = floor = True
    prefix_credit = 0
    first_floor = None
    while True:
        growth_checks(n, k, x, j, one, floor)
        states.append(x)
        weights.append(j)
        prefix_credit = max(prefix_credit, 2 * j - k)
        if x <= 64 and first_floor is None:
            first_floor = k
        if x == 1:
            break
        one &= x > 1
        floor &= x > 64
        j += x % 2
        x = step(x)
        k += 1
        assert k < guard, ('Arrival not established within the replay guard', n)
    grade = k - 2 * j
    credit = max(prefix_credit, 1 - grade)
    b = (n - 1).bit_length()
    assert first_floor <= 4 * credit + 5 * b
    assert k <= 4 * credit + 5 * b + 71
    assert k - first_floor <= 71
    return {'first_one_time': k, 'first_floor64_time': first_floor,
            'odd_count_at_one': j, 'grade': grade, 'minimum_full_orbit_credit': credit,
            'ceiling_log2_source': b, 'linear_time_bound': 4 * credit + 5 * b + 71,
            'states': states, 'weights': weights}


def complete_trajectories(limit=32768):
    index_checks = 0
    minimum_margin = None
    selected = []
    for n in range(1, limit + 1):
        row = trace_to_one(n)
        index_checks += len(row['states'])
        margin = row['linear_time_bound'] - row['first_one_time']
        minimum_margin = margin if minimum_margin is None else min(minimum_margin, margin)
        if n in (1, 2, 3, 27, 159, 6171, limit):
            selected.append({'source': n, **{k: v for k, v in row.items() if k not in ('states', 'weights')}})
    print(f'Direct trajectories and linear bounds passed for 1..{limit}.', flush=True)
    return {'complete_source_interval': [1, limit], 'direct_index_checks': index_checks,
            'smallest_time_bound_margin_in_window': minimum_margin, 'selected_cases': selected,
            'all_source_extension_inferred': False}


def endpoint_certificates():
    sources = (1, 2, 3, 27, 31, 159, 6171, 837799, 1723519)
    cases = []
    valid = invalid = endpoint_only = 0
    for n in sources:
        trace = trace_to_one(n)
        b = trace['ceiling_log2_source']
        full_credit = trace['minimum_full_orbit_credit']
        for A in range(full_credit + 3):
            clock = 4 * A + 5 * b + 1
            x, j = n, 0
            earlier_max = 0
            for i in range(clock):
                earlier_max = max(earlier_max, 2 * j - i)
                j += x % 2
                x = step(x)
            holds = 2 * j <= clock + A
            if holds:
                valid += 1
                assert trace['first_floor64_time'] <= clock - 1
                assert trace['first_one_time'] <= clock + 70
                endpoint_only += int(earlier_max > A)
            else:
                invalid += 1
            cases.append({'source': n, 'allowance': A, 'clock': clock,
                          'odd_count': j, 'endpoint_condition': holds,
                          'earlier_credit_violation': earlier_max > A,
                          'source_converges': True})
    witness = next(r for r in cases if r['source'] == 27 and r['allowance'] == 12)
    assert witness['clock'] == 74 and witness['odd_count'] == 43
    assert witness['endpoint_condition'] and witness['earlier_credit_violation']
    assert valid and invalid and endpoint_only
    return {'sources': list(sources), 'cases': cases, 'valid_endpoint_certificates': valid,
            'failed_conditions_on_convergent_sources': invalid,
            'valid_despite_earlier_credit_violation': endpoint_only,
            'explicit_endpoint_only_witness': witness}


def large_families():
    prefix_cases = 0
    for k in range(1, 257):
        for q in (1, 3, 17, (1 << 128) + 3):
            n = (1 << k) * q - 1
            x, j = n, 0
            for _ in range(k):
                assert x % 2
                j += 1
                x = step(x)
            assert x == 3 ** k * q - 1 and j == k
            growth_checks(n, k, x, j, n > 1, n > 64)
            prefix_cases += 1
    arrivals = []
    for k in range(2, 10):
        a = 3 ** (k - 1)
        assert ((1 << a) + 1) % 3 ** k == 0
        q = ((1 << a) + 1) // 3 ** k
        n = (1 << k) * q - 1
        row = trace_to_one(n)
        assert row['first_one_time'] == k + a
        assert row['odd_count_at_one'] == k
        assert row['minimum_full_orbit_credit'] == k
        assert row['states'][k] == 1 << a
        arrivals.append({'odd_prefix_length': k, 'source_bits': n.bit_length(),
                         'source_decimal_sha256': hashlib.sha256(str(n).encode()).hexdigest(),
                         'power_of_two_endpoint_exponent': a,
                         **{key: value for key, value in row.items() if key not in ('states', 'weights')}})
    return {'all_odd_prefix_cases': prefix_cases, 'all_odd_length_interval': [1, 256],
            'explicit_large_convergent_family': arrivals,
            'arbitrary_all_odd_family_convergence_inferred': False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    assert 10 ** 4 < 3 ** 4 * 2 ** 7
    assert 196 ** 5 < 65 ** 5 * 2 ** 8
    prefixes = complete_prefix_windows()
    paths = complete_trajectories()
    endpoints = endpoint_certificates()
    families = large_families()
    replay = {'all_checks_passed': True, 'prefix_windows': prefixes,
              'complete_trajectory_window': paths, 'endpoint_tests': endpoints,
              'large_families': families,
              'universal_parity_bound_proved': False, 'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [*SOURCES, 'docs/PARITY-SURVIVAL.md', 'verify_parity_survival.py',
             'results/coalescence-grades/verification.json',
             'results/weighted-survivors/verification.json',
             'results/parity-survival/replay.json', *[b['log'] for b in builds]]
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['general prefix growth bound conditional on an odd-step bound',
                         'general exact power comparison converting growth into parity counts',
                         '4k<=7w+4b on prefixes avoiding one',
                         '5k<=8w+5b on prefixes avoiding 1..64',
                         'single endpoint credit at clock 4A+5b+1 forces floor64 entry by the previous clock',
                         'arrival at one by 4A+5b+71 under endpoint or full-orbit credit',
                         'every hypothetical positive counterexample satisfies 5k<=8w+5b at every clock',
                         'each proposed credit is exceeded at a specific linear clock on a counterexample',
                         'a sufficiently sparse single parity prefix certifies ordinary convergence',
                         'explicit implications between logarithmic credit and logarithmic total-time bounds'],
        'written_scope': ['liminf odd frequency at least 5/8 on every hypothetical counterexample',
                          'O(log n) credit and O(log n) total time are equivalent uniform proposals'],
        'python_scope': ['complete positive canonical residue windows through depth16',
                         'direct trajectories and conditional bounds for every source1..32768',
                         'endpoint conditions checked separately from all-prefix credit',
                         'large all-odd prefixes and an explicit convergent family through a6556-bit source'],
        'not_proved': ['a finite credit for every positive source',
                       'a universal logarithmic credit or stopping-time bound',
                       'a universal individual-orbit lower limiting odd frequency below5/8',
                       'exclusion of nontrivial positive cycles or divergent positive trajectories',
                       'the full positive-integer Collatz conjecture'],
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('All checks passed. The universal parity premise and Collatz remain unresolved.', flush=True)


if __name__ == '__main__':
    main()
