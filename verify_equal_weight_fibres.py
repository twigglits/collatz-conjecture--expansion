"""Exact replay of shifted envelopes and equal-weight coalescence fibres.

No finite plateau is declared permanent. The divergence implication uses
the separately recorded written reciprocal-summability argument.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/equal-weight-fibres'


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def iterate(n, k):
    x, j = n, 0
    for _ in range(k):
        j += x % 2
        x = step(x)
    return x, j


def envelopes(n, k, y, j):
    assert 0 <= j <= k
    assert 3 ** j * (n + 1) <= (1 << k) * y + (1 << j)
    assert (1 << k) * (y + 1) <= 3 ** j * (n + (1 << (k - j)))


def complete_residue_checks():
    records, moment_records = [], []
    residues = lifts = moment_targets = 0
    for k in range(17):
        fibres = Counter()
        ranges = {}
        p3 = [3 ** j for j in range(k + 1)]
        for n in range(1 << k):
            y, j = iterate(n, k)
            envelopes(n, k, y, j)
            assert y < p3[j]
            fibres[j, y] += 1
            if (j, y) not in ranges:
                ranges[j, y] = [n, n]
            else:
                ranges[j, y][1] = n
            residues += 1
        largest_by_j = {}
        for (j, y), count in fibres.items():
            lo, hi = ranges[j, y]
            e = k - j
            assert count <= 1 << e
            assert p3[j] * (hi - lo) <= (p3[j] - (1 << j)) * ((1 << e) - 1)
            if e <= 1:
                assert count == 1
            if j not in largest_by_j or count > largest_by_j[j]['count']:
                largest_by_j[j] = {'odd_count': j, 'even_count': e,
                                  'target_residue': y, 'count': count,
                                  'smallest_source': lo, 'largest_source': hi}
        # Replay representatives of every maximal weight group at large lifts.
        for row in largest_by_j.values():
            j, y = row['odd_count'], row['target_residue']
            for q in (1, 7, 2 ** 80 + 3):
                for r in sorted({row['smallest_source'], row['largest_source']}):
                    n = (1 << k) * q + r
                    yy, jj = iterate(n, k)
                    assert (yy, jj) == (p3[j] * q + y, j)
                    envelopes(n, k, yy, jj)
                    lifts += 1
        records.append({'depth': k, 'canonical_residues': 1 << k,
                        'distinct_weight_target_fibres': len(fibres),
                        'maxima_by_odd_count': list(largest_by_j.values())})
        if k <= 10:
            maxima = {p: {'moment': -1} for p in (1, 2)}
            # For a given j, every source for target Y lies in the one block
            # q=floor(Y/3^j), by the exact affine formula and residue bound.
            # Consequently these counts reconstruct the complete fibres,
            # not merely sources below 2^k. Y>=3^k makes every source positive.
            for r in range(3 ** k):
                Y = 3 ** k + r
                counts = [fibres.get((j, Y % p3[j]), 0) for j in range(k + 1)]
                for p in (1, 2):
                    moment = sum(c * 3 ** (p * j) for j, c in enumerate(counts))
                    assert (3 ** p - 2) * moment <= 3 ** (p * (k + 1)) - 2 ** (k + 1)
                    if moment > maxima[p]['moment']:
                        maxima[p] = {'moment': moment, 'target_residue': r,
                                     'target_used': Y}
                moment_targets += 1
            # The all-odd residue attains the required lower exponential rate.
            assert fibres[k, 3 ** k - 1] == 1
            moment_records.append({'depth': k, 'all_target_residue_classes': 3 ** k,
                                   'integer_exponent_maxima': maxima})
        print(f'depth {k}: {1 << k} residues, {len(fibres)} complete canonical fibres', flush=True)
    return records, moment_records, {'residue_envelope_checks': residues,
                                    'large_lift_checks': lifts,
                                    'complete_moment_target_classes': moment_targets}


def evolving_fibres():
    limit, horizon = 65536, 128
    starts = (1, 27, 159, 6171)
    values, weights = list(range(1, limit + 1)), [0] * limit
    previous = {n: set() for n in starts}
    snapshots, first_smaller = [], {n: None for n in starts}
    selected_times = {0, 1, 8, 16, 34, 35, 36, 64, 76, 77, 96, 128}
    membership_checks = 0
    for k in range(horizon + 1):
        targets = {(values[n - 1], weights[n - 1]) for n in starts}
        groups = {target: set() for target in targets}
        for m, (y, j) in enumerate(zip(values, weights), 1):
            if (y, j) in groups:
                groups[y, j].add(m)
            membership_checks += 1
        for n in starts:
            y, j = values[n - 1], weights[n - 1]
            members = groups[y, j]
            assert previous[n] <= members
            cap = ((1 << k) * y + (1 << j)) // 3 ** j - 1
            assert n in members and max(members) <= cap
            if first_smaller[n] is None and min(members) < n:
                first_smaller[n] = {'time': k, 'smaller_source': min(members),
                                    'complete_fibre_at_this_time': cap <= limit}
            if n == 1 and k <= 34:
                assert members == {1} and cap <= limit
            if n == 1 and k in (35, 36):
                assert members == {1, 159} and cap <= limit
            if n in (1, 159) and k >= 35:
                assert groups[values[0], weights[0]] == groups[values[158], weights[158]]
            if k in selected_times:
                snapshots.append({'source': n, 'time': k, 'target': y, 'odd_count': j,
                                  'all_source_upper_bound': cap,
                                  'searched_source_interval': [1, limit],
                                  'complete_fibre': cap <= limit,
                                  'count_in_search_interval': len(members),
                                  'smallest_member': min(members),
                                  'largest_member_in_search_interval': max(members)})
            previous[n] = members
        if k < horizon:
            for i, x in enumerate(values):
                weights[i] += x % 2
                values[i] = step(x)
    x, first_one = 159, None
    for k in range(37):
        if x == 1 and first_one is None:
            first_one = k
        x = step(x)
    assert first_one == 36
    return {'source_limit': limit, 'horizon': horizon,
            'direct_source_time_checks': membership_checks,
            'snapshots': snapshots, 'first_smaller_member_found': first_smaller,
            'complete_plateau_through_time': 34, 'first_new_member_time': 35,
            'first_new_member': 159, 'witness_first_one_time': first_one,
            'permanent_stabilization_inferred': False,
            'infinite_fibre_growth_inferred': False}


def build_lean():
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-equal-weight-') as build:
        for source in ('CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
                       'lean/FinitePathPacking.lean', 'lean/EqualWeightFibres.lean'):
            command = ['lean', '-o', str(Path(build) / (Path(source).stem + '.olean')), source]
            result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            log = OUT / (Path(source).stem + '.log')
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ('sorryAx', 'ofReduceBool', 'warning:'))
            builds.append({'source': source, 'command': command, 'returncode': result.returncode,
                           'log': str(log.relative_to(ROOT))})
            print(f'Lean passed: {source}', flush=True)
    return builds


def smaller_mate_obstruction():
    rows = []
    for n in range(1, 28):
        x, t, j = n, 0, 0
        while x != 1:
            j += x % 2
            x = step(x)
            t += 1
            assert t < 1000, ('first arrival not established', n)
        y72, w72 = iterate(n, 72)
        assert y72 in (1, 2)
        rows.append({'source': n, 'first_one_time': t, 'odd_count_at_first_one': j,
                     'arrival_label': t - 2 * j, 'state_at72': y72, 'odd_count_at72': w72})
    witness = rows[-1]
    assert (witness['first_one_time'], witness['arrival_label']) == (70, -12)
    for row in rows[:-1]:
        assert row['arrival_label'] != witness['arrival_label']
        assert (row['state_at72'], row['odd_count_at72']) != (
            witness['state_at72'], witness['odd_count_at72'])
    return {'complete_sources': rows, 'witness': 27,
            'all_time_conclusion_scope': 'The Lean cycle-cancellation theorem extends this complete finite check to all times.',
            'universal_smaller_equal_time_equal_weight_mate_claim_refuted': True,
            'broader_coalescence_descent_refuted': False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    residues, moments, totals = complete_residue_checks()
    evolution = evolving_fibres()
    obstruction = smaller_mate_obstruction()
    replay = {'all_checks_passed': True, 'residue_cases': residues,
              'coefficient_moment_cases': moments, 'totals': totals,
              'finite_fibre_evolution': evolution, 'smaller_mate_obstruction': obstruction,
              'new_collatz_counterexample': False}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = ['CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
             'lean/FinitePathPacking.lean', 'lean/EqualWeightFibres.lean',
             'docs/FINITE-PATH-PACKING.md', 'docs/EQUAL-WEIGHT-FIBRES.md',
             'results/finite-path-packing/verification.json',
             'verify_equal_weight_fibres.py', 'results/equal-weight-fibres/replay.json',
             *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['two all-time finite shifted affine envelopes',
                         'fibre span and cardinality at most 2^(even count)',
                         'injectivity when there is at most one even step',
                         'nesting of equal-time equal-weight coalescence fibres',
                         'all-source finite endpoint cap',
                         'eventual fibre stabilization conditional on a uniform normalized endpoint bound',
                         'complete fibres F34(1)={1} and F35(1)={1,159}',
                         'cancellation of later equal-weight merging inside the standard cycle',
                         '27 reaches one and has no positive smaller equal-weight mate at any time'],
        'written_scope': ['sharp uniform exponential growth rate of coefficient moments',
                          'reciprocal summability gives the normalized bound for divergent orbits',
                          'divergence forces eventual equal-weight fibre stabilization',
                          'divergence exists iff an all-prefix coefficient-supercritical start exists',
                          'classification of convergent equal-weight coalescence classes by the integer arrival label'],
        'python_scope': ['complete canonical residue fibres and envelopes through depth16, including zero',
                         'large affine lifts of representatives from every maximum-weight group',
                         'complete target-residue coefficient moments through depth10 at integer exponents1,2',
                         'finite evolving fibres in an explicit source window, with completeness flags',
                         'independent replay of the complete plateau and its convergent new member',
                         'complete convergence and arrival-label table for starts1..27'],
        'not_proved': ['unbounded fibre growth for every start',
                       'universal coefficient stopping', 'exclusion of nontrivial positive cycles',
                       'vanishing fixed-floor survivor mass', 'the full Collatz conjecture'],
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('All finite fibre checks passed. The universal growth premise and Collatz remain unresolved.', flush=True)


if __name__ == '__main__':
    main()
