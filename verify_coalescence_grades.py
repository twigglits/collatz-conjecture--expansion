"""Exact finite replay of arrival grades and the conditional credit rank.

The universal existence of a finite credit is not inferred from this census.
Lean supplies all-index theorems; the larger census is independent Python.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/coalescence-grades'
SOURCES = ('CollatzPacking.lean', 'CollatzContradiction.lean',
           'lean/FirstPassagePacking.lean', 'lean/FinitePathPacking.lean',
           'lean/EqualWeightFibres.lean', 'lean/CoalescenceGrades.lean')


def step(x):
    return (3 * x + 1) // 2 if x % 2 else x // 2


def rank(x, g):
    assert x > 0 and g >= 0
    return (1 << (g + 1)) * (x - 1) + g


def iterate(n, k):
    x, j = n, 0
    for _ in range(k):
        j += x % 2
        x = step(x)
    return x, j


def build_lean():
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-coalescence-grades-') as build:
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


def grade_census(limit=2_000_000):
    # (first-one time, odd count at first one, minimum credit for the full orbit).
    # The final component includes the continued 1<->2 cycle: its credit at 1 is 1.
    known = {1: (0, 0, 1)}
    lowest = 0
    highest_credit = 1
    grade_records, credit_records = [], []
    minima = {}
    digest = hashlib.sha256()
    for n in range(1, limit + 1):
        path, x = [], n
        while x not in known:
            path.append(x)
            assert len(path) < 10000, ('Convergence not certified within replay guard', n)
            x = step(x)
        t, j, credit = known[x]
        for x in reversed(path):
            t += 1
            if x % 2:
                j += 1
                credit += 1
            else:
                credit = max(0, credit - 1)
            known[x] = t, j, credit
        t, j, credit = known[n]
        d = t - 2 * j
        digest.update(f'{n},{t},{j},{credit}\n'.encode())
        minima.setdefault(d, n)
        assert t <= rank(n, credit)
        if d >= 0:
            assert (1 << d) <= n
        if d < lowest:
            grade_records.append({'source': n, 'grade': d, 'drop_from_previous': lowest - d})
            lowest = d
        if credit > highest_credit:
            credit_records.append({'source': n, 'minimum_credit': credit})
            highest_credit = credit
    for a in range(limit.bit_length()):
        assert minima[a] == 1 << a
    report = {'complete_source_interval': [1, limit],
              'all_sources_reach_one_in_python': True,
              'kernel_checked_source_interval_not_claimed': True,
              'canonical_row_format': 'source,first_one_time,odd_count,minimum_full_orbit_credit\n',
              'canonical_rows_sha256': digest.hexdigest(),
              'negative_grade_records': grade_records,
              'minimum_credit_records': credit_records,
              'lowest_grade': lowest, 'highest_minimum_credit': highest_credit,
              'nonnegative_grade_minima': {str(a): minima[a] for a in range(limit.bit_length())},
              'all_start_extension_inferred': False}
    print(f'Python certified arrivals, grades, and credits for sources 1..{limit}.', flush=True)
    return known, report


def direct_replay(known, limit=8192):
    steps = 0
    for n in range(1, limit + 1):
        expected_t, expected_j, credit = known[n]
        x, j, observed_credit = n, 0, 0
        first = None
        for k in range(expected_t + 3):
            assert (1 << k) * x <= (1 << (2 * j)) * n
            observed_credit = max(observed_credit, 2 * j - k)
            g = credit + k - 2 * j
            assert g >= 0
            if x == 1 and first is None:
                first = k, j
            y = step(x)
            ng = g + 1 - 2 * (x % 2)
            if x > 1:
                assert rank(y, ng) < rank(x, g)
                drop = rank(x, g) - rank(y, ng)
                exact_drop = ((1 << (g - 1)) * (x - 3) + 1 if x % 2
                              else (1 << (g + 1)) - 1)
                assert drop == exact_drop >= 1
            j += x % 2
            x = y
            steps += 1
        assert first == (expected_t, expected_j)
        assert observed_credit == credit
    print(f'Independent direct replay passed for {limit} sources, {steps} steps.', flush=True)
    return {'complete_source_interval': [1, limit], 'direct_step_checks': steps,
            'includes_two_post_arrival_indices': True,
            'checks': ['first arrival and odd count against memoized census',
                       'exact minimum credit against direct prefix maximum',
                       'dyadic envelope at every replay index',
                       'strict rank decrease and exact drop before reaching one']}


def meeting_partitions(known, limit=8192):
    clock = max(known[n][0] for n in range(1, limit + 1))
    by_grade, by_pair = {}, {}
    for n in range(1, limit + 1):
        t, j, _ = known[n]
        d = t - 2 * j
        y, w = iterate(n, clock)
        assert y in (1, 2)
        assert clock - 2 * w + y - 1 == d
        if d in by_grade:
            assert by_grade[d] == (y, w)
        if (y, w) in by_pair:
            assert by_pair[y, w] == d
        by_grade[d] = y, w
        by_pair[y, w] = d
    return {'complete_source_interval': [1, limit], 'common_clock': clock,
            'number_of_grade_classes': len(by_grade),
            'grade_partition_equals_state_and_weight_partition': True,
            'ordered_pairs_classified_by_partition_equality': limit ** 2}


def sharp_meetings(known, horizon=128):
    paths = {n: [iterate(n, k) for k in range(horizon + 1)] for n in range(1, 28)}
    same_clock_checks = equal_weight_checks = 0
    minimum_odd_gap, minimum_clock_gap = None, None
    rows = []
    t27, j27, _ = known[27]
    assert (t27, j27, t27 - 2 * j27) == (70, 41, -12)
    for m in range(1, 27):
        t, j, _ = known[m]
        d = t - 2 * j
        assert d >= 0
        rows.append({'source': m, 'first_one_time': t, 'odd_count': j, 'grade': d})
        for a, (y, wa) in enumerate(paths[27]):
            ym, wm = paths[m][a]
            if y == ym:
                assert wa - wm >= 6
                assert -12 - d == -2 * (wa - wm)
                same_clock_checks += 1
                minimum_odd_gap = min(minimum_odd_gap or wa - wm, wa - wm)
            for b, (z, wb) in enumerate(paths[m]):
                if y != z:
                    continue
                assert -12 - d == a - b - 2 * (wa - wb)
                if wa == wb:
                    assert b - a >= 12
                    equal_weight_checks += 1
                    minimum_clock_gap = min(minimum_clock_gap or b - a, b - a)
    assert (minimum_odd_gap, minimum_clock_gap) == (6, 12)
    assert paths[27][70] == (1, 41)
    assert paths[1][70] == (1, 35)
    assert paths[1][82] == (1, 41)
    return {'small_grade_table': rows, 'clock_horizon': horizon,
            'same_clock_meetings_checked': same_clock_checks,
            'equal_weight_meetings_checked': equal_weight_checks,
            'minimum_odd_gap_at_common_clock': minimum_odd_gap,
            'minimum_clock_gap_at_equal_weight': minimum_clock_gap,
            'all_time_extension': 'Kernel meeting_grade_balance with the complete small-grade table.'}


def all_odd_checks():
    cases = 0
    for k in range(1, 257):
        for q in (1, 3, 17, (1 << 128) + 3):
            n = (1 << k) * q - 1
            y, j = iterate(n, k)
            assert y == 3 ** k * q - 1 and j == k
            assert 2 * j - k == k
            cases += 1
    return {'length_interval': [1, 256], 'positive_quotients': [1, 3, 17, (1 << 128) + 3],
            'cases': cases, 'minimum_credit_through_tested_prefix': 'K',
            'convergence_of_arbitrary_family_members_inferred': False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    known, census = grade_census()
    direct = direct_replay(known)
    partitions = meeting_partitions(known)
    sharp = sharp_meetings(known)
    odd = all_odd_checks()
    replay = {'all_checks_passed': True, 'grade_and_credit_census': census,
              'independent_direct_replay': direct, 'meeting_partitions': partitions,
              'sharp_27_meetings': sharp, 'all_odd_prefixes': odd,
              'universal_credit_bound_proved': False, 'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [*SOURCES, 'docs/COALESCENCE-GRADES.md', 'verify_coalescence_grades.py',
             'results/equal-weight-fibres/verification.json',
             'results/coalescence-grades/replay.json', *[b['log'] for b in builds]]
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['dyadic envelope for every positive source and finite time',
                         'classification of convergent equal-time equal-weight meetings by arrival grade',
                         'grade balance for arbitrary clocks and odd counts at a physical meeting',
                         'sharp all-time lower bounds of six odd steps or twelve clock steps for 27',
                         'powers of two are exact minimal nonnegative-grade representatives',
                         'powers of two have no positive smaller equal-time equal-weight mates at any time',
                         'strict conditional credit-rank decrease and explicit hitting-time bound',
                         'finite-credit test and bounded-time excess witnesses for hypothetical counterexamples',
                         'all-odd prefixes force arbitrarily large credits across starting numbers',
                         'full Collatz equivalence to finite per-source odd/even credit',
                         'full Collatz equivalence to same-clock descent allowing unequal odd counts',
                         'full Collatz equivalence to equal-weight descent allowing different clocks'],
        'python_scope': ['exact memoized convergence, grade, and minimum-credit census through 2,000,000',
                         'independent direct trajectory and rank replay through source 8192',
                         'complete finite grade/meeting partition comparison through source 8192',
                         'finite arbitrary-clock meeting identities for starts 1..27',
                         'large all-odd family prefixes through length 256'],
        'not_proved': ['a finite credit for every positive start',
                       'a computable universal formula for such a credit',
                       'universal smaller coalescence under either relaxed criterion',
                       'exclusion of nontrivial positive cycles or divergent positive trajectories',
                       'the positive-integer Collatz conjecture'],
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('All checks passed. Finite per-source credit and the full conjecture remain unproved.', flush=True)


if __name__ == '__main__':
    main()
