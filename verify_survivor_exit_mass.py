"""Exact finite certificates for the full weighted survivor mass.

The first-entry table is a Python check, not a Lean proof. Written
nonnegative-sum and integral estimates justify the infinite tail.
No finite set of successful horizons is extrapolated to all time.
"""
from array import array
from datetime import datetime, timezone
import hashlib
import json
from math import isqrt
from pathlib import Path

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/survivor-exit-mass'
FLOOR = 64
LIMIT = 2_000_000
SCALE = 2 ** 96


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def floor_weight(n):
    a = isqrt(SCALE * SCALE // n ** 3)
    assert a * a * n ** 3 <= SCALE * SCALE < (a + 1) ** 2 * n ** 3
    return a


def floor_reciprocal_root(n):
    a = isqrt(SCALE * SCALE // n)
    assert a * a * n <= SCALE * SCALE < (a + 1) ** 2 * n
    return a


def validate_previous():
    rows = []
    for name in ('weighted-survivors', 'fibre-prefix-bound'):
        path = ROOT / 'results' / name / 'verification.json'
        record = json.loads(path.read_text())
        for relative, expected in record['sha256'].items():
            actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
            assert actual == expected, ('previous verification is stale', relative)
        rows.append({'manifest': str(path.relative_to(ROOT)),
                     'matched_hashes': len(record['sha256']),
                     'scope': 'reused verification; no new Lean build claimed'})
    return rows


def hitting_table():
    times = array('i', [-1]) * (LIMIT + 1)
    for n in range(1, FLOOR + 1):
        times[n] = 0
    records, high = [], 0
    for n in range(FLOOR + 1, LIMIT + 1):
        x, path = n, []
        while x > LIMIT or times[x] < 0:
            path.append(x)
            # Reaching this guard is a failure to certify, never a divergence claim.
            assert len(path) <= 10000, ('finite replay guard exceeded', n)
            x = step(x)
        t = times[x]
        for x in reversed(path):
            t += 1
            if x <= LIMIT:
                times[x] = t
        if times[n] > high:
            high = times[n]
            records.append({'source': n, 'first_floor_entry': high})
        if n % 500000 == 0:
            print(f'first-entry table: all starts through {n}', flush=True)
    assert high == 335
    assert all(t >= 0 for t in times[1:])
    digest = hashlib.sha256()
    for n in range(1, LIMIT + 1):
        digest.update(f'{n},{times[n]}\n'.encode('ascii'))
    return times, {'source_interval': [1, LIMIT], 'floor': FLOOR,
                   'all_sources_reach_floor_in_python': True,
                   'maximum_first_entry_time': high,
                   'record_first_entry_times': records,
                   'table_row_format': 'source,first_floor_entry\n',
                   'table_sha256': digest.hexdigest(),
                   'kernel_verification_of_this_table_claimed': False}


def direct_replay(times):
    by_time = {}
    for n in range(1, LIMIT + 1):
        t = times[n]
        if t not in by_time:
            by_time[t] = [n, n]
        else:
            by_time[t][1] = n
    initial = range(1, 65537)
    extra = set(range(65537, LIMIT + 1, 997))
    extra.add(LIMIT)
    for ends in by_time.values():
        extra.update(ends)
    extra.difference_update(initial)
    steps = 0
    for n in [*initial, *sorted(extra)]:
        x, t = n, 0
        while x > FLOOR:
            x = step(x)
            t += 1
            assert t <= 10000, ('independent replay guard exceeded', n)
        assert t == times[n], (n, t, times[n])
        steps += t
    # Independently verify a physical first-return edge for EVERY table row.
    # Outside-window states are all above the floor. The certified table
    # label strictly decreases on return, so induction on that label proves
    # the claimed first-entry time without assuming convergence outside R.
    inside = outside = return_steps = 0
    assert all(times[n] == 0 for n in range(1, FLOOR + 1))
    for n in range(FLOOR + 1, LIMIT + 1):
        y, length = step(n), 1
        if y <= LIMIT:
            inside += 1
        else:
            outside += 1
        while y > LIMIT:
            y = step(y)
            length += 1
            assert length <= 10000, ('first-return certificate guard exceeded', n)
        assert times[n] == times[y] + length
        assert times[y] < times[n]
        return_steps += length
    assert inside + outside == LIMIT - FLOOR
    return {'complete_direct_interval': [1, 65536], 'additional_sources': len(extra),
            'direct_step_count': steps, 'attained_time_layers': len(by_time),
            'in_table_step_recurrences': inside,
            'outside_excursion_recurrences': outside,
            'first_return_certificate_step_count': return_steps,
            'all_nonbase_table_rows_independently_certified': inside + outside}


def exact_mass_certificates(times):
    horizon = max(times)
    weights, counts = [0] * (horizon + 1), [0] * (horizon + 1)
    for n in range(FLOOR + 1, LIMIT + 1):
        t = times[n]
        weights[t] += floor_weight(n)
        counts[t] += 1
    assert sum(counts) == LIMIT - FLOOR
    mass, count = sum(weights), sum(counts)
    tail_hi = 2 * (floor_reciprocal_root(LIMIT) + 1)
    rows, good = [], []
    for k in range(horizon + 1):
        mass -= weights[k]
        count -= counts[k]
        guaranteed_tail_start = max(LIMIT, FLOOR * (1 << k))
        mass_lo = mass + 2 * floor_reciprocal_root(guaranteed_tail_start + 1)
        mass_hi = mass + count + tail_hi
        # At very late horizons the guaranteed positive tail can be below
        # one unit of SCALE; zero is then a valid rounded lower bound.
        assert 0 <= mass_lo <= mass_hi and mass_hi > 0
        loss_lo = weights[k + 1] if k < horizon else 0
        known_exit_count = counts[k + 1] if k < horizon else 0
        complete_exit = FLOOR * (1 << (k + 1)) <= LIMIT
        loss_hi = loss_lo + known_exit_count + (0 if complete_exit else tail_hi)
        passed = 1000 * loss_lo >= 7 * mass_hi
        if passed:
            good.append(k)
        rows.append({'k': k, 'mass_scaled_interval': [mass_lo, mass_hi],
                     'known_survivor_count': count,
                     'known_survivor_mass_lower_numerator': mass,
                     'known_exit_count': known_exit_count,
                     'exit_mass_scaled_interval': [loss_lo, loss_hi],
                     'complete_exit_layer_in_source_window': complete_exit,
                     'relative_loss_lower_fraction': [loss_lo, mass_hi],
                     'mass_ratio_upper_fraction': [mass_hi - loss_lo, mass_hi],
                     'certifies_ratio_at_most_993_over_1000': passed,
                     'failed_test_is_not_a_refutation_of_contraction': not passed})
    assert good == [*range(127), 128]
    # The decimal sentence in the note is itself certified by integer comparison.
    lo128, hi128 = rows[128]['relative_loss_lower_fraction']
    assert 100_000_000 * lo128 > 711966 * hi128
    old = json.loads((ROOT / 'results/weighted-survivors/replay.json').read_text())
    assert int(old['scale']) == SCALE
    for row in old['rows']:
        lo, hi = row['mass_scaled_interval']
        new_lo, new_hi = rows[row['k']]['mass_scaled_interval']
        assert max(lo, new_lo) <= min(hi, new_hi)
    for before, after in zip(old['rows'], old['rows'][1:]):
        lo, hi = before['mass_scaled_interval']
        nlo, nhi = after['mass_scaled_interval']
        dl, dh = rows[before['k']]['exit_mass_scaled_interval']
        assert max(lo - nhi, dl) <= min(hi - nlo, dh)
    print(f'Certified {len(good)} actual mass contractions: k=0..126 and k=128.', flush=True)
    return {'scale': SCALE, 'source_cutoff': LIMIT,
            'whole_tail_upper_numerator': tail_hi, 'rows': rows,
            'certified_horizons': good, 'first_failed_sufficient_test': 127,
            'older_mass_interval_comparisons': len(old['rows']),
            'older_exit_interval_comparisons': len(old['rows']) - 1,
            'all_time_contraction_claimed': False,
            'infinitely_many_contractions_claimed': False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    dependencies = validate_previous()
    times, table = hitting_table()
    direct = direct_replay(times)
    masses = exact_mass_certificates(times)
    report = {'all_checks_passed': True, 'floor': FLOOR, 'exponent': '3/2',
              'first_entry_table': table, 'independent_direct_replay': direct,
              'mass_certificates': masses, 'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(report, indent=2) + '\n')
    files = ['verify_survivor_exit_mass.py', 'docs/SURVIVOR-EXIT-MASS.md',
             'results/survivor-exit-mass/replay.json',
             'results/weighted-survivors/verification.json',
             'results/weighted-survivors/replay.json',
             'results/fibre-prefix-bound/verification.json']
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'new_kernel_theorems': [],
        'reused_verifications': dependencies,
        'written_scope': ['exact exit-mass identity for nested actual survivor sets',
                          'known exits divided by a full mass upper bound certify relative loss',
                          'integral bounds on unclassified infinite tails'],
        'python_scope': ['exact first-floor-entry times for all starts1..2000000',
                         'direct replay for all starts1..65536 and recorded extra samples',
                         'independent physical first-return certificates for every nonbase table row',
                         'exact integer enclosures of weights and tails',
                         '128 certificates for full infinite mass contraction, at k=0..126 and128',
                         'overlap with every prior complete inverse-cone mass interval'],
        'not_proved': ['that a failed sufficient test disproves the actual contraction inequality',
                       'infinitely many successful contraction horizons',
                       'all-time contraction', 'vanishing survivor mass',
                       'exclusion of nontrivial positive cycles or divergent positive orbits',
                       'the full Collatz conjecture'],
        'external_proof_inputs': [],
        'sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('All finite checks passed. No infinite extension is inferred.', flush=True)


if __name__ == '__main__':
    main()
