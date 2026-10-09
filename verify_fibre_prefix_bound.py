"""Independent exact replay of the parity-prefix inverse-fibre bound.

Finite maxima are never extrapolated. The universal recurrence is a Lean
theorem; exponential and real moment estimates are separately written.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from functools import cache
import hashlib
from itertools import combinations
import json
from math import comb, isqrt
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/fibre-prefix-bound'
SOURCES = ('CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
           'lean/FinitePathPacking.lean', 'lean/EqualWeightFibres.lean',
           'lean/FibrePrefixBound.lean')


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def iterate(n, k):
    x, j, evens = n, 0, []
    for i in range(k):
        if x % 2:
            j += 1
        else:
            evens.append(i)
        x = step(x)
    return x, j, evens


@cache
def bound(e, a=0):
    assert e >= 0 and a >= 0
    if 3 ** a + 1 >= 2 ** e:
        return 1
    assert a < e
    return bound(e - 1, a) + bound(e, a + 1)


def build_lean():
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-fibre-prefix-') as build:
        for source in SOURCES:
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


def complete_windows():
    rows, direct, total = [], {}, 0
    for k in range(19):
        counts, spans = Counter(), {}
        for n in range(1 << k):
            y, j, evens = iterate(n, k)
            e = k - j
            E = sum((1 << i) * 3 ** (j - i + r) for r, i in enumerate(evens))
            assert (1 << k) * (y + 1) == 3 ** j * (n + 1) + E
            assert 0 <= y < 3 ** j
            counts[j, y] += 1
            if (j, y) not in spans:
                spans[j, y] = [n, n]
            else:
                spans[j, y][1] = n
            total += 1
        maxima = {}
        for (j, y), count in counts.items():
            e, (lo, hi) = k - j, spans[j, y]
            assert count <= bound(e)
            if e:
                assert hi + 1 < lo + (1 << e)
            else:
                assert lo == hi
            if count > maxima.get(e, {}).get('count', 0):
                maxima[e] = {'odd_count': j, 'even_count': e, 'count': count,
                             'target_residue': y, 'recurrence_bound': bound(e)}
        if k <= 12:
            direct[k] = counts
        rows.append({'depth': k, 'canonical_sources': 1 << k,
                     'maxima_by_even_count': list(maxima.values())})
        print(f'direct depth {k}: all {1 << k} canonical sources', flush=True)
    return {'source_depth_pairs': total, 'complete_depths': [0, 18], 'rows': rows}, direct


def word_counter(e, j):
    k, modulus = e + j, 3 ** j
    terms = [[(1 << i) * 3 ** (j - i + r) if r <= i <= j + r else 0
              for i in range(k)] for r in range(e)]

    def words():
        for positions in combinations(range(k), e):
            E = sum(terms[r][i] for r, i in enumerate(positions))
            yield positions, E

    counts = Counter(E % modulus for _, E in words())
    assert sum(counts.values()) == comb(k, e)
    assert max(counts.values()) <= bound(e)
    return counts, words


def parity_word_checks(direct):
    small_words = 0
    for k, targets in direct.items():
        for j in range(k + 1):
            counts, _ = word_counter(k - j, j)
            modulus = 3 ** j
            inv2 = pow(1 << k, -1, modulus)
            translated = {(r * inv2 - 1) % modulus: count for r, count in counts.items()}
            expected = {y: count for (jj, y), count in targets.items() if jj == j}
            assert translated == expected
            small_words += sum(counts.values())
    selected = [(2, 64), (3, 48), (4, 32), (5, 24), (6, 16), (7, 16),
                (8, 16), (9, 7), (9, 8), (9, 15), (10, 9), (11, 9),
                (12, 11), (13, 10), (14, 9), (15, 9), (16, 8)]
    rows, total, lifts = [], 0, 0
    for e, j in selected:
        k, modulus = e + j, 3 ** j
        counts, words = word_counter(e, j)
        residue = max(counts, key=counts.get)
        maximum = counts[residue]
        target = (residue * pow(1 << k, -1, modulus) - 1) % modulus
        inv3 = pow(modulus, -1, 1 << k)
        members = []
        for positions, E in words():
            if E % modulus != residue:
                continue
            nplus = (-E * inv3) % (1 << k) or (1 << k)
            n = nplus - 1
            assert (1 << k) * (target + 1) == modulus * nplus + E
            for q in (0, 1, 2 ** 100 + 37):
                actual_y, actual_j, actual_positions = iterate((1 << k) * q + n, k)
                assert (actual_y, actual_j) == (modulus * q + target, j)
                assert tuple(actual_positions) == positions
                lifts += 1
            members.append(n)
        assert len(members) == maximum == len(set(members))
        assert max(members) + 1 < min(members) + (1 << e)
        rows.append({'even_count': e, 'odd_count': j, 'depth': k,
                     'parity_words': comb(k, e), 'complete_target_residue_classes': modulus,
                     'nonempty_fibres': len(counts), 'maximum': maximum,
                     'recurrence_bound': bound(e), 'witness_target_residue': target,
                     'complete_canonical_witness_members': sorted(members),
                     'maximum_valid_for_all_targets_at_this_depth_and_weight': True,
                     'maximum_extrapolated_to_other_depths': False})
        total += comb(k, e)
        print(f'word class e={e}, j={j}: {comb(k,e)} words, maximum {maximum}', flush=True)
    nine = {row['odd_count']: row['maximum'] for row in rows if row['even_count'] == 9}
    assert nine[7] == 25 and nine[8] == 26
    return {'small_words_compared_with_direct_trajectories': small_words,
            'selected_parity_words': total, 'direct_witness_lift_checks': lifts,
            'rows': rows}


def grid_checks():
    rows, pairs = [], 0
    for a in range(7):
        q = 3 ** a
        for r in sorted({0, 1, q - 1, q + 7, 2 ** 80 + 19}):
            values, weights = [q * x + r for x in range(128)], [0] * 128
            for k in range(21):
                counts = Counter(zip(values, weights))
                for (_, j), size in counts.items():
                    assert size <= bound(k - j, a)
                pairs += len(values)
                for x, n in enumerate(values):
                    weights[x] += n % 2
                    values[x] = step(n)
            rows.append({'spacing_exponent': a, 'offset': r, 'index_interval': [0, 127],
                         'depth_interval': [0, 20], 'complete_infinite_grid_fibre': False})
    for q in (0, 1, 17, 2 ** 256 + 33):
        for n in (8 * q + 4, 8 * q + 5):
            y, j, _ = iterate(n, 3)
            assert (y, j) == (3 * q + 2, 1)
    return {'source_depth_pairs': pairs, 'grids': rows, 'two_even_sharp_lift_checks': 8}


def sqrt_interval(num, den, scale):
    """Enclose sqrt(num/den) in integer units of 1/scale."""
    lo = isqrt(num * scale * scale // den)
    assert lo * lo * den <= num * scale * scale < (lo + 1) ** 2 * den
    hi = lo if lo * lo * den == num * scale * scale else lo + 1
    return lo, hi


def moment_checks(direct):
    scale, rows, total = 2 ** 80, [], 0
    assert 1000 ** 24 < 2 ** 19 * 579 ** 24
    assert 1000 ** 24 < 3 ** 19 * 421 ** 24
    assert 2 ** 19 * 2000 ** 24 < 3 ** 12 * 1999 ** 24
    for k in range(10):
        counts = direct[k]
        unit = [sqrt_interval(3 ** j, 1 << k, scale) for j in range(k + 1)]
        rate_lo, _ = sqrt_interval(3 ** k, 1 << k, scale)
        sum_lo = sum_hi = maximum_hi = 0
        for residue in range(3 ** k):
            # Choose y=3^k+residue: all complete fibres then have positive sources.
            amounts = [counts[j, residue % 3 ** j] for j in range(k + 1)]
            lo = sum(count * unit[j][0] for j, count in enumerate(amounts))
            hi = sum(count * unit[j][1] for j, count in enumerate(amounts))
            assert hi <= 4000 * rate_lo
            maximum_hi = max(maximum_hi, hi)
            sum_lo += lo
            sum_hi += hi
            total += 1
        # Check the exact combinatorial identity behind the written average.
        expected_lo = sum(comb(k, j) * 3 ** (k - j) * unit[j][0] for j in range(k + 1))
        expected_hi = sum(comb(k, j) * 3 ** (k - j) * unit[j][1] for j in range(k + 1))
        assert (sum_lo, sum_hi) == (expected_lo, expected_hi)
        rows.append({'depth': k, 'complete_target_classes': 3 ** k,
                     'interval_scale': scale, 'maximum_upper_numerator': maximum_hi,
                     'rate_lower_numerator': rate_lo, 'uniform_constant_checked': 4000,
                     'mean_combinatorial_identity_checked': True})
    return {'complete_target_classes': total, 'rows': rows,
            'arithmetic': 'exact integer square-root enclosures; no floating-point decisions'}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    windows, direct = complete_windows()
    words = parity_word_checks(direct)
    grids = grid_checks()
    moments = moment_checks(direct)
    recurrence = [{'even_count': e, 'bound': bound(e)} for e in range(129)]
    replay = {'all_checks_passed': True, 'canonical_windows': windows,
              'parity_words': words, 'arithmetic_grids': grids,
              'square_root_moments': moments, 'recurrence_values': recurrence,
              'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [*SOURCES, 'docs/FIBRE-PREFIX-BOUND.md', 'verify_fibre_prefix_bound.py',
             'results/equal-weight-fibres/verification.json',
             'results/fibre-prefix-bound/replay.json', *[b['log'] for b in builds]]
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['strict fibre diameter below 2^e-1 when e>0',
                         'exact parity images of grids with spacing 3^a',
                         'terminating universal recurrence B(e,a)',
                         'every finite same-time same-weight grid fibre has size at most B(e,a)',
                         'every finite unrestricted fibre has size at most B(e,0)',
                         'two even steps give at most two sources, with an all-index sharp family',
                         'exact integer comparisons supporting a rational analytic exponent'],
        'written_scope': ['B(e,0)<=2*(2^delta)^e where 2^-delta+3^-delta=1',
                          'uniform coefficient-moment bound for s>delta*log(2)/log(3)',
                          'square-root coefficient moment at most 4000*(3/2)^(k/2)',
                          'all-odd targets show optimal time-exponential rate in the proved range',
                          'averaging prevents that rate below s=log(3/2)/log(3)'],
        'python_scope': ['all canonical sources through depth18',
                         'independent even-position words versus direct paths through depth12',
                         'selected complete parity-word classes through64 odd steps',
                         'reconstructed maximal fibres and large positive affine lifts',
                         'finite source windows on arithmetic grids',
                         'exact interval checks of square-root moments and complete target averaging through depth9'],
        'not_proved': ['exact universal fibre maxima for e>=3',
                       'the optimal coefficient-moment threshold',
                       'vanishing or reusable contraction of actual survivor mass',
                       'unbounded fibre growth along a particular forward orbit',
                       'universal pointwise descent', 'exclusion of nontrivial positive cycles',
                       'exclusion of divergent positive orbits', 'the full Collatz conjecture'],
        'external_proof_inputs': [],
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('All checks passed. The stronger fibre bound does not prove Collatz.', flush=True)


if __name__ == '__main__':
    main()
