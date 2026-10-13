"""Check dyadic refinement defects inside the actual known Collatz basin.

Finite arithmetic is kernel checked; infinite counting/measure arguments
are written in the companion note. Positive lower density at one reuses
the completed external replay; no density-one assertion is assumed.
"""

from array import array
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
OUT = ROOT / 'results/dyadic-coalescence-defects'
SOURCE = 'lean/DyadicCoalescenceDefects.lean'
SOURCES = ['CollatzPacking.lean', 'CollatzContradiction.lean',
           'lean/FirstPassagePacking.lean', 'lean/FinitePathPacking.lean',
           'lean/EqualWeightFibres.lean', 'lean/CoalescenceGrades.lean', SOURCE]
THEOREMS = [
    'grade_unique', 'grade_one', 'grade_double', 'grade_transfer',
    'safe_child_grade', 'safe_chain_grade', 'avoid_one_tail',
    'strict_odd_step', 'strict_prefix_envelope', 'first_arrival_contraction',
    'arrival_length_bound', 'parity_word_length', 'parity_word_sum',
    'parity_word_binary', 'same_parity_step_injective',
    'parity_word_endpoint_injective', 'two_five_le_six',
    'leading_grade_odd_bound',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(q):
    return [q.numerator, q.denominator]


def shortcut(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def direct(n):
    x, odds, path, seen = n, 0, [], set()
    while x != 1:
        assert x not in seen, ('unexpected nonstandard cycle', n, x)
        seen.add(x)
        path.append(x)
        odds += x & 1
        x = shortcut(x)
        assert len(path) < 100000, 'unresolved source, not a divergence certificate'
    return len(path), odds, path


def finite_checks():
    counts = Counter()
    maximum = 1 << 19
    memo = {1: (0, 0)}
    for n in range(2, maximum + 1):
        x, trail, seen = n, [], set()
        while x not in memo:
            assert x not in seen, ('unexpected cycle', n, x)
            seen.add(x)
            trail.append(x)
            x = shortcut(x)
            assert len(trail) < 100000, 'unresolved source, not a divergence certificate'
        t, a = memo[x]
        for x in reversed(trail):
            t, a = t + 1, a + (x & 1)
            memo[x] = (t, a)

    safe = bytearray(maximum + 1)
    defects = array('B', [0]) * (maximum + 1)
    safe[1] = 1
    max_a = max(memo[n][1] for n in range(1, maximum + 1))
    p3, p4, p10 = ([base ** a for a in range(max_a + 1)] for base in (3, 4, 10))
    for n in range(1, maximum + 1):
        t, a = memo[n]
        g = t - 2 * a
        assert (1 << t) <= p4[a] * n
        assert p3[a] * (1 << t) <= p10[a] * n
        counts['complete_first_arrival_integer_bounds'] += 1
        k = n.bit_length() - 1
        if g == k:
            assert a <= 3
            counts['leading_grade_odd_caps'] += 1
        if n > 1:
            tp, ap = memo[n // 2]
            good = g == tp - 2 * ap + 1
            if n % 2 == 0:
                assert good
                counts['doubling_grade_identities'] += 1
            safe[n] = safe[n // 2] and good
            defects[n] = defects[n // 2] + (not good)
            if safe[n]:
                assert g == k and a <= 3
                counts['safe_root_one_descendants'] += 1
    for n in range(1, 4097):
        t, a, path = direct(n)
        assert (t, a) == memo[n]
        odd = 0
        x = n
        for j, y in enumerate(path):
            assert x == y and y != 1
            assert 3 ** odd * (1 << j) * x <= 10 ** odd * n
            if y & 1:
                assert y >= 3 and 3 * shortcut(y) <= 5 * y
            odd += y & 1
            x = shortcut(x)
            counts['direct_strict_prefix_envelopes'] += 1
        assert x == 1 and odd == a
        counts['independent_first_arrival_paths'] += 1

    inverse_words = {}
    for t in range(13):
        for mask in range(1 << t):
            if mask.bit_count() > 3:
                continue
            x, valid = 1, True
            for j in reversed(range(t)):
                if (mask >> j) & 1:
                    if (2 * x - 1) % 3:
                        valid = False
                        break
                    x = (2 * x - 1) // 3
                    if x <= 0 or x % 2 != 1:
                        valid = False
                        break
                else:
                    x *= 2
            if not valid:
                continue
            y, word = x, 0
            for j in range(t):
                word |= (y & 1) << j
                y = shortcut(y)
            assert y == 1 and word == mask
            key = (t, mask)
            assert key not in inverse_words or inverse_words[key] == x
            inverse_words[key] = x
            counts['independent_inverse_word_certificates'] += 1

    for L in range(4, 20):
        for K in range(6):
            low = [n for n in range(1, (1 << L) + 1) if memo[n][1] <= K]
            for n in low:
                assert memo[n][0] <= L + 2 * K
            assert len(low) <= (L + 2 * K + 1) ** (K + 1)
            counts['finite_low_odd_count_bounds'] += 1

    rows = []
    scale = 1 << 48
    for k in range(4, 19):
        lo, hi = 1 << k, 1 << (k + 1)
        n_safe = sum(safe[lo:hi])
        assert n_safe <= (k + 8) ** 4
        floor_sum, remainders = 0, 0
        odd_histogram = Counter()
        for n in range(lo, hi):
            t, a = memo[n]
            g = t - 2 * a
            numerator, denominator = ((1 << g, n) if g >= 0 else (1, n << (-g)))
            q, r = divmod(scale * numerator, denominator)
            floor_sum += q
            remainders += bool(r)
            odd_histogram[a] += 1
            if n < lo + 64 or (n - lo) % 7919 == 0:
                v = Fraction(numerator, denominator)
                assert 0 < v <= 1 and v <= Fraction(5, 6) ** a
                assert Fraction(q, scale) <= v <= Fraction(q + bool(r), scale)
                counts['independent_fraction_grade_weights'] += 1
        row = {'dyadic_exponent': k, 'source_interval': [lo, hi],
               'uninterrupted_balanced_descendants_of_one': n_safe,
               'safe_fraction': ratio(Fraction(n_safe, lo)),
               'polynomial_count_upper_bound': (k + 8) ** 4,
               'first_arrival_odd_histogram': dict(sorted(odd_histogram.items())),
               'mean_grade_weight_lower': ratio(Fraction(floor_sum, lo * scale)),
               'mean_grade_weight_upper': ratio(Fraction(floor_sum + remainders, lo * scale)),
               'mean_refinement_defects': ratio(Fraction(sum(defects[lo:hi]), lo))}
        if k <= 17:
            bad = sum(memo[2 * n][0] - 2 * memo[2 * n][1] !=
                      memo[2 * n + 1][0] - 2 * memo[2 * n + 1][1]
                      for n in range(lo, hi))
            row['actual_eventual_unbalanced_even_pairs'] = bad
            row['B_k'] = ratio(Fraction(bad, lo))
            row['actual_unsafe_refinement_measure'] = ratio(Fraction(bad, 2 * lo))
        rows.append(row)
        print('Finite dyadic census passed:', k, flush=True)

    root_rows = []
    for root in (1, 3, 5, 13, 27):
        t0, a0 = memo[root]
        g0 = t0 - 2 * a0
        constant = (Fraction(1 << g0, root + 1) if g0 >= 0
                    else Fraction(1, (root + 1) << (-g0)))
        cap = 0
        while Fraction(5, 6) ** (cap + 1) > constant:
            cap += 1
        frontier = [root]
        for depth in range(13):
            assert all(memo[n][0] - 2 * memo[n][1] == g0 + depth and memo[n][1] <= cap
                       for n in frontier)
            counts['safe_general_root_leaves'] += len(frontier)
            root_rows.append({'root': root, 'depth': depth, 'safe_leaves': len(frontier),
                              'uniform_odd_cap': cap})
            if depth < 12:
                next_frontier = []
                for n in frontier:
                    for child in (2 * n, 2 * n + 1):
                        tc, ac = memo[child]
                        if tc - 2 * ac == g0 + depth + 1:
                            next_frontier.append(child)
                frontier = next_frontier
    return {'maximum_source': maximum, 'counts': dict(counts), 'dyadic_rows': rows,
            'general_convergent_roots': root_rows,
            'scope': 'All sampled starts have explicit finite first arrivals at one. Counts do not estimate an asymptotic error.'}


def validate_external():
    record = json.loads((ROOT / 'results/predecessor-density-review/verification.json').read_text())
    assert record['status'] == 'passed' and record['modules_total'] == 389
    assembled = Path(record['assembled'])
    for b in record['builds']:
        command = b['command']
        source = assembled / command[-1]
        obj = Path(command[command.index('-o') + 1])
        assert digest(source) == b['source_sha256'], source
        assert digest(obj) == b['olean_sha256'], obj
        assert digest(ROOT / b['log']) == b['log_sha256'], b['log']
    assert digest(assembled / 'lake-manifest.json') == record['lake_manifest_sha256']
    return {'reused_completed_replay': True, 'project_module_source_object_log_hashes_revalidated': 389,
            'premise_used': 'Positive lower natural density of predecessors of 1 only.',
            'full_third_party_source_rebuild': False,
            'natural_passage_or_density_one_premise_used': False}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-dyadic-defects-') as directory:
        build = Path(directory)
        for source in SOURCES:
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
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
                assert {name for name, _ in found} == {'DyadicCoalescenceDefects.' + t for t in THEOREMS}
                for name, axioms in found:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': proc.returncode,
                           'elapsed_seconds': round(time.monotonic() - start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Lean passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = ['results/coalescence-grades/verification.json',
             'results/coalescence-tail/verification.json',
             'results/weighted-dissipation/verification.json']
    prior_counts = {}
    for name in prior:
        record = json.loads((ROOT / name).read_text())
        for path, expected in record['sha256'].items():
            assert digest(ROOT / path) == expected, (name, path)
        prior_counts[name] = len(record['sha256'])
    external = validate_external()
    print('Revalidated completed external PLD replay; no rebuild.', flush=True)
    version, builds = build_lean()
    finite = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(finite, indent=2) + '\n')
    files = [*SOURCES, Path(__file__).name, 'docs/DYADIC-COALESCENCE-DEFECTS.md',
             'docs/COALESCENCE-TAIL.md', *prior,
             'results/predecessor-density-review/verification.json',
             'results/dyadic-coalescence-defects/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': prior_counts, 'external_input': external,
        'kernel_scope': [
            'Arrival-grade uniqueness and transport along doubling or a balanced odd refinement.',
            'A strict rational envelope before first arrival at one.',
            'A source-size and odd-count bound on arrival length; injectivity of endpoint plus parity word.',
            'Every leading-grade first arrival uses at most three odd inputs.',
        ],
        'written_scope': [
            'A polynomial bound on sources with bounded first-arrival odd count.',
            'Uninterrupted balanced descendants of any convergent root have bounded first-arrival odd count and zero limiting fraction.',
            'Dyadic paths eventually making only balanced refinements, and later visiting the known basin, form a null set.',
            'Using positive lower density at one, actual eventual-unbalanced even-pair fractions B_k have divergent sum.',
            'If full Collatz holds, almost every dyadic path has infinitely many such unweighted defects despite having identically zero infinite weights.',
        ],
        'finite_scope': finite['counts'],
        'not_proved': ['A summable bound for actual infinite-weight changes.',
                       'Zero escaping mass or exclusion of other cycles.',
                       'The full positive-integer Collatz conjecture.'],
        'sha256': {str(path): digest(ROOT / path) for path in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: dyadic coalescence defects; full Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
