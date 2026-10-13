"""Verify exact minimum-clock transport for finite ordinary Collatz samples.

The natural-density and logarithmic-time conclusions are written deductions
from the separately recorded analytic premises, not finite-test conclusions.
"""
import argparse
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/clocked-minimum'
SOURCE = 'lean/ClockedMinimum.lean'
THEOREMS = ['minimum_exists', 'minimum_by_exists', 'minimum_by_mono',
            'finite_population_minimum_clock', 'first_odd_below_record',
            'minimum_after_record', 'record_minimum_at', 'record_minimum_by',
            'record_minimum_suffix', 'first_minimum_unique',
            'record_first_minimum', 'record_first_minimum_suffix',
            'coupled_first_minimum_clocks', 'coupled_record_minimum_by',
            'coupled_first_odd_below_minimum_by', 'minimum_by_of_hit_one',
            'minimum_by_iff_hit_one', 'target_before_or_after',
            'geometric_chernoff_comparison', 'log_two_partial_sum_comparison',
            'clock_coefficient_comparison', 'ordinary_clock_budget']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ordinary(n):
    return 3 * n + 1 if n % 2 else n // 2


def complete_path(n):
    path, positions = [], {}
    x = n
    while x not in positions:
        positions[x] = len(path)
        path.append(x)
        x = ordinary(x)
        assert len(path) < 100000, ('unresolved trajectory', n)
    assert set(path[positions[x]:]) == {1, 2, 4}, (n, x)
    return tuple(path)


def fraction_json(value):
    return [value.numerator, value.denominator]


def finite_checks():
    totals = Counter()
    paths = {n: complete_path(n) for n in range(1, 8193)}
    minimum = {n: min(path) for n, path in paths.items()}
    tau = {n: path.index(minimum[n]) for n, path in paths.items()}
    totals['complete_known_cycle_sources'] = len(paths)
    totals['distinct_path_entries_with_source_multiplicity'] = sum(map(len, paths.values()))
    assert all(value == 1 for value in minimum.values())
    floors = [0, 1, 3, 7, 31, 127, 511, 2047]
    passages = {}
    floor_rows = []
    for H in floors:
        marks, groups = {}, defaultdict(list)
        prefix_checks = 0
        for n, path in paths.items():
            i = next((j for j, x in enumerate(path) if x % 2 and x <= H), None)
            b = path[i] if i is not None else None
            marks[n] = (i, b)
            groups[b].append(n)
            if i is None:
                assert H == 0
                totals['nonentry_marks_checked'] += 1
                continue
            assert all(x > b for x in path[:i]), (H, n, i, b)
            assert minimum[n] == minimum[b]
            assert tau[n] == i + tau[b], (H, n, i, b)
            assert tau[n] >= i
            prefix_checks += i
            totals['record_entry_and_minimum_clock_checks'] += 1
            if n <= 1024:
                suffix_values = set(paths[b])
                for t, a in enumerate(path):
                    assert t <= i or a in suffix_values, (H, n, a)
                    totals['target_before_or_after_checks'] += 1
        for b, sources in groups.items():
            if b is None:
                continue
            m = sources[0]
            j = marks[m][0]
            for n in sources:
                i = marks[n][0]
                assert tau[n] <= i + tau[m]
                assert tau[n] - i == tau[m] - j
                assert tau[n] + j == tau[m] + i
                totals['coupled_clock_checks_against_group_representative'] += 1
        passages[H] = marks
        floor_rows.append({'floor': H, 'finite_landing_groups': len(groups) - (None in groups),
                           'nonentry_sources': len(groups.get(None, [])),
                           'ordinary_prefix_values_compared_with_landing': prefix_checks})
    assert passages[31][85] == (9, 1)
    assert paths[85][5] == 16 and 16 <= 31

    # Test the finite probability inequality for arbitrary populations.
    # No analytic mixing bound is inferred: the TV and slow-passage term
    # are evaluated exactly as rational numbers for these finite samples.
    probability_rows = []
    for Y in (128, 256, 1024, 4096):
        Z = Y // 2
        source = list(range(Y + 1, 2 * Y, 2))
        reference = list(range(Z + 1, 2 * Z, 2))
        for H in (0, 1, 7, 31, 127):
            marks = passages[H]
            p = Counter(marks[n][1] for n in source)
            q = Counter(marks[n][1] for n in reference)
            keys = set(p) | set(q)
            tv = sum((abs(Fraction(p[b], len(source)) - Fraction(q[b], len(reference)))
                      for b in keys), Fraction()) / 2
            checked = 0
            maximum_excess = None
            for L in (0, 1, 4, 16, 64, 128):
                slow = Fraction(sum(marks[n][0] is None or marks[n][0] > L for n in source),
                                len(source))
                for T in (0, 8, 32, 128):
                    lhs = Fraction(sum(tau[n] > L + T for n in source), len(source))
                    ref = Fraction(sum(tau[n] > T for n in reference), len(reference))
                    g_source = Fraction(sum(marks[n][1] is not None and tau[marks[n][1]] > T
                                            for n in source), len(source))
                    g_reference = Fraction(sum(marks[n][1] is not None and tau[marks[n][1]] > T
                                               for n in reference), len(reference))
                    assert lhs <= slow + g_source
                    assert g_source <= g_reference + tv
                    assert g_reference <= ref
                    assert lhs <= ref + slow + tv
                    excess = lhs - ref - slow - tv
                    maximum_excess = excess if maximum_excess is None else max(maximum_excess, excess)
                    checked += 1
                    totals['exact_probability_clock_transfer_checks'] += 1
            probability_rows.append({'source_odd_interval': [Y, 2 * Y],
                                     'reference_odd_interval': [Z, 2 * Z], 'floor': H,
                                     'total_variation': fraction_json(tv),
                                     'clock_pairs_checked': checked,
                                     'maximum_lhs_minus_rhs': fraction_json(maximum_excess)})

            # Centered comparisons use both passage clocks. Centers and
            # radii are rational, unrelated to any asymptotic claim.
            for center_source, center_reference in ((Fraction(17, 3), Fraction(5, 2)),
                                                    (Fraction(48), Fraction(32))):
                for radius in (Fraction(0), Fraction(3, 2), Fraction(16), Fraction(64)):
                    bad_source = Fraction(sum(marks[n][0] is None or
                        abs(marks[n][0] - center_source) > radius for n in source), len(source))
                    bad_reference = Fraction(sum(marks[n][0] is None or
                        abs(marks[n][0] - center_reference) > radius for n in reference), len(reference))
                    for threshold in (Fraction(0), Fraction(13, 2), Fraction(40), Fraction(128)):
                        lhs = Fraction(sum(abs(tau[n] - center_source) > threshold + 2 * radius
                                           for n in source), len(source))
                        ref = Fraction(sum(abs(tau[n] - center_reference) > threshold
                                           for n in reference), len(reference))
                        assert lhs <= ref + bad_source + bad_reference + tv
                        totals['exact_centered_probability_clock_checks'] += 1

    alpha = Fraction(1001, 1000)
    partial_log = 2 * sum((Fraction(1, (2 * j + 1) * 3 ** (2 * j + 1))
                           for j in range(4)), Fraction())
    assert partial_log == Fraction(53056, 76545) > Fraction(693, 1000)
    chernoff = Fraction(101 ** 100 * 201 ** 201, 100 ** 100 * 202 ** 201)
    assert 0 < chernoff < 1
    coefficient_bound = Fraction(301, 693) / (alpha * (alpha - 1))
    assert coefficient_bound == Fraction(301000000, 693 * 1001) < 435
    partial_clock = Fraction()
    for J in range(129):
        expected = coefficient_bound * (1 - alpha ** (-J))
        assert partial_clock == expected < 435
        totals['exact_scale_clock_sums'] += 1
        partial_clock += Fraction(301, 693) * alpha ** (-J - 2)
    for n0 in range(257):
        for steps in (0, n0 // 2, n0):
            valuation = 201 * n0 // 100
            assert 100 * (steps + valuation) <= 301 * n0
            totals['ordinary_clock_budget_checks'] += 1

    population_clocks = []
    for N in (64, 256, 1024, 4096, 8192):
        T = max(tau[n] for n in range(1, N + 1))
        population_clocks.append({'source_cutoff': N, 'exact_maximum_minimum_time': T,
                                  'least_maximizing_source': next(n for n in range(1, N + 1) if tau[n] == T)})
    return {'scope': 'Exact finite ordinary Collatz trajectories and rational inequalities; no numerical certification of a density error or asymptotic time bound.',
            'counts': dict(totals), 'floors': floor_rows,
            'even_below_floor_before_odd_landing_witness': {'source': 85, 'floor': 31,
                'ordinary_landing_time': 9, 'landing': 1, 'earlier_time': 5, 'earlier_value': 16},
            'probability_clock_transfers': probability_rows,
            'exact_arithmetic': {'log_two_positive_partial_sum': fraction_json(partial_log),
                                 'chernoff_factor': fraction_json(chernoff),
                                 'scale_clock_coefficient_upper_bound': fraction_json(coefficient_bound)},
            'finite_population_minimum_clocks': population_clocks,
            'minimum_scope': 'All sampled paths end in the verified 1,4,2 cycle, so their global minimum and first attainment are determined exactly.'}


def build_lean(cache):
    version = subprocess.check_output(['lean', '--version'], text=True, cwd=ROOT).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    cached, cache_hash = {}, None
    if cache:
        manifest = cache / 'build-manifest.json'
        data = json.loads(manifest.read_text())
        assert data['lean_version'] == version
        cached = {r['source']: r for r in data['builds']}
        cache_hash = digest(manifest)
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-clocked-minimum-') as directory:
        build = Path(directory)
        for source in ['CollatzContradiction.lean', SOURCE]:
            started = time.monotonic()
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            reused = bool(cache) and source == 'CollatzContradiction.lean'
            if reused:
                old = cached[source]
                for path, key in [(ROOT / source, 'source_sha256'),
                                  (cache / (stem + '.olean'), 'olean_sha256'),
                                  (cache / (stem + '.log'), 'log_sha256')]:
                    assert digest(path) == old[key], (source, key)
                assert old['returncode'] == 0
                shutil.copyfile(cache / (stem + '.olean'), obj)
                log.write_text((cache / (stem + '.log')).read_text())
                command = old.get('command')
            else:
                command = ['lean', '-o', str(obj), source]
                proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT,
                                      env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
                log.write_text(proc.stdout)
                assert proc.returncode == 0, proc.stdout
            output = log.read_text()
            assert not any(s in output for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                found = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
                assert len(found) == len(THEOREMS)
                assert {n for n, _ in found} == {'ClockedMinimum.' + t for t in THEOREMS}
                for name, axioms in found:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': 0, 'reused_verified_build': reused,
                           'elapsed_seconds': round(time.monotonic() - started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj), 'native_computation_used': False})
            print('Lean passed:', source, '(validated cache)' if reused else '(fresh)', flush=True)
    return version, builds, cache_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-build-dir', type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    prior = ['results/density-time-truncation/verification.json',
             'results/density-to-pointwise/written-review.json']
    prior_counts = {}
    for record in prior:
        data = json.loads((ROOT / record).read_text())
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (record, path)
        prior_counts[record] = len(data['sha256'])
    version, builds, cache_hash = build_lean(args.reuse_build_dir)
    replay = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [SOURCE, 'CollatzContradiction.lean', Path(__file__).name, 'docs/CLOCKED-MINIMUM.md',
             'docs/NATURAL-DENSITY-ALMOST-BOUNDED.md', 'docs/DENSITY-TO-POINTWISE.md',
             'docs/DENSITY-TIME-TRUNCATION.md', 'results/predecessor-density-review/verification.json',
             *prior, 'results/clocked-minimum/replay.json', *[b['log'] for b in builds]]
    result = {'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'collatz_status': 'unresolved', 'map_scope': 'Ordinary positive-integer Collatz.',
              'lean_version': version, 'builds': builds, 'kernel_theorems': len(THEOREMS),
              'reused_build_manifest_sha256': cache_hash, 'prior_hashes_validated': prior_counts,
              'kernel_scope': ['Every orbit attains its global minimum at a finite time; this does not identify it with one.',
                               'Every finite population has a finite common minimum-attainment clock.',
                               'First odd passage is a strict record low, with exact suffix and coupled clock transfer, including the signed difference of first-minimum times.',
                               'For a convergent source, MinimumBy is equivalent to hitting one within the same time.',
                               'Exact rational comparisons for the Chernoff and logarithmic clock budgets.'],
              'written_scope': ['Conditional on written natural first-passage stabilization, the global-minimum time divided by log n tends in natural density to 3/log(4/3).',
                                'Every fixed finite eventual-target profile is captured by c log n outside density zero for each c greater than 3/log(4/3); every fixed target has zero density of earlier hits for smaller c.',
                                'The uniform eventual-hit truncation defect at c log X tends to the largest component density below that coefficient, and to the largest divergent-component density above it; the equality case is not determined.',
                                'A separate coarse one-sided argument gives the explicit 435 log n bound using kernel-checked integer comparisons.'],
              'python_scope': replay,
              'dependencies': {'natural_passage_mixing': 'Local written Proposition 4.1; not kernel checked or independently strengthened here.',
                               'early_valuation_law': 'Tao arXiv:1909.03562v7 Proposition 1.9 and Lemma 2.2, with the local uniform-residue argument; primary source rechecked this turn.',
                               'minimum_and_component_density_laws': 'Earlier written deductions from the passage estimates.',
                               'external_PLD': 'Only for positivity of each fixed eligible target and for zero divergent density implying no divergent component; previous source replay reused.'},
              'primary_source': 'https://arxiv.org/html/1909.03562v7',
              'not_proved': ['That the global orbit minimum equals one for every positive start.',
                             'That the logarithmic-clock uniform defect or divergent-component density is zero.',
                             'Exclusion of nontrivial cycles or the full Collatz conjecture.',
                             'Kernel formalization or an effective numerical error rate for the analytic density conclusions.'],
              'sha256': {name: digest(ROOT / name) for name in files}}
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'kernel_theorems': len(THEOREMS),
                      'finite_checks': replay['counts'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
