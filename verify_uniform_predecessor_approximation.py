"""Check the exact passage comparison behind uniform predecessor approximation.

The limits and logarithmic rate remain written analysis. Finite experiments
cannot certify those limits, density-one convergence, or the Collatz conjecture.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
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
OUT = ROOT / 'results/uniform-predecessor-approximation'
DEPENDENCY = 'CollatzContradiction.lean'
SOURCE = 'lean/PassageApproximation.lean'
THEOREMS = ['first_entry_exists', 'first_entry_unique', 'mark_none_iff',
            'mark_some_iff', 'reaches_trans', 'first_entry_suffix',
            'never_after_reach', 'landing_reaches_subset', 'passage_comparison',
            'early_hit_same_mark', 'odd_floor_comparison']


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


def count_hash(counts):
    data = ''.join(f'{a}:{counts[a]}\n' for a in sorted(counts) if counts[a])
    return hashlib.sha256(data.encode()).hexdigest()


def finite_checks():
    populations = [32, 128, 512, 2048]
    paths = {n: complete_path(n) for n in range(1, max(populations) + 1)}
    universe = set().union(*(set(path) for path in paths.values()))
    for a in universe - paths.keys():
        paths[a] = complete_path(a)
    assert all(ordinary(a) in universe for a in universe)
    orbits = {n: set(path) for n, path in paths.items()}
    predicates = [(f'odd_floor_{H}', lambda n, H=H: n % 2 == 1 and n <= H)
                  for H in (1, 7, 31, 127)]
    for targets in ((), (3,), (4,), (5,), (27,), (8, 13)):
        target_set = frozenset(targets)
        predicates.append(('finite_set_' + '_'.join(map(str, targets)),
                           lambda n, values=target_set: n in values))
    totals = Counter()
    rows, halving = [], []
    for X in populations:
        actual = Counter()
        stripped = Counter()
        for n in range(1, X + 1):
            actual.update(orbits[n])
            odd = n // (n & -n)
            stripped.update(orbits[odd])
        max_halving_difference = 0
        for a in universe:
            difference = actual[a] - stripped[a]
            doubling_sources = (X // a).bit_length()
            assert 0 <= difference <= doubling_sources, (X, a)
            assert doubling_sources <= X.bit_length()
            if a % 2:
                assert difference == 0, (X, a)
            max_halving_difference = max(max_halving_difference, difference)
            totals['initial_halving_target_checks'] += 1
        halving.append({'cutoff': X, 'maximum_count_difference': max_halving_difference,
                        'uniform_integer_bound': X.bit_length()})
        for label, predicate in predicates:
            marks = {a: next((v for v in path if predicate(v)), None)
                     for a, path in paths.items()}
            histogram = Counter(marks[n] for n in range(1, X + 1))
            mixture = Counter()
            for b, weight in histogram.items():
                if b is not None:
                    for a in orbits[b]:
                        mixture[a] += weight
            for n in range(1, X + 1):
                mark = marks[n]
                late = orbits[mark] if mark is not None else set()
                assert late <= orbits[n], (X, label, n)
                for a in orbits[n] - late:
                    assert marks[a] == mark, (X, label, n, a)
                    totals['early_hit_same_mark_checks'] += 1
                totals['landing_subset_checks'] += 1
            max_difference = 0
            for a in universe:
                difference = actual[a] - mixture[a]
                assert 0 <= difference <= histogram[marks[a]], (X, label, a)
                max_difference = max(max_difference, difference)
                totals['target_uniform_histogram_checks'] += 1
            max_atom = max(histogram.values())
            assert max_difference <= max_atom
            rows.append({'cutoff': X, 'predicate': label,
                         'finite_mark_count': sum(b is not None for b in histogram),
                         'nonentry_count': histogram[None], 'maximum_atom_count': max_atom,
                         'maximum_target_count_error': max_difference,
                         'target_vector_sha256': count_hash(actual),
                         'mixture_vector_sha256': count_hash(mixture)})
    assert any(row['nonentry_count'] > 0 for row in rows)
    assert any(row['nonentry_count'] == 0 for row in rows)
    return {'scope': 'Exact finite populations, complete represented trajectories, and all their reachable targets; no asymptotic conclusion.',
            'source_cutoffs': populations, 'complete_original_sources': max(populations),
            'closed_orbit_universe_size': len(universe), 'maximum_observed_value': max(universe),
            'target_scope': 'All values in the closed orbit universe are checked. Both finite-population target vectors are zero outside it.',
            'counts': dict(totals), 'initial_halving_checks': halving,
            'histogram_comparisons': rows}


def build_lean(cache):
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    cached, cache_hash = {}, None
    if cache is not None:
        manifest = cache / 'build-manifest.json'
        data = json.loads(manifest.read_text())
        assert data['lean_version'] == version
        cache_hash = digest(manifest)
        cached = {r['source']: r for r in data['builds']}
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-passage-approximation-') as directory:
        build = Path(directory)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        for source in [DEPENDENCY, SOURCE]:
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            reused = cache is not None and source == DEPENDENCY
            started = time.monotonic()
            if reused:
                row = cached[source]
                old_obj, old_log = cache / (stem + '.olean'), cache / (stem + '.log')
                assert row['returncode'] == 0 and row['source_sha256'] == digest(ROOT / source)
                assert row['olean_sha256'] == digest(old_obj)
                assert row['log_sha256'] == digest(old_log)
                shutil.copyfile(old_obj, obj)
                log.write_text(old_log.read_text())
                command = row.get('command')
            else:
                command = ['lean', '-o', str(obj), source]
                result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                log.write_text(result.stdout)
                assert result.returncode == 0, result.stdout
            output = log.read_text()
            assert not any(s in output for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
                assert len(blocks) == len(THEOREMS)
                assert {name for name, _ in blocks} == {'PassageApproximation.' + t for t in THEOREMS}
                for name, axioms in blocks:
                    assert {s.strip() for s in axioms.split(',')} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': 0,
                           'elapsed_seconds': round(time.monotonic() - started, 3),
                           'reused_verified_build': reused,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj), 'native_computation_used': False})
            print(f'Lean passed: {source}' + (' (validated dependency reused)' if reused else ''), flush=True)
    return version, builds, cache_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-build-dir', type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    version, builds, cache_hash = build_lean(args.reuse_build_dir)
    replay = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    prior = ['results/predecessor-density-flow/verification.json',
             'results/density-to-pointwise/written-review.json']
    prior_counts = {}
    for record in prior:
        previous = json.loads((ROOT / record).read_text())
        for source, expected in previous['sha256'].items():
            assert digest(ROOT / source) == expected, (record, source)
        prior_counts[record] = len(previous['sha256'])
    files = [SOURCE, DEPENDENCY, Path(__file__).name,
             'docs/UNIFORM-PREDECESSOR-APPROXIMATION.md',
             'docs/PREDECESSOR-DENSITY-FLOW.md', 'docs/NATURAL-DENSITY-ALMOST-BOUNDED.md',
             *prior, 'results/uniform-predecessor-approximation/replay.json',
             *[r['log'] for r in builds]]
    result = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
        'reused_build_manifest_sha256': cache_hash, 'prior_hashes_validated': prior_counts,
        'kernel_scope': ['Noncomputable first-passage mark with correct entry and nonentry cases.',
                         'Existence, uniqueness, and suffix transport of a first entry.',
                         'Any target hit is after the landing or shares the target passage mark.',
                         'The landing-hit event is contained in the full target-hit event.'],
        'written_scope': ['Uniform convergence of predecessor proportions over all targets, with logarithmic error, conditional on the written first-passage estimates.',
                          'Finite-mixture approximation of the entire target-density function, with maximum-atom error.',
                          'Uniform control of the initial-halving discrepancy for positive source populations.'],
        'python_scope': replay,
        'dependencies': {'uniform_first_passage': 'Written Proposition 4.1, not kernel checked.',
                         'limiting_passage_atom_bound': 'Written Section 2 of PREDECESSOR-DENSITY-FLOW, with the earlier kernel bounded-time fibre estimate.',
                         'external_PLD': 'Only used when describing the positive density of a hypothetical divergent component, not in the uniform-approximation proof.'},
        'not_proved': ['Density-one convergence or decay of r_a along every unbounded forward orbit.',
                       'Exclusion of all nontrivial positive cycles or divergent positive orbits.',
                       'Kernel verification or a new numerical value for the analytic error bound.'],
        'sha256': {name: digest(ROOT / name) for name in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'kernel_theorems': len(THEOREMS),
                      'finite_checks': replay['counts'],
                      'closed_orbit_universe_size': replay['closed_orbit_universe_size'],
                      'histogram_comparisons': len(replay['histogram_comparisons']),
                      'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
