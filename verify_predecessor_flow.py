"""Verify finite inputs to the written predecessor-density flow argument.

The limiting laws, decay of density within a fixed basin, and infinite branch
sums remain written analysis. This script does not prove density-one convergence.
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
OUT = ROOT / 'results/predecessor-density-flow'
DEPENDENCIES = ['CollatzPacking.lean', 'CollatzContradiction.lean',
                'lean/WeightedSurvivors.lean']
SOURCE = 'lean/BoundedHitFibres.lean'
THEOREMS = ['mem_hitCone', 'predecessor_length', 'flat_predecessor_length',
            'hitCone_length', 'distinct_bounded_hit_count', 'first_hit_unique',
            'first_hit_succ', 'ordinary_iterate_succ', 'nonperiodic_hit_time_unique',
            'predecessor_basins_disjoint', 'ordinary_predecessor_iff', 'basin_one_step']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def shortcut(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def ordinary(n):
    return 3 * n + 1 if n % 2 else n // 2


def inverse(y):
    return {2 * y} | ({(2 * y - 1) // 3} if y % 3 == 2 else set())


def ordinary_path(n):
    path, positions = [], {}
    x = n
    while x not in positions:
        positions[x] = len(path)
        path.append(x)
        x = ordinary(x)
        assert len(path) < 100000, ('unresolved finite trajectory', n)
    assert set(path[positions[x]:]) == {1, 2, 4}, (n, x)
    return path, positions


def finite_checks():
    counts = Counter()
    depth = 8
    for a in range(1, 33):
        level, cone = {a}, {a}
        cones = [set(cone)]
        for k in range(1, depth + 1):
            level = {n for y in level for n in inverse(y)}
            cone |= level
            cones.append(set(cone))
        direct = [set() for _ in range(depth + 1)]
        # The earlier kernel inequality n <= 2^k U^k(n) supplies this
        # complete source bound; forward simulation uses no inverse recursion.
        for n in range(1, (a << depth) + 1):
            counts['complete_bounded_fibre_sources'] += 1
            x = n
            for k in range(depth + 1):
                if x == a:
                    for j in range(k, depth + 1):
                        direct[j].add(n)
                    break
                if k < depth:
                    x = shortcut(x)
                    counts['bounded_fibre_forward_steps'] += 1
        for k, (backward, forward) in enumerate(zip(cones, direct)):
            assert backward == forward, (a, k)
            assert len(forward) + 1 <= 2 ** (k + 1), (a, k)
            counts['complete_bounded_fibres'] += 1

    thresholds = []
    for a in (1, 5, 27):
        for floor in (32, 64, 128):
            retained = set()
            for z in range(1, floor + 1):
                path, positions = ordinary_path(z)
                if a in positions:
                    retained.update(path[:positions[a] + 1])
            thresholds.append({'root': a, 'floor': floor,
                               'retained_count': len(retained), 'R': max(retained)})

    for n in range(1, 4097):
        path, positions = ordinary_path(n)
        counts['complete_ordinary_trajectories'] += 1
        counts['ordinary_steps'] += len(path)
        for row in thresholds:
            a, floor, R = row['root'], row['floor'], row['R']
            if a not in positions:
                continue
            landing = next(v for v in path if v % 2 and v <= floor)
            for i, b in enumerate(path[:positions[a] + 1]):
                if b > R:
                    assert all(v > floor for v in path[:i]), (n, a, floor, b)
                    landing_b = next(v for v in path[i:] if v % 2 and v <= floor)
                    assert landing == landing_b, (n, a, floor, b)
                    counts['finite_basin_passage_transports'] += 1
        for a in range(1, 33):
            hit = a in positions
            mark = None
            direct_power = None
            if hit:
                odds = [v for v in path[:positions[a]] if v % 2]
                if odds:
                    u = odds[-1]
                    assert (3 * u + 1) % a == 0
                    ratio = (3 * u + 1) // a
                    assert ratio > 0 and ratio & (ratio - 1) == 0
                    mark = ratio.bit_length() - 1
                else:
                    assert n % a == 0
                    ratio = n // a
                    assert ratio > 0 and ratio & (ratio - 1) == 0
                    direct_power = ratio.bit_length() - 1
                counts['terminal_halving_marks'] += 1
            for j in range(1, 11):
                target = (1 << j) * a
                # All enumerated trajectories were followed through a full
                # cycle; targets >4 cannot occur after the first hit of a.
                if target <= 4:
                    continue
                expected = hit and ((mark is not None and mark >= j) or
                                    (direct_power is not None and direct_power >= j))
                assert (target in positions) == expected, (n, a, j)
                counts['exact_doubling_tail_identities'] += 1
            if a > 1 and a % 2:
                # These targets are not periodic: their computed orbit reaches
                # {1,2,4}, as it did when n=a above (and also on its own here).
                for K in range(1, 9):
                    parents = [(2 ** k * a - 1) // 3 for k in range(1, K)
                               if (2 ** k * a - 1) % 3 == 0]
                    membership = [n in {a << j for j in range(K)},
                                  (a << K) in positions,
                                  *[b in positions for b in parents]]
                    assert sum(membership) == int(hit), (n, a, K)
                    counts['exact_finite_branch_partitions'] += 1
    # A periodic root really does violate the disjointness used in the flow.
    cycle_overlap = {'root': 4, 'distinct_parents': [8, 1], 'common_start': 8,
                     'path': [8, 4, 2, 1]}
    assert ordinary(8) == ordinary(1) == 4
    assert [ordinary(n) for n in cycle_overlap['path'][:-1]] == cycle_overlap['path'][1:]
    return {'scope': 'complete stated finite ranges; no asymptotic density conclusion',
            'counts': dict(counts), 'bounded_fibre_targets': [1, 32],
            'bounded_fibre_depths': [0, 8], 'ordinary_sources': [1, 4096],
            'terminal_mark_targets': [1, 32], 'doubling_exponents': [1, 10],
            'branch_partition_cutoffs': [1, 8], 'basin_transport_thresholds': thresholds,
            'periodic_overlap_witness': cycle_overlap}


def build_lean(cache):
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    cached = {}
    cache_manifest_hash = None
    if cache is not None:
        manifest = cache / 'build-manifest.json'
        data = json.loads(manifest.read_text())
        assert data['lean_version'] == version
        cache_manifest_hash = digest(manifest)
        cached = {row['source']: row for row in data['builds']}
    records = []
    with tempfile.TemporaryDirectory(prefix='collatz-predecessor-flow-') as directory:
        build = Path(directory)
        env = dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1')
        for source in [*DEPENDENCIES, SOURCE]:
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            reused = cache is not None and source in DEPENDENCIES
            start = time.monotonic()
            if reused:
                row = cached[source]
                old_obj, old_log = cache / (stem + '.olean'), cache / (stem + '.log')
                assert row['returncode'] == 0 and row['source_sha256'] == digest(ROOT / source)
                assert row['olean_sha256'] == digest(old_obj)
                assert row['log_sha256'] == digest(old_log)
                shutil.copyfile(old_obj, obj)
                log.write_text(old_log.read_text())
                # Older cache manifests record hashes but no original command.
                # Do not present an inferred command as an executed compilation.
                command = row.get('command')
            else:
                command = ['lean', '-o', str(obj), source]
                p = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
                log.write_text(p.stdout)
                assert p.returncode == 0, p.stdout
            output = log.read_text()
            assert not any(s in output for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
                assert {name for name, _ in blocks} == {'BoundedHitFibres.' + t for t in THEOREMS}
                assert len(blocks) == len(THEOREMS)
                for name, axioms in blocks:
                    assert {s.strip() for s in axioms.split(',')} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, (name, axioms)
            records.append({'source': source, 'source_sha256': digest(ROOT / source),
                            'command': command, 'returncode': 0,
                            'elapsed_seconds': round(time.monotonic() - start, 3),
                            'reused_verified_build': reused,
                            'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                            'olean_sha256': digest(obj), 'native_computation_used': False})
            print(f'Lean passed: {source}' + (' (validated dependency reused)' if reused else ''), flush=True)
    return version, records, cache_manifest_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-build-dir', type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    version, builds, cache_hash = build_lean(args.reuse_build_dir)
    replay = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    prior = 'results/density-to-pointwise/written-review.json'
    previous = json.loads((ROOT / prior).read_text())
    for path, expected in previous['sha256'].items():
        assert digest(ROOT / path) == expected, path
    files = [SOURCE, *DEPENDENCIES, Path(__file__).name,
             'docs/PREDECESSOR-DENSITY-FLOW.md', 'docs/DENSITY-TO-POINTWISE.md',
             prior, 'results/predecessor-density-review/verification.json',
             'results/predecessor-density-flow/replay.json', *[r['log'] for r in builds]]
    result = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
        'reused_build_manifest_sha256': cache_hash,
        'kernel_scope': ['Exact bounded-time shortcut predecessor list membership.',
                         'At most 2^(k+1)-1 distinct starts hit a positive target by time k.',
                         'First-hit uniqueness and one-step recursion.',
                         'Ordinary predecessor arithmetic and basin decomposition.',
                         'Disjoint immediate predecessor basins at a nonperiodic root.'],
        'written_scope': ['Limiting first-passage location laws and vanishing maximum atom.',
                          'Predecessor densities tend to zero at infinity within each fixed basin.',
                          'Doubling-ray tail decay and the countable inverse Syracuse flow at a nonperiodic odd root.'],
        'python_scope': replay,
        'dependencies': {'uniform_first_passage': 'Written Proposition 4.1, not kernel checked.',
                         'early_valuation_and_overshoot': 'Written deduction using Tao Proposition 1.9 and Chernoff.',
                         'external_PLD': 'Independently replayed 389-module proof; used for positivity and comparison with divergent component mass.'},
        'not_proved': ['Uniform decay over all targets in all basins at once.',
                       'Density-one convergence, exclusion of every cycle, or exclusion of divergence.',
                       'Kernel verification of the analytic limits or infinite branch sums.'],
        'sha256': {path: digest(ROOT / path) for path in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'kernel_theorems': len(THEOREMS),
                      'finite_checks': replay['counts'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
