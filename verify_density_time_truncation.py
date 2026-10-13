"""Verify finite ordinary-Collatz fibres and time-truncation examples.

The density spectrum and limiting defects are written mathematics, not
consequences of these finite samples. No divergent Collatz orbit is claimed.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from functools import lru_cache
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
OUT = ROOT / 'results/density-time-truncation'
SOURCE = 'lean/DensityTimeTruncation.lean'
THEOREMS = ['two_step_predecessor_iff', 'mem_parentsTwo', 'parentsTwo_length',
            'mem_fibre', 'fibre_length', 'count_binary_bound', 'count_shift',
            'count_residue', 'twelve_step_residue_bound', 'twelve_step_bound',
            'twelve_step_witness', 'twelve_step_witness_nodup',
            'count_composition_bound', 'repeated_block_bound', 'all_depth_bound',
            'nodup_length_le_of_subset', 'distinct_fibre_bound']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ordinary(n):
    return 3 * n + 1 if n % 2 else n // 2


def one_step_parents(a):
    return [2 * a] + ([(a - 1) // 3] if a % 6 == 4 else [])


def inverse_set(a, steps):
    level = {a}
    for _ in range(steps):
        new = [n for b in level for n in one_step_parents(b)]
        assert len(new) == len(set(new))
        assert all(ordinary(n) in level for n in new)
        level = set(new)
    return level


@lru_cache(None)
def count(k, a):
    if k == 0:
        return 1
    extra = count(k - 1, (2 * a - 1) // 3) if a % 3 == 2 else (
        count(k - 1, 2 * ((a - 1) // 3)) if a % 6 == 4 else 0)
    return count(k - 1, 4 * a) + extra


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


def integer_hit_bound(T):
    return sum((1 << (((j % 12) + 1) // 2)) * 38 ** (j // 12)
               for j in range(T + 1))


def finite_checks():
    totals = Counter()
    residue_rows, lift_rows, forward_rows = [], [], []
    for k in range(1, 7):
        period = 2 * 3 ** k
        values = []
        for a in range(period):
            exact = inverse_set(a, 2 * k)
            assert count(k, a) == len(exact), (k, a)
            assert all(n <= (1 << (2 * k)) * a for n in exact)
            values.append(len(exact))
            totals['residue_fibres_checked_by_one_step_inversion'] += 1
            totals['inverse_sources_checked'] += len(exact)
        maximum = max(values)
        witness = values.index(maximum)
        residue_rows.append({'ordinary_steps': 2 * k, 'target_period': period,
                             'maximum_fibre_size': maximum, 'least_residue_witness': witness,
                             'counts_sha256': hashlib.sha256(json.dumps(values).encode()).hexdigest()})
        selected = sorted(set(range(0, period, max(1, period // 32))) | {period - 1, witness})
        for a in selected:
            for q in (1, 17, (1 << 65) + 17):
                lifted = a + period * q
                actual = inverse_set(lifted, 2 * k)
                assert len(actual) == values[a] == count(k, lifted), (k, a, q)
                totals['lifted_residue_checks'] += 1
        lift_rows.append({'ordinary_steps': 2 * k, 'residues_checked': len(selected),
                          'quotients': [1, 17, (1 << 65) + 17]})
        count.cache_clear()
    assert residue_rows[-1]['maximum_fibre_size'] == 38
    assert residue_rows[-1]['least_residue_witness'] == 364
    witness = sorted(inverse_set(364, 12))
    assert len(witness) == 38 and len(set(witness)) == 38

    # n <= 2^t a follows at every inverse ordinary step. Thus these
    # forward enumerations cover every possible source for a <= 64.
    for k in range(7):
        end = 64 * (1 << (2 * k))
        found = {a: set() for a in range(65)}
        for n in range(end + 1):
            x = n
            for _ in range(2 * k):
                x = ordinary(x)
                totals['independent_forward_steps'] += 1
            if x <= 64:
                found[x].add(n)
            totals['independent_forward_sources'] += 1
        for a in range(65):
            assert found[a] == inverse_set(a, 2 * k), (k, a)
            assert len(found[a]) == count(k, a)
            totals['complete_forward_fibre_comparisons'] += 1
        forward_rows.append({'ordinary_steps': 2 * k, 'targets': [0, 64],
                             'complete_source_interval': [0, end]})

    repeated_rows = []
    for k in range(19):
        bound = (1 << (k % 6)) * 38 ** (k // 6)
        for a in (1, 5, 27, 40, 364):
            actual = inverse_set(a, 2 * k)
            assert len(actual) == count(k, a) <= bound, (k, a)
            totals['all_depth_composition_checks'] += 1
        repeated_rows.append({'ordinary_steps': 2 * k, 'certified_bound': bound})
        count.cache_clear()

    cutoffs = [256, 1024, 4096]
    paths = {n: complete_path(n) for n in range(1, max(cutoffs) + 1)}
    totals['complete_convergent_sources'] = len(paths)
    totals['complete_path_distinct_vertices_with_multiplicity'] = sum(map(len, paths.values()))
    clock_rows = []
    for X in cutoffs:
        full = Counter()
        for n in range(1, X + 1):
            full.update(paths[n])
        final_time = max(len(paths[n]) - 1 for n in range(1, X + 1))
        clocks = sorted(set([0, 4, 12, 24, 48, 96, 192, final_time]))
        previous = X + 1
        for T in clocks:
            partial = Counter()
            for n in range(1, X + 1):
                partial.update(paths[n][:T + 1])
            differences = {a: full[a] - partial[a] for a in full}
            assert all(0 <= value <= X for value in differences.values())
            defect = max(differences.values())
            assert defect <= previous
            previous = defect
            largest_hit = max(partial.values())
            bound = integer_hit_bound(T)
            assert largest_hit <= bound < 195 * 38 ** (T // 12)
            assert defect >= full[1] - partial[1]
            if T >= final_time:
                assert defect == 0 and partial == full
            target = min(a for a in full if differences[a] == defect)
            totals['finite_population_target_comparisons'] += len(full)
            clock_rows.append({'source_cutoff': X, 'ordinary_clock': T,
                               'defect_numerator': defect, 'defect_denominator': X,
                               'least_maximizing_target': target,
                               'largest_finite_hit_count': largest_hit,
                               'integer_union_fibre_bound': bound,
                               'complete_orbit_cover_time': final_time})
        assert previous == 0
    return {'scope': 'Exact finite arithmetic for ordinary Collatz; no asymptotic or infinite-orbit classification.',
            'counts': dict(totals), 'residue_maxima': residue_rows,
            'twelve_step_distinct_witness_sources': witness,
            'lift_checks': lift_rows, 'complete_forward_enumeration': forward_rows,
            'all_depth_checks': {'targets': [1, 5, 27, 40, 364], 'bounds': repeated_rows},
            'finite_clock_defects': clock_rows,
            'clock_target_scope': 'All targets reached by each complete sample; all other full and truncated counts are zero.'}


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
    with tempfile.TemporaryDirectory(prefix='collatz-density-time-truncation-') as directory:
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
                assert {n for n, _ in found} == {'DensityTimeTruncation.' + t for t in THEOREMS}
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
    prior = ['results/uniform-predecessor-approximation/verification.json',
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
    files = [SOURCE, 'CollatzContradiction.lean', Path(__file__).name,
             'docs/DENSITY-TIME-TRUNCATION.md', 'docs/UNIFORM-PREDECESSOR-APPROXIMATION.md',
             'docs/DENSITY-TO-POINTWISE.md', 'docs/NATURAL-DENSITY-ALMOST-BOUNDED.md',
             'results/predecessor-density-review/verification.json', *prior,
             'results/density-time-truncation/replay.json', *[b['log'] for b in builds]]
    result = {'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'collatz_status': 'unresolved', 'map_scope': 'Ordinary positive-integer Collatz.',
              'lean_version': version, 'builds': builds, 'kernel_theorems': len(THEOREMS),
              'reused_build_manifest_sha256': cache_hash, 'prior_hashes_validated': prior_counts,
              'kernel_scope': ['Exact two-step inverse branches and complete finite inverse lists.',
                               'Inverse count periodicity modulo 2*3^k at time 2*k.',
                               'At most 38 distinct twelve-step predecessors, attained at target 364.',
                               'Composition and the all-depth even-time bound 2^(k mod 6)*38^(k/6).'],
              'written_scope': ['The bounded-hit estimate 195*38^(T/12) and necessary logarithmic clock.',
                                'Positive accumulation values of r_a are precisely divergent component masses.',
                                'Exact eventual finite-population truncation defect equals the largest divergent component fraction.',
                                'The two iterated limits of the defect and the unresolved existence of a vanishing-defect clock.'],
              'python_scope': replay,
              'dependencies': {'density_limits': 'Written first-passage adaptation and its uniform-target and component-law consequences; not kernel checked.',
                               'positive_component_masses': 'External predecessor theorem, independently replayed earlier; not rebuilt here.'},
              'not_proved': ['A clock producing vanishing uniform time-truncation error.',
                             'Global decay r_a -> 0 or exclusion of divergent positive orbits.',
                             'Exclusion of nontrivial cycles or the full Collatz conjecture.',
                             'Kernel verification of the density limits, accumulation spectrum, or limit exchanges.'],
              'sha256': {name: digest(ROOT / name) for name in files}}
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'kernel_theorems': len(THEOREMS),
                      'finite_checks': replay['counts'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
