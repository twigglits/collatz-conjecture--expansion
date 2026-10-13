"""Exact stopped-gap and balanced-coalescence checks for shortcut Collatz.

The all-depth harmonic lower bounds are kernel proved. The stronger
random-walk comparison and the weighted dyadic criterion are written
arguments, not consequences inferred from this finite enumeration.
"""

from array import array
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import comb
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/coalescence-tail'
SOURCE = 'lean/CoalescenceTail.lean'
THEOREMS = [
    'weight_lift', 'weight_snoc', 'weight_le_length', 'gap_lift',
    'alive_lift', 'alive_gap_ne', 'stopped_of_alive', 'stopped_of_dead',
    'endpoint_parity_flip', 'gap_snoc', 'gap_snoc_lift', 'absolute_pair',
    'stopped_children', 'stopped_bound', 'balanced_lift', 'orbit_snoc',
    'balanced_persists', 'stopped_zero_of_equal_weight',
    'stopped_bound_unmerged', 'stopped_mass', 'harmonic_tail',
    'stopped_parity_mass', 'parity_harmonic_tail',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    return [x.numerator, x.denominator]


def shortcut(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def direct(depth, n):
    """Two actual integer trajectories, without affine lifts or a residue tree."""
    x, y, wx, wy, live = n, n + 1, 0, 0, True
    gaps = []
    for _ in range(depth):
        wx += x & 1
        wy += y & 1
        x, y = shortcut(x), shortcut(y)
        live = live and wx != wy
        gaps.append(wx - wy)
    return (x, y, wx, wy, int(live)), gaps


def finite_checks(max_depth=20):
    counts, rows = Counter(), []
    prior = json.loads((ROOT / 'results/prefix-coalescence/replay.json').read_text())
    prior_counts = {p['shortcut_depth']: p['coalescing_adjacent_residues']
                    for p in prior['complete_periods']['periods']}
    states = [array('Q', [0]), array('Q', [1]), array('B', [0]),
              array('B', [0]), array('B', [1])]
    reactivation = None
    for depth in range(1, max_depth + 1):
        parent_depth, size = depth - 1, 1 << (depth - 1)
        child = [array(kind, [0]) * (2 * size) for kind in ('Q', 'Q', 'B', 'B', 'B')]
        powers = [3 ** w for w in range(depth)]
        for r in range(size):
            a, b, u, v, live = (column[r] for column in states)
            parent_gap = abs(u - v) if live else 0
            child_mass = 0
            parent_balanced = a == b and u == v
            for bit in (0, 1):
                x, y = a + bit * powers[u], b + bit * powers[v]
                uu, vv = u + (x & 1), v + (y & 1)
                aa, bb = shortcut(x), shortcut(y)
                alive = int(bool(live) and uu != vv)
                index = r + bit * size
                for column, value in zip(child, (aa, bb, uu, vv, alive)):
                    column[index] = value
                if parent_balanced:
                    assert aa == bb and uu == vv
                    counts['balanced_child_persistence'] += 1
                child_mass += abs(uu - vv) if alive else 0
                assert uu - vv == u - v + (x & 1) - (y & 1)
                if bit:
                    assert (x & 1, y & 1) == (1 - (a & 1), 1 - (b & 1))
                    counts['affine_parity_flip_pairs'] += 1
            if parent_depth:
                assert child_mass == 2 * parent_gap
                counts['local_stopped_mass_identities'] += 1
        states = child
        mass, survivors, merged, unstopped = [0, 0], [0, 0], [0, 0], [0, 0]
        hist = Counter()
        for r in range(2 * size):
            a, b, u, v, live = (column[r] for column in states)
            g = abs(u - v) if live else 0
            balanced = a == b and u == v
            assert 0 <= g <= depth * (not balanced)
            mass[r & 1] += g
            survivors[r & 1] += bool(g)
            merged[r & 1] += balanced
            unstopped[r & 1] += abs(u - v)
            hist[g] += 1
            counts['pointwise_gap_bounds'] += 1
            if reactivation is None and not live and u != v:
                _, history = direct(depth, r)
                assert 0 in history and history[-1] != 0
                reactivation = {'depth': depth, 'residue': r, 'signed_gaps': history}
        assert mass == [size, size]
        for parity in (0, 1):
            assert depth * (size - merged[parity]) >= size
            assert survivors[parity] >= comb(depth - 1, (depth - 1) // 2)
        assert sum(merged) == prior_counts[depth]
        sample = set(range(min(2 * size, 1 << 12)))
        sample.update(((7919 * j + 104729) % (2 * size)) for j in range(1024))
        sample.update((2 * size - 1, 2 * size - 2))
        for r in sorted(sample):
            observed, _ = direct(depth, r)
            assert observed == tuple(column[r] for column in states)
            counts['independent_direct_pair_paths'] += 1
        for r in sorted({0, 1, size - 1, size, 2 * size - 2, 2 * size - 1}):
            base, _ = direct(depth, r)
            for q in (1, 3, 29, 1 << 20):
                lifted, _ = direct(depth, (1 << depth) * q + r)
                assert lifted[:2] == (base[0] + 3 ** base[2] * q,
                                      base[1] + 3 ** base[3] * q)
                assert lifted[2:] == base[2:]
                assert (base[0] == base[1] and base[2] == base[3]) == (
                    lifted[0] == lifted[1] and lifted[2] == lifted[3])
                counts['independent_lifted_pair_paths'] += 1
        rows.append({
            'shortcut_depth': depth, 'residue_period': 2 * size,
            'stopped_gap_mass_by_initial_parity': mass,
            'stopped_survivors_by_initial_parity': survivors,
            'balanced_coalescence_by_initial_parity': merged,
            'unmerged_proportion': ratio(Fraction(2 * size - sum(merged), 2 * size)),
            'harmonic_lower_bound': ratio(Fraction(1, depth)),
            'written_random_walk_lower_bound': ratio(Fraction(
                comb(depth - 1, (depth - 1) // 2), 1 << (depth - 1))),
            'unstopped_absolute_gap_mass_by_initial_parity': unstopped,
            'stopped_gap_histogram': dict(sorted(hist.items())),
        })
        print('Exact residue tree and independent paths passed:', depth, flush=True)
    assert reactivation is not None
    return {'scope': 'Finite exact checks through depth 20, with direct trajectory samples and separate affine residue recursion.',
            'counts': dict(counts), 'rows': rows,
            'why_the_gap_must_be_stopped': reactivation}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-coalescence-tail-') as directory:
        build = Path(directory)
        for source in ('CollatzAffine.lean', SOURCE):
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
                assert {name for name, _ in found} == {'CoalescenceTail.' + t for t in THEOREMS}
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
    prior = ['results/prefix-coalescence/verification.json',
             'results/weighted-dissipation/verification.json']
    prior_counts = {}
    for record in prior:
        data = json.loads((ROOT / record).read_text())
        assert data['status'] == 'passed'
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (record, path)
        prior_counts[record] = len(data['sha256'])
    version, builds = build_lean()
    finite = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(finite, indent=2) + '\n')
    files = ['CollatzAffine.lean', SOURCE, Path(__file__).name,
             'docs/COALESCENCE-TAIL.md', 'docs/WEIGHTED-DISSIPATION.md',
             'docs/PREFIX-COALESCENCE-AUDIT.md', *prior,
             'results/prefix-coalescence/replay.json', 'results/coalescence-tail/replay.json',
             *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'passed', 'collatz_status': 'unresolved',
        'map_scope': 'Actual shortcut Collatz on nonnegative residue representatives; positive lifts retain their exact properties.',
        'lean_version': version, 'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': prior_counts,
        'kernel_scope': [
            'All-depth exact affine odd-count periodicity and simultaneous endpoint parity flips.',
            'Balanced coalescence is periodic and persists with depth.',
            'Stopped absolute-gap mass equals the residue-period length at every positive depth.',
            'The same unit mean holds conditioned on either initial parity.',
            'At least 1/H of each whole period, and of each parity half, is unmerged at depth H.',
        ],
        'written_scope': [
            'The complete-period coalescence errors are not summable, and Haar balanced-fusion time has infinite expectation.',
            'Coupling the changing gap to a simple symmetric walk gives the stronger central-binomial survival lower bound.',
            'Assuming the prior natural mean exists, a summable actual dyadic refinement error would force the infinite-weight mean d to zero.',
            'The whole-period coalescence bounds cannot supply that summable error at depths within the source scale.',
        ],
        'finite_scope': finite['counts'],
        'not_proved': [
            'An upper bound on the actual source-interval refinement error sufficient to make its sum finite.',
            'Any asymptotic upper rate of balanced coalescence, or adoption of an external density-one theorem.',
            'Vanishing infinite-weight mean d, exclusion of other cycles, or full Collatz.',
        ],
        'sha256': {str(path): digest(ROOT / path) for path in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: coalescence tail; full Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
