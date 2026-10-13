"""Check a sparse altered map, not a counterexample to actual Collatz.

Fresh kernel builds, exact finite replay, and prior external evidence are
recorded separately. Passage-law stability and density limits are written.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/sparse-collatz-perturbation'
SOURCE = 'lean/SparseCollatzPerturbation.lean'
THEOREMS = ['spine_power', 'partner_between', 'swap_involutive', 'swap_parity',
            'unchanged_below', 'step_spine', 'step_partner', 'escape_even',
            'escape_odd', 'escape_never_one', 'differs_from_collatz', 'known_cycle',
            'hits_spine_never_one', 'unchanged_prefix', 'predecessor_iff',
            'multiple_three_fibre', 'old_trap_closed', 'unchanged_safe_basin',
            'safe_ancestor', 'inherited_unit_basin']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def original(n):
    return 3 * n + 1 if n & 1 else n // 2


def original_shortcut(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def spine(j):
    return ((1 << (6 * j + 16)) - 1) // 3


def partner(j):
    return (2 * spine(j + 1) - 1) // 3


def swap(t, n):
    """Finite search through increasing pairs, independent of Lean choice."""
    a = spine(t)
    while a <= n:
        next_a = 64 * a + 21
        b = (2 * next_a - 1) // 3
        if n == a:
            return b
        if n == b:
            return a
        a = next_a
    return n


def altered(t, n):
    return original(swap(t, n))


def altered_shortcut(t, n):
    return original_shortcut(swap(t, n))


def spine_index(n):
    q = 3 * n + 1
    if q > 0 and q & (q - 1) == 0:
        e = q.bit_length() - 1
        if e >= 16 and (e - 16) % 6 == 0:
            return (e - 16) // 6
    return None


def modifications(t, bound):
    rows = []
    j = t
    while spine(j) <= bound:
        rows.append(spine(j))
        if partner(j) <= bound:
            rows.append(partner(j))
        j += 1
    return rows


def structural_checks():
    counts = Counter()
    for j in range(128):
        a, b, nxt = spine(j), partner(j), spine(j + 1)
        assert nxt == 64 * a + 21 and 3 * a + 1 == 4 ** (3 * j + 8)
        assert a % 12 == 5 and b % 4 == 3 and a < b < nxt
        assert original(a) == 4 ** (3 * j + 8)
        assert original(b) == 2 * nxt
        for t in (0, j, j + 1):
            assert swap(t, swap(t, a)) == a
            assert swap(t, swap(t, b)) == b
            assert altered(t, a) == (2 * nxt if j >= t else original(a))
            assert altered(t, b) == (4 ** (3 * j + 8) if j >= t else original(b))
            counts['large_index_swap_cases'] += 1
    for t in (0, 1, 4):
        for bits in range(1, 1025):
            bound = (1 << bits) - 1
            support = modifications(t, bound)
            assert len(support) == len(set(support))
            assert len(support) <= 2 * (1 + (bound.bit_length() - 1) // 6)
            assert all(altered(t, n) != original(n) for n in support)
            counts['sparse_support_cutoffs'] += 1
        x = spine(t)
        for k in range(256):
            expected = spine(t + k // 2) if k % 2 == 0 else 2 * spine(t + k // 2 + 1)
            assert x == expected and x > 1
            x = altered(t, x)
            counts['escaping_path_states'] += 1
    maximum = steps = 0
    for n in range(1, 65):
        x = n
        while x != 1:
            assert x < spine(0) and altered(0, x) == original(x)
            maximum = max(maximum, x)
            steps += 1
            x = original(x)
        counts['unchanged_base_sources'] += 1
    assert maximum == 9232
    return {'counts': dict(counts), 'base_maximum_state': maximum,
            'base_direct_steps': steps, 'first_spine': [spine(j) for j in range(4)],
            'first_partners': [partner(j) for j in range(4)]}


def inverse_checks():
    raw_cutoff, shortcut_cutoff = 65536, 32768
    source_cutoff = 16 * raw_cutoff + 16
    raw_seen, shortcut_seen = defaultdict(list), defaultdict(list)
    changed = []
    for n in range(1, source_cutoff + 1):
        s = swap(0, n)
        assert swap(0, s) == n and s % 2 == n % 2
        if s != n:
            changed.append(n)
        a = original(s)
        if a <= raw_cutoff:
            raw_seen[a].append(n)
        u = a // 2 if n & 1 else a
        if u <= shortcut_cutoff:
            shortcut_seen[u].append(n)
    assert changed == modifications(0, source_cutoff)
    for a in range(1, raw_cutoff + 1):
        expected = [2 * a]
        if a % 6 == 4:
            expected.append(swap(0, (a - 1) // 3))
        assert all(n <= source_cutoff for n in expected)
        assert sorted(expected) == raw_seen[a], a
        if a % 3 == 0:
            assert raw_seen[a] == [2 * a]
    for a in range(1, shortcut_cutoff + 1):
        expected = [2 * a]
        if a % 3 == 2:
            expected.append(swap(0, (2 * a - 1) // 3))
        assert all(n <= source_cutoff for n in expected)
        assert sorted(expected) == shortcut_seen[a], a
    return {'enumerated_sources': source_cutoff, 'ordinary_targets': raw_cutoff,
            'shortcut_targets': shortcut_cutoff, 'changed_sources_in_enumeration': changed,
            'scope': 'Forward enumeration agrees with both exact inverse formulas over these cutoffs; the universal formulas are kernel results.'}


def safe_ancestor_checks():
    counts = Counter()
    roots = list(range(1, 8193)) + [2 ** k + d for k in (64, 128, 256) for d in (0, 1, 5)]
    for a in roots:
        if a % 3 == 0:
            continue
        e = next(e for e in range(6, 12) if (2 ** e * a) % 9 == 4)
        c = (2 ** e * a - 1) // 3
        assert c > 1 and c % 12 == 1 and 3 * c + 1 == 2 ** e * a
        for t in (0, 1, 4):
            x = c
            for _ in range(e + 1):
                x = altered(t, x)
            assert x == a, (t, a, c)
            counts['safe_ancestor_paths'] += 1
    for n in range(1, 4097):
        path, x = [n], n
        while x != 1:
            x = original(x)
            path.append(x)
            assert len(path) < 10000
        good = [i for i, c in enumerate(path) if c > 1 and c % 12 == 1]
        counts['safe_target_occurrences'] += len(good)
        if good:
            x = n
            for i in range(max(good) + 1):
                assert x == path[i], (n, i)
                x = altered(0, x)
                counts['unchanged_safe_prefix_states'] += 1
    return dict(counts)


def classify_finite():
    cutoff = 1 << 18
    # label 0 reaches one; label 1 enters the kernel-proved escaping family.
    rows = {1: (0, 0)}
    for n in range(1, cutoff + 1):
        x, path, seen = n, [], set()
        while x not in rows:
            j = spine_index(x)
            if j is not None:
                rows[x] = (1, 0)
                break
            assert x not in seen, ('unclassified cycle', n, x)
            assert len(path) < 10000, ('unresolved path', n)
            seen.add(x)
            path.append(x)
            x = altered(0, x)
        label, time_to_mark = rows[x]
        for x in reversed(path):
            time_to_mark += 1
            rows[x] = (label, time_to_mark)
    for n, (label, t) in rows.items():
        if t == 0:
            assert (n == 1 and label == 0) or (spine_index(n) is not None and label == 1)
        else:
            next_label, next_time = rows[altered(0, n)]
            assert label == next_label and t == next_time + 1
    direct_steps = 0
    for n in range(1, 4097):
        x, t = n, 0
        while x != 1 and spine_index(x) is None:
            x = altered(0, x)
            t += 1
            assert t < 10000
        assert rows[n] == (int(x != 1), t)
        direct_steps += t
    populations = []
    for bits in (6, 10, 14, 16, 18):
        X = 1 << bits
        escape = sum(rows[n][0] for n in range(1, X + 1))
        populations.append({'cutoff': X, 'proved_escape_sources': escape,
                            'proved_one_sources': X - escape})
    return {'source_cutoff': cutoff, 'checked_state_rows': len(rows),
            'direct_sources': 4096, 'direct_steps': direct_steps,
            'populations': populations, 'scope': 'Finite exact classification using a proved infinite tail; no density value is inferred.'}


def prefix_coupling_checks():
    X, depth = 65536, 12
    raw = list(range(1, X + 1))
    mod = raw.copy()
    word_raw, word_mod = [0] * X, [0] * X
    bad = [False] * X
    rows = []
    for k in range(1, depth + 1):
        for i in range(X):
            word_raw[i] |= (raw[i] & 1) << (k - 1)
            word_mod[i] |= (mod[i] & 1) << (k - 1)
            bad[i] |= swap(0, raw[i]) != raw[i]
            raw[i] = original_shortcut(raw[i])
            mod[i] = altered_shortcut(0, mod[i])
            if not bad[i]:
                assert raw[i] == mod[i] and word_raw[i] == word_mod[i]
            if mod[i] % 3 == 0:
                assert i + 1 == 2 ** k * mod[i]
        histogram_raw = Counter(word_raw)
        histogram_mod = Counter(word_mod)
        assert set(histogram_raw.values()) == {X // 2 ** k}
        discrepancy_twice = sum(abs(histogram_raw[w] - histogram_mod[w]) for w in range(2 ** k))
        bad_count = sum(bad)
        support = len(modifications(0, (1 << k) * X))
        upper = support * ((1 << k) - 1)
        assert discrepancy_twice <= 2 * bad_count and bad_count <= upper
        rows.append({'depth': k, 'sources_with_old_prefix_modification': bad_count,
                     'histogram_l1_count': discrepancy_twice,
                     'inverse_fibre_union_bound': upper,
                     'modified_inputs_below_envelope': support})
    return {'source_cutoff': X, 'depth': depth, 'checked_source_steps': X * depth,
            'rows': rows, 'scope': 'Exact finite prefix coupling; the growing-floor asymptotic and fixed-depth limits are written arguments.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-sparse-perturbation-') as directory:
        for source in ['CollatzContradiction.lean', SOURCE]:
            obj = Path(directory) / (Path(source).stem + '.olean')
            log = OUT / (Path(source).stem + '.log')
            cmd = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(s in p.stdout for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            reports = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
            assert reports
            for name, axioms in reports:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, name
            if source == SOURCE:
                assert len(reports) == len(THEOREMS)
                assert {n for n, _ in reports} == {'SparseCollatzPerturbation.' + n for n in THEOREMS}
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': cmd, 'returncode': p.returncode, 'fresh_build': True,
                           'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic() - start, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean passed:', source, flush=True)
    return version, builds


def external_evidence():
    name = 'results/predecessor-density-review/verification.json'
    record = json.loads((ROOT / name).read_text())
    assert record['status'] == 'passed' and not record['density_one_convergence_proved']
    # Revalidate the local artifacts from the completed replay, without rebuilding it.
    assembled = Path(record['assembled'])
    for b in record['builds']:
        source = assembled / (b['module'].replace('.', '/') + '.lean')
        obj = Path(b['command'][b['command'].index('-o') + 1])
        assert digest(source) == b['source_sha256'], source
        assert digest(ROOT / b['log']) == b['log_sha256'], b['log']
        assert digest(obj) == b['olean_sha256'], obj
    return {'record': name, 'record_sha256': digest(ROOT / name),
            'status': record['status'], 'finished_at_utc': record['finished_at_utc'],
            'revalidated_module_artifact_triples': len(record['builds']),
            'recompiled': False, 'axiom_lines': record['axiom_lines']}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = 'results/prefix-coalescence/verification.json'
    prior_data = json.loads((ROOT / prior).read_text())
    for p, h in prior_data['sha256'].items():
        assert digest(ROOT / p) == h, p
    external = external_evidence()
    print('Prior external replay artifacts revalidated:', external['revalidated_module_artifact_triples'], flush=True)
    version, builds = build_lean()
    replay = {}
    for name, check in [('structure', structural_checks), ('inverse', inverse_checks),
                        ('safe_ancestors', safe_ancestor_checks), ('classification', classify_finite),
                        ('prefix_coupling', prefix_coupling_checks)]:
        replay[name] = check()
        print('Exact replay passed:', name, flush=True)
    replay_path = OUT / 'replay.json'
    replay_path.write_text(json.dumps(replay, indent=2) + '\n')
    dependencies = [SOURCE, 'CollatzContradiction.lean', Path(__file__).name,
                    'docs/SPARSE-COLLATZ-PERTURBATION.md', 'docs/NATURAL-DENSITY-ALMOST-BOUNDED.md',
                    'docs/PREDECESSOR-DENSITY-REVIEW.md', 'docs/FINITE-PATH-PACKING.md', prior,
                    external['record'], str(replay_path.relative_to(ROOT)),
                    *[b['log'] for b in builds]]
    record = {'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
              'audited_kernel_theorems': THEOREMS, 'external_predecessor_input': external,
              'prior_artifact_hashes_revalidated': len(prior_data['sha256']),
              'kernel_scope': ['An explicitly altered map with an all-depth escaping path and the unchanged known cycle.',
                               'An involution of odd inputs, exact inverse branches, and pure-doubling fibres at multiples of three.',
                               'Agreement below an arbitrarily large threshold and exact transport of safe original basins.',
                               'Every unit target of the altered map contains a whole original unit-target predecessor basin.'],
              'written_scope': ['Positive predecessor lower density at every altered-map unit target, inherited from external PLD.',
                                'Positive lower density of both convergence and escape for the altered map.',
                                'A logarithmically sparse set of changed inputs; zero predecessor density at multiples of three.',
                                'Conditional stability of the large-floor first-passage estimates under the sparse changes.',
                                'Fixed-depth parity frequencies and finite-path packing persist, with the stated scopes.'],
              'finite_scope': {'structure': replay['structure']['counts'], 'inverse': replay['inverse'],
                               'safe_ancestors': replay['safe_ancestors'],
                               'classification': replay['classification'],
                               'prefix_source_steps': replay['prefix_coupling']['checked_source_steps']},
              'not_proved': ['A positive-integer counterexample or complete proof for the ACTUAL Collatz map.',
                             'Density one of actual Collatz convergence, or an estimate excluding its divergent components.',
                             'An unconditional or kernel-checked natural-density first-passage theorem.',
                             'An exact asymptotic convergence or escape fraction for the altered map.'],
              'sha256': {p: digest(ROOT / p) for p in dependencies}}
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({'status': 'passed', 'kernel_theorem_roots': len(THEOREMS),
                      'finite_scope': record['finite_scope'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
