"""Check an explicitly different integer map, not a Collatz counterexample.

Kernel scope: its known cycle and explicit escaping family.
Written scope: infinite density, passage, and packing formulas.
Python scope: exact finite comparisons, including symbolic infinite tails.
"""
import argparse
from collections import Counter
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/density-countermodel'
SOURCE = 'lean/DensityCountermodel.lean'
THEOREMS = ['even_step', 'cycle_one', 'cycle_four', 'cycle_two', 'spine_lower',
            'spine_step', 'spine_two_steps', 'iterate_add', 'iterate_even',
            'iterate_odd', 'spine_never_one', 'exponent_lower', 'spine_unbounded',
            'differs_from_collatz']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def power(n):
    return n > 0 and n & (n - 1) == 0


def split_odd(n):
    assert n > 0 and n % 2
    c = 3 if n % 4 == 1 else 1
    return c, (n + c) // 4


def split_even(n):
    v = (n & -n).bit_length() - 1
    return v, n >> v


def step(n):
    assert n > 0
    if n % 2 == 0:
        return n // 2
    if n == 1:
        return 4
    c, m = split_odd(n)
    L = m.bit_length() - 1
    if power(m):
        return 2 * (4 * (m // 2) - 3) if c == 3 else 2 * (8 * m - 1)
    r = m - (1 << L)
    h = L + 2 if c == 3 and r == 1 else L - (r.bit_length() - 1) + 1
    return (1 << h) * (4 * r - c)


def spine(k):
    return (4 << k) - 1


def spine_index(n):
    if n % 4 == 3 and power((n + 1) // 4):
        return ((n + 1) // 4).bit_length() - 1
    return None


def trace(n):
    """Finite prefix, then either the known cycle or the proved infinite tail."""
    seen = set()
    while n not in {1, 2, 4}:
        assert n not in seen, ('unexpected cycle', n)
        seen.add(n)
        k = spine_index(n)
        if k is not None:
            return seen, k
        n = step(n)
        assert len(seen) < 10000, 'unclassified trajectory'
    return seen | {1, 2, 4}, None


def trace_hits(data, a):
    seen, k = data
    if a in seen:
        return True
    if k is None:
        return False
    j = spine_index(a)
    if j is not None and j >= k:
        return True
    if a % 2 == 0:
        j = spine_index(a // 2)
        if j is not None and j >= k + 1:
            return True
    return False


def odd_hits(n, a):
    c, m = split_odd(n)
    if a in {1, 2, 4}:
        return c == 3
    v, q = split_even(a)
    d, target = split_odd(q)
    if c != d:
        return False
    k = target.bit_length() - 1
    if v <= 1:
        if power(target):
            hit = m % target == 0 if c == 3 else m % (2 * target) != 0
        else:
            hit = m % (1 << (k + 1)) == target
        return hit and (v == 0 or n != q)
    L = v - 2 if q == 1 else k + v - 1
    return m > target and m % (1 << L) == target


def predicted_hit(n, a):
    _, odd = split_even(n)
    if odd_hits(odd, a):
        return True
    return n % a == 0 and power(n // a)


def density(a):
    v, q = split_even(a)
    c, m = split_odd(q)
    k = m.bit_length() - 1
    if v <= 1:
        if power(m):
            return Fraction(1, 1 << (k + 1)) if c == 3 else Fraction(1, 2) - Fraction(1, 1 << (k + 2))
        return Fraction(1, 1 << (k + 2))
    if q == 1:
        return Fraction(1, 2) if v == 2 else Fraction(1, 1 << (v - 1))
    return Fraction(1, 1 << (k + v))


def parents(a):
    out = [2 * a]
    v, q = split_even(a)
    if not v:
        return out
    c, m = split_odd(q)
    k = m.bit_length() - 1
    if v == 1:
        if power(m) and c == 3:
            out.append(8 * m - 3)
        elif power(m) and c == 1 and m >= 2:
            out.append(2 * m - 1)
    elif q == 1:
        out.append(1 if v == 2 else (1 << v) + 1)
    else:
        out.append(4 * ((1 << (k + v - 1)) + m) - c)
    return out


def passage(n, H):
    seen = set()
    while not (n % 2 and n <= H):
        if spine_index(n) is not None:
            return None
        assert n not in seen
        seen.add(n)
        n = step(n)
        assert len(seen) < 10000
    return n


def passage_formula(n, H):
    assert n % 2 and n > H
    c, m = split_odd(n)
    h = (H + c) // 4
    q = 1 << (h.bit_length() - 1)
    z = m % (2 * q)
    if not z:
        return None if c == 1 else 4 * q - 3
    return 4 * (z if z <= h else z - q) - c


def pair(x):
    return [x.numerator, x.denominator]


def finite_checks():
    counts = Counter()
    for a in range(1, 513):
        actual = [n for n in range(1, 3 * a + 1) if step(n) == a]
        expected = parents(a)
        assert sorted(actual) == sorted(expected) and len(expected) <= 2
        counts['inverse_parent_targets'] += 1
        counts['inverse_source_steps'] += 3 * a
    targets = list(range(1, 1025)) + [spine(k) for k in (20, 40, 80)] + [2 * spine(k) for k in (20, 40, 80)]
    totals = Counter()
    rows = []
    for n in range(1, 8193):
        data = trace(n)
        assert (data[1] is not None) == (split_even(n)[1] % 4 == 3)
        bands = Counter(a.bit_length() - 1 for a in data[0])
        if data[1] is not None:
            k = data[1]
            for j in range(k, max(bands, default=0) + 8):
                for a in ([spine(j)] + ([2 * spine(j)] if j >= k + 1 else [])):
                    if a not in data[0]:
                        bands[a.bit_length() - 1] += 1
        assert max(bands.values()) <= 10
        for a in targets:
            observed = trace_hits(data, a)
            assert observed == predicted_hit(n, a), (n, a, data)
            totals[a] += observed
            counts['trajectory_membership_comparisons'] += 1
        counts['classified_sources'] += 1
        if n in (64, 512, 8192):
            errors = [abs(Fraction(totals[a], n) - density(a)) for a in targets]
            bound = Fraction(8 * n.bit_length(), n)
            assert max(errors) <= bound
            rows.append({'cutoff': n, 'targets_checked': len(targets),
                         'maximum_density_error': pair(max(errors)), 'stated_uniform_bound': pair(bound),
                         'convergent_source_count': totals[1]})
    for a in range(1, 8193):
        assert density(a) >= Fraction(1, 2 * a)
        if a not in {1, 2, 4}:
            assert density(a) == sum((density(n) for n in parents(a)), Fraction())
        counts['density_formula_targets'] += 1
    for k in range(129):
        b, u = spine(k), 4 * spine(k + 1)
        assert step(b) == 2 * spine(k + 1) and step(step(b)) == spine(k + 1)
        assert density(u) == Fraction(1, 1 << (k + 3))
        assert density(u) / density(b) == Fraction(1, b - 1)
        counts['explicit_tail_parameters'] += 1
    passage_rows = []
    for H in (7, 15, 31, 63, 127, 255):
        Q = {c: 1 << (((H + c) // 4).bit_length()) for c in (1, 3)}
        P = 4 * max(Q.values())
        law = Counter()
        for residue in range(1, P, 2):
            n = P + residue
            mark = passage(n, H)
            assert mark == passage_formula(n, H)
            law[mark] += 1
            counts['passage_formula_residues'] += 1
        mass = P // 2
        assert Fraction(max(law.values()), mass) <= Fraction(8, H)
        assert Fraction(law[None], mass) == Fraction(1, 2 * Q[1])
        for Y in (H + 1, H * H, H * H * H):
            observed = Counter()
            for residue in range(1, P, 2):
                weight = (2 * Y - 1 - residue) // P - (Y - 1 - residue) // P
                observed[passage_formula(P + residue, H)] += weight
            size = sum(observed.values())
            tv = sum((abs(Fraction(observed[z], size) - Fraction(law[z], mass))
                      for z in set(observed) | set(law)), Fraction()) / 2
            assert tv <= Fraction(4 * H, Y)
            for offset in range(64):
                n = Y + (Y % 2 == 0) + 2 * offset
                assert passage(n, H) == passage_formula(n, H)
                counts['passage_interval_spot_checks'] += 1
            passage_rows.append({'floor': H, 'source_scale': Y, 'period': P,
                                 'total_variation': pair(tv), 'bound': pair(Fraction(4 * H, Y))})
    return {'scope': 'An explicitly altered map; exact finite comparisons do not assert a Collatz counterexample.',
            'counts': dict(counts), 'density_rows': rows, 'passage_rows': passage_rows,
            'tail_handling': 'Known cycle or explicit symbolic escaping spine, not a fuel-based classification.'}


def build_lean(cache):
    version = subprocess.check_output(['lean', '--version'], text=True, cwd=ROOT).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    cached, cache_hash = {}, None
    if cache:
        data = json.loads((cache / 'build-manifest.json').read_text())
        assert data['lean_version'] == version
        cached = {r['source']: r for r in data['builds']}
        cache_hash = digest(cache / 'build-manifest.json')
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-density-countermodel-') as directory:
        build = Path(directory)
        for source in ['CollatzContradiction.lean', SOURCE]:
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            reused = bool(cache) and source == 'CollatzContradiction.lean'
            if reused:
                old = cached[source]
                for path, key in [(ROOT / source, 'source_sha256'),
                                  (cache / (stem + '.olean'), 'olean_sha256'),
                                  (cache / (stem + '.log'), 'log_sha256')]:
                    assert digest(path) == old[key]
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
                assert {n for n, _ in found} == {'DensityCountermodel.' + t for t in THEOREMS}
                for name, axioms in found:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': 0, 'reused_verified_build': reused,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj), 'native_computation_used': False})
            print('Lean passed:', source, flush=True)
    return version, builds, cache_hash


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-build-dir', type=Path)
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    version, builds, cache_hash = build_lean(args.reuse_build_dir)
    replay = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    sources = [SOURCE, 'CollatzContradiction.lean', Path(__file__).name,
               'docs/DENSITY-COUNTERMODEL.md', 'docs/DENSITY-BRANCH-LEAKAGE.md',
               'results/density-branch-leakage/verification.json',
               'results/density-countermodel/replay.json', *[b['log'] for b in builds]]
    result = {'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
              'collatz_status': 'unresolved', 'map_scope': 'Explicitly altered odd branch; not ordinary Collatz.',
              'lean_version': version, 'builds': builds, 'kernel_theorems': len(THEOREMS),
              'reused_build_manifest_sha256': cache_hash,
              'kernel_scope': ['Ordinary even halving and the 1,4,2 cycle for the comparison map.',
                               'All iterates of the explicit escaping spine, nonarrival at one, and unboundedness.',
                               'The comparison map differs from ordinary Collatz at 3.'],
              'written_scope': ['Complete orbit classification and density formulas for the comparison map.',
                                'Target-uniform density convergence and the lower bound r_a >= 1/(2a).',
                                'Periodic first-passage laws, small atoms, and sparse orbit values.',
                                'Failure of the logarithmic relative branch estimate in this comparison map.'],
              'python_scope': replay,
              'not_proved': ['A counterexample to ordinary positive-integer Collatz.',
                             'The required relative branch estimate for ordinary Collatz.',
                             'Kernel verification of the infinite density, passage, or packing arguments.'],
              'sha256': {name: digest(ROOT / name) for name in sources}}
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'kernel_theorems': len(THEOREMS),
                      'finite_counts': replay['counts'], 'collatz_status': 'unresolved'}, indent=2))


if __name__ == '__main__':
    main()
