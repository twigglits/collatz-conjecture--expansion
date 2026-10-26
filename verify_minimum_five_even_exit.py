"""Verify the contracting adjacent pair and the later d=3 mod4 merger.

Kernel proofs, complete weighted paths, modular-only pure lifts and bounded
inverse trees have distinct scopes. The full Collatz conjecture stays open.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

from verify_minimum_inverse_locality import digest, save, ordinary, paired, inverse_tree
from verify_minimum_five_odd_exit import replay_word
from verify_minimum_seventeen_transition import BRIDGES, CYCLE
from verify_minimum_seventeen_separation import affine_seed
from verify_minimum_seventeen_fourth import SECOND_BRIDGE
from verify_minimum_seventeen_phase import coordinates as base_coordinates, four_windows, secondary_window
from verify_minimum_five_transition import N_BRIDGE, S_BRIDGE, FIVE_CYCLE
from verify_minimum_five_inverse_cone import forward_check

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-five-even-exit'
PRIOR = 'results/minimum-five-inverse-cone/verification.json'
SOURCE = 'lean/MinimumFiveEvenExit.lean'
NOTE = 'docs/MINIMUM-FIVE-EVEN-EXIT.md'
THEOREMS = [
    'adjacent_even_step', 'adjacent_even_blocks', 'even_bridges', 'even_exit_meeting',
    'even_opposite_profiles', 'fourth_third_profile', 'full_even_exit_meeting',
    'even_exit_not_least', 'even_branch_residue', 'exit_residue',
    'pure_even_exit_lift', 'weighted_even_exit_lift', 'build_even_escape',
    'pure_even_escape', 'weighted_even_escape', 'realization_windows',
    'realized_inverse_obstruction', 'even_exit_dichotomy',
    'full_even_opposite_profiles', 'pure_later_escape',
    'even_valuation_profiles', 'three_mod_four_split',
]


def exit_unit(k, t, l, g):
    assert t >= 1 and l >= 1 and g in [1, 3]
    Z, A, V = 1 << (l + 2), 1 << (2 * t + 1), 1 << (2 * t + l + 3)
    y0 = g * pow(pow(3, l + 1, 4), -1, 4) % 4
    z0 = ((1 << l) * y0 - 1) * pow(pow(3, t, Z), -1, Z) % Z
    target = 3 + A * z0
    eps = target * pow(pow(9, k + 1, V), -1, V) % V
    assert 0 < z0 < Z and z0 % 2 and 0 < y0 < 4 and y0 % 2
    assert (1 + pow(3, t, Z) * z0) % Z == (1 << l) * y0
    assert pow(3, l + 1, 4) * y0 % 4 == g
    assert 0 < target < V and target % 8 == 3
    assert 0 < eps < V and eps % 2 and pow(9, k + 1, V) * eps % V == target
    return eps, z0, y0, target


def weight(R, r, j, k, t, l, g, offset=0):
    D, E, T, V = 1 << (57 + 11 * r), 1 << (9 + 11 * j), 1 << (3 * k + 4), 1 << (2 * t + l + 3)
    M = V * D * E * T
    A, c = pow(3, 35 + 7 * r, M), pow(3, 6 + 7 * j, M)
    eps, _, _, _ = exit_unit(k, t, l, g)
    w = (D * E * (1 + T * eps) - c * D - 7 * c * A) * pow(c * A * pow(9, R, M), -1, M) % M
    w += offset * M
    assert w > 0 and w % 2
    return w


def coordinates(R, r, j, k, t, l, g, w):
    starts, ends, clocks, words, a, X = base_coordinates(R, r, w)
    u, rem = divmod(X + 7, 1 << (57 + 11 * r))
    assert rem == 0 and u > 0 and u % 2
    q, rem = divmod(9 * a + 1, 1 << (9 + 11 * j))
    assert rem == 0 and q > 0 and q % 2
    b = 3 ** (6 + 7 * j) * q
    v, rem = divmod(b - 1, 1 << (3 * k + 4))
    assert rem == 0 and v > 0 and v % 2
    d = 9 ** (k + 1) * v
    z, rem = divmod(d - 3, 1 << (2 * t + 1))
    assert rem == 0 and z > 0 and z % 2 and d % 8 == 3
    y, rem = divmod(1 + 3 ** t * z, 1 << l)
    assert rem == 0 and y > 0 and y % 2 and pow(3, l + 1, 4) * y % 4 == g
    assert 0 < starts[3] < starts[0]
    return starts, ends, clocks, words, a, b, v, d, z, y


def local_exit(t, z, l, y, g):
    d = 3 + 2 * 4 ** t * z
    assert 1 + 3 ** t * z == 2 ** l * y and y % 2
    assert pow(3, l + 1, 4) * y % 4 == g
    nw = 'E' + 'EO' * t + 'O' * l
    sw = 'OE' * (t + 1) + 'E' + 'O' * (l - 1)
    if g == 1:
        target = (3 ** (l + 1) * y - 1) // 4
        return d, target, target, nw + 'EE', sw + 'EO'
    h, rem = divmod(3 ** l * y - 1, 4)
    assert rem == 0 and h > 0 and h % 3 == 2
    return d, 9 * h + 2, h, nw + 'EO', sw + 'EE'


def generic_checks(counts):
    for d in range(7, 16384, 4):
        n = d - 3
        K = (n & -n).bit_length() - 1
        z = n >> K
        assert K >= 2 and z > 0 and z % 2
        if K % 2:
            t = K // 2
            assert t >= 1 and d == 3 + 2 * 4 ** t * z
        else:
            t = K // 2 - 1
            assert d == 3 + 4 ** (t + 1) * z
            u = (1 + 3 ** (t + 1) * z) // 2
            assert ordinary(3 * d - 5, 3 * t + 3)[-1] == u
            assert ordinary(2 * d - 5, 3 * t + 7)[-1] == 9 * u - 1
            counts['even_valuation_pairs'] += 1
            counts['even_valuation_steps'] += 6 * t + 10
        counts['three_mod_four_splits'] += 1
    for t in list(range(33)) + [128, 1024]:
        for q in [0, 1, 2, 3, 17]:
            for c in [1, 2]:
                start, end = 4 ** t * q + c, 3 ** t * q + c
                p = ordinary(start, 3 * t)
                assert p[-1] == end and p == paired(start, 3 * t)
                counts['adjacent_block_paths'] += 1
                counts['adjacent_block_steps'] += 3 * t
    params = []
    for t in range(1, 25):
        for z in range(1, 128, 2):
            n = 1 + 3 ** t * z
            l = (n & -n).bit_length() - 1
            y = n >> l
            params.append((t, z, l, y, pow(3, l + 1, 4) * y % 4))
    for t, l in [(1, 128), (128, 1), (128, 128), (1024, 1024), (4096, 16), (16, 4096)]:
        for g in [1, 3]:
            for offset in [0, 1]:
                _, z0, _, _ = exit_unit(0, t, l, g)
                z = z0 + (1 << (l + 2)) * offset
                y, rem = divmod(1 + 3 ** t * z, 1 << l)
                assert rem == 0 and y % 2
                params.append((t, z, l, y, g))
    for t, z, l, y, g in params:
        d, ne, se, nw, sw = local_exit(t, z, l, y, g)
        upper = 2 + 3 ** (t + 1) * z
        nc = replay_word(3 * d - 5, nw, ne, counts, 'local_N_steps', {1 + 3 * t: upper}, True)
        sc = replay_word(2 * d - 5, sw, se, counts, 'local_S_steps', {3 + 3 * t: upper - 1}, True)
        assert nc == 3 * t + 2 * l + (3 if g == 1 else 4)
        assert sc == 3 * t + 2 * l + (5 if g == 1 else 4)
        counts['local_successful_pairs' if g == 1 else 'local_opposite_pairs'] += 1
    return {'regular_t': [1, 24], 'regular_odd_z': [1, 127], 'large_t_l': [[1, 128], [128, 1], [128, 128], [1024, 1024], [4096, 16], [16, 4096]],
            'scope': 'Complete local pairs for both exits, ordinary and paired paths, all prescribed shortcut parities, inverse replay, and the contraction boundary checkpoints.'}


def complete_paths(counts):
    params = [(R, r, j, k, t, l, g, 0) for R in [14, 36] for r in [5, 6]
              for j in [0, 1] for k in [0, 1] for t in [1, 2, 8] for l in [1, 2, 5] for g in [1, 3]]
    params += [(R, r, j, k, t, l, g, 0) for R, r, j, k, t, l in
               [(4096, 5, 1, 1, 128, 128), (36, 128, 128, 128, 128, 128),
                (36, 5, 1, 1, 4096, 16), (36, 5, 1, 1, 16, 4096),
                (36, 5, 1, 4096, 4, 4)] for g in [1, 3]]
    params += [(36, 5, 1, 6, t, l, g, 1) for t in [1, 4] for l in [1, 4] for g in [1, 3]]
    rows, maxima = [], Counter()
    for R, r, j, k, t, l, g, offset in params:
        w = weight(R, r, j, k, t, l, g, offset)
        starts, ends, clocks, words, a, b, v, d, z, y = coordinates(R, r, j, k, t, l, g, w)
        _, ne, se, nw0, sw0 = local_exit(t, z, l, y, g)
        nw = words[0] + SECOND_BRIDGE + CYCLE * j + N_BRIDGE + FIVE_CYCLE * k + nw0
        sw = words[3] + 'O' + BRIDGES[0] + CYCLE * j + S_BRIDGE + FIVE_CYCLE * k + sw0
        nbase = 5 * R + 116 + 18 * r + 18 * j + 5 * k
        sbase = 4 * R + 125 + 18 * r + 18 * j + 5 * k
        upper = 2 + 3 ** (t + 1) * z
        np = {clocks[0]: ends[0], clocks[0] + 16 + 18 * j: 4 * b - 17,
              nbase: 3 * d - 5, nbase + 1 + 3 * t: upper}
        sp = {clocks[3]: ends[3], clocks[3] + 21 + 18 * j: 3 * b - 17,
              sbase: 2 * d - 5, sbase + 3 + 3 * t: upper - 1}
        nc = replay_word(starts[0], nw, ne, counts, 'full_N_steps', np, True)
        sc = replay_word(starts[3], sw, se, counts, 'full_S_steps', sp, True)
        assert nc == nbase + 3 * t + 2 * l + (3 if g == 1 else 4)
        assert sc == sbase + 3 * t + 2 * l + (5 if g == 1 else 4)
        assert ne == se if g == 1 else ne == 9 * se + 2
        counts['complete_successful_cases' if g == 1 else 'complete_opposite_cases'] += 1
        if j:
            four_windows(a, 11 * j - 4, counts)
            counts['complete_primary_windows'] += 1
        if k:
            secondary_window(b, 3 * k - 2, counts)
            counts['complete_secondary_windows'] += 1
        if j and k:
            counts['complete_both_windows'] += 1
        budget = None
        if R >= 26:
            H, budget = (3 * d - 5) // 2, min(k, 8)
            assert H == 2 + 3 * 4 ** t * z
            tree = inverse_tree(H, budget)
            for p, e, o in tree:
                assert p > starts[0]
                forward_check(p, e, o, H, counts)
            counts['weighted_inverse_trees'] += 1
            counts['weighted_trees_at_full_k_budget'] += budget == k
        row = {'R': R, 'r': r, 'j': j, 'k': k, 't': t, 'l': l, 'g': g, 'offset': offset,
               'weight_bits': w.bit_length(), 'N_bits': starts[0].bit_length(), 'S_bits': starts[3].bit_length(),
               'd_bits': d.bit_length(), 'z_bits': z.bit_length(), 'y_bits': y.bit_length(),
               'N_clock': nc, 'S_clock': sc, 'inverse_budget': budget}
        for key, val in row.items():
            if val is not None:
                maxima[key] = max(maxima[key], val)
        rows.append(row)
    return {'rows': rows, 'maxima': dict(maxima), 'scope': 'Complete weighted N and S paths, four checkpoints each, earlier separated windows and both final exits. At R>=26 inverse trees are complete at min(k,8), not always at k. No earliest-meeting assertion.'}


def modular_checks(counts):
    params = [(r, j, k, t, l, g) for r in [0, 5, 6] for j, k in [(0, 0), (1, 1), (2, 2)]
              for t in [1, 2, 8] for l in [1, 2, 5] for g in [1, 3]]
    params += [(r, j, k, t, l, g) for r, j, k, t, l in
               [(128, 128, 128, 128, 128), (5, 1, 4096, 16, 128), (5, 1, 1, 4096, 1024), (5, 1, 1, 16, 8192)] for g in [1, 3]]
    rows, maxima = [], Counter()
    for r, j, k, t, l, g in params:
        m, K = 57 + 11 * r, 9 + 11 * j
        D, E, T, V = 1 << m, 1 << K, 1 << (3 * k + 4), 1 << (2 * t + l + 3)
        M = D * E * T * V
        A, c = pow(3, 35 + 7 * r, M), 3 ** (6 + 7 * j)
        eps, z0, y0, target = exit_unit(k, t, l, g)
        ca = c * A % M
        F = 7 * ca + D * (c - E) + (V - eps) * D * E * T
        precision = m + K + 3 * k + 2 * t + l + 4
        seed = affine_seed(precision, ca, F)
        for B in [0, 1 << (r + j + k + t + l + 32)]:
            R = seed + (1 << precision) * (B + 36)
            assert R > B and R >= 36
            X = pow(9, R, M)
            assert (ca * (X + 7) + c * D) % M == D * E * (1 + T * eps)
            u, rem = divmod(X + 7, D)
            assert rem == 0 and u % 2
            au = pow(3, 35 + 7 * r, E * T * V) * u % (E * T * V)
            q, rem = divmod(au + 1, E)
            assert rem == 0 and q % 2
            b = c * q % (T * V)
            v, rem = divmod(b - 1, T)
            assert rem == 0 and v == eps and v % 2
            d = pow(9, k + 1, V) * v % V
            assert d == target and d % 8 == 3
            z, rem = divmod(d - 3, 1 << (2 * t + 1))
            assert rem == 0 and z == z0 and z % 2
            ym = (1 + pow(3, t, 1 << (l + 2)) * z) % (1 << (l + 2))
            y, rem = divmod(ym, 1 << l)
            assert rem == 0 and y == y0 and pow(3, l + 1, 4) * y % 4 == g
            counts['modular_pure_lifts'] += 1
            maxima['exponent_bits'] = max(maxima['exponent_bits'], R.bit_length())
            maxima['modulus_bits'] = max(maxima['modulus_bits'], M.bit_length())
            if max(r, j, k, t, l) >= 128:
                rows.append({'r': r, 'j': j, 'k': k, 't': t, 'l': l, 'g': g, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'large_rows': rows, 'maxima': dict(maxima), 'scope': 'Both residues and all exact binary valuations are checked with modular powers. No pure starting value or pure trajectory is materialized; the lift itself permits r<5.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumFiveEvenExit.'+t for t in THEOREMS}
        assert len(roots) == len(THEOREMS)
        source_text = (ROOT/source).read_text()
        assert set(re.findall(r'^theorem (\w+)', source_text, re.M)) == set(THEOREMS)
        assert not re.search(r'\b(sorry|native_decide|axiom)\b', source_text)
    for _, axioms in roots:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}


def build(prior, lean, threads, cache):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert version == prior['lean_version']
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    old = {b['source']: b for b in prior['builds']}
    sources = list(old)+[SOURCE]
    assert len(sources) == len(set(sources)) == 47
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-five-even-exit-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj, log = Path(directory)/(stem+'.olean'), OUT/(stem+'.log')
            cached = Path(cache)/(stem+'.olean') if cache else None
            previous = old.get(source)
            if previous and cached and cached.is_file() and digest(cached) == previous['olean_sha256']:
                assert digest(ROOT/source) == previous['source_sha256']
                assert digest(ROOT/previous['log']) == previous['log_sha256']
                shutil.copyfile(cached, obj)
                assert digest(obj) == previous['olean_sha256']
                output = (ROOT/previous['log']).read_text()
                log.write_text(output)
                audit_log(source, output)
                builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                               'fresh_build': False, 'reused_verified_build': True,
                               'reused_from_manifest': PRIOR, 'cache_path': str(cached),
                               'prior_compile_command': previous.get('command', previous.get('prior_compile_command')),
                               'prior_elapsed_seconds': previous.get('prior_elapsed_seconds', previous['elapsed_seconds']),
                               'prior_build_record': previous,
                               'threads': previous['threads'], 'returncode': 0,
                               'elapsed_seconds': 0.0, 'native_computation_used': False,
                               'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                               'olean_sha256': digest(obj)})
                print('Authenticated cached Lean object:', source, flush=True)
                continue
            command = [lean, '-j', str(threads), '-o', str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS=str(threads)))
            log.write_text(result.stdout)
            assert result.returncode == 0, (source, result.stdout)
            audit_log(source, result.stdout)
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'threads': threads, 'returncode': 0,
                           'fresh_build': True, 'reused_verified_build': False,
                           'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic()-started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, sources, builds

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--threads', type=int, default=min(16, os.cpu_count() or 1))
    parser.add_argument('--cache', type=Path)
    args = parser.parse_args()
    assert args.threads > 0
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT / PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT / name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    version, sources, builds = build(prior, args.lean, args.threads, args.cache)
    counts, sections = Counter(), {}
    for check in [generic_checks, complete_paths, modular_checks]:
        sections[check.__name__] = check(counts)
        print('Independent replay passed:', check.__name__, flush=True)
    save(OUT / 'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources + [Path(__file__).name, NOTE, PRIOR]
    files += [name for name in prior['sha256'] if name.endswith('.py')]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'verification.json']
    save(OUT / 'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'fresh_build_count': sum(b['fresh_build'] for b in builds),
        'reused_verified_build_count': sum(b['reused_verified_build'] for b in builds),
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': [],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])}, 'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'Adjacent values4^t*q+2 and4^t*q+1 reach3^t*q+2 and3^t*q+1 after3t ordinary steps.',
            'For d=3+2*4^t*z and1+3^t*z=2^l*y, favorable residue3^(l+1)*y=1mod4 merges the two third endpoints. Full source clocks and exclusion of leastness use the known smaller fourth source.',
            'For t>=1 the new branch has d=3mod8 and is disjoint from the earlier d=1mod4 odd-exit family.',
            'For every prescribed positive t,l, both final residues have arbitrarily large pure exponents, and unbounded weights at each fixed R. Positivity and oddness of z,y and all coordinate equations are retained.',
            'For r>=5 and R>=14 the favorable exit excludes the constructed N from leastness; both earlier separated windows remain available at their stated j,k bounds.',
            'For R>=26 all inverse predecessors of the earlier H with e<=k are larger than N. A combined theorem gives arbitrarily large pure sources having this obstruction and a later merger with a smaller source.',
            'Exact odd factorization gives the two exits for every positive odd z at t>=1. The opposite exit yields9h+2,h, not a merger, with full source clock identities.',
            'Every d>3 with d=3mod4 has either the treated odd valuation of d-3 or the even valuation d=3+4^(t+1)*q. The latter has local endpoints u,9u-1 with2u=1+3^(t+1)*q; no merger is asserted.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication precedes isolated dependency reuse. The new module is always built freshly.',
        'external_dependency': 'Lean4.33.1 and standard libraries. No external mathematical premise, installation or credential access in this turn.',
        'not_proved': [
            'A merger for the opposite exit, or for the remaining even valuation of d-3 in the d=3mod4 branch.',
            'Earliest meeting, all-time separation, an unbounded-budget inverse minimum, or full family convergence.',
            'Exclusion of arbitrary least counterexamples, nontrivial cycles, divergence, or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT / name) for name in dict.fromkeys(files)},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS), 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
