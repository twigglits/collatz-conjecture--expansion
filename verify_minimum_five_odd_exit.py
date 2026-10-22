"""Verify variable odd-block exits and their complementary residual pair.

Full weighted meetings, finite windows, modular-only pure lifts and larger
tail-only cases are separate from the universal kernel results.
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

from verify_minimum_inverse_locality import digest, save, ordinary, paired
from verify_minimum_ladder_block_exit import inverse, shortcut
from verify_minimum_seventeen_transition import BRIDGES, CYCLE
from verify_minimum_seventeen_separation import affine_seed
from verify_minimum_seventeen_fourth import endpoint, SECOND_BRIDGE
from verify_minimum_seventeen_phase import coordinates as base_coordinates, four_windows, secondary_window
from verify_minimum_five_transition import N_BRIDGE, S_BRIDGE, FIVE_CYCLE

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-five-odd-exit'
PRIOR = 'results/minimum-five-transition/verification.json'
SOURCE = 'lean/MinimumFiveOddExit.lean'
NOTE = 'docs/MINIMUM-FIVE-ODD-EXIT.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py', 'verify_minimum_seventeen_separation.py',
           'verify_minimum_seventeen_fourth.py', 'verify_minimum_seventeen_phase.py',
           'verify_minimum_five_transition.py']
THEOREMS = ['adjacent_bridges', 'odd_exit_meeting', 'opposite_exit_meeting', 'full_odd_exit_meeting', 'odd_exit_not_least', 'pure_residue_lift', 'binary_target', 'pure_odd_exit_lift', 'weighted_odd_exit_lift', 'exit_growth_bound', 'companion_above_source', 'exit_units_odd', 'realization_windows', 'build_odd_escape', 'pure_odd_escape', 'weighted_odd_escape', 'full_opposite_meeting', 'odd_exit_dichotomy', 'least_odd_exit_constraint', 'opposite_exit_profiles']


def exit_unit(k, l, g):
    assert g in [1, 3]
    V, D = 1 << (l+3), 1 << (l+1)
    z0 = g*pow(pow(3, l+1, 4), -1, 4) % 4
    target = 1+D*z0
    eps = target*pow(pow(9, k+1, V), -1, V) % V
    assert 0 < eps < V and eps % 2 == 1
    assert 0 < z0 < 4 and z0 % 2 == 1 and pow(3, l+1, 4)*z0 % 4 == g
    assert pow(9, k+1, V)*eps % V == target
    return eps, z0, target


def weight(R, r, j, k, l, g, offset=0):
    D, E, T, V = 1 << (57+11*r), 1 << (9+11*j), 1 << (3*k+4), 1 << (l+3)
    M = V*D*E*T
    A, c = pow(3, 35+7*r, M), pow(3, 6+7*j, M)
    eps, _, _ = exit_unit(k, l, g)
    w = (D*E*(1+T*eps)-c*D-7*c*A)*pow(c*A*pow(9, R, M), -1, M) % M
    w += offset*M
    assert w > 0 and w % 2 == 1
    return w


def coordinates(R, r, j, k, l, g, w):
    starts, ends, clocks, words, a, X = base_coordinates(R, r, w)
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0 and u % 2 == 1
    q, rem = divmod(9*a+1, 1 << (9+11*j))
    assert rem == 0 and q > 0 and q % 2 == 1
    b = 3**(6+7*j)*q
    v, rem = divmod(b-1, 1 << (3*k+4))
    assert rem == 0 and v > 0 and v % 2 == 1
    d = 9**(k+1)*v
    z, rem = divmod(d-1, 1 << (l+1))
    assert rem == 0 and z > 0 and z % 2 == 1
    assert pow(3, l+1, 4)*z % 4 == g
    assert 3*d >= 5*(1 << (3*R))*w and 3*d-4 > starts[0]
    return starts, ends, clocks, words, a, X, b, v, d, z


def local_exit(l, z, g):
    assert l >= 1 and z > 0 and z % 2 == 1 and pow(3, l+1, 4)*z % 4 == g
    d = 1+(1 << (l+1))*z
    if g == 1:
        target = (3**(l+1)*z-1)//4
        return d, target, target, 'E'+'O'*l+'EE', 'OEE'+'O'*(l-1)+'EO', None
    h, rem = divmod(3**l*z-1, 4)
    assert rem == 0 and h > 0 and h % 3 == 2
    return d, 9*h+2, h, 'E'+'O'*l+'EO', 'OEE'+'O'*(l-1)+'EE', 'O'*(l+1)+'EE'


def replay_word(n, word, expected, counts, key, checkpoints=None, paired_check=False):
    clock = len(word)+word.count('O')
    assert endpoint(n, clock, counts, key, checkpoints) == expected
    if paired_check:
        path = ordinary(n, clock)
        assert path == paired(n, clock) and path[-1] == expected
        counts['paired_path_comparisons'] += 1
    assert shortcut(n, word, counts) == expected
    assert inverse(expected, word[::-1], counts) == n
    return clock


def generic_checks(counts):
    for l in list(range(65))+[128, 1024]:
        for z in [1, 2, 3, 5, 17]:
            d, a = 1+(1 << (l+1))*z, (1 << l)*(3*z)-1
            assert ordinary(3*d-5, 1) == paired(3*d-5, 1)
            assert endpoint(3*d-5, 1, counts, 'bridge_steps') == a
            assert ordinary(2*d-5, 3) == paired(2*d-5, 3)
            assert endpoint(2*d-5, 3, counts, 'bridge_steps') == a-1
            counts['bridge_pairs'] += 1
    params = [(l, z) for l in range(1, 65) for z in range(1, 128, 2)]
    params += [(l, z) for l in [128, 1024, 4096] for z in [1, 3, 17, 31]]
    for l, z in params:
        g = pow(3, l+1, 4)*z % 4
        d, nend, send, nw, sw, tw = local_exit(l, z, g)
        nc = replay_word(3*d-5, nw, nend, counts, 'local_N_steps', paired_check=True)
        sc = replay_word(2*d-5, sw, send, counts, 'local_S_steps', paired_check=True)
        if g == 1:
            assert nend == send and (nc, sc) == (2*l+3, 2*l+5)
            counts['local_successful_pairs'] += 1
        else:
            assert nc == sc == 2*l+4 and nend == 9*send+2
            assert replay_word(3*d-4, tw, nend, counts, 'local_companion_steps', paired_check=True) == 2*l+4
            counts['local_opposite_pairs'] += 1
    for h in range(5):
        M = 1 << (h+1)
        for c in range(1, M, 2):
            for g in range(1, M, 2):
                eps = g*pow(c, -1, M) % M
                assert 0 < eps < M and eps % 2 == 1 and c*eps % M == g
                counts['binary_target_cases'] += 1
    return {'bridge_l_interval': [0, 64], 'additional_bridge_l': [128, 1024],
            'bridge_z': [1, 2, 3, 5, 17], 'local_l_interval': [1, 64],
            'local_odd_z_interval': [1, 127], 'additional_local_l': [128, 1024, 4096],
            'additional_local_z': [1, 3, 17, 31], 'binary_target_h_interval': [0, 4],
            'scope': 'Both residue exits, the complementary larger companion, and the residual pair 9h+2,h are independently replayed with ordinary, paired, shortcut and inverse operations.'}


def complete_case(R, r, j, k, l, g, w, counts):
    starts, ends, clocks, words, a, _, b, v, d, z = coordinates(R, r, j, k, l, g, w)
    d2, nend, send, nw0, sw0, tw = local_exit(l, z, g)
    assert d2 == d
    nw = words[0]+SECOND_BRIDGE+CYCLE*j+N_BRIDGE+FIVE_CYCLE*k+nw0
    sw = words[3]+'O'+BRIDGES[0]+CYCLE*j+S_BRIDGE+FIVE_CYCLE*k+sw0
    npoints = {clocks[0]: ends[0], clocks[0]+16+18*j: 4*b-17,
               clocks[0]+25+18*j+5*k: 3*d-5}
    spoints = {clocks[3]: ends[3], clocks[3]+21+18*j: 3*b-17,
               clocks[3]+25+18*j+5*k: 2*d-5}
    nc = replay_word(starts[0], nw, nend, counts, 'full_N_steps', npoints)
    sc = replay_word(starts[3], sw, send, counts, 'full_S_steps', spoints)
    if g == 1:
        assert nc == 5*R+119+18*r+18*j+5*k+2*l
        assert sc == 4*R+130+18*r+18*j+5*k+2*l and nend == send
        counts['complete_successful_cases'] += 1
    else:
        assert nc == 5*R+120+18*r+18*j+5*k+2*l
        assert sc == 4*R+129+18*r+18*j+5*k+2*l and nend == 9*send+2
        assert replay_word(3*d-4, tw, nend, counts, 'full_companion_steps') == 2*l+4
        counts['complete_opposite_cases'] += 1
    for i in [1, 2]:
        assert replay_word(starts[i], words[i], ends[i], counts, 'older_partner_prefix_steps') == clocks[i]
    if j > 0:
        four_windows(a, 11*j-4, counts)
        counts['complete_primary_windows'] += 1
    if k > 0:
        secondary_window(b, 3*k-2, counts)
        counts['complete_secondary_windows'] += 1
    if j > 0 and k > 0:
        counts['complete_both_windows'] += 1
    counts['complete_four_source_cases'] += 1
    return {'R': R, 'r': r, 'j': j, 'k': k, 'l': l, 'g': g, 'weight_bits': w.bit_length(),
            'N_bits': starts[0].bit_length(), 'S_bits': starts[3].bit_length(),
            'a_bits': a.bit_length(), 'b_bits': b.bit_length(), 'd_bits': d.bit_length(),
            'z_bits': z.bit_length(), 'N_clock': nc, 'S_clock': sc,
            'primary_horizon': 11*j-4 if j else None, 'secondary_horizon': 3*k-2 if k else None}


def complete_paths(counts):
    params = {(R, r, j, k, l, g) for R in range(14, 17) for r in [5, 6]
              for j in range(3) for k in range(3) for l in range(1, 9) for g in [1, 3]}
    for g in [1, 3]:
        for R in [128, 1024, 16384]:
            params.add((R, 5, 1, 1, 16, g))
        for r in [128, 512, 4096]:
            params.add((14, r, 1, 1, 16, g))
        for j in [128, 512, 4096]:
            params.add((14, 5, j, 1, 16, g))
        for k in [128, 512, 4096]:
            params.add((14, 5, 1, k, 16, g))
        for l in [128, 512, 4096]:
            params.add((14, 5, 1, 1, l, g))
        params.add((128, 128, 128, 128, 128, g))
    rows, maxima = [], Counter()
    for R, r, j, k, l, g in sorted(params):
        row = complete_case(R, r, j, k, l, g, weight(R, r, j, k, l, g), counts)
        for key, value in row.items():
            if value is not None:
                maxima[key] = max(maxima[key], value)
        if R >= 128 or max(r, j, k, l) >= 128:
            rows.append(row)
    return {'distinct_cases': len(params), 'maxima': dict(maxima), 'large_rows': rows,
            'regular_R_interval': [14, 16], 'regular_r': [5, 6],
            'regular_j_k_interval': [0, 2], 'regular_l_interval': [1, 8], 'exit_residues': [1, 3],
            'scope': 'Complete N,S paths reach the successful common value or the complementary residual pair. P,Q have complete primary-prefix replays. Complementary larger companions are replayed to the same N endpoint. Every claimed checkpoint, unit parity, source bound and both available windows are checked.'}


def modular_checks(counts):
    params = [(r, j, k, l, g) for r in [0, 5, 6] for j in range(3) for k in range(3)
              for l in range(1, 9) for g in [1, 3]]
    params += [(r, j, k, l, g) for r, j, k, l in
               [(128, 128, 128, 128), (512, 1, 1, 64), (5, 512, 4096, 1024), (5, 1, 1, 8192)]
               for g in [1, 3]]
    rows, maxima = [], Counter()
    for r, j, k, l, g in params:
        m, K = 57+11*r, 9+11*j
        D, E, T, V = 1 << m, 1 << K, 1 << (3*k+4), 1 << (l+3)
        M = D*E*T*V
        A, c = pow(3, 35+7*r, M), 3**(6+7*j)
        eps, z0, target = exit_unit(k, l, g)
        ca = c*A % M
        F = 7*ca+D*(c-E)+(V-eps)*D*E*T
        assert c >= E
        precision = m+K+3*k+l+4
        seed = affine_seed(precision, ca, F)
        for B in [0, 1 << (r+j+k+l+32)]:
            R = seed+(1 << precision)*(B+14)
            assert R > B and R >= 14
            X = pow(9, R, M)
            assert (ca*(X+7)+c*D) % M == D*E*(1+T*eps)
            u_mod, rem = divmod(X+7, D)
            assert rem == 0 and u_mod % 2 == 1
            au_mod = pow(3, 35+7*r, E*T*V)*u_mod % (E*T*V)
            q_mod, rem = divmod(au_mod+1, E)
            assert rem == 0 and q_mod % 2 == 1
            b_mod = c*q_mod % (T*V)
            v_mod, rem = divmod(b_mod-1, T)
            assert rem == 0 and v_mod == eps and v_mod % 2 == 1
            d_mod = pow(9, k+1, V)*v_mod % V
            assert d_mod == target
            z_mod, rem = divmod(d_mod-1, 1 << (l+1))
            assert rem == 0 and z_mod == z0 and z_mod % 2 == 1
            assert pow(3, l+1, 4)*z_mod % 4 == g
            counts['modular_pure_lifts'] += 1
            maxima['exponent_bits'] = max(maxima['exponent_bits'], R.bit_length())
            maxima['modulus_bits'] = max(maxima['modulus_bits'], M.bit_length())
            if max(r, j, k, l) >= 128:
                rows.append({'r': r, 'j': j, 'k': k, 'l': l, 'g': g,
                             'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'regular_r': [0, 5, 6], 'regular_j_k_interval': [0, 2], 'regular_l_interval': [1, 8],
            'exit_residues': [1, 3], 'maxima': dict(maxima), 'large_rows': rows,
            'scope': 'Both final residues and all four exact odd quotients are checked using modular powers. Pure starting values and full trajectories are not materialized. The lift permits r below the merger threshold.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        r = 5
        for j, k, l, g in [(1, 16, 128, 1), (16, 128, 512, 3)]:
            w = weight(R, r, j, k, l, g)
            starts, ends, _, _, a, X, b, v, d, z = coordinates(R, r, j, k, l, g, w)
            for n, t, expected in zip([4*X-5, 243*X-1, 14348907*X-1, 1594323*X-1],
                                      [91+18*r, 89+18*r, 69+18*r, 164+18*(r-5)], ends):
                assert endpoint(n, t, counts, 'larger_transition_steps') == expected
            assert endpoint(ends[0], 16+18*j, counts, 'larger_secondary_steps') == 4*b-17
            assert endpoint(ends[3], 21+18*j, counts, 'larger_secondary_steps') == 3*b-17
            assert endpoint(4*b-17, 9+5*k, counts, 'larger_third_steps') == 3*d-5
            assert endpoint(3*b-17, 4+5*k, counts, 'larger_third_steps') == 2*d-5
            _, ne, se, nw, sw, tw = local_exit(l, z, g)
            replay_word(3*d-5, nw, ne, counts, 'larger_exit_steps')
            replay_word(2*d-5, sw, se, counts, 'larger_exit_steps')
            if g == 3:
                replay_word(3*d-4, tw, ne, counts, 'larger_companion_steps')
            four_windows(a, 11*j-4, counts)
            secondary_window(b, 3*k-2, counts)
            rows.append({'R': R, 'r': r, 'j': j, 'k': k, 'l': l, 'g': g,
                         'N_bits': starts[0].bit_length(), 'S_bits': starts[3].bit_length(),
                         'full_growing_prefixes_replayed': False})
    return {'rows': rows, 'scope': 'Exact weighted coordinates, four primary tails, both secondary/third tails, both final exits and the two earlier separated windows. Full initial growing prefixes are not replayed.'}

def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumFiveOddExit.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 44
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-five-odd-exit-') as directory:
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
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT/name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    version, sources, builds = build(prior, args.lean, args.threads, args.cache)
    counts, sections = Counter(), {}
    for name, check in [('generic_checks', generic_checks), ('complete_paths', complete_paths),
                        ('modular_checks', modular_checks), ('larger_coordinates', larger_coordinates)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources+[Path(__file__).name, NOTE, PRIOR]+HELPERS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'fresh_build_count': sum(b['fresh_build'] for b in builds),
        'reused_verified_build_count': sum(b['reused_verified_build'] for b in builds),
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': [],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])}, 'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For l>=1,z>0,d=1+2^(l+1)*z and 3^(l+1)*z=1mod4, C^(2l+5)(2d-5)=C^(2l+3)(3d-5). Full N,S clocks are 5R+119+18r+18j+5k+2l and 4R+130+18r+18j+5k+2l.',
            'The positive smaller S excludes N as a least counterexample for R>=14,r>=5. Both earlier separated windows coexist with the later merger under their explicit horizon bounds, at every l>=1.',
            'A general residue lift realizes any positive nonzero residue of v modulo any power 2^(h+1). Both final odd-block residues g=1 and g=3 occur at unbounded pure exponents and unbounded weights at each fixed initial R, for every r,j,k,l.',
            'At the opposite residue, the companion 3d-4 merges with 3d-5 at equal local clocks 2l+4 and with full N at clock5R+120+18r+18j+5k+2l. This companion is strictly larger than N throughout the coordinate family with R>=14,r>=5.',
            'For d>1,d=1mod4, exact odd factorization gives the two final residue alternatives. A least source in these coordinates must take the g=3 branch.',
            'In the opposite branch let 3^l*z=4h+1. At the same local clock2l+4, the third N,S endpoints reach9h+2,h respectively. This is a residual pair, not a merger.',
            'The coordinates force u,q,v odd; the lifts also give positive odd z, so all four binary valuations are exact.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication precedes reuse. Copied dependency objects are isolated, provenance is retained, and the new module is always freshly built.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation or credential access.',
        'finite_scope_limit': 'Generic finite checks, complete weighted paths, pure modular-only lifts and larger tail-only cases have separate scopes. No claim of earliest meeting. Primary phase counts include a repeated main window in the old and new phase checks.',
        'not_proved': [
            'A smaller original source for every complementary final exit, or a merger between every residual pair9h+2,h.',
            'A merger for d=3mod4 or every normalized secondary exit.',
            'Convergence of the whole family or of all smaller fourth sources.',
            'Exclusion of arbitrary least counterexamples, nontrivial positive cycles, divergence or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
