"""Verify a variable negative-five transition beyond both separated windows.

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

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-five-transition'
PRIOR = 'results/minimum-seventeen-phase/verification.json'
SOURCE = 'lean/MinimumFiveTransition.lean'
NOTE = 'docs/MINIMUM-FIVE-TRANSITION.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py', 'verify_minimum_seventeen_separation.py',
           'verify_minimum_seventeen_fourth.py', 'verify_minimum_seventeen_phase.py']
THEOREMS = [
    'five_bridges', 'third_profiles', 'local_profiles', 'local_meeting', 'third_meeting',
    'full_third_meeting', 'third_not_least', 'finite_five_units', 'secondary_scale_bound',
    'third_units_odd', 'pure_third_lift', 'weighted_third_lift', 'third_window_separation',
    'build_third_escape', 'pure_third_escape', 'weighted_third_escape',
    'escape_primary_window', 'pure_both_windows', 'weighted_both_windows',
]
N_BRIDGE, S_BRIDGE, FIVE_CYCLE = 'OOEEOE', 'EOE', 'OOE'
N_LOCAL, S_LOCAL = 'EOEE', 'OEEEO'


def weight(R, r, j, k, offset=0):
    D, E, T = 1 << (57+11*r), 1 << (9+11*j), 1 << (3*k+4)
    M = 16*D*E*T
    A, c = pow(3, 35+7*r, M), pow(3, 6+7*j, M)
    eps = 5*pow(pow(9, k+1, 16), -1, 16) % 16
    w = (D*E*(1+T*eps)-c*D-7*c*A)*pow(c*A*pow(9, R, M), -1, M) % M
    w += offset*M
    assert w > 0 and w % 2 == 1
    return w


def coordinates(R, r, j, k, w):
    starts, ends, clocks, words, a, X = base_coordinates(R, r, w)
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0 and u % 2 == 1
    q, rem = divmod(9*a+1, 1 << (9+11*j))
    assert rem == 0 and q > 0 and q % 2 == 1
    b = 3**(6+7*j)*q
    v, rem = divmod(b-1, 1 << (3*k+4))
    assert rem == 0 and v > 0 and v % 2 == 1
    d = 9**(k+1)*v
    assert d % 16 == 5 and b % 16 == 1
    return starts, ends, clocks, words, a, X, b, v, d


def generic_checks(counts):
    for q in list(range(1, 129))+[2**128+1, 3**128+7]:
        for n, t, expected, word in [(64*q-13, 9, 27*q-5, N_BRIDGE),
                                      (48*q-14, 4, 18*q-5, S_BRIDGE)]:
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == expected
            assert shortcut(n, word, counts) == expected
            assert inverse(expected, word[::-1], counts) == n
            counts['generic_bridge_paths'] += 1
            counts['generic_bridge_steps'] += t
    for t in range(1024):
        n, s = 48*t+10, 32*t+5
        pn, ps = ordinary(n, 5), ordinary(s, 7)
        assert pn == paired(n, 5) and ps == paired(s, 7)
        assert pn[-1] == ps[-1] == 9*t+2
        assert shortcut(n, N_LOCAL, counts) == shortcut(s, S_LOCAL, counts) == 9*t+2
        assert inverse(9*t+2, N_LOCAL[::-1], counts) == n
        assert inverse(9*t+2, S_LOCAL[::-1], counts) == s
        counts['generic_local_meetings'] += 1
        counts['generic_local_steps'] += 12
    for k in list(range(65))+[128, 1024]:
        for v in [1, 2, 3, 5, 17]:
            b = 1+(1 << (3*k+4))*v
            d = 9**(k+1)*v
            assert endpoint(4*b-17, 9+5*k, counts, 'generic_third_profile_steps') == 3*d-5
            assert endpoint(3*b-17, 4+5*k, counts, 'generic_third_profile_steps') == 2*d-5
            counts['generic_third_profile_pairs'] += 1
        eps = 5*pow(pow(9, k+1, 16), -1, 16) % 16
        for offset in [0, 1, 2, 17]:
            v = eps+16*offset
            b, d = 1+(1 << (3*k+4))*v, 9**(k+1)*v
            target = 9*((d-5)//16)+2
            nword, sword = N_BRIDGE+FIVE_CYCLE*k+N_LOCAL, S_BRIDGE+FIVE_CYCLE*k+S_LOCAL
            assert endpoint(4*b-17, 14+5*k, counts, 'generic_third_meeting_steps') == target
            assert endpoint(3*b-17, 11+5*k, counts, 'generic_third_meeting_steps') == target
            assert shortcut(4*b-17, nword, counts) == shortcut(3*b-17, sword, counts) == target
            assert inverse(target, nword[::-1], counts) == 4*b-17
            assert inverse(target, sword[::-1], counts) == 3*b-17
            if k > 0:
                secondary_window(b, 3*k-2, counts)
            counts['generic_third_meetings'] += 1
    for f in range(1, 16, 2):
        eps = 5*pow(f, -1, 16) % 16
        assert 0 < eps < 16 and eps % 2 == 1 and f*eps % 16 == 5
        counts['finite_five_units'] += 1
    return {'bridge_q_interval': [1, 128], 'additional_q': ['2**128+1', '3**128+7'],
            'local_t_interval': [0, 1023], 'k_interval': [0, 64], 'additional_k': [128, 1024],
            'profile_units': [1, 2, 3, 5, 17], 'meeting_unit_offsets': [0, 1, 2, 17],
            'words': {'N_bridge': N_BRIDGE, 'S_bridge': S_BRIDGE, 'cycle': FIVE_CYCLE,
                      'N_local': N_LOCAL, 'S_local': S_LOCAL},
            'scope': 'Finite generic bridges, arbitrary-unit third profiles, conditional meetings and secondary separated windows supplement the universal kernel identities. Full shortcut meetings add one shared halving to the kernel clocks.'}


def full_meeting(R, r, j, k, w, counts):
    starts, ends, clocks, words, a, _, b, v, d = coordinates(R, r, j, k, w)
    target = 9*((d-5)//16)+2
    nw = words[0]+SECOND_BRIDGE+CYCLE*j+N_BRIDGE+FIVE_CYCLE*k+N_LOCAL
    sw = words[3]+'O'+BRIDGES[0]+CYCLE*j+S_BRIDGE+FIVE_CYCLE*k+S_LOCAL
    nc, sc = 5*R+121+18*r+18*j+5*k, 4*R+132+18*r+18*j+5*k
    assert len(nw)+nw.count('O') == nc and len(sw)+sw.count('O') == sc
    npoints = {clocks[0]: ends[0], clocks[0]+16+18*j: 4*b-17,
               clocks[0]+25+18*j+5*k: 3*d-5}
    spoints = {clocks[3]: ends[3], clocks[3]+21+18*j: 3*b-17,
               clocks[3]+25+18*j+5*k: 2*d-5}
    assert endpoint(starts[0], nc, counts, 'full_N_steps', npoints) == target
    assert endpoint(starts[3], sc, counts, 'full_S_steps', spoints) == target
    assert shortcut(starts[0], nw, counts) == shortcut(starts[3], sw, counts) == target
    assert inverse(target, nw[::-1], counts) == starts[0]
    assert inverse(target, sw[::-1], counts) == starts[3]
    for i in [1, 2]:
        assert len(words[i])+words[i].count('O') == clocks[i]
        assert endpoint(starts[i], clocks[i], counts, 'older_partner_prefix_steps') == ends[i]
        assert shortcut(starts[i], words[i], counts) == ends[i]
        assert inverse(ends[i], words[i][::-1], counts) == starts[i]
    if j > 0:
        four_windows(a, 11*j-4, counts)
        counts['complete_cases_with_primary_separation'] += 1
    if k > 0:
        secondary_window(b, 3*k-2, counts)
        counts['complete_cases_with_secondary_separation'] += 1
    if j > 0 and k > 0:
        counts['complete_cases_with_both_windows'] += 1
    counts['complete_four_source_cases'] += 1
    return {'R': R, 'r': r, 'j': j, 'k': k, 'weight_bits': w.bit_length(),
            'N_bits': starts[0].bit_length(), 'S_bits': starts[3].bit_length(),
            'a_bits': a.bit_length(), 'b_bits': b.bit_length(), 'd_bits': d.bit_length(),
            'N_clock': nc, 'S_clock': sc,
            'primary_horizon': 11*j-4 if j else None, 'secondary_horizon': 3*k-2 if k else None}


def complete_paths(counts):
    params = {(R, r, j, k) for R in range(14, 19) for r in range(5, 9)
              for j in range(5) for k in range(9)}
    for R in [128, 1024, 16384]:
        for j in [1, 16]:
            for k in [1, 16]:
                params.add((R, 5, j, k))
    for r in [128, 512, 4096]:
        for k in [1, 16]:
            params.add((14, r, 1, k))
    for j in [128, 512, 4096]:
        for k in [1, 16]:
            params.add((14, 5, j, k))
    for k in [128, 512, 4096]:
        for j in [1, 16]:
            params.add((14, 5, j, k))
    rows, maxima = [], Counter()
    for R, r, j, k in sorted(params):
        row = full_meeting(R, r, j, k, weight(R, r, j, k), counts)
        for key, value in row.items():
            if value is not None:
                maxima[key] = max(maxima[key], value)
        if R >= 16384 or r >= 512 or j >= 512 or k >= 512:
            rows.append(row)
    return {'distinct_cases': len(params), 'maxima': dict(maxima), 'large_rows': rows,
            'regular_R_interval': [14, 18], 'regular_r_interval': [5, 8],
            'regular_j_interval': [0, 4], 'regular_k_interval': [0, 8],
            'additional_R': [128, 1024, 16384], 'additional_r_j_k': [128, 512, 4096],
            'scope': 'N,S are replayed completely to a common value, with checkpoints at all three block boundaries. P,Q have full transition-prefix replays. Positive odd u,q,v and source inequalities are checked. For j,k positive both prior separated windows are checked. No earliest-meeting claim is made.'}


def modular_checks(counts):
    params = [(r, j, k) for r in range(5, 9) for j in range(5) for k in range(9)]
    params += [(128, 128, 128), (512, 1, 1), (5, 512, 4096)]
    rows = []
    for r, j, k in params:
        m, K, L = 57+11*r, 9+11*j, 3*k+4
        D, E, T = 1 << m, 1 << K, 1 << L
        V, M = 16*T, 16*D*E*T
        A, c = pow(3, 35+7*r, M), 3**(6+7*j)
        eps = 5*pow(pow(9, k+1, 16), -1, 16) % 16
        ca = c*A % M
        F = 7*ca+D*(c-E)+(16-eps)*D*E*T
        assert c >= E
        precision = m+K+3*k+5
        seed = affine_seed(precision, ca, F)
        for B in [0, 1 << (r+j+k+32)]:
            R = seed+(1 << precision)*(B+14)
            assert R > B and R >= 14
            X = pow(9, R, M)
            assert (ca*(X+7)+c*D) % M == D*E*(1+T*eps)
            u_mod, rem = divmod(X+7, D)
            assert rem == 0 and u_mod % 2 == 1
            au_mod = pow(3, 35+7*r, E*V)*u_mod % (E*V)
            q_mod, rem = divmod(au_mod+1, E)
            assert rem == 0 and q_mod % 2 == 1
            b_mod = (c*q_mod) % V
            v_mod, rem = divmod(b_mod-1, T)
            assert rem == 0 and v_mod == eps and v_mod % 2 == 1
            assert pow(9, k+1, 16)*v_mod % 16 == 5
            counts['modular_pure_lifts'] += 1
            if r >= 128 or j >= 128 or k >= 128:
                rows.append({'r': r, 'j': j, 'k': k, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'regular_r_interval': [5, 8], 'regular_j_interval': [0, 4], 'regular_k_interval': [0, 8],
            'additional_coordinates': [[128, 128, 128], [512, 1, 1], [5, 512, 4096]],
            'large_rows': rows,
            'scope': 'Pure exponent coordinates, all three odd units and the last exit residue are checked with modular powers. Enormous pure starting values and trajectories are not materialized.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        r = 5
        for j, k in [(1, 16), (16, 128)]:
            w = weight(R, r, j, k)
            starts, ends, _, _, a, X, b, v, d = coordinates(R, r, j, k, w)
            for n, t, expected in zip([4*X-5, 243*X-1, 14348907*X-1, 1594323*X-1],
                                      [91+18*r, 89+18*r, 69+18*r, 164+18*(r-5)], ends):
                assert endpoint(n, t, counts, 'larger_transition_steps') == expected
            assert endpoint(ends[0], 16+18*j, counts, 'larger_secondary_steps') == 4*b-17
            assert endpoint(ends[3], 21+18*j, counts, 'larger_secondary_steps') == 3*b-17
            target = 9*((d-5)//16)+2
            assert endpoint(4*b-17, 14+5*k, counts, 'larger_third_steps') == target
            assert endpoint(3*b-17, 11+5*k, counts, 'larger_third_steps') == target
            four_windows(a, 11*j-4, counts)
            secondary_window(b, 3*k-2, counts)
            rows.append({'R': R, 'r': r, 'j': j, 'k': k, 'N_bits': starts[0].bit_length(),
                         'S_bits': starts[3].bit_length(), 'full_growing_prefixes_replayed': False})
    return {'rows': rows,
            'scope': 'Exact weighted coordinates, all transition and later-merger tails and both separated windows are checked. Full initial growing prefixes are not replayed.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumFiveTransition.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 43
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-five-transition-') as directory:
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
            'For b=1+2^(3k+4)*v with v positive, the two secondary endpoints 4b-17,3b-17 reach 3d-5,2d-5 at clocks9+5k,4+5k, where d=9^(k+1)*v.',
            'If d=5mod16, those endpoints merge. The complete N,S clocks are5R+120+18r+18j+5k and4R+131+18r+18j+5k; S is positive and smaller than N for R>=14, so N is excluded as least.',
            'All three units u,q,v are odd under the coordinate and exit conditions. The first, second and third binary valuations are exactly57+11r,9+11j,3k+4.',
            'For every r,j,k and every bound, pure exponents above the bound satisfy all three coordinate equations and the final exit residue. At every fixed initial R, weights above every bound also exist.',
            'When H+6<=3k+4, the secondary exit windows remain separated through H despite the specified later merger. Pure and fixed-prefix weighted realizations are kernel theorems.',
            'For every r>=5 and H, choosing j=k=H+1 gives unbounded pure exponents and weights at each fixed R>=14 with both primary and secondary separation through H, a later fourth-source merger and a least-source exclusion.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication precedes dependency reuse. Objects are copied into an isolated import directory; mismatches are rebuilt and nested prior provenance is retained. The new module is always freshly built.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation or credential access.',
        'finite_scope_limit': 'Complete weighted meetings, full older-partner prefixes, phase-window checks, modular-only pure exponents and larger tail-only coordinates have distinct scopes. Shortcut meetings add one common halving to kernel clocks. Primary state counts include a repeated main window in the old and new phase checks.',
        'not_proved': [
            'A merger for every final negative-five exit unit or every normalized secondary source.',
            'Convergence of all family members or the smaller fourth-source family.',
            'An earliest meeting, an optimal inverse budget or a uniform source-dependent meeting bound.',
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

