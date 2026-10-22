"""Audit a fourth-source merger beyond separated transition exit windows.

The two negative-seventeen block counts are arbitrary in the kernel proofs.
Finite full meetings, old-partner windows, and modular pure lifts are separate.
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
from verify_minimum_seventeen_transition import BRIDGES, CYCLE, shadow_word, complete_word
from verify_minimum_seventeen_separation import separated_windows, affine_seed

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-seventeen-fourth'
PRIOR = 'results/minimum-seventeen-separation/verification.json'
SOURCE = 'lean/MinimumSeventeenFourth.lean'
NOTE = 'docs/MINIMUM-SEVENTEEN-FOURTH.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py', 'verify_minimum_seventeen_separation.py']
THEOREMS = ["bridge_thirteen","bridge_thirteen_clock","bridge_twentyfive","fourth_bounds","fourth_prefix","fourth_profile","secondary_profiles","pair_profiles","scalar_pair_meeting","nested_meeting","nested_not_least","finite_exit_units","pure_nested_lift","weighted_nested_lift","old_partner_separation","pure_escape_past_window","weighted_escape_past_window","fourth_shifted_profile"]
FOURTH_BRIDGE = shadow_word(11160262)
SECOND_BRIDGE = shadow_word(25)
assert (len(FOURTH_BRIDGE), FOURTH_BRIDGE.count('O')) == (108, 56)
assert (len(SECOND_BRIDGE), SECOND_BRIDGE.count('O')) == (10, 6)


def endpoint(n, steps, counts, key, checkpoints=None):
    checkpoints = checkpoints or {}
    for t in range(1, steps+1):
        n = 3*n+1 if n % 2 else n//2
        assert n > 0
        if t in checkpoints:
            assert n == checkpoints[t]
            counts['ordinary_checkpoints'] += 1
    counts[key] += steps
    return n


def weight(R, r, j, offset=0):
    m, K = 57+11*r, 9+11*j
    D, E = 1 << m, 1 << K
    M = D*E*64
    A = pow(3, 35+7*r, M)
    eps = 23*pow(pow(3, 6+7*j, 64), -1, 64) % 64
    w = (D*E*eps-7*A-D)*pow(A*pow(9, R, M), -1, M) % M
    w += offset*M
    assert w > 0 and w % 2 == 1
    return w


def coordinates(R, r, j, w):
    assert R >= 14 and r >= 5 and j >= 0 and w > 0
    X = 9**R*w
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0 and u % 2 == 1
    a = 3**(33+7*r)*u
    q, rem = divmod(9*a+1, 1 << (9+11*j))
    assert rem == 0 and q > 0 and q % 2 == 1
    b = 3**(6+7*j)*q
    assert a % 64 == 7 and b % 64 == 23
    N = 4*(1 << (3*R))*w-5
    P = (1 << (2*R+5))*w-1
    Q = (1 << (2*R+15))*w-1
    S = (1 << (2*R+13))*w-1
    assert 0 < P < S < Q < N
    ends = [72*a-17, 81*a-17, 64*a-17, 48*a-17]
    clocks = [5*R+91+18*r, 4*R+99+18*r, 4*R+99+18*r, 4*R+100+18*r]
    return [N, P, Q, S], ends, clocks, a, b, X, q


def generic_checks(counts):
    for q in list(range(1, 129))+[2**128+1, 3**128+7]:
        for A, B, t, D, word in [(2**108, 11160262, 164, 3**56, FOURTH_BRIDGE),
                                  (4096, 25, 16, 2916, SECOND_BRIDGE)]:
            n, expected = A*q-B, D*q-17
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == expected
            assert shortcut(n, word, counts) == expected
            assert inverse(expected, word[::-1], counts) == n
            counts['generic_bridge_paths'] += 1
            counts['generic_bridge_ordinary_steps'] += t
    for v in range(1024):
        b = 64*v+23
        n, p = 4*b-17, 3*b-17
        np, pp = ordinary(n, 11), ordinary(p, 8)
        assert np == paired(n, 11) and pp == paired(p, 8)
        assert np[-1] == pp[-1] == 27*v+8
        counts['generic_scalar_meetings'] += 1
        counts['generic_scalar_ordinary_steps'] += 19
    for j in list(range(33))+[128]:
        E = 1 << (9+11*j)
        q0 = pow(E, -1, 9)
        if q0 % 2 == 0:
            q0 += 9
        for h in range(4):
            q = q0+18*h
            a = (E*q-1)//9
            assert 9*a+1 == E*q
            b = 3**(6+7*j)*q
            assert endpoint(72*a-17, 16+18*j, counts, 'generic_secondary_steps') == 4*b-17
            assert endpoint(48*a-17, 21+18*j, counts, 'generic_secondary_steps') == 3*b-17
            counts['generic_secondary_pairs'] += 1
    for c in range(1, 64, 2):
        eps = 23*pow(c, -1, 64) % 64
        assert 0 < eps < 64 and eps % 2 == 1 and c*eps % 64 == 23
        counts['odd_exit_units'] += 1
    return {'bridge_q_interval': [1, 128], 'additional_q': ['2**128+1', '3**128+7'],
            'new_bridge_words': [FOURTH_BRIDGE, SECOND_BRIDGE],
            'scalar_v_interval': [0, 1023], 'secondary_j_interval': [0, 32],
            'additional_secondary_j': [128], 'secondary_q_offsets': [0, 18, 36, 54],
            'scope': 'Finite generic bridge, secondary-block and local merger checks supplement the universal kernel proofs. The local replay adds one shared halving to the kernel clocks7 and10.'}


def full_meeting(R, r, j, w, counts):
    starts, ends, clocks, a, b, _, _ = coordinates(R, r, j, w)
    N, P, Q, S = starts
    nlocal, target = complete_word(4*b-17, 11)
    slocal, same = complete_word(3*b-17, 8)
    assert target == same
    nw = 'OOE'*R+BRIDGES[0]+CYCLE*(r+4)+SECOND_BRIDGE+CYCLE*j+nlocal
    sw = 'O'*(2*R+13)+FOURTH_BRIDGE+CYCLE*(r-5)+'O'+BRIDGES[0]+CYCLE*j+slocal
    nclock = 5*R+118+18*r+18*j
    sclock = 4*R+129+18*r+18*j
    assert len(nw)+nw.count('O') == nclock
    assert len(sw)+sw.count('O') == sclock
    assert endpoint(N, nclock, counts, 'complete_N_steps',
                    {clocks[0]: ends[0], clocks[0]+16+18*j: 4*b-17}) == target
    assert endpoint(S, sclock, counts, 'complete_S_steps',
                    {clocks[3]: ends[3], clocks[3]+2: 72*a-25,
                     clocks[3]+21+18*j: 3*b-17}) == target
    assert shortcut(N, nw, counts) == shortcut(S, sw, counts) == target
    assert inverse(target, nw[::-1], counts) == N
    assert inverse(target, sw[::-1], counts) == S
    old_words = ['O'*(2*R+5)+BRIDGES[1]+CYCLE*(r+3),
                 'O'*(2*R+15)+BRIDGES[2]+CYCLE*r]
    for n, t, end, word in zip([P, Q], clocks[1:3], ends[1:3], old_words):
        assert len(word)+word.count('O') == t
        assert endpoint(n, t, counts, 'old_partner_prefix_steps') == end
        assert shortcut(n, word, counts) == end
        assert inverse(end, word[::-1], counts) == n
    if j > 0:
        separated_windows(a, 11*j-3, counts)
        counts['meeting_cases_with_old_separation'] += 1
    counts['complete_four_source_cases'] += 1
    return {'R': R, 'r': r, 'j': j, 'weight_bits': w.bit_length(),
            'N_bits': N.bit_length(), 'S_bits': S.bit_length(),
            'a_bits': a.bit_length(), 'b_bits': b.bit_length(),
            'N_clock': nclock, 'S_clock': sclock,
            'old_separated_horizon': 11*j-3 if j else None}


def complete_paths(counts):
    cases = set()
    for R in range(14, 23):
        for r in range(5, 13):
            for j in range(9):
                cases.add((R, r, j, weight(R, r, j)))
    for R in [128, 1024, 16384]:
        for r in [5, 9]:
            for j in [1, 16]:
                cases.add((R, r, j, weight(R, r, j, 1)))
    for r in [128, 512, 1024, 4096]:
        for j in [1, 16]:
            cases.add((14, r, j, weight(14, r, j)))
    for j in [64, 128, 512, 1024, 4096]:
        for r in [5, 16]:
            cases.add((14, r, j, weight(14, r, j)))
    maxima, rows = Counter(), []
    for R, r, j, w in sorted(cases):
        row = full_meeting(R, r, j, w, counts)
        for key, value in row.items():
            if value is not None:
                maxima[key] = max(maxima[key], value)
        if R >= 16384 or r >= 512 or j >= 512:
            rows.append(row)
    return {'distinct_cases': len(cases), 'maxima': dict(maxima), 'large_rows': rows,
            'regular_R_interval': [14, 22], 'regular_r_interval': [5, 12],
            'regular_j_interval': [0, 8], 'additional_R': [128, 1024, 16384],
            'additional_r': [128, 512, 1024, 4096], 'additional_j': [64, 128, 512, 1024, 4096],
            'scope': 'The main and fourth sources have full ordinary, shortcut and inverse replays of their meeting, with checkpoints at both block boundaries. Both older partners have their full prefixes replayed. For j>0 their separated exit windows are also replayed independently. No earliest-meeting claim is made.'}


def modular_checks(counts):
    pairs = [(r, j) for r in range(5, 13) for j in range(17)]
    pairs += [(128, 128), (512, 1), (5, 512)]
    rows = []
    for r, j in pairs:
        m, K = 57+11*r, 9+11*j
        D, E = 1 << m, 1 << K
        M = D*E*64
        A = pow(3, 35+7*r, M)
        eps = 23*pow(pow(3, 6+7*j, 64), -1, 64) % 64
        C = 7*A+D+(64-eps)*D*E
        precision = m+K+3
        seed = affine_seed(precision, A, C)
        for B in [0, 1 << (r+j+32)]:
            R = seed+(1 << precision)*(B+14)
            assert R > B and R >= 14
            X = pow(9, R, M)
            assert (A*(X+7)+D) % M == D*E*eps
            u_mod, rem = divmod(X+7, D)
            assert rem == 0
            a_mod = pow(3, 33+7*r, E*64)*u_mod % (E*64)
            q_mod, rem = divmod(9*a_mod+1, E)
            assert rem == 0 and q_mod % 64 == eps
            assert a_mod % 64 == 7 and q_mod % 2 == 1
            assert pow(3, 6+7*j, 64)*q_mod % 64 == 23
            counts['modular_pure_lifts'] += 1
            if r >= 128 or j >= 128:
                rows.append({'r': r, 'j': j, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'regular_r_interval': [5, 12], 'regular_j_interval': [0, 16],
            'additional_pairs': [[128, 128], [512, 1], [5, 512]],
            'bounds': ['0', '2**(r+j+32)'], 'large_rows': rows,
            'scope': 'Pure exponent coordinates and required residues are checked by modular powers. No enormous pure starting value or full trajectory is materialized. Universal existence and least-source exclusion are separate kernel proofs.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        r = 5
        for j in [1, 16]:
            w = weight(R, r, j)
            starts, ends, clocks, a, b, X, _ = coordinates(R, r, j, w)
            for n, t, expected in zip([4*X-5, 243*X-1, 14348907*X-1, 1594323*X-1],
                                      [91+18*r, 89+18*r, 69+18*r, 164+18*(r-5)], ends):
                assert endpoint(n, t, counts, 'larger_transition_steps') == expected
            target = endpoint(ends[0], 27+18*j, counts, 'larger_meeting_steps')
            assert endpoint(ends[3], 29+18*j, counts, 'larger_meeting_steps') == target
            separated_windows(a, 11*j-3, counts)
            rows.append({'R': R, 'r': r, 'j': j, 'N_bits': starts[0].bit_length(),
                         'S_bits': starts[3].bit_length(), 'full_growing_prefixes_replayed': False})
    return {'rows': rows,
            'scope': 'Exact weighted source coordinates, four transition tails, the later merger and older separated windows are checked. The full initial growing prefixes are not iterated.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumSeventeenFourth.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 41
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-seventeen-fourth-') as directory:
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
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir()) if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'fresh_build_count': sum(b['fresh_build'] for b in builds),
        'reused_verified_build_count': sum(b['reused_verified_build'] for b in builds),
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': [],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])}, 'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For R>=14,r>=5,w,u positive with 9^R*w+7=2^(57+11r)*u, the fourth source S=2^(2R+13)*w-1 is positive, smaller than N=4*8^R*w-5, and reaches48a-17 at clock4R+100+18r, where a=3^(33+7r)*u.',
            'If 9a+1=2^(9+11j)*q with q positive, the main and fourth scalar endpoints reach4b-17 and3b-17 at clocks16+18j and21+18j, where b=3^(6+7j)*q.',
            'For b=23mod64 these endpoints merge, giving full source clocks N:5R+117+18r+18j and S:4R+128+18r+18j. The weighted main source is excluded as least.',
            'At j>0, the two older partner exit windows remain separated from the main exit for every pair of clocks up to11j-3.',
            'For every r>=5 and window horizon H, pure exponents beyond every bound, and weights beyond every bound at any fixed R>=14, satisfy the new merger conditions while both older partner windows are separated through H.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication is required before dependency reuse. Verified objects are copied into an isolated import directory, mismatches are rebuilt, and prior reused-build provenance is retained. The new module is always fresh.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation, or credential access.',
        'finite_scope_limit': 'Full weighted meetings, full older-partner prefixes and finite exit windows, larger tail-only coordinates, modular-only pure exponents, and universal kernel statements have distinct scopes. Full shortcut replays add one common halving to the kernel meeting clocks.',
        'not_proved': [
            'A merger for every secondary exit unit or every transition source.',
            'Convergence of all family members or the smaller fourth-source family.',
            'Earliest meeting or an optimal inverse budget.',
            'Exclusion of arbitrary least counterexamples, nontrivial positive cycles, divergence, or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()

