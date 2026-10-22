"""Audit the two-partner cover and weighted doubled/quadrupled exclusions.

An optional cache reuses only dependency objects whose exact bytes match the
preceding verified manifest. A fresh build remains the default.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-phase-cover'
PRIOR = 'results/minimum-double-ladder/verification.json'
SOURCE = 'lean/MinimumPhaseCover.lean'
NOTE = 'docs/MINIMUM-PHASE-COVER.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py']
THEOREMS = [
    'third_partner_even', 'two_partner_cover', 'two_source_escape',
    'two_source_not_least', 'double_source_bounds', 'quad_source_bounds',
    'double_coordinates', 'quad_coordinates', 'double_profiles', 'quad_profiles',
    'double_three_paths', 'quad_three_paths', 'double_residual_escape',
    'quad_residual_escape', 'double_residual_not_least', 'quad_residual_not_least',
    'finite_phase_periods', 'double_exponent_exclusion', 'quad_exponent_exclusion',
]
PARAMETERS = {
    'double': {'modulus': 256, 'residue': 17, 'power': 2, 'period': 32, 'exponent': 26,
               'coefficient': 81, 'constant': 97, 'bridge_clocks': [13, 10, 12],
               'bridge_words': ['OEEOOEOEE', 'EOEOOEE', 'EOOEOEOE']},
    'quad': {'modulus': 512, 'residue': 473, 'power': 4, 'period': 64, 'exponent': 35,
             'coefficient': 243, 'constant': 251, 'bridge_clocks': [16, 14, 16],
             'bridge_words': ['OOOOOEEEEEE', 'OEEOEOEOO', 'OEEOOEOOEO']},
}


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def choose(b):
    a, rem = divmod(b-2, 3)
    assert rem == 0 and a >= 0
    if b % 4 == 0:
        return 'third_even', a, 3, 2, 0
    if b % 4 == 2:
        # One extra common halving completes both shortcut words.
        return 'double_even', 2*b+1, 4, 3, 0
    k = v2(b+1)
    q = (b+1) >> k
    if pow(3, k, 4)*q % 4 == 3:
        return 'double_odd', 2*b+1, 2*k+4, 2*k+3, k
    assert pow(3, k, 4)*q % 4 == 1
    return 'third_odd', a, 2*k+3, 2*k+2, k


def local_pair(b, counts):
    kind, p, s, t, k = choose(b)
    left, right = ordinary(p, s), ordinary(b, t)
    assert left == paired(p, s) and right == paired(b, t)
    assert left[-1] == right[-1]
    counts['local_pairs'] += 1
    counts['local_ordinary_steps'] += s+t
    return kind, p, s, t, k, left[-1]


def generic_checks(counts):
    branches = Counter()
    for a in range(8192):
        kind, *_ = local_pair(3*a+2, counts)
        branches[kind] += 1
    for k in list(range(1, 129))+[512, 1024, 4096]:
        for q in [3, 9]:
            _, _, _, _, actual_k, _ = local_pair((1 << k)*q-1, counts)
            assert actual_k == k
            counts['generic_long_odd_blocks'] += 1
    profiles = [(1536, 541, 13, 243, 86), (2304, 818, 10, 486, 173),
                (256, 86, 12, 81, 28), (18432, 12127, 16, 2187, 1439),
                (9216, 6061, 14, 4374, 2879), (1024, 669, 16, 729, 479)]
    for u in list(range(512))+[2**128+17, 3**100+5]:
        for A, B, t, D, E in profiles:
            path = ordinary(A*u+B, t)
            assert path == paired(A*u+B, t) and path[-1] == D*u+E
            counts['generic_bridge_paths'] += 1
            counts['generic_bridge_steps'] += t
    return {'a_interval': [0, 8191], 'branch_counts': dict(branches),
            'long_k_interval': [1, 128], 'additional_long_k': [512, 1024, 4096],
            'long_odd_units': [3, 9], 'bridge_u_interval': [0, 511],
            'additional_bridge_u': ['2**128+17', '3**100+5'],
            'scope': 'Finite local meetings exercise all four scalar branches and arbitrarily parameterized examples. The universal scalar cover is separately kernel proved. The double-even replay appends one common halving to the kernel base identity.'}


def seed(phase, R):
    p = PARAMETERS[phase]
    w = p['residue']*pow(pow(9, R, p['modulus']), -1, p['modulus']) % p['modulus']
    assert w > 0 and w % 2 == 1
    return w


def long_weight(phase, R, k, exit_residue):
    p = PARAMETERS[phase]
    shift = 8 if phase == 'double' else 9
    modulus = 1 << (k+shift+2)
    eps = exit_residue*pow(pow(3, k, 4), -1, 4) % 4
    correction = p['modulus']-p['constant']
    w = ((1 << (k+shift))*eps-correction)*pow(p['coefficient']*9**R, -1, modulus) % modulus
    assert w > 0 and w % 2 == 1
    X = 9**R*w
    assert X % p['modulus'] == p['residue']
    b, rem = divmod(p['coefficient']*X-p['constant'], p['modulus'])
    assert rem == 0 and v2(b+1) == k
    assert pow(3, k, 4)*((b+1) >> k) % 4 == exit_residue
    return w


def modular_checks(counts):
    for phase, p in PARAMETERS.items():
        assert pow(9, p['period'], p['modulus']) == 1
        assert pow(9, p['exponent'], p['modulus']) == p['residue']
        for j in range(129):
            R = (1 << j)+2
            w0 = seed(phase, R)
            for h in range(8):
                w = w0+p['modulus']*h
                assert pow(9, R, p['modulus'])*w % p['modulus'] == p['residue']
                counts['modular_weight_examples'] += 1
            pure_R = p['period']*(1 << j)+p['exponent']
            assert pow(9, pure_R, p['modulus']) == p['residue']
            counts['modular_pure_examples'] += 1
    return {'j_interval': [0, 128], 'h_interval': [0, 7],
            'weighted_R': '2**j+2', 'pure_R': 'period*2**j+exponent',
            'scope': 'Only modular powers and exponent/weight coordinates are computed. The enormous full sources are not materialized.'}


def endpoint(n, t, counts, key, growing_prefix=0):
    initial = n
    for j in range(t):
        n = 3*n+1 if n % 2 else n//2
        assert n > 0
        if j < growing_prefix:
            assert n >= initial
            counts['finite_prefix_lower_checks'] += 1
    counts[key] += t
    return n


def complete_word(n, t):
    word = []
    while t:
        if n % 2:
            assert t >= 2
            n = (3*n+1)//2
            word.append('O')
            t -= 2
        else:
            n //= 2
            word.append('E')
            t -= 1
    return ''.join(word), n


def coordinates(phase, R, w):
    p = PARAMETERS[phase]
    X = 9**R*w
    assert X % p['modulus'] == p['residue']
    N = p['power']*(1 << (3*R))*w-5
    b, rem = divmod(p['coefficient']*X-p['constant'], p['modulus'])
    assert rem == 0 and b % 3 == 2
    a = (b-2)//3
    if phase == 'double':
        P, Q = (1 << (2*R+1))*w-1, 3*(1 << (3*(R-1)))*w-5
        clocks = [5*R+13, 4*R+12, 5*R+7]
        growing = [5*R, 4*R+2, 5*(R-1)]
        words = ['OOE'*R, 'O'*(2*R+1), 'OOE'*(R-1)]
        ends = [2*X-5, 3*X-1, X//3-5]
        assert 3*(N+5) == 16*(Q+5)
    else:
        P, Q = 2*(1 << (3*R))*w-5, 2*(1 << (3*(R-1)))*w-5
        clocks = [5*R+16, 5*R+14, 5*R+11]
        growing = [5*R, 5*R, 5*(R-1)]
        words = ['OOE'*R, 'OOE'*R, 'OOE'*(R-1)]
        ends = [4*X-5, 2*X-5, 2*(X//9)-5]
        assert N+5 == 2*(P+5) == 16*(Q+5)
    assert 0 < P < N and 0 < Q < N and a > 0
    return N, [P, Q], b, a, clocks, growing, words, ends


def full_pair(phase, R, w, counts):
    N, candidates, b, a, clocks, growing, words, ends = coordinates(phase, R, w)
    kind, partner, s, t, k, target = local_pair(b, counts)
    ix = 0 if kind.startswith('double') else 1
    P = candidates[ix]
    assert partner == [2*b+1, a][ix]
    nclock, pclock = clocks[0]+t, clocks[ix+1]+s
    assert endpoint(N, nclock, counts, 'complete_N_ordinary_steps', growing[0]) == target
    assert endpoint(P, pclock, counts, 'complete_P_ordinary_steps', growing[ix+1]) == target
    nl, nt = complete_word(b, t)
    pl, pt = complete_word(partner, s)
    assert nt == pt == target
    bridges = PARAMETERS[phase]['bridge_words']
    nw = words[0]+bridges[0]+nl
    pw = words[ix+1]+bridges[ix+1]+pl
    assert len(nw)+nw.count('O') == nclock
    assert len(pw)+pw.count('O') == pclock
    assert shortcut(N, nw, counts) == shortcut(P, pw, counts) == target
    assert inverse(target, nw[::-1], counts) == N
    assert inverse(target, pw[::-1], counts) == P
    for end, clock, expected in zip(ends, PARAMETERS[phase]['bridge_clocks'], [b, 2*b+1, a]):
        path = ordinary(end, clock)
        assert path == paired(end, clock) and path[-1] == expected
        counts['all_source_bridge_steps'] += clock
    counts['complete_pairs'] += 1
    counts[phase+'_complete_pairs'] += 1
    return {'phase': phase, 'R': R, 'weight_bits': w.bit_length(), 'branch': kind,
            'N_bits': N.bit_length(), 'P_bits': P.bit_length(), 'block_length': k,
            'N_clock': nclock, 'P_clock': pclock}


def complete_paths(counts):
    pairs = set()
    for phase, p in PARAMETERS.items():
        for h in list(range(33))+[128, 256]:
            pairs.add((phase, p['period']*h+p['exponent'], 1))
        for R in range(2, 25):
            w0 = seed(phase, R)
            for h in range(8):
                pairs.add((phase, R, w0+p['modulus']*h))
        for k in list(range(1, 65))+[128, 512, 1024, 4096]:
            for g in [1, 3]:
                pairs.add((phase, 2, long_weight(phase, 2, k, g)))
    maxima, branches, rows = Counter(), Counter(), []
    for phase, R, w in sorted(pairs):
        row = full_pair(phase, R, w, counts)
        branches[phase+'_'+row['branch']] += 1
        for key in ['R', 'N_bits', 'P_bits', 'weight_bits', 'block_length']:
            maxima[key] = max(maxima[key], row[key])
        if R > 2048 or row['block_length'] >= 512:
            rows.append(row)
    assert len(branches) == 8
    return {'distinct_pairs': len(pairs), 'branch_counts': dict(branches),
            'maxima': dict(maxima), 'large_rows': rows,
            'pure_h_interval': [0, 32], 'additional_pure_h': [128, 256],
            'weighted_R_interval': [2, 24], 'weighted_h_interval': [0, 7],
            'long_block_R': 2, 'long_k_interval': [1, 64], 'additional_long_k': [128, 512, 1024, 4096],
            'long_exit_residues': [1, 3],
            'scope': 'Every distinct source/phase pair has complete ordinary, shortcut, and inverse replays of its selected meeting. All three source bridges are checked. Prefix lower bounds are finite observations; no convergence beyond a meeting or general prefix-minimum theorem is asserted.'}


def larger_coordinates(counts):
    rows = []
    for phase, p in PARAMETERS.items():
        for h in [1024, 16384]:
            R = p['period']*h+p['exponent']
            N, candidates, b, a, clocks, growing, _, ends = coordinates(phase, R, 1)
            kind, partner, s, t, k = choose(b)
            ix = 0 if kind.startswith('double') else 1
            for end, clock, expected in zip(ends, p['bridge_clocks'], [b, 2*b+1, a]):
                assert endpoint(end, clock, counts, 'larger_tail_steps') == expected
            assert endpoint(b, t, counts, 'larger_tail_steps') == endpoint(partner, s, counts, 'larger_tail_steps')
            rows.append({'phase': phase, 'R': R, 'N_bits': N.bit_length(),
                         'P_bits': candidates[ix].bit_length(), 'branch': kind,
                         'block_length': k, 'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'Exact sources and endpoints are materialized. Only the three bridges and selected local meeting tails are replayed; full growing prefixes are not numerically iterated at these exponents.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumPhaseCover.'+t for t in THEOREMS}
        assert len(roots) == len(THEOREMS)
        source_text = (ROOT/source).read_text()
        assert set(re.findall(r'^theorem (\w+)', source_text, re.M)) == set(THEOREMS)
        assert not re.search(r'\b(sorry|native_decide|axiom)\b', source_text)
        assert "'MinimumPhaseCover.finite_phase_periods' does not depend on any axioms" in output
    for _, axioms in roots:
        assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}


def build(prior, lean, threads, cache):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert version == prior['lean_version']
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    old = {b['source']: b for b in prior['builds']}
    sources = list(old)+[SOURCE]
    assert len(sources) == len(set(sources)) == 38
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-phase-cover-') as directory:
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
                               'prior_compile_command': previous['command'],
                               'prior_elapsed_seconds': previous['elapsed_seconds'],
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
    parser.add_argument('--cache', type=Path, help='Optional directory of previously verified dependency objects')
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
    for name, check in [('generic_checks', generic_checks), ('modular_checks', modular_checks),
                        ('complete_paths', complete_paths), ('larger_coordinates', larger_coordinates)]:
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
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': ['finite_phase_periods'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])}, 'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For every b=3a+2, at least one of a and 2b+1 coalesces with b. The proof covers both even residues and arbitrary odd blocks.',
            'Two smaller original sources reaching those partners exclude N as least whenever N reaches b.',
            'For R>=2,w>0 and X=9^R*w=17 mod256, N=2*8^R*w-5 reaches b=(81X-97)/256; smaller sources 2^(2R+1)*w-1 and 3*8^(R-1)*w-5 reach 2b+1 and (b-2)/3.',
            'For R>=2,w>0 and X=9^R*w=473 mod512, N=4*8^R*w-5 reaches b=(243X-251)/512; smaller sources 2*8^R*w-5 and 2*8^(R-1)*w-5 reach 2b+1 and (b-2)/3.',
            'Both weighted classes are excluded as least; for w=1 the corresponding exponent classes are R=26 mod32 and R=35 mod64.',
        ],
        'cache_policy': 'A dependency is reused only if its source, prior log, and cached object match the preceding verified manifest hashes and the compiler version matches. The exact authenticated object is copied into an isolated import directory. Missing or mismatched cache entries are freshly rebuilt. The new module is always freshly built.',
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and standard libraries; no installation or credential access.',
        'finite_scope_limit': 'Kernel universality, complete finite meetings, larger short tails, and modular-only examples are distinct. No general family convergence follows from least-source exclusion.',
        'not_proved': ['Exclusion of every doubled or quadrupled exponent or arbitrary positive weight.',
                       'Convergence of all members of either family or of their partner sources.',
                       'That every possible least counterexample belongs to a covered class.',
                       'Earliest meeting, optimal inverse cost, or a uniform inverse budget.',
                       'Universal cap/residual estimates, nontrivial-cycle exclusion, divergence exclusion, or the full Collatz conjecture.'],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
