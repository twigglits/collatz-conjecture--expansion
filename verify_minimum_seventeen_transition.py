"""Audit the transition into variable negative-seventeen blocks.

Kernel proofs, complete positive coalescences, short-tail coordinates, and
modular-only pure exponents have deliberately separate verification scopes.
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
OUT = ROOT / 'results/minimum-seventeen-transition'
PRIOR = 'results/minimum-phase-cover/verification.json'
SOURCE = 'lean/MinimumSeventeenTransition.lean'
NOTE = 'docs/MINIMUM-SEVENTEEN-TRANSITION.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py']
THEOREMS = ["bridge_33","bridge_1702","bridge_fifteen","bridge_clocks","base_profiles","source_bounds","source_prefixes","base_three_sources","cycle_lift","three_sources","even_exit_profiles","odd_exit_profiles","scalar_cover","weighted_escape","weighted_not_least","powered_unit","finite_odd_targets","lifted_exponents","unbounded_pure_escape"]
CYCLE = 'OOOOEOOOEEE'


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def shadow_word(magnitude):
    word = []
    while magnitude != 17:
        assert len(word) < 1000
        if magnitude % 2:
            magnitude = (3*magnitude-1)//2
            word.append('O')
        else:
            magnitude //= 2
            word.append('E')
    return ''.join(word)


BRIDGES = [shadow_word(c) for c in [33, 1702, 100442350]]
assert [(len(w)-w.count('O'), w.count('O')) for w in BRIDGES] == [(5, 7), (13, 11), (33, 18)]


def endpoint(n, t, counts, key):
    for _ in range(t):
        n = 3*n+1 if n % 2 else n//2
        assert n > 0
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


def local_choice(a):
    if a % 64 == 13:
        # Kernel clocks are 7 and 12. One shared halving completes both words.
        return 'even', 0, 8, 13, 0
    assert a % 64 == 61
    b = (729*a-149)//32
    assert b == 1458*((a-61)//64)+1385
    k = v2(b+1)
    q = (b+1) >> k
    g = pow(3, k, 4)*q % 4
    if g == 3:
        return 'double_odd', 0, 2*k+10, 2*k+15, k
    assert g == 1
    return 'adjacent_odd', 1, 2*k+19, 2*k+14, k


def local_pair(a, counts):
    kind, ix, s, t, k = local_choice(a)
    n, p = 72*a-17, [81*a-17, 64*a-17][ix]
    left, right = ordinary(p, s), ordinary(n, t)
    assert left == paired(p, s) and right == paired(n, t)
    assert left[-1] == right[-1]
    counts['local_pairs'] += 1
    counts['local_ordinary_steps'] += s+t
    return kind, ix, s, t, k, left[-1]


def generic_checks(counts):
    bridges = [(4096, 33, 19, 2187), (2**24, 1702, 35, 3**11),
               (2**51, 100442350, 69, 3**18)]
    for q in list(range(1, 257))+[2**128+1, 3**128+7]:
        for (A, B, t, E), word in zip(bridges, BRIDGES):
            n, expected = A*q-B, E*q-17
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == expected
            assert shortcut(n, word, counts) == expected
            assert inverse(expected, word[::-1], counts) == n
            counts['bridge_paths'] += 1
            counts['bridge_ordinary_steps'] += t
    branches = Counter()
    for v in range(2048):
        for e in [13, 61]:
            kind, *_ = local_pair(64*v+e, counts)
            branches[kind] += 1
    for c in range(1, 64, 2):
        for e in [13, 61]:
            solutions = [h for h in range(64) if c*h % 64 == e]
            assert len(solutions) == 1
            counts['odd_target_permutations'] += 1
    for d in range(5):
        for v in range(1, 16, 2):
            for h in range(17):
                if d == 0:
                    U = h*v
                else:
                    U, rem = divmod(pow(1+64*d*v, h)-1, 64*d)
                    assert rem == 0
                assert (1+64*d*v)**h == 1+64*d*U and U % 64 == h*v % 64
                counts['powered_unit_examples'] += 1
    return {'bridge_q_interval': [1, 256], 'additional_q': ['2**128+1', '3**128+7'],
            'bridge_words': BRIDGES, 'cycle_word': CYCLE,
            'scalar_v_interval': [0, 2047], 'scalar_branches': dict(branches),
            'scope': 'Finite bridge and exit replays, odd multiplier permutations, and exact power identities supplement separate universal kernel proofs.'}


def weight(R, r, e, offset=0):
    m = 57+11*r
    modulus = 1 << (m+6)
    u0 = e*pow(pow(3, 33+7*r, 64), -1, 64) % 64
    w = (((1 << m)*u0-7)*pow(pow(9, R, modulus), -1, modulus)) % modulus
    w += offset*modulus
    assert w > 0
    return w


def long_weight(R, r, k, g):
    m = 57+11*r
    unit_modulus = 1 << (k+7)
    q0 = g*pow(pow(3, k, 4), -1, 4) % 4
    u0 = (117+(1 << (k+5))*q0)*pow(729*pow(3, 33+7*r, unit_modulus), -1, unit_modulus) % unit_modulus
    modulus = (1 << m)*unit_modulus
    w = (((1 << m)*u0-7)*pow(pow(9, R, modulus), -1, modulus)) % modulus
    u, rem = divmod(9**R*w+7, 1 << m)
    a = 3**(33+7*r)*u
    assert rem == 0 and a % 64 == 61
    b = (729*a-149)//32
    assert v2(b+1) == k and pow(3, k, 4)*((b+1) >> k) % 4 == g
    return w


def coordinates(R, w, r):
    assert R >= 14 and w > 0
    X = 9**R*w
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0
    a = 3**(33+7*r)*u
    assert a % 64 in [13, 61] and u % 2 == 1
    N = 4*(1 << (3*R))*w-5
    candidates = [(1 << (2*R+5))*w-1, (1 << (2*R+15))*w-1]
    assert all(0 < p < N for p in candidates)
    clocks = [5*R+91+18*r, 4*R+99+18*r, 4*R+99+18*r]
    ends = [72*a-17, 81*a-17, 64*a-17]
    words = ['OOE'*R+BRIDGES[0]+CYCLE*(r+4),
             'O'*(2*R+5)+BRIDGES[1]+CYCLE*(r+3),
             'O'*(2*R+15)+BRIDGES[2]+CYCLE*r]
    assert all(len(word)+word.count('O') == t for word, t in zip(words, clocks))
    return N, candidates, a, clocks, ends, words, X


def full_pair(R, w, r, counts):
    N, candidates, a, clocks, ends, words, X = coordinates(R, w, r)
    kind, ix, s, t, k, target = local_pair(a, counts)
    P = candidates[ix]
    nclock, pclock = clocks[0]+t, clocks[ix+1]+s
    assert endpoint(N, nclock, counts, 'complete_N_ordinary_steps') == target
    assert endpoint(P, pclock, counts, 'complete_P_ordinary_steps') == target
    nl, nt = complete_word(ends[0], t)
    pl, pt = complete_word(ends[ix+1], s)
    assert nt == pt == target
    nw, pw = words[0]+nl, words[ix+1]+pl
    assert len(nw)+nw.count('O') == nclock and len(pw)+pw.count('O') == pclock
    assert shortcut(N, nw, counts) == shortcut(P, pw, counts) == target
    assert inverse(target, nw[::-1], counts) == N
    assert inverse(target, pw[::-1], counts) == P
    # Also replay the unselected third source through its entire prescribed path.
    j = 1-ix
    other = candidates[j]
    assert endpoint(other, clocks[j+1], counts, 'other_source_ordinary_steps') == ends[j+1]
    assert shortcut(other, words[j+1], counts) == ends[j+1]
    assert inverse(ends[j+1], words[j+1][::-1], counts) == other
    counts['complete_pairs'] += 1
    return {'R': R, 'r': r, 'weight_bits': w.bit_length(), 'exit_residue': a % 64,
            'branch': kind, 'N_bits': N.bit_length(), 'P_bits': P.bit_length(),
            'late_odd_block': k, 'N_clock': nclock, 'P_clock': pclock}


def complete_paths(counts):
    cases = set()
    for R in range(14, 25):
        for r in range(17):
            for e in [13, 61]:
                cases.add((R, r, weight(R, r, e)))
    for R in [128, 1024, 16384]:
        for r in [0, 7, 32]:
            for e in [13, 61]:
                cases.add((R, r, weight(R, r, e, 1)))
    for r in [64, 128, 512, 1024, 4096]:
        for R in [14, 17]:
            for e in [13, 61]:
                cases.add((R, r, weight(R, r, e)))
    for r in [0, 3, 32]:
        for k in list(range(1, 33))+[64, 128, 512, 1024, 4096]:
            for g in [1, 3]:
                cases.add((14, r, long_weight(14, r, k, g)))
    maxima, branches, rows = Counter(), Counter(), []
    for R, r, w in sorted(cases):
        row = full_pair(R, w, r, counts)
        branches[row['branch']] += 1
        for key in ['R', 'r', 'N_bits', 'P_bits', 'weight_bits', 'late_odd_block']:
            maxima[key] = max(maxima[key], row[key])
        if R > 1024 or r >= 512 or row['late_odd_block'] >= 512:
            rows.append(row)
    assert set(branches) == {'even', 'double_odd', 'adjacent_odd'}
    return {'distinct_pairs': len(cases), 'branches': dict(branches),
            'maxima': dict(maxima), 'large_rows': rows,
            'regular_R_interval': [14, 24], 'regular_r_interval': [0, 16],
            'additional_R': [128, 1024, 16384], 'additional_r': [64, 128, 512, 1024, 4096],
            'long_odd_r': [0, 3, 32], 'long_odd_k_interval': [1, 32],
            'additional_long_k': [64, 128, 512, 1024, 4096],
            'scope': 'Both complete meeting paths and the full third source path are independently replayed by ordinary steps, shortcut steps, and inverse guards. These are weighted sources, not huge pure exponent materializations.'}


def modular_lift(j):
    # Compute liftExponent(j) without ever constructing 9**liftExponent(j).
    modulus = 1 << (j+3)
    A, z, power = 0, 1, 9 % modulus
    for k in range(j):
        if ((z+7) >> (k+3)) & 1:
            A += 1 << k
            z = z*power % modulus
        assert (z+7) % (1 << (k+4)) == 0
        power = power*power % modulus
    assert A < (1 << j) and (pow(9, A, modulus)+7) % modulus == 0
    return A


def modular_checks(counts):
    rows = []
    for r in list(range(65))+[128, 256, 1024]:
        m = 57+11*r
        D, T = 1 << m, 1 << (m-3)
        modulus = D*64
        A = modular_lift(m+3)
        base = pow(9, A, modulus)
        assert (base+7) % modulus == 0 and base % 64 == 57
        top = pow(9, T, modulus)
        v, rem = divmod(top-1, D)
        assert rem == 0 and v % 2 == 1
        coefficient = 57*pow(3, 33+7*r, 64)*v % 64
        for e in [13, 61]:
            h0 = e*pow(coefficient, -1, 64) % 64
            for B in [0, 2**r+17, 2**(r+128)]:
                h = h0+64*(B+14)
                R = A+T*h
                assert R > B and R >= 14
                u_mod, rem = divmod(pow(9, R, modulus)+7, D)
                assert rem == 0
                assert pow(3, 33+7*r, 64)*u_mod % 64 == e and u_mod % 2 == 1
                counts['modular_pure_exponents'] += 1
                if r >= 128:
                    rows.append({'r': r, 'e': e, 'B_bits': B.bit_length(), 'R_bits': R.bit_length()})
    # Small exact exponent lifts independently test the modular implementation.
    for j in range(10):
        A = modular_lift(j)
        assert (9**A+7) % (1 << (j+3)) == 0
        counts['small_exact_lifts'] += 1
    return {'r_interval': [0, 64], 'additional_r': [128, 256, 1024],
            'bounds': ['0', '2**r+17', '2**(r+128)'], 'large_rows': rows,
            'scope': 'Pure exponents and their congruences are checked with modular powers only. Their enormous 9**R, positive starting values, quotients, and full trajectories are not materialized. Existence and exclusion for every r and bound are separate kernel theorems.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        for r, e in [(0, 13), (16, 61)]:
            w = weight(R, r, e)
            N, candidates, a, clocks, ends, words, X = coordinates(R, w, r)
            kind, ix, s, t, k, target = local_pair(a, counts)
            # Only tails beginning after the growing ladder/Mersenne prefixes.
            starts = [4*X-5, 243*X-1, 14348907*X-1]
            tail_clocks = [91+18*r, 89+18*r, 69+18*r]
            for n, steps, expected in zip(starts, tail_clocks, ends):
                assert endpoint(n, steps, counts, 'larger_transition_tail_steps') == expected
            rows.append({'R': R, 'r': r, 'N_bits': N.bit_length(),
                         'P_bits': candidates[ix].bit_length(), 'branch': kind,
                         'full_prefixes_replayed': False})
    return {'rows': rows,
            'scope': 'Exact weighted source and endpoint coordinates are materialized; only the transition and exit tails are replayed. Full growing prefixes are not iterated.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumSeventeenTransition.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 39
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-seventeen-transition-') as directory:
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
    parser.add_argument('--cache', type=Path, help='Previously verified dependency objects')
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
            'Three positive source paths are proved for every R,w,r,u with w,u positive and 9^R*w+7=2^(57+11r)*u. Their endpoints are 72a-17,81a-17,64a-17 with a=3^(33+7r)*u.',
            'For R>=14 both Mersenne partners are strictly positive and smaller than N=4*8^R*w-5.',
            'Whenever a=13 or61 mod64, at least one partner coalesces with N. The odd exit covers every subsequent odd-block length and either exit residue.',
            'The whole specified weighted class is excluded as least positive counterexamples, without a convergence premise.',
            'For every r, every bound B, and either scalar exit e=13 or61, a pure exponent R>B with R>=14 and a positive unit u satisfying the same identities exists. Its pure source 4*8^R-5 is excluded as least.',
        ],
        'cache_policy': 'Only dependencies whose source, prior log, object bytes, and compiler version authenticate against the preceding manifest are reused. The authenticated object is copied into an isolated import directory; a missing or mismatched object is rebuilt. Prior reused-build provenance is retained. The new module is always fresh.',
        'external_dependency': 'Lean 4.33.1 and standard libraries. No external mathematical premise, new installation, or credential access.',
        'finite_scope_limit': 'Complete finite positive coalescences, larger short-tail coordinates, modular-only pure exponents, and universal kernel theorems have separate scopes.',
        'not_proved': [
            'A merger for all scalar residues or exclusion of all quadrupled exponents and weights.',
            'Convergence of every family member or every smaller Mersenne partner.',
            'That any arbitrary least counterexample belongs to a covered source class.',
            'Earliest meetings, optimal inverse costs, or a uniform inverse budget.',
            'Universal cap/residual estimates, nontrivial-cycle exclusion, divergence exclusion, or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()

