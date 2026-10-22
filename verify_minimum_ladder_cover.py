"""Audit the three-source cover and exclusion of pure ladders as least sources.

Least-counterexample exclusion, finite convergence, complete coalescing paths,
short-tail checks, and modular-only evidence have separate recorded scopes.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_minimum_inverse_locality import digest, save, ordinary, paired
from verify_minimum_ladder_block_exit import inverse, shortcut

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-ladder-cover'
PRIOR = 'results/minimum-ladder-complement/verification.json'
SOURCE = 'lean/MinimumLadderCover.lean'
NOTE = 'docs/MINIMUM-LADDER-COVER.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py']
THEOREMS = [
    'double_partner_even', 'ninth_partner_even', 'adjacent_odd_block',
    'odd_two_partner_cover', 'three_partner_cover', 'merger_transport',
    'source_bounds', 'weighted_clock', 'weighted_mersenne_clock',
    'weighted_coordinates', 'partner_profiles', 'three_sources',
    'weighted_residual_escape', 'weighted_residual_not_least',
    'all_ladder_not_least', 'finite_small_ladders', 'positive_ladder_not_least',
]


def choose(b):
    if b % 4 == 2:
        return 'double_even', 2*b+1, 3, 2, 0
    if b % 4 == 0:
        assert (b-5) % 9 == 0
        return 'ninth_even', (b-5)//9, 4, 2, 0
    k = ((b+1) & -(b+1)).bit_length()-1
    q = (b+1) >> k
    assert k > 0 and q % 2 == 1
    if (3**k*q) % 4 == 3:
        return 'double_odd', 2*b+1, 2*k+4, 2*k+3, k
    assert (3**k*q) % 4 == 1
    return 'adjacent_odd', b-1, 2*k+2, 2*k+2, k


def check_local(b, counts, prefix):
    kind, p, s, t, k = choose(b)
    left, right = ordinary(p, s), ordinary(b, t)
    assert left == paired(p, s) and right == paired(b, t)
    assert left[-1] == right[-1]
    counts[prefix+'_pairs'] += 1
    counts[prefix+'_ordinary_steps'] += s+t
    return kind, k


def generic_checks(counts):
    branches = Counter()
    for a in range(4096):
        kind, _ = check_local(9*a+5, counts, 'generic_three_partner')
        branches[kind] += 1
    for k in range(1, 65):
        for q in range(1, 64, 2):
            _, actual_k = check_local(2**k*q-1, counts, 'generic_odd_block')
            assert actual_k == k
    for u in list(range(512))+[2**128+17, 3**100+5]:
        for n, t, b in [(128*u+66, 9, 54*u+29), (128*u+60, 11, 81*u+40),
                         (256*u+237, 12, 81*u+76), (384*u+196, 9, 27*u+14)]:
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == b
            counts['generic_bridge_paths'] += 1
            counts['generic_bridge_ordinary_steps'] += t
    for R, t in [(1, 7), (2, 32)]:
        path = ordinary(8**R-5, t)
        assert path == paired(8**R-5, t) and path[-1] == 1 and 1 not in path[:-1]
        counts['small_convergence_cases'] += 1
        counts['small_convergence_steps'] += t
    return {'cover_a_interval': [0, 4095], 'cover_branch_counts': dict(branches),
            'odd_block_k_interval': [1, 64], 'odd_block_odd_q_interval': [1, 63],
            'bridge_u_interval': [0, 511], 'larger_u': ['2**128+17', '3**100+5'],
            'finite_convergence': [{'R': 1, 'N': 3, 'steps': 7}, {'R': 2, 'N': 59, 'steps': 32}],
            'scope': 'Finite generic paths independently test all four branches, arbitrary-block examples, and the three bridges. The universal cover and the two small convergence certificates are separately kernel proved.'}


def weight_seed(R):
    q = 73*pow(pow(9, R, 128), -1, 128) % 128
    assert 0 < q < 128 and q % 2 == 1
    return q


def long_weight(k, exit_residue):
    R = 3
    D = 1 << (k+7)
    modulus = 4*D
    eps = exit_residue*pow(pow(3, k, 4), -1, 4) % 4
    q = (D*eps-111)*pow(9**(R+1), -1, modulus) % modulus
    assert q > 0 and q % 2 == 1
    X = 9**R*q
    assert X % 128 == 73
    b = (9*X-17)//128
    power = ((b+1) & -(b+1)).bit_length()-1
    assert power == k and (3**k*((b+1) >> k)) % 4 == exit_residue
    return q


def modular_checks(counts):
    for j in range(129):
        R = (1 << j)+3
        seed = weight_seed(R)
        for h in range(32):
            q = seed+128*h
            assert q > 0 and pow(9, R, 128)*q % 128 == 73
            counts['modular_weight_examples'] += 1
    rows = []
    for k in list(range(1, 129))+[512, 1024, 4096]:
        for g in (1, 3):
            q = long_weight(k, g)
            counts['long_block_weight_constructions'] += 1
            if k <= 5 or k >= 512:
                rows.append({'k': k, 'exit_residue': g, 'weight_bits': q.bit_length()})
    return {'large_R_rule': '2**j+3 for j=0..128', 'modular_h_interval': [0, 31],
            'long_block_k_interval': [1, 128], 'additional_k': [512, 1024, 4096],
            'sample_long_weights': rows,
            'scope': 'Large R examples are checked only modulo 128; their sources are not materialized. The secondary-block weight construction is independently checked at the listed k values and both exit residues. The kernel theorem covers any positive weight satisfying the residue condition, without assuming this finite construction is exhaustive.'}


def full_pair(R, q, counts):
    assert R >= 3 and q > 0
    X = 9**R*q
    assert X % 128 == 73
    N = (1 << (3*R))*q-5
    candidates = [(1 << (2*R-1))*q-1, (1 << (3*(R-1)))*q-5,
                  (1 << (3*(R-2)))*(2*q)-5]
    assert all(0 < P < N for P in candidates)
    assert N+5 == 8*(candidates[1]+5) == 32*(candidates[2]+5)
    b, rem = divmod(9*X-17, 128)
    assert rem == 0 and b % 27 == 14
    kind, partner, tail_p, tail_n, k = choose(b)
    ix = 0 if kind.startswith('double') else 1 if kind == 'adjacent_odd' else 2
    P = candidates[ix]
    nprefix, pprefix = 5*R+9, [4*R+7, 5*R+6, 5*R+2][ix]
    nclock, pclock = nprefix+tail_n, pprefix+tail_p
    nword = 'OOE'*R+'EEOEOEE'
    pword = ['O'*(2*R-1)+'EOEOEO', 'OOE'*(R-1)+'EEOOOOE',
             'OOE'*(R-2)+'OEEOEOOE'][ix]
    assert len(nword)+nword.count('O') == nprefix
    assert len(pword)+pword.count('O') == pprefix
    nlocal, plocal = ordinary(b, tail_n), ordinary(partner, tail_p)
    assert nlocal == paired(b, tail_n) and plocal == paired(partner, tail_p)
    assert nlocal[-1] == plocal[-1]
    target = nlocal[-1]
    x, first_descent = N, None
    for t in range(nclock+1):
        if t <= 5*R:
            assert x >= N
            counts['observed_growing_prefix_lower_checks'] += 1
        if t == 5*R:
            assert x == X-5
        if t == nprefix:
            assert x == b
        if x < N and first_descent is None:
            first_descent = t
        if t < nclock:
            x = 3*x+1 if x & 1 else x >> 1
    assert x == target and shortcut(N, nword, counts) == b
    y = P
    for t in range(pclock+1):
        if t == pprefix:
            assert y == partner
        if t < pclock:
            y = 3*y+1 if y & 1 else y >> 1
    assert y == target and shortcut(P, pword, counts) == partner
    assert inverse(partner, pword[::-1], counts) == P
    counts['complete_pairs'] += 1
    counts['complete_'+kind+'_pairs'] += 1
    counts['complete_N_steps'] += nclock
    counts['complete_P_steps'] += pclock
    counts['independent_local_tail_steps'] += tail_n+tail_p
    return {'R': R, 'weight_hex': hex(q), 'kind': kind, 'block_k': k,
            'N_bits': N.bit_length(), 'P_bits': P.bit_length(),
            'N_clock': nclock, 'P_clock': pclock,
            'first_forward_descent_through_meeting': first_descent}


def complete_paths(counts):
    cache, rows = {}, []
    def run(R, q):
        key = R, q
        if key not in cache:
            cache[key] = full_pair(R, q, counts)
            rows.append(cache[key])
        return cache[key]
    for R in range(3, 33):
        for h in range(8):
            run(R, weight_seed(R)+128*h)
    for h in list(range(129))+[512, 1024]:
        run(16*h+9, 1)
    print('Complete small weighted and pure-ladder paths passed', flush=True)
    for k in list(range(1, 129))+[512, 1024, 4096]:
        for g in (1, 3):
            row = run(3, long_weight(k, g))
            assert row['block_k'] == k
            assert row['kind'] == ('adjacent_odd' if g == 1 else 'double_odd')
        if k in (1, 64, 128, 512, 1024, 4096):
            print('Both complete long-block exits passed: k=%d' % k, flush=True)
    return {'small_weighted_R_interval': [3, 32], 'weight_h_interval': [0, 7],
            'pure_ladder_h_interval': [0, 128], 'extra_pure_h': [512, 1024],
            'long_block_k_interval': [1, 128], 'extra_long_k': [512, 1024, 4096],
            'rows': rows,
            'scope': 'Both paths are completely iterated from their positive sources to the common endpoint. The prefixes are independently replayed with shortcut parities and inverse guards; local tails are replayed using both ordinary and paired steps, including endpoints after an unpaired odd operation. Repeated source pairs are reused. Prefix lower bounds are finite observations for the weighted examples. Universal convergence and earliest or optimal coalescence are not inferred.'}


def larger_coordinates(counts):
    rows = []
    for R in [65545, 1048585]:
        X = 9**R
        N = (1 << (3*R))-5
        b = (9*X-17)//128
        kind, partner, tp, tn, k = choose(b)
        if kind.startswith('double'):
            P, start, bridge = (1 << (2*R-1))-1, 3**(2*R-1)-1, 9
        elif kind == 'adjacent_odd':
            P, start, bridge = (1 << (3*(R-1)))-5, 9**(R-1)-5, 11
        else:
            P, start, bridge = 2*(1 << (3*(R-2)))-5, 2*9**(R-2)-5, 12
        assert 0 < P < N
        npath = ordinary(X-5, 9+tn)
        ppath = ordinary(start, bridge+tp)
        assert npath == paired(X-5, 9+tn) and ppath == paired(start, bridge+tp)
        assert npath[9] == b and ppath[bridge] == partner
        assert npath[-1] == ppath[-1]
        counts['large_coordinate_pairs'] += 1
        counts['large_short_tail_steps'] += 9+tn+bridge+tp
        rows.append({'R': R, 'kind': kind, 'block_k': k,
                     'N_bits': N.bit_length(), 'P_bits': P.bit_length(),
                     'N_tail_steps': 9+tn, 'P_tail_steps': bridge+tp,
                     'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'The exact sources and algebraic coordinates are materialized. Only the short tails are replayed; the full prefixes are not numerically iterated at these larger exponents.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-ladder-cover-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj, log = Path(directory)/(stem+'.olean'), OUT/(stem+'.log')
            command = [lean, '-j', str(threads), '-o', str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory,
                                             LEAN_NUM_THREADS=str(threads)))
            log.write_text(result.stdout)
            assert result.returncode == 0, (source, result.stdout)
            assert not any(s in result.stdout for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == SOURCE:
                assert {n for n, _ in roots} == {stem+'.'+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                source_text = (ROOT/source).read_text()
                assert set(re.findall(r'^theorem (\w+)', source_text, re.M)) == set(THEOREMS)
                assert not re.search(r'\b(sorry|native_decide|axiom)\b', source_text)
                assert "'MinimumLadderCover.finite_small_ladders' does not depend on any axioms" in result.stdout
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'threads': threads, 'returncode': 0,
                           'fresh_build': True, 'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic()-started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--threads', type=int, default=min(16, os.cpu_count() or 1))
    args = parser.parse_args()
    assert args.threads > 0
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT/name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [SOURCE]
    assert len(sources) == len(set(sources)) == 36
    version, builds = build(sources, args.lean, args.threads)
    counts, sections = Counter(), {}
    for name, check in [('generic_checks', generic_checks), ('modular_checks', modular_checks),
                        ('complete_paths', complete_paths), ('larger_coordinates', larger_coordinates)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources + [Path(__file__).name, NOTE, PRIOR] + HELPERS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'kernel_theorems_audited': len(THEOREMS),
        'axiom_free_roots': ['finite_small_ladders'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For b=9a+5, at least one of 2b+1, b-1, and a coalesces with b. The odd case is proved for every block length by odd factorization and the half-source meeting theorem.',
            'For R>=3, q>0, and 9^R*q=73 mod128, the three positive sources 2^(2R-1)*q-1, 8^(R-1)*q-5, and 2*8^(R-2)*q-5 are smaller than N=8^R*q-5 and reach the three partners of b=(9^(R+1)*q-17)/128. At least one coalesces with N.',
            'The whole residual weighted class is excluded as least counterexamples, with no unproved merger hypothesis.',
            'Combining this with the earlier exponent restriction excludes every 8^R-5 with R>=3 as a least counterexample. Kernel convergence certificates for R=1,2 extend the exclusion to every positive R.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and standard libraries; no installation or credential access.',
        'finite_scope_limit': 'Complete paths, larger short tails, and modular-only examples have separate ranges. The cover is kernel proved for all parameters; finite tests do not replace it. Only the two small family members have new convergence certificates.',
        'not_proved': [
            'Convergence of every 8^R-5 or of its smaller coalescing sources.',
            'That an arbitrary least counterexample belongs to the pure ladder family or to the weighted residual residue class.',
            'A merger of the previously considered endpoints b and 4b-1 for every remaining exponent.',
            'Universal exclusion of all weights without the residue condition, earliest coalescence, optimal inverse costs, or a new uniform inverse budget.',
            'Universal cap/residual estimates, nontrivial-cycle exclusion, divergence exclusion, or the positive-integer Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
