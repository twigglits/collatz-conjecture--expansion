"""Audit the complementary ladder exit, without claiming universal convergence.

Fresh kernel builds, complete positive paths, larger short-tail checks,
and modular-only examples are recorded separately.
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
from verify_minimum_ladder_block_exit import factor, inverse, lift, seed, shortcut

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-ladder-complement'
PRIOR = 'results/minimum-ladder-block-exit/verification.json'
SOURCE = 'lean/MinimumLadderComplement.lean'
NOTE = 'docs/MINIMUM-LADDER-COMPLEMENT.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py']
THEOREMS = [
    'weighted_step', 'weighted_ladder', 'smaller_source_bounds',
    'complementary_bridge', 'complementary_profile', 'complementary_coordinates',
    'complementary_escape', 'complementary_not_least', 'finite_residue_injection',
    'least_exponent_nine', 'outside_nine_not_least', 'complementary_first_target',
    'all_long_blocks_have_target', 'old_progression_resolved',
    'remaining_progression', 'remaining_profile', 'remaining_pair',
    'remaining_merge_suffices', 'half_period_flip',
    'unbounded_complementary_lifts', 'unbounded_complementary_first_targets',
]


def generic_paths(counts):
    for r in range(25):
        for q in range(6, 70):
            n, b, t = 8**r*q-5, 9**r*q-5, 5*r
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == b
            assert shortcut(n, 'OOE'*r, counts) == b
            assert inverse(b, 'EOO'*r, counts) == n
            counts['weighted_ladder_paths'] += 1
            counts['weighted_ladder_ordinary_steps'] += t
    for u in list(range(1024)) + [2**256+1, 3**128+7]:
        for n, t, b in [(32*u+1, 8, 27*u+2),
                         (384*u+196, 9, 27*u+14),
                         (256*u+129, 9, 108*u+55)]:
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == b
            counts['generic_affine_paths'] += 1
            counts['generic_affine_ordinary_steps'] += t
        assert inverse(27*u+2, 'OEOEO', counts) == 32*u+1
    for k in range(2, 33):
        for q in range(1, 513, 2):
            if (2**k*q) % 9 != 2 or (3**k*q) % 4 != 1:
                continue
            u = (2**k*q-2)//9
            b = (3**k*q-1)//4
            assert u >= 0 and 4*b+1 == 3**k*q
            for n, word, t in [(48*u+4, 'EEOE'+'O'*k+'EE', 2*k+7),
                                (32*u+1, 'OEOEO'+'EE'+'O'*(k-2)+'EO', 2*k+9)]:
                path = ordinary(n, t)
                assert path == paired(n, t) and path[-1] == b
                assert shortcut(n, word, counts) == b
                counts['generic_complementary_paths'] += 1
                counts['generic_complementary_ordinary_steps'] += t
            assert inverse(b, 'OE'+'O'*(k-2)+'EE'+'OEOEO', counts) == 32*u+1
    return {'weighted_r_interval': [0, 24], 'weighted_q_interval': [6, 69],
            'affine_u_interval': [0, 1023], 'extra_u': ['2**256+1', '3**128+7'],
            'profile_k_interval': [2, 32], 'profile_odd_q_interval': [1, 511],
            'profile_filter': '2**k*q=2 mod9 and 3**k*q=1 mod4',
            'scope': 'Every path in these finite ranges is independently replayed with ordinary steps, paired steps, and applicable shortcut and inverse words.'}


def bad_seed(k, counts):
    D = 1 << (k+4)
    eps = 1 if k % 2 == 0 else 3
    r = lift(k+3, 3, 5+(4-eps)*D, counts)
    assert (3*pow(9, r, 4*D)+5) % (4*D) == eps*D
    assert pow(3, k, 4)*eps % 4 == 1 and r % 2 == 1
    return r


def modular_checks(counts):
    assert [r for r in range(16) if pow(9, r, 128) == 73] == [9]
    counts['finite_residue_injection_cases'] = 16
    seeds = []
    for k in range(2, 129):
        r = bad_seed(k, counts)
        period = 1 << (k+3)
        M = 1 << (k+6)
        expected = (1 << (k+4))*(1 if k % 2 == 0 else 3)
        assert pow(9, period, M) == 1
        good_r = seed(k, counts)
        flipped = good_r+(1 << (k+2))
        assert flipped % period == r
        assert (3*pow(9, flipped, M)+5) % M == expected
        counts['modular_half_period_flips'] += 1
        if k <= 8:
            _, good_k, good_q = factor(good_r)
            _, bad_k, bad_q = factor(flipped)
            odd = (9**(1 << (k+2))-1)//(1 << (k+5))
            assert odd % 2 == 1 and good_k == bad_k == k
            assert bad_q == good_q+2*(3*9**good_r*odd)
            assert (3**k*good_q) % 4 == 3 and (3**k*bad_q) % 4 == 1
            counts['exact_half_period_flips'] += 1
        if k <= 10:
            seeds.append({'k': k, 'r': r, 'period': period})
        for h in range(32):
            R = r+period*(h+1)
            assert R >= 3 and R % 2 == 1
            assert (3*pow(9, R, M)+5) % M == expected
            counts['modular_complementary_examples'] += 1
    classes = Counter()
    for R in range(3, 1026):
        if R % 2 == 0:
            assert (pow(8, R, 3)-5) % 3 == 2
            classes['even_source_restriction'] += 1
        elif R % 4 == 3:
            assert R % 8 == 7 or R % 16 in (3, 11)
            classes['earlier_odd_exclusions'] += 1
        else:
            _, k, q = factor(R)
            assert k > 0
            if (3**k*q) % 4 == 3:
                classes['earlier_block_exit'] += 1
            elif k >= 2:
                classes['new_complementary_exit'] += 1
            else:
                assert k == 1 and q % 4 == 3 and R % 16 == 9
                classes['remaining_nine_mod_sixteen'] += 1
        counts['finite_exponent_classification_cases'] += 1
    for h in range(257):
        R = 512*h+5
        assert (3*pow(9, R, 4096)+5) % 4096 == 1024
        counts['old_progression_modular_cases'] += 1
        R = 16*h+9
        assert pow(9, R, 128) == 73
        counts['remaining_progression_modular_cases'] += 1
    return {'complementary_seed_k_interval': [2, 128], 'seed_rows': seeds,
            'modular_h_interval': [0, 31], 'classification_R_interval': [3, 1025],
            'classification_counts': dict(classes), 'progression_h_interval': [0, 256],
            'scope': 'The large lifted exponents are checked modulo powers of two only. Half-period flips are materialized exactly for k=2..8. Existence of arbitrarily large complementary exponents for every k is separately kernel proved. No universal uniqueness claim is made. The classification census is finite; the necessary exponent restriction is separately kernel proved.'}


def complete_complementary(R, counts):
    X, k, q = factor(R)
    assert k >= 2 and (3**k*q) % 4 == 1
    N, P = (1 << (3*R))-5, 6*(1 << (3*(R-1)))-5
    b = (3**k*q-1)//4
    nt, pt = 5*R+2*k+7, 5*R+2*k+4
    nword = 'OOE'*R+'EEOE'+'O'*k+'EE'
    pword = 'OOE'*(R-1)+'OEOEO'+'EE'+'O'*(k-2)+'EO'
    assert 0 < P < N and 4*(P+5) == 3*(N+5)
    assert pword.count('E') == R+4 and pword.count('O') == 2*R+k
    assert len(nword)+nword.count('O') == nt
    assert len(pword)+pword.count('O') == pt
    x, first_late, first_descent = N, None, None
    for t in range(nt+1):
        if t <= 5*R:
            assert x >= N
        if t < 5*R:
            assert (x % 27 == 20) == (t % 5 == 2 and t//5 > 0)
            counts['complete_growing_prefix_residue_checks'] += 1
        if t == 5*R:
            assert x == X-5
        if t >= 5*R and x % 27 == 20 and first_late is None:
            first_late = t
        if x < N and first_descent is None:
            first_descent = t
        if t < nt:
            x = 3*x+1 if x & 1 else x >> 1
    assert x == b and shortcut(N, nword, counts) == b
    y = P
    for t in range(pt):
        if t == 5*(R-1):
            assert y == 6*9**(R-1)-5
        y = 3*y+1 if y & 1 else y >> 1
    assert y == b and shortcut(P, pword, counts) == b
    assert inverse(b, pword[::-1], counts) == P
    if k >= 3:
        assert first_late == nt and b % 27 == 20
        counts['complete_first_late_target_checks'] += 1
    counts['complete_complementary_pairs'] += 1
    counts['complete_N_steps'] += nt
    counts['complete_P_steps'] += pt
    return {'R': R, 'k': k, 'N_bits': N.bit_length(), 'P_bits': P.bit_length(),
            'N_clock': nt, 'P_clock': pt, 'even_inverse_count': R+4,
            'odd_inverse_count': 2*R+k,
            'first_late_residue20_through_meeting': first_late,
            'first_forward_descent_through_meeting': first_descent}


def complete_paths(counts):
    rows, cache = [], {}
    def run(R):
        if R not in cache:
            cache[R] = complete_complementary(R, counts)
            rows.append(cache[R])
        return cache[R]
    for R in range(3, 514, 2):
        _, k, q = factor(R)
        if k >= 2 and (3**k*q) % 4 == 1:
            run(R)
    for h in range(17):
        row = run(512*h+5)
        assert row['k'] == 6 and row['N_clock'] == 5*row['R']+19
    lifted = []
    for k in range(2, 11):
        r = bad_seed(k, counts)
        R = r+(1 << (k+3))
        row = run(R)
        assert row['k'] == k
        lifted.append({'k': k, 'r': r, 'R': R})
        print('Complete complementary replay: k=%d, R=%d' % (k, R), flush=True)
    return {'small_odd_R_interval': [3, 513], 'old_progression_h_interval': [0, 16],
            'lifted_cases': lifted, 'rows': rows,
            'scope': 'Both positive paths are fully iterated from their starts. Every shortcut parity and inverse guard is checked independently. For k>=3 every ordinary clock after the ladder endpoint is checked for the first residue-20 visit. Repeated cases are reused. No convergence beyond the meeting or optimal inverse cost is inferred.'}


def remaining_paths(counts):
    rows = []
    for h in list(range(17))+[64, 256]:
        R = 16*h+9
        N, P = (1 << (3*R))-5, 6*(1 << (3*(R-1)))-5
        X = 9**R
        b, rem = divmod(9*X-17, 128)
        assert rem == 0 and b % 27 == 14
        nt, pt = 5*R+9, 5*R+4
        for n, t, end, word in [(N, nt, b, 'OOE'*R+'EEOEOEE'),
                                 (P, pt, 4*b-1, 'OOE'*(R-1)+'OEOEOE')]:
            x = n
            for _ in range(t):
                x = 3*x+1 if x & 1 else x >> 1
            assert x == end and shortcut(n, word, counts) == end
            assert inverse(end, word[::-1], counts) == n
        counts['complete_remaining_pairs'] += 1
        counts['complete_remaining_N_steps'] += nt
        counts['complete_remaining_P_steps'] += pt
        rows.append({'h': h, 'R': R, 'N_bits': N.bit_length(),
                     'N_clock': nt, 'P_clock': pt, 'same_endpoint': False})
    path = ordinary(8**9-5, 309)
    assert path == paired(8**9-5, 309) and path[-1] == 1 and 1 not in path[:-1]
    counts['remaining_member_convergence_steps'] = 309
    return {'rows': rows, 'convergent_member': {'R': 9, 'N': 134217723, 'first_arrival': 309},
            'scope': 'These complete paths reach the different endpoints b and 4*b-1. A universal merger of these endpoints has not been proved. Convergence of the single R=9 member is an independent Python check only, not a new kernel convergence certificate.'}


def larger_coordinates(counts):
    rows = []
    for k in [12, 16]:
        r = bad_seed(k, counts)
        R = r+(1 << (k+3))
        X, actual_k, q = factor(R)
        assert actual_k == k and (3**k*q) % 4 == 1
        N, P = (1 << (3*R))-5, 6*(1 << (3*(R-1)))-5
        b = (3**k*q-1)//4
        nt, pt = 2*k+7, 2*k+9
        a, c = X-5, 6*9**(R-1)-5
        path = ordinary(a, nt)
        other = ordinary(c, pt)
        assert path == paired(a, nt) and other == paired(c, pt)
        assert path[-1] == other[-1] == b
        assert b % 27 == 20 and all(x % 27 != 20 for x in path[:-1])
        assert inverse(b, 'OE'+'O'*(k-2)+'EE'+'OEOEO', counts) == c
        assert 0 < P < N and 4*(P+5) == 3*(N+5)
        counts['large_coordinate_pairs'] += 1
        counts['large_short_tail_steps'] += nt+pt
        rows.append({'k': k, 'r': r, 'R': R, 'N_bits': N.bit_length(),
                     'P_bits': P.bit_length(), 'N_tail_steps': nt,
                     'P_tail_steps': pt, 'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'The exact source and endpoint coordinates are materialized. Only the two short tails are independently replayed; the full weighted and unweighted growing prefixes rely on the kernel theorems.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-ladder-complement-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory)/(stem+'.olean')
            log = OUT/(stem+'.log')
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
                assert "'MinimumLadderComplement.finite_residue_injection' does not depend on any axioms" in result.stdout
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
    assert len(sources) == len(set(sources)) == 35
    version, builds = build(sources, args.lean, args.threads)
    counts, sections = Counter(), {}
    for name, check in [('generic_paths', generic_paths), ('modular_checks', modular_checks),
                        ('complete_paths', complete_paths), ('remaining_paths', remaining_paths),
                        ('larger_coordinates', larger_coordinates)]:
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
        'axiom_free_roots': ['finite_residue_injection'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'The weighted growing block gives Backtrack(r,2r,9^r*q-5,8^r*q-5) for q>0.',
            'For odd R>=3, k>=2, 3*9^R+5=2^(k+4)*q with q>0 and 3^k*q=1 mod4, P=6*8^(R-1)-5 is positive and smaller than N=8^R-5. It joins N at ordinary clocks 5R+2k+4 and 5R+2k+7. Inverse counts are (R+4,2R+k).',
            'For this complementary case and k>=3, the meeting is the first residue-20 visit at or after clock 5R. Combining the two exit cases gives a useful first later target for every odd factorization with k>=3.',
            'Adding 2^(k+2) to a successful exponent flips the exit condition. For each k, complementary exponents are unbounded; for each k>=3 and source bound, the kernel constructs a larger source with exact first later return delay 2k+7 and the new smaller predecessor.',
            'Every R=512h+5 is excluded as a least counterexample by the complementary path; the first later target is at clock 5R+19.',
            'A least source 8^R-5, R>=3, must have R=9 mod16 and k=1 with q=3 mod4. The remaining progression has this factorization unconditionally.',
            'For R=9 mod16, the two sources reach b=(9*9^R-17)/128 and 4b-1, with b=14 mod27. A merger of these particular endpoints would exclude N; that merger is a hypothesis of the conditional theorem, not an established universal property.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and its standard libraries; no installation or credential access.',
        'finite_scope_limit': 'Complete positive paths, larger short tails, and modular-only examples have separate ranges. Finite seed checks are separate from the kernel half-period and unbounded-lift constructions. The R=9 convergence replay is independent Python evidence only.',
        'not_proved': [
            'Convergence of every covered source or its smaller coalescing predecessor.',
            'A merger of b and 4b-1 for every remaining exponent, or exclusion of all R=9 mod16.',
            'A fixed absolute even-inverse bound for the new predecessor, or optimal inverse cost.',
            'A useful later target on every possible least-counterexample orbit, universal cap/residual estimates, nontrivial-cycle exclusion, divergence exclusion, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
