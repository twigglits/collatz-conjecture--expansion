"""Audit doubled-ladder coalescence and its exact exponent restriction.

Kernel proofs, complete finite paths, coordinate-only checks, and modular-only
checks have separate scopes. No general convergence claim is made.
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
OUT = ROOT / 'results/minimum-double-ladder'
PRIOR = 'results/minimum-ladder-cover/verification.json'
SOURCE = 'lean/MinimumDoubleLadder.lean'
NOTE = 'docs/MINIMUM-DOUBLE-LADDER.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py']
THEOREMS = [
    'nine_quotient_mod_four', 'nine_unit_lift', 'nine_unit_positive',
    'adjacent_bridges', 'double_source_bounds', 'weighted_adjacent_profiles',
    'weighted_double_meeting', 'weighted_double_not_least',
    'double_odd_exponent_not_least', 'double_exponent_meeting',
    'double_exponent_not_least', 'least_double_exponent_constraint',
]


def v2(n):
    assert n > 0
    return (n & -n).bit_length()-1


def ordinary_end(n, t, counts, key, growing_prefix=0):
    initial = n
    for j in range(t):
        n = 3*n+1 if n % 2 else n//2
        assert n > 0
        if j < growing_prefix:
            assert n >= initial
            counts['finite_prefix_lower_checks'] += 1
    counts[key] += t
    return n


def generic_checks(counts):
    for v in list(range(1024))+[2**128+17, 3**100+5]:
        for n, t, end in [(32*v+29, 6, 18*v+17), (16*v+12, 5, 18*v+16)]:
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == end
            counts['generic_bridge_paths'] += 1
            counts['generic_bridge_steps'] += t
    for k in range(9):
        for s in range(33):
            R = (1 << k)*s
            X = 9**R
            u, rem = divmod(X-1, 1 << (k+3))
            assert rem == 0 and u % 4 == s % 4
            if s:
                assert u > 0
            if s % 2:
                assert v2(X-1) == k+3
            counts['exact_unit_examples'] += 1
    for k in range(1, 17):
        for u in range(1, 64, 2):
            if (3**k*u) % 4 != 3:
                continue
            b = (1 << k)*9*u-1
            p, n = ordinary(b-1, 2*k+2), ordinary(b, 2*k+2)
            assert p == paired(b-1, 2*k+2) and n == paired(b, 2*k+2)
            assert p[-1] != n[-1]
            counts['opposite_exit_clock_nonmeetings'] += 1
            counts['opposite_exit_steps'] += 4*k+4
    for R in range(1, 512, 2):
        n = 2*8**R-5
        p, rem = divmod(2*n-1, 3)
        assert rem == 0 and 0 < p < n and n % 3 == 2
        path = ordinary(p, 2)
        assert path == paired(p, 2) and path[-1] == n
        counts['odd_exponent_predecessors'] += 1
        counts['odd_exponent_predecessor_steps'] += 2
    return {
        'bridge_v_interval': [0, 1023], 'additional_v': ['2**128+17', '3**100+5'],
        'exact_unit_k_interval': [0, 8], 'exact_unit_s_interval': [0, 32],
        'opposite_exit_k_interval': [1, 16], 'opposite_exit_odd_u_interval': [1, 63],
        'odd_exponent_R_interval': [1, 511],
        'scope': 'Finite affine bridges, exact unit identities, and two-step predecessors. Opposite-exit failures concern only the specified clocks, not eventual coalescence. The corresponding universal positive results are separately kernel proved.',
    }


def modular_checks(counts):
    for k in range(257):
        modulus = 1 << (k+5)
        for s in range(1, 64, 2):
            R = (1 << k)*s
            u, rem = divmod(pow(9, R, modulus)-1, 1 << (k+3))
            assert rem == 0 and u % 4 == s % 4
            assert (pow(3, k, 4)*u) % 4 == (pow(3, k, 4)*s) % 4
            counts['modular_unit_examples'] += 1
    return {
        'k_interval': [0, 256], 'odd_s_interval': [1, 63],
        'modulus': '2**(k+5)',
        'scope': 'Only modular powers and exponent coordinates are computed. The values 9**R and the Collatz sources are not materialized in this section.',
    }


def weight_seed(R, k):
    modulus = 1 << (k+5)
    unit = pow(3, k, 4)
    w = ((1 << (k+3))*unit+1)*pow(pow(9, R, modulus), -1, modulus) % modulus
    assert w > 0 and w % 2 == 1
    return w


def full_pair(R, w, counts):
    assert R > 0 and w > 0
    X = 9**R*w
    k = v2(X-1)-3
    assert k > 0
    u = (X-1) >> (k+3)
    assert u > 0 and u % 2 == 1 and (3**k*u) % 4 == 1
    N, P = (1 << (3*R+1))*w-5, (1 << (3*R))*w-5
    assert 0 < P < N and N+5 == 2*(P+5)
    a, b = (1 << k)*u, (1 << k)*9*u-1
    assert X == 8*a+1 and b == 9*a-1
    target, rem = divmod(9*3**k*u-1, 4)
    assert rem == 0 and target > 0
    nclock, pclock = 5*R+2*k+8, 5*R+2*k+7
    assert ordinary_end(N, nclock, counts, 'complete_N_ordinary_steps', 5*R) == target
    assert ordinary_end(P, pclock, counts, 'complete_P_ordinary_steps', 5*R) == target
    nword = 'OOE'*R+'OEEO'+'O'*k+'EE'
    pword = 'OOE'*R+'EE'+'O'*(k+1)+'EO'
    assert len(nword)+nword.count('O') == nclock
    assert len(pword)+pword.count('O') == pclock
    assert shortcut(N, nword, counts) == shortcut(P, pword, counts) == target
    assert inverse(target, nword[::-1], counts) == N
    assert inverse(target, pword[::-1], counts) == P
    local_n, local_p = ordinary(b, 2*k+2), ordinary(b-1, 2*k+2)
    assert local_n == paired(b, 2*k+2) and local_p == paired(b-1, 2*k+2)
    assert local_n[-1] == local_p[-1] == target
    counts['local_tail_ordinary_steps'] += 4*k+4
    counts['complete_pairs'] += 1
    return {'R': R, 'weight_bits': w.bit_length(), 'N_bits': N.bit_length(),
            'P_bits': P.bit_length(), 'secondary_block_length': k,
            'N_clock': nclock, 'P_clock': pclock, 'target_bits': target.bit_length()}


def complete_paths(counts):
    pure = set()
    for R in range(2, 513, 2):
        k = v2(R)
        s = R >> k
        if (3**k*s) % 4 == 1:
            pure.add((R, 1))
    for k in list(range(1, 13))+[14]:
        s = 3 if k % 2 else 1
        pure.add(((1 << k)*s, 1))
    weighted = set()
    for R in range(1, 17):
        for k in range(1, 17):
            seed = weight_seed(R, k)
            for h in range(4):
                weighted.add((R, seed+(h << (k+5))))
    for R in [1, 3]:
        for k in [32, 64, 128, 256, 512, 1024, 4096]:
            weighted.add((R, weight_seed(R, k)))
    rows = []
    maxima = Counter()
    for R, w in sorted(pure | weighted):
        row = full_pair(R, w, counts)
        if w == 1:
            k = v2(R)
            assert row['secondary_block_length'] == k
            assert (3**k*(R >> k)) % 4 == 1
        for key in ['R', 'N_bits', 'P_bits', 'secondary_block_length', 'weight_bits']:
            maxima[key] = max(maxima[key], row[key])
        if (w == 1 and R > 512) or row['secondary_block_length'] >= 128:
            rows.append(row)
    return {
        'distinct_pure_pairs': len(pure), 'distinct_weighted_pairs': len(weighted),
        'overlap_pairs': len(pure & weighted), 'maxima': dict(maxima), 'large_rows': rows,
        'pure_R_interval': [2, 512], 'additional_pure_k': list(range(1, 13))+[14],
        'additional_pure_s': '3 if k is odd, 1 if k is even',
        'weighted_R_interval': [1, 16], 'weighted_k_interval': [1, 16], 'weighted_h_interval': [0, 3],
        'long_weighted_R': [1, 3], 'long_weighted_k': [32, 64, 128, 256, 512, 1024, 4096],
        'scope': 'Every distinct pair has complete ordinary, parity-checked shortcut, and inverse replays; source size and meeting clocks are checked. Growing-prefix lower checks are finite observations. No convergence beyond the meetings is claimed.',
    }


def larger_coordinates(counts):
    rows = []
    for k in [16, 20]:
        R = 1 << k
        X = 9**R
        u, rem = divmod(X-1, 1 << (k+3))
        assert rem == 0 and u % 4 == 1 and (3**k*u) % 4 == 1
        N, P = (1 << (3*R+1))-5, (1 << (3*R))-5
        assert 0 < P < N and N+5 == 2*(P+5)
        target, rem = divmod(9*3**k*u-1, 4)
        assert rem == 0
        assert ordinary_end(2*X-5, 2*k+8, counts, 'larger_tail_steps') == target
        assert ordinary_end(X-5, 2*k+7, counts, 'larger_tail_steps') == target
        rows.append({'R': R, 'k': k, 'N_bits': N.bit_length(), 'P_bits': P.bit_length(),
                     'N_tail_steps': 2*k+8, 'P_tail_steps': 2*k+7,
                     'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'Exact source and endpoint coordinates are materialized, but only the tails after the growing prefixes are replayed. Full growing prefixes are not numerically iterated at these exponents.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-double-ladder-') as directory:
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
    assert len(sources) == len(set(sources)) == 37
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
        'axiom_free_roots': [], 'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For all k,s, 9^(2^k*s)=1+2^(k+3)*u for a natural u with u=s mod4; u is positive for positive s.',
            'For R,w,k,u positive, 9^R*w=1+2^(k+3)*u and 3^k*u=1 mod4, the positive source P=8^R*w-5 is smaller than N=2*8^R*w-5 and C^(5R+2k+7)(P)=C^(5R+2k+8)(N). Such N cannot be a least counterexample.',
            'For pure doubled sources, every odd R is excluded. For R=2^k*s with k,s positive and 3^k*s=1 mod4, the same meeting and exclusion hold.',
            'If a positive-exponent pure doubled source were least, its exponent would have the form R=2^k*s with k>0, s>0 odd, and 3^k*s=3 mod4.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and standard libraries; no installation or credential access.',
        'finite_scope_limit': 'Complete paths, larger short tails, and modular-only examples have separate ranges. Finite checks do not replace the universal kernel proofs. No new convergence theorem is asserted.',
        'not_proved': [
            'Exclusion of the opposite secondary exit 3^k*s=3 mod4 for every even exponent in the doubled family.',
            'Exclusion of every 4*8^R-5, or of all positive weighted sources without a residue or exit condition.',
            'Convergence of all members of any new excluded least-source family.',
            'That an arbitrary least counterexample belongs to any covered family.',
            'Earliest meeting, optimal inverse costs, general weighted-prefix minimum, or a uniform inverse budget.',
            'Universal cap/residual estimates, nontrivial-cycle exclusion, divergence exclusion, or the positive-integer Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
