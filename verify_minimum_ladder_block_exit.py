"""Verify variable post-ladder exits and the first useful later residue-20 target.

Kernel proofs, complete paths, short-tail coordinates, and modular-only
checks are recorded separately. Collatz remains unresolved.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-ladder-block-exit'
PRIOR = 'results/minimum-ladder-exit/verification.json'
SOURCE = 'lean/MinimumLadderBlockExit.lean'
NOTE = 'docs/MINIMUM-LADDER-BLOCK-EXIT.md'
HELPER = 'verify_minimum_inverse_locality.py'
THEOREMS = [
    "nine_odd_residue",
    "bridge_profile",
    "preceding_profile",
    "preceding_source_size",
    "preceding_escape",
    "preceding_not_least",
    "block_escape",
    "block_not_least",
    "three_mod_four_not_least",
    "odd_factorization",
    "least_exponent_odd",
    "least_exit_constraint",
    "finite_surviving_period",
    "surviving_progression",
    "odd_affine_lift",
    "exit_unit",
    "block_seed",
    "block_lift_odd",
    "unbounded_block_lifts",
    "unbounded_block_escapes",
    "good_odd_pair",
    "odd_block_avoids",
    "bridge_residues",
    "first_late_target",
    "unbounded_first_late_targets"
]


def inverse(b, word, counts):
    for letter in word:
        if letter == 'E':
            b *= 2
        else:
            assert b % 3 == 2
            b = (2*b-1)//3
        assert b > 0
        counts['inverse_edges'] += 1
    return b


def shortcut(n, word, counts):
    for letter in word:
        assert ('O' if n & 1 else 'E') == letter
        n = (3*n+1)//2 if n & 1 else n >> 1
        counts['shortcut_edges'] += 1
    return n


def generic_paths(counts):
    for u in list(range(1024))+[2**64+1, 3**128+7]:
        for n, t, b in [(16*u+4, 5, 3*u+1), (48*u+26, 5, 9*u+5),
                         (1152*u+724, 8, 27*u+17), (128*u+76, 10, 27*u+17)]:
            path = ordinary(n, t)
            assert path == paired(n, t) and path[-1] == b
            counts['generic_affine_paths'] += 1
            counts['generic_ordinary_steps'] += t
        assert inverse(9*u+5, 'EEOE', counts) == 48*u+26
        if (16*u+9) % 27 == 0:
            residues = [x % 27 for x in ordinary(16*u+4, 5)]
            assert residues == [22, 11, 19, 4, 2, 1]
            counts['bridge_residue_profiles'] += 1
    good = {1, 2, 17, 26}
    for k in range(33):
        for q in range(1, 257):
            n = 2**k*q-1
            if n % 27 in good:
                path = ordinary(n, 2*k)
                assert path == paired(n, 2*k)
                assert path[-1] == 3**k*q-1 and all(x % 27 != 20 for x in path)
                assert all(x % 27 in good for x in path[::2])
                counts['good_odd_blocks'] += 1
                counts['good_odd_block_ordinary_steps'] += 2*k
    return {'small_u_interval': [0, 1023], 'larger_u': ['2**64+1', '3**128+7'],
            'odd_block_k_interval': [0, 32], 'odd_block_q_interval': [1, 256],
            'scope': 'Generic affine paths, the inverse bridge, and all qualifying odd-block avoidance paths are independently replayed. These finite checks are separate from the universal kernel proofs.'}


def lift(j, A, C, counts):
    assert A % 2 == 1 and (A+C) % 8 == 0
    r = 0
    for bit in range(j):
        M = 1 << (bit+4)
        residue = (A*pow(9, r, M)+C) % M
        assert residue in (0, M//2)
        assert pow(9, 1 << bit, M) == 1+M//2
        assert (A*pow(9, r+(1 << bit), M)+C) % M == (residue+M//2) % M
        if residue:
            r += 1 << bit
        assert (A*pow(9, r, M)+C) % M == 0
        counts['lift_bit_checks'] += 1
    assert r < 1 << j
    assert (A*pow(9, r, 1 << (j+3))+C) % (1 << (j+3)) == 0
    return r


def seed(k, counts):
    D = 1 << (k+4)
    eps = 3 if k % 2 == 0 else 1
    r = lift(k+3, 3, 5+(4-eps)*D, counts)
    assert (3*pow(9, r, 4*D)+5) % (4*D) == D*eps
    assert pow(3, k, 4)*eps % 4 == 3
    return r


def lift_checks(counts):
    for j in range(11):
        for A in range(1, 32, 2):
            for c in range(4):
                C = (-A) % 8+8*c
                r = lift(j, A, C, counts)
                value = A*9**r+C
                q, rem = divmod(value, 1 << (j+3))
                assert rem == 0 and q > 0
                counts['exact_affine_lifts'] += 1
    rows = []
    for k in range(129):
        r = seed(k, counts)
        period = 1 << (k+3)
        M = 1 << (k+6)
        expected = (1 << (k+4))*(3 if k % 2 == 0 else 1)
        assert r % 2 == 1
        assert pow(9, period, M) == 1
        if k <= 10:
            matches = [a for a in range(period) if (3*pow(9, a, M)+5) % M == expected]
            assert matches == [r]
            counts['finite_unique_seed_censuses'] += 1
            counts['finite_seed_residues_tested'] += period
            rows.append({'k': k, 'r': r, 'period': period})
        for h in range(32):
            R = r+period*(h+1)
            assert R >= 3 and R % 2 == 1
            assert (3*pow(9, R, M)+5) % M == expected
            counts['modular_block_families'] += 1
    return {'affine_j_interval': [0, 10], 'affine_A_odd_interval': [1, 31],
            'affine_C_rule': '(-A)%8+8*c for c=0..3',
            'seed_k_interval': [0, 128], 'modular_h_interval': [0, 31],
            'small_seed_rows': rows,
            'scope': 'Small affine lifts materialize their exact quotients. Larger seed and family checks use modular exponentiation only. Seed uniqueness is exhaustively checked only for k<=10; the kernel construction needs existence, not uniqueness.'}


def factor(R):
    X = 9**R
    value = 3*X+5
    shift = (value & -value).bit_length()-1
    assert shift >= 4 and R % 2 == 1
    k, q = shift-4, value >> shift
    assert q % 2 == 1
    return X, k, q


def complete_pair(R, kind, counts):
    N = (1 << (3*R))-5
    X = 9**R
    if kind == 'block':
        _, k, q = factor(R)
        assert (3**k*q) % 4 == 3
        P = (1 << (2*R+1))-1
        b = (3**(k+1)*q-1)//4
        nword = 'OOE'*R+'EEOE'+'O'*k+'EO'
        pword = 'O'*(2*R+1)+'EOEE'+'O'*k+'EE'
        nclock, pclock = 5*R+2*k+8, 4*R+2*k+9
        assert pword.count('E') == 5 and pword.count('O') == 2*R+k+2
        assert (P+1)**3 == 8*(N+5)**2
    else:
        assert kind == 'preceding' and R % 16 == 3
        k = None
        P = (1 << (3*(R-1)))-5
        assert N == 8*P+35
        b = (3*X-11)//128
        nword = 'OOE'*R+'EEOEEEE'
        pword = 'OOE'*(R-1)+'EEOOEEO'
        nclock, pclock = 5*R+8, 5*R+5
    assert 0 < P < N
    assert nclock == len(nword)+nword.count('O')
    assert pclock == len(pword)+pword.count('O')
    x = N
    first_late = None
    first_descent = None
    for t in range(nclock+1):
        if t < 5*R:
            assert (x % 27 == 20) == (t % 5 == 2 and t//5 > 0)
            counts['growing_prefix_residue_checks'] += 1
        if t <= 5*R:
            assert x >= N
        if t == 5*R:
            assert x == X-5
        if t >= 5*R and x % 27 == 20 and first_late is None:
            first_late = t
        if x < N and first_descent is None:
            first_descent = t
        if t < nclock:
            x = 3*x+1 if x & 1 else x >> 1
    assert x == b and shortcut(N, nword, counts) == b
    if kind == 'block' and k >= 2:
        assert first_late == nclock and b % 27 == 20
        counts['complete_first_late_target_checks'] += 1
    y = P
    for _ in range(pclock):
        y = 3*y+1 if y & 1 else y >> 1
    assert y == b and shortcut(P, pword, counts) == b
    assert inverse(b, pword[::-1], counts) == P
    counts['complete_N_steps'] += nclock
    counts['complete_P_steps'] += pclock
    counts['complete_'+kind+'_pairs'] += 1
    return {'kind': kind, 'R': R, 'k': k, 'source_bits': N.bit_length(),
            'predecessor_bits': P.bit_length(), 'N_clock': nclock, 'P_clock': pclock,
            'first_post_ladder_residue20_through_meeting': first_late,
            'first_forward_descent_through_meeting': first_descent}


def complete_paths(counts):
    rows = []
    cache = {}
    def run(R, kind):
        key = R, kind
        if key not in cache:
            row = complete_pair(R, kind, counts)
            cache[key] = row
            rows.append(row)
        return cache[key]
    for R in range(3, 258, 2):
        _, k, q = factor(R)
        if (3**k*q) % 4 == 3:
            run(R, 'block')
        if R % 16 == 3:
            run(R, 'preceding')
    for R in [515, 1027, 2051]:
        run(R, 'preceding')
    lifted = []
    for k in range(11):
        r = seed(k, counts)
        R = r+(1 << (k+3))
        row = run(R, 'block')
        assert row['k'] == k
        lifted.append({'k': k, 'r': r, 'R': R})
        print('Complete lifted block replay: k=%d, R=%d' % (k, R), flush=True)
    return {'small_odd_R_interval': [3, 257], 'extra_preceding_R': [515, 1027, 2051],
            'lifted_cases': lifted, 'rows': rows,
            'scope': 'Every listed N and P is actually iterated from its start to the common meeting. Shortcut parities and every inverse guard are independently checked. For k>=2, every clock from the ladder endpoint to the meeting is checked for the exact first later residue-20 visit. Repeated cases are reused, not counted twice. No later convergence or optimal inverse cost is inferred.'}


def larger_coordinates(counts):
    rows = []
    for k in [12, 16]:
        r = seed(k, counts)
        R = r+(1 << (k+3))
        X, actual_k, q = factor(R)
        assert actual_k == k and (3**k*q) % 4 == 3
        N = (1 << (3*R))-5
        P = (1 << (2*R+1))-1
        b = (3**(k+1)*q-1)//4
        ntail, ptail = 2*k+8, 2*k+7
        path = ordinary(X-5, ntail)
        assert path == paired(X-5, ntail) and path[-1] == b
        assert all(x % 27 != 20 for x in path[:-1]) and b % 27 == 20
        Y = 3**(2*R+1)-1
        other = ordinary(Y, ptail)
        assert other == paired(Y, ptail) and other[-1] == b
        assert inverse(b, 'EE'+'O'*k+'EEOE', counts) == Y
        assert 0 < P < N and (P+1)**3 == 8*(N+5)**2
        counts['large_coordinate_cases'] += 1
        counts['large_short_tail_steps'] += ntail+ptail
        rows.append({'k': k, 'r': r, 'R': R, 'source_bits': N.bit_length(),
                     'predecessor_bits': P.bit_length(), 'short_N_tail': ntail,
                     'short_P_tail': ptail, 'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'The large integers are materialized for exact coordinates and short tails only. The full growing prefix and full pure odd Mersenne block rely on their kernel theorems and are not numerically replayed here.'}


def surviving(counts):
    rows = []
    for h in range(129):
        R = 512*h+5
        assert R % 4 == 1 and h < R
        assert (3*pow(9, R, 4096)+5) % 4096 == 1024
        counts['compatible_progression_modular_cases'] += 1
        if h < 3:
            _, k, q = factor(R)
            assert k == 6 and q % 4 == 1 and (3**k*q) % 4 == 1
            rows.append({'h': h, 'R': R, 'k': k, 'q_mod4': q % 4})
            counts['compatible_exact_factorizations'] += 1
    path = ordinary(8**5-5, 160)
    assert path == paired(8**5-5, 160) and path[-1] == 1 and 1 not in path[:-1]
    counts['compatible_convergent_witness_steps'] = 160
    return {'h_interval': [0, 128], 'exact_rows': rows,
            'convergent_member': {'R': 5, 'N': 32763, 'first_arrival': 160},
            'scope': 'This progression satisfies the new necessary arithmetic conditions. No member is asserted to be a counterexample or to resist every other method. The first member is already kernel certified to converge in the preceding ladder module and is independently replayed here.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-ladder-exit-') as directory:
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
                assert "'MinimumLadderBlockExit.finite_surviving_period' does not depend on any axioms" in result.stdout
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
    assert len(sources) == len(set(sources)) == 34
    version, builds = build(sources, args.lean, args.threads)
    counts = Counter()
    sections = {}
    for name, check in [('generic_paths', generic_paths), ('binary_lifts', lift_checks),
                        ('complete_paths', complete_paths), ('larger_coordinates', larger_coordinates),
                        ('compatible_progression', surviving)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources+[Path(__file__).name, HELPER, NOTE, PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'kernel_theorems_audited': len(THEOREMS),
        'axiom_free_roots': ['finite_surviving_period'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For R>=3, R=3 mod16, N=8^R-5 coalesces with P=8^(R-1)-5 at ordinary clocks 5R+8 and 5R+5. N=8P+35 and P is positive.',
            'For odd R>=3, 3*9^R+5=2^(k+4)*q, q>0, and 3^k*q=3 mod4, P=2^(2R+1)-1 is smaller than N and coalesces at clocks 4R+2k+9 and 5R+2k+8, with inverse counts (5,2R+k+2).',
            'For k>=2 the meeting is the first residue-20 visit at or after clock 5R; every intervening ordinary clock is excluded.',
            'Odd affine binary lifting constructs a seed for every k and arbitrarily large exponents and sources satisfying the sufficient exit condition. For every k>=2 and source bound, the first useful later residue-20 visit has delay exactly 2k+8 from the end of the growing prefix.',
            'A least source 8^R-5 with R>=3 must have R=1 mod4 and a positive factorization with k>0, q odd, and 3^k*q=1 mod4.',
            'The unbounded progression R=512h+5 satisfies those necessary conditions with k=6 and q=1 mod4. This is arithmetic compatibility, not existence of a counterexample.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and its standard libraries; no installation or credential access in this continuation.',
        'finite_scope_limit': 'Complete positive paths, larger short-tail coordinates, and modular-only exponents have separate ranges. Finite seed uniqueness does not replace the parameterized kernel existence construction. No universal convergence follows from these tests.',
        'not_proved': [
            'Convergence of every covered source or coalescing predecessor.',
            'A useful first later target for all exponents, every previous whole-window obstruction progression, or an arbitrary least-counterexample orbit.',
            'Failure of every other descent or coalescence method on the compatible progression.',
            'Optimal inverse costs, earliest coalescence by any method, cap/residual bounds, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()

