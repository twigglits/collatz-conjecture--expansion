"""Audit coalescing Mersenne sources after growing return-ladder prefixes.

Kernel proofs, complete positive paths, algebraic short-tail checks, and
modular-only family checks have separate recorded scopes.
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
OUT = ROOT/'results/minimum-ladder-exit'
PRIOR = 'results/minimum-ladder-window/verification.json'
SOURCE = 'lean/MinimumLadderExit.lean'
NOTE = 'docs/MINIMUM-LADDER-EXIT.md'
HELPER = 'verify_minimum_inverse_locality.py'
THEOREMS = [
    "source_identity",
    "endpoint_clock",
    "mersenne_clock",
    "plus_smaller",
    "minus_smaller",
    "cubic_gain_plus",
    "cubic_gain_minus",
    "exit_seven_profile",
    "exit_eleven_profile",
    "exit_one_profile",
    "finite_exit_periods",
    "residue_seven",
    "residue_eleven",
    "residue_one",
    "seven_escape",
    "eleven_escape",
    "one_escape",
    "residue_not_least",
    "window_seven",
    "window_exit",
    "unbounded_delayed_escape"
]


def inverse_word(b, word, counts):
    p = b
    for letter in word:
        if letter == 'E':
            p *= 2
        else:
            assert p % 3 == 2
            p = (2*p-1)//3
        assert p > 0
        counts['inverse_edges'] += 1
    return p


def shortcuts(n, word, counts):
    ordinary_clock = 0
    for letter in word:
        assert ('O' if n & 1 else 'E') == letter
        n = (3*n+1)//2 if n & 1 else n//2
        ordinary_clock += 2 if letter == 'O' else 1
        counts['shortcut_edges'] += 1
    return n, ordinary_clock


def generic_profiles(counts):
    profiles = [
        (64, 52, 8, 9, 8, 192, 170, 'EEEEOE', 'EEOEEO'),
        (384, 148, 9, 27, 11, 128, 50, 'EEOOEOE', 'EEOEEEO'),
        (128, 4, 10, 27, 2, 384, 26, 'EEOEEOE', 'EEOEOEO'),
    ]
    for u in list(range(1024)) + [2**32+1, 3**64+7, 2**512+19]:
        for A, B, t, D, F, G, H, w, forward in profiles:
            x, b, y = A*u+B, D*u+F, G*u+H
            path = ordinary(x, t)
            assert path == paired(x, t) and path[-1] == b
            assert inverse_word(b, w, counts) == y
            backward_clock = w.count('E')+2*w.count('O')
            other = ordinary(y, backward_clock)
            assert other == paired(y, backward_clock) and other[-1] == b
            assert shortcuts(x, forward, counts) == (b, t)
            assert shortcuts(y, w[::-1], counts) == (b, backward_clock)
            assert b % 27 != 20
            counts['generic_profile_queries'] += 1
            counts['generic_ordinary_steps'] += t+backward_clock
    return {'small_u_interval': [0, 1023],
            'larger_u': ['2**32+1', '3**64+7', '2**512+19'],
            'scope': 'All three affine path pairs, both shortcut words, and every inverse guard are replayed. These are finite checks of separate universal kernel profiles.'}


def periods(counts):
    assert pow(9, 8, 64) == 1 and pow(9, 7, 64) == 57
    assert pow(3, 32, 128) == 1 and pow(3, 21, 128) == 51
    assert pow(9, 16, 128) == 1
    for R in range(4096):
        if R % 8 == 7:
            assert pow(9, R, 64) == 57
        if R % 16 == 11:
            assert pow(3, 2*R-1, 128) == 51
        if R % 16 == 1:
            assert pow(9, R, 128) == 9
        counts['residue_exponents'] += 1
    # The R>=3 size condition must not be silently dropped.
    assert 2**(2*1+1)-1 > 8**1-5
    return {'R_interval': [0, 4095], 'excluded_small_case': {'R': 1, 'P': 7, 'N': 3},
            'scope': 'The finite period certificate and the three modular consequences are checked independently. R=1 meets a residue condition but fails the smaller-source inequality.'}


def coordinates(R):
    assert R >= 3
    X = 9**R
    N = (1 << (3*R))-5
    if R % 8 == 7:
        j, tail, w, b = 2*R+1, 8, 'EEEEOE', (9*X-1)//64
        assert (9*X-1) % 64 == 0 and b % 9 == 8
    elif R % 16 == 11:
        j, tail, w, b = 2*R-1, 9, 'EEOOEOE', (9*X+31)//128
        assert (9*X+31) % 128 == 0 and b % 27 == 11
    else:
        assert R % 16 == 1
        j, tail, w, b = 2*R+1, 10, 'EEOEEOE', (27*X+13)//128
        assert (27*X+13) % 128 == 0 and b % 27 == 2
    P = (1 << j)-1
    assert 0 < P < N and b % 27 != 20
    if j == 2*R+1:
        assert (P+1)**3 == 8*(N+5)**2
    else:
        assert 8*(P+1)**3 == (N+5)**2
    return N, P, X, j, tail, w, b


def complete_case(R, counts):
    N, P, X, j, tail, w, b = coordinates(R)
    x = N
    minimum = N
    first_descent = None
    for t in range(5*R+tail):
        if t < 5*R:
            assert (x % 27 == 20) == (t % 5 == 2 and t//5 > 0)
            counts['ladder_residue_checks'] += 1
        if t == 5*R:
            assert x == X-5
        x = 3*x+1 if x & 1 else x >> 1
        minimum = min(minimum, x)
        if x < N and first_descent is None:
            first_descent = t+1
        if t+1 <= 5*R:
            assert x >= N
        counts['complete_N_ordinary_steps'] += 1
    assert x == b
    full_word = w+'O'*j
    assert inverse_word(b, full_word, counts) == P
    expected_clock = full_word.count('E')+2*full_word.count('O')
    y = P
    for _ in range(expected_clock):
        y = 3*y+1 if y & 1 else y >> 1
        counts['complete_P_ordinary_steps'] += 1
    assert y == b
    assert shortcuts(P, full_word[::-1], counts) == (b, expected_clock)
    # Replay the ladder in a separate shortcut block implementation.
    y = N
    for _ in range(R):
        y, t = shortcuts(y, 'OOE', counts)
        assert t == 5
    assert y == X-5
    assert ordinary(y, tail) == paired(y, tail)
    assert ordinary(y, tail)[-1] == b
    counts['complete_coalescing_pairs'] += 1
    return {'R': R, 'source_bits': N.bit_length(), 'predecessor_bits': P.bit_length(),
            'N_clock': 5*R+tail, 'P_clock': expected_clock,
            'inverse_even': full_word.count('E'), 'inverse_odd': full_word.count('O'),
            'first_forward_descent_through_meeting': first_descent,
            'minimum_through_meeting_is_N': minimum == N}


def complete_paths(counts):
    Rs = [R for R in range(3, 258, 2)
          if R % 8 == 7 or R % 16 in (1, 11)]
    Rs += [511, 513, 523, 1023, 2047, 4095]
    rows = [complete_case(R, counts) for R in Rs]
    assert next(row for row in rows if row['R'] == 17)['minimum_through_meeting_is_N']
    family_rows = []
    for s, a in [(0, 0), (0, 1)]:
        K = 2*(s+3)
        h = 4*a+2
        R = 1+2*3**K*(h+1)
        row = complete_case(R, counts)
        row.update({'s': s, 'a': a, 'h': h, 'K': K})
        assert R % 8 == 7
        assert ((1 << (3*R))-8) % 3**K == 0
        family_rows.append(row)
        print('Complete obstructed-window exit replay:', R, flush=True)
    return {'covered_odd_R_interval': [3, 257], 'larger_R': [511, 513, 523, 1023, 2047, 4095],
            'rows': rows, 'whole_window_rows': family_rows,
            'scope': 'Each listed N is actually iterated from its start through its full growing prefix and short tail. Each P is independently iterated to the same meeting, and every inverse guard and shortcut parity is replayed. Prefix minima and residue-20 positions are checked. No later convergence or optimal inverse minimum is claimed.'}


def larger_coordinates(counts):
    rows = []
    for s, a in [(1, 0), (2, 0)]:
        K = 2*(s+3)
        R = 1+2*3**K*(4*a+3)
        N, P, X, j, tail, w, b = coordinates(R)
        assert (N-3) % 3**K == 0
        assert inverse_word(b, w, counts) == 3**j-1
        assert ordinary(X-5, tail) == paired(X-5, tail)
        assert ordinary(X-5, tail)[-1] == b
        assert ordinary(3**j-1, w.count('E')+2*w.count('O'))[-1] == b
        counts['large_short_ordinary_steps'] += tail+w.count('E')+2*w.count('O')
        counts['large_coordinate_cases'] += 1
        rows.append({'s': s, 'a': a, 'K': K, 'R': R,
                     'source_bits': N.bit_length(), 'predecessor_bits': P.bit_length(),
                     'N_clock_formula': 5*R+tail, 'P_clock_formula': 2*j+w.count('E')+2*w.count('O'),
                     'full_paths_replayed': False})
    return {'rows': rows,
            'scope': 'These integers are materialized, but only algebraic coordinates, the cubic size identities, and the short tails are independently replayed. The full ladder and pure odd blocks rely on the separate parameterized kernel theorems.'}


def modular_families(counts):
    for s in range(129):
        K = 2*(s+3)
        M = 3**K
        assert M % 4 == 1
        for a in range(32):
            R = 1+2*M*(4*a+3)
            assert R % 8 == 7 and R >= 3
            assert pow(8, R, M) == 8
            assert pow(9, R, 64) == 57
            counts['modular_delayed_escape_cases'] += 1
    return {'s_interval': [0, 128], 'a_interval': [0, 31],
            'scope': 'Only exponents and congruences are computed in this section. No huge source is constructed here; the two complete and two coordinate-only family examples are identified separately.'}


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
                assert "'MinimumLadderExit.finite_exit_periods' does not depend on any axioms" in result.stdout
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
    assert len(sources) == len(set(sources)) == 33
    version, builds = build(sources, args.lean, args.threads)
    counts = Counter()
    sections = {}
    for name, check in [('generic_profiles', generic_profiles), ('periods', periods),
                        ('complete_paths', complete_paths), ('larger_coordinates', larger_coordinates),
                        ('modular_families', modular_families)]:
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
        'axiom_free_roots': ['finite_exit_periods'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'The growing prefix ends at 9^R-5 at ordinary clock 5R.',
            'For R>=3 and R=7 mod8, P=2^(2R+1)-1 is positive and smaller than N=8^R-5, with ordinary coalescence at clocks 4R+9 and 5R+8 and inverse counts (5,2R+2).',
            'For R>=3 and R=11 mod16, P=2^(2R-1)-1 has ordinary coalescence at clocks 4R+8 and 5R+9 and inverse counts (4,2R+2).',
            'For R>=3 and R=1 mod16, P=2^(2R+1)-1 has ordinary coalescence at clocks 4R+11 and 5R+10 and inverse counts (5,2R+3).',
            'The corresponding powers satisfy exact cubic size identities. Every covered N is excluded as a least positive counterexample.',
            'For K=2*(s+3), R=1+2*3^K*(4a+3), every target b_i, i<R, has inverse minimum N at even budget i+s, but the first late-escape path applies after the prefix.',
            'For every extra budget, visit-count bound and source bound, one source exceeds both bounds and has both the entire prefix obstruction and a smaller coalescing source eight ordinary steps after the prefix.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and its standard libraries; no installation or credential access in this continuation.',
        'finite_scope_limit': 'Complete ordinary paths, coordinate-only short-tail replay, and modular-only families have separate explicit ranges. The universal paths and exclusions are kernel proofs, not inferred from finite experiments.',
        'not_proved': [
            'Convergence of every covered N or every coalescing Mersenne P.',
            'A late escape for all odd R, every h in the whole-window family, or an arbitrary positive source.',
            'Optimal inverse cost, a useful residue-20 meeting for every possible least counterexample, or cap/residual bounds.',
            'Exclusion of all nontrivial cycles or divergence, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()

