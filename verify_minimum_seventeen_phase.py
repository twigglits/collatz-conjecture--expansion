"""Verify exact binary-phase obstructions for primary and secondary exits.

Kernel theorems, full weighted prefixes, delayed mergers, modular pure lifts,
and larger tail-only examples have separately recorded verification scopes.
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

from verify_minimum_inverse_locality import digest, save
from verify_minimum_ladder_block_exit import inverse, shortcut
from verify_minimum_seventeen_transition import BRIDGES, CYCLE
from verify_minimum_seventeen_separation import (
    separated_windows, paired_stream, affine_seed, weight as primary_weight,
)
from verify_minimum_seventeen_fourth import (
    FOURTH_BRIDGE, SECOND_BRIDGE, endpoint, full_meeting, weight as merger_weight,
)

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-seventeen-phase'
PRIOR = 'results/minimum-seventeen-fourth/verification.json'
SOURCE = 'lean/MinimumSeventeenPhase.lean'
NOTE = 'docs/MINIMUM-SEVENTEEN-PHASE.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py', 'verify_minimum_seventeen_separation.py',
           'verify_minimum_seventeen_fourth.py']
THEOREMS = [
    'binary_exponent_unique', 'exact_phase_step', 'phase_track', 'phase_separation',
    'finite_phase_sets', 'exact_binary_from_divisibility', 'fourth_scalar_separation',
    'four_scalar_separation', 'four_source_separation', 'pure_four_separation',
    'weighted_four_separation', 'no_uniform_four_scalar_clock', 'secondary_scalar_separation',
    'secondary_source_separation', 'odd_binary_inverse', 'pure_delayed_merger',
    'weighted_delayed_merger', 'pure_secondary_unit_lift', 'pure_secondary_separation',
    'weighted_secondary_separation', 'no_uniform_secondary_exit_clock',
    'finite_secondary_convergent_witness',
]


def valuation(n):
    assert n > 0
    return (n & -n).bit_length()-1


def phase_orbit(M, L, c):
    states, seen, h = [], set(), 0
    while (c, h) not in seen:
        seen.add((c, h))
        states.append((c, h))
        if c & 1:
            c = 3*c-M
        else:
            c //= 2
            h = (h+1) % L
    return states, states.index((c, h))


MAIN, _ = phase_orbit(9, 11, 225)
FOURTH, _ = phase_orbit(9, 11, 201)
EXIT_MAIN, _ = phase_orbit(1, 3, 13)
EXIT_PARTNER, _ = phase_orbit(1, 3, 14)


def phase_pair(M, L, bits, n, p, c, d, A, D, H, counts, kind):
    allowed = [phase_orbit(M, L, c)[0], phase_orbit(M, L, d)[0]]
    initial = [valuation(M*n+c), valuation(M*p+d)]
    K = initial[0]-A
    assert initial[1] == K+D and K >= H+bits
    signatures, values = [], []
    for start, shadow, e0, states in zip([n, p], [c, d], initial, allowed):
        x, h, e, u = start, 0, e0, (M*start+shadow) >> e0
        assert u % 2 == 1
        other = paired_stream(start)
        sig, exact_values = set(), set()
        for t in range(H+1):
            assert x == next(other) and x > 0
            assert M <= shadow < 1 << bits and (shadow, h % L) in states
            z = M*x+shadow
            assert z == (u << e) and u % 2 == 1
            assert valuation(z) == e == e0-h and e >= bits
            assert (-M*x) % (1 << bits) == shadow
            sig.add((shadow, e % L))
            if H <= 128:
                exact_values.add(x)
            counts[kind+'_phase_states'] += 1
            if t != H:
                assert x % 2 == shadow % 2
                if x & 1:
                    x, shadow, u = 3*x+1, 3*shadow-M, 3*u
                else:
                    x, shadow, h, e = x//2, shadow//2, h+1, e-1
        signatures.append(sig)
        values.append(exact_values)
    assert signatures[0].isdisjoint(signatures[1])
    if H <= 128:
        assert values[0].isdisjoint(values[1])
        counts[kind+'_actual_value_pairs'] += 1
    counts[kind+'_phase_pairs'] += 1
    counts[kind+'_phase_steps'] += 2*H


def four_windows(a, H, counts):
    assert (9*a+1) % (1 << (H+13)) == 0
    separated_windows(a, H, counts)
    phase_pair(9, 11, 13, 72*a-17, 48*a-17, 225, 201, 3, 4, H, counts, 'primary')


def secondary_window(b, H, counts):
    assert b >= 6 and (b-1) % (1 << (H+6)) == 0
    phase_pair(1, 3, 6, 4*b-17, 3*b-17, 13, 14, 2, 0, H, counts, 'secondary')


def inverse_lift(k, c):
    e, q = 1, (c-1)//2
    assert c % 2 == 1
    for bit in range(1, k+1):
        if q % 2:
            e += 1 << bit
            q = (q+c)//2
        else:
            q //= 2
        assert c*e == 1+(q << (bit+1))
    assert 0 < e < 1 << (k+1) and e % 2 == 1
    assert e == pow(c, -1, 1 << (k+1))
    return e


def generic_checks(counts):
    groups = [(9, 11, 13, MAIN, FOURTH, 3, 4),
              (1, 3, 6, EXIT_MAIN, EXIT_PARTNER, 2, 0)]
    for M, L, B, left, right, A, D in groups:
        for states in [left, right]:
            for c, h in states:
                nxt = (3*c-M, h) if c & 1 else (c//2, (h+1) % L)
                assert M <= c < 1 << B and nxt in states
                counts['finite_phase_states'] += 1
        assert {c for c, _ in left} & {c for c, _ in right}
        assert all((h+D) % L != (k+A) % L
                   for c, h in left for d, k in right if c == d)
    for H in list(range(65))+[128, 512, 4096]:
        for offset in [0, 1, 2, 17]:
            modulus = 1 << (H+13)
            a = -pow(9, -1, modulus) % modulus + offset*modulus
            four_windows(a, H, counts)
            b = 1+(2*offset+1)*(1 << (H+6))
            secondary_window(b, H, counts)
            counts['generic_primary_secondary_pairs'] += 1
    for k in list(range(129))+[512, 1024]:
        for c in list(range(1, 66, 2))+[3**128, 3**1024]:
            inverse_lift(k, c)
            counts['odd_inverse_checks'] += 1
    return {'primary_phase_tables': [MAIN, FOURTH], 'secondary_phase_tables': [EXIT_MAIN, EXIT_PARTNER],
            'cycle_start_indices': [0, 13, 5, 0], 'cycle_halving_periods': [11, 11, 3, 3],
            'generic_H_interval': [0, 64], 'additional_H': [128, 512, 4096],
            'offsets': [0, 1, 2, 17], 'inverse_k_interval': [0, 128],
            'additional_inverse_k': [512, 1024],
            'scope': 'Finite phase closure and nonresonance checks, actual scalar windows, and binary inverses independently supplement universal kernel proofs.'}


def unit_weight(R, r, j, H, offset=0):
    m, K, L = 57+11*r, 9+11*j, H+6
    D, E, V = 1 << m, 1 << K, 1 << L
    M = D*E*V
    A = pow(3, 35+7*r, M)
    eps = pow(pow(3, 6+7*j, V), -1, V)
    w = (D*E*eps-7*A-D)*pow(A*pow(9, R, M), -1, M) % M + offset*M
    assert w > 0 and w % 2 == 1
    return w


def coordinates(R, r, w):
    assert R >= 14 and r >= 5 and w > 0
    X = 9**R*w
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0
    a = 3**(33+7*r)*u
    starts = [4*(1 << (3*R))*w-5, (1 << (2*R+5))*w-1,
              (1 << (2*R+15))*w-1, (1 << (2*R+13))*w-1]
    assert 0 < starts[1] < starts[3] < starts[2] < starts[0]
    ends = [72*a-17, 81*a-17, 64*a-17, 48*a-17]
    clocks = [5*R+91+18*r, 4*R+99+18*r, 4*R+99+18*r, 4*R+100+18*r]
    words = ['OOE'*R+BRIDGES[0]+CYCLE*(r+4),
             'O'*(2*R+5)+BRIDGES[1]+CYCLE*(r+3),
             'O'*(2*R+15)+BRIDGES[2]+CYCLE*r,
             'O'*(2*R+13)+FOURTH_BRIDGE+CYCLE*(r-5)]
    return starts, ends, clocks, words, a, X


def full_case(R, r, H, w, counts, j=None):
    starts, ends, clocks, words, a, _ = coordinates(R, r, w)
    primary_ends, primary_clocks = ends[:], clocks[:]
    b = None
    if j is not None:
        q, rem = divmod(9*a+1, 1 << (9+11*j))
        assert rem == 0 and q > 0 and q % 2 == 1
        b = 3**(6+7*j)*q
        assert (b-1) % (1 << (H+6)) == 0
        ends[0], ends[3] = 4*b-17, 3*b-17
        clocks[0] += 16+18*j
        clocks[3] += 21+18*j
        words[0] += SECOND_BRIDGE+CYCLE*j
        words[3] += 'O'+BRIDGES[0]+CYCLE*j
    for i, (n, end, clock, word) in enumerate(zip(starts, ends, clocks, words)):
        checkpoints = {primary_clocks[i]: primary_ends[i]}
        assert len(word)+word.count('O') == clock
        assert endpoint(n, clock, counts, 'full_source_steps', checkpoints) == end
        assert shortcut(n, word, counts) == end
        assert inverse(end, word[::-1], counts) == n
    if j is None:
        four_windows(a, H, counts)
        counts['complete_primary_cases'] += 1
    else:
        secondary_window(b, H, counts)
        if j > 0:
            four_windows(a, 11*j-4, counts)
            counts['secondary_cases_with_primary_separation'] += 1
        counts['complete_secondary_cases'] += 1
    return {'R': R, 'r': r, 'j': j, 'H': H, 'weight_bits': w.bit_length(),
            'N_bits': starts[0].bit_length(), 'S_bits': starts[3].bit_length(),
            'a_bits': a.bit_length(), 'b_bits': b.bit_length() if b is not None else None,
            'N_clock': clocks[0], 'S_clock': clocks[3],
            'primary_horizon': H if j is None else (11*j-4 if j else None)}


def complete_paths(counts):
    primary, secondary = set(), set()
    for R in range(14, 22):
        for r in range(5, 11):
            for H in [0, 1, 2, 4, 8, 16, 32, 64, 128]:
                primary.add((R, r, H))
    for R in [128, 1024, 16384]:
        for r in [5, 9]:
            for H in [32, 256]:
                primary.add((R, r, H))
    for r in [128, 512, 4096]:
        for H in [32, 256]:
            primary.add((14, r, H))
    for H in [512, 1024, 4096, 16384]:
        for r in [5, 9]:
            primary.add((14, r, H))
    for R in range(14, 19):
        for r in range(5, 9):
            for j in range(5):
                for H in [0, 1, 4, 16, 64]:
                    secondary.add((R, r, j, H))
    for j in [128, 512, 4096]:
        secondary.add((14, 5, j, 32))
    for H in [128, 512, 4096, 16384]:
        secondary.add((14, 5, 1, H))
    for R in [128, 1024, 16384]:
        secondary.add((R, 5, 1, 32))
    for r in [128, 512, 4096]:
        secondary.add((14, r, 1, 32))
    rows, maxima = [], Counter()
    for R, r, H in sorted(primary):
        row = full_case(R, r, H, primary_weight(R, r, H+1), counts)
        rows.append(row)
    for R, r, j, H in sorted(secondary):
        row = full_case(R, r, H, unit_weight(R, r, j, H), counts, j)
        rows.append(row)
    for row in rows:
        for key, value in row.items():
            if value is not None:
                maxima[key] = max(maxima[key], value)
    return {'primary_cases': len(primary), 'secondary_cases': len(secondary),
            'maxima': dict(maxima),
            'large_rows': [r for r in rows if r['R'] >= 16384 or r['r'] >= 512
                           or r['H'] >= 512 or (r['j'] or 0) >= 512],
            'scope': 'All four full source paths are replayed by ordinary, shortcut and inverse operations. Secondary cases continue N,S to their secondary endpoints and verify q odd. Both types check all pairs of window times by disjoint exact phase signatures. Small windows also compare actual value sets.'}


def delayed_checks(counts):
    rows = []
    for R, r, j in [(14, 5, 1), (14, 5, 128), (14, 512, 16), (16384, 5, 16)]:
        w = merger_weight(R, r, j)
        row = full_meeting(R, r, j, w, counts)
        _, _, _, _, a, _ = coordinates(R, r, w)
        H = 11*j-4
        four_windows(a, H, counts)
        assert 26+18*j > H
        row['all_four_primary_horizon'] = H
        rows.append(row)
        counts['delayed_merger_cases'] += 1
    return {'rows': rows,
            'scope': 'Full N,S meetings and old-partner prefixes are independently replayed, while all three partners have primary exit windows disjoint from the main window. These examples refute an interpretation of window separation as eventual noncoalescence.'}


def modular_checks(counts):
    params = [(r, j, H) for r in range(5, 9) for j in range(5) for H in [0, 1, 8, 32, 128]]
    params += [(128, 128, 128), (512, 1, 0), (5, 512, 4096)]
    rows = []
    for r, j, H in params:
        m, K, L = 57+11*r, 9+11*j, H+6
        D, E, V = 1 << m, 1 << K, 1 << L
        M = D*E*V
        A = pow(3, 35+7*r, M)
        eps = pow(pow(3, 6+7*j, V), -1, V)
        F = 7*A+D+(V-eps)*D*E
        precision = m+K+H+3
        seed = affine_seed(precision, A, F)
        for B in [0, 1 << (r+j+H+32)]:
            R = seed+(1 << precision)*(B+14)
            assert R > B and R >= 14
            X = pow(9, R, M)
            assert (A*(X+7)+D) % M == D*E*eps
            u_mod, rem = divmod(X+7, D)
            assert rem == 0
            a_mod = pow(3, 33+7*r, E*V)*u_mod % (E*V)
            q_mod, rem = divmod(9*a_mod+1, E)
            assert rem == 0 and q_mod % V == eps and q_mod % 2 == 1
            assert pow(3, 6+7*j, V)*q_mod % V == 1
            counts['modular_secondary_pure_lifts'] += 1
            if r >= 128 or j >= 128 or H >= 4096:
                rows.append({'r': r, 'j': j, 'H': H, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'regular_r_interval': [5, 8], 'regular_j_interval': [0, 4],
            'regular_H': [0, 1, 8, 32, 128],
            'additional_coordinates': [[128, 128, 128], [512, 1, 0], [5, 512, 4096]],
            'large_rows': rows,
            'scope': 'Pure exponent coordinates and normalized secondary units are checked using modular powers. Enormous pure sources and complete trajectories are not materialized.'}


def witness_checks(counts):
    R, r, j, H = 14, 5, 1, 128
    w = unit_weight(R, r, j, H)
    starts, _, _, _, a, X = coordinates(R, r, w)
    u = (X+7) // (1 << (57+11*r))
    q = (9*a+1) // (1 << (9+11*j))
    source = (ROOT/SOURCE).read_text()
    for name, value in [('phaseWitnessWeight', w), ('phaseWitnessUnit', u), ('phaseWitnessExit', q)]:
        assert f'def {name} : Nat := {value}' in source
    arrivals = [2683, 3675, 2682, 2680]
    for n, t in zip(starts, arrivals):
        other = paired_stream(n)
        for s in range(t+1):
            assert n == next(other)
            assert (n == 1) == (s == t)
            if s != t:
                n = 3*n+1 if n % 2 else n//2
        counts['convergent_witness_steps'] += t
    four_windows(a, 7, counts)
    secondary_window(3**(6+7*j)*q, H, counts)
    return {'R': R, 'r': r, 'j': j, 'H': H, 'weight': str(w), 'unit': str(u), 'q': str(q),
            'source_bits': [n.bit_length() for n in starts], 'first_arrival_clocks': arrivals,
            'scope': 'The kernel certifies positive coordinates, odd exit, secondary separation condition and all four arrivals at one. Python also checks first-arrival minimality and both separated windows.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        r = 5
        for j, H in [(1, 32), (16, 128)]:
            w = unit_weight(R, r, j, H)
            starts, ends, _, _, a, X = coordinates(R, r, w)
            q, rem = divmod(9*a+1, 1 << (9+11*j))
            assert rem == 0 and q % 2 == 1
            b = 3**(6+7*j)*q
            for n, t, expected in zip([4*X-5, 243*X-1, 14348907*X-1, 1594323*X-1],
                                      [91+18*r, 89+18*r, 69+18*r, 164+18*(r-5)], ends):
                assert endpoint(n, t, counts, 'larger_transition_steps') == expected
            assert endpoint(ends[0], 16+18*j, counts, 'larger_secondary_steps') == 4*b-17
            assert endpoint(ends[3], 21+18*j, counts, 'larger_secondary_steps') == 3*b-17
            four_windows(a, 11*j-4, counts)
            secondary_window(b, H, counts)
            rows.append({'R': R, 'r': r, 'j': j, 'H': H, 'N_bits': starts[0].bit_length(),
                         'S_bits': starts[3].bit_length(), 'full_growing_prefixes_replayed': False})
    return {'rows': rows,
            'scope': 'Exact weighted coordinates, four transition tails, two secondary tails and both separated windows are checked. Full growing prefixes are not iterated.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumSeventeenPhase.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 42
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-seventeen-phase-') as directory:
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
                        ('delayed_checks', delayed_checks), ('modular_checks', modular_checks),
                        ('witness_checks', witness_checks), ('larger_coordinates', larger_coordinates)]:
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
            'Exact binary exponents and finite halving-phase tables separate paths whose reference cycles can overlap. The generic proof uses an odd scale and all pairs of clocks in a finite window.',
            'For a>0 and 2^(H+13) dividing 9a+1, all three scalar partners 81a-17,64a-17,48a-17 have windows disjoint from 72a-17 through every pair of ordinary clocks at most H.',
            'For every r>=5,H and exponent bound there are pure transition exponents with all four primary windows separated. Weights beyond every bound exist at every fixed R>=14,r>=5.',
            'For b>=6 and 2^(H+6) dividing b-1, the windows from 3b-17 and 4b-17 are separated through every pair of clocks at most H.',
            'For every fixed r>=5,j,H and exponent bound, pure sources realize the secondary separation with q positive odd in 9a+1=2^(9+11j)*q. Weights beyond every bound exist at fixed R>=14. Thus the secondary delay is not an unremoved power of two in q.',
            'Arbitrarily large pure exponents and fixed-prefix weights also realize the earlier successful secondary unit23 merger together with arbitrarily long four-source primary separation.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication precedes dependency reuse. Objects are copied into an isolated import directory; mismatches are rebuilt and nested prior provenance is retained. The new module is always freshly built.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation or credential access.',
        'finite_scope_limit': 'Full weighted prefixes, delayed full meetings, exact phase signatures, modular-only pure exponents and larger tail-only cases are distinct. Primary checks replay the main window twice, in the old three-source check and in the new two-source phase check; their state counts are not a count of distinct visits. No quadratic enumeration of all time pairs is claimed.',
        'not_proved': [
            'Separation for all time, failure of eventual coalescence or a divergent orbit.',
            'A merger for every normalized secondary unit or every transition source.',
            'A uniform source-size bound on meeting clocks or a successful unrestricted variable-clock cover.',
            'Convergence of all family members, exclusion of arbitrary least counterexamples, nontrivial cycles, divergence or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()


