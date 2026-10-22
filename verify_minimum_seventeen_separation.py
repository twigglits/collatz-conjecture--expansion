"""Audit separation of the three transition sources on every fixed exit window.

This verifies bounded-window nonmeetings, not eventual noncoalescence. One
explicit triple is separately kernel-certified to converge.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-seventeen-separation'
PRIOR = 'results/minimum-seventeen-transition/verification.json'
SOURCE = 'lean/MinimumSeventeenSeparation.lean'
NOTE = 'docs/MINIMUM-SEVENTEEN-SEPARATION.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py']
THEOREMS = ["finite_shadow_sets","shadow_step","shadow_track","shadow_separation","scalar_separation","odd_power_cancel","unbounded_affine_lift","pure_shadow_lift","unbounded_pure_separation","shadow_exit_residue","weighted_shadow_lift","weighted_window_separation","no_uniform_scalar_clock","finite_convergent_witness"]
STARTS = [225, 234, 217]
MODULUS = 4096


def shadow_step(c):
    return 3*c-9 if c % 2 else c//2


def shadow_set(c):
    values = []
    while c not in values:
        values.append(c)
        c = shadow_step(c)
    return values, values.index(c)


SHADOWS = [shadow_set(c)[0] for c in STARTS]


def paired_stream(n):
    yield n
    while True:
        if n % 2:
            n = 3*n+1
            yield n
            n //= 2
            yield n
        else:
            n //= 2
            yield n


def endpoint(n, steps, counts, key):
    for _ in range(steps):
        n = 3*n+1 if n % 2 else n//2
        assert n > 0
    counts[key] += steps
    return n


def separated_windows(a, H, counts):
    assert a > 0 and (9*a+1) % (1 << (H+12)) == 0
    assert a % 64 == 7
    residues, actual_sets = [], []
    for factor, c0, allowed in zip([72, 81, 64], STARTS, SHADOWS):
        n, c = factor*a-17, c0
        other = paired_stream(n)
        rs, values = set(), set()
        for t in range(H+1):
            assert n == next(other) and n > 0
            assert c in allowed and 9 <= c < MODULUS
            assert ((9*n+c) & ((1 << (H+12-t))-1)) == 0
            residue = 9*n % MODULUS
            assert residue == (-c) % MODULUS
            rs.add(residue)
            if H <= 128:
                values.add(n)
            counts['window_states_replayed'] += 1
            if t != H:
                n = 3*n+1 if n % 2 else n//2
                c = shadow_step(c)
        residues.append(rs)
        actual_sets.append(values)
    assert residues[0].isdisjoint(residues[1])
    assert residues[0].isdisjoint(residues[2])
    if H <= 128:
        assert actual_sets[0].isdisjoint(actual_sets[1])
        assert actual_sets[0].isdisjoint(actual_sets[2])
        counts['windows_with_actual_value_sets'] += 1
    counts['separated_triples'] += 1
    counts['window_ordinary_steps'] += 3*H


def generic_checks(counts):
    assert [len(s) for s in SHADOWS] == [18, 11, 21]
    assert [shadow_set(c)[1] for c in STARTS] == [0, 6, 19]
    for S in SHADOWS:
        assert all(9 <= c < MODULUS and shadow_step(c) in S for c in S)
    assert set(SHADOWS[0]).isdisjoint(SHADOWS[1])
    assert set(SHADOWS[0]).isdisjoint(SHADOWS[2])
    counts['finite_shadow_states'] = sum(map(len, SHADOWS))
    for H in range(65):
        D = 1 << (H+12)
        a0 = -pow(9, -1, D) % D
        for offset in [0, 1, 2, 17]:
            separated_windows(a0+D*offset, H, counts)
            counts['generic_scalar_triples'] += 1
    return {'shadows': SHADOWS, 'cycle_start_indices': [0, 6, 19],
            'H_interval': [0, 64], 'lift_offsets': [0, 1, 2, 17],
            'scope': 'Finite closure and disjointness tables, plus positive scalar windows. All cross-time nonmeetings in a window follow from disjoint residue sets; small windows also compare sets of the exact integer states.'}


def weight(R, r, H, offset=0):
    m = 57+11*r
    M = 1 << (m+H+12)
    A = pow(3, 35+7*r, M)
    w = (-7*A-(1 << m))*pow(A*pow(9, R, M), -1, M) % M
    w += offset*M
    assert w > 0
    return w


def coordinates(R, r, H, w):
    X = 9**R*w
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0
    a = 3**(33+7*r)*u
    assert (9*a+1) % (1 << (H+12)) == 0 and a % 64 == 7 and u % 2 == 1
    starts = [4*(1 << (3*R))*w-5, (1 << (2*R+5))*w-1, (1 << (2*R+15))*w-1]
    assert 0 < starts[1] < starts[0] and 0 < starts[2] < starts[0]
    ends = [72*a-17, 81*a-17, 64*a-17]
    clocks = [5*R+91+18*r, 4*R+99+18*r, 4*R+99+18*r]
    words = ['OOE'*R+BRIDGES[0]+CYCLE*(r+4),
             'O'*(2*R+5)+BRIDGES[1]+CYCLE*(r+3),
             'O'*(2*R+15)+BRIDGES[2]+CYCLE*r]
    return starts, ends, clocks, words, a, u, X


def complete_case(R, r, H, w, counts):
    starts, ends, clocks, words, a, _, _ = coordinates(R, r, H, w)
    for n, end, t, word in zip(starts, ends, clocks, words):
        assert len(word)+word.count('O') == t
        assert endpoint(n, t, counts, 'complete_prefix_ordinary_steps') == end
        assert shortcut(n, word, counts) == end
        assert inverse(end, word[::-1], counts) == n
        counts['complete_source_prefixes'] += 1
    separated_windows(a, H, counts)
    counts['complete_weighted_triples'] += 1
    return {'R': R, 'r': r, 'H': H, 'weight_bits': w.bit_length(),
            'N_bits': starts[0].bit_length(), 'P_bits': starts[1].bit_length(),
            'Q_bits': starts[2].bit_length(), 'scalar_bits': a.bit_length()}


def complete_paths(counts):
    cases = set()
    for R in range(14, 21):
        for r in range(9):
            for H in [0, 1, 2, 3, 4, 8, 16, 32, 64]:
                cases.add((R, r, H, weight(R, r, H)))
    for R in [128, 1024, 16384]:
        for r in [0, 7]:
            for H in [16, 64]:
                cases.add((R, r, H, weight(R, r, H, 1)))
    for r in [0, 16, 64]:
        for H in [128, 512, 1024, 4096, 16384]:
            cases.add((14, r, H, weight(14, r, H)))
    for r in [512, 1024, 4096]:
        for H in [32, 128]:
            cases.add((14, r, H, weight(14, r, H)))
    maxima, rows = Counter(), []
    for R, r, H, w in sorted(cases):
        row = complete_case(R, r, H, w, counts)
        for key in row:
            maxima[key] = max(maxima[key], row[key])
        if R >= 16384 or r >= 512 or H >= 4096:
            rows.append(row)
    return {'distinct_triples': len(cases), 'maxima': dict(maxima), 'large_rows': rows,
            'regular_R_interval': [14, 20], 'regular_r_interval': [0, 8],
            'regular_H': [0, 1, 2, 3, 4, 8, 16, 32, 64],
            'additional_R': [128, 1024, 16384], 'additional_r': [512, 1024, 4096],
            'additional_H': [128, 512, 1024, 4096, 16384],
            'scope': 'All three complete original-source prefixes are replayed by ordinary, shortcut, and inverse operations. Every following window is replayed by two independent ordinary-step implementations, with exact shadow congruences. This establishes no meeting in either pair of exit windows, not absence of earlier or later coalescence.'}


def affine_seed(j, A, C):
    M = 1 << (j+3)
    b, z, power = 0, A % M, 9 % M
    assert (A+C) % 8 == 0
    for k in range(j):
        if ((z+C) >> (k+3)) & 1:
            b += 1 << k
            z = z*power % M
        assert (z+C) % (1 << (k+4)) == 0
        power = power*power % M
    assert b < (1 << j) and (A*pow(9, b, M)+C) % M == 0
    return b


def modular_checks(counts):
    params = [(r, H) for r in range(9) for H in range(17)]
    params += [(128, 128), (512, 0), (0, 4096)]
    rows = []
    for r, H in params:
        m, K = 57+11*r, H+12
        M = 1 << (m+K)
        A = pow(3, 35+7*r, M)
        C = 7*A+(1 << m)
        j = m+H+9
        b = affine_seed(j, A, C)
        for B in [0, 1 << (r+H+32)]:
            R = b+(1 << j)*(B+14)
            assert R > B and R >= 14
            X = pow(9, R, M)
            assert (A*X+C) % M == 0
            u_mod, rem = divmod(X+7, 1 << m)
            assert rem == 0
            a_mod = pow(3, 33+7*r, 1 << K)*u_mod % (1 << K)
            assert (9*a_mod+1) % (1 << K) == 0 and a_mod % 64 == 7
            counts['modular_pure_lifts'] += 1
            if r >= 128 or H >= 4096:
                rows.append({'r': r, 'H': H, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'r_interval': [0, 8], 'H_interval': [0, 16],
            'additional_pairs': [[128, 128], [512, 0], [0, 4096]],
            'bounds': ['0', '2**(r+H+32)'], 'large_rows': rows,
            'scope': 'Only exponent coordinates and modular powers are computed for pure sources. Their huge starting integers, quotients, and full trajectories are not materialized. The all-horizon existence and separation statements are kernel theorems.'}


def witness_checks(counts):
    R, r, H = 14, 0, 128
    w = weight(R, r, H)
    starts, ends, clocks, words, a, u, _ = coordinates(R, r, H, w)
    source = (ROOT/SOURCE).read_text()
    assert f'def witnessWeight : Nat := {w}' in source
    assert f'def witnessUnit : Nat := {u}' in source
    arrivals = [1795, 1978, 2660]
    for n, t in zip(starts, arrivals):
        path = ordinary(n, t)
        assert path == paired(n, t)
        assert path[-1] == 1 and 1 not in path[:-1]
        counts['convergent_witness_ordinary_steps'] += t
    separated_windows(a, H, counts)
    return {'R': R, 'r': r, 'H': H, 'weight': str(w), 'unit': str(u),
            'sources': [str(n) for n in starts], 'first_arrival_clocks': arrivals,
            'scope': 'Lean certifies arrivals at one and the separating coordinate conditions for this explicit triple. Python also checks first-arrival minimality and the separated 129-state exit windows.'}


def larger_coordinates(counts):
    rows = []
    for R in [65536, 1048576]:
        r, H = 0, 32
        w = weight(R, r, H)
        starts, ends, clocks, words, a, _, X = coordinates(R, r, H, w)
        for n, t, expected in zip([4*X-5, 243*X-1, 14348907*X-1],
                                  [91, 89, 69], ends):
            assert endpoint(n, t, counts, 'larger_transition_tail_steps') == expected
        separated_windows(a, H, counts)
        rows.append({'R': R, 'r': r, 'H': H, 'N_bits': starts[0].bit_length(),
                     'full_prefixes_replayed': False})
    return {'rows': rows,
            'scope': 'Exact weighted source coordinates, short transition tails, and exit windows are checked. The full initial growing prefixes are not iterated.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumSeventeenSeparation.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 40
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-seventeen-separation-') as directory:
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
                        ('modular_checks', modular_checks), ('witness_checks', witness_checks),
                        ('larger_coordinates', larger_coordinates)]:
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
            'Three finite shadow sets are closed under c -> 3c-9 for odd c and c/2 for even c. The main set is disjoint from either partner set.',
            'Divisibility by 2*d of 9*n+c transfers under one ordinary Collatz step to divisibility by d of 9*C(n)+shadowStep(c), provided c>=9.',
            'For every H and positive a with 2^(H+12) dividing 9a+1, neither partner 81a-17 or64a-17 meets 72a-17 at any pair of clocks s,t<=H. Such a is7mod64.',
            'For every fixed transition block count r and horizon H, arbitrarily large pure exponents R satisfy the transition identities and this separation of the three exit windows.',
            'For every fixed R>=14,r,H and weight bound B, a weight w>B satisfies the transition identities, both partners are smaller than N, and the exit windows are separated.',
            'There is no uniform scalar meeting-clock bound even at any fixed r.',
            'One explicit R14,r0,H128 weighted triple has its coordinate conditions and all three arrivals at1 kernel certified.',
        ],
        'cache_policy': 'Dependencies are reused only after compiler, source, prior log and object authentication; exact objects are copied into an isolated import directory. Missing or mismatched entries are rebuilt. Prior reused-build provenance is retained. The new module is always fresh.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation, or credential access.',
        'finite_scope_limit': 'Full weighted prefixes and finite exit windows, larger tail-only coordinates, modular-only pure exponents, and universal kernel statements are distinct. First-arrival minimality of the witness is Python checked; the kernel certifies arrival.',
        'not_proved': [
            'Failure of eventual coalescence, any divergent positive trajectory, or a nontrivial positive cycle.',
            'Separation of all earlier original-source visits or all visits beyond the specified windows.',
            'Impossibility of a cover using unbounded later clocks or additional partner sources.',
            'Exclusion of arbitrary least counterexamples, convergence of the full transition family, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()

