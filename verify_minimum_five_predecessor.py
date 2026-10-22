"""Verify the immediate predecessor, its exact size boundary and inverse certificate.

Full weighted meetings, finite windows, modular-only pure lifts and larger
tail-only cases are separate from the universal kernel results.
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

from verify_minimum_inverse_locality import digest, save, ordinary, paired, inverse_tree
from verify_minimum_ladder_block_exit import inverse, shortcut
from verify_minimum_seventeen_transition import BRIDGES, CYCLE
from verify_minimum_seventeen_separation import affine_seed
from verify_minimum_seventeen_fourth import endpoint, SECOND_BRIDGE
from verify_minimum_seventeen_phase import coordinates as base_coordinates, four_windows, secondary_window
from verify_minimum_five_transition import N_BRIDGE, S_BRIDGE, FIVE_CYCLE

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-five-predecessor'
PRIOR = 'results/minimum-five-odd-exit/verification.json'
SOURCE = 'lean/MinimumFivePredecessor.lean'
NOTE = 'docs/MINIMUM-FIVE-PREDECESSOR.md'
HELPERS = ['verify_minimum_inverse_locality.py', 'verify_minimum_ladder_block_exit.py',
           'verify_minimum_seventeen_transition.py', 'verify_minimum_seventeen_separation.py',
           'verify_minimum_seventeen_fourth.py', 'verify_minimum_seventeen_phase.py',
           'verify_minimum_five_transition.py', 'verify_minimum_five_odd_exit.py']
THEOREMS = ['immediate_predecessor', 'main_third_profile', 'scaled_coordinates', 'finite_size_boundary', 'growth_transport', 'slope_boundary', 'denominator_bound', 'padding_bound', 'normalized_scales', 'candidate_size', 'candidate_size_iff', 'candidate_meeting', 'candidate_not_least', 'pure_exponent_bound', 'pure_candidate_above', 'weighted_candidate_escape', 'finite_inverse_certificate', 'certificate_lift', 'certificate_lower', 'fourteen_even_minimum', 'fourteen_even_above_source']


def small_region(s, t):
    return any(s <= a and t <= b for a, b in [(6, 19), (8, 18), (10, 17), (11, 16), (13, 15), (15, 14)])


def weight(R, r, j, k, offset=0):
    D, E, T = 1 << (57+11*r), 1 << (9+11*j), 1 << (3*k+4)
    M = 2*D*E*T
    A, c = pow(3, 35+7*r, M), pow(3, 6+7*j, M)
    w = (D*E*(1+T)-c*D-7*c*A)*pow(c*A*pow(9, R, M), -1, M) % M
    w += offset*M
    assert w > 0 and w % 2 == 1
    return w


def coordinates(R, r, j, k, w):
    starts, ends, clocks, words, a, X = base_coordinates(R, r, w)
    u, rem = divmod(X+7, 1 << (57+11*r))
    assert rem == 0 and u > 0 and u % 2 == 1
    q, rem = divmod(9*a+1, 1 << (9+11*j))
    assert rem == 0 and q > 0 and q % 2 == 1
    b = 3**(6+7*j)*q
    v, rem = divmod(b-1, 1 << (3*k+4))
    assert rem == 0 and v > 0 and v % 2 == 1
    d = 9**(k+1)*v
    D, E = 1 << (57+11*r), 1 << (9+11*j)
    den, fac = 1 << (70+11*(r+j)+3*k), 3**(43+7*(r+j)+2*k)
    padding = 7*fac+9**(k+1)*D*(3**(6+7*j)-E)
    assert den*d == fac*X+padding and padding <= 10*fac
    assert d > 2 and 3*(d-2)+1 == 3*d-5
    assert (d-2 < starts[0]) == small_region(r+j, R+k)
    assert (starts[0] < d-2) == (not small_region(r+j, R+k))
    return starts, ends, clocks, words, a, X, b, v, d


def generic_checks(counts):
    inside = []
    for s in range(5, 65):
        for t in range(14, 65):
            A, B = 3**(43+7*s+2*t), 1 << (72+11*s+3*t)
            if small_region(s, t):
                assert 1000*A <= 993*B and A < B
                inside.append((s, t))
            else:
                assert B <= A
            counts['size_comparison_pairs'] += 1
    assert len(inside) == 39
    assert 9**35+7 < 2**112
    for k in list(range(33))+[128, 1024, 4096]:
        for v in list(range(1, 64, 2))+[2**128+1, 3**128+2]:
            d = 9**(k+1)*v
            assert ordinary(d-2, 1) == paired(d-2, 1) == [d-2, 3*d-5]
            assert shortcut(d-2, 'O', counts) == (3*d-5)//2
            assert inverse((3*d-5)//2, 'O', counts) == d-2
            counts['generic_immediate_predecessors'] += 1
        for v in [2, 4]:
            d = 9**(k+1)*v
            assert ordinary(d-2, 1)[-1] != 3*d-5
            counts['even_units_outside_merger_hypothesis'] += 1
    return {'size_s_interval': [5, 64], 'size_t_interval': [14, 64], 'inside_pairs': inside,
            'generic_k_interval': [0, 32], 'additional_k': [128, 1024, 4096],
            'odd_v_interval': [1, 63], 'additional_odd_v': ['2**128+1', '3**128+2'],
            'scope': 'Finite arithmetic supplements the universal size boundary. Odd units have the immediate merger; even units are deliberately outside its hypothesis.'}


def inverse_states():
    seen, stack = {(0, 0, 2)}, [(0, 0, 2)]
    while stack:
        e, o, m = stack.pop()
        children = [(e+1, o, 2*m)] if e < 14 else []
        if (2*m+1) % 3 == 0:
            children.append((e, o+1, (2*m+1)//3))
        for child in children:
            if child not in seen:
                seen.add(child)
                stack.append(child)
    return seen


def actual_inverse_check(K, v, reference, counts):
    b = 3**K*v-2
    states = inverse_tree(b, 14)
    expected = {(2**(e+o)*3**(K-o)*v-m, e, o) for e, o, m in reference}
    assert states == expected and len(states) == 683
    assert min(p for p, e, o in states) == b and max(o for p, e, o in states) == 13
    for p, e, o in states:
        assert endpoint(p, e+2*o, counts, 'inverse_forward_steps') == b
    counts['inverse_complete_trees'] += 1
    counts['inverse_tree_states'] += len(states)
    return {'K': K, 'unit_bits': v.bit_length(), 'target_bits': b.bit_length(), 'states': len(states)}


def certificate_checks(counts):
    states = inverse_states()
    source_text = (ROOT/SOURCE).read_text()
    table = source_text.split('def inverseStates :', 1)[1].split(']\n', 1)[0]
    source_rows = [tuple(map(int, row)) for row in re.findall(r'\((\d+), (\d+), (\d+)\)', table)]
    assert len(source_rows) == len(set(source_rows)) == len(states) == 683
    assert set(source_rows) == states
    for e, o, m in states:
        assert e <= 14 and o < 14 and m >= 2
        assert m+3**14 <= 2+2**(e+o)*3**(14-o)
        if e < 14:
            assert (e+1, o, 2*m) in states
        if (2*m+1) % 3 == 0:
            assert (e, o+1, (2*m+1)//3) in states
    counts['reference_certificate_states'] = len(states)
    rows = []
    for K in [14, 16, 32, 128, 4096]:
        for v in [1, 2, 3, 17, 2**128+1]:
            rows.append(actual_inverse_check(K, v, states, counts))
    for R in [14, 36, 128]:
        for j in [0, 1]:
            for k in [6, 14, 64]:
                w = weight(R, 5, j, k)
                starts, _, _, _, _, _, _, v, d = coordinates(R, 5, j, k, w)
                assert d-2 > starts[0]
                row = actual_inverse_check(2*k+2, v, states, counts)
                row.update(R=R, r=5, j=j, k=k, source_comparison='N<U<=every_predecessor')
                rows.append(row)
    return {'reference_states': 683, 'even_budget': 14, 'reference_precision': 14,
            'max_odd_edges': 13, 'max_reference_offset': max(m for e, o, m in states), 'rows': rows,
            'scope': 'Complete inverse trees have no imposed odd-edge or total-depth cap. Every state is compared with the reference formula and replayed forward. These concern predecessors of U=d-2, not every predecessor of the later N endpoint or every coalescing source.'}


def complete_case(R, r, j, k, w, counts):
    starts, ends, clocks, words, _, _, b, v, d = coordinates(R, r, j, k, w)
    N, U = starts[0], d-2
    target = (3*d-5)//2
    nw = words[0]+SECOND_BRIDGE+CYCLE*j+N_BRIDGE+FIVE_CYCLE*k+'E'
    nc = 5*R+117+18*r+18*j+5*k
    assert len(nw)+nw.count('O') == nc
    checkpoints = {clocks[0]: ends[0], clocks[0]+16+18*j: 4*b-17, nc-1: 3*d-5}
    assert endpoint(N, nc, counts, 'complete_N_steps', checkpoints) == target
    assert endpoint(U, 2, counts, 'complete_U_steps', {1: 3*d-5}) == target
    assert shortcut(N, nw, counts) == shortcut(U, 'O', counts) == target
    assert inverse(target, nw[::-1], counts) == N
    assert inverse(target, 'O', counts) == U
    if U < N:
        counts['complete_smaller_candidates'] += 1
    else:
        counts['complete_larger_candidates'] += 1
    if d % 4 == 3:
        counts['complete_d_three_mod_four'] += 1
    else:
        exponent = ((d-1) & -(d-1)).bit_length()-1
        assert exponent >= 2
        z = (d-1) >> exponent
        g = pow(3, exponent, 4)*z % 4
        counts['complete_odd_exit_residue_'+str(g)] += 1
    counts['complete_candidate_pairs'] += 1
    return {'R': R, 'r': r, 'j': j, 'k': k, 'weight_bits': w.bit_length(),
            'N_bits': N.bit_length(), 'U_bits': U.bit_length(), 'v_bits': v.bit_length(),
            'N_clock_with_shared_halving': nc, 'candidate_smaller': U < N}


def complete_paths(counts):
    params = set()
    for s in range(5, 16):
        for t in range(14, 20):
            if small_region(s, t):
                for r in range(5, s+1):
                    for R in range(14, t+1):
                        for offset in [0, 1]:
                            params.add((R, r, s-r, t-R, offset))
    assert len(params) == 784
    for s in range(5, 18):
        for t in range(14, 22):
            if not small_region(s, t):
                params.add((14, 5, s-5, t-14, 0))
                params.add((t, s, 0, 0, 0))
    params.add((36, 5, 0, 0, 0))
    for R in [128, 1024, 16384]:
        params.add((R, 5, 1, 6, 0))
    for r in [128, 512, 4096]:
        params.add((14, r, 1, 6, 0))
    for j in [128, 512, 4096]:
        params.add((14, 5, j, 6, 0))
    for k in [128, 512, 4096]:
        params.add((14, 5, 1, k, 0))
    maxima, rows = Counter(), []
    for R, r, j, k, offset in sorted(params):
        row = complete_case(R, r, j, k, weight(R, r, j, k, offset), counts)
        for key, value in row.items():
            if key != 'candidate_smaller':
                maxima[key] = max(maxima[key], value)
        if max(R, r, j, k) >= 128:
            rows.append(row)
    return {'distinct_cases': len(params), 'inside_parameter_quadruples': 392,
            'inside_weight_offsets': [0, 1], 'maxima': dict(maxima), 'large_rows': rows,
            'scope': 'Full N paths and immediate U predecessors are replayed to a common value after one shared halving. All 392 parameter quadruples in the smaller-candidate region have two weights, while boundary and large cases check strict reverse inequalities. No earliest-meeting claim.'}


def modular_checks(counts):
    params = [(r, j, k) for r in [5, 6] for j in range(4) for k in range(9)]
    params += [(128, 128, 128), (512, 1, 6), (5, 128, 1024)]
    rows = []
    maxima = Counter()
    for r, j, k in params:
        m, K = 57+11*r, 9+11*j
        D, E, T = 1 << m, 1 << K, 1 << (3*k+4)
        M = 2*D*E*T
        A, c = pow(3, 35+7*r, M), 3**(6+7*j)
        ca = c*A % M
        F = 7*ca+D*(c-E)+D*E*T
        precision = m+K+3*k+2
        seed = affine_seed(precision, ca, F)
        for B in [0, 1 << (r+j+k+32)]:
            R = seed+(1 << precision)*(B+14)
            assert R > B and R >= 36
            X = pow(9, R, M)
            assert (ca*(X+7)+c*D) % M == D*E*(1+T)
            u_mod, rem = divmod(X+7, D)
            assert rem == 0 and u_mod % 2 == 1
            aq = pow(3, 35+7*r, 2*E*T)*u_mod % (2*E*T)
            q_mod, rem = divmod(aq+1, E)
            assert rem == 0 and q_mod % 2 == 1
            b_mod = c*q_mod % (2*T)
            v_mod, rem = divmod(b_mod-1, T)
            assert rem == 0 and v_mod == 1
            assert not small_region(r+j, R+k)
            counts['modular_pure_lifts'] += 1
            maxima['exponent_bits'] = max(maxima['exponent_bits'], R.bit_length())
            if max(r, j, k) >= 128:
                rows.append({'r': r, 'j': j, 'k': k, 'R_bits': R.bit_length(), 'B_bits': B.bit_length()})
    return {'regular_r': [5, 6], 'regular_j_interval': [0, 3], 'regular_k_interval': [0, 8],
            'large_rows': rows, 'maxima': dict(maxima),
            'scope': 'Pure coordinates and odd units are checked modulo powers of two. All exponents exceed the proved lower bound36. Pure starting values, trajectories and candidate sizes are not materialized; their universal size comparison is a kernel theorem.'}


def larger_tails(counts):
    rows = []
    for R in [65536, 1048576]:
        r = 5
        for j, k in [(1, 6), (16, 128)]:
            w = weight(R, r, j, k)
            starts, ends, _, _, _, X, b, v, d = coordinates(R, r, j, k, w)
            assert endpoint(4*X-5, 91+18*r, counts, 'larger_primary_tail_steps') == ends[0]
            assert endpoint(ends[0], 16+18*j, counts, 'larger_secondary_tail_steps') == 4*b-17
            assert endpoint(4*b-17, 9+5*k, counts, 'larger_third_tail_steps') == 3*d-5
            assert endpoint(d-2, 1, counts, 'larger_U_steps') == 3*d-5
            assert starts[0] < d-2
            rows.append({'R': R, 'r': r, 'j': j, 'k': k, 'N_bits': starts[0].bit_length(),
                         'U_bits': (d-2).bit_length(), 'full_initial_prefix_replayed': False,
                         'large_inverse_tree_enumerated': False})
    return {'rows': rows, 'scope': 'Only the three N transition tails and the one-step U merger are replayed. Exact large source comparisons are checked, but full initial prefixes and large inverse trees are not enumerated.'}

def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumFivePredecessor.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 45
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-five-predecessor-') as directory:
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
    for name, check in [('generic_checks', generic_checks), ('certificate_checks', certificate_checks),
                        ('complete_paths', complete_paths), ('modular_checks', modular_checks),
                        ('larger_tails', larger_tails)]:
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
        'kernel_theorems_audited': len(THEOREMS),
        'axiom_free_roots': ['MinimumFivePredecessor.finite_size_boundary'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])}, 'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For every positive odd v, U=9^(k+1)*v-2 is a positive immediate ordinary predecessor of3d-5, and coalesces with N at its third endpoint. No final odd-block residue is required.',
            'For R>=14,r>=5,w>0 and the three coordinate equations, U<N holds exactly when SmallRegion(r+j,R+k) holds. Outside that region N<U strictly. The boundary is independent of w and of the final residue.',
            'For each fixed parameter quadruple inside the region, unbounded weights have positive odd third units, the immediate merger and least-source exclusion.',
            'A pure source with r>=5 and positive first quotient has R>=36. Thus U is strictly larger than every pure N in this coordinate family.',
            'A finite kernel certificate with683 states proves closure of all admissible inverse paths with at most14 even-input shortcut edges at reference precision14. No odd-count or total-depth hypothesis is imposed on paths.',
            'A generic certificate lift transports the exact reference offset to every target3^K*v-2 with K>=14 and positive v, proving that no such inverse predecessor is smaller than the target.',
            'For k>=6 the inverse minimum at U=d-2 is exactly U at even budget14. Since R+k>=20, all those predecessors are strictly larger than N under the source hypotheses.',
        ],
        'cache_policy': 'Exact compiler, source, prior log and object authentication precedes reuse. Copied dependency objects are isolated, provenance is retained, and the new module is always freshly built.',
        'external_dependency': 'Lean4.33.1 and standard libraries; no external mathematical premise, new installation or credential access.',
        'finite_scope_limit': 'Finite size comparisons, generic one-step mergers, complete inverse trees, complete weighted N/U paths, modular-only pure coordinates and larger tail-only cases have separate scopes. Full shortcut comparisons add one shared halving to the kernel merger. The inverse obstruction concerns U, not all other coalescing sources or later targets.',
        'not_proved': [
            'A smaller source outside the exact SmallRegion via this immediate predecessor.',
            'An obstruction for all inverse budgets, all predecessors of3d-5, or all coalescing branches.',
            'Convergence of the entire coordinate family or a least-source exclusion for every final exit.',
            'Exclusion of arbitrary least counterexamples, nontrivial positive cycles, divergence or the full Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
