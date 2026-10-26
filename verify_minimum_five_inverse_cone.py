"""Audit parameter-dependent inverse bounds and the pure-source obstruction.

Kernel proofs quantify over all paths at the stated even budget. Independent
trees have no imposed odd-count or total-depth cap; their scope is finite.
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

from verify_minimum_inverse_locality import digest, save, inverse_tree, ordinary, paired
from verify_minimum_five_predecessor import weight, coordinates

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-five-inverse-cone'
PRIOR = 'results/minimum-five-predecessor/verification.json'
SOURCE = 'lean/MinimumFiveInverseCone.lean'
NOTE = 'docs/MINIMUM-FIVE-INVERSE-CONE.md'
THEOREMS = [
    'two_reference', 'five_reference', 'reference_odd_bound', 'reference_lift',
    'potential_lower', 'budget_monotone', 'two_lower', 'five_lower',
    'five_block', 'five_blocks', 'five_exact_minimum', 'precision_boundary_witness', 'backtrack_first',
    'third_inverse_minimum', 'half_third_lower', 'doubled_growth', 'source_gap',
    'pure_half_third_obstruction', 'weighted_half_third_obstruction', 'half_third_profile',
]


def reference(c, budget):
    seen, stack = set(), [(0, 0, c)]
    while stack:
        e, o, m = stack.pop()
        if (e, o, m) in seen:
            continue
        seen.add((e, o, m))
        if e < budget:
            stack.append((e + 1, o, 2 * m))
        if (2 * m + 1) % 3 == 0:
            stack.append((e, o + 1, (2 * m + 1) // 3))
    return seen


def forward_check(p, e, o, target, counts):
    """Reconstruct the word from input parities, then replay ordinary steps."""
    start, odds, evens = p, 0, 0
    for _ in range(e + o):
        if p % 2:
            p = (3 * p + 1) // 2
            odds += 1
        else:
            p //= 2
            evens += 1
    assert (p, evens, odds) == (target, e, o)
    path = ordinary(start, e + 2 * o)
    assert path[-1] == target
    assert path == paired(start, e + 2 * o)
    counts['inverse_states_replayed'] += 1
    counts['inverse_forward_ordinary_steps'] += e + 2 * o


def reference_checks(counts):
    rows = []
    for c, a in [(2, 2), (5, 4)]:
        states = reference(c, 24)
        for e, o, m in states:
            assert o <= 2 * e and m >= c
            d = 2 * e - o
            assert 2 ** d * (m - 1) <= a * 3 ** d
            if c == 2:
                assert m >= 5 or (e, o, m) in [(0, 0, 2), (1, 0, 4), (1, 1, 3)]
            if e < 24:
                assert (e + 1, o, 2 * m) in states
            if (2 * m + 1) % 3 == 0:
                assert (e, o + 1, (2 * m + 1) // 3) in states
        counts['reference_states'] += len(states)
        rows.append({'offset': c, 'even_budget': 24, 'states': len(states),
                     'max_odd_count': max(o for e, o, m in states)})
    return {'rows': rows, 'scope': 'Complete finite reference graphs, with no odd or depth cap.'}


def exact_trees(counts):
    rows = []
    budgets = list(range(9)) + [12, 16]
    for c in [2, 5]:
        for B in budgets:
            refs = reference(c, B)
            cases = [(2 * B + 1, v) for v in [1, 2, 3, 17, 2 ** 128 + 1]]
            cases += [(2 * B + 2, 1), (2 * B + 19, 3)]
            if B in [0, 8, 16]:
                cases.append((4096, 2 ** 128 + 1))
            for K, v in cases:
                b = 3 ** K * v - c
                if b <= 0:
                    continue
                actual = inverse_tree(b, B)
                expected = {(2 ** (e + o) * 3 ** (K - o) * v - m, e, o)
                            for e, o, m in refs}
                assert actual == expected
                lower = 8 ** B * 3 ** (K - 2 * B) * v
                for p, e, o in actual:
                    assert o <= 2 * e and lower <= p + (3 if c == 2 else 5)
                    forward_check(p, e, o, b, counts)
                minimum = min(p for p, e, o in actual)
                if c == 5:
                    assert minimum == lower - 5
                    assert (lower - 5, B, 2 * B) in actual
                    counts['exact_five_minima'] += 1
                counts['complete_inverse_trees'] += 1
                rows.append({'offset': c, 'B': B, 'K': K, 'v_bits': v.bit_length(),
                             'target_bits': b.bit_length(), 'states': len(actual),
                             'minimum_bits': minimum.bit_length()})
    return {'rows': rows, 'scope': 'Every state in each complete positive inverse tree is compared with the reference formula and replayed by two ordinary implementations.'}


def endpoint_trees(counts):
    rows = []
    for k in list(range(9)) + [12, 16]:
        for v in [1, 3, 17]:
            d = 9 ** (k + 1) * v
            H = (3 * d - 5) // 2
            states = inverse_tree(H, k)
            expected = {(H, 0, 0)}
            expected |= {(p, e, o + 1) for p, e, o in inverse_tree(d - 2, k)}
            if k:
                expected |= {(p, e + 1, o) for p, e, o in inverse_tree(2 * H, k - 1)}
            assert states == expected
            for p, e, o in states:
                assert 9 * 8 ** k * v <= p + 3
                forward_check(p, e, o, H, counts)
            counts['complete_half_endpoint_trees'] += 1
            rows.append({'k': k, 'v': v, 'states': len(states), 'minimum': min(p for p, e, o in states)})
    return {'rows': rows, 'scope': 'Complete half-endpoint trees through the full even budget k, including both possible first inverse edges.'}


def weighted_paths(counts):
    rows = []
    cases = [(R, r, j, k) for R in [26, 36, 64] for r in [5, 8]
             for j in [0, 2] for k in [0, 1, 6, 16]]
    cases += [(512, 32, 16, 64), (4096, 128, 128, 4096)]
    for R, r, j, k in cases:
        w = weight(R, r, j, k)
        starts, _, _, _, _, _, b, v, d = coordinates(R, r, j, k, w)
        N, H = starts[0], (3 * d - 5) // 2
        Z, W = 9 * 8 ** k * v, 3 * 8 ** (k + 1) * v - 5
        assert N + 3 < Z and 2 * W + 13 == 3 * b
        clock = 5 * R + 117 + 18 * r + 18 * j + 5 * k
        path = ordinary(N, clock)
        assert path[-1] == H and path == paired(N, clock)
        forward_check(W, k + 2, 2 * (k + 1), H, counts)
        forward_check(d - 2, 0, 1, H, counts)
        counts['complete_weighted_sources'] += 1
        counts['weighted_source_ordinary_steps'] += clock
        budget = min(k, 8)
        tree = inverse_tree(H, budget)
        for p, e, o in tree:
            assert N < p and Z <= p + 3
            forward_check(p, e, o, H, counts)
        counts['weighted_endpoint_trees'] += 1
        counts['weighted_trees_at_full_k_budget'] += budget == k
        rows.append({'R': R, 'r': r, 'j': j, 'k': k, 'weight_bits': w.bit_length(),
                     'N_bits': N.bit_length(), 'H_bits': H.bit_length(), 'v_bits': v.bit_length(),
                     'N_clock': clock, 'inverse_budget': budget, 'inverse_states': len(tree),
                     'full_initial_prefix_replayed': True, 'full_k_inverse_budget': budget == k})
    return {'rows': rows, 'scope': 'Complete N, U and W paths. Every weighted inverse tree is complete at its recorded budget, which is min(k,8), not always the full k. No enormous pure trajectory is materialized.'}


def boundary_checks(counts):
    forward_check(39, 2, 5, 76, counts)
    assert 76 + 5 == 3 ** (2 * 2) and 39 < 8 ** 2 - 5
    counts['precision_boundary_witnesses'] += 1
    for s in range(5, 65):
        for t in range(26, 65):
            assert 2 * 2 ** (72 + 11 * s + 3 * t) <= 3 ** (43 + 7 * s + 2 * t)
            counts['doubled_coefficient_comparisons'] += 1
    assert 9 ** 35 + 7 < 2 ** 112
    return {'s': [5, 64], 't': [26, 64], 'precision_boundary': {'B': 2, 'K': 4, 'v': 1, 'target': 76, 'predecessor': 39, 'e': 2, 'o': 5}, 'scope': 'Finite coefficient checks supplement the universal kernel growth transport. The actual 39-to-76 path shows that allowing K=2B invalidates the odd-count bound and the proposed exact minimum.'}


def audit_log(source, output):
    assert not any(s in output for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
    roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", output, re.M)
    if source == SOURCE:
        assert {n for n, _ in roots} == {'MinimumFiveInverseCone.'+t for t in THEOREMS}
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
    assert len(sources) == len(set(sources)) == 46
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-five-inverse-cone-') as directory:
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
    prior = json.loads((ROOT / PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT / name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    version, sources, builds = build(prior, args.lean, args.threads, args.cache)
    counts, sections = Counter(), {}
    for check in [reference_checks, exact_trees, endpoint_trees, weighted_paths, boundary_checks]:
        sections[check.__name__] = check(counts)
        print('Independent replay passed:', check.__name__, flush=True)
    save(OUT / 'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources + [Path(__file__).name, NOTE, PRIOR]
    # Include all imported Python helpers and their transitive source record.
    files += [name for name in prior['sha256'] if name.endswith('.py')]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT / 'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'fresh_build_count': sum(b['fresh_build'] for b in builds),
        'reused_verified_build_count': sum(b['reused_verified_build'] for b in builds),
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': [],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For negative reference offsets 2 and 5, induction bounds every reference path by o<=2e and a power potential. No finite state certificate is used.',
            'If 2B<K, all actual inverse paths into 3^K*v-c with e<=B lift to the reference graph. No odd-count or total-depth assumption is imposed.',
            'At offset 2 the bound is p+3>=8^B*3^(K-2B)*v. At offset 5 the exact minimum is 8^B*3^(K-2B)*v-5, attained by B inverse EOO blocks.',
            'The precision hypothesis is essential in general: at B=2,K=4,v=1, a path from39 to76 has e=2,o=5 and39<8^2-5.',
            'The exact minimum at 3d-5, d=9^(k+1)*v, with e<=k+1 is W=3*8^(k+1)*v-5.',
            'At H=(3d-5)/2, both first inverse branches are covered. Every path with e<=k obeys p+3>=9*8^k*v.',
            'All weighted sources with R>=26,r>=5 and the three coordinates satisfy N+3<9*8^k*v. Hence all such inverse predecessors of H are strictly larger than N.',
            'Every pure source in the coordinate family has R>=36, so the same obstruction holds throughout the pure family.',
            'H is an actual N iterate at ordinary clock 5R+117+18r+18j+5k.',
        ],
        'cache_policy': 'Compiler, source, prior log and object hashes are checked before reuse; dependencies are copied into isolated imports and the new module is built freshly.',
        'external_dependency': 'Lean 4.33.1 and standard libraries. The public compiler release was restored this session. No external mathematical premise or credential access.',
        'not_proved': [
            'Exact inverse minimum at the half endpoint H or at offset 2 for arbitrary budgets.',
            'An obstruction for paths with e>k at H, all later targets, or all coalescing sources.',
            'Convergence of the full coordinate family, exclusion of all least counterexamples, cycles, divergence, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT / name) for name in dict.fromkeys(files)},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'fresh_builds': sum(b['fresh_build'] for b in builds),
                      'reused_builds': sum(b['reused_verified_build'] for b in builds),
                      'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
