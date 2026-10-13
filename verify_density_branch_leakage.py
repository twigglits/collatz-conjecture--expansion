"""Replay finite branch counts behind the written density-flow audit.

The finite ratios are not estimates with certified asymptotic error bars.
The logarithmic branch criterion remains unproved; Collatz is unresolved.
"""
from collections import Counter, deque
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/density-branch-leakage'
CUTOFFS = (4096, 8192, 65536, 524288)
CYCLE = {1, 2, 4}


def ordinary(n):
    return 3 * n + 1 if n % 2 else n // 2


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def count_hash(counts):
    h = hashlib.sha256()
    for a in sorted(counts):
        if counts[a]:
            h.update(f'{a}:{counts[a]}\n'.encode())
    return h.hexdigest()


def graph_and_order(N):
    successors = {n: ordinary(n) for n in CYCLE}
    for source in range(1, N + 1):
        n = source
        while n not in successors:
            nxt = ordinary(n)
            successors[n] = nxt
            n = nxt
            assert len(successors) < 4000000, 'finite graph budget exceeded'
    assert all(n > 0 and nxt in successors and nxt == ordinary(n)
               for n, nxt in successors.items())
    indegrees = dict.fromkeys(successors, 0)
    for nxt in successors.values():
        indegrees[nxt] += 1
    queue = deque(n for n, degree in indegrees.items() if degree == 0)
    order = []
    while queue:
        n = queue.popleft()
        order.append(n)
        nxt = successors[n]
        indegrees[nxt] -= 1
        if indegrees[nxt] == 0:
            queue.append(nxt)
    assert set(successors) - set(order) == CYCLE
    return successors, order


def aggregate(successors, order, X):
    counts = {n: int(n <= X) for n in successors}
    for n in order:
        counts[successors[n]] += counts[n]
    assert sum(counts[n] for n in CYCLE) == X
    for n in CYCLE:
        counts[n] = X
    return counts


def direct_counts(X):
    counts = Counter()
    steps = 0
    for source in range(1, X + 1):
        n, seen = source, set()
        while n not in seen:
            seen.add(n)
            n = ordinary(n)
            steps += 1
            assert len(seen) < 100000, ('unresolved finite trajectory', source)
        assert n in CYCLE
        counts.update(seen)
    return counts, steps


def ratio_row(b, counts):
    own, other = counts[b], counts.get(2 * (3 * b + 1), 0)
    ratio = Fraction(other, own)
    return {'odd_target': b, 'used_branch_count': own,
            'unused_target': 2 * (3 * b + 1), 'unused_branch_count': other,
            'ratio_numerator': ratio.numerator, 'ratio_denominator': ratio.denominator}


def finite_replay():
    started = time.monotonic()
    graph, order = graph_and_order(max(CUTOFFS))
    print(f'Closed graph: {len(graph)} vertices; only cycle {sorted(CYCLE)}', flush=True)
    direct, direct_steps = direct_counts(CUTOFFS[0])
    comparisons, rows = 0, []
    for X in CUTOFFS:
        counts = aggregate(graph, order, X)
        if X == CUTOFFS[0]:
            assert all(counts[a] == direct[a] for a in graph)
            assert set(direct) <= set(graph)
        for a in order:
            odd_parent = (a - 1) // 3 if a % 6 == 4 else None
            total = int(a <= X) + counts.get(2 * a, 0)
            if odd_parent is not None:
                total += counts.get(odd_parent, 0)
            assert counts[a] == total, (X, a, counts[a], total)
            comparisons += 1
        candidates = [b for b in range(3, 10000, 2)
                      if b % 3 and counts.get(b, 0) * 2000 >= X]
        candidates.sort(key=lambda b: (Fraction(counts.get(2 * (3 * b + 1), 0), counts[b]), b))
        witness = ratio_row(3077, counts)
        witness['merge_target'] = 9232
        witness['merge_count'] = counts[9232]
        assert counts[9232] == counts[3077] + counts.get(18464, 0) + int(9232 <= X)
        if X == 524288:
            assert (counts[3077], counts[18464], counts[9232]) == (206048, 39, 206088)
            assert 1000 * counts[18464] < counts[3077]
        rows.append({'source_cutoff': X, 'target_counts_sha256': count_hash(counts),
                     'noncycle_parent_partitions': len(order), 'witness': witness,
                     'ranked_scope': 'Odd 3<=b<10000, 3 not dividing b, with at least X/2000 represented predecessors.',
                     'smallest_ratios': [ratio_row(b, counts) for b in candidates[:12]]})
        print(f'Exact parent partitions passed at cutoff {X}', flush=True)
    return {'scope': 'Distinct source counts in complete finite forward graphs; no asymptotic density assertion.',
            'source_cutoffs': list(CUTOFFS), 'closed_graph_size': len(graph),
            'maximum_observed_value': max(graph), 'cycle': sorted(CYCLE),
            'finite_convergence_scope': f'All positive sources at most {max(CUTOFFS)}.',
            'direct_replay_source_cutoff': CUTOFFS[0], 'direct_replay_steps': direct_steps,
            'direct_target_comparisons': len(graph), 'parent_partition_checks': comparisons,
            'rows': rows, 'elapsed_seconds': round(time.monotonic() - started, 3)}


def main():
    prior = ['results/predecessor-density-flow/verification.json',
             'results/uniform-predecessor-approximation/verification.json',
             'results/finite-path-packing/verification.json']
    checked = {}
    for name in prior:
        record = json.loads((ROOT / name).read_text())
        for source, expected in record['sha256'].items():
            assert digest(ROOT / source) == expected, (name, source)
        checked[name] = len(record['sha256'])
    replay = finite_replay()
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    sources = [Path(__file__).name, 'docs/DENSITY-BRANCH-LEAKAGE.md',
               'docs/PREDECESSOR-DENSITY-FLOW.md', 'docs/UNIFORM-PREDECESSOR-APPROXIMATION.md',
               'docs/DENSITY-TO-POINTWISE.md', 'docs/FINITE-PATH-PACKING.md',
               'results/predecessor-density-review/verification.json',
               *prior, 'results/density-branch-leakage/replay.json']
    result = {'verified_at_utc': datetime.now(timezone.utc).isoformat(),
              'status': 'passed', 'collatz_status': 'unresolved',
              'prior_hashes_validated': checked,
              'new_lean_compilation': False, 'new_kernel_theorems': 0,
              'kernel_dependency_scope': 'Previously checked nonperiodic parent partition, validated by the prior record; no new Lean replay.',
              'written_scope': ['Summability of unused branch densities along a hypothetical divergent orbit.',
                                'A logarithmic relative branch lower bound would exclude divergent orbits; that lower bound is not proved.',
                                'The existing orbit packing estimate makes reciprocal orbit values summable, so an absolute c/a predecessor lower bound gives no contradiction by summing its contributions.'],
              'external_review': {'url': 'https://arxiv.org/html/2608.27617',
                                  'version': 'arXiv:2608.27617v1, 2026-08-27',
                                  'scope': 'Inspected the claimed program and its remaining condition; no new theorem adopted as an input.'},
              'python_scope': replay,
              'not_proved': ['A positive uniform constant in the logarithmic relative branch estimate.',
                             'Asymptotic density ratios from the finite population ratios.',
                             'Exclusion of divergent orbits or all nontrivial positive cycles.'],
              'sha256': {source: digest(ROOT / source) for source in sources}}
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'], 'closed_graph_size': replay['closed_graph_size'],
                      'parent_partition_checks': replay['parent_partition_checks'],
                      'direct_target_comparisons': replay['direct_target_comparisons'],
                      'collatz_status': result['collatz_status']}, indent=2), flush=True)


if __name__ == '__main__':
    main()
