"""Exact certificate replay, without an SMT solver or floating-point arithmetic.

The all-real weighted-sum argument and logarithmic limits are written in
APERIODIC-ATTEMPT.md. This script checks their finite arithmetic inputs.
"""
import itertools
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DATA = ROOT / 'results' / 'valuation-graph-rank'


def valuation(n, p):
    assert n > 0 and p in (2, 3)
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def features(n):
    return [valuation(n, 2), valuation(n + 1, 2),
            valuation(n, 3), valuation(n + 1, 3)]


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def stable(slope, seed, expected):
    assert features(seed) == expected
    # A multiple of p^(k+1) preserves exact valuation k for every quotient.
    for p, k in zip((2, 2, 3, 3), expected):
        assert slope % p**(k + 1) == 0


def verify():
    data = json.loads((DATA / 'certificates.json').read_text())
    patterns = json.loads((DATA / 'patterns.json').read_text())
    assert data['variables'] == ['C', 'L', 'a', 'b', 'c', 'd']
    base = [([1, 0, 0, 0, 0, 0], True),
            ([-7, 12, 0, 0, 0, 0], True),
            ([3, -5, 0, 0, 0, 0], True),
            ([1, 0, 1, 0, 0, 0], False)]
    assert data['base'] == [[v, strict] for v, strict in base]
    assert 2**19 < 3**12 and 3**5 < 2**8
    assert [p['seed'] for p in patterns] == [131, 134, 137, 142, 147]
    rows = []
    lifted_checks = 0
    for pattern in patterns:
        n, modulus = pattern['seed'], pattern['modulus']
        assert modulus > 0 and modulus % 6 == 0
        source = pattern['source']
        stable(modulus, n, source)
        kinds = ['odd' if n % 2 else 'even', 'double']
        if n % 3 == 2:
            kinds.append('inverse')
        assert [v['kind'] for v in pattern['neighbors']] == kinds
        options = []
        for v in pattern['neighbors']:
            kind, slope, seed = v['kind'], v['slope'], v['seed']
            stable(slope, seed, v['features'])
            if kind == 'odd':
                assert 2 * slope == 3 * modulus and 2 * seed == 3 * n + 1
                log_coeffs, strict = [0, -1], True
            elif kind == 'even':
                assert 2 * slope == modulus and 2 * seed == n
                log_coeffs, strict = [1, 0], True
            elif kind == 'double':
                assert slope == 2 * modulus and seed == 2 * n
                log_coeffs, strict = [-1, 0], True
            else:
                assert 3 * slope == 2 * modulus and 3 * seed == 2 * n - 1
                assert slope % 2 == 0 and seed % 2 == 1
                log_coeffs, strict = [0, 1], False
            delta = [x - y for x, y in zip(source, v['features'])]
            options.append([log_coeffs + delta, strict])
            for q in (0, 1, 2, 17, 2**80 + 13):
                x, y = modulus * q + n, slope * q + seed
                assert features(x) == source and features(y) == v['features']
                assert (step(x) == y if kind in ('odd', 'even') else step(y) == x)
                lifted_checks += 1
        rows.append(options)
    assert rows == data['rows']
    choices = list(itertools.product(*(range(len(r)) for r in rows)))
    assert [tuple(c['choices']) for c in data['certificates']] == choices
    assert len(choices) == 108
    for cert in data['certificates']:
        inequalities = base + [rows[i][j] for i, j in enumerate(cert['choices'])]
        weights = cert['weights']
        assert len(weights) == len(inequalities) == 9
        assert all(type(w) is int and w >= 0 for w in weights)
        for j in range(6):
            assert sum(w * row[j] for w, (row, _) in zip(weights, inequalities)) == 0
        assert sum(w for w, (_, strict) in zip(weights, inequalities) if strict) > 0
    return dict(all_checks_passed=True, exhaustive_certificates=len(choices),
                universal_progression_patterns=len(patterns), lifted_edge_checks=lifted_checks,
                maximum_certificate_weight=max(max(c['weights']) for c in data['certificates']),
                scope='Exact arithmetic inputs; full real rank obstruction is a written deduction, not a Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
