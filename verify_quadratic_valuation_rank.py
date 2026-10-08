"""Independent integer replay of the quadratic valuation rank certificates.

No SMT dependency. Universal properness and real logarithm bridges are
written in APERIODIC-ATTEMPT.md, not proved by this finite replay.
"""
import itertools
import json
import math
from pathlib import Path

from verify_valuation_graph_rank import features, stable, step


ROOT = Path(__file__).resolve().parent


def verify():
    data = json.loads((ROOT / 'results/quadratic-valuation-rank/certificates.json').read_text())
    assert data['variables'] == ['C', 'L', 'A', 'B', 'Z', 'W', 'AC', 'AD', 'BC', 'BD', 'CC', 'DD']
    monomials = [(0,), (1,), (2,), (3,), (0, 2), (0, 3), (1, 2), (1, 3), (2, 2), (3, 3)]
    assert data['monomials'] == [list(m) for m in monomials]

    def expand(f):
        return [math.prod(f[i] for i in m) for m in monomials]

    base = []
    # C>0; 12L>7C; C+A>=0; B<=0; BD>=0; A+AD<=0.
    for entries, strict in [({0: 1}, True), ({0: -7, 1: 12}, True),
                            ({0: 1, 2: 1}, False), ({3: -1}, False),
                            ({9: 1}, False), ({2: -1, 7: -1}, False)]:
        vector = [0] * 12
        for j, x in entries.items():
            vector[j] = x
        base.append([vector, strict])
    assert data['base'] == base
    assert 2**19 < 3**12
    patterns = data['patterns']
    assert [p['seed'] for p in patterns] == [151, 153, 155, 170, 230, 233]
    rows, lifted_checks = [], 0
    for pattern in patterns:
        n, modulus, source = pattern['seed'], pattern['modulus'], pattern['source']
        assert modulus > 0 and modulus % 6 == 0
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
                logs = [0, -1]
            elif kind == 'even':
                assert 2 * slope == modulus and 2 * seed == n
                logs = [1, 0]
            elif kind == 'double':
                assert slope == 2 * modulus and seed == 2 * n
                logs = [-1, 0]
            else:
                assert 3 * slope == 2 * modulus and 3 * seed == 2 * n - 1
                assert slope % 2 == 0 and seed % 2 == 1
                logs = [0, 1]
            for q in (0, 1, 2, 17, 2**80 + 13):
                x, y = modulus * q + n, slope * q + seed
                assert features(x) == source and features(y) == v['features']
                assert (step(x) == y if kind in ('odd', 'even') else step(y) == x)
                lifted_checks += 1
            # Proven graph restriction: at multiples of three, a proper rank
            # with local progress must decrease forward (written real bridge).
            if n % 3 == 0 and kind not in ('odd', 'even'):
                continue
            delta = [x - y for x, y in zip(expand(source), expand(v['features']))]
            options.append([logs + delta, kind != 'inverse'])
        rows.append(options)
    assert rows == data['rows']
    choices = list(itertools.product(*(range(len(r)) for r in rows)))
    assert len(choices) == 162
    assert [tuple(c['choices']) for c in data['certificates']] == choices
    for cert in data['certificates']:
        weights = cert['weights']
        inequalities = base + [rows[i][j] for i, j in enumerate(cert['choices'])]
        assert len(weights) == len(inequalities) == 12
        assert all(type(w) is int and w >= 0 for w in weights)
        for j in range(12):
            assert sum(w * row[j] for w, (row, _) in zip(weights, inequalities)) == 0
        assert sum(w for w, (_, strict) in zip(weights, inequalities) if strict) > 0
    # Finite independent diagnostics for the three universal families used
    # in the written properness argument. These are not universal proofs.
    for k in range(2, 257):
        u = next(u for u in range(1, 55, 2) if (2**(k + 1) * u) % 27 == 10)
        n = (2**(k + 1) * u - 1) // 3
        assert features(n) == [0, 1, 1, 0]
        assert features(2**k * u) == [k, 0, 0, 1]
    for b in range(1, 41):
        for c in range(1, 21):
            p, q = 2**(b + 1), 3**(c + 1)
            r, s = 2**b - 1, 3**c
            n = r + p * ((s - r) * pow(p, -1, q) % q)
            assert 0 < n < p * q and features(n) == [0, b, c, 0]
            assert features(2 * n) == [1, 0, c, 0]
            assert features(2**b * 3**c - 1) == [0, b, 0, c]
    return dict(all_checks_passed=True, exhaustive_certificates=len(choices),
                universal_progression_patterns=len(patterns), lifted_edge_checks=lifted_checks,
                finite_properness_family_cases=255 + 800 + 800,
                maximum_certificate_weight=max(max(c['weights']) for c in data['certificates']),
                scope='Finite exact arithmetic; properness, polynomial restrictions, and real interpretation are written bridges. Not a Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
