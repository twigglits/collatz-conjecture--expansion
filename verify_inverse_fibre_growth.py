"""Exhaustive finite inverse-fibre counts and an independent shifted replay.

The exponential lower bound for arbitrary depths is a written proof using
parity-word bijection and pigeonhole counting. Only the listed finite depths
are enumerated here; the 48-member shifted family is separately kernel proved.
"""
from collections import Counter
import json
from math import comb
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def endpoint(n, k):
    weight = 0
    for _ in range(k):
        weight += n % 2
        n = (3 * n + 1) // 2 if n % 2 else n // 2
    return weight, n


def verify():
    certificate = json.loads((ROOT / 'results/inverse-fibre-growth/certificate.json').read_text())
    depth, weight, target = (certificate[key] for key in ('depth', 'weight', 'endpoint'))
    members = certificate['members']
    assert (depth, weight, target) == (16, 4, 2)
    assert len(members) == len(set(members)) == 48
    assert all(0 < n < 2**depth and endpoint(n, depth) == (weight, target) for n in members)
    shifted_checks = 0
    for q in (0, 1, 2, 17, 2**128 + 1, 2**256 - 1):
        lifted = [2**depth * q + n for n in members]
        assert len(set(lifted)) == 48
        for n in lifted:
            assert 2**depth * q <= n < 2**depth * (q + 1)
            assert endpoint(n, depth) == (weight, 3**weight * q + target)
            shifted_checks += 1
    records = []
    for k in range(1, 21):
        fibres = Counter(endpoint(n, k) for n in range(2**k))
        histogram = [0] * (k + 1)
        for (j, y), count in fibres.items():
            assert y < 3**j
            histogram[j] += count
        assert histogram == [comb(k, j) for j in range(k + 1)]
        assert sum(histogram[j] * 3**(k-j) for j in range(k + 1)) == 4**k
        (j, y), maximum = max(fibres.items(), key=lambda item: item[1])
        denominator = (k + 1) * 3**k
        weighted_lower = (4**k + denominator - 1) // denominator
        weightwise_lower = max((comb(k, j) + 3**j - 1) // 3**j for j in range(k + 1))
        assert weighted_lower <= weightwise_lower <= maximum
        if k == depth:
            assert maximum == len(members)
            assert fibres[weight, target] == len(members)
        records.append(dict(depth=k, maximizing_weight=j, endpoint=y,
                            maximum_multiplicity=maximum,
                            weighted_pigeonhole_bound=weighted_lower,
                            weightwise_pigeonhole_bound=weightwise_lower,
                            weight_histogram=histogram))
    return dict(all_checks_passed=True, certificate_members=len(members),
                shifted_member_checks=shifted_checks,
                enumerated_depths=[1, 20], residue_inputs=sum(2**k for k in range(1, 21)),
                records=records,
                scope='Exact finite enumeration through depth 20. Universal 48-member shifts are kernel proved; the all-depth exponential lower bound is written. Not a Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
