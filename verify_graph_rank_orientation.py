"""Exact replay of closed finite bases and growing, feature-matched witnesses.

The universal orientation theorem is separately kernel proved. This finite
calculation neither constructs a global rank nor proves universal convergence.
"""
import json


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def val(n, p):
    assert n > 0
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def features(n, modulus):
    return [val(n, 2), val(n + 1, 2), val(n, 3), val(n + 1, 3), n % modulus]


def closed_base(limit):
    region = {0, 1, 2}
    for n in range(1, limit + 1):
        path, seen = [], set()
        while n not in region:
            assert n not in seen, 'Nontrivial cycle encountered'
            assert len(path) < 100000, 'Finite replay fuel exhausted'
            seen.add(n)
            path.append(n)
            n = step(n)
        region.update(path)
    assert all(step(n) in region for n in region)
    assert all(n in region for n in range(limit + 1))
    return region


def verify():
    cases = []
    for limit in (1, 2, 26, 100, 1000, 32768):
        region = closed_base(limit)
        bound = max(region)
        witnesses = []
        for modulus in (1, 2, 3, 5, 16, 27, 97):
            s = modulus * (bound + 1)
            path = [192 * s - 5, 288 * s - 7, 432 * s - 10, 216 * s - 5]
            assert all(step(a) == b for a, b in zip(path, path[1:]))
            assert all(n > bound and n not in region for n in path)
            assert min(path) == path[0] and path[-1] > path[0]
            left, right = features(path[0], modulus), features(path[-1], modulus)
            assert left == right and left[:4] == [0, 2, 0, 0]
            witnesses.append(dict(modulus=modulus, parameter=s, path=path, endpoint_features=left))
        cases.append(dict(base_limit=limit, region_size=len(region), region_bound=bound,
                          witnesses=witnesses))
    return dict(all_checks_passed=True, cases=cases, witness_count=42,
                scope='Finite closed-base and exact path replay; the general graph orientation theorem is kernel proved separately. No Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
