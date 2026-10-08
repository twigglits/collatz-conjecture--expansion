"""Exact binary-window replay for the separated-block rank obstruction.

The universal block-law theorem is kernel checked for integer scores.
The all-window counting interpretation and real-weight argument are written.
"""
from collections import Counter
import hashlib
import json


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def counts(n, width):
    assert n > 0 and width > 0
    word = '0' * (width - 1) + bin(n)[2:] + '0' * (width - 1)
    return Counter(word[i:i + width] for i in range(len(word) - width + 1))


def combine(terms):
    result = Counter()
    for multiplier, vector in terms:
        for key, value in vector.items():
            result[key] += multiplier * value
    return {key: value for key, value in result.items() if value}


def verify():
    records = []
    block_checks = 0
    for width in range(1, 65):
        zero = '0' * width
        for a, b in ((1, 1), (3, 9), (7, 21), (85, 32), (187, 211)):
            # Include the exact minimum gap allowed by the written law.
            for extra in (0, 1, 17):
                k = b.bit_length() + width - 1 + extra
                n = (a << k) + b
                assert n.bit_length() == a.bit_length() + k
                assert combine([(1, counts(n, width)), (-1, counts(a, width)),
                                (-1, counts(b, width)),
                                (-(k - b.bit_length() - width + 1), {zero: 1})]) == {}
                assert combine([(1, counts(2 * n, width)), (-1, counts(n, width)),
                                (-1, {zero: 1})]) == {}
                block_checks += 1
        for k in (width + 5, width + 23, 4096):
            q = 1 << k
            starts = [2 * q + 2, 2 * q + 21, 6 * q + 9, 14 * q + 1]
            ends = [q + 1, 3 * q + 32, 9 * q + 14, 21 * q + 2]
            assert [step(n) for n in starts] == ends
            weights = [2, 1, 1, 1]
            assert sum(w * (b.bit_length() - a.bit_length())
                       for w, a, b in zip(weights, starts, ends)) == 0
            terms = []
            for w, a, b in zip(weights, starts, ends):
                terms.extend([(w, counts(b, width)), (-w, counts(a, width))])
            assert combine(terms) == {}
            payload = json.dumps(dict(starts=[str(n) for n in starts],
                                      ends=[str(n) for n in ends]), sort_keys=True).encode()
            records.append(dict(width=width, exponent=k,
                                minimum_start_bits=min(n.bit_length() for n in starts),
                                maximum_endpoint_bits=max(n.bit_length() for n in ends),
                                integers_sha256=hashlib.sha256(payload).hexdigest()))
    return dict(all_checks_passed=True, block_law_checks=block_checks,
                family_vector_checks=len(records), certificate_weights=[2, 1, 1, 1],
                cases=records,
                scope='Finite exact window-count replay; the universal block-score contradiction is kernel proved, and its all-window real-score interpretation is written. Not a Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
