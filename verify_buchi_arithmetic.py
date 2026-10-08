"""Exact finite replay of fixed-block pumping conditions.

This does not construct a Buchi recognizer or prove Collatz termination.
The all-length number-theoretic and language arguments are documented in
APERIODIC-ATTEMPT.md; Lean proves the necessary divisibility certificates.
"""

import itertools
import json
import math
from fractions import Fraction


def affine(word):
    a, b, d = 1, 0, 1
    for bit in word:
        if bit:
            a, b = 3 * a, 3 * b + d
        d *= 2
    return a, b, d


def forward(word, n):
    for bit in word:
        if n % 2 != bit:
            return None
        n = (3 * n + 1) // 2 if bit else n // 2
    return n


def backward(word, n):
    for bit in reversed(word):
        if bit:
            numerator = 2 * n - 1
            if numerator % 3:
                return None
            n = numerator // 3
        else:
            n *= 2
    return n


def valuation(n, prime):
    n = abs(n)
    assert n != 0
    result = 0
    while n % prime == 0:
        n //= prime
        result += 1
    return result


def polynomial(coefficients, x):
    result = 0
    for coefficient in reversed(coefficients):
        result = result * x + coefficient
    return result


def polynomial_ranking_witness(primes, modulus, polynomials):
    """Construct growing endpoints indistinguishable by the finite features.

    The supplied prime list must contain every prime factor of modulus.
    Every computation, including the rational fixed point, is exact.
    """
    remaining = modulus
    for prime in primes:
        while remaining % prime == 0:
            remaining //= prime
    assert remaining == 1 and 2 in primes and 3 in primes
    period = math.lcm(*(p - 1 for p in primes if p > 3))
    j = period
    while True:
        a, b, d = 3**j, 3**j - 2**j, 2**(j + 1)
        c = Fraction(b, d - a)
        if j >= 2 and all(polynomial(f, c) != 0 for f in polynomials):
            break
        j += period
    assert a > d and c < 0
    precision = {}
    for prime in primes:
        assert c.denominator % prime
        values = [polynomial(f, c) for f in polynomials]
        local = [valuation(v.numerator, prime) - valuation(v.denominator, prime) for v in values]
        assert min(local) >= 0
        precision[prime] = max(1, valuation(modulus, prime), 1 + max(local))
    progression = math.prod(p ** (precision[p] + (j + 1 if p == 2 else 0)) for p in primes)
    residue = c.numerator * pow(c.denominator, -1, progression) % progression
    rows = []
    word = (1,) * j + (0,)
    for lift in (1, 2, 2**40):
        n = residue + progression * lift
        m = forward(word, n)
        assert m is not None and m > n
        assert m % modulus == n % modulus
        assert d * m == a * n + b
        features = []
        for f in polynomials:
            before = polynomial(f, n)
            after = polynomial(f, m)
            row = [valuation(before, p) for p in primes]
            assert row == [valuation(after, p) for p in primes]
            features.append(row)
        rows.append({"lift": lift, "start_hex": hex(n), "end_hex": hex(m), "valuations": features})
    return {"primes": primes, "modulus": modulus, "polynomials_low_degree_first": polynomials,
            "odd_steps": j, "final_even_steps": 1, "fixed_point": str(c),
            "progression_hex": hex(progression), "precision": precision, "witnesses": rows}


def main():
    direction_checks = 0
    fixed_points = set()
    for length in range(1, 9):
        for word in itertools.product((0, 1), repeat=length):
            a, b, d = affine(word)
            if d > a and b % (d - a) == 0:
                fixed = b // (d - a)
                if fixed > 0:
                    assert forward(word, fixed) == fixed
                    fixed_points.add(fixed)
            for endpoint in range(1, 129):
                delta = (d - a) * endpoint - b
                left, right = endpoint, endpoint
                for repeats in range(6):
                    assert (left is not None) == (delta % (a**repeats) == 0)
                    assert (right is not None) == (delta % (d**repeats) == 0)
                    if left is not None:
                        assert left > 0
                        assert a**repeats * ((d - a) * left - b) == d**repeats * delta
                    if right is not None:
                        assert right > 0
                        assert d**repeats * ((d - a) * right - b) == a**repeats * delta
                    direction_checks += 2
                    left = None if left is None else backward(word, left)
                    right = None if right is None else forward(word, right)

    pumping_checks = 0
    for k in range(1, 129):
        endpoint = 3**k - 1
        assert forward((1,) * k, 2**k - 1) == endpoint
        for added in range(1, 17):
            assert backward((1,) * (k + added), endpoint) is None
            pumping_checks += 1

    feature_family_checks = 0
    for modulus in (1, 2, 3, 9, 16, 25, 72, 1024, 65537):
        for multiplier in (1, 2, 17, 2**80 + 1):
            s = modulus * multiplier
            n, m = 192 * s - 5, 216 * s - 5
            assert forward((1, 1, 0), n) == m and m > n > 2
            assert n % modulus == m % modulus
            features = lambda x: (valuation(x, 2), valuation(x + 1, 2),
                                  valuation(x, 3), valuation(x + 1, 3))
            assert features(n) == features(m) == (0, 2, 0, 0)
            feature_family_checks += 1
    polynomials = [(0, 1), (1, 1), (5, 1), (1, 1, 1), (1, 0, 1), (7, 5), (1, 2, 1)]
    general_witnesses = [polynomial_ranking_witness(primes, modulus, polynomials)
                         for primes, modulus in (
                             ((2, 3), 1),
                             ((2, 3), 72),
                             ((2, 3, 5, 7), 2880),
                             ((2, 3, 5, 7, 11, 13), 720720),
                             ((2, 3, 17, 19), 2**20 * 3**4 * 17 * 19),
                         )]

    print(json.dumps({
        "all_checks_passed": True,
        "words": sum(2**length for length in range(1, 9)),
        "max_word_length": 8,
        "positive_endpoints_per_word": 128,
        "max_repetitions": 5,
        "direction_checks": direction_checks,
        "odd_prefix_pumping_checks": pumping_checks,
        "positive_fixed_points_seen": sorted(fixed_points),
        "expanding_feature_family_checks": feature_family_checks,
        "polynomial_feature_witnesses": general_witnesses,
        "scope": "Finite exact checks of both directions of the block divisibility criterion. Not an all-input convergence certificate or a formal automaton proof.",
    }, indent=2))


if __name__ == "__main__":
    main()
