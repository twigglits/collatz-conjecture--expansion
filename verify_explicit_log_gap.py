#!/usr/bin/env python3
"""Exact checks for docs/EXPLICIT-LOG-GAP.md; optional extended Farey replay.

Uses integers and Fraction only. The integral argument, its all-index
denominator proof, and the external prime estimate remain written proofs.
This script prints results and never writes to the repository.
"""

import argparse
from fractions import Fraction as F
import json
from math import comb, lcm
from time import monotonic

from verify_mask_resonance import catalog, require


POLYNOMIAL = [72, -450, 1153, -1550, 1153, -450, 72]
CENTERED = [4900, -14700, 18301, -12102, 4483, -882, 72]


def multiply(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def power(p, n):
    out = [1]
    for _ in range(n):
        out = multiply(out, p)
    return out


def bernstein(p, a, b):
    coefficients = [
        sum(p[j] * comb(j, k) * a ** (j - k) * (b - a) ** k
            for j in range(k, 4))
        for k in range(4)
    ]
    return [sum(coefficients[k] * F(comb(i, k), comb(3, k))
                for k in range(i + 1)) for i in range(4)]


def dyadic_log(p, q, bits=128, terms=64):
    """Floor each term for log((q+p)/(q-p)); check the scaled tail."""
    require(0 < p < q, "valid logarithm series argument")
    scaled_two = 2 ** (bits + 1)
    pn, qn = p, q
    total = 0
    for j in range(terms):
        total += scaled_two * pn // ((2 * j + 1) * qn)
        pn *= p * p
        qn *= q * q
    require(scaled_two * p ** (2 * terms + 1)
            < (2 * terms + 1) * (q * q - p * p) * q ** (2 * terms - 1),
            "scaled logarithm tail below one")
    return total


def check_constants():
    square = [1500625, -2450, 1, 0]
    numerator = [0, 1225, -74, 1]
    inputs = [
        ([159 * x - 40000 * y for x, y in zip(square, numerator)],
         [F(x, 64) for x in [0, 400, 600, 650, 675, 700, 800, 1600]]),
        ([389 * x + 100000 * y for x, y in zip(square, numerator)],
         [F(x, 2) for x in [50, 74, 77, 80, 86, 98]]),
        ([100000 * y - 397 * x for x, y in zip(square, numerator)],
         [F(4225, 400), F(4356, 400)]),
    ]
    for p, endpoints in inputs:
        for a, b in zip(endpoints, endpoints[1:]):
            require(a < b and min(bernstein(p, a, b)) > 0,
                    "strictly positive cubic Bernstein coefficients")
    require(6 * 24500 * 389 ** 300 < 588 * 397 ** 300,
            "tail integral is less than one sixth of the first")

    p = [1]
    for factor in [[-1, 1], [-1, 1], [-3, 2], [-2, 3], [-4, 3], [-3, 4]]:
        p = multiply(p, factor)
    require(p == POLYNOMIAL and p == p[::-1], "reciprocal numerator")
    c = [1]
    for factor in [[-2, 1], [-2, 1], [-5, 2], [-5, 3], [-7, 3], [-7, 4]]:
        c = multiply(c, factor)
    require(c == CENTERED, "numerator at the other pole")
    for prime, e, v in [(2, 2, 3), (2, 1, 2), (3, 1, 2)]:
        require(all(prime ** (e * j) * a % prime ** v == 0
                    for j, a in enumerate(p)), "origin seed divisibility")
    for prime in [2, 5, 7]:
        require(all(prime ** j * a % prime ** 2 == 0
                    for j, a in enumerate(c)), "other-pole seed divisibility")
    g2 = sum(p[j] * (-1) ** j * (3 - j) for j in range(3))
    require(g2 == 2269, "positive-series coefficient of degree two")
    r = F(5, 19)
    coefficient_bound = ((1 + r) ** 2 * (6 + 13*r + 6*r*r)
                         * (12 + 25*r + 12*r*r) / (1-r)**2 / r**2)
    require(coefficient_bound == F(73122192, 9025) < 8103,
            "uniform logarithm-coefficient bound")

    scale = 2 ** 128
    two = dyadic_log(1, 3)
    a = dyadic_log(4007, 12199)  # log(8103/4096)
    b = dyadic_log(307, 943)    # log(625/318)
    c = dyadic_log(1, 9)        # log(5/4)
    sigma_upper = 250 * (13 * (two + 65) + a + 65) + 509 * scale
    tau_lower = 250 * (6 * two + b) - 509 * scale
    tau_upper = 250 * (6 * (two + 65) + b + 65) - 509 * scale
    require(0 < tau_lower and tau_upper < 700 * scale, "zero < tau < 14/5")
    require(sigma_upper < 3000 * scale, "sigma < twelve")
    require(125 * sigma_upper < 524 * tau_lower, "sigma/tau < 524/125")
    require(two + 65 < scale, "log two < one")
    require(scale < 2 * two, "log two > one half")
    require(4 * (3 * two + c) > 9 * scale, "log ten > 9/4")
    require(14262 < 180 * 80 and 101624000 + 14262 < 101800000,
            "prime-estimate constants")
    require(80**2 == 6400 and 4000 * 9 == 4 * 9000 and 14 * 3200 < 5 * 9000,
            "least even approximation index is above 3200")
    require(6524 < 9000, "N^(-21/5) absorbs the fixed constant")
    require(19 * 26 == 500 - 6, "strict catalog exponent gap")
    require(2304 * 12000 < 2 ** 121 and 121 * 250 < 3 * 12000
            and 500 < 3 * 12000,
            "catalog cutoff and positive logarithmic derivative")
    require(10**4000 < 2**16384, "explicit height cutoff precedes density cutoff")
    return {"bernstein_intervals": 13, "logarithm_bits": 128,
            "logarithm_terms": 64, "seed_divisibilities": 6,
            "coefficient_bound": "73122192/9025 < 8103"}


def check_small_indices():
    """Sanity checks only; the all-index proof is in the written note."""
    for n in range(1, 17):
        p, c = power(POLYNOMIAL, n), power(CENTERED, n)
        a = [sum(p[i] * (-1)**(j-i) * comb(2*n+j-i-1, j-i)
                 for i in range(j+1)) for j in range(2*n+1)]
        b = [-sum(c[i] * comb(2*n+j-i, j-i) for i in range(j+1))
             for j in range(2*n)]
        require(b[-1] == 0, "zero logarithmic residue at minus one")
        common = [comb(2*n, i) for i in range(2*n+1)]
        reconstructed = multiply(a, common)
        polynomial_part = multiply([0]*(2*n+1) + common, list(reversed(a[:-1])))
        reconstructed += [0] * (len(polynomial_part) - len(reconstructed))
        reconstructed = [x+y for x, y in zip(reconstructed, polynomial_part)]
        for j, bj in enumerate(b):
            for i in range(j+1):
                reconstructed[2*n+1+i] += bj * comb(j, i)
        require(reconstructed == p, "complete partial-fraction identity")
        for prime, e, v in [(2, 2, 3), (2, 1, 2), (3, 1, 2)]:
            require(all(prime ** (e*j) * x % prime ** (n*v) == 0
                        for j, x in enumerate(a)), "weighted origin coefficients")
        for prime in [2, 5, 7]:
            require(all(prime ** j * x % prime ** (2*n) == 0
                        for j, x in enumerate(b)), "weighted other-pole coefficients")

        def rational_part(z):
            first = sum((F(a[j], 2*n-j) * (z**(2*n-j) - z**(j-2*n))
                         for j in range(2*n)), F(0))
            second = sum((F(b[j], j-2*n+1)
                          * ((z+1)**(j-2*n+1) - F(2)**(j-2*n+1))
                          for j in range(2*n-1)), F(0))
            return first + second

        q = 2**n * lcm(*range(1, 2*n+1))
        require(all((q*rational_part(z)).denominator == 1
                    for z in [F(4, 3), F(3, 2)]), "endpoint denominator clearance")
    return {"first_index": 1, "last_index": 16,
            "scope": "Finite sanity checks; not the all-index integrality proof."}


def candidate_window(start):
    """Repair a logarithmic estimate; acceptance never trusts the estimate."""
    bits = start.bit_length()
    m = max(0, 80 * (bits - bits.bit_length() - 5) // 21)
    while m and catalog(m) >= start:
        m -= 1
    while catalog(m + 1) < start:
        m += 1
    return m


def extended_cover():
    bits, terms, first, stop = 32768, 16384, 2**21, 10**4000+1
    two, three = dyadic_log(1, 3, bits, terms), dyadic_log(1, 2, bits, terms)
    lower, upper = F(two, three+terms+1), F(two+terms+1, three)
    require(0 < lower < upper, "positive ordered ratio enclosure")
    # Reciprocal subtraction preserves reducedness, so repeated Fraction
    # normalization is unnecessary. The proposed brackets are still checked
    # independently below. Integer arithmetic keeps this replay practical.
    ln, ld, un, ud = lower.numerator, lower.denominator, upper.numerator, upper.denominator
    coefficients = []
    while True:
        q = ln // ld
        if q != un // ud:
            break
        coefficients.append(q)
        require(ln > q*ld and un > q*ud, "positive continued-fraction remainders")
        ln, ld, un, ud = ud, un-q*ud, ld, ln-q*ld
        require(len(coefficients) <= 20000, "continued-fraction work bound")
    require(coefficients[0] == 0, "first continued-fraction coefficient")
    a, b, c, d = 0, 1, 1, 0
    start, rows, skipped = first, 0, 0
    minimum_margin, first_window, last_window = None, None, None
    for index, q in enumerate(coefficients[1:]):
        if index % 2 == 0:
            c, d = c+q*a, d+q*b
        else:
            a, b = a+q*c, b+q*d
        end = min(stop, b+d)
        if end <= start:
            skipped += 1
            continue
        m = candidate_window(start)
        require(catalog(m) < start and b > 0 and d > 0, "admissible catalog")
        require(b*c == a*d+1, "Farey determinant")
        require(upper.numerator*d < c*upper.denominator, "upper enclosure")
        gap = lower.numerator*b-a*lower.denominator
        require(gap > 0, "positive lower separation")
        margin = (gap*2**m, 4*lower.denominator*b)
        require(margin[0] > margin[1] and start < end <= b+d,
                "excluded denominator interval")
        if first_window is None:
            first_window = m
        last_window = m
        if minimum_margin is None or margin[0]*minimum_margin[1] < minimum_margin[0]*margin[1]:
            minimum_margin = margin
        rows += 1
        start = end
        if start == stop:
            break
    require(start == stop, "complete extended cover")
    return {"first": "2^21", "last_inclusive": "10^4000", "dyadic_bits": bits,
            "series_terms": terms, "common_cf_terms": len(coefficients),
            "terms_consumed": index+2, "accepted_rows": rows, "skipped": skipped,
            "first_window": first_window, "last_window": last_window,
            "minimum_gap_margin_floor": minimum_margin[0] // minimum_margin[1]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cover", action="store_true", help="also replay the cover to 10^4000")
    args = parser.parse_args()
    tick = monotonic()
    result = {"constants": check_constants(), "small_index_sanity": check_small_indices()}
    if args.cover:
        result["extended_cover"] = extended_cover()
    result.update(all_exact_checks_passed=True, seconds=monotonic()-tick,
                  scope="Finite exact arithmetic; the all-index integral and cycle arguments are written.")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
