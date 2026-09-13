#!/usr/bin/env python3
"""Independent exact replay of the finite mask-resonance cover.

Prints a compact report; does not modify the repository. This corroborates
the finite arithmetic, not the written logarithm or mask-cycle arguments.
"""

from fractions import Fraction
import json
from time import monotonic


BITS = 8192
TERMS = 4096
FIRST = 2**21
STOP = 10**1000 + 1


def require(condition: bool, description: str) -> None:
    if not condition:
        raise ValueError(description)


def dyadic_log_floor(q: int) -> int:
    power = q
    total = 0
    scaled_two = 2 ** (BITS + 1)
    for j in range(TERMS):
        total += scaled_two // ((2 * j + 1) * power)
        power *= q * q
    require(
        scaled_two < (2 * TERMS + 1) * (q * q - 1) * q ** (2 * TERMS - 1),
        f"scaled series tail for q={q}",
    )
    return total


def catalog(m: int) -> int:
    return (m + 4) * 2 ** (21 * (m + 1) // 80 + 3)


def choose_window(start: int) -> int:
    # A descending search differs from the Lean generator's binary search.
    # Its result is checked directly, so optimality is not trusted.
    m = 4 * start.bit_length()
    while m and catalog(m) >= start:
        m -= 1
    return m


def replay() -> dict:
    tick = monotonic()
    log_two = dyadic_log_floor(3)
    log_three = dyadic_log_floor(2)
    require(log_two > 0 and log_three > 0, "positive logarithm floors")
    lower = Fraction(log_two, log_three + TERMS + 1)
    upper = Fraction(log_two + TERMS + 1, log_three)
    require(lower < upper, "ordered ratio enclosure")

    lo, hi = lower, upper
    coefficients = []
    while True:
        q = lo.numerator // lo.denominator
        if q != hi.numerator // hi.denominator:
            break
        coefficients.append(q)
        require(lo > q and hi > q, "nonzero continued-fraction remainders")
        lo, hi = 1 / (hi - q), 1 / (lo - q)
        require(len(coefficients) <= 5000, "continued-fraction generation limit")
    require(coefficients[0] == 0, "initial continued-fraction coefficient")

    a, b, c, d = 0, 1, 1, 0
    start = FIRST
    rows = 0
    skipped = 0
    first_window = None
    last_window = None
    smallest_margin = None
    for index, q in enumerate(coefficients[1:]):
        if index % 2 == 0:
            c, d = c + q * a, d + q * b
        else:
            a, b = a + q * c, b + q * d
        end = min(STOP, b + d)
        if end <= start:
            skipped += 1
            continue
        m = choose_window(start)
        require(catalog(m) < start, "catalog shorter than covered periods")
        require(b > 0 and d > 0, "positive Farey denominators")
        require(b * c == a * d + 1, "Farey determinant")
        require(upper.numerator * d < c * upper.denominator, "upper enclosure")
        gap = lower.numerator * b - a * lower.denominator
        require(gap > 0, "positive lower gap before subtraction")
        margin = Fraction(gap * 2**m, 4 * lower.denominator * b)
        require(margin > 1, "separation exceeds the cycle's allowed gap")
        require(start < end <= b + d, "nonempty covered interval")
        if first_window is None:
            first_window = m
        last_window = m
        if smallest_margin is None or margin < smallest_margin:
            smallest_margin = margin
        rows += 1
        start = end
        if start == STOP:
            break
    require(start == STOP, "complete denominator coverage through the endpoint")
    require(3**101 > 2**160, "catalog slope constant")
    require((32 * (3 * 64 + 7)) ** 80 < 2 ** (17 * 64), "cubic-bound base case")
    require(17**80 < 2**337, "cubic-bound induction constant")
    require(smallest_margin is not None, "nonempty cover")
    return {
        "all_exact_checks_passed": True,
        "denominator_interval": {"first": "2^21", "last_inclusive": "10^1000"},
        "dyadic_bits": BITS,
        "series_terms_per_logarithm": TERMS,
        "common_continued_fraction_terms": len(coefficients),
        "candidate_terms_consumed": index + 2,
        "accepted_cover_rows": rows,
        "skipped_initial_brackets": skipped,
        "first_window": first_window,
        "last_window": last_window,
        "minimum_gap_margin_floor": smallest_margin.numerator // smallest_margin.denominator,
        "seconds": monotonic() - tick,
        "scope": "Independent finite integer replay; real logarithm bounds and the application to all masks are written proofs.",
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))
