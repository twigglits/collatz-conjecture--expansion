#!/usr/bin/env python3
"""Exact arithmetic and finite sanity checks for the written mask-span proof.

This script does not modify the repository. The circle argument for arbitrary
slopes and phases and the all-period integer-cycle theorem are written proofs,
not conclusions inferred from the finite examples below.
"""

from fractions import Fraction
from math import gcd
import json
from time import monotonic


Q = 1054
P = 665
WIDTH = Fraction(185001, 10**6)
EPSILON = Fraction(1, 10**7)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def circle_maximum(slope: Fraction) -> int:
    """Maximum over all phases, at this one exact slope, in a Q-block."""
    points = sorted((j * slope) % 1 for j in range(Q))
    require(len(set(points)) == Q, "distinct points at the checked slope")
    doubled = points + [p + 1 for p in points]
    end = 0
    largest = 0
    for start in range(Q):
        end = max(end, start)
        while end < start + Q and doubled[end] - doubled[start] < WIDTH:
            end += 1
        largest = max(largest, end - start)
    return largest


def phase_patterns(slope: Fraction, length: int) -> int:
    """Check every boundary and intervening cell at one slope and length."""
    offsets = [(j * slope) % 1 for j in range(length)]
    boundaries = sorted(
        {(-p) % 1 for p in offsets}
        | {(1 - WIDTH - p) % 1 for p in offsets}
    )
    phases = list(boundaries)
    for index, left in enumerate(boundaries):
        right = boundaries[(index + 1) % len(boundaries)]
        if index + 1 == len(boundaries):
            right += 1
        phases.append(((left + right) / 2) % 1)
    patterns = {
        tuple((theta + p) % 1 >= 1 - WIDTH for p in offsets)
        for theta in phases
    }
    require(len(patterns) <= 2 * length, "two endpoints per phase coordinate")
    return len(patterns)


def rational_mask(k: int, n: int, omit_thirds: bool) -> dict:
    """A positive rational example below span 2.45; not an integer cycle."""
    base = [(i + 1) * n // k - i * n // k for i in range(k)]
    layers = [
        int(
            i > 0
            and base[(i - 1) % k] == 2
            and base[i] == 1
            and 50 * (i * n % k) <= 9 * n
            and (not omit_thirds or i % 3 != 0)
        )
        for i in range(k)
    ]
    actual = [
        base[i] + layers[i] - layers[(i + 1) % k]
        for i in range(k)
    ]
    require(all(h in (1, 2) for h in actual), "positive mask exponents")
    require(sum(actual) == n and gcd(k, n) == 1, "counts and primitivity")
    require(2 ** (n - 1) < 3**k < 2**n, "critical count pair")
    numerator, prefix_power = 0, 1
    for h in actual:
        numerator = 3 * numerator + prefix_power
        prefix_power <<= h
    denominator = 2**n - 3**k
    state = numerator
    states = []
    for h in actual:
        states.append(state)
        next_scaled = 3 * state + denominator
        require(next_scaled % (2**h) == 0, "exact cyclic numerator edge")
        state = next_scaled // (2**h)
    require(state == numerator, "rational cycle closure")
    require(min(states) == numerator, "minimum cut in the rational example")
    require(20 * max(states) < 49 * min(states), "rational span below 2.45")
    require(numerator % denominator != 0, "nonintegral rational example")

    folded = [(2 - layers[i]) * states[i] for i in range(k)]
    ranked = sorted(range(k), key=lambda i: i * n % k)
    require(
        all(folded[ranked[j]] < folded[ranked[j + 1]] for j in range(k - 1)),
        "folded rank order",
    )
    p3, p2 = 1, 1
    for i in range(k):
        require(
            p3 * folded[0] <= p2 * folded[i],
            "folded positive-forcing prefix",
        )
        if i:
            require(
                p3 * folded[0] < p2 * folded[i],
                "strict interior folded prefix",
            )
            require(
                ((i * n // k) * k) % n == n - i * n % k,
                "edit-boundary phase identity",
            )
        if layers[i]:
            require(
                Fraction(((i * n // k) * k) % n, n) >= 1 - WIDTH,
                "selected center in the allowed phase interval",
            )
        p3 *= 3
        p2 <<= base[i]
    return {
        "odd_count": k,
        "shortcut_count": n,
        "omitted_indices_divisible_by_three": omit_thirds,
        "selected_edits": sum(layers),
        "span_times_million_floor": 10**6 * max(states) // min(states),
        "nonintegral": True,
    }


def replay() -> dict:
    started = monotonic()
    require(49**200 < 40**200 * 3**37, "span logarithm comparison")
    require(3**15601 < 2**24727, "lower rotation-slope comparison")
    require(2**1054 < 3**665, "upper rotation-slope comparison")
    lower, grid = Fraction(15601, 24727), Fraction(P, Q)
    require(grid - lower == Fraction(1, Q * 24727), "Farey determinant")
    require(grid - lower + Fraction(1, 10**8) < EPSILON, "slope padding")
    require(gcd(P, Q) == 1, "permutation of the comparison grid")
    enlarged = WIDTH + 2 * Q * EPSILON
    require(enlarged < 1 and Q * enlarged < 196, "uniform grid arc cap")
    require(Fraction(196, Q) < Fraction(3, 16), "catalog exponent")
    require(72 * 12000**2 < 2**34, "polynomial cutoff")
    require(197 + 34 < 300 and 40 * 300 == 12000, "cutoff gap")
    require(2**12000 < 10**4000, "overlap with the finite cover")

    slopes = [grid - EPSILON * Fraction(j, 6) for j in range(7)]
    maxima = [circle_maximum(slope) for slope in slopes]
    require(all(count <= 196 for count in maxima), "finite circle-count sanity")
    lengths = [1, 2, 3, 17, 65]
    pattern_counts = [
        [phase_patterns(slope, length) for length in lengths]
        for slope in slopes
    ]
    examples = [
        rational_mask(k, n, sparse)
        for k, n in [(306, 485), (2966, 4701)]
        for sparse in (False, True)
    ]
    return {
        "all_exact_checks_passed": True,
        "grid_length": Q,
        "allowed_centers_per_grid_block": 196,
        "enlarged_arc_times_grid": str(Q * enlarged),
        "finite_slope_examples": len(slopes),
        "all_phase_maxima_at_these_slopes": maxima,
        "pattern_window_lengths": lengths,
        "all_boundary_and_cell_pattern_counts": pattern_counts,
        "rational_examples": examples,
        "seconds": monotonic() - started,
        "scope": (
            "Exact constants and finite sanity checks. The uniform circle "
            "argument, factor catalog, and all-period integer-cycle span "
            "theorem remain written proofs. Rational examples are nonintegral."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))
