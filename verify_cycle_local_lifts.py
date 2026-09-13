#!/usr/bin/env python3
"""Finite exact corroboration of CycleLocalLifts.lean.

Every lifted edge is tested with the actual accelerated integer map, including
its exact valuation. A closed residue walk is not counted as an integer cycle.
The arbitrary-word and arbitrary-precision statements are kernel theorems.
"""

from itertools import product
from math import gcd
import json
from time import monotonic


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def numerator(word: list[int]) -> int:
    total, prefix_power = 0, 1
    for h in word:
        total = 3 * total + prefix_power
        prefix_power <<= h
    return total


def accelerated(x: int) -> tuple[int, int]:
    n = 3 * x + 1
    h = (n & -n).bit_length() - 1
    return n >> h, h


def check_word(word: list[int], a: int, b: int) -> dict:
    k, total = len(word), sum(word)
    denominator = 2**total - 3**k
    require(k > 0 and min(word) > 0 and denominator > 0, "theorem hypotheses")
    require(a > 0 and b >= 0, "precision hypotheses")
    modulus = 2**a * 3**b
    precision = 2**total * modulus
    require(gcd(denominator, precision) == 1, "invertible denominator")
    inverse = pow(denominator, -1, precision)
    require(denominator * inverse % precision == 1, "checked modular inverse")

    first = numerator(word)
    weights = [first]
    current = first
    for h in word:
        scaled = 3 * current + denominator
        require(scaled % 2**h == 0, "cyclic numerator identity")
        current = scaled // 2**h
        weights.append(current)
    require(current == first and all(w % 2 for w in weights), "odd numerator closure")
    lifts = [(w * inverse) % precision for w in weights]
    require(lifts[-1] == lifts[0], "closure of the lifted representatives")
    require(all(0 < x < precision and x % 2 for x in lifts), "positive odd lifts")
    all_integer_edges_equal = True
    for i, h in enumerate(word):
        x, y = lifts[i], lifts[i + 1]
        actual, valuation = accelerated(x)
        require(valuation == h, "exact halving at the actual integer witness")
        require(actual % modulus == y % modulus, "successor after precision loss")
        require(denominator * x % precision == weights[i] % precision, "lift equation")
        all_integer_edges_equal &= actual == y
    integral = first % denominator == 0
    if not integral:
        require(not all_integer_edges_equal, "nonintegral word must not yield an integer cycle")
    return {
        "odd_count": k,
        "halving_sum": total,
        "two_precision": a,
        "three_precision": b,
        "integral_rational_value": integral,
        "integer_edges_close": all_integer_edges_equal,
    }


def masked_word(k: int, total: int, mode: int) -> list[int]:
    base = [(i + 1) * total // k - i * total // k for i in range(k)]
    layers = [
        int(
            i > 0
            and base[(i - 1) % k] == 2
            and base[i] == 1
            and (i % 7 < 3 if mode == 0 else (i * total % k) * 5 < k)
        )
        for i in range(k)
    ]
    return [base[i] + layers[i] - layers[(i + 1) % k] for i in range(k)]


def replay() -> dict:
    started = monotonic()
    precisions = [(1, 0), (6, 0), (12, 4), (64, 16)]
    words = systems = edges = nonintegral = 0
    for length in range(1, 8):
        for digits in product((1, 2, 3), repeat=length):
            word = list(digits)
            if 2**sum(word) <= 3**length:
                continue
            words += 1
            if numerator(word) % (2**sum(word) - 3**length):
                nonintegral += 1
            for a, b in precisions:
                check_word(word, a, b)
                systems += 1
                edges += length

    masks = []
    for k, total in [(193, 306), (2966, 4701)]:
        for mode in range(2):
            report = check_word(masked_word(k, total, mode), 128, 32)
            report["selection_mode"] = mode
            masks.append(report)

    witnesses = [107, 161, 57]
    graph = []
    for i, x in enumerate(witnesses):
        y, h = accelerated(x)
        target = witnesses[(i + 1) % len(witnesses)] % 64
        require(y % 64 == target, "concrete closed residue walk")
        graph.append({
            "integer_witness": x,
            "source_residue": x % 64,
            "actual_successor": y,
            "target_residue": target,
            "exact_halving": h,
        })
    require(len({row["source_residue"] for row in graph}) == 3, "distinct graph vertices")
    require(all(row["source_residue"] != 1 for row in graph), "no residue-one vertex")
    require(accelerated(57)[0] != 107, "graph witnesses do not close as integers")

    external_word = [1, 2, 2, 2, 2, 1, 2, 2]
    require(
        all(
            external_word != external_word[:d] * (8 // d)
            for d in (1, 2, 4)
        ),
        "primitive external size-counterexample word",
    )
    external_w = numerator(external_word)
    external_d = 2**sum(external_word) - 3**len(external_word)
    require(external_w == 23413 and external_d == 9823, "external example values")
    require(2**14 >= 2 * 3**8 and external_w - external_d > external_d, "failed size claim")

    return {
        "all_exact_checks_passed": True,
        "small_word_alphabet": [1, 2, 3],
        "small_word_lengths": [1, 7],
        "positive_denominator_words": words,
        "nonintegral_words": nonintegral,
        "precision_pairs": precisions,
        "small_lift_systems_checked": systems,
        "small_actual_edges_checked": edges,
        "larger_mask_checks": masks,
        "graph_mod64": graph,
        "external_size_counterexample": {
            "word": external_word, "W": external_w, "D": external_d,
            "W_minus_D": external_w - external_d,
            "is_collatz_counterexample": False,
        },
        "seconds": monotonic() - started,
        "scope": (
            "Finite exact corroboration. The generic local-lift and bounded-lift "
            "theorems are kernel checked separately. Residue walks are not "
            "asserted to be integer Collatz cycles."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))
