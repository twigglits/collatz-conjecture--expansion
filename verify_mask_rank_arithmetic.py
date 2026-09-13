#!/usr/bin/env python3
"""Exact finite replay of the mechanical-rank congruence.

The general modular algebra is proved in Lean. Mechanical floor identities,
reindexing, and bounded-modulus coverage have written proofs in the note;
this script independently checks finite instances, not those universal claims.
"""

from itertools import product
from math import gcd
from time import monotonic
import json


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def numerator(word: list[int]) -> int:
    value, power = 0, 1
    for h in word:
        value = 3 * value + power
        power <<= h
    return value


def rank_data(k: int, total: int) -> dict:
    require(k > 1 and 3 * k <= 2 * total < 4 * k, "mechanical count range")
    require(gcd(k, total) == 1, "coprime count hypothesis")
    denominator = 2**total - 3**k
    require(denominator > 1, "positive nontrivial denominator")
    lower = [(i + 1) * total // k - i * total // k for i in range(k)]
    base = lower[1:] + lower[:1]
    require(base[0] == 2 and base[-1] == 1, "common cut after lower symbol zero")
    count = 2 * k - total
    prefix = 0
    entries = {}
    three = 3 ** (k - 1)
    for i, h in enumerate(base):
        rank = (i + 1) * total % k
        require(k * prefix + rank + k == total * (i + 1), "exact floor phase")
        require((h == 1) == (rank < count), "eligible rank interval")
        if h == 1:
            require(i > 0 and base[i - 1] == 2 and prefix > 0, "disjoint eligible pair")
            coefficient = three * 2 ** (prefix - 1)
            require(
                total * (k - 1 - i) + k * (prefix - 1) + rank == k * (total - 2),
                "rank exponent identity",
            )
            entries[rank] = (i, coefficient)
        prefix += h
        three //= 3
    require(sorted(entries) == list(range(count)), "rank permutation is complete")
    q = pow(total, -1, k)
    t = (q * total - 1) // k
    require(q * total == k * t + 1, "Bezout determinant")
    z = pow(2, t, denominator) * pow(pow(3, q, denominator), -1, denominator) % denominator
    require(2 * pow(z, k, denominator) % denominator == 1, "first count root")
    require(3 * pow(z, total, denominator) % denominator == 1, "second count root")
    require(4 * pow(z, count, denominator) % denominator == 3 % denominator, "interval root")
    kappa = 2 ** (total - 2)
    require(entries[0][1] == kappa, "explicit rank-zero coefficient")
    powers = []
    power = 1
    for rank in range(count):
        powers.append(power)
        require(entries[rank][1] % denominator == kappa * power % denominator, "rank coefficient")
        power = power * z % denominator
    geometric = sum(powers) % denominator
    require(4 * (1 - z) * geometric % denominator == 1, "geometric inverse")
    coefficients = sum(c for _, c in entries.values())
    require(coefficients % denominator == kappa * geometric % denominator, "coefficient sum")
    require(gcd(coefficients, denominator) == 1, "total coefficient is a unit")
    weight = numerator(base)
    require(weight == denominator + 4 * coefficients, "old normal form agrees")
    return {
        "k": k, "total": total, "s": count, "D": denominator, "z": z,
        "base": base, "entries": entries, "powers": powers, "C": coefficients,
        "kappa": kappa, "W": weight,
    }


def check_mask(data: dict, bits: tuple[bool, ...]) -> bool:
    require(len(bits) == data["s"], "mask length")
    word = data["base"].copy()
    selected = polynomial = 0
    digit_polynomial = 0
    for rank, chosen in enumerate(bits):
        i, coefficient = data["entries"][rank]
        digit_polynomial += (3 if chosen else 4) * data["powers"][rank]
        if chosen:
            word[i - 1], word[i] = 1, 2
            selected += coefficient
            polynomial += data["powers"][rank]
    denominator = data["D"]
    weight = numerator(word)
    require(weight + selected == data["W"], "independent edited numerator")
    require(weight == denominator + 4 * data["C"] - selected, "integer mask equation")
    require(selected % denominator == data["kappa"] * polynomial % denominator, "selected rank sum")
    integral = weight % denominator == 0
    require(integral == (digit_polynomial % denominator == 0), "digit equation equivalence")
    require(
        integral == ((1 - data["z"]) * polynomial % denominator == 1),
        "normalized target-one equivalence",
    )
    return integral


def bounded_modulus_checks() -> dict:
    sequences = stages = 0
    for modulus in range(2, 81):
        units = [a for a in range(1, modulus) if gcd(a, modulus) == 1]
        for mode in range(3):
            reachable = {0}
            for index in range(modulus - 1):
                a = units[(index * index + 7 * mode * index + mode) % len(units)]
                next_reachable = reachable | {(x + a) % modulus for x in reachable}
                require(
                    len(next_reachable) >= min(modulus, len(reachable) + 1),
                    "unit translation grows every proper subset",
                )
                reachable = next_reachable
                stages += 1
            require(len(reachable) == modulus, "M-1 unit coefficients cover Z/M")
            sequences += 1
        require(set(range(modulus - 1)) != set(range(modulus)), "one fewer coefficient can miss target")
    return {"moduli": [2, 80], "unit_sequences": sequences, "growth_stages": stages}


def replay() -> dict:
    started = monotonic()
    all_pairs = critical_pairs = rank_coefficients = mask_checks = 0
    # Cover noncritical slopes as well: no logarithm assumption is used by
    # the rank arithmetic, only this exact count interval and D>0.
    for k in range(2, 81):
        for total in range((3 * k + 1) // 2, 2 * k):
            if gcd(k, total) != 1 or 2**total <= 3**k:
                continue
            data = rank_data(k, total)
            all_pairs += 1
            rank_coefficients += data["s"]
            for mode in range(4):
                bits = tuple(
                    False if mode == 0 else True if mode == 1 else
                    j % 2 == 0 if mode == 2 else (j * j + 3 * j + k) % 7 < 3
                    for j in range(data["s"])
                )
                require(not check_mask(data, bits), "finite selected mask is nonintegral")
                mask_checks += 1

    exhaustive_masks = 0
    exhaustive_pairs = []
    for k in range(2, 513):
        total = (3**k).bit_length()
        if gcd(k, total) != 1:
            continue
        data = rank_data(k, total)
        critical_pairs += 1
        rank_coefficients += data["s"]
        if k <= 36:
            for bits in product((False, True), repeat=data["s"]):
                require(not check_mask(data, bits), "finite exhaustive mask is nonintegral")
                exhaustive_masks += 1
            exhaustive_pairs.append([k, total])

    repeated_checks = 0
    for k in range(2, 201):
        total = (3**k).bit_length()
        g = gcd(k, total)
        lower = [(i + 1) * total // k - i * total // k for i in range(k)]
        base = lower[1:] + lower[:1]
        denominator = 2**total - 3**k
        primitive_denominator = 2 ** (total // g) - 3 ** (k // g)
        weight = numerator(base)
        require((weight - denominator) % 4 == 0, "repeated coefficient sum")
        coefficients = (weight - denominator) // 4
        require(gcd(weight, denominator) == denominator // primitive_denominator, "mechanical numerator gcd")
        require(gcd(coefficients, denominator) == denominator // primitive_denominator, "repeated coefficient gcd")
        repeated_checks += 1

    larger = []
    for k, total in [(193, 306), (2966, 4701)]:
        data = rank_data(k, total)
        for mode in range(4):
            bits = tuple((j * (mode + 1) + j * j + mode) % 11 < 3 + mode for j in range(data["s"]))
            require(not check_mask(data, bits), "larger finite mask is nonintegral")
            mask_checks += 1
        larger.append({"k": k, "N": total, "s": data["s"], "selected_masks_checked": 4})

    data = rank_data(11, 18)
    bits = (False, True, False, True)
    require(not check_mask(data, bits), "small-prime witness fails full divisibility")
    word = data["base"].copy()
    for j, b in enumerate(bits):
        if b:
            i = data["entries"][j][0]
            word[i - 1], word[i] = 1, 2
    weight = numerator(word)
    require(data["D"] % 11 == 0 and data["z"] % 11 == 6 and weight % 11 == 0, "small prime passes")
    order = next(d for d in range(1, 11) if pow(6, d, 11) == 1)
    require(order == 10 and 4 + 3 * 6 + 4 * 6**2 + 3 * 6**3 == 814, "short polynomial arithmetic")

    return {
        "all_exact_checks_passed": True,
        "noncritical_and_critical_count_pairs_k_through_80": all_pairs,
        "critical_count_pairs_k_through_512": critical_pairs,
        "individual_rank_coefficients_checked_in_those_ranges": rank_coefficients,
        "exhaustive_critical_pairs_k_through_36": exhaustive_pairs,
        "exhaustive_masks_rejected": exhaustive_masks,
        "additional_selected_masks_rejected": mask_checks,
        "mechanical_gcd_checks_k_through_200": repeated_checks,
        "larger_counts": larger,
        "small_prime_limitation": {
            "k": 11, "N": 18, "D": data["D"], "modulus": 11,
            "z_mod_11": 6, "order_mod_11": order,
            "rank_selection": list(bits), "word": word, "W": weight,
            "W_mod_11": weight % 11, "W_mod_D": weight % data["D"],
            "digit_polynomial_at_6": 814, "polynomial_degree": 3,
        },
        "bounded_modulus_coverage": bounded_modulus_checks(),
        "seconds": monotonic() - started,
        "scope": (
            "Finite exact corroboration. The modular implications and exponent "
            "bridge are kernel checked separately. Full mechanical reindexing, "
            "the repeated-word gcd corollary, and bounded-modulus coverage are "
            "written arguments. No unrestricted all-period mask exclusion follows."
        ),
    }


if __name__ == "__main__":
    print(json.dumps(replay(), indent=2))
