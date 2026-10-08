"""Exact finite replay of the tower-deposit obstruction; no floating point.

The all-index arithmetic is separately kernel proved in
lean/TowerDepositObstruction.lean. This replay checks its interpretation in
the actual odd Collatz map, including the first-return stopping rule.
"""
import json


def odd_step(n):
    assert n > 0 and n % 2 == 1
    value = 3 * n + 1
    deposit = (value & -value).bit_length() - 1
    return value >> deposit, deposit


def contracting_return(n, fuel):
    assert n % 4 == 1
    deposits = []
    for _ in range(fuel):
        n, deposit = odd_step(n)
        deposits.append(deposit)
        if n % 4 == 1:
            return n, deposits
    raise AssertionError("First-return replay exhausted its explicit bound")


def main():
    rows = []
    for s in range(1, 14):
        k = 2 ** (s + 1) + 1
        numerator = 2**k - 5
        assert numerator % 3 == 0
        seed = numerator // 3
        first, first_deposits = contracting_return(seed, k)
        assert first == 2 * 3 ** (k - 3) - 1
        assert first_deposits == [2] + [1] * (k - 3)
        second, second_deposits = contracting_return(first, 1)
        assert second == (3 ** (k - 2) - 1) // 2
        assert second_deposits == [2]
        _, next_deposit = odd_step(second)
        assert next_deposit == s + 2
        q, remainder = divmod(3 * second + 1, 2 ** (s + 2))
        assert remainder == 0 and q % 2 == 1
        rows.append({
            "s": s, "k": k, "seed_bits": seed.bit_length(),
            "first_return_odd_steps": len(first_deposits),
            "second_return_odd_steps": len(second_deposits),
            "next_deposit": next_deposit,
        })
    print(json.dumps({
        "all_checks_passed": True,
        "cases": rows,
        "scope": "Finite exact orbit replay; not a proof of convergence or divergence.",
    }, indent=2))


if __name__ == "__main__":
    main()
