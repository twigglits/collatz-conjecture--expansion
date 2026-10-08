"""Independent exact replay of the real/2-adic shadow separation example.

Finite tests only. Infinite deductions and their formal scope are recorded
in APERIODIC-ATTEMPT.md, Section 6.
"""
import json
from fractions import Fraction


def main():
    y = Fraction(2)
    partial = Fraction(0)
    a = 2
    ones = 0
    signed_sum_numerator = 0
    word = []
    samples = []
    for t in range(2000):
        bit = int(t == 0 or a < 2 ** (t + 1))
        assert bit == int(t == 0 or y < 2)
        word.append(bit)
        if bit:
            a = 3 * a - 2**t
            signed_sum_numerator = 3 * signed_sum_numerator - 2**t
            if t < 128:
                partial -= Fraction(2**t, 3 ** (ones + 1))
            ones += 1
        # Fraction replay uses a separate representation and branch update.
        if t < 128:
            y = (3 * y - 1) / 2 if bit else y / 2
        length = t + 1
        modulus = 2**length
        assert a % 2 == 1
        assert modulus <= a and 2 * a <= 5 * modulus
        assert 5**ones * a <= 2 * 13**ones
        assert signed_sum_numerator == a - 2 * 3**ones
        if t < 128:
            assert y == Fraction(a, modulus)
            assert partial == -2 + Fraction(a, 3**ones)
        else:
            # Only the short independent Fraction replay is needed; preserve
            # the current rational value for the next branch comparison.
            y = Fraction(a, modulus)
        if length in (64, 128, 512, 2000):
            residue = signed_sum_numerator * pow(3**ones, -1, modulus) % modulus
            assert residue % 2 == 1 and (-2) % 2 == 0
            if samples:
                old = samples[-1]
                assert residue % (2 ** old["length"]) == int(old["residue_hex"], 16)
            x = residue
            for expected in word:
                assert x % 2 == expected
                x = (3 * x + 1) // 2 if x % 2 else x // 2
            samples.append({
                "length": length, "ones": ones,
                "residue_hex": hex(residue),
                "real_error_numerator_bits": a.bit_length(),
                "real_error_denominator_bits": (3**ones).bit_length(),
            })
    print(json.dumps({
        "all_checks_passed": True,
        "steps": len(word), "ones": ones,
        "prefix": "".join(map(str, word[:100])),
        "samples": samples,
        "scope": "Exact finite shadow and parity-prefix checks; not an integer counterexample to Collatz.",
    }, indent=2))


if __name__ == "__main__":
    main()
