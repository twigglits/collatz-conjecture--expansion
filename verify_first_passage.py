"""Exact finite checks for the first-passage packing argument.

These check finite partitions and interval transport, not the external
ballot theorem or the analytic all-length induction.
"""
import json


def shortcut(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def survivors(length, slack):
    counts = [1]
    p3 = [3**j for j in range(length + 1)]
    for t in range(1, length + 1):
        new = [0] * (t + 1)
        for j in range(t + 1):
            if (p3[j] << slack) >= 1 << t:
                new[j] = (counts[j] if j < t else 0) + (counts[j - 1] if j else 0)
        counts = new
    return sum(counts)


def main():
    image_checks = 0
    partition_checks = 0
    for ell in range(2, 11):
        width = 1 << ell
        for q in (0, 7, 2**80 + 3):
            for b in range(1, ell):
                groups = {}
                survivors_seen = 0
                parity_codes = set()
                for n in range(q * width, (q + 1) * width):
                    x, j, first, code = n, 0, None, 0
                    for t in range(1, ell + 1):
                        bit = x % 2
                        code |= bit << (t - 1)
                        j += bit
                        x = shortcut(x)
                        size = (1 << (ell - t)) * 3**j
                        assert q * size <= x < (q + 1) * size
                        image_checks += 1
                        if first is None and (3**j << b) < 1 << t:
                            assert bit == 0
                            assert 1 << t <= (3**j << (b + 1))
                            assert size < 1 << (ell - b)
                            assert groups.setdefault(t, j) == j
                            first = t
                    parity_codes.add(code)
                    survivors_seen += first is None
                assert len(parity_codes) == width
                assert survivors_seen == survivors(ell, b)
                assert len(groups) <= ell
                partition_checks += 1
    rows = []
    for ell in (16, 32, 64, 128, 256, 512, 1024):
        # The data are exact counts at a fixed slack, not a fitted constant
        # for the all-index ballot estimate.
        count = survivors(ell, 4)
        rows.append({"length": ell, "slack": 4, "surviving_words": count})
    print(json.dumps({
        "all_checks_passed": True,
        "image_checks": image_checks,
        "partition_checks": partition_checks,
        "survivor_counts": rows,
        "scope": "Finite exact transport and word-count checks. No numerical claim about the unspecified universal constant.",
    }, indent=2))


if __name__ == "__main__":
    main()
