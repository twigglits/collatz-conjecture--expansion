"""Exact coalescence certificates and finite replay of the horizon obstruction.

The all-horizon obstruction is kernel proved in lean/CoalescenceDescent.lean
and explained in APERIODIC-ATTEMPT.md. This script independently tests its
arithmetic; finite replay is not its proof. Lean also proves certificate
soundness and the complete depth-eight table.
"""

import json
from fractions import Fraction


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def orbit(n, t):
    weight = 0
    for _ in range(t):
        weight += n % 2
        n = step(n)
    return n, weight


def coverage(k):
    """Pair equal-weight, equal-time images in one binary residue block."""
    modulus = 1 << k
    tables = [{} for _ in range(k + 1)]
    direct_count = merge_count = covered_count = lift_checks = 0
    residuals, extra, certificates = [], [], []
    for r in range(modulus):
        x, weight = r, 0
        direct = merge = False
        selected = None
        for t in range(1, k + 1):
            weight += x % 2
            x = step(x)
            coefficient = 3**weight * 2 ** (k - t)
            q0 = int(r <= 1)
            descends = (coefficient <= modulus and
                        coefficient * q0 + x < modulus * q0 + r)
            previous = tables[t].setdefault((weight, x), r)
            merges = 0 < previous < r
            direct |= descends
            merge |= merges
            if selected is None and (descends or merges):
                selected = (r, t, not descends, previous if not descends else 0)
        direct_count += direct
        merge_count += merge
        covered_count += direct or merge
        if not (direct or merge):
            residuals.append(r)
        if merge and not direct:
            extra.append(r)
        if k == 8 and selected is not None:
            certificates.append(selected)
            _, t, is_merge, target = selected
            base_image, base_weight = orbit(r, t)
            for q in (0, 1, 2, 17, 2**80 + 7):
                n = modulus * q + r
                if n <= 1:
                    continue
                actual, actual_weight = orbit(n, t)
                assert actual_weight == base_weight
                assert actual == 3**base_weight * 2 ** (k - t) * q + base_image
                if is_merge:
                    m = modulus * q + target
                    assert 0 < m < n and orbit(m, t)[0] == actual
                else:
                    assert 0 < actual < n
                lift_checks += 1
    row = dict(depth=k, total=modulus, direct=direct_count,
               merging=merge_count, covered=covered_count,
               additional=covered_count-direct_count,
               remaining=modulus-covered_count)
    if k == 8:
        row.update(residuals=residuals, additional_residues=extra,
                   certificates=certificates, exact_lift_checks=lift_checks)
        assert direct_count == 237 and covered_count == 240
        assert extra == [63, 207, 223]
        assert residuals == [27, 31, 47, 71, 91, 103, 111, 127,
                             155, 159, 167, 191, 231, 239, 251, 255]
    return row


def horizon_case(k):
    """Enumerate every inverse branch through depth k at each forward image."""
    modulus, power3 = 2**k, 3**k
    n = power3 * (-pow(power3, -1, modulus) % modulus)
    assert n > 1 and n % power3 == 0 and (n + 1) % modulus == 0
    x = n
    nodes = shifted_checks = 0
    for a in range(k + 1):
        assert 2**a * (x + 1) == 3**a * (n + 1)
        # j records the number of odd steps in the inverse-selected word.
        current = {(x, 0)}
        for b in range(k + 1):
            for m, j in current:
                nodes += 1
                assert m >= n
                assert orbit(m, b) == (x, j)
                if b > a:
                    c = b - a
                    slope = Fraction(2**c * 3**a, 3**j)
                    shifted = m - slope * n
                    assert shifted.denominator == 1
                    shifted = int(shifted)
                    assert (m - shifted) % 2**c == 0
                    assert 0 <= shifted <= slope - 1
                    assert orbit(shifted, c)[0] >= 0
                    shifted_checks += 1
            if b < k:
                following = set()
                for m, j in current:
                    following.add((2*m, j))
                    if m % 3 == 2:
                        following.add(((2*m-1)//3, j+1))
                current = following
        x = step(x)
    return dict(horizon=k, start=n, inverse_nodes=nodes,
                shifted_start_checks=shifted_checks,
                smaller_coalescing_starts=0)


def main():
    result = dict(
        coverage=[coverage(k) for k in (8, 12, 16, 18)],
        horizons=[horizon_case(k) for k in range(1, 25)],
        all_checks_passed=True,
        scope="Finite exact replay. No universal convergence or divergence conclusion.",
    )
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
