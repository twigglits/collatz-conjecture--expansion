"""Independent exact replay of the universal, separately kernel-proved envelope."""
import json
from fractions import Fraction


def step(n):
    return (3*n+1)//2 if n % 2 else n//2


def case(k):
    p, q = 2**k, 3**k
    n = q * (-pow(q, -1, p) % p)
    assert (n+1) % p == 0 and n % q == 0
    x = n
    checks = strict_positive_offset = zero_offset = upper_boundary = 0
    for a in range(k+1):
        assert 2**a * (x+1) == 3**a * (n+1)
        current = {(x, 0)}
        for b in range(k+1):
            for m, j in current:
                A, B = 2**a * 3**j, 2**b * 3**a
                assert B*n <= A*m and A*(m+1) <= B*(n+1)
                slope = Fraction(B, A)
                offset = m - slope*n
                assert slope >= 1 and 0 <= offset <= slope-1
                strict_positive_offset += offset > 0
                zero_offset += offset == 0
                upper_boundary += offset == slope-1
                checks += 1
            if b < k:
                following = set()
                for m, j in current:
                    following.add((2*m, j))
                    if m % 3 == 2:
                        following.add(((2*m-1)//3, j+1))
                current = following
        x = step(x)
    return dict(horizon=k, start=n, checks=checks,
                positive_offset_checks=strict_positive_offset,
                zero_offset_checks=zero_offset,
                upper_boundary_checks=upper_boundary)


if __name__ == '__main__':
    cases = [case(k) for k in range(1, 25)]
    total = sum(row['checks'] for row in cases)
    assert total == 716286
    print(json.dumps(dict(cases=cases, total_checks=total,
                          all_checks_passed=True,
                          scope='Finite exact arithmetic replay; universal claims are in the Lean module.'),
                     indent=2))
