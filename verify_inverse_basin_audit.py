"""Exact replay of basin collisions and version-specific congruence examples.

The universal basin and chain statements are kernel proved separately.
No external density bound is used as an input.
"""
import itertools
import json


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def orbit(n, k):
    for _ in range(k):
        n = step(n)
    return n


def collision(a):
    q, r = divmod(a, 3)
    assert r in (1, 2)
    if r == 1:
        u, v, t = 12 * q + 4, 4 * q + 1, 2
    else:
        u, v, t = 6 * q + 4, 2 * q + 1, 1
    assert u > 0 and v > 0 and u != v
    assert step(u) == step(v)
    assert orbit(u, t) == orbit(v, t) == a
    return dict(root=a, first=u, second=v, common_image=step(u), steps_to_root=t)


def verify():
    checked = 0
    for a in range(1, 32769):
        if a % 3:
            collision(a)
            checked += 1
    large = [collision(3**k + offset) for k in (32, 128, 512)
             for offset in (-1, 1)]
    dyadic_checks = 0
    for a in (3, 6, 9, 81, 3 * 2**128):
        for k in range(65):
            n = 2**k * a
            assert orbit(n, k) == a and n % 3 == 0
            assert step(2 * n) == n
            dyadic_checks += 1
    v1 = []
    for a, b in itertools.product((5, 6), (1, 2)):
        assert (a + 1) // 2 == 3 and (b + 1) // 2 == 1
        left, right = pow(2, a + b, 9), (2**b + 3) % 9
        assert left != right
        v1.append(dict(v1=a, v2=b, lhs_mod9=left, rhs_mod9=right))
    # The first v1 inverse step at exponent six is 21, a multiple of three.
    assert (2**6 - 1) // 3 == 21
    assert all((2**k * 21 - 1) % 3 == 2 for k in range(1, 129))
    v2 = []
    for v in (8, 10):
        assert (v + 1) // 6 == 2 - 1
        assert pow(2, v, 3) == 1 and pow(2, v, 9) != 1
        n = (2**v - 1) // 3
        assert n % 3 != 0 and 3 * n + 1 == 2**v
        v2.append(dict(u1=2, v1=v, resulting_odd_start=n,
                       pow2_mod3=pow(2, v, 3), pow2_mod9=pow(2, v, 9)))
    return dict(all_checks_passed=True, small_root_collisions=checked,
                large_root_collisions=large, dyadic_basin_checks=dyadic_checks, v1_no_solution=v1,
                v2_two_solutions=v2,
                sources=[
                    'https://arxiv.org/html/2512.13760v1#S2',
                    'https://arxiv.org/html/2512.13760v2#S3',
                    'https://arxiv.org/pdf/math/0205002'],
                scope='Finite arithmetic replay; universal basin statements are separately kernel checked. Counterexamples address the stated lemmas, not the truth of the final density bounds. No Collatz proof.')


if __name__ == '__main__':
    print(json.dumps(verify(), indent=2))
