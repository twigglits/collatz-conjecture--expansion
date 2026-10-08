"""Exact finite replay for the coalescence height investigation.

The universal lower bound and the 27 example are kernel proved separately.
The search below supplies no universal upper bound.
"""
import json
from fractions import Fraction


def step(n):
    return (3*n+1)//2 if n % 2 else n//2


def finite_region():
    region = set()
    for n in range(1, 27):
        while n not in region:
            region.add(n)
            n = step(n)
    assert all(step(n) in region for n in region)
    path = []
    n = 27
    while n not in region:
        path.append(n)
        n = step(n)
    assert len(region) == 34 and len(path) == 59 and n == 23
    x, odd_count, first_drop = 27, 0, None
    for t in range(1, 60):
        odd_count += x % 2
        x = step(x)
        if 3**odd_count < 2**t and first_drop is None:
            first_drop = t
    assert first_drop == 59
    return dict(region=sorted(region), disjoint_prefix=path,
                first_meeting_forward_time=59, first_meeting_value=23,
                first_coefficient_drop=first_drop)


def crt_witnesses():
    rows = []
    for k in range(1, 257):
        p, q = 2**k, 3**k
        n = q * (-pow(q, -1, p) % p)
        assert q <= n < 6**k
        assert (n+1) % p == 0 and n % q == 0
        rows.append(dict(horizon=k, start=n))
    return rows


def exact_meeting_search(limit=32768, horizon=192):
    # At the start of n's iteration, each entry gives the shortest b from
    # ANY smaller positive start. Every such orbit was traversed through
    # horizon or until its first repeat. Later repeats cannot lower b.
    predecessors = {}
    maximum_ratio = Fraction(0)
    records = []
    unresolved = []
    improvement_count = 0
    for n in range(1, limit+1):
        path, seen, x = [], set(), n
        for _ in range(horizon+1):
            if x in seen:
                break
            seen.add(x)
            path.append(x)
            x = step(x)
        best = None
        for a, x in enumerate(path):
            if x in predecessors:
                b, m = predecessors[x]
                candidate = (max(a, b), a, b, m, x)
                if best is None or candidate < best:
                    best = candidate
        if n > 1:
            if best is None:
                unresolved.append(n)
            else:
                depth, a, b, m, x = best
                assert 0 < m < n and a <= depth and b <= depth
                direct = next((a for a, x in enumerate(path) if x < n), None)
                if direct is None or depth < direct:
                    improvement_count += 1
                digits = (n-1).bit_length()  # exactly ceil(log_2(n))
                ratio = Fraction(depth, digits)
                if ratio > maximum_ratio:
                    maximum_ratio = ratio
                    records.append(dict(start=n, minimum_horizon=depth,
                                        a=a, b=b, smaller_start=m, common_value=x,
                                        ceil_log2_start=digits,
                                        ratio_numerator=ratio.numerator,
                                        ratio_denominator=ratio.denominator))
        for b, x in enumerate(path):
            if x not in predecessors or b < predecessors[x][0]:
                predecessors[x] = (b, n)
    assert not unresolved
    assert maximum_ratio == Fraction(59, 5)
    return dict(limit=limit, search_horizon=horizon,
                exact_meeting_horizon_records=records,
                starts_with_earlier_meeting_than_descent=improvement_count,
                unresolved=unresolved,
                diagnostic_node_count=len(predecessors),
                scope="Exact minima of max(a,b) for these finite starts only; no universal upper bound.")


def main():
    print(json.dumps(dict(region27=finite_region(),
                          crt_witnesses=crt_witnesses(),
                          meeting_search=exact_meeting_search(),
                          all_checks_passed=True), indent=2))


if __name__ == '__main__':
    main()
