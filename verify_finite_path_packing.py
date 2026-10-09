"""Exact replay of finite-path packing and first-entry transport.

The all-length entropy induction and infinite shell summation are written
arguments. This script checks the kernel lemmas and finite instances, not
universal entry or a vanishing weighted survivor mass.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import comb
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/finite-path-packing'


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def first_entry(n, floor):
    assert n > floor >= 1
    path, seen = [n], {n}
    while path[-1] > floor:
        x = step(path[-1])
        assert x not in seen, ('repetition before entry', n, floor, x)
        path.append(x)
        seen.add(x)
        assert len(path) < 20000, ('fuel exhausted; entry not proved', n, floor)
    assert len(path) == len(set(path))
    assert path[-2] % 2 == 0 and path[-2] == 2 * path[-1]
    assert floor < 2 * path[-1] <= 2 * floor
    return path


def correction(path, floor):
    """Compute the product directly and compare it with endpoint arithmetic."""
    assert floor > 0 and floor & (floor - 1) == 0
    odd_successors = [y for x, y in zip(path, path[1:]) if x % 2]
    assert len(odd_successors) == len(set(odd_successors))
    assert all(y > floor for y in odd_successors)
    product, loss = Fraction(1), Fraction(0)
    shells = Counter()
    for y in odd_successors:
        product *= Fraction(2 * y - 1, 2 * y)
        loss += Fraction(1, 2 * y)
        r = y.bit_length() - floor.bit_length()
        assert floor << r <= y < floor << (r + 1)
        shells[r] += 1
    h, j, y = len(path) - 1, len(odd_successors), path[-1]
    endpoint_product = Fraction(path[0] * 3 ** j, (1 << h) * y)
    assert product == endpoint_product
    assert 1 - loss <= product <= 1
    assert loss <= Fraction(j, 2 * (floor + 1))
    shell_bound = sum((Fraction(c, 2 * (floor << r)) for r, c in shells.items()),
                      Fraction(0))
    assert loss <= shell_bound
    # This is a finite-instance check of the explicit written estimate.
    # Integer powers avoid numerical real exponents or rounded comparisons.
    assert shell_bound.numerator ** 20 * floor < (
        4096 ** 20 * shell_bound.denominator ** 20)
    for r, c in shells.items():
        assert c ** 20 <= 256 ** 20 * (floor << r) ** 19
    return h, j, y, loss, product


def check_transfers(path):
    """Check shortened prefixes too, so the endpoint need not be an entry."""
    image_checks = groups_checked = boundary_checks = interval_checks = 0
    for N in sorted({len(path) - 1, (len(path) - 1) // 2}):
        prefix = path[:N + 1]
        values = set(prefix)
        assert len(values) == N + 1
        odd_prefix = [0]
        for x in prefix:
            odd_prefix.append(odd_prefix[-1] + x % 2)
        for k in sorted(set(range(1, min(12, N + 1) + 1)) | {N + 2}):
            terminal = [t for t in range(N + 1) if t + k > N]
            assert len(terminal) == min(k, N + 1)
            assert len({N - t for t in terminal}) == len(terminal)
            assert all(0 <= N - t < k for t in terminal)
            boundary_checks += 1
            groups = defaultdict(list)
            for t in range(max(0, N - k + 1)):
                n = prefix[t]
                q, residue = divmod(n, 1 << k)
                j = odd_prefix[t + k] - odd_prefix[t]
                r, residue_weight = residue, 0
                for _ in range(k):
                    residue_weight += r % 2
                    r = step(r)
                assert residue_weight == j
                image = prefix[t + k]
                assert image == q * 3 ** j + r
                assert q * 3 ** j <= image < (q + 1) * 3 ** j
                groups[q, j].append((n, image))
                image_checks += 1
            images = [y for group in groups.values() for _, y in group]
            assert len(images) == len(set(images))
            for (q, j), group in groups.items():
                a, width = q * 3 ** j, 3 ** j
                ambient = [v for v in values if a <= v < a + width]
                assert len(group) <= len(ambient)
                assert len(group) <= comb(k, j)
                groups_checked += 1
        # Aligned and half-shifted intervals at all dyadic widths up to peak.
        # These are samples of (1), not a proof for every interval and prefix.
        for ell in range(max(prefix).bit_length() + 1):
            width = 1 << ell
            for shift in sorted({0, width // 2}):
                buckets = Counter((v - shift) // width for v in values)
                for q, count in buckets.items():
                    if q * width + shift < 0:
                        continue
                    assert count ** 20 <= 256 ** 20 * width ** 19
                    interval_checks += 1
    return image_checks, groups_checked, boundary_checks, interval_checks


def finite_shells():
    cases = []
    totals = Counter()
    for floor in (1, 2, 16, 64, 256, 1024):
        for X in (2 * floor, 4 * floor, 8 * floor):
            fibres = defaultdict(list)
            max_h, max_h_start = -1, None
            max_loss = Fraction(0)
            qualified = 0
            for n in range(X, 2 * X):
                path = first_entry(n, floor)
                h, j, y, loss, product = correction(path, floor)
                totals['first_entry_paths'] += 1
                totals['shortcut_steps'] += h
                if h > max_h:
                    max_h, max_h_start = h, n
                max_loss = max(max_loss, loss)
                if loss <= Fraction(1, 3):
                    assert product >= Fraction(2, 3)
                    fibres[h, y].append((n, j, loss))
                    qualified += 1
                if n - X < 8 or n % 257 == 0:
                    checks = check_transfers(path)
                    for key, count in zip(('image_checks', 'fixed_weight_groups',
                                           'boundary_checks', 'interval_checks'), checks):
                        totals[key] += count
                    totals['selected_paths_for_transfer'] += 1
            collisions = 0
            largest = {'size': 0}
            for (h, y), members in fibres.items():
                weights = {j for _, j, _ in members}
                assert len(weights) == 1
                j = next(iter(weights))
                delta = max(loss for _, _, loss in members)
                B = Fraction((1 << h) * y, 3 ** j)
                assert B < 3 * X
                assert all((1 - delta) * B <= n <= B for n, _, _ in members)
                assert len(members) <= 1 + delta * B <= 1 + 3 * delta * X
                totals['fixed_time_fibres'] += 1
                collisions += len(members) > 1
                if len(members) > largest['size']:
                    largest = {'size': len(members), 'time': h, 'landing': y,
                               'odd_count': j, 'sources': [n for n, _, _ in members]}
            cases.append({
                'floor': floor, 'source_interval': [X, 2 * X],
                'source_count': X, 'longest_first_entry_time': max_h,
                'first_longest_source': max_h_start,
                'sources_with_correction_sum_at_most_one_third': qualified,
                'excluded_sources_from_fibre_margin': X - qualified,
                'max_correction_sum_numerator': str(max_loss.numerator),
                'max_correction_sum_denominator': str(max_loss.denominator),
                'qualified_fibre_count': len(fibres),
                'qualified_fibres_with_collisions': collisions,
                'largest_qualified_fibre': largest,
            })
            print(f'Y={floor} shell=[{X},{2 * X}): {X} first entries, '
                  f'largest qualified fibre={largest["size"]}', flush=True)
    return cases, dict(totals)


def large_floor_witness():
    K, exponent = 9, 3 ** 8
    target = 1 << exponent
    q, rem = divmod(target + 1, 3 ** K)
    assert rem == 0
    n, floor = (1 << K) * q - 1, 1 << 300
    assert floor >= 12288 ** 20
    path = first_entry(n, floor)
    h, j, y, loss, product = correction(path, floor)
    assert (h, j, y) == (K + exponent - 300, K, floor)
    assert loss < Fraction(1, 3) and product > Fraction(2, 3)
    return {'family_K': K, 'power_target_exponent': exponent,
            'floor_power_of_two': 300, 'source_bits': n.bit_length(),
            'source_sha256_hexadecimal': hashlib.sha256(hex(n).encode()).hexdigest(),
            'first_entry_time': h, 'odd_count': j, 'entry_is_exactly_the_floor': True,
            'explicit_uniform_margin_applies': True,
            'distinct_states': len(path), 'exact_product_and_sum_checked': True}


def build_lean():
    records = []
    with tempfile.TemporaryDirectory(prefix='collatz-finite-path-') as build:
        for source in ('CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
                       'lean/PackingExponent.lean', 'lean/FinitePathPacking.lean'):
            name = Path(source).stem
            command = ['lean', '-o', str(Path(build) / (name + '.olean')), source]
            result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT / (name + '.log')
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ('sorryAx', 'ofReduceBool', 'warning:'))
            records.append({'source': source, 'command': command,
                            'returncode': result.returncode, 'log': str(log.relative_to(ROOT))})
            print(f'Lean passed: {source}', flush=True)
    return records


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    cases, totals = finite_shells()
    large = large_floor_witness()
    replay = {'all_checks_passed': True, 'complete_source_shells': cases,
              'totals': totals, 'large_floor_witness': large,
              'new_collatz_counterexample': False,
              'universal_first_entry_proved': False}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = ['CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
             'lean/PackingExponent.lean', 'lean/FinitePathPacking.lean',
             'docs/ORBIT-PACKING-BOOTSTRAP.md', 'docs/FINITE-PATH-PACKING.md',
             'verify_finite_path_packing.py', 'results/finite-path-packing/replay.json',
             *[row['log'] for row in builds]]
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['first entry implies a simple finite prefix',
                         'at most k terminal positions lack a k-step image inside the prefix',
                         'fixed-time injectivity and local image packing on the remaining positions',
                         'even final entry and landing in (H/2,H]',
                         'unique odd count in a dyadic source shell under a 2/3 reverse-product margin',
                         'exact integer constants supporting the entropy and reciprocal estimates'],
        'written_scope': ['uniform 256 L^sigma packing for finite simple trajectories',
                          'extension to the distinct value set of every individual orbit',
                          'uniform reciprocal bound 8192 Y^(-1/20) on distinct values above Y',
                          'time-independent first-entry correction and reverse product',
                          'fixed-time first-entry fibre bound and its restriction on summing over time'],
        'python_scope': ['complete finite source shells and direct first-entry replay',
                         'exact rational reverse products, correction sums, and finite shell estimates',
                         'fixed-time fibre odd-count uniqueness and interval width',
                         'selected finite and truncated-prefix image transfers and boundary counts',
                         'one long exact first passage above the explicit large-floor threshold'],
        'not_proved': ['an all-time union bound over possible entry times',
                       'universal finite entry', 'vanishing weighted survivor mass',
                       'exclusion of all nontrivial cycles or divergent orbits'],
        'external_source_scope': 'The elementary fibre argument was motivated by Shaik draft Section 4; '
                                 'no global theorem or foreign code from that source is assumed.',
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'Verified {totals["first_entry_paths"]} finite first entries plus the large-floor witness. '
          'Universal entry and Collatz remain unresolved.', flush=True)


if __name__ == '__main__':
    main()
