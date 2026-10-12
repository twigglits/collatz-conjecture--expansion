"""Exact replay of the integer inputs to the killed-operator norm calculation.

The infinite sums, real powers, operator norms, compactness argument and spectral
radii remain written analysis. No finite check proves survivor-mass decay.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
from math import isqrt
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/killed-operator-bounds'
SCALE = 1 << 112
MODULES = [
    'CollatzPacking.lean', 'lean/FirstPassagePacking.lean',
    'lean/FinitePathPacking.lean', 'lean/EqualWeightFibres.lean',
    'CollatzContradiction.lean', 'CollatzGrowth.lean',
    'lean/WeightedSurvivors.lean', 'lean/WeightedBasinBarrier.lean',
    'lean/KilledOperatorBounds.lean',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def trajectory(n, k):
    x, j, minimum = n, 0, n
    for _ in range(k):
        j += x % 2
        x = step(x)
        minimum = min(minimum, x)
    return x, j, minimum


def power_floor(num, den):
    """Floor of SCALE*(num/den)^(3/2), verified by exact squaring."""
    assert num > 0 and den > 0
    top, bottom = SCALE * SCALE * num ** 3, den ** 3
    a = isqrt(top // bottom)
    assert a * a * bottom <= top < (a + 1) ** 2 * bottom
    return a


def reuse_records():
    records = []
    for name in ('equal-weight-fibres', 'weighted-basin-barrier',
                 'fibre-prefix-bound', 'exit-certificate-budget'):
        relative = f'results/{name}/verification.json'
        previous = __import__('json').loads((ROOT / relative).read_text())
        for source, expected in previous['sha256'].items():
            assert digest(ROOT / source) == expected, source
        records.append({'manifest': relative, 'matched_hashes': len(previous['sha256'])})
    return records


def build_lean(build, allow_reuse):
    import json
    build.mkdir(parents=True, exist_ok=True)
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    cache_file = build / 'build-manifest.json'
    cached = {}
    if allow_reuse:
        data = json.loads(cache_file.read_text())
        assert data['lean_version'] == version
        cached = {row['source']: row for row in data['builds']}
    env = os.environ.copy()
    env['LEAN_PATH'] = str(build)
    records, may_reuse = [], allow_reuse
    for source in MODULES:
        name = Path(source).stem
        obj, cache_log = build / f'{name}.olean', build / f'{name}.log'
        row = cached.get(source)
        reused = False
        if may_reuse and row is not None:
            assert row['returncode'] == 0
            assert row['source_sha256'] == digest(ROOT / source), source
            assert row['olean_sha256'] == digest(obj), source
            assert row['log_sha256'] == digest(cache_log), source
            reused = True
        else:
            # A new dependency invalidates reuse of every later module.
            may_reuse = False
            command = ['lean', '-o', str(obj), source]
            result = subprocess.run(command, cwd=ROOT, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True)
            cache_log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
        log_text = cache_log.read_text()
        assert not any(x in log_text for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
        if name == 'KilledOperatorBounds':
            assert len([line for line in log_text.splitlines()
                        if line.startswith("'KilledOperatorBounds.")]) == 10
        final_log = OUT / f'{name}.log'
        final_log.write_text(log_text)
        records.append({
            'source': source, 'source_sha256': digest(ROOT / source),
            'command': ['lean', '-o', str(obj), source], 'returncode': 0,
            'log': str(final_log.relative_to(ROOT)),
            'log_sha256': digest(final_log), 'olean_sha256': digest(obj),
            'reused_verified_build': reused,
            'native_computation_used': False,
        })
        print(f'Lean passed: {source}' + (' (verified build reused)' if reused else ''), flush=True)
    return version, records


def canonical_checks():
    tables, counts = {}, Counter()
    for k in range(15):
        table = []
        for a in range(1 << k):
            b, j, _ = trajectory(a, k)
            assert b < 3 ** j
            assert (1 << k) * b <= 3 ** j * a + 3 ** k
            table.append((a, b, j))
            counts['canonical_sources'] += 1
            for q in (1, 66, (1 << 80) + 3):
                n = (1 << k) * q + a
                y, jj, minimum = trajectory(n, k)
                assert (y, jj) == (3 ** j * q + b, j)
                assert (1 << k) * y <= 3 ** j * n + 3 ** k
                assert (1 << k) * y <= 3 ** k * (n + 1)
                if q >= 66:
                    assert minimum > 64
                if 2 * 3 ** k <= (1 << k) * y:
                    assert (1 << k) * y <= 2 * 3 ** j * n
                    counts['high_target_lifts'] += 1
                for B in (0, 64, n - 1, n):
                    if 3 ** k * (B + 1) < (1 << k) * y:
                        assert B < n
                        counts['source_escape_checks'] += 1
                counts['large_affine_lifts'] += 1
        tables[k] = table
    return tables, dict(counts)


def inverse_fibre(k, y, floor):
    """Complete killed fibre, with odd counts, by exact backward branching."""
    assert y > floor
    current = {y: 0}
    for _ in range(k):
        nxt = {}
        for z, j in current.items():
            assert 2 * z not in nxt
            nxt[2 * z] = j
            if z % 3 == 2:
                n = (2 * z - 1) // 3
                if n > floor:
                    assert n % 2 and step(n) == z and n not in nxt
                    nxt[n] = j + 1
        current = nxt
    return current


def affine_fibre(k, y, floor, table):
    """Independently reconstruct every source from its canonical residue."""
    result = {}
    for a, b, j in table:
        q, remainder = divmod(y - b, 3 ** j)
        if remainder or q < 0:
            continue
        n = (1 << k) * q + a
        if n <= floor:
            continue
        actual, jj, minimum = trajectory(n, k)
        assert (actual, jj) == (y, j)
        if minimum > floor:
            assert n not in result
            result[n] = j
    return result


def column_checks(tables):
    counts, rows = Counter(), []
    for k in range(13):
        rate_lower = power_floor(3 ** k, 1 << k)
        for floor in (1, 64, 256):
            targets = set(range(floor + 1, floor + 129))
            targets.update(3 ** k * q + r
                           for q in (66, (1 << 80) + 3)
                           for r in (0, 1, 3 ** k - 1)
                           if 3 ** k * q + r > floor)
            maximum_scaled = 0
            for y in sorted(targets):
                fibre = inverse_fibre(k, y, floor)
                assert fibre == affine_fibre(k, y, floor, tables[k])
                by_weight = Counter(fibre.values())
                assert all(c <= 1 << (k - j) for j, c in by_weight.items())
                lower = sum(power_floor(y, n) for n in fibre)
                upper = lower + len(fibre)
                # Written bound is 5 for H=64; 6 suffices uniformly for H>=1.
                constant = 6 if floor == 1 else 5
                assert upper <= constant * rate_lower
                if 2 * 3 ** k <= (1 << k) * y:
                    assert all((1 << k) * y <= 2 * 3 ** j * n
                               for n, j in fibre.items())
                    counts['high_target_columns'] += 1
                else:
                    counts['low_target_columns'] += 1
                maximum_scaled = max(maximum_scaled, upper)
                counts['complete_killed_columns'] += 1
                counts['complete_fibre_members'] += len(fibre)
            rows.append({'depth': k, 'floor': floor, 'targets': len(targets),
                         'maximum_column_upper_numerator': maximum_scaled,
                         'scale': SCALE, 'norm_rate_lower_numerator': rate_lower})
        print(f'Complete killed fibres and source-weight columns passed at depth {k}.', flush=True)
    return {'counts': dict(counts), 'rows': rows}


def coefficient_limit_checks(tables):
    counts, rows = Counter(), []
    for k in range(13):
        table, modulus = tables[k], 3 ** k
        for r in sorted({0, 1 % modulus, modulus // 2, modulus - 1}):
            eligible = [(a, b, j) for a, b, j in table if (r - b) % 3 ** j == 0]
            coefficient_lower = sum(power_floor(3 ** j, 1 << k) for _, _, j in eligible)
            coefficient_upper = coefficient_lower + len(eligible)
            for q in (66, (1 << 40) + 3, (1 << 80) + 3):
                y = modulus * q + r
                fibre = inverse_fibre(k, y, 64)
                assert len(fibre) == len(eligible)
                assert fibre == affine_fibre(k, y, 64, table)
                lower = sum(power_floor(y, n) for n in fibre)
                upper = lower + len(fibre)
                # All canonical affine corrections are nonnegative forward.
                for a, b, j in eligible:
                    n = (1 << k) * ((y - b) // 3 ** j) + a
                    assert (1 << k) * y >= 3 ** j * n
                    assert ((1 << k) * y - 3 ** k) <= 3 ** j * n
                assert lower <= upper and coefficient_lower <= upper
                # R <= (1-t)^(-3/2)*Z, t=3^k/(2^k*y), in directed intervals.
                numerator = (1 << k) * y
                factor_upper = power_floor(numerator, numerator - 3 ** k) + 1
                assert lower * SCALE <= factor_upper * coefficient_upper
                counts['residue_limit_columns'] += 1
                if q > 1 << 80:
                    # Certify a small relative discrepancy, without floating point.
                    assert (upper - coefficient_lower) * (1 << 70) <= coefficient_lower
                    counts['relative_error_below_two_pow_minus_70'] += 1
                    rows.append({'depth': k, 'target_residue': r,
                                 'fibre_count': len(eligible),
                                 'relative_error_certified_below': '2^-70'})
    return {'counts': dict(counts), 'large_target_rows': rows}


def growing_witnesses():
    counts, family = Counter(), []
    for k in range(257):
        for floor, B in ((1, 0), (64, 1000), (256, 1 << 100)):
            q = floor + B + 2
            x, y = (1 << k) * q - 1, 3 ** k * q - 1
            assert x > max(floor, B) and y > B
            n = x
            for i in range(k):
                assert n == (1 << (k - i)) * 3 ** i * q - 1
                assert n > floor and n % 2
                n = step(n)
                counts['all_odd_physical_steps'] += 1
            assert n == y > floor
            assert 3 ** k * x <= (1 << k) * y
            assert 27 ** k * x ** 3 <= 8 ** k * y ** 3
            counts['all_odd_columns'] += 1
    for k in range(7, 13):
        a, b = 3 ** (k - 1), 1 << (3 ** (k - 1))
        q, remainder = divmod(b + 1, 3 ** k)
        assert remainder == 0 and q > 0
        x = (1 << k) * q - 1
        endpoint, odd, minimum = trajectory(x, k)
        assert (endpoint, odd) == (b, k) and minimum > 64
        assert 27 ** k * x ** 3 <= 8 ** k * b ** 3
        # Square the single-source contribution of the specified f.
        assert 128 ** k * 9 ** k * b ** 3 >= 243 ** k * 16 ** k * x ** 3
        full = k <= 10
        if full:
            n = b
            for i in range(a):
                assert n == 1 << (a - i) and n > 1
                if i < a - 6:
                    assert n > 64
                n = step(n)
                counts['power_tail_physical_steps'] += 1
            assert n == 1
        family.append({'K': k, 'target_power_exponent': a,
                       'source_bits': x.bit_length(), 'target_bits': b.bit_length(),
                       'source_sha256_hexadecimal': hashlib.sha256(hex(x).encode()).hexdigest(),
                       'first_floor_entry_time': k + a - 6,
                       'arrival_at_one': k + a,
                       'full_power_tail_replayed': full,
                       'squared_norm_lower_bound': [243 ** k, 128 ** k]})
    assert Fraction(3, 4) ** 7 / (1 - Fraction(3, 4)) == Fraction(2187, 4096)
    assert 243 > 128 and 8 < 9 and 25 < 27
    return {'counts': dict(counts), 'convergent_family': family,
            'infinite_spike_function_norm': [2187, 4096],
            'infinite_spike_function_and_pointwise_limit_are_written': True}


def main():
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-build-dir', type=Path,
                        help='Reuse dependency builds only after matching source, log and olean hashes.')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    reused = reuse_records()
    if args.reuse_build_dir:
        version, builds = build_lean(args.reuse_build_dir.resolve(), True)
    else:
        with tempfile.TemporaryDirectory(prefix='collatz-killed-operator-') as build:
            version, builds = build_lean(Path(build), False)
    tables, source_checks = canonical_checks()
    columns = column_checks(tables)
    limits = coefficient_limit_checks(tables)
    witnesses = growing_witnesses()
    replay = {'all_checks_passed': True, 'arithmetic': 'exact integers and directed square roots',
              'scale': SCALE, 'source_checks': source_checks, 'columns': columns,
              'coefficient_limits': limits, 'witnesses': witnesses,
              'new_survivor_contraction_horizons': 0, 'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [*MODULES, 'docs/KILLED-OPERATOR-BOUNDS.md',
             'verify_killed_operator_bounds.py', 'results/killed-operator-bounds/replay.json',
             *[row['log'] for row in builds], *[row['manifest'] for row in reused]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved', 'lean_version': version,
        'builds': builds, 'reused_verification': reused,
        'kernel_scope': [
            'uniform additive error converting affine coefficients to source sizes',
            'actual source comparison above the high-target threshold',
            'inverse sources escape every fixed bound when the target does',
            'arbitrarily large killed all-odd column witnesses at every depth',
            'convergent power-target column witnesses for every K>=7',
            'cubic ratio and integer constants for the written analysis',
        ],
        'written_scope': [
            'exact killed composition operator norm as supremum of weighted columns',
            'two-sided all-depth norm bounds with exponential rate (3/2)^s for s>1',
            'constant 5 at floor64 and exponent3/2',
            'essential norm equals the maximum finite target-residue coefficient moment',
            'spectral radius and essential spectral radius both equal (3/2)^s',
            'positive summable observable with pointwise eventual zero and diverging norms',
        ],
        'python_scope': [
            'canonical sources and large affine lifts with source comparisons',
            'complete killed inverse fibres reconstructed independently in two ways',
            'directed square-root enclosures for actual weighted columns',
            'large-target coefficient comparison at specified residues and quotients',
            'all-odd witnesses and explicit convergent power-target witnesses',
        ],
        'not_proved': [
            'spectral or infinite-sum theorems in Lean',
            'contraction of the specific scalar survivor masses at new horizons',
            'decay of K^k applied to the constant function',
            'a survivor-conditioned renewal or mixing estimate',
            'the full Collatz conjecture or a positive-integer counterexample',
        ],
        'external_collatz_proof_inputs': [],
        'standard_analysis_used_in_written_proof': [
            'summability and integral bounds for positive power tails',
            'compactness of images of bounded sequences',
            'spectral radius formula in a Banach algebra and its Calkin quotient',
        ],
        'sha256': {name: digest(ROOT / name) for name in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('All checks passed. The spectral conclusions are written; Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
