"""Exact finite checks for weighted Collatz survivor mass, with rigorous tails.

Integer square roots give rational enclosures; the infinite-tail integral
inequalities are proved in docs/WEIGHTED-SURVIVORS.md, not in Lean. All
finite inverse cones are Python checks. Separate Lean builds certify the
universal inverse-cone characterization and the convergent base through 64.
No finite run establishes the all-time contraction premise.
"""
from datetime import datetime, timezone
import hashlib
import json
from math import isqrt
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/weighted-survivors'
SCALE = 2 ** 96
TAIL_CUTOFF = 2 ** 16
FLOOR = 64
DEPTH = 36
ODD_ENDPOINT = 98


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def weight_floor(n):
    """a/SCALE <= n^(-3/2) < (a+1)/SCALE, checked by squaring."""
    cube = n ** 3
    a = isqrt(SCALE ** 2 // cube)
    assert a * a * cube <= SCALE ** 2 < (a + 1) ** 2 * cube
    return a


def root_floor(n):
    """a/SCALE <= n^(-1/2) < (a+1)/SCALE."""
    a = isqrt(SCALE ** 2 // n)
    assert a * a * n <= SCALE ** 2 < (a + 1) ** 2 * n
    return a


def infinite_totals():
    """Enclose zeta(3/2) and the eligible ternary progression by integrals."""
    total = qtotal = qcount = 0
    for n in range(1, TAIL_CUTOFF + 1):
        a = weight_floor(n)
        total += a
        if n >= ODD_ENDPOINT and n % 3 == 2:
            qtotal += a
            qcount += 1
    # Integral from N+1 is a lower bound; integral from N is an upper bound.
    zeta = (total + 2 * root_floor(TAIL_CUTOFF + 1),
            total + TAIL_CUTOFF + 2 * (root_floor(TAIL_CUTOFF) + 1))
    first = TAIL_CUTOFF + 1
    first += (2 - first) % 3
    b = root_floor(first)
    # For f(j)=(first+3j)^(-3/2), integral <= sum <= f(0)+integral.
    qtail_lo = 2 * b // 3
    qtail_hi = weight_floor(first) + 1 + (2 * (b + 1) + 2) // 3
    progression = (qtotal + qtail_lo, qtotal + qcount + qtail_hi)
    return zeta, progression


def check_forward(cone, samples):
    """Separate forward simulation checks exact first entry, without caching."""
    checked = 0
    for n in samples:
        x, first = n, None
        for j in range(DEPTH + 1):
            if x <= FLOOR:
                first = j
                break
            x = step(x)
        assert first == cone.get(n), (n, first, cone.get(n))
        checked += 1
    return checked


def finite_replay():
    zeta, progression = infinite_totals()
    cone = {n: 0 for n in range(1, FLOOR + 1)}
    frontier = set(cone)
    absorbed = qabsorbed = 0
    qabsorbed_count = 0
    rows, larger_samples = [], set()
    for k in range(DEPTH + 1):
        digest = hashlib.sha256()
        ordered = sorted(frontier)
        for n in ordered:
            a = weight_floor(n)
            absorbed += a
            if n >= ODD_ENDPOINT and n % 3 == 2:
                qabsorbed += a
                qabsorbed_count += 1
            assert 1 <= n <= (2 ** k) * FLOOR
            digest.update(str(n).encode('ascii') + b'\n')
        # Samples at every level include high sources outside the direct scan.
        if ordered:
            stride = max(1, len(ordered) // 256)
            larger_samples.update(ordered[::stride])
            larger_samples.add(ordered[-1])
        mass_lo = zeta[0] - absorbed - len(cone)
        mass_hi = zeta[1] - absorbed
        q_lo = progression[0] - qabsorbed - qabsorbed_count
        q_hi = progression[1] - qabsorbed
        assert 0 < mass_lo <= mass_hi
        assert 0 <= q_lo <= q_hi < mass_hi
        # The weaker proposed bound is certified only at these finite depths.
        assert 200 * q_hi < 69 * mass_lo
        if k < 19:
            assert 3 * q_hi < mass_lo
        if k == 19:
            assert 3 * q_lo > mass_hi
        row = {
            'k': k, 'cone_count': len(cone), 'frontier_count': len(frontier),
            'frontier_sha256_sorted_decimal_lines': digest.hexdigest(),
            'mass_scaled_interval': [mass_lo, mass_hi],
            'eligible_mass_scaled_interval': [q_lo, q_hi],
            'share_lower_fraction': [q_lo, mass_hi],
            'share_upper_fraction': [q_hi, mass_lo],
            'share_display_only': [q_lo / mass_hi, q_hi / mass_lo],
        }
        rows.append(row)
        if k in (0, 19, 24, 30, 34, DEPTH):
            print(f'depth={k} cone={len(cone)} share in '
                  f'[{q_lo / mass_hi:.10f}, {q_hi / mass_lo:.10f}]', flush=True)
        if k == DEPTH:
            break
        new = set()
        for y in frontier:
            even = 2 * y
            if even not in cone:
                new.add(even)
            if y % 3 == 2:
                odd = (2 * y - 1) // 3
                assert odd > 0 and odd % 2 == 1 and step(odd) == y
                if odd not in cone:
                    new.add(odd)
        cone.update((n, k + 1) for n in new)
        frontier = new

    for current, following in zip(rows, rows[1:]):
        lo, hi = current['mass_scaled_interval']
        next_lo, next_hi = following['mass_scaled_interval']
        assert next_hi < lo
        # Direct numerical enclosures corroborate the written conditional bound.
        assert 1000 * next_hi < 993 * lo
        current['next_mass_ratio_interval'] = [[next_lo, hi], [next_hi, lo]]

    forward_interval = range(1, 2 ** 18 + 1)
    checks = check_forward(cone, forward_interval)
    larger_samples.difference_update(forward_interval)
    checks += check_forward(cone, sorted(larger_samples))

    base_times = []
    for n in range(1, FLOOR + 1):
        x = n
        for j in range(72):
            if x == 1:
                base_times.append(j)
                break
            x = step(x)
        else:
            raise AssertionError(f'Base convergence not established for {n}')
    assert max(base_times) == 71

    return {
        'floor': FLOOR, 'exponent': '3/2', 'depth': DEPTH,
        'eligible_endpoint_minimum': ODD_ENDPOINT, 'scale': str(SCALE),
        'tail_cutoff': TAIL_CUTOFF, 'zeta_scaled_interval': zeta,
        'eligible_progression_scaled_interval': progression,
        'rows': rows, 'base_first_hitting_times': base_times,
        'direct_forward_checks': checks,
        'direct_forward_interval': [1, 2 ** 18],
        'additional_direct_forward_samples': len(larger_samples),
        'no_claim_beyond_depth': DEPTH,
        'all_time_contraction_proved': False,
    }


def build_lean():
    records = []
    with tempfile.TemporaryDirectory(prefix='collatz-weighted-survivors-') as build:
        for source in ['CollatzContradiction.lean', 'lean/WeightedSurvivors.lean']:
            name = Path(source).stem
            command = ['lean', '-o', str(Path(build) / f'{name}.olean'), source]
            process = subprocess.run(command, cwd=ROOT,
                                     env=dict(os.environ, LEAN_PATH=build), text=True,
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT / f'{name}.log'
            log.write_text(process.stdout)
            assert process.returncode == 0, process.stdout
            assert 'sorryAx' not in process.stdout and 'ofReduceBool' not in process.stdout
            assert 'warning:' not in process.stdout
            records.append({'source': source, 'command': command,
                            'returncode': process.returncode,
                            'log': str(log.relative_to(ROOT))})
            print(f'Lean passed: {source}', flush=True)
    return records


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    replay = finite_replay()
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = ['lean/WeightedSurvivors.lean', 'CollatzContradiction.lean',
             'verify_weighted_survivors.py', 'docs/WEIGHTED-SURVIVORS.md',
             'results/weighted-survivors/replay.json',
             *[record['log'] for record in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['exact killed predecessor characterization',
                         'complete finite inverse-cone membership and height bound',
                         'all n > 2^k H survive k steps',
                         'convergence of every positive n <= 64',
                         'full Collatz equivalent to eventual absorption below 65',
                         'integer inequalities for the conditional contraction factor'],
        'python_scope': ['37 complete inverse cones through depth 36',
                         'integer square-root enclosures with analytic integral tails',
                         'independent direct forward checks and base hitting times'],
        'written_scope': ['infinite weighted transport identity',
                          'mass tends to zero iff all starts reach the certified floor',
                          'exponential mass envelope iff a uniform logarithmic hitting bound',
                          'obstruction to power-comparable pointwise supersolutions',
                          'conditional aggregate contraction and persistent-bias criterion',
                          'integral inequalities enclosing infinite tails'],
        'not_proved': ['all-time or eventual survivor residue-share bound',
                       'exponential mass decay', 'any universal hitting-time upper bound',
                       'Collatz for every positive integer'],
        'source_lead': 'https://github.com/GettysburgResearch/collatz/blob/main/research/astra-three-routes/ROUTE1_MELLIN.md',
        'source_role': 'independently reconstructed definitions, conditional target, and finite test',
        'foreign_code_executed': False,
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('Finite weighted checks passed. No all-time contraction or Collatz proof.', flush=True)


if __name__ == '__main__':
    main()
