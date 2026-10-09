"""Exact finite replay of the backward-closure contraction obstruction.

Universal inverse geometry and the convergent family are Lean checked.
Infinite weighted analysis and the all-parameter cofinite construction
are written arguments. The finite examples here are independent checks,
not a proof of contraction or its failure for actual survivor horizons.
"""
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from verify_weighted_survivors import SCALE, infinite_totals, weight_floor

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/weighted-basin-barrier'
weight = lru_cache(maxsize=None)(weight_floor)


def step(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def interval(values):
    lo = sum(weight(n) for n in values)
    return [lo, lo + len(values)]


def predecessors(values, floor):
    result = set()
    for y in values:
        result.add(2 * y)
        if y % 3 == 2:
            odd = (2 * y - 1) // 3
            if odd > floor:
                result.add(odd)
    assert all(n > floor for n in result)
    return result


def check_family():
    records = []
    for K in range(1, 13):
        a = 3 ** (K - 1)
        b = 2 ** a
        q, rem = divmod(b + 1, 3 ** K)
        assert rem == 0 and q > 0
        x = 2 ** K * q - 1
        assert 3 ** K * x <= 2 ** K * b
        n = x
        for j in range(K):
            assert n == 2 ** (K - j) * 3 ** j * q - 1
            assert n % 2 == 1
            n = step(n)
        assert n == b
        full = K <= 10
        if full:
            # Replaying the known power-of-two suffix uses actual shortcut steps.
            for j in range(a):
                assert n > 1 and n % 2 == 0
                n = step(n)
            assert n == 1
        records.append({
            'K': K, 'power_target_exponent': a, 'source_bits': x.bit_length(),
            'divisibility_remainder': rem, 'shortcut_hitting_certificate': K + a,
            'full_certificate_replayed': full,
            'certificate_is_first_arrival': K >= 2 if full else None,
            'source_sha256_hexadecimal': hashlib.sha256(hex(x).encode()).hexdigest(),
        })
    assert 1000 ** 2 * 2 ** 27 < 7 ** 2 * 3 ** 27
    assert 2000 * 2 ** 15 < 7 * 3 ** 15
    return records


def classify(floor, root, cutoff):
    """0 unknown, 1 absorbed before either target, 2 retained (including cycles)."""
    labels = bytearray(cutoff)
    for n in range(1, floor + 1):
        labels[n] = 1
    labels[root] = 2
    trapped_cycles = 0
    for n in range(floor + 1, cutoff):
        if labels[n]:
            continue
        path, visiting = [], set()
        x = n
        while x < cutoff and labels[x] == 0 and x not in visiting:
            path.append(x)
            visiting.add(x)
            x = step(x)
        if x >= cutoff:
            label = 2
        elif labels[x]:
            label = labels[x]
        else:
            trapped_cycles += 1
            label = 2
        for x in path:
            labels[x] = label
    assert all(labels[n] in (1, 2) for n in range(1, cutoff))
    return labels, trapped_cycles


def check_profile_witness():
    source, target = 2 ** 64 * 66 - 1, 3 ** 64 * 66 - 1
    assert 16 * source ** 9 < target ** 6
    records = []
    for n, expected in ((source, 560), (target, 496)):
        x, t, peak, floor_time = n, 0, n, None
        while x != 1 and t < 10000:
            if x <= 64 and floor_time is None:
                floor_time = t
            x = step(x)
            t += 1
            peak = max(peak, x)
        assert x == 1 and t == expected
        records.append({'start': str(n), 'first_one_time': t,
                        'first_floor64_time': floor_time, 'peak': str(peak),
                        'fuel_exhausted': False})
    return {'K': 64, 'q': 66, 'exact_power_inequality_passed': True,
            'convergent_trajectories': records, 'huge_cofinite_complement_enumerated': False}


def check_cofinite(floor, root, cutoff, zeta):
    assert 1 <= floor < root < cutoff and root & (root - 1) == 0 and root >= 4
    labels, cycles = classify(floor, root, cutoff)

    def member(n):
        return n > floor and (n >= cutoff or labels[n] == 2)

    def pulled(n, depth):
        for _ in range(depth):
            if n <= floor:
                return False
            n = step(n)
        return member(n)

    removed = [n for n in range(1, cutoff) if labels[n] == 1]
    longest = 0
    # This forward replay is separate from the memoized finite-state classifier.
    for n in removed:
        x, t = n, 0
        while x > floor:
            assert x < cutoff and x != root
            assert t < cutoff, ('absorption not established', floor, root, cutoff, n)
            x = step(x)
            t += 1
        longest = max(longest, t)
    assert longest <= cutoff

    exits = set()
    for n in range(1, 2 * cutoff):
        here, after = member(n), pulled(n, 1)
        assert not after or here
        if here and not after:
            exits.add(n)
            assert n == root or cutoff <= n < 2 * cutoff and n % 2 == 0
    assert root in exits
    # Above this checked range U(n)>=n/2>=cutoff, so there are no further exits.
    rem_lo, rem_hi = interval(removed)
    mass = [zeta[0] - rem_hi, zeta[1] - rem_lo]
    assert 0 < mass[0] <= mass[1]

    layers = [exits]
    occupied = set(exits)
    for _ in range(4):
        new = predecessors(layers[-1], floor)
        assert not new & occupied
        assert all(member(n) for n in new)
        occupied.update(new)
        layers.append(new)
    weights = [interval(layer) for layer in layers]
    for j in range(1, len(weights)):
        # Gamma_(3/2)<4; this checks a deliberately loose integer bound.
        assert weights[j][1] < 4 ** j * weights[0][0]

    # Direct membership checks of the loss-layer identity, independently of BFS.
    layer_checks = 0
    for k, r in ((0, 1), (0, 2), (2, 2)):
        lost = set().union(*layers[k:k + r])
        sample_max = min(2 ** (k + r) * cutoff, 32768)
        samples = set(range(1, sample_max)) | lost
        for n in samples:
            assert (pulled(n, k) and not pulled(n, k + r)) == (n in lost)
            layer_checks += 1

    loss_lo, loss_hi = weights[0]
    assert loss_hi < mass[0]
    ratio = [[mass[0] - loss_hi, mass[0]], [mass[1] - loss_lo, mass[1]]]
    digest = hashlib.sha256()
    for n in removed:
        digest.update(str(n).encode('ascii') + b'\n')
    return {
        'floor': floor, 'root': root, 'cutoff': cutoff,
        'removed_count': len(removed), 'removed_sha256_decimal_lines': digest.hexdigest(),
        'every_removed_start_directly_replayed': True,
        'longest_removed_hitting_time': longest,
        'trapped_cycles_retained': cycles,
        'mass_scaled_interval': mass,
        'exit_count': len(exits), 'loss_layer_counts': list(map(len, layers)),
        'loss_layer_scaled_intervals': weights,
        'one_step_retained_fraction_interval': ratio,
        'one_step_retained_display_only': [a / b for a, b in ratio],
        'direct_loss_layer_checks': layer_checks,
    }


def build_lean():
    records = []
    with tempfile.TemporaryDirectory(prefix='collatz-weighted-basin-') as build:
        for source in ['CollatzContradiction.lean', 'CollatzGrowth.lean',
                       'lean/WeightedSurvivors.lean', 'lean/WeightedBasinBarrier.lean']:
            name = Path(source).stem
            command = ['lean', '-o', str(Path(build) / (name + '.olean')), source]
            p = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT / (name + '.log')
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(s in p.stdout for s in ('sorryAx', 'ofReduceBool', 'warning:'))
            records.append({'source': source, 'command': command, 'returncode': p.returncode,
                            'log': str(log.relative_to(ROOT))})
            print(f'Lean passed: {source}', flush=True)
    return records


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    builds = build_lean()
    family = check_family()
    profile_witness = check_profile_witness()
    zeta, _ = infinite_totals()
    parameters = ([(64, 128, R) for R in (512, 2048, 8192, 32768)]
                  + [(64, 512, R) for R in (2048, 8192, 32768)]
                  + [(2, 8, R) for R in (64, 256, 1024)]
                  + [(16, 32, R) for R in (128, 1024)])
    cases = []
    for H, b, R in parameters:
        row = check_cofinite(H, b, R, zeta)
        assert row['trapped_cycles_retained'] == 0, (
            'Positive cycle detected: audit before reporting conjecture status', H, b, R)
        cases.append(row)
        print(f'H={H} b={b} R={R}: removed={row["removed_count"]} '
              f'exits={row["exit_count"]} all finite checks passed', flush=True)
    replay = {
        'scale': str(SCALE), 'exponent': '3/2', 'family': family, 'cofinite_cases': cases,
        'power_profile_witness': profile_witness,
        'total_removed_start_replays_with_repetitions': sum(r['removed_count'] for r in cases),
        'total_direct_loss_layer_checks_with_repetitions': sum(r['direct_loss_layer_checks'] for r in cases),
        'new_collatz_counterexample': False,
        'actual_survivor_contraction_refuted': False,
    }
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = ['lean/WeightedBasinBarrier.lean', 'lean/WeightedSurvivors.lean',
             'CollatzContradiction.lean', 'CollatzGrowth.lean',
             'verify_weighted_basin_barrier.py', 'verify_weighted_survivors.py',
             'docs/WEIGHTED-BASIN-BARRIER.md', 'results/weighted-basin-barrier/replay.json',
             *[r['log'] for r in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['exact single exit for any nonreturning root basin',
                         'convergence of every member of a convergent root basin',
                         'power-of-two convergence and nonreturn above two',
                         'all-index divisibility 3^(k+1) divides 2^(3^k)+1',
                         'all-index rising path to a power of two, convergence, and source/target inequality',
                         'K9 concrete parameters, convergence, basin boundary, and ratio arithmetic',
                         'rational comparisons for the 0.993 obstructions',
                         'finite 3/2 power-profile witness arithmetic and convergence'],
        'python_scope': ['12 family arithmetic checks; first 10 full trajectory certificates replayed',
                         '12 moderate cofinite constructions',
                         'independent absorption check for every removed start in each construction',
                         'complete finite exits, disjoint inverse loss layers, and direct membership checks',
                         'directed rational mass bounds using existing written integral tails',
                         'first arrivals and peaks for the two power-profile witness starts'],
        'written_scope': ['weighted basin mass identity and no uniform one-step contraction',
                          'cofinite extension with finite absorbed complement',
                          'fixed-block obstruction after any fixed survival history',
                          'bounds for the infinite weighted transfer operator',
                          'no uniform power loss bound below exponent log_2(3) on this class of populations'],
        'not_proved': ['failure of contraction for the actual S_k at a new horizon',
                       'the needed infinitely recurrent contraction for the actual S_k',
                       'a complete proof or disproof of Collatz'],
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'builds': builds,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('Verified the closure obstruction. Collatz and actual survivor contraction remain unresolved.', flush=True)


if __name__ == '__main__':
    main()
