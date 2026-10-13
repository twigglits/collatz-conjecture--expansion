"""Exact finite inputs for the written stopped-correction moment bounds.

Infinite stopping, probabilities, real powers, and energy consequences
remain written arguments. No floating arithmetic is used in decisions.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/return-correction-moments'
SOURCE = 'lean/ReturnCorrectionMoments.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean',
           'lean/CountReturnClock.lean', SOURCE]
PRIOR = ['results/count-return-control/verification.json',
         'results/count-return-clock/verification.json',
         'results/return-image-bounds/verification.json']
THEOREMS = ['numerator_snoc', 'numerator_lift', 'numerator_children',
            'four_pow', 'stopped_correction_identity', 'clock_numerator_bound',
            'stopped_slope_identity', 'boundary_clock_budget',
            'quarter_root_constants', 'quarter_drift_constants',
            'prescribed_attempt_constants', 'odd_offset_bit_bound']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, h):
    start, a = n, 0
    for _ in range(h):
        a += n & 1
        n = step(n)
    return n, a, (1 << h)*n-3**a*start


def correction_checks(counts):
    for h in range(14):
        q, correction_mass, slope_mass = 1 << h, 0, 0
        for n in range(q):
            x, a, N = direct(n, h)
            _, lifted_a, lifted_N = direct(n+q, h)
            _, _, left_N = direct(n, h+1)
            _, _, right_N = direct(n+q, h+1)
            assert N >= 0 and lifted_a == a and lifted_N == N
            assert left_N == 3**(x & 1)*N+q*(x & 1)
            assert left_N+right_N == 4*N+q
            correction_mass += N
            slope_mass += 3**a
            counts['direct_affine_child_identities'] += 1
        assert 4*correction_mass == h*4**h
        assert slope_mass == 4**h
        counts['full_period_correction_and_slope_masses'] += 1
    return {'maximum_full_period_depth': 13,
            'scope': 'Direct integer iteration, including n=0; no assumed moment law.'}


def stopped_checks(counts):
    horizon = 14
    separations = [1, 2, 3, 4, 5, 7, 15, 31, 255, 1023,
                   400**4-1, 400**4, (1 << 35)-1]
    barriers = [1, 2, 3, 4, 8, horizon+1]
    thresholds = [1, 2, 4, 16, 64, 256]
    rows = []
    for D in separations:
        for K in barriers:
            # Each live tuple is the exact image of r and r+D after h bits.
            live = [(0, 0, D, 0, 0, 0, 0)]
            closed_probability = closed_clock = upper_exit = 0
            closed_B1 = closed_B2 = closed_A1 = closed_A2 = 0
            return_tails = [[0]*len(thresholds) for _ in range(3)]
            for h in range(1, horizon+1):
                closed_probability *= 2
                closed_clock *= 2
                upper_exit *= 2
                closed_B1 *= 4
                closed_B2 *= 4
                closed_A1 *= 4
                closed_A2 *= 4
                return_tails = [[2*x for x in row] for row in return_tails]
                q = 1 << (h-1)
                following = []
                for r, x, y, a, b, N1, N2 in live:
                    for bit in (0, 1):
                        r1 = r+bit*q
                        x0, y0 = x+bit*3**a, y+bit*3**b
                        ex, ey = x0 & 1, y0 & 1
                        x1, y1 = step(x0), step(y0)
                        a1, b1 = a+ex, b+ey
                        C1, C2 = 3**ex*N1+q*ex, 3**ey*N2+q*ey
                        assert C1 == (2*q)*x1-3**a1*r1
                        assert C2 == (2*q)*y1-3**b1*(r1+D)
                        if h <= 7 or r1 % 257 == 0:
                            assert direct(r1, h) == (x1, a1, C1)
                            assert direct(r1+D, h) == (y1, b1, C2)
                            counts['direct_stopped_endpoint_replays'] += 2
                        counts['actual_stopping_tree_edges'] += 1
                        gap = abs(a1-b1)
                        if gap == 0 or gap == K:
                            closed_probability += 1
                            closed_clock += h
                            closed_B1 += C1
                            closed_B2 += C2
                            closed_A1 += 3**a1
                            closed_A2 += 3**b1
                            upper_exit += int(gap == K)
                            if gap == 0:
                                for i, L in enumerate(thresholds):
                                    return_tails[0][i] += int(C1 > L*2*q)
                                    return_tails[1][i] += int(C2 > L*2*q)
                                    return_tails[2][i] += int(abs(x1-y1) > L)
                        else:
                            following.append((r1, x1, y1, a1, b1, C1, C2))
                live = following
                mass = 1 << h
                B1 = closed_B1+sum(row[5] for row in live)
                B2 = closed_B2+sum(row[6] for row in live)
                A1 = closed_A1+sum(3**row[3] for row in live)
                A2 = closed_A2+sum(3**row[4] for row in live)
                clock = closed_clock+h*len(live)
                assert closed_probability+len(live) == mass
                assert 4*B1 == mass*clock == 4*B2
                assert A1 == mass*mass == A2
                assert 2*(D*A1+B1+B2) == 2*D*mass*mass+mass*clock
                assert clock <= min(h, 9*K-8)*mass
                if D & 1:
                    assert K*upper_exit+sum(abs(row[3]-row[4]) for row in live) == mass
                else:
                    assert not live and not upper_exit and clock == mass
                counts['bounded_stopping_law_identities'] += 1
            if K == horizon+1:
                # There is no upper exit within this horizon: these are
                # truncated first-return tails, not the full infinite tails.
                assert upper_exit == 0
                for i, L in enumerate(thresholds):
                    for endpoint in (0, 1):
                        p = return_tails[endpoint][i]
                        assert 4*p*p*L <= 49*mass*mass
                        for barrier in range(1, 33):
                            assert Fraction(p, mass) <= Fraction(1, barrier)+Fraction(9*barrier-8, 4*L)
                            counts['finite_correction_tail_checks'] += 1
                    p = return_tails[2][i]
                    assert p*p*L <= (D+6)**2*mass*mass
                    counts['finite_return_separation_tail_checks'] += 1
            rows.append({'separation': D, 'gap_boundary': K, 'horizon': horizon,
                         'truncated_clock_mean': rational(Fraction(clock, mass)),
                         'each_correction_mean': rational(Fraction(B1, mass*mass)),
                         'each_stopped_slope_mean': rational(Fraction(A1, mass*mass)),
                         'upper_exit_mass': rational(Fraction(upper_exit, mass)),
                         'unresolved_prefixes': len(live)})
    return {'horizon': horizon, 'separations': separations, 'barriers': barriers,
            'rows': rows, 'tail_scope': 'Only returns completed by the finite horizon.'}


def prescribed_cycle(D):
    if D % 2 == 0:
        desired = [0]
    else:
        c = (3*D+1)//2
        desired = [0]
        while c % 2 == 0:
            desired.append(0)
            c //= 2
        desired.append(1)
    r, x, y, a, b = 0, 0, D, 0, 0
    for h, parity in enumerate(desired):
        bit = (parity-(x & 1)) % 2
        r += bit*(1 << h)
        x, y = x+bit*3**a, y+bit*3**b
        a, b = a+(x & 1), b+(y & 1)
        x, y = step(x), step(y)
        if h+1 < len(desired):
            assert a != b
    assert a == b
    assert direct(r, len(desired))[:2] == (x, a)
    assert direct(r+D, len(desired))[:2] == (y, b)
    distance = abs(x-y)
    assert distance < D and 4*distance <= 3*D
    if D & 1:
        assert distance == (c-1)//2 and 4*distance <= 3*D-1
    else:
        assert distance == D//2
    return distance, len(desired)


def descent_checks(counts):
    R = 400**4
    starts = set(range(1, 4097)) | {R, R-1, R-2, R-3}
    starts |= {d for j in range(1, 36) for d in ((1 << j)-1, 1 << j, (1 << j)+1)
               if 0 < d <= R}
    maximum_cycles = maximum_bits = maximum_cycle_bits = 0
    for start in sorted(starts):
        D, cycles, bits = start, 0, 0
        while D:
            D, used = prescribed_cycle(D)
            assert used <= 37
            cycles += 1
            bits += used
            maximum_cycle_bits = max(maximum_cycle_bits, used)
            counts['direct_prescribed_return_cycles'] += 1
        assert cycles <= 140 and bits <= 5180
        maximum_cycles = max(maximum_cycles, cycles)
        maximum_bits = max(maximum_bits, bits)
        counts['finite_prescribed_fusion_paths'] += 1
    return {'sample_count': len(starts), 'largest_start': max(starts),
            'maximum_cycles_observed': maximum_cycles, 'maximum_bits_observed': maximum_bits,
            'maximum_cycle_bits_observed': maximum_cycle_bits,
            'scope': 'Finite replay; the all-separation descent and bit-count argument is written with kernel transition inputs.'}


def constant_checks(counts):
    assert 120**4 < 2*101**4
    assert 3*120**4 < 2*133**4
    assert Fraction(101+133, 240) == Fraction(39, 40)
    assert 1+7*Fraction(1, 4)/(1-2*Fraction(1, 4)) == Fraction(9, 2)
    assert Fraction(39, 40)*400+9 == 399
    assert 400**4 == 25600000000 < 1 << 35
    assert (3*((1 << 35)-1)+1)//2 < 1 << 36
    assert Fraction(3, 4)**4 < Fraction(1, 2)
    assert 4*35 == 140 and 140*37 == 5180 and 140+400 == 540
    counts['exact_drift_and_attempt_constant_checks'] += 9
    for numerator in range(16, 4097):
        s = Fraction(numerator, 16)
        L, K = s*s, int(s)+1
        assert Fraction(1, K)+Fraction(9*K-8, 4)/L <= Fraction(7, 2)/s
        for D in (1, 2, 31, 400**4):
            assert Fraction(1, K)+(D+Fraction(9*K-8, 2))/L <= (D+6)/s
        counts['rational_tail_bound_comparisons'] += 5
    for denominator in range(3, 101):
        for numerator in range(1, (denominator+1)//2):
            beta = Fraction(numerator, denominator)
            assert beta < Fraction(1, 2)
            assert 7+7*beta/(Fraction(1, 2)-beta) == 7/(1-2*beta)
            counts['exact_truncation_constant_identities'] += 1
    return {'correction_tail_coefficient': [7, 2], 'adjacent_return_tail_coefficient': 7,
            'quarter_moment_per_endpoint': [9, 2], 'quarter_drift': [[39, 40], 9],
            'small_set_limit': 400**4, 'attempt_cycles': 140, 'attempt_bits': 5180,
            'return_cycle_bound': {'coefficient': 540, 'power_of_two': 5180},
            'truncation_bound': '7/(1-2*beta)*H^(beta-1/2), 0<=beta<1/2'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-return-correction-') as directory:
        for source in SOURCES:
            obj = Path(directory)/(Path(source).stem+'.olean')
            log = OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(x in p.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {name for name, _ in roots} == {'ReturnCorrectionMoments.'+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': p.returncode,
                           'elapsed_seconds': round(time.monotonic()-start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    authenticated = {}
    for prior in PRIOR:
        record = json.loads((ROOT/prior).read_text())
        assert record['status'] == 'passed'
        for path, expected in record['sha256'].items():
            assert digest(ROOT/path) == expected, (prior, path)
        authenticated[prior] = len(record['sha256'])
    version, builds = build_lean()
    counts = Counter()
    replay = {'actual_affine_corrections': correction_checks(counts)}
    print('Direct affine correction identities passed.', flush=True)
    replay['bounded_stopping_laws'] = stopped_checks(counts)
    print('Exact bounded stopping laws and finite return tails passed.', flush=True)
    replay['prescribed_descent'] = descent_checks(counts)
    replay['constants'] = constant_checks(counts)
    replay['counts'] = dict(counts)
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/RETURN-CORRECTION-MOMENTS.md',
             'docs/COUNT-RETURN-CLOCK.md', 'docs/COUNT-RETURN-CONTROL.md',
             'docs/RETURN-IMAGE-BOUNDS.md', *PRIOR,
             'results/return-correction-moments/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'Actual affine numerator recurrence, residue lift, and two-child drift identity.',
            'All finite binary stopping trees: exact correction and slope identities, with denominators cleared, and clock bound.',
            'Named prior gap-boundary clock budget and exact quarter-power drift, descent-attempt, and bit constants.',
        ],
        'written_scope': [
            'Unbounded boundary stopping via Fatou gives correction tail <=7/(2*sqrt(L)), uniformly in starting separation.',
            'First-return correction moments and summable cycle separation moments exist for every 0<beta<1/2.',
            'Returned separation from D has tail <=(D+6)/sqrt(L); adjacent case coefficient is 7.',
            'Quarter-power drift yields expected balanced-fusion cycle count <=540*2^5180.',
            'Return-image logarithmic moment region improves to beta+alpha<1/2.',
            'Haar L1 truncation error <=7/(1-2*beta)*H^(beta-1/2), including that endpoint rate, for 0<=beta<1/2.',
            'Earlier square-root fusion-clock and energy bounds can use the smaller cycle constant.',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in this verification.',
        'external_scope': 'No new external theorem. Earlier written gap-clock, fresh-prefix, and return-image arguments are reused.',
        'not_proved': ['Moments at exponent 1/2 or above.',
                       'An L^p bound with p>1 for the full returned-endpoint density.',
                       'A uniform comparison for actual weighted progression gradients or a bounded actual-energy subsequence.',
                       'Escape exclusion, exclusion of additional cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: stopped correction inputs and exact finite replay; probability is written and Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
