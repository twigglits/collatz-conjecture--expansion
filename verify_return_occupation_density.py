"""Exact arithmetic and finite occupation laws for all count returns.

The exponential cycle moment and all infinite density conclusions are
written arguments. Finite integer-power checks do not prove infinite moments.
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
OUT = ROOT / 'results/return-occupation-density'
SOURCE = 'lean/ReturnOccupationDensity.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean',
           'lean/CountReturnClock.lean', 'lean/ReturnCorrectionMoments.lean',
           'lean/OrderedWeightDrift.lean', 'lean/ReversalPersistence.lean',
           'lean/ReturnImageBounds.lean', SOURCE]
PRIOR = ['results/return-correction-moments/verification.json',
         'results/return-image-bounds/verification.json',
         'results/reversal-persistence/verification.json']
THEOREMS = ['return_class', 'family_early_return', 'weight_prefix_mono',
            'power_pair_no_return', 'geometric_drift_arithmetic',
            'inverse_bernoulli_step', 'inverse_bernoulli',
            'exponential_linearization', 'attempt_denominator',
            'failed_attempt_contraction', 'half_root_constants',
            'total_attempt_constant', 'return_weight_bound',
            'return_level_mass', 'cumulative_column_bound']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct_pair(n, horizon):
    x, y, a, b, visits = n, n+1, 0, 0, []
    for t in range(1, horizon+1):
        a, b = a+(x & 1), b+(y & 1)
        x, y = step(x), step(y)
        if a == b:
            visits.append((t, a, x, y))
            if x == y:
                break
    return visits, (x, y, a, b)


def family_checks(counts):
    for q in [*range(4096), *[(1 << j)+j for j in range(16, 257, 16)]]:
        visits, _ = direct_pair(64*q+48, 6)
        assert visits == [(6, 2, 9*q+8, 9*q+7)]
        counts['direct_fixed_return_cylinders'] += 1
    rows = []
    for j in range(2, 34, 2):
        n, k, a = 8*(64**j-1)//9, 6*j-1, 3*j-1
        visits, _ = direct_pair(2*n, 6+3*a-2)
        assert visits == [(6, 2, (1 << (2*a))+1, 1 << (2*a))]
        counts['full_persistent_second_excursions'] += 1
        x, y, ax, ay = n, 3*n+2, 0, 0
        for _ in range(k+6):
            ax, ay = ax+(x & 1), ay+(y & 1)
            x, y = step(x), step(y)
        negative_cost = Fraction(0)
        for h in range(3*j-4):
            P = Fraction(3**ax, (1 << (6+h))*x)
            B = Fraction(3**(ay+1), (1 << (6+h))*y)
            assert P >= Fraction(1, 2) and B <= Fraction(27, 64)
            assert P*(P-B) >= Fraction(5, 128)
            negative_cost += P*(P-B)
            counts['exact_persistent_drift_offsets'] += 1
            ax, ay = ax+(x & 1), ay+(y & 1)
            x, y = step(x), step(y)
        assert negative_cost >= Fraction(5*(3*j-4), 128)
        rows.append({'j': j, 'source_binary_level': k, 'first_return': [6, 2, 1],
                     'last_checked_pair_clock_without_second_return': 6+3*a-2,
                     'guaranteed_negative_cost': rational(Fraction(5*(3*j-4), 128))})
    return rows


def arithmetic_checks(counts):
    for m in range(33):
        for a in range(9):
            for b in range(65):
                assert max(0, b-(m+1)*a)*(b+a) <= b*max(0, b-m*a)
                assert max(0, b-m*a)*(b+a)**m <= b**(m+1)
                counts['inverse_bernoulli_checks'] += 1
                if b > 0 and 2*m*a <= b:
                    assert b*(b+a)**m <= (b+2*m*a)*b**m
                    counts['exponential_linearization_checks'] += 1
    for Q in range(1, 129):
        for P in range(Q+1):
            assert 2048*Q <= 4096*Q-399*P
            assert 280*P <= 4096*Q
            lhs = 2*(4096*Q+280*P)*(4096*Q-3296*P)
            rhs = 4096**2*Q*(2*Q-P)
            assert lhs+7929856*P*Q+1845760*P*P == rhs
            assert lhs <= rhs
            counts['failed_attempt_rational_comparisons'] += 1
    assert 140**2 < 2*101**2 and 3*140**2 < 2*172**2
    assert Fraction(101+172, 280) == Fraction(39, 40)
    assert (4096+280)*(4096+800) <= 2*4096**2
    b = 1 << 5192
    assert b*(b+1)**140 <= (b+280)*b**140
    assert 800*(b-399) >= 400*b
    counts['explicit_cycle_constant_checks'] += 5
    for denominator in range(4, 101):
        for numerator in range(1, denominator):
            gamma = Fraction(numerator, denominator)
            if Fraction(1, 4) <= gamma < Fraction(1, 2):
                moment = 1+7*gamma/(1-2*gamma)
                assert 2*moment <= 7/(1-2*gamma)
                counts['near_half_moment_constant_checks'] += 1
    return {'failure_probability_exponent': 5180, 'cycle_moment_base': '1+2^-5192',
            'cycle_moment_upper': '2^5182',
            'scope': 'Exact rational and integer comparisons; infinite cycle probability proof is written.'}


def occupation_prefixes(counts):
    horizon = 16
    live = [(0, 0, 2, 0, 1, 0)]  # after the first step, even source
    records, fusions, rows = [], [], []
    for t in range(2, horizon+1):
        following = []
        for r, x, y, a, b, j in live:
            for bit in (0, 1):
                r1 = r+bit*(1 << (t-1))
                x0, y0 = x+bit*3**a, y+bit*3**b
                a1, b1 = a+(x0 & 1), b+(y0 & 1)
                x1, y1 = step(x0), step(y0)
                j1 = j
                counts['all_return_tree_edges'] += 1
                if a1 == b1:
                    j1 += 1
                    if x1 == y1:
                        fusions.append((t, j1))
                        continue
                    D = abs(x1-y1)
                    assert r1 % 2 == 0 and r1+1 < 1 << t
                    assert x1 < 2*3**a1 and y1 < 2*3**a1 and D < 2*3**a1
                    records.append({'t': t, 'r': r1, 'a': a1, 'x': x1, 'y': y1,
                                    'D': D, 'j': j1})
                    counts['nonfused_return_prefixes'] += 1
                    counts['later_return_prefixes'] += int(j1 > 1)
                following.append((r1, x1, y1, a1, b1, j1))
        live = following
        mass = 1 << t
        fused_mass = sum(1 << (t-clock) for clock, _ in fusions)
        assert fused_mass+len(live) == mass//2
        occupation = sum(1 << (t-v['t']) for v in records)
        leaves_occupation = sum((N-1)*(1 << (t-clock)) for clock, N in fusions)+sum(v[5] for v in live)
        assert occupation == leaves_occupation
        for beta in (0, 1, 2):
            columns = sum((1 << (t-v['t']))*3**v['a']*v['D']**beta for v in records)
            assert columns <= (1 << (beta+1))*(2*3**beta)**t*mass
            if beta == 0:
                assert columns <= ((1 << (t+1))-2)*mass
            counts['finite_all_return_column_bounds'] += 1
        rows.append({'horizon': t, 'nonfused_prefixes': len(records),
                     'nonfused_return_occupation': rational(Fraction(occupation, mass)),
                     'unfused_even_prefixes': len(live), 'fused_mass': rational(Fraction(fused_mass, mass))})
    # Independent direct trajectories through the complete even period.
    direct_hist = Counter()
    direct_occupation = 0
    for r in range(0, 1 << horizon, 2):
        visits, terminal = direct_pair(r, horizon)
        nonfused = sum(x != y for _, _, x, y in visits)
        direct_occupation += nonfused
        for t, a, x, y in visits:
            if x != y:
                direct_hist[(t, r % (1 << t), a, x-y)] += 1
        counts['direct_full_period_pair_trajectories'] += 1
    expected_hist = {(v['t'], v['r'], v['a'], v['x']-v['y']): 1 << (horizon-v['t']) for v in records}
    assert direct_hist == expected_hist
    assert direct_occupation == sum(1 << (horizon-v['t']) for v in records)
    counts['exact_occupation_prefix_identities'] += len(rows)+1
    return records, {'horizon': horizon, 'rows': rows,
                     'largest_return_index': max(v['j'] for v in records),
                     'first_return_prefixes': sum(v['j'] == 1 for v in records),
                     'later_return_prefixes': sum(v['j'] > 1 for v in records),
                     'scope': 'Complete finite even-period law, pruned only at balanced fusion.'}


def projected_density(records, H, L, beta):
    values = [0]*(3**L)
    for v in records:
        if v['t'] > H:
            continue
        period = 3**min(v['a'], L)
        coefficient = (1 << (H-v['t']))*v['D']**beta*period
        for x in range(v['x'] % period, len(values), period):
            values[x] += coefficient
    return values


def density_checks(records, counts):
    rows = []
    for H in (6, 8, 10, 12, 14, 16):
        for beta in (0, 1):
            mass_num = sum((1 << (H-v['t']))*v['D']**beta for v in records if v['t'] <= H)
            for L in (3, 5, 7):
                coarse = projected_density(records, H, L, beta)
                fine = projected_density(records, H, L+1, beta)
                q = 3**L
                assert sum(coarse) == q*mass_num and sum(fine) == 3*q*mass_num
                assert all(fine[x]+fine[x+q]+fine[x+2*q] == 3*coarse[x] for x in range(q))
                tail_num = sum((1 << (H-v['t']))*v['D']**beta for v in records if L < v['t'] <= H)
                distance_num = sum(abs(value-coarse[x % q]) for x, value in enumerate(fine))
                assert distance_num <= 2*tail_num*3*q
                counts['ternary_occupation_projection_checks'] += 1
                counts['ternary_density_values_checked'] += len(coarse)+len(fine)
                rows.append({'horizon': H, 'integer_power': beta, 'coarse_depth': L,
                             'mass': rational(Fraction(mass_num, 1 << H)),
                             'one_level_projection_error': rational(Fraction(distance_num, (1 << H)*3*q))})
    return {'rows': rows, 'scope': 'Finite powers zero and one test counting; the power-one infinite moment is not claimed.'}


def interval_checks(records, counts):
    for H in (6, 10, 14):
        selected = [v for v in records if v['t'] <= H]
        for beta in (0, 1):
            mass_num = sum((1 << (H-v['t']))*v['D']**beta for v in selected)
            column_num = sum((1 << (H-v['t']))*v['D']**beta*3**v['a'] for v in selected)
            for start in (0, 17, 511):
                for length in (1, 7, 31, 257):
                    density = [0]*length
                    sum_by_counts = 0
                    for v in selected:
                        period, residue = 3**v['a'], v['x'] % 3**v['a']
                        coefficient = (1 << (H-v['t']))*v['D']**beta*period
                        first = (residue-start) % period
                        multiplicity = sum(1 for x in range(start, start+length) if x % period == residue)
                        floor_count = (start+length+period-1-residue)//period-(start+period-1-residue)//period
                        assert multiplicity == floor_count
                        for offset in range(first, length, period):
                            density[offset] += coefficient
                        sum_by_counts += coefficient*multiplicity
                        counts['direct_occupation_residue_counts'] += 1
                    assert sum(density) == sum_by_counts
                    assert abs(sum(density)-length*mass_num) <= column_num
                    assert column_num <= (1 << (beta+1))*(2*3**beta)**H*(1 << H)
                    counts['finite_occupation_interval_bounds'] += 1
                    counts['integer_density_values_checked'] += length
    return {'horizons': [6, 10, 14], 'integer_powers': [0, 1],
            'starts': [0, 17, 511], 'lengths': [1, 7, 31, 257]}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-return-occupation-') as directory:
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
                assert {name for name, _ in roots} == {'ReturnOccupationDensity.'+t for t in THEOREMS}
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
    replay = {'persistent_return_family': family_checks(counts)}
    replay['generating_function_arithmetic'] = arithmetic_checks(counts)
    print('Exact return family and generating-function arithmetic passed.', flush=True)
    records, replay['return_occupation'] = occupation_prefixes(counts)
    print('All-return prefixes matched independent complete-period trajectories.', flush=True)
    replay['ternary_projections'] = density_checks(records, counts)
    replay['integer_intervals'] = interval_checks(records, counts)
    replay['counts'] = dict(counts)
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/RETURN-OCCUPATION-DENSITY.md',
             'docs/RETURN-CORRECTION-MOMENTS.md', 'docs/RETURN-IMAGE-BOUNDS.md',
             'docs/REVERSAL-PERSISTENCE.md', *PRIOR,
             'results/return-occupation-density/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'A fixed first-return cylinder and the persistent family return at time six with separation one.',
            'Absence of another count return for the power-of-two adjacent pair through its long persistence window.',
            'Multiplicative drift arithmetic, finite inverse Bernoulli bounds, and failed/total attempt generating-function constants.',
            'Half-power root comparisons and cumulative all-return slope-column mass.',
        ],
        'written_scope': [
            'No pointwise excursion cost depending only on first-return clock, common count, and separation can cover the persistent family.',
            'Exponential cycle moment E[(1+2^-5192)^N]<=2^5182 under the coherent binary law.',
            'All-return occupation clock and separation tails are O((1+log H)/sqrt(H)).',
            'All-return joint separation/physical-clock moments are finite when beta+alpha<1/2.',
            'The ternary all-return density K*_beta belongs to L(log L)^alpha in that range.',
            'Its Haar clock truncation error is O_beta((1+log H)*H^(beta-1/2)).',
            'Finite interval mean and logarithmic moment retain an explicit depth/length error, with column constant 2^(beta+1).',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in verification decisions.',
        'external_scope': 'No new external theorem; prior written return drift, physical-clock tail, and image Jensen argument are reused.',
        'not_proved': ['An exponential physical fusion-clock moment, or a finite physical mean.',
                       'An L^p occupation-density bound for p>1 or a separation moment at power 1/2.',
                       'The actual future-gradient pairing or a bounded weighted-energy subsequence.',
                       'Escape exclusion, exclusion of additional cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: all-return arithmetic and exact finite replay; probability remains written and Collatz unresolved.', flush=True)


if __name__ == '__main__':
    main()
