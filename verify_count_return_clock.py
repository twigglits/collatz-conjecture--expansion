"""Exact arithmetic and finite-law checks for the written square-root clock bound.

The all-horizon stopping, probability, and energy arguments remain written.
No floating arithmetic is used in verification decisions.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import gcd, isqrt
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/count-return-clock'
SOURCE = 'lean/CountReturnClock.lean'
PRIOR = ['results/count-return-control/verification.json',
         'results/coalescence-energy-caps/verification.json',
         'results/annulus-height-coupling/verification.json']
THEOREMS = ['odd_power_mod_eight', 'odd_exponent_cofactor', 'first_square_cofactor',
            'square_cofactor_step', 'dyadic_exponent_cofactor',
            'odd_cofactor_not_next_power', 'halve_mass_zero', 'halve_mass_rec',
            'halve_mass_lt', 'halve_mass_le', 'cost_mass_bound', 'green_boundaries',
            'green_equation', 'green_cap', 'stopped_clock_budget']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def v2(n):
    assert n != 0
    n = abs(n)
    return (n & -n).bit_length()-1


def coefficient_v(d):
    assert d > 0
    return 1 if d % 2 else 2+v2(d)


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def arithmetic_checks(counts):
    power = 1
    for d in range(1, 8193):
        power *= 3
        actual, predicted = v2(power-1), coefficient_v(d)
        assert actual == predicted
        cofactor = (power-1) >> actual
        assert cofactor & 1 and (1 << actual)*cofactor == power-1
        counts['exact_coefficient_valuations'] += 1
    for j in range(11):
        for u in range(1, 64, 2):
            exponent = (1 << (j+1))*u
            value = 3**exponent-1
            assert value % (1 << (j+3)) == 0
            assert (value >> (j+3)) & 1
            counts['dyadic_odd_cofactors'] += 1
    valuation_sum = cost_sum = 0
    for n in range(1, 65537):
        valuation_sum += v2(n)
        cost_sum += coefficient_v(n)+2
        q, halved = n, 0
        while q:
            q //= 2
            halved += q
        assert valuation_sum == halved < n
        assert cost_sum == 3*n+n//2+halved
        assert 2*cost_sum <= 9*n
        counts['exact_valuation_mass_identities'] += 1
    print('Exact coefficient valuations and summed wait costs passed.', flush=True)


def holding_checks(counts):
    # Count each linear congruence exactly, then sum its finite prefix and
    # explicit geometric remainder. This checks the wait expectation itself.
    largest = Fraction(0)
    for d in range(1, 65):
        coefficient, v = 3**d-1, coefficient_v(d)
        for c in range(-128, 129):
            truncated = Fraction(1)
            for h in range(1, 13):
                modulus = 1 << h
                divisor = gcd(coefficient, modulus)
                solutions = divisor if c % divisor == 0 else 0
                truncated += Fraction(solutions, modulus)
                counts['exact_holding_congruence_counts'] += 1
            if c % (1 << v) == 0:
                expected = truncated+Fraction(1 << v, 1 << 12)
                assert expected == v+2
            else:
                expected = truncated
                assert expected == v2(c)+1
            assert expected <= v+2
            largest = max(largest, expected)
            counts['exact_wait_expectations'] += 1
    return {'largest_checked_wait_expectation': rational(largest),
            'gap_range': [1, 64], 'offset_range': [-128, 128],
            'scope': 'Exact congruence probabilities with exact geometric remainder.'}


def solve_walk_system(rhs):
    # Solve 2*x_j-x_(j-1)-x_(j+1)=rhs_j with zero boundaries.
    # Independent rational tridiagonal elimination, not the proposed formula.
    n = len(rhs)
    if not n:
        return []
    diag, upper, answer = [], [], []
    for i in range(n):
        d = Fraction(2) if i == 0 else 2+upper[i-1]
        r = Fraction(rhs[i]) if i == 0 else Fraction(rhs[i])+answer[i-1]
        diag.append(d)
        upper.append(-1/d)
        answer.append(r/d)
    for i in range(n-2, -1, -1):
        answer[i] -= upper[i]*answer[i+1]
    return answer


def green_checks(counts):
    rows = []
    for K in [*range(1, 129), 256, 512, 1024, 4096]:
        green = [Fraction(2*(K-d), K) for d in range(1, K)]
        costs = [coefficient_v(d)+2 for d in range(1, K)]
        envelope = 1+sum(g*c for g, c in zip(green, costs))
        assert envelope <= 1+2*sum(costs) <= 9*K-8
        if K <= 128:
            solved_green = solve_walk_system([2]+[0]*(K-2)) if K > 1 else []
            assert solved_green == green
            solved_exit = solve_walk_system([0]*(K-2)+[1]) if K > 1 else []
            assert solved_exit == [Fraction(d, K) for d in range(1, K)]
            solved_cost = solve_walk_system([2*c for c in costs])
            assert (1+solved_cost[0] if K > 1 else 1) == envelope
            counts['independent_rational_walk_systems'] += 3
        for d, g in enumerate(green, 1):
            left = green[d-2] if d > 1 else 0
            right = green[d] if d+1 < K else 0
            assert 2*g == left+right+2*(d == 1)
            assert 0 <= g <= 2
            counts['exact_green_equations'] += 1
        counts['stopped_clock_envelope_bounds'] += 1
        if K in (1, 2, 3, 8, 16, 64, 128, 1024, 4096):
            rows.append({'height_boundary': K,
                         'expected_clock_under_wait_envelope': rational(envelope),
                         'linear_bound': 9*K-8})
    print('Independent rational walk systems and clock envelopes passed.', flush=True)
    return rows


def actual_prefix_checks(counts):
    rows = []
    H, denominator = 12, 1 << 12
    for D in (1, 3, 5, 17, 257, 8191):
        for K in (2, 3, 4, 8):
            clock_sum = high_hits = low_hits = survivor_gap = 0
            visits = Counter()
            for r in range(denominator):
                x, y, a, b = r, r+D, 0, 0
                previous_gap = 0
                for t in range(1, H+1):
                    a += x & 1
                    b += y & 1
                    x, y = step(x), step(y)
                    d = abs(a-b)
                    if t == 1:
                        assert d == 1
                    if d in (0, K):
                        high_hits += d == K
                        low_hits += d == 0
                        break
                    if d != previous_gap:
                        visits[d] += 1
                    previous_gap = d
                else:
                    survivor_gap += d
                clock_sum += t
                counts['actual_stopped_residue_paths'] += 1
            assert K*high_hits+survivor_gap == denominator
            assert high_hits*K <= denominator
            assert clock_sum <= (9*K-8)*denominator
            predictable_envelope = denominator
            for d in range(1, K):
                assert K*visits[d] <= 2*(K-d)*denominator
                predictable_envelope += visits[d]*(coefficient_v(d)+2)
            assert clock_sum <= predictable_envelope
            counts['exact_stopped_prefix_laws'] += 1
            rows.append({'initial_separation': D, 'height_boundary': K,
                         'source_period_depth': H, 'denominator': denominator,
                         'upper_exit_mass': high_hits, 'lower_exit_mass': low_hits,
                         'surviving_gap_mass': survivor_gap,
                         'truncated_clock_mean': rational(Fraction(clock_sum, denominator))})
    print('Actual integer prefixes satisfy the stopped-walk accounting.', flush=True)
    return rows


def horizon_checks(counts):
    for H in range(1, 65537):
        K = isqrt(H)//3+1
        # Square both positive sides to check the exact proposed choice,
        # without a floating square root.
        numerator = H+K*(9*K-8)
        assert numerator*numerator <= 49*K*K*H
        counts['integer_horizon_tail_comparisons'] += 1


def image_family_checks(counts):
    selected = []
    for m in range(129):
        v = (125*pow(3**m, -1, 128)) % 128
        r, tau, a = (1 << (m+1))*v-2, m+8, m+5
        assert 0 < r < (1 << tau) and r % 2 == 0 and v % 2 == 1
        x0 = (3**a*v+601)//128
        assert 128*x0 == 3**a*v+601
        assert Fraction(3**a, 1 << tau) == Fraction(243, 256)*Fraction(3, 2)**m
        for q in (0, 1, 3, 17):
            x, y, ca, cb = (1 << tau)*q+r, (1 << tau)*q+r+1, 0, 0
            word_x, word_y = '', ''
            for t in range(1, tau+1):
                px, py = x & 1, y & 1
                word_x += str(px)
                word_y += str(py)
                ca, cb = ca+px, cb+py
                x, y = step(x), step(y)
                if t < tau:
                    assert cb > ca
            assert word_x == '0'+'1'*m+'0011111'
            assert word_y == '1'+'1'*m+'0110110'
            assert ca == cb == a and x-y == 4
            assert x == 3**a*q+x0 and y == 3**a*q+x0-4
            counts['actual_expanding_return_family_lifts'] += 1
        if m in (0, 1, 4, 16, 32, 64, 128):
            selected.append({'parameter': m, 'residue': r, 'clock': tau,
                             'common_count': a, 'base_endpoint': x0,
                             'separation': 4, 'multiplier': rational(Fraction(3**a, 1 << tau))})
    return {'selected': selected,
            'scope': 'Finite exact replay of a written all-parameter family; not one of the new Lean roots.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    with tempfile.TemporaryDirectory(prefix='collatz-count-return-clock-') as directory:
        obj, log = Path(directory)/'CountReturnClock.olean', OUT/'CountReturnClock.log'
        command = ['lean', '-o', str(obj), SOURCE]
        start = time.monotonic()
        p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT,
                           env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
        log.write_text(p.stdout)
        assert p.returncode == 0, p.stdout
        assert not any(x in p.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
        roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
        assert len(roots) == len(THEOREMS)
        assert {name for name, _ in roots} == {'CountReturnClock.'+t for t in THEOREMS}
        for name, axioms in roots:
            assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                'propext', 'Classical.choice', 'Quot.sound'}, name
        build = {'source': SOURCE, 'source_sha256': digest(ROOT/SOURCE),
                 'command': command, 'returncode': p.returncode,
                 'elapsed_seconds': round(time.monotonic()-start, 3),
                 'fresh_build': True, 'native_computation_used': False,
                 'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                 'olean_sha256': digest(obj)}
    print('Fresh standalone Lean build and fifteen-root audit passed.', flush=True)
    return version, build


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    authenticated = {}
    for prior in PRIOR:
        record = json.loads((ROOT/prior).read_text())
        assert record['status'] == 'passed'
        for path, expected in record['sha256'].items():
            assert digest(ROOT/path) == expected, (prior, path)
        authenticated[prior] = len(record['sha256'])
    version, build = build_lean()
    counts = Counter()
    arithmetic_checks(counts)
    replay = {'holding_expectations': holding_checks(counts),
              'finite_walks': green_checks(counts),
              'actual_stopped_prefixes': actual_prefix_checks(counts)}
    horizon_checks(counts)
    replay['expanding_image_family'] = image_family_checks(counts)
    replay['counts'] = dict(counts)
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [SOURCE, Path(__file__).name, 'docs/COUNT-RETURN-CLOCK.md',
             'docs/COUNT-RETURN-CONTROL.md', 'docs/COALESCENCE-ENERGY-CAPS.md',
             'docs/ANNULUS-HEIGHT-COUPLING.md', *PRIOR,
             'results/count-return-clock/replay.json', build['log']]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': [build],
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'Exact odd cofactors for odd and dyadically factored even exponents of three, and nondivisibility by the next power of two.',
            'Repeated-halving sum bound and integer holding-cost mass inequality.',
            'Finite Green-function boundaries, difference equation, cap, and stopped-clock linear budget.',
        ],
        'written_scope': [
            'Haar first positive count-return tail <=7/sqrt(H), uniformly over initial separation.',
            'Predictable holding-time sum before embedded walk exits [0,K] has mean <=9K-8.',
            'Balanced noncoalescence <=14*C_star/sqrt(H), doubled when conditioned on either initial input parity.',
            'Actual refinement energy E_s <=28*C_star*sqrt(ceil(121*s/50))+23/4.',
            'The coalescence-only cap-plus-tail certificate, not the actual energy, has square-root growth order.',
            'Expected sum of D_j^beta over Haar return cycles is finite for every 0<beta<1/3.',
            'All-parameter first-return family of separation four has multiplier (243/256)*(3/2)^m; raw aggregate endpoint coefficients are unbounded.',
            'Raw ternary return-image density is integrable but has unbounded essential supremum.',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None.',
        'external_scope': 'No new external theorem, package, or replay. Earlier written return-cycle budget and authenticated kernel annulus transport are reused.',
        'not_proved': ['A bounded actual-energy subsequence or a uniform weighted progression comparison.',
                       'A square-root lower bound on actual energy.',
                       'Return-separation moments at exponent 1/3 or above.',
                       'Escape exclusion, exclusion of additional cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: square-root count-return clock; bounded energy and full Collatz remain open.', flush=True)


if __name__ == '__main__':
    main()
