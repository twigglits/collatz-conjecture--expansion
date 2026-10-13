"""Finite checks supporting the written count-return probability argument.

The kernel audit covers arithmetic and restart identities, not the full
stochastic proof. Exact finite distributions are not asymptotic evidence.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import gcd
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/count-return-control'
SOURCE = 'lean/CountReturnControl.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', SOURCE]
PRIOR = ['results/coalescence-energy-caps/verification.json',
         'results/reversal-persistence/verification.json']
THEOREMS = ['absolute_pair_restart', 'raw_children', 'raw_mass_recurrence',
            'holding_coefficient_bound', 'balanced_even_transition',
            'balanced_odd_departure', 'positive_even_hold', 'positive_odd_return',
            'odd_return_descent', 'even_return_descent',
            'fractional_constant_checks', 'return_budget_constants']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(t, n):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def state_from_endpoints(x, a, y, b):
    if a == b:
        return 0, abs(y-x)
    if a < b:
        return b-a, y-3**(b-a)*x
    return a-b, x-3**(a-b)*y


def children(d, c):
    if c % 2 == 0:
        return (d, c//2), (d, (3*c+1-3**d)//2)
    if d:
        D, C = d-1, (c-3**(d-1))//2
        return (d+1, (3*c+1)//2), (D, abs(C) if D == 0 else C)
    return (1, (3*c+1)//2), (1, (1-3*c)//2)


def refine(states):
    result = defaultdict(int)
    for state, mass in states.items():
        for child in children(*state):
            result[child] += mass
    return dict(result)


def direct_law_checks(counts):
    rows = []
    for distance in range(1, 17):
        states = {(0, distance): 1}
        for t in range(13):
            actual = Counter()
            for r in range(1 << t):
                x, a = direct(t, r)
                y, b = direct(t, r+distance)
                actual[state_from_endpoints(x, a, y, b)] += 1
                counts['actual_pair_residue_paths'] += 1
            assert actual == states, (distance, t)
            counts['complete_direct_state_laws'] += 1
            states = refine(states)
        rows.append({'initial_distance': distance, 'maximum_direct_depth': 12})
    print('Exact state laws match actual residue orbits.', flush=True)
    return rows


def raw_moments(counts):
    states, rows = {(0, 1): 1}, []
    for t in range(25):
        denominator = 1 << t
        mass = sum(d*m for (d, c), m in states.items())
        starts = sum(m for (d, c), m in states.items() if d == 0 and c % 2)
        fused = states.get((0, 0), 0)
        rows.append({'depth': t, 'state_count': len(states),
                     'raw_gap_mass': mass, 'restart_mass': starts,
                     'balanced_mass': fused, 'denominator': denominator,
                     'mean_gap': rational(Fraction(mass, denominator))})
        nxt = refine(states)
        assert sum(nxt.values()) == 2*denominator
        assert sum(d*m for (d, c), m in nxt.items()) == 2*mass+2*starts
        assert nxt.get((0, 0), 0) >= 2*fused
        counts['exact_full_gap_mass_recurrences'] += 1
        counts['state_nodes_refined'] += len(states)
        states = nxt
    print('Exact full-gap restart accounting passed through depth 24.', flush=True)
    return rows


def holding_checks(counts):
    offsets = [-129, -64, -3, -2, -1, 0, 1, 2, 3, 64, 129]
    rows = []
    for d in range(1, 13):
        coefficient = 3**d-1
        valuation = (coefficient & -coefficient).bit_length()-1
        assert 0 < coefficient < 2**(2*d) and valuation <= 2*d-1
        for c in offsets:
            partial = Fraction(0)
            for h in range(1, 11):
                modulus, same = 1 << h, 0
                for r in range(modulus):
                    x, y = r+256*modulus, 3**d*(r+256*modulus)+c
                    congruent = (y-x) % modulus == 0
                    parity_match = True
                    for _ in range(h):
                        if (x & 1) != (y & 1):
                            parity_match = False
                            break
                        x, y = step(x), step(y)
                    assert parity_match == congruent
                    same += parity_match
                    counts['holding_prefix_congruence_cases'] += 1
                divisor = gcd(coefficient, modulus)
                assert same == (divisor if c % divisor == 0 else 0)
                assert Fraction(same, modulus) <= min(Fraction(1), Fraction(2**valuation, modulus))
                partial += Fraction(same, modulus)
                counts['exact_holding_period_counts'] += 1
            assert partial <= valuation+1
        rows.append({'gap': d, 'coefficient_valuation': valuation,
                     'written_expected_wait_bound': 2*d+1})
    print('Exact holding-prefix congruence checks passed.', flush=True)
    return {'gaps': rows, 'offsets': offsets, 'maximum_holding_prefix': 10}


def descent_paths(counts):
    selected, largest_clock, largest_returns = [], 0, 0
    for initial in range(1, 8193):
        r, t, x, y, a, b, returns = 0, 0, 0, initial, 0, 0, 0

        def expose(desired):
            nonlocal r, t, x, y, a, b
            bit = desired ^ (x & 1)
            r += bit*(1 << t)
            x += bit*3**a
            y += bit*3**b
            assert (x & 1) == desired
            a, b = a+(x & 1), b+(y & 1)
            x, y = step(x), step(y)
            t += 1
            counts['prescribed_actual_bits'] += 1

        while y != x:
            assert a == b and y > x
            distance, beginning = y-x, t
            expose(0)
            if distance % 2:
                c = (3*distance+1)//2
                assert b == a+1 and y == 3*x+c
                while c % 2 == 0:
                    expose(0)
                    c //= 2
                    assert b == a+1 and y == 3*x+c
                expose(1)
                assert a == b and y-x == (c-1)//2
            assert a == b and 0 <= y-x < distance and 4*(y-x) <= 3*distance
            assert t-beginning <= (3*distance+1).bit_length()+2
            returns += 1
            counts['strict_return_descent_cycles'] += 1
        assert 0 < r < (1 << t)
        assert direct(t, r) == direct(t, r+initial) == (x, a)
        largest_clock, largest_returns = max(largest_clock, t), max(largest_returns, returns)
        counts['actual_balanced_fusion_witnesses'] += 1
        if initial in (1, 2, 3, 5, 16, 127, 1024, 8192):
            selected.append({'initial_distance': initial, 'source_residue': r,
                             'depth': t, 'return_cycles': returns,
                             'common_endpoint': x, 'common_odd_count': a})
    print('Prescribed paths verified against actual orbits for all distances <=8192.', flush=True)
    return {'maximum_distance': 8192, 'largest_clock': largest_clock,
            'largest_return_count': largest_returns, 'selected_witnesses': selected}


def constant_checks():
    assert 3*256**2 < 449**2
    assert 256**16 < 2*246**16 and 3*256**16 < 2*263**16
    assert 51**20 < 2*50**20 and 246+263 == 509 < 512
    assert 3*1093120 == 512*6405
    assert Fraction(1093120)+Fraction(6404*512, 3) < 2186070
    assert 1093120**16 < 2**336
    assert 3**4 < 2**7 and 4*336 == 1344
    assert 1344*338 == 454272 and 1344+2186070 == 2187414
    return {'alpha': [1, 2], 'beta': [1, 16], 'gamma_upper': [509, 512],
            'fixed_time_half_moment_upper': 16, 'stopped_beta_moment_upper': 3202,
            'return_drift_additive_upper': 6404, 'small_set_cutoff': '1093120^16',
            'return_attempt_length': 1344, 'success_probability_lower': '2^(-454272)',
            'expected_return_count_upper': '2187414 * 2^454272',
            'scope': 'Integer constants checked; their real and stochastic applications are written.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-count-return-') as directory:
        build = Path(directory)
        for source in SOURCES:
            obj, log = build/(Path(source).stem+'.olean'), OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(x in p.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {name for name, _ in roots} == {'CountReturnControl.'+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
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
    validated = {}
    for prior in PRIOR:
        record = json.loads((ROOT/prior).read_text())
        assert record['status'] == 'passed'
        for path, expected in record['sha256'].items():
            assert digest(ROOT/path) == expected, (prior, path)
        validated[prior] = len(record['sha256'])
    version, builds = build_lean()
    counts = Counter()
    replay = {'direct_state_laws': direct_law_checks(counts), 'full_gap_moments': raw_moments(counts),
              'holding_checks': holding_checks(counts), 'descent_paths': descent_paths(counts),
              'constants': constant_checks(), 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/COUNT-RETURN-CONTROL.md',
             'docs/COALESCENCE-ENERGY-CAPS.md', *PRIOR,
             'results/count-return-control/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': validated,
        'kernel_scope': [
            'Two-child absolute-gap restart identity and exact all-depth full-period mass recurrence.',
            'Positive coefficient 3^d-1 is below 2^(2d), supporting the written holding bound.',
            'Prescribed even departure, holding, and return transitions and strict separation descent.',
            'Integer comparisons for the fractional-moment and finite-set return constants.',
        ],
        'written_scope': [
            'Conditioned Haar endpoint law, parity-prefix congruence, and uniform expected holding bound.',
            'First positive count-return tail <=16*H^(-1/5), uniformly in starting separation.',
            'Stopped 1/16 correction moment <=3202 and return drift <=509/512*D^(1/16)+6404.',
            'Finite-set return and prescribed-path argument gives expected count-return cycles <=C_star.',
            'Full-period unstopped absolute count gap has mean <=C_star, with C_star=2187414*2^454272.',
            'Balanced noncoalescence <=21*C_star*H^(-1/5), without importing an external coalescence theorem.',
            'Actual energy E_s <=(105/4)*C_star*ceil(121*s/50)^(4/5)+23/4, hence E_s=o(s).',
        ],
        'finite_scope': dict(counts),
        'external_scope': 'No new external theorem, package, or coalescence replay used.',
        'not_proved': ['A complete Lean formalization of the probability and real-analysis arguments.',
                       'A bounded late-offset energy subsequence or a uniform whole-annulus reversal charge.',
                       'Exclusion of escape, additional positive cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: count-return arithmetic and finite replay; probability theorem is written; Collatz remains open.', flush=True)


if __name__ == '__main__':
    main()
