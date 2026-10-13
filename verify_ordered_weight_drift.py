"""Replay finite inputs to the written bound on ordered negative drift.

Kernel arithmetic, finite rational checks, and written Cesaro estimates
have distinct scopes. The post-reversal mean and full Collatz are open.
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
OUT = ROOT / 'results/ordered-weight-drift'
SOURCE = 'lean/OrderedWeightDrift.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', SOURCE]
THEOREMS = [
    'shifted_step', 'halving_order', 'shifted_order_step',
    'ordered_shifted_endpoints', 'ordered_cross_product',
    'refinement_shifted_order', 'alive_even_count_order', 'alive_prefix',
    'first_return_order', 'reciprocal_downward_bound',
    'odd_charge_denominator', 'even_charge_denominator',
    'shifted_orbit_identity', 'shifted_correction_lift',
    'shifted_correction_mass', 'reversal_example',
    'reversed_shifted_order_fails', 'odd_power_mod_eight',
    'family_even_clock', 'family_even_reversed',
    'unshifted_order_step', 'initial_positive_transition',
    'positive_even_transitions', 'first_odd_after_even_closes',
    'all_odd_one_turn', 'one_turn_lift', 'all_odd_children',
    'one_turn_children', 'all_odd_mass', 'one_turn_mass', 'one_turn_annulus',
]
PRIOR = ['results/escape-weight-refinements/verification.json',
         'results/coalescence-energy-caps/verification.json']
PRECISION = 1 << 64


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(t, n):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def direct_with_pattern(t, n):
    a, seen_even, one_turn = 0, False, True
    for _ in range(t):
        bit = n & 1
        if bit and seen_even:
            one_turn = False
        seen_even = seen_even or not bit
        a += bit
        n = step(n)
    return n, a, one_turn


def add_enclosure(acc, value):
    assert value >= 0
    q, r = divmod(value.numerator * PRECISION, value.denominator)
    acc[0] += q
    acc[1] += q + bool(r)


def lower(acc):
    return Fraction(acc[0], PRECISION)


def upper(acc):
    return Fraction(acc[1], PRECISION)


def display(acc):
    return {'lower': ratio(lower(acc)), 'upper': ratio(upper(acc)),
            'midpoint_float_display_only': float((lower(acc)+upper(acc))/2)}


def order_checks(counts):
    first_returns = Counter()
    for n in range(1, 8193):
        x, y, a, b, p, q = 2*n, 2*n+1, 0, 0, 1, 1
        ordered, returned = True, False
        seen_even, one_turn = False, True
        for t in range(1, 129):
            if t > 1:
                if x & 1 and seen_even:
                    one_turn = False
                seen_even = seen_even or not (x & 1)
            a += x & 1
            b += y & 1
            p *= 3 if x & 1 else 1
            q *= 3 if y & 1 else 1
            assert step(x)+1 == 3**(x & 1)*(x//2+1)
            assert step(y)+1 == 3**(y & 1)*(y//2+1)
            x, y = step(x), step(y)
            ordered = ordered and a <= b
            if ordered:
                assert y+1 <= 3**(b-a)*(x+1)
                assert p*(y+1) <= q*(x+1)
                assert max(p*y-q*x, 0)*(x+1) <= p*y
                counts['ordered_endpoint_and_reciprocal_checks'] += 1
                if p*y > q*x:
                    assert one_turn and y-3**(b-a)*x in (1, 2)
                    k = n.bit_length()-1
                    assert t-1 <= 3*k+2
                    counts['ordered_negative_pattern_and_height_checks'] += 1
            if a == b and not returned:
                assert ordered and y <= x
                first_returns[t] += 1
                returned = True
                counts['first_positive_count_returns'] += 1
            if not returned:
                assert a < b
            counts['adjacent_pair_clocks'] += 1
    return {'sources': [1, 8192], 'max_pair_clock': 128,
            'first_return_histogram': dict(sorted(first_returns.items())),
            'no_return_within_clock': 8192-sum(first_returns.values())}


def moment_checks(counts):
    rows = []
    for t in range(19):
        two, three = 1 << t, 3**t
        dsum, rsum, turns, annulus_turns = 0, 0, 0, 0
        for n in range(two):
            x, a, one_turn = direct_with_pattern(t, n)
            turns += one_turn
            Xann, Aann, annulus_turn = direct_with_pattern(t, n+two)
            assert (Xann, Aann, annulus_turn) == (3**a+x, a, one_turn)
            annulus_turns += annulus_turn
            p, d = 3**a, 3**(t-a)
            b = two*x-p*n
            assert b >= 0
            r = d*(b+two)
            assert d*two*(x+1) == three*n+r
            dsum += d
            rsum += r
            counts['direct_shifted_affine_rows'] += 1
            if n < 8:
                for lift in (1, 7, 2**63+1):
                    source = two*lift+n
                    X, A = direct(t, source)
                    R = 3**(t-A)*(two*(X+1)-3**A*source)
                    assert (X, A, R) == (p*lift+x, a, r)
                    counts['nonzero_quotient_shifted_lifts'] += 1
        assert dsum == 4**t
        assert 2*rsum+6**t == 3*8**t
        assert turns == annulus_turns == t+1
        counts['one_turn_annulus_rows'] += two
        rows.append({'depth': t, 'scale_sum': dsum, 'shifted_correction_sum': rsum,
                     'one_turn_residue_count': turns, 'one_turn_annulus_count': annulus_turns})
        print('Exact shifted moment passed:', t, flush=True)
    return rows


def drift_checks(counts, max_level=10, max_offset=96):
    names = ('energy', 'ordered_negative', 'reversed_negative',
             'original_deficit', 'shifted_deficit')
    cells = {s: {name: [0, 0] for name in names} for s in range(max_offset+2)}
    by_level = []
    for k in range(max_level+1):
        level = 1 << k
        # Fixed-precision enclosures avoid huge common denominators in sums.
        mass_bounds = {s: [[0, 0], [0, 0]] for s in range(max_offset+2)}
        for n in range(level, 2*level):
            x, y, a, b, p, q = 2*n, 2*n+1, 0, 0, 1, 1
            ordered = True
            for T in range(1, k+max_offset+3):
                a += x & 1
                b += y & 1
                p *= 3 if x & 1 else 1
                q *= 3 if y & 1 else 1
                x, y = step(x), step(y)
                ordered = ordered and a <= b
                if T < k+1:
                    continue
                s = T-k-1
                A = Fraction(p, (1 << s)*x)
                Z = Fraction(p, (1 << s)*(x+1))
                B = Fraction(q, (1 << s)*y)
                Bshift = Fraction(q, (1 << s)*(y+1))
                G = Fraction(level, n)
                assert 0 < Z <= A <= G <= 1 and 0 < Bshift <= B <= 1
                pp = p*(3 if x & 1 else 1)
                Anext = Fraction(pp, (1 << (s+1))*step(x))
                Znext = Fraction(pp, (1 << (s+1))*(step(x)+1))
                assert Anext <= A and Znext <= Z
                if x & 1:
                    assert A-Anext == A/(3*x+1) and Z-Znext == 0
                else:
                    assert A-Anext == 0 and Z-Znext == A*x/((x+1)*(x+2))
                charge = 3*(A-Anext)+2*(Z-Znext)
                assert A*A/(x+1) <= charge
                negative = A*max(A-B, 0)
                if ordered:
                    assert Z <= Bshift <= B
                    assert negative <= A*A/(x+1) <= charge
                    if negative:
                        assert s <= 2*k+2
                    counts['ordered_rational_time_charges'] += 1
                counts['rational_cells_and_time_losses'] += 1
                if s <= max_offset:
                    add_enclosure(cells[s]['energy'], (A-B)**2/(2*level))
                    kind = 'ordered_negative' if ordered else 'reversed_negative'
                    add_enclosure(cells[s][kind], negative/(2*level))
                for name, value, idx in (
                    ('original_deficit', (G-A)/level, 0),
                    ('shifted_deficit', (G-Z)/level, 1),
                ):
                    add_enclosure(cells[s][name], value)
                    add_enclosure(mass_bounds[s][idx], value)
        for s in range(max_offset+2):
            base_bound = Fraction(8, 3)**s * Fraction(2, 3)**k
            assert upper(mass_bounds[s][0]) <= base_bound/2
            assert upper(mass_bounds[s][1]) <= 3*base_bound/2
            counts['finite_annulus_deficit_bounds'] += 2
        by_level.append({'level': k, 'cells_per_offset': level})
        print('Exact rational drift cells passed at level:', k, flush=True)

    cumulative = [0, 0]
    budgets = []
    for S in range(1, max_offset+2):
        for i in (0, 1):
            cumulative[i] += cells[S-1]['ordered_negative'][i]
        original_budget = lower(cells[S]['original_deficit'])-upper(cells[0]['original_deficit'])
        shifted_budget = lower(cells[S]['shifted_deficit'])-upper(cells[0]['shifted_deficit'])
        certified_budget_lower = Fraction(3, 2)*original_budget+shifted_budget
        assert upper(cumulative) <= certified_budget_lower
        J = (121*S+49)//50
        universal_budget = Fraction(5, 2)*J+Fraction(27, 4)
        assert upper(cumulative) <= universal_budget
        assert upper(cumulative) <= 14
        assert universal_budget < Fraction(121, 20)*S+Fraction(37, 4)
        counts['finite_cumulative_ordered_budgets'] += 1
        if S in (1, 2, 4, 8, 16, 32, 64, 97):
            budgets.append({'offset_count': S, 'ordered_negative_sum': display(cumulative),
                            'finite_deficit_budget_lower': ratio(certified_budget_lower),
                            'written_all_level_budget': ratio(universal_budget)})
    selected = []
    for s in (0, 4, 8, 16, 32, 64, 96):
        assert upper(cells[s]['ordered_negative']) <= 2
        selected.append({'offset': s, **{name: display(cells[s][name]) for name in names}})
    return {'max_level': max_level, 'max_offset': max_offset,
            'precision_denominator': PRECISION, 'finite_partial_sums': selected,
            'cumulative_budgets': budgets, 'levels': by_level,
            'scope': 'Finite partial sums only; no asymptotic or late-offset reversal bound.'}


def family_checks(counts):
    rows = []
    for j in range(2, 130, 2):
        n, k = 8*(64**j-1)//9, 6*j-1
        A, t = 3**(3*j-1), k+6
        x, a = direct(t, n)
        y, b = direct(t, 3*n+2)
        assert (x, a, y, b) == ((A+1)//4, 3*j+1, 1, 2)
        assert x & 1 and (1 << k) <= n < (1 << (k+1))
        assert 1+b < a
        parent, child = Fraction(3**a, 64*x), Fraction(3**(1+b), 64*y)
        assert parent == Fraction(9*A, 16*(A+1)) and child == Fraction(27, 64)
        delta = parent/(3*x+1)
        negative_product = parent*(parent-child)
        charge_ratio = negative_product/delta
        assert charge_ratio == Fraction(9*(A-3)*(3*A+7), 256*(A+1))
        assert charge_ratio >= Fraction(27*(A-3), 256)
        assert negative_product > 3*delta
        counts['even_jump_family_exact_paths'] += 1
        if j in (2, 4, 8, 16, 32, 64, 128):
            rows.append({'j': j, 'level': k, 'source_bits': n.bit_length(),
                         'parent': ratio(parent), 'odd_child': ratio(child),
                         'downward_product': ratio(negative_product),
                         'parent_time_loss': ratio(delta), 'required_charge_factor': ratio(charge_ratio)})
    assert direct(12, 74) == (5, 5) and direct(12, 75) == (2, 4)
    assert direct(16, 74)[0] == 1 and direct(13, 75)[0] == 1
    for s in range(1024):
        J = (121*s+49)//50
        assert 2**(3*s+J) <= 3**(s+J)
        assert Fraction(5, 2)*J+Fraction(27, 4) < Fraction(121, 20)*s+Fraction(37, 4)
        counts['cutoff_and_cesaro_constant_checks'] += 1
    return rows


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-ordered-drift-') as directory:
        build = Path(directory)
        for source in SOURCES:
            obj = build/(Path(source).stem+'.olean')
            log = OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(x in p.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                found = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
                assert len(found) == len(THEOREMS)
                assert {n for n, _ in found} == {'OrderedWeightDrift.'+t for t in THEOREMS}
                for name, axioms in found:
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
    validated = {}
    for prior in PRIOR:
        record = json.loads((ROOT/prior).read_text())
        assert record['status'] == 'passed'
        for path, expected in record['sha256'].items():
            assert digest(ROOT/path) == expected, (prior, path)
        validated[prior] = len(record['sha256'])
    version, builds = build_lean()
    counts = Counter()
    replay = {'order_checks': order_checks(counts), 'shifted_moments': moment_checks(counts),
              'drift_checks': drift_checks(counts), 'reversal_family': family_checks(counts),
              'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, 'lean/CoalescenceEnergyCaps.lean', Path(__file__).name,
             'docs/ORDERED-WEIGHT-DRIFT.md', 'docs/ESCAPE-WEIGHT-REFINEMENTS.md',
             'docs/COALESCENCE-ENERGY-CAPS.md', *PRIOR,
             'results/ordered-weight-drift/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': validated,
        'kernel_scope': [
            'Shifted one-step identity, all-depth count-order propagation, and first-return endpoint order.',
            'Cross-multiplied downward reciprocal estimate and time-charge denominator inequalities.',
            'All-depth shifted affine identity, periodicity, and exact moment.',
            'A convergent example has reversed counts and violates shifted refinement order.',
            'Even-indexed jump-family endpoint formulas and count reversal at every parameter.',
            'All positive-offset transition formulas and persistence of unshifted order while count order remains nonnegative.',
            'Exactly k+1 one-turn parity prefixes on every depth-k period and on its actual source annulus.',
        ],
        'written_scope': [
            'Ordered negative drift is at most three halves of the original deficit increment plus the shifted deficit increment.',
            'The original and shifted total deficits are finite and have explicit linear upper bounds.',
            'Sum over offsets s<S of ordered negative drift <= (5/2)*ceil(121*S/50)+27/4 < (121/20)*S+37/4.',
            'The positive-offset transitions force a one-turn parent parity prefix for any ordered negative change; the source-height bound gives s<=2k+2.',
            'Stronger unconditional bounds: ordered negative drift is <=2 at each offset, tends to zero exponentially, and its sum over all offsets is <=14.',
            'The full drift series is absolutely convergent at each fixed offset, without a uniform bound.',
            'A bounded subsequence of reversal Cesaro means would imply the existing sufficient escape-exclusion criterion.',
            'No fixed immediate parent time-loss multiplier bounds all reversed downward changes; an exact family makes the required factor unbounded.',
        ],
        'finite_scope': dict(counts),
        'external_scope': 'No new external theorem adopted or replayed. New bounds need neither passage mixing nor PLD. The conditional implication to no escape reuses the prior packing/PLD route.',
        'not_proved': ['A bound on the reversal Cesaro means or the full late-offset energies.',
                       'Absence of escape, exclusion of other positive cycles, or full Collatz.'],
        'sha256': {str(p): digest(ROOT/p) for p in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: ordered weight drift; reversal bound and Collatz remain open.', flush=True)


if __name__ == '__main__':
    main()
