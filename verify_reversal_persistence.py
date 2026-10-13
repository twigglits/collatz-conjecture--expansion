"""Check endpoint retention, persistent reversals, and finite annulus charges.

All comparison decisions are exact. The real asymptotic deductions are
written arguments; a uniform annulus charge and full Collatz remain open.
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
OUT = ROOT / 'results/reversal-persistence'
SOURCE = 'lean/ReversalPersistence.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/OrderedWeightDrift.lean', SOURCE]
PRIOR = 'results/ordered-weight-drift/verification.json'
THEOREMS = ['reciprocal_retention', 'shifted_retention', 'half_value_arithmetic',
            'retained_half', 'family_horizon', 'family_persistent_half',
            'family_child_ceiling', 'family_reversal_persists']
PRECISION = 1 << 64


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pair(value):
    return [value.numerator, value.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(t, n):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def enclose(acc, value):
    assert value >= 0
    q, r = divmod(value.numerator*PRECISION, value.denominator)
    acc[0] += q
    acc[1] += q+bool(r)


def show_enclosure(acc, divisor=1):
    return {'lower': pair(Fraction(acc[0], PRECISION*divisor)),
            'upper': pair(Fraction(acc[1], PRECISION*divisor))}


def retention_checks(counts):
    for n in range(1, 4097):
        x, p, two = n, 1, 1
        for h in range(129):
            assert 3*two*x+p <= p*(3*n+two)
            assert two*(x+1) <= p*(n+two)
            assert p*n <= two*x
            if 4*two <= n and 4*n-1 >= 26:
                assert 32*two*x <= 9*(4*n-1)*p
                counts['retained_half_cross_products'] += 1
            counts['direct_endpoint_retention_clocks'] += 1
            p *= 3 if x & 1 else 1
            x = step(x)
            two *= 2
    return {'source_range': [1, 4096], 'extra_clock_range': [0, 128]}


def family_checks(counts):
    rows = []
    for j in range(2, 130, 2):
        n, k, R, H = 8*(64**j-1)//9, 6*j-1, 3**(3*j-1), 3*j-5
        X = (R+1)//4
        x, a = direct(k+6, n)
        y, b = direct(k+6, 3*n+2)
        assert (x, a, y, b) == (X, 3*j+1, 1, 2)
        assert a > 1+b and (1 << k) <= n < (1 << (k+1))
        P, B = Fraction(9*R, 16*(R+1)), Fraction(27, 64)
        Z = P*X/(X+1)
        total_negative, total_energy = [0, 0], [0, 0]
        p, q, two = 3**a, 3**(1+b), 64
        initial_negative = P*(P-B)
        for h in range(H+1):
            A, C = Fraction(p, two*x), Fraction(q, two*y)
            shifted = A*x/(x+1)
            assert 4*(1 << h) <= X
            assert A >= Fraction(1, 2) and C <= B
            neg, energy = A*(A-C), (A-C)**2
            assert neg >= Fraction(5, 128) and energy >= Fraction(25, 4096)
            loss = 3*(P-A)+2*(Z-shifted)
            upper_loss = 3*P*((1 << h)-1)/X
            assert 0 <= loss <= upper_loss
            assert 0 <= P-A <= P*((1 << h)-1)/(3*X)
            assert 0 <= Z-shifted <= P*X*((1 << h)-1)/((X+1)*(X+(1 << h)))
            enclose(total_negative, neg)
            enclose(total_energy, energy)
            counts['persistent_family_offset_cells'] += 1
            if h == H:
                horizon_loss, horizon_upper = loss, upper_loss
            p *= 3 if x & 1 else 1
            q *= 3 if y & 1 else 1
            x, y, two = step(x), step(y), 2*two
        negative_lower = Fraction(total_negative[0], PRECISION)
        assert negative_lower >= Fraction(5*(3*j-4), 128)
        assert Fraction(total_energy[0], PRECISION) >= Fraction(25*(3*j-4), 4096)
        full_budget_upper = 3*P+2*Z
        assert full_budget_upper < Fraction(45, 16)
        assert negative_lower/full_budget_upper > Fraction(3*j-4, 72)
        counts['family_members'] += 1
        if j in (2, 4, 8, 16, 32, 64, 128):
            rows.append({'j': j, 'level': k, 'initial_offset': 6, 'extra_horizon': H,
                         'parent_endpoint_bits': X.bit_length(),
                         'parent': pair(P), 'child': pair(B),
                         'accumulated_negative_enclosure': show_enclosure(total_negative),
                         'accumulated_negative_lower': pair(Fraction(5*(3*j-4), 128)),
                         'accumulated_energy_lower': pair(Fraction(25*(3*j-4), 4096)),
                         'all_future_parent_charge_upper': pair(full_budget_upper),
                         'charge_to_horizon': pair(horizon_loss),
                         'charge_to_horizon_upper': pair(horizon_upper),
                         'initial_negative_over_horizon_charge': pair(initial_negative/horizon_loss),
                         'required_full_future_multiplier_lower': pair(Fraction(3*j-4, 72))})
    qgeom = Fraction(1, 4096)
    rectangle_mass = 2*qgeom*(1+2*qgeom)/(1-qgeom)**2
    partial = sum(Fraction(6*m+2, 2**(12*m+12)) for m in range(64))
    assert 0 < partial < rectangle_mass < Fraction(1, 2000)
    return {'rows': rows, 'guaranteed_rectangle_measure_written_formula': pair(rectangle_mass),
            'scope': 'Every listed orbit segment is computed exactly; all-parameter conclusions use the kernel and written proof, not extrapolation.'}


def annulus_checks(counts):
    max_level, max_offset = 10, 96
    levels, exact_witness = [], None
    for k in range(max_level+1):
        size = 1 << k
        cells = {s: {'negative': [0, 0], 'charge': [0, 0]} for s in range(max_offset+1)}
        exact_negative, exact_charge = Fraction(0), Fraction(0)
        for n in range(size, 2*size):
            x, y, a, b, p, q, reversed_history = n, 3*n+2, 0, 1, 1, 3, False
            for t in range(k+max_offset+1):
                if t >= k:
                    s = t-k
                    A, B = Fraction(p, (1 << s)*x), Fraction(q, (1 << s)*y)
                    negative = A*max(A-B, 0) if reversed_history else Fraction(0)
                    charge = 3*A/(3*x+1) if x & 1 else 2*A*x/((x+1)*(x+2))
                    enclose(cells[s]['negative'], negative)
                    enclose(cells[s]['charge'], charge)
                    if (k, s) == (5, 46):
                        exact_negative += negative
                        exact_charge += charge
                    counts['exact_annulus_weight_cells'] += 1
                a, b = a+(x & 1), b+(y & 1)
                p, q = p*(3 if x & 1 else 1), q*(3 if y & 1 else 1)
                x, y = step(x), step(y)
                reversed_history = reversed_history or a > b
        maximum, max_at = Fraction(0), 0
        for s, data in cells.items():
            negative, charge = data['negative'], data['charge']
            assert charge[0] > 0
            assert negative[1] <= 8*charge[0], (k, s)
            ratio_upper = Fraction(negative[1], charge[0])
            if ratio_upper > maximum:
                maximum, max_at = ratio_upper, s
            counts['finite_C8_annulus_inequalities'] += 1
        levels.append({'level': k, 'largest_ratio_upper': pair(maximum), 'at_offset': max_at,
                       'float_display_only': float(maximum)})
        if k == 5:
            r = exact_negative/exact_charge
            assert 6 < r < 7
            exact_witness = {'level': 5, 'offset': 46,
                             'negative': pair(exact_negative/(2*size)),
                             'charge': pair(exact_charge/(2*size)),
                             'ratio': pair(r), 'float_display_only': float(r)}
        print('Exact finite annulus comparisons passed:', k, flush=True)
    assert exact_witness is not None
    return {'max_level': max_level, 'max_offset': max_offset, 'tested_constant': 8,
            'precision_denominator': PRECISION, 'levels': levels, 'C6_counterexample': exact_witness,
            'scope': 'Finite rectangle only. No uniform charge constant, escape exclusion, or cycle exclusion follows.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-reversal-persistence-') as directory:
        build = Path(directory)
        for source in SOURCES:
            obj, log = build/(Path(source).stem+'.olean'), OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT,
                                  env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(proc.stdout)
            assert proc.returncode == 0, proc.stdout
            assert not any(x in proc.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", proc.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {name for name, _ in roots} == {'ReversalPersistence.'+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': proc.returncode,
                           'elapsed_seconds': round(time.monotonic()-start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for path, expected in prior['sha256'].items():
        assert digest(ROOT/path) == expected, (PRIOR, path)
    version, builds = build_lean()
    counts = Counter()
    replay = {'retention_checks': retention_checks(counts),
              'persistence_family': family_checks(counts),
              'annulus_checks': annulus_checks(counts), 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/REVERSAL-PERSISTENCE.md', PRIOR,
             'results/reversal-persistence/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'kernel_scope': [
            'All-clock original and shifted endpoint retention inequalities.',
            'Integer arithmetic for a parent value at least one half.',
            'All-parameter horizon h<=6m+1, persistent parent lower bound, child upper bound, and historical reversal.',
        ],
        'written_scope': [
            'Real weight factorization and bounds on parent losses over a block of future steps.',
            'At every family clock in the stated horizon, negative product >=5/128 and squared difference >=25/4096.',
            'No uniform pointwise charge to fixed future blocks, or to horizons with 2^h/X tending to zero.',
            'No uniform charge of one cell\'s accumulated negative drift to all of that parent\'s future losses.',
            'The guaranteed persistence rectangles have finite total source/offset measure; no all-time family integrability is asserted.',
            'A uniform whole-annulus charge with constant C would imply limsup Cesaro energy <=1/2+121*C/10.',
        ],
        'finite_scope': dict(counts),
        'external_scope': 'No new external input adopted or replayed. Only the conditional escape implication reuses the earlier packing/rigidity/PLD route.',
        'not_proved': ['Any whole-annulus charge constant valid at all offsets and levels.',
                       'Bounded late-offset energies or reversal Cesaro means.',
                       'Exclusion of escape, additional positive cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: reversal persistence; integrated charge and Collatz remain open.', flush=True)


if __name__ == '__main__':
    main()
