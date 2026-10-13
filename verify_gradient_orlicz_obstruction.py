"""Exact returned-gradient inputs for the written Orlicz obstruction.

Exponential growth, Luxemburg norms, and convex conjugates remain written.
No floating arithmetic is used in verification decisions.
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
OUT = ROOT / 'results/gradient-orlicz-obstruction'
SOURCE = 'lean/GradientOrliczObstruction.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean',
           'lean/CountReturnClock.lean', 'lean/ReturnCorrectionMoments.lean',
           'lean/OrderedWeightDrift.lean', 'lean/ReversalPersistence.lean',
           'lean/ReturnImageBounds.lean', 'lean/ReturnOccupationDensity.lean', SOURCE]
PRIOR = ['results/return-occupation-density/verification.json',
         'results/reversal-persistence/verification.json']
THEOREMS = ['image_scale_mod_nine', 'family_image_location',
            'returned_scale_identity', 'returned_parent_half',
            'returned_child_ceiling', 'gap_cross_product',
            'squared_gap_cross_product', 'quadratic_exponential_witness']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def enclosure(x):
    scale = 1 << 64
    lower = x.numerator*scale//x.denominator
    assert Fraction(lower, scale) <= x < Fraction(lower+1, scale)
    return {'lower': rational(Fraction(lower, scale)),
            'upper': rational(Fraction(lower+1, scale))}


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, clock):
    count = 0
    for _ in range(clock):
        count += n & 1
        n = step(n)
    return n, count


def family_checks(counts):
    rows = []
    parameters = [*range(17), 24, 32, 48, 64]
    for m in parameters:
        Q = 1 << (12*m+6)
        M, q = 9*Q, 16*(Q//9)+1
        x, y, source = 16*Q+1, 16*Q, 64*q+48
        level, clock = 12*m+11, 12*m+12
        assert Q % 9 == 1 and Q <= q < 2*Q
        assert x == 9*q+8 and M+8 <= x < 2*M+8
        assert source == 16*(64**(2*m+2)-1)//9
        assert direct(source, 6) == (x, 2)
        assert direct(source+1, 6) == (y, 2)
        for t in range(1, 6):
            assert direct(source, t)[1] != direct(source+1, t)[1]
        counts['exact_family_image_and_first_return_checks'] += 1
        X, a = direct(x, clock)
        Y, b = direct(y, clock)
        smallest_gap = None
        for h in range(6*m+2):
            t = clock+h
            P = Fraction(M*3**a, (1 << t)*X)
            B = Fraction(M*3**b, (1 << t)*Y)
            assert M*(1 << (h+6)) == 9*(1 << t)
            assert (1 << (h+5))*X <= 9*3**a
            assert 3**b <= 3*(1 << h)*Y
            assert P >= Fraction(1, 2) and B <= Fraction(27, 64)
            gap = P-B
            assert gap >= Fraction(5, 64) and gap*gap >= Fraction(25, 4096)
            p, u, z, v = P.numerator, P.denominator, B.numerator, B.denominator
            assert 5*u*v <= 64*(p*v-z*u)
            assert 25*(u*v)**2 <= 4096*(p*v-z*u)**2
            smallest_gap = gap if smallest_gap is None else min(smallest_gap, gap)
            if h in (0, 6*m+1):
                parent, parent_count = direct(source//2, level+6+h)
                child, child_count = direct(3*(source//2)+2, level+6+h)
                assert P == Fraction(3**parent_count, (1 << (6+h))*parent)
                assert B == Fraction(3**(child_count+1), (1 << (6+h))*child)
                counts['independent_original_source_transport_checks'] += 2
            counts['exact_returned_gradient_offsets'] += 1
            a, b = a+(X & 1), b+(Y & 1)
            X, Y = step(X), step(Y)
        lower = Fraction(25*(6*m+2), 4096)
        assert (6*m+2)*smallest_gap**2 >= lower
        rows.append({'m': m, 'image_length_binary_bits': M.bit_length(),
                     'window_length': 6*m+2, 'gradient_sum_lower': rational(lower),
                     'quadratic_Luxemburg_norm_squared_lower': rational(lower**2/(12*m+10)),
                     'scope': 'Exact pointwise gradient bounds; logarithmic norm interpretation is written.'})
    return rows


def gradient(n, M, first, length):
    x, a = direct(n, first)
    y, b = direct(n-1, first)
    value = Fraction(0)
    for h in range(length):
        difference = Fraction(M*3**a, (1 << (first+h))*x)-Fraction(M*3**b, (1 << (first+h))*y)
        value += difference*difference
        a, b = a+(x & 1), b+(y & 1)
        x, y = step(x), step(y)
    return value


def small_interval_check(counts):
    m, Q, M = 0, 64, 576
    start, length, first = M+8, 2, 12
    values = [gradient(n, M, first, length) for n in range(start, start+M)]
    progression = [9*q+8 for q in range(Q, 2*Q)]
    assert progression == [x for x in range(start, start+M) if x % 9 == 8]
    witness = 16*Q+1
    assert values[witness-start] >= Fraction(50, 4096)
    selected = [values[x-start] for x in progression]
    interval_mean = sum(values, Fraction(0))/M
    progression_mean = sum(selected, Fraction(0))/Q
    column_pairing = sum((9*values[x-start] for x in range(start, start+M) if x % 9 == 8), Fraction(0))/M
    assert column_pairing == progression_mean
    counts['complete_small_interval_gradients'] += len(values)
    counts['complete_small_progression_gradients'] += len(selected)
    return {'m': m, 'interval': [start, start+M], 'progression_length': Q,
            'witness': witness, 'witness_gradient_sum': rational(values[witness-start]),
            'interval_mean_enclosure': enclosure(interval_mean),
            'progression_mean_enclosure': enclosure(progression_mean),
            'scope': 'One finite interval only; no extrapolation to bounded or unbounded ordinary means.'}


def exponential_arithmetic(counts):
    rows = []
    for C in (1, 2, 4, 8, 16):
        m = 16384*C*C
        numerator = 25*(6*m+2)
        target = 12*m+9+100000*C*C
        assert numerator**2 > (4096*C)**2*target
        counts['large_quadratic_exponential_integer_certificates'] += 1
        rows.append({'m': m, 'scale': C, 'power': 2,
                     'written_log_average_lower': 100000*C*C,
                     'scope': 'Integer comparison plus general family theorem; no orbit enumeration at this size.'})
    assert Fraction(1)+3+Fraction(9, 2)+Fraction(27, 6) > 9
    assert 1+1+Fraction(1, 2) > 2
    counts['elementary_exponential_constant_checks'] += 2
    return rows


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-gradient-orlicz-') as directory:
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
                assert {name for name, _ in roots} == {'GradientOrliczObstruction.'+t for t in THEOREMS}
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
    replay = {'returned_gradient_family': family_checks(counts)}
    print('Actual returned-gradient family and source transport passed.', flush=True)
    replay['small_interval'] = small_interval_check(counts)
    replay['large_exponential_arithmetic'] = exponential_arithmetic(counts)
    replay['counts'] = dict(counts)
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/GRADIENT-ORLICZ-OBSTRUCTION.md',
             'docs/RETURN-OCCUPATION-DENSITY.md', 'docs/REVERSAL-PERSISTENCE.md',
             *PRIOR, 'results/gradient-orlicz-obstruction/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'All-parameter membership of the exceptional endpoint in its actual returned progression and interval.',
            'Exact returned scale, retained parent lower bound, and child ceiling.',
            'Cross-multiplied difference and squared-gap bounds and an explicit large integer certificate.',
        ],
        'written_scope': [
            'A finite accumulated squared returned gradient is >=25*(6m+2)/4096 at one sampled endpoint.',
            'Every fixed exponential moment exp((G/C)^p), p>1, is unbounded over these actual intervals and progressions.',
            'Corresponding Luxemburg norms have lower growth order m^(1-1/p).',
            'The conjugate of u*log(1+u)^alpha has a lower bound of exponential power 1/alpha.',
            'A uniform complementary norm after summing time contributions cannot pair the current L(log L)^alpha density bounds with these gradients.',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in verification decisions.',
        'external_scope': 'No new external theorem. Earlier kernel family and return formulas are reused.',
        'not_proved': ['Unbounded ordinary means of the accumulated gradient or failure of a direct density-gradient pairing.',
                       'Failure of every possible use of Orlicz estimates or of an ordinary exponential norm at sufficiently large scale.',
                       'A uniform actual weighted-energy bound, escape exclusion, other-cycle exclusion, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: exact gradient obstruction inputs; norm deductions remain written and Collatz unresolved.', flush=True)


if __name__ == '__main__':
    main()
