"""Audit finite grade-weight moments and the written initial-interval bound.

The all-depth integer identities are kernel checked. The real power bound
and infinite limits are written arguments. This auxiliary weight does not
detect escape, and no density-one or full Collatz claim is made.
"""

from array import array
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
OUT = ROOT / 'results/grade-weight-moments'
SOURCE = 'lean/GradeWeightMoments.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean', SOURCE]
THEOREMS = [
    'step_equation', 'scale_identity', 'principal_identity',
    'scaled_orbit_identity', 'correction_identity', 'step_grade_bound',
    'grade_envelope', 'grade_step_monotone', 'data_lift', 'data_children',
    'principal_mass', 'scale_mass', 'correction_mass',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(q):
    return [q.numerator, q.denominator]


def shortcut(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def direct(t, n):
    """Actual forward trajectory, independent of the residue recursion."""
    x, a, w_num, w_den, v_num, v_den = n, 0, 1, 1, 1, 1
    for j in range(t):
        if x & 1:
            a += 1
            w_num *= 3 * x
            w_den *= 3 * x + 1
            v_num *= 3 * x + 1
            v_den *= 4 * x
        x = shortcut(x)
        if n:
            assert w_num * (1 << (j + 1)) * x == w_den * n * 3 ** a
            assert v_num * 4 ** a * n == v_den * (1 << (j + 1)) * x
            assert v_num <= v_den
    return x, a, w_num, w_den, v_num, v_den


def finite_checks(max_depth=20):
    counts, rows = Counter(), []
    # Endpoint, odd count, P, E, Q at depth zero.
    state = [array('Q', [0]), array('B', [0]), array('Q', [1]),
             array('Q', [1]), array('Q', [0])]
    precision = 1 << 48
    for t in range(1, max_depth + 1):
        size = 1 << (t - 1)
        child = [array(kind, [0]) * (2 * size) for kind in ('Q', 'B', 'Q', 'Q', 'Q')]
        pow3 = [3 ** a for a in range(t + 1)]
        pow4 = [4 ** a for a in range(t + 1)]
        for r in range(size):
            x, a, p, e, q = (column[r] for column in state)
            local = [0, 0, 0]
            for bit in (0, 1):
                before = x + bit * pow3[a]
                odd = before & 1
                aa, xx = a + odd, shortcut(before)
                rr = r + bit * size
                ee = pow4[t - aa]
                pp = pow3[aa] * ee
                bb = (1 << t) * xx - pow3[aa] * rr
                assert bb >= 0
                qq = bb * ee
                if odd:
                    assert (pp, ee, qq) == (3 * p, e, 3 * q + size * e)
                else:
                    assert (pp, ee, qq) == (4 * p, 4 * e, 4 * q)
                assert ee * pow4[aa] == pow4[t]
                assert ee * ((1 << t) * xx) == pp * rr + qq
                assert (1 << t) * xx <= pow4[aa] * rr
                for column, value in zip(child, (xx, aa, pp, ee, qq)):
                    column[rr] = value
                for j, value in enumerate((pp, ee, qq)):
                    local[j] += value
                counts['exact_affine_data_rows'] += 1
            assert tuple(local) == (7 * p, 5 * e, 7 * q + size * e)
            counts['next_bit_moment_identities'] += 1
        state = child
        mass_p, mass_e, mass_q = (sum(state[j]) for j in (2, 3, 4))
        assert mass_p == 7 ** t
        assert mass_e == 5 ** t
        assert 3 * mass_q + 7 ** t == 10 ** t
        counts['complete_period_moment_triples'] += 1

        floor_sum, inexact = 0, 0
        for r in range(2 * size):
            # Zero's positive representative is 2^t; its endpoint is one.
            n = r if r else 2 * size
            x = state[0][r] if r else 1
            a = state[1][r]
            numerator, denominator = (1 << t) * x, pow4[a] * n
            assert 0 < numerator <= denominator
            assert pow4[t] * numerator == denominator * state[2][r] + pow4[a] * state[4][r]
            whole, remainder = divmod(precision * numerator, denominator)
            floor_sum += whole
            inexact += bool(remainder)
            counts['positive_source_weight_rows'] += 1
        lower = Fraction(floor_sum, precision * 2 * size)
        upper = Fraction(floor_sum + inexact, precision * 2 * size)
        bound = Fraction(7, 8) ** t + Fraction(4, 5) ** t + Fraction(25, 32) ** t / 3
        assert 0 <= lower <= upper <= bound
        assert upper - lower < Fraction(1, precision)
        assert bound <= Fraction(7, 3) * Fraction(7, 8) ** t

        sample = set(range(min(2 * size, 4096)))
        sample.update((7919 * j + 104729) % (2 * size) for j in range(128))
        sample.update((2 * size - 1, 2 * size - 2))
        for r in sorted(sample):
            x, a, wn, wd, vn, vd = direct(t, r)
            assert (x, a) == (state[0][r], state[1][r])
            if r:
                v = Fraction(vn, vd)
                w = Fraction(wn, wd)
                assert v == Fraction((1 << t) * x, 4 ** a * r)
                assert v * w == Fraction(3, 4) ** a
                counts['independent_fraction_dualities'] += 1
            counts['independent_direct_residue_paths'] += 1
        for r in sorted({0, 1, size - 1, size, 2 * size - 1}):
            x0, a0 = state[0][r], state[1][r]
            for block in (1, 3, 29, 1 << 20):
                n = (1 << t) * block + r
                x, a, *_ = direct(t, n)
                assert x == x0 + 3 ** a0 * block and a == a0
                e = 4 ** (t - a)
                assert (3 ** a * e, e, ((1 << t) * x - 3 ** a * n) * e) == tuple(
                    state[j][r] for j in (2, 3, 4))
                counts['independent_lifted_data_rows'] += 1
        rows.append({
            'shortcut_depth': t, 'positive_source_cutoff': 2 * size,
            'principal_integer_mass': mass_p, 'scale_integer_mass': mass_e,
            'correction_integer_mass': mass_q,
            'mean_V_at_depth_lower': ratio(lower), 'mean_V_at_depth_upper': ratio(upper),
            'written_rational_upper_bound': ratio(bound),
            'display_only_mean_interval': [float(lower), float(upper)],
        })
        print('Exact finite grade moments and source mean passed:', t, flush=True)

    for n in range(1, 4097):
        x, t, a, seen = n, 0, 0, set()
        num, den = n, n
        while x != 1:
            assert x not in seen, ('unexpected positive cycle', n, x)
            seen.add(x)
            odd = x & 1
            if odd:
                assert x >= 3 and 6 * (3 * x + 1) <= 20 * x
                counts['strict_prearrival_odd_steps'] += 1
            a, t = a + odd, t + 1
            x = shortcut(x)
            next_num, next_den = (1 << t) * x, 4 ** a * n
            assert 0 < next_num * den <= num * next_den
            num, den = next_num, next_den
            assert t < 100000, 'unresolved path; this is not a divergence certificate'
            counts['direct_prearrival_monotonicity_steps'] += 1
        terminal_num, terminal_den = num, den
        assert terminal_num == 1 << t
        for _ in range(12):
            a, t = a + (x & 1), t + 1
            x = shortcut(x)
            assert (1 << t) * x * terminal_den == 4 ** a * n * terminal_num
            counts['known_cycle_plateau_steps'] += 1
        counts['independent_first_arrival_paths'] += 1

    return {'scope': 'Exact finite checks through depth 20 and positive cutoff 2^20; terminal samples through 4096.',
            'counts': dict(counts), 'rows': rows,
            'rational_enclosure_precision': precision,
            'no_asymptotic_error_inferred_from_samples': True}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-grade-weight-') as directory:
        build = Path(directory)
        for source in SOURCES:
            stem = Path(source).stem
            obj, log = build / (stem + '.olean'), OUT / (stem + '.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT,
                                  env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(proc.stdout)
            assert proc.returncode == 0, proc.stdout
            assert not any(s in proc.stdout for s in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                found = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
                                   proc.stdout, re.M)
                assert {name for name, _ in found} == {'GradeWeightMoments.' + t for t in THEOREMS}
                assert len(found) == len(THEOREMS)
                for name, axioms in found:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT / source),
                           'command': command, 'returncode': proc.returncode,
                           'elapsed_seconds': round(time.monotonic() - start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Lean passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = ['results/dyadic-coalescence-defects/verification.json',
             'results/coalescence-tail/verification.json',
             'results/weighted-dissipation/verification.json']
    prior_counts = {}
    for record in prior:
        data = json.loads((ROOT / record).read_text())
        assert data['status'] == 'passed'
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (record, path)
        prior_counts[record] = len(data['sha256'])
    version, builds = build_lean()
    finite = finite_checks()
    (OUT / 'replay.json').write_text(json.dumps(finite, indent=2) + '\n')
    files = [*SOURCES, Path(__file__).name, 'docs/GRADE-WEIGHT-MOMENTS.md',
             'docs/DYADIC-COALESCENCE-DEFECTS.md', 'docs/WEIGHTED-DISSIPATION.md',
             *prior, 'results/grade-weight-moments/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'status': 'passed', 'collatz_status': 'unresolved',
        'lean_version': version, 'kernel_theorems_audited': len(THEOREMS),
        'builds': builds, 'prior_hashes_validated': prior_counts,
        'kernel_scope': [
            'Exact scaled affine principal and correction identities for actual shortcut trajectories.',
            'The auxiliary grade weight is bounded by one and decreases at every step, in integer form.',
            'All-depth periodicity, paired next-bit recursions, and exact masses 7^t, 5^t, (10^t-7^t)/3.',
        ],
        'written_scope': [
            'The auxiliary limit is arrival-grade weight on the known basin and zero on every orbit never reaching one.',
            'Explicit rational finite-time mean bound and a uniform O(X^(-log_2(8/7))) initial-interval bound.',
            'Unconditional summability of auxiliary dyadic amplitudes and finite total amplitude variation.',
            'Conditional on the prior density law and external PLD, any divergent orbit forces infinite escape-weight dyadic squared variation almost everywhere.',
        ],
        'finite_scope': finite['counts'],
        'external_dependencies': {
            'unconditional_grade_weight_bound': [],
            'conditional_escape_variation_interpretation': [
                'Previously written natural-density/component law.',
                'Previously replayed target-dependent predecessor positive lower density.',
            ],
            'new_external_theorems_adopted': False,
            'external_modules_rebuilt': False,
        },
        'not_proved': [
            'Any upper bound implying finite squared variation for the actual escape weight.',
            'A sharp logarithmic occupation upper bound or uniform decay of all moving-target densities.',
            'Vanishing escape mass, exclusion of other cycles, or full Collatz.',
        ],
        'sha256': {str(path): digest(ROOT / path) for path in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: auxiliary grade-weight moments; full Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
