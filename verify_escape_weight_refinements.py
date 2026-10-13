"""Check actual correction-weight refinements, moments, and finite energies.

Kernel arithmetic, independent finite checks, and written infinite energy
arguments have separate scopes. No bounded-energy subsequence or universal
eventual periodicity is inferred from these computations.
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
OUT = ROOT / 'results/escape-weight-refinements'
SOURCE = 'lean/EscapeWeightRefinements.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean', SOURCE]
THEOREMS = [
    'even_refinement', 'odd_refinement', 'scale_identity',
    'scaled_orbit_identity', 'correction_identity', 'data_lift',
    'data_children', 'scale_mass', 'correction_mass', 'orbit_add',
    'weight_add', 'cycle_one', 'zero_data', 'halving_data', 'lifted_one',
    'family_first_five', 'family_target_two', 'family_common_clock',
    'family_shell', 'family_seed_equation', 'two_step_jump_bound',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(q):
    return [q.numerator, q.denominator]


def shortcut(n):
    return (3 * n + 1) // 2 if n & 1 else n // 2


def direct(t, n):
    x, a = n, 0
    for _ in range(t):
        a += x & 1
        x = shortcut(x)
    return x, a


def moment_checks(counts, max_depth=18):
    # Endpoint, odd count, scale D, correction Q at depth zero.
    state = [array('Q', [0]), array('B', [0]), array('Q', [1]), array('Q', [0])]
    rows = []
    for t in range(1, max_depth + 1):
        half = 1 << (t - 1)
        child = [array(kind, [0]) * (2 * half) for kind in ('Q', 'B', 'Q', 'Q')]
        p3 = [3 ** a for a in range(t + 1)]
        for r in range(half):
            x, a, d, q = (column[r] for column in state)
            local_d, local_q = 0, 0
            for bit in (0, 1):
                before = x + bit * p3[a]
                odd = before & 1
                xx, aa, rr = shortcut(before), a + odd, r + bit * half
                dd = p3[t - aa]
                bb = (1 << t) * xx - p3[aa] * rr
                assert bb >= 0
                qq = bb * dd
                assert (dd, qq) == ((d, 3*q + half*d) if odd else (3*d, 3*q))
                assert dd * p3[aa] == p3[t]
                assert dd * (1 << t) * xx == p3[t] * rr + qq
                for column, value in zip(child, (xx, aa, dd, qq)):
                    column[rr] = value
                local_d += dd
                local_q += qq
                counts['exact_reciprocal_affine_data_rows'] += 1
            assert (local_d, local_q) == (4*d, 6*q + half*d)
            counts['paired_reciprocal_moment_identities'] += 1
        state = child
        mass_d, mass_q = sum(state[2]), sum(state[3])
        assert mass_d == 4 ** t and 2 * mass_q + 6 ** t == 8 ** t
        counts['complete_reciprocal_moment_pairs'] += 1
        sample = set(range(min(2 * half, 2048)))
        sample.update((7919*j + 104729) % (2 * half) for j in range(64))
        sample.add(2 * half - 1)
        for r in sorted(sample):
            assert direct(t, r) == (state[0][r], state[1][r])
            counts['independent_direct_residue_paths'] += 1
        for r in sorted({0, 1, half - 1, half, 2 * half - 1}):
            for block in (1, 5, 1 << 20):
                n = (1 << t) * block + r
                x, a = direct(t, n)
                assert (x, a) == (state[0][r] + 3 ** state[1][r] * block, state[1][r])
                assert ((1 << t) * x - 3 ** a * n) * 3 ** (t - a) == state[3][r]
                counts['independent_lifted_corrections'] += 1
        rows.append({'depth': t, 'scale_mass': mass_d, 'correction_mass': mass_q,
                     'reciprocal_offset_mass': ratio(Fraction(mass_q, 3 ** t))})
        print('Exact reciprocal affine moments passed:', t, flush=True)
    return rows


def family_checks(counts):
    rows = []
    for j in range(1, 129):
        u = (64 ** j - 1) // 9
        assert 9 * u + 1 == 64 ** j
        n, q, k, t, A = 8*u, 24*u+2, 6*j-1, 6*j+5, 3 ** (3*j-1)
        assert (1 << k) <= n < 1 << (k + 1)
        assert direct(5, n) == ((1 << (6*j-2)) + 1, 2)
        assert direct(t - 2, n) == (A + 1, 3*j+1)
        assert direct(t - 2, q) == (1, 1)
        xn, an = direct(t, n)
        xq, aq = direct(t, q)
        xo, ao = direct(t + 1, 2*n+1)
        assert (xq, aq) == (1, 2) and (xo, ao) == (1, 3)
        parent, child = Fraction(3 ** an, 64*xn), Fraction(3 ** ao, 64*xo)
        assert child == Fraction(27, 64)
        expected = (Fraction(9*A, 16*(A+1)) if j % 2 == 0 else Fraction(27*A, 16*(3*A+5)))
        assert parent == expected
        jump = parent - child
        assert Fraction(27, 512) <= jump < Fraction(9, 64)
        counts['independent_large_jump_family_members'] += 1
        if j <= 8 or j in (16, 32, 64, 128):
            rows.append({'j': j, 'parent': n, 'target': q, 'level': k, 'time': t,
                         'parent_minus_odd_child': ratio(jump)})
    for A in range(9, 8192, 2):
        x, a = direct(2, A+1)
        assert 27*x <= 8*A*3**a
        counts['independent_two_step_jump_bounds'] += 1
    return rows


def energy_checks(counts, max_level=12):
    offsets = (0, 4, 8, 16, 32, 48, 64)
    precision = 1 << 60
    limit = 1 << (max_level + 2)
    low = [array('Q', [0]) * limit for _ in offsets]
    high = [array('Q', [0]) * limit for _ in offsets]
    powers = [3 ** a for a in range(offsets[-1] + max_level + 3)]
    for n in range(1, limit):
        k, x, a, ci = n.bit_length() - 1, n, 0, 0
        for t in range(k + offsets[-1] + 1):
            if t == k + offsets[ci]:
                num, den = powers[a], (1 << offsets[ci]) * x
                assert 0 < num <= den
                floor, rem = divmod(precision * num, den)
                low[ci][n], high[ci][n] = floor, floor + bool(rem)
                counts['exact_finite_weight_enclosures'] += 1
                ci += 1
                if ci == len(offsets):
                    break
            a += x & 1
            x = shortcut(x)

    rows, totals = [], {}
    for ci, s in enumerate(offsets):
        total_low, total_high = Fraction(0), Fraction(0)
        for k in range(max_level + 1):
            lo, hi = 1 << k, 1 << (k + 1)
            elow, ehigh, weighted_low, weighted_high = 0, 0, 0, 0
            for n in range(lo, hi):
                assert low[ci][2*n] == low[ci][n] and high[ci][2*n] == high[ci][n]
                dl, du = low[ci][2*n+1] - high[ci][n], high[ci][2*n+1] - low[ci][n]
                assert dl <= du
                elow += min(dl*dl, du*du) if dl*du > 0 else 0
                ehigh += max(dl*dl, du*du)
                weighted_low += n * low[ci][n]
                weighted_high += n * high[ci][n]
                counts['exact_binary_energy_cells'] += 1
                if n < lo+8 or n % 1021 == 0:
                    xp, ap = direct(s+k, n)
                    xe, ae = direct(s+k+1, 2*n)
                    xo, ao = direct(s+k+1, 2*n+1)
                    p, e, o = (Fraction(3 ** aa, (1 << s)*xx) for xx, aa in ((xp, ap), (xe, ae), (xo, ao)))
                    assert p == e
                    assert (o-p)**2/2 == (o**2-p**2)/2 - p*(o-p)
                    for nn, vv in ((n, p), (2*n, e), (2*n+1, o)):
                        assert Fraction(low[ci][nn], precision) <= vv <= Fraction(high[ci][nn], precision)
                    counts['independent_fraction_energy_cells'] += 1
            lower = Fraction(elow, precision**2 * hi)
            upper = Fraction(ehigh, precision**2 * hi)
            assert 0 <= lower <= upper <= Fraction(1, 2) + Fraction(2, precision)
            total_low += lower
            total_high += upper
            loss_lo = 1 - Fraction(weighted_high, precision * lo * lo)
            loss_hi = 1 - Fraction(weighted_low, precision * lo * lo)
            loss_bound = Fraction(1, 2) * Fraction(8, 3)**s * Fraction(2, 3)**k
            assert loss_lo <= loss_hi <= loss_bound
            counts['finite_mean_loss_bounds'] += 1
            rows.append({'offset': s, 'level': k, 'energy_lower': ratio(lower),
                         'energy_upper': ratio(upper), 'partial_sum_lower': ratio(total_low),
                         'partial_sum_upper': ratio(total_high),
                         'display_only_partial_interval': [float(total_low), float(total_high)]})
        assert total_high - total_low < Fraction(4*(max_level+1), precision)
        totals[s] = (total_low, total_high)
        print('Exact finite energy enclosures passed at offset:', s, flush=True)
    K = max_level + 1
    zero_tail_bound = Fraction(1, 2) * Fraction(1, 4)**K + Fraction(21, 4) * Fraction(2, 3)**K
    assert totals[0][1] + zero_tail_bound < Fraction(1, 7)
    assert totals[16][0] > Fraction(1, 4)
    return {'offsets': list(offsets), 'maximum_level': max_level, 'positive_source_limit_exclusive': limit,
            'precision': precision, 'rows': rows,
            'noncontraction_certificate': {
                'E_0_upper_using_written_all_depth_tail': ratio(totals[0][1] + zero_tail_bound),
                'E_16_finite_partial_lower': ratio(totals[16][0]),
                'strict_comparisons': ['E_0 < 1/7', 'E_16 > 1/4'],
                'scope': 'This disproves monotone energy contraction, not a larger bound independent of offset.'}}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-escape-refinement-') as directory:
        build = Path(directory)
        for source in SOURCES:
            obj = build / (Path(source).stem + '.olean')
            log = OUT / (Path(source).stem + '.log')
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
                assert {name for name, _ in found} == {'EscapeWeightRefinements.' + t for t in THEOREMS}
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
    prior = ['results/grade-weight-moments/verification.json',
             'results/weighted-dissipation/verification.json',
             'results/dyadic-coalescence-defects/verification.json']
    prior_counts = {}
    for record in prior:
        data = json.loads((ROOT / record).read_text())
        assert data['status'] == 'passed'
        for path, expected in data['sha256'].items():
            assert digest(ROOT / path) == expected, (record, path)
        prior_counts[record] = len(data['sha256'])
    version, builds = build_lean()
    counts = Counter()
    finite = {'moment_rows': moment_checks(counts), 'jump_family_rows': family_checks(counts),
              'energy': energy_checks(counts)}
    finite['counts'] = dict(counts)
    (OUT / 'replay.json').write_text(json.dumps(finite, indent=2) + '\n')
    files = [*SOURCES, Path(__file__).name, 'docs/ESCAPE-WEIGHT-REFINEMENTS.md',
             'docs/GRADE-WEIGHT-MOMENTS.md', 'docs/WEIGHTED-DISSIPATION.md',
             'docs/PREDECESSOR-DENSITY-REVIEW.md', *prior,
             'results/predecessor-density-review/verification.json',
             'results/escape-weight-refinements/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': prior_counts,
        'kernel_scope': [
            'Exact even and odd refinement arithmetic for actual shortcut paths.',
            'All-depth reciprocal affine identities, periodicity, and moment formula.',
            'An infinite integer family with explicit paired endpoints, odd counts, source shells, and a two-step jump bound.',
        ],
        'written_scope': [
            'A geometric tail bound at each fixed offset, yielding E_s <= 3s/2+23/4.',
            'The actual fixed-offset jump family has parent-minus-odd-child jump at least 27/512 and limit 9/64.',
            'Finite exact energy enclosures plus the written tail prove E_0<1/7 and E_16>1/4.',
            'A convergent dyadic-prefix indicator invariant under actual Collatz has constant zero-or-one scaling limit and natural density.',
            'Finite limiting escape-weight squared variation would exclude divergence using packing and external PLD, without the natural-passage premise.',
            'A bounded subsequence of E_s at offsets tending to infinity would suffice by Fatou; no such bound is proved.',
        ],
        'finite_scope': dict(counts),
        'external_scope': {
            'fixed_offset_bounds_and_jump_family': 'No external dependencies.',
            'exclusion_criterion': 'Previously replayed target-dependent PLD; previous packing argument remains written.',
            'natural_passage_premise_used': False,
            'external_modules_rebuilt': False,
            'operator_sources_reviewed_not_adopted': [
                'https://arxiv.org/html/2106.11859v9', 'https://arxiv.org/html/2303.03203v1'],
        },
        'not_proved': [
            'liminf_(s to infinity) E_s < infinity, or finite limiting escape-weight energy.',
            'No divergent positive orbit, exclusion of other cycles, or full Collatz.',
        ],
        'sha256': {str(path): digest(ROOT / path) for path in files},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print('PASS: actual escape-weight refinements; full Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
