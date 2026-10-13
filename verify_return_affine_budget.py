"""Exact finite support for the written all-return affine budget.

Fractional powers are enclosed by integer roots, never float decisions.
Probability, Haar norms, concentration, and infinite sums remain written.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from fractions import Fraction
from functools import lru_cache
import hashlib
import json
from math import comb
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/return-affine-budget'
SOURCE = 'lean/ReturnAffineBudget.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean',
           'lean/CountReturnClock.lean', 'lean/ReturnCorrectionMoments.lean',
           'lean/OrderedWeightDrift.lean', 'lean/ReversalPersistence.lean',
           'lean/ReturnImageBounds.lean', 'lean/BinaryImageEnergy.lean', SOURCE]
THEOREMS = ['augmented_snoc', 'augmented_lift', 'numerator_append',
            'augmented_append', 'power_count_children', 'power_count_mass',
            'finite_drift_budget', 'augmented_fibre_rank']
PRIOR = ['results/binary-image-energy/verification.json',
         'results/return-correction-moments/verification.json',
         'results/return-occupation-density/verification.json']
PRECISION = 1 << 48
POWERS = (Fraction(9, 8), Fraction(19, 16), Fraction(3, 2))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def enclosed(lo, hi, denominator):
    return {'lower': rational(Fraction(lo, denominator)),
            'upper': rational(Fraction(hi, denominator))}


def integer_root(value, degree):
    assert value >= 0 and degree >= 1
    if value == 0 or degree == 1:
        return value
    x = 1 << ((value.bit_length()+degree-1)//degree)
    while True:
        y = ((degree-1)*x+value//x**(degree-1))//degree
        if y >= x:
            break
        x = y
    assert x**degree <= value < (x+1)**degree
    return x


@lru_cache(maxsize=500000)
def power_bounds(n, d, exponent):
    """Enclose (n/d)^exponent with common denominator PRECISION."""
    assert n >= 0 and d > 0 and exponent > 0
    a, b = exponent.numerator, exponent.denominator
    num, den = n**a*PRECISION**b, d**a
    lo = integer_root(num//den, b)
    assert lo**b*den <= num < (lo+1)**b*den
    hi = lo if lo**b*den == num else lo+1
    return lo, hi


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, t):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def selected_return_at(n, t):
    x, y, a, b = n, n+1, 0, 0
    for _ in range(t):
        a, b = a+(x & 1), b+(y & 1)
        x, y = step(x), step(y)
        if a == b and x == y:
            return None
    return (a, x, abs(x-y)) if a == b else None


def composition_checks(counts):
    for n in range(1024):
        for t in (0, 1, 2, 4, 8, 16):
            x, a = direct(n, t)
            N = (1 << t)*x-3**a*n
            Cnum = 3**a+N
            for h in (0, 1, 2, 5, 9, 17):
                y, b = direct(x, h)
                Nh = (1 << h)*y-3**b*x
                z, c = direct(n, t+h)
                Ntotal = (1 << (t+h))*z-3**c*n
                assert (y, a+b) == (z, c)
                assert N >= 0 and Nh >= 0
                assert Ntotal == 3**b*N+(1 << t)*Nh
                assert 3**c+Ntotal == 3**b*Cnum+(1 << t)*Nh
                counts['direct_affine_composition_checks'] += 1
            for q in (1, 7):
                y, b = direct((1 << t)*q+n, t)
                Ny = (1 << t)*y-3**b*((1 << t)*q+n)
                assert b == a and Ny == N
                counts['direct_augmented_lift_checks'] += 1


def component_bounds(t, fibres, counts, label):
    by_count = defaultdict(list)
    for (a, v), nums in fibres.items():
        d = 3**a
        quotients = sorted((num-d)//d for num in nums)
        assert len(set(quotients)) == len(nums)
        assert all(q >= j for j, q in enumerate(quotients))
        assert all(d*(j+1) <= num for j, num in enumerate(sorted(nums)))
        by_count[a].append((v, nums))
        counts[label+'_ordered_fibre_checks'] += 1
    for p in POWERS:
        alpha = p-1
        for a, groups in by_count.items():
            d = 3**a
            lhs_hi = sum(power_bounds(d*len(nums), 1 << t, p)[1]
                         for _, nums in groups)
            rhs_lo = sum(power_bounds(num, 1 << t, alpha)[0]
                         for _, nums in groups for num in nums)
            assert Fraction(lhs_hi, d) <= p*Fraction(rhs_lo, 1 << t)
            counts[label+'_fractional_component_bounds'] += 1


def finite_periods(counts):
    rows, records = [], []
    for t in range(17):
        hist, fibres, selected = Counter(), defaultdict(list), defaultdict(list)
        moments = {eta: [0, 0] for eta in (Fraction(1, 4), Fraction(1, 2))}
        selected_moments = {eta: [0, 0] for eta in moments}
        for r in range(1 << t):
            x, a = direct(r, t)
            N = (1 << t)*x-3**a*r
            assert N >= 0
            num = 3**a+N
            hist[a] += 1
            fibres[a, x % 3**a].append(num)
            roots = {eta: power_bounds(num, 1 << t, eta) for eta in moments}
            for eta, (lo, hi) in roots.items():
                moments[eta][0] += lo
                moments[eta][1] += hi
            counts['direct_full_period_rows'] += 1
            if t and r % 2 == 0:
                returned = selected_return_at(r, t)
                counts['direct_adjacent_return_tests'] += 1
                if returned is not None:
                    ar, xr, D = returned
                    assert (ar, xr) == (a, x) and D > 0
                    selected[a, x % 3**a].append(num)
                    records.append((t, r, a, x, D, num))
                    for eta, (lo, hi) in roots.items():
                        selected_moments[eta][0] += lo
                        selected_moments[eta][1] += hi
                    counts['nonfused_even_return_prefixes'] += 1
        assert hist == Counter({a: comb(t, a) for a in range(t+1)})
        for z in (0, 1, 2, 3, 5, 11):
            assert sum(m*z**a for a, m in hist.items()) == (1+z)**t
            counts['exact_generating_polynomial_checks'] += 1
        assert sum(m*(2*a-t)**4 for a, m in hist.items()) == (3*t*t-2*t)*(1 << t)
        counts['centered_binomial_fourth_moments'] += 1
        # These safe fixed-clock constants follow from r_1/4<39/40,
        # r_1/2<31/32, and the additive moment term at most 1/2.
        assert 2*91**2 > 128**2 and 2*157**2 > 3*128**2
        assert 91+157 == 8*31
        assert moments[Fraction(1, 4)][1] <= 21*PRECISION*(1 << t)
        assert moments[Fraction(1, 2)][1] <= 17*PRECISION*(1 << t)
        component_bounds(t, fibres, counts, 'full')
        component_bounds(t, selected, counts, 'selected')
        rows.append({'clock': t, 'source_count': 1 << t,
                     'return_prefixes': sum(map(len, selected.values())),
                     'full_coefficient_moments': {
                         str(eta): enclosed(*value, PRECISION*(1 << t))
                         for eta, value in moments.items()},
                     'return_layer_coefficient_moments': {
                         str(eta): enclosed(*value, PRECISION*(1 << t))
                         for eta, value in selected_moments.items()}})
        print('Exact binary period and fractional fibre costs passed:', t, flush=True)
    return rows, records


def killed_return_budget(counts):
    H, eta = 14, Fraction(1, 4)
    population = 1 << H
    mass = Counter({0: population})
    moments = defaultdict(lambda: [0, 0])
    moments[0] = [population*PRECISION, population*PRECISION]
    for n in range(population):
        x, y, a, b, j = n, n+1, 0, 0, 0
        last_t, last_x, last_a, last_num = 0, n, 0, 1
        for t in range(1, H+1):
            a, b = a+(x & 1), b+(y & 1)
            x, y = step(x), step(y)
            if a != b:
                continue
            if x == y:
                break
            j += 1
            num = 3**a+(1 << t)*x-3**a*n
            delta_a, h = a-last_a, t-last_t
            correction = (1 << h)*x-3**delta_a*last_x
            assert correction >= 0
            assert num == 3**delta_a*last_num+(1 << last_t)*correction
            last_t, last_x, last_a, last_num = t, x, a, num
            lo, hi = power_bounds(num, 1 << t, eta)
            moments[j][0] += lo
            moments[j][1] += hi
            mass[j] += 1
            counts['direct_cumulative_return_compositions'] += 1
    rows = []
    for j in range(max(mass)+1):
        lo, hi = moments[j]
        next_hi = moments[j+1][1]
        assert 40*next_hi <= 39*lo+180*mass[j]*PRECISION
        counts['finite_killed_return_drift_checks'] += 1
        rows.append({'return_index': j, 'prefix_mass': rational(Fraction(mass[j], population)),
                     'coefficient_quarter_moment': enclosed(lo, hi, population*PRECISION)})
    total_lo = sum(value[0] for value in moments.values())
    total_hi = sum(value[1] for value in moments.values())
    assert total_hi <= 40*population*PRECISION+180*sum(mass.values())*PRECISION
    return {'clock_cap': H, 'source_count': population, 'rows': rows,
            'coefficient_budget_through_cap': enclosed(total_lo, total_hi, population*PRECISION),
            'scope': 'All initial parities; nonfused returns through the stated clock cap, including index zero. No infinite bound is inferred from this census.'}


def explicit_density(records, H):
    period = 3**H
    values = [0]*period
    for t, _, a, x, _, _ in records:
        if t <= H:
            d = 3**a
            weight = (1 << (H-t))*d
            for z in range(x % d, period, d):
                values[z] += weight
    return values


def finite_density_moments(records, counts):
    rows = []
    for H in (4, 6, 8, 9):
        values = explicit_density(records, H)
        expected_mass = sum(Fraction(1, 1 << t) for t, *_ in records if t <= H)
        assert Fraction(sum(values), len(values)*(1 << H)) == expected_mass
        row = {'clock_cap': H, 'ternary_period': len(values), 'moments': {}}
        for p in POWERS:
            bounds = [power_bounds(v, 1 << H, p) for v in values]
            row['moments'][str(p)] = enclosed(sum(lo for lo, _ in bounds),
                                             sum(hi for _, hi in bounds),
                                             len(values)*PRECISION)
            counts['direct_ternary_fractional_power_values'] += len(values)
        rows.append(row)
    return rows


def exponent_checks(counts):
    examples = []
    for d in range(2, 161):
        for n in range(d+1, (6*d+4)//5):
            p = Fraction(n, d)
            if p >= Fraction(6, 5):
                continue
            alpha = p-1
            threshold = alpha/(1-3*alpha)
            eta = (threshold+Fraction(1, 2))/2
            exponent = 3*alpha/2-Fraction(1, 2)+alpha/(2*eta)
            limiting = (5*alpha-1)/2
            assert 0 < alpha < threshold < eta < Fraction(1, 2)
            assert exponent < 0
            assert exponent-limiting == alpha*(1-2*eta)/(2*eta)
            assert (17*alpha-8)/p < -1
            counts['exact_dyadic_and_atypical_exponent_checks'] += 1
    for p in (Fraction(9, 8), Fraction(7, 6), Fraction(19, 16), Fraction(119, 100)):
        alpha = p-1
        eta = (alpha/(1-3*alpha)+Fraction(1, 2))/2
        exponent = 3*alpha/2-Fraction(1, 2)+alpha/(2*eta)
        examples.append({'power': rational(p), 'coefficient_moment': rational(eta),
                         'dyadic_power_before_pth_root': rational(exponent)})
    weighted = []
    for beta in (Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(3, 8)):
        for d in (32, 128, 512):
            gamma, p0 = Fraction(1, 2)-Fraction(1, d), Fraction(6, 5)-Fraction(1, d)
            theta = beta/gamma
            p = 1/(theta+(1-theta)/p0)
            assert 0 <= theta < 1 and 1 < p < 6/(5+2*beta)
            assert 1/p == theta+(1-theta)/p0
            counts['exact_weighted_exponent_checks'] += 1
            weighted.append({'separation_power': rational(beta), 'auxiliary_power': rational(gamma),
                             'base_power': rational(p0), 'density_power': rational(p)})
    return {'unweighted': examples, 'weighted': weighted}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-return-affine-') as directory:
        for source in SOURCES:
            obj = Path(directory)/(Path(source).stem+'.olean')
            log = OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(x in result.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {name for name, _ in roots} == {'ReturnAffineBudget.'+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': result.returncode,
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
    composition_checks(counts)
    print('Direct affine compositions and lifts passed.', flush=True)
    periods, records = finite_periods(counts)
    replay = {'binary_periods': periods, 'killed_return_budget': killed_return_budget(counts),
              'finite_ternary_moments': finite_density_moments(records, counts),
              'exponent_examples': exponent_checks(counts), 'counts': dict(counts),
              'fractional_enclosure_denominator': PRECISION,
              'finite_power_scope': 'p=3/2 is included only in finite moment and fibre checks; no infinite all-return claim is made at that exponent.'}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/RETURN-AFFINE-BUDGET.md', *PRIOR,
             'results/return-affine-budget/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'All-depth numerator and augmented-numerator composition, one-step recurrence, and source lifts.',
            'Parity-count generating-polynomial identities for every natural argument and depth.',
            'Finite natural-number drift-budget algebra after clearing denominators, and ordered augmented fibre cost.',
        ],
        'written_scope': [
            'Uniform fixed-clock fractional moments of the cumulative affine coefficient C=lambda+B for powers below one.',
            'Summable cumulative affine-coefficient moments at every nonfused return for powers below one half.',
            'Fractional fixed-count image-fibre inequality and binomial concentration of the full parity count.',
            'Atypical count components are Lp-summable; typical dyadic return blocks are Lp-summable for 1<p<6/5.',
            'All-return separation-weighted density is in Lp for 0<=beta<1/2 and 1<=p<6/(5+2*beta).',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in verification decisions.',
        'external_scope': 'No new external theorem. Prior written return-law, occupation-tail, and fibre-injection arguments are reused with authenticated records.',
        'not_proved': [
            'The endpoint p=6/(5+2*beta), optimal integrability, or full L2 integrability.',
            'Infinite-cutoff trace bounds on a fixed ordinary integer interval.',
            'Complementary power bounds for actual accumulated gradients or the required density-gradient pairing.',
            'Universal temporal criterion Q, a bounded actual-energy subsequence, escape exclusion, other-cycle exclusion, or full Collatz.',
        ],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: eight kernel roots and exact finite affine-budget checks; infinite Lp proof remains written and Collatz unresolved.', flush=True)


if __name__ == '__main__':
    main()
