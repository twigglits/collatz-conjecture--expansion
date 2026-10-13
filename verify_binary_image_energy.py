"""Kernel arithmetic and exact finite laws for binary image energy.

Haar analysis, infinite Lp interpolation, and return-tail consequences
remain written in docs/BINARY-IMAGE-ENERGY.md. No floating decisions.
"""
from collections import Counter, defaultdict
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
OUT = ROOT / 'results/binary-image-energy'
SOURCE = 'lean/BinaryImageEnergy.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean',
           'lean/CountReturnClock.lean', 'lean/ReturnCorrectionMoments.lean',
           'lean/OrderedWeightDrift.lean', 'lean/ReversalPersistence.lean',
           'lean/ReturnImageBounds.lean', SOURCE]
PRIOR = ['results/return-occupation-density/verification.json',
         'results/return-image-bounds/verification.json']
THEOREMS = ['total_const', 'numerator_mass', 'source_eq_of_numerator_eq',
            'numerator_image_residue', 'quotient_injective_on_fibre',
            'consecutive_mass', 'ranked_numerator_cost', 'image_cost_mass',
            'quadratic_norm_cap', 'cumulative_linear_mass',
            'cumulative_quadratic_cap']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, t):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def energy_numerator(nodes):
    """Integral of (sum_node w*3^a*1_residue)^2, exactly as an integer.

    Distinct ternary cylinders are disjoint unless one contains the other.
    Each off-diagonal pair is counted once from its deeper cylinder.
    """
    result = 0
    for (a, v), weight in nodes.items():
        result += 3**a*weight*weight
        for b in range(a):
            result += 2*weight*3**b*nodes.get((b, v % 3**b), 0)
    return result


def explicit_density(nodes, depth):
    period = 3**depth
    values = [0]*period
    for (a, v), weight in nodes.items():
        assert a <= depth and 0 <= v < 3**a
        for x in range(v, period, 3**a):
            values[x] += weight*3**a
    return values


def full_image_laws(counts):
    levels, rows = [], []
    # The frontier recurrence lifts the source at each new binary bit.
    frontier = [(0, 0, 0)]  # endpoint, count, affine numerator
    for t in range(17):
        nodes = Counter()
        fibres = defaultdict(list)
        seen_numerators = set()
        cube_mass, numerator_mass = 0, 0
        for r, (x, a, N) in enumerate(frontier):
            assert direct(r, t) == (x, a)
            assert N == (1 << t)*x-3**a*r >= 0
            assert a <= t and (a, N) not in seen_numerators
            seen_numerators.add((a, N))
            v = x % 3**a
            assert N % 3**a == ((1 << t)*v) % 3**a
            fibres[a, v].append(N)
            nodes[a, v] += 1
            cube_mass += 3**a
            numerator_mass += N
            counts['direct_full_period_source_checks'] += 1
        assert cube_mass == 4**t
        assert 4*numerator_mass == t*4**t
        assert 4*(cube_mass+numerator_mass) == (t+4)*4**t
        diagonal_numerator = 0
        for (a, v), nums in fibres.items():
            d, m = 3**a, len(nums)
            quotients = sorted(N//d for N in nums)
            assert len(set(quotients)) == m
            assert all(q >= j for j, q in enumerate(quotients))
            assert d*m*m <= 2*sum(d+N for N in nums)
            diagonal_numerator += d*m*m
            counts['injective_fibre_and_rank_checks'] += 1
        energy = energy_numerator(nodes)
        assert energy <= (t+1)*diagonal_numerator
        assert diagonal_numerator <= 2*(cube_mass+numerator_mass)
        assert 2*energy <= (t+1)*(t+4)*4**t
        assert energy <= (t+2)**2*4**t
        counts['complete_finite_quadratic_energy_checks'] += 1
        if t <= 8:
            values = explicit_density(nodes, t)
            assert sum(values) == 3**t*(1 << t)
            assert sum(x*x for x in values) == 3**t*energy
            counts['direct_ternary_energy_values'] += len(values)
            counts['independent_ternary_energy_cross_checks'] += 1
        rows.append({'clock': t, 'source_count': len(frontier),
                     'image_fibres': len(fibres),
                     'largest_fibre': max(map(len, fibres.values())),
                     'norm_squared': rational(Fraction(energy, 4**t)),
                     'proven_upper': rational(Fraction((t+1)*(t+4), 2))})
        levels.append(nodes)
        if t != 16:
            following = [None]*(2*len(frontier))
            for r, (x, a, N) in enumerate(frontier):
                for bit in (0, 1):
                    lifted = x+bit*3**a
                    parity = lifted & 1
                    following[r+bit*(1 << t)] = (
                        step(lifted), a+parity, 3**parity*N+(1 << t)*parity)
            frontier = following
    return levels, rows


def selected_return_at(n, t):
    """Direct adjacent trajectories, killed only at balanced fusion."""
    x, y, a, b = n, n+1, 0, 0
    for clock in range(1, t+1):
        a, b = a+(x & 1), b+(y & 1)
        x, y = step(x), step(y)
        if a == b and x == y:
            return None
    return (a, x, abs(x-y)) if a == b else None


def all_return_laws(levels, counts):
    rows, records = [], []
    for t in range(1, 17):
        layer = Counter()
        for r in range(0, 1 << t, 2):
            returned = selected_return_at(r, t)
            counts['independent_adjacent_source_trajectories'] += 1
            if returned is None:
                continue
            a, x, D = returned
            assert D > 0
            layer[a, x % 3**a] += 1
            records.append((t, r, a, x, D))
            counts['nonfused_return_prefixes'] += 1
        assert all(weight <= levels[t][node] for node, weight in layer.items())
        layer_energy = energy_numerator(layer)
        assert layer_energy <= energy_numerator(levels[t])
        cumulative = Counter()
        for clock, _, a, x, _ in records:
            cumulative[a, x % 3**a] += 1 << (t-clock)
        energy = energy_numerator(cumulative)
        assert 4*energy <= t*t*(t+5)**2*4**t
        assert energy <= 9*t**4*4**t
        counts['selected_layer_domination_checks'] += 1
        counts['all_return_quadratic_energy_checks'] += 1
        rows.append({'clock_cutoff': t, 'selected_prefixes_at_clock': sum(layer.values()),
                     'total_return_prefixes': len(records),
                     'occupation_mass': rational(Fraction(sum(cumulative.values()), 1 << t)),
                     'norm_squared': rational(Fraction(energy, 4**t))})
    return records, rows


def interval_and_column_checks(records, counts):
    rows = []
    for H in (6, 8, 10):
        period = 3**H
        columns = []
        for beta in (0, 1, 2):
            nodes = Counter()
            for t, _, a, x, D in records:
                if t <= H:
                    nodes[a, x % 3**a] += (1 << (H-t))*D**beta
            columns.append(explicit_density(nodes, H))
        for k0, k1, k2 in zip(*columns):
            assert k1*k1 <= k0*k2
            counts['exact_column_holder_values'] += 1
        for beta in (0, 1):
            for power in (2, 3):
                values = [x**power for x in columns[beta]]
                full = sum(values)
                for start in (0, 17, 10**12+39):
                    for length in (1, period-1, period, period+1, 2*period+17):
                        sampled = sum(values[(start+j) % period] for j in range(length))
                        assert period*sampled <= (length+period)*full
                        if length == period:
                            assert sampled == full
                        counts['periodic_integer_interval_power_checks'] += 1
        rows.append({'cutoff': H, 'period': period,
                     'scope': 'Finite integer powers only; beta=1,2 and p=2,3 are not claimed as infinite moment ranges.'})
    return rows


def exponent_checks(counts):
    examples = []
    for d in range(2, 101):
        for n in range(d+1, 2*d):
            p = Fraction(n, d)
            theta, eta = (2-p)/p, 2*(p-1)/p
            exponent = -theta/2+2*eta
            assert theta+eta == 1 and 0 < theta < 1 and 0 < eta < 1
            assert exponent == Fraction(9, 2)-5/p
            assert (exponent < 0) == (p < Fraction(10, 9))
            counts['exact_interpolation_exponent_checks'] += 1
    for beta in (Fraction(0), Fraction(1, 8), Fraction(1, 4), Fraction(3, 8)):
        limit_p = 10/(9+2*beta)
        for d in (16, 64, 256):
            gamma, p0 = Fraction(1, 2)-Fraction(1, d), Fraction(10, 9)-Fraction(1, d)
            if beta >= gamma:
                continue
            theta = beta/gamma
            p = 1/(theta+(1-theta)/p0)
            assert 1 < p < limit_p
            assert 1/p == theta+(1-theta)/p0
            counts['exact_weighted_exponent_checks'] += 1
            examples.append({'beta': rational(beta), 'gamma': rational(gamma),
                             'base_power': rational(p0), 'weighted_power': rational(p)})
    return examples


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-binary-image-') as directory:
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
                assert {name for name, _ in roots} == {'BinaryImageEnergy.'+t for t in THEOREMS}
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
    levels, full_rows = full_image_laws(counts)
    print('Full binary image laws, fibre injection, and exact L2 energies passed.', flush=True)
    records, occupation_rows = all_return_laws(levels, counts)
    print('Direct all-return layers and cumulative exact L2 energies passed.', flush=True)
    replay = {'full_image_laws': full_rows, 'all_return_laws': occupation_rows,
              'finite_interval_checks': interval_and_column_checks(records, counts),
              'weighted_exponent_examples': exponent_checks(counts), 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/BINARY-IMAGE-ENERGY.md',
             'docs/RETURN-OCCUPATION-DENSITY.md', *PRIOR,
             'results/binary-image-energy/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'At every depth, equal odd count and affine numerator identify a source within its binary period.',
            'Affine numerator quotient is injective on each fixed-count ternary image fibre.',
            'Ranked numerator cost, exact full-period numerator mass, combined cubic/numerator mass, and polynomial sum arithmetic.',
        ],
        'written_scope': [
            'Full depth-t image density has squared L2 norm at most (t+1)*(t+4)/2.',
            'All-return truncation through H has L2 norm at most H*(H+5)/2 <= 3*H^2.',
            'Existing all-return L1 clock tail plus dyadic interpolation gives K*_0 in Lp for 1<=p<10/9.',
            'Separation-weighted all-return density K*_beta is in Lp for 0<=beta<1/2 and 1<=p<10/(9+2*beta).',
            'Every finite logarithmic moment order follows for each beta<1/2.',
            'Integer interval pth means of the truncated density are bounded by (1+3^H/M) times the full Haar pth moment.',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in verification decisions.',
        'external_scope': 'Quotient-counting idea credited to Valbuena; no external stationary theorem or mixing result is used. Existing written project occupation bounds are reused.',
        'not_proved': [
            'The endpoint p=10/(9+2*beta), optimal integrability, or full L2 integrability.',
            'Infinite-cutoff sampling bounds on a fixed ordinary integer interval.',
            'A uniform complementary power norm for actual accumulated gradients or the required density-gradient pairing.',
            'A bounded actual-energy subsequence, escape exclusion, other-cycle exclusion, or full Collatz.',
        ],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: kernel and exact finite image energy checks; infinite Lp analysis remains written and Collatz unresolved.', flush=True)


if __name__ == '__main__':
    main()
