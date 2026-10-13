"""Exact checks for return-image prefix weights and finite interval sampling.

Haar logarithmic moments and all infinite probability assertions are written
arguments. The finite integer-power checks do not assert those infinite moments.
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
OUT = ROOT / 'results/return-image-bounds'
SOURCE = 'lean/ReturnImageBounds.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/OrderedWeightDrift.lean',
           'lean/ReversalPersistence.lean', SOURCE]
PRIOR = ['results/count-return-clock/verification.json',
         'results/annulus-height-coupling/verification.json',
         'results/reversal-persistence/verification.json']
THEOREMS = ['cubic_children', 'cubic_mass', 'column_le_tilted', 'tilted_kraft',
            'column_numerator_bound', 'binary_kraft', 'prefix_endpoint_bound',
            'equal_count_distance_bound', 'image_lift', 'residue_count_zero',
            'residue_count_discrepancy', 'residue_count_full_period']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def rational(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(t, n):
    a, word = 0, ''
    for _ in range(t):
        parity = n & 1
        a += parity
        word += str(parity)
        n = step(n)
    return n, a, word


def cubic_checks(counts):
    rows = []
    for t in range(15):
        mass = 0
        for n in range(1 << t):
            x, a, _ = direct(t, n)
            assert x < 2*3**a
            mass += 3**a
            a0 = direct(t+1, n)[1]
            a1 = direct(t+1, (1 << t)+n)[1]
            assert 3**a0+3**a1 == 4*3**a
            counts['actual_cubic_child_and_endpoint_checks'] += 1
        assert mass == 4**t
        counts['exact_cubic_period_masses'] += 1
        rows.append({'depth': t, 'cubic_mass': mass})
    return rows


def insert_word(tree, word):
    for c in word:
        assert 'stop' not in tree
        tree = tree.setdefault(c, {})
    assert not tree
    tree['stop'] = True


def tree_numerators(tree, h):
    if 'stop' in tree:
        return 2**h, 4**h, 2**h
    if h == 0:
        return 0, 0, 0
    even = tree_numerators(tree.get('0', {}), h-1)
    odd = tree_numerators(tree.get('1', {}), h-1)
    return even[0]+3*odd[0], even[1]+3*odd[1], even[2]+odd[2]


def first_returns(counts):
    # Even first input. Finite prefix lifts expose higher source bits.
    live = [(0, 0, 2, 0, 1)]
    selected, rows = [], []
    for t in range(1, 18):
        nxt = []
        for r, x, y, a, b in live:
            assert a < b
            for bit in (0, 1):
                R = r+bit*(1 << t)
                X, Y = x+bit*3**a, y+bit*3**b
                A, B = a+(X & 1), b+(Y & 1)
                X, Y = step(X), step(Y)
                counts['first_return_prefix_tree_edges'] += 1
                if A == B:
                    assert X >= Y
                    counts['all_first_return_prefixes'] += 1
                    if X != Y:
                        H, D = t+1, X-Y
                        dx, da, word = direct(H, R)
                        dy, db, _ = direct(H, R+1)
                        assert (dx, dy, da, db) == (X, Y, A, B)
                        assert all(direct(j, R)[1] != direct(j, R+1)[1] for j in range(1, H))
                        assert R % 2 == 0 and R+1 < 1 << H
                        assert X < 2*3**A and Y < 2*3**A and 0 < D < 2*3**A
                        selected.append({'tau': H, 'r': R, 'a': A,
                                         'x': X, 'y': Y, 'D': D, 'word': word})
                        counts['nonfused_first_return_prefixes'] += 1
                else:
                    assert A < B
                    nxt.append((R, X, Y, A, B))
        live = nxt
        H, tree = t+1, {}
        for p in selected:
            insert_word(tree, p['word'])
        column, tilted, binary = tree_numerators(tree, H)
        assert column == sum(3**p['a']*2**(H-p['tau']) for p in selected)
        assert tilted == sum(3**p['a']*4**(H-p['tau']) for p in selected)
        assert binary == sum(2**(H-p['tau']) for p in selected)
        assert column <= tilted <= 4**H
        assert binary <= 2**(H-1)
        for power in (0, 1, 2):
            weighted = sum(3**p['a']*p['D']**power*2**(H-p['tau']) for p in selected)
            assert weighted <= 2**H*2**power*(2*3**power)**H
            counts['finite_integer_power_column_bounds'] += 1
        counts['exact_prefix_tree_identities'] += 1
        rows.append({'depth': H, 'nonfused_prefix_count': len(selected),
                     'binary_mass': rational(Fraction(binary, 2**H)),
                     'multiplier_sum': rational(Fraction(column, 2**H)),
                     'tilted_mass': rational(Fraction(tilted, 4**H))})
    print('Exact first-return trees, tilted prefix bounds, and endpoint caps passed.', flush=True)
    return selected, rows


def floor_count(start, length, period, residue):
    assert 0 <= residue < period
    shift = period-1-residue
    return (start+length+shift)//period-(start+shift)//period


def residue_checks(counts):
    for period in [*range(1, 33), 81, 243, 729]:
        residues = range(period) if period <= 32 else (0, 1, period//2, period-1)
        for residue in residues:
            for start in (0, 1, period-1, period, period+1, 2*period+17, 10**9+3):
                for length in (0, 1, 2, period-1, period, period+1, 2*period+3, 4*period+7):
                    actual = sum(n % period == residue for n in range(start, start+length))
                    result = floor_count(start, length, period, residue)
                    assert result == actual
                    assert abs(period*result-length) < period
                    if length == period:
                        assert result == 1
                    counts['direct_interval_residue_counts'] += 1


def projected_density(prefixes, H, L):
    values = [0]*(3**L)
    for p in prefixes:
        if p['tau'] > H:
            continue
        a = min(p['a'], L)
        period = 3**a
        coefficient = period*2**(H-p['tau'])
        for r in range(p['x'] % period, len(values), period):
            values[r] += coefficient
    return values


def density_checks(prefixes, counts):
    H = 14
    selected = [p for p in prefixes if p['tau'] <= H]
    maximum_a = max(p['a'] for p in selected)
    period, denominator = 3**maximum_a, 2**H
    values = projected_density(selected, H, maximum_a)
    binary = sum(2**(H-p['tau']) for p in selected)
    assert sum(values) == period*binary
    previous, rows = None, []
    for L in range(maximum_a+1):
        projection = projected_density(selected, H, L)
        assert sum(projection) == 3**L*binary
        if previous is not None:
            assert all(3*previous[r] == projection[r]+projection[r+3**(L-1)]+
                       projection[r+2*3**(L-1)] for r in range(3**(L-1)))
        difference = sum(abs(values[r]-projection[r % (3**L)]) for r in range(period))
        tail_a = sum(2**(H-p['tau']) for p in selected if p['a'] > L)
        tail_t = sum(2**(H-p['tau']) for p in selected if p['tau'] > L)
        assert difference <= 2*period*tail_a <= 2*period*tail_t
        counts['exact_ternary_projection_comparisons'] += 1
        counts['ternary_residues_compared'] += period
        rows.append({'projection_depth': L,
                     'L1_difference': rational(Fraction(difference, denominator*period)),
                     'twice_odd_count_tail_mass': rational(Fraction(2*tail_a, denominator))})
        previous = projection
    return {'return_cutoff': H, 'full_ternary_period': period,
            'density_mass': rational(Fraction(binary, denominator)), 'projections': rows}


def interval_checks(prefixes, counts):
    rows = []
    for H in (6, 10, 14, 18):
        selected = [p for p in prefixes if p['tau'] <= H]
        for power in (0, 1):
            mass = sum(p['D']**power*2**(H-p['tau']) for p in selected)
            column = sum(3**p['a']*p['D']**power*2**(H-p['tau']) for p in selected)
            for start in (0, 1, 97, 10**6+7, 10**12+19):
                for length in (1, 17, 257, 4096):
                    values = [0]*length
                    floor_area = 0
                    for p in selected:
                        period = 3**p['a']
                        coefficient = period*p['D']**power*2**(H-p['tau'])
                        floor_area += coefficient*floor_count(start, length, period, p['x'] % period)
                        first = (p['x']-start) % period
                        for j in range(first, length, period):
                            values[j] += coefficient
                    area = sum(values)
                    assert area == floor_area
                    error = abs(area-length*mass)
                    assert error <= column <= 2**H*2**power*(2*3**power)**H
                    counts['direct_truncated_density_interval_checks'] += 1
                    counts['integer_density_values_summed'] += length
                    if power == 0 and start == 10**12+19:
                        rows.append({'clock_cutoff': H, 'interval_start': start,
                                     'interval_length': length,
                                     'integer_mean': rational(Fraction(area, length*2**H)),
                                     'Haar_mean': rational(Fraction(mass, 2**H)),
                                     'absolute_error': rational(Fraction(error, length*2**H)),
                                     'unweighted_error_bound': rational(Fraction(2**H, length))})
    print('Exact ternary projections and finite integer sampling bounds passed.', flush=True)
    return {'selected_unweighted_intervals': rows,
            'scope': 'Powers zero and one test finite weighted counting algebra only; no infinite first separation moment is claimed.'}


def logarithmic_constant_checks(counts):
    assert 2*5**4 < 6**4
    assert 2*2**2 < 3**2
    assert 20**4 < 2*17**4
    assert 4*10**4 < 3*11**4
    assert Fraction(6, 5)+7*Fraction(3, 2)*Fraction(20, 3) == Fraction(356, 5)
    assert Fraction(356, 5)*Fraction(11, 10) == Fraction(3916, 50) < 80
    assert Fraction(29, 9) > 3 and 80+Fraction(11, 10) < 82
    counts['exact_logarithmic_constant_comparisons'] += 7
    return {'logarithmic_power': [1, 4], 'Haar_moment_upper': 80,
            'finite_interval_moment_upper': 82,
            'finite_interval_condition': '2^H*(H+1)<=M',
            'scope': 'Integer/rational comparisons checked; exponential, logarithm, and Jensen applications are written.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-return-image-') as directory:
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
                assert {name for name, _ in roots} == {'ReturnImageBounds.'+t for t in THEOREMS}
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
    replay = {'cubic_periods': cubic_checks(counts)}
    prefixes, replay['first_return_prefixes'] = first_returns(counts)
    residue_checks(counts)
    replay['ternary_densities'] = density_checks(prefixes, counts)
    replay['finite_integer_intervals'] = interval_checks(prefixes, counts)
    replay['logarithmic_constants'] = logarithmic_constant_checks(counts)
    replay['counts'] = dict(counts)
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/RETURN-IMAGE-BOUNDS.md',
             'docs/COUNT-RETURN-CLOCK.md', 'docs/ANNULUS-HEIGHT-COUPLING.md',
             *PRIOR, 'results/return-image-bounds/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': authenticated,
        'kernel_scope': [
            'Cubic child and full-period masses; ordinary and tilted prefix-tree bounds and multiplier numerator cap.',
            'All-prefix endpoint and equal-count separation caps and exact endpoint image lift.',
            'Integer residue floor counter, its interval discrepancy, and full-period count.',
        ],
        'written_scope': [
            'Joint first-return moment sum p_i D_i^beta (1+tau_i)^alpha is finite when beta>=0, alpha>0, and 3beta+2alpha<1.',
            'Separation-weighted image density K_beta lies in L(log L)^alpha under ternary Haar probability in that range.',
            'Quantitative Haar absolute continuity, clock truncation rate, and coarse-cylinder L1 approximation.',
            'Finite integer interval mean error <=2^beta*(2*3^beta)^H/M for truncated image coefficients.',
            'Logarithmic density moment transfers to finite integer intervals with the explicitly retained depth/length error.',
            'Unweighted logarithmic quarter-moment is <80 under Haar, and <82 on finite integer intervals when 2^H*(H+1)<=M.',
        ],
        'finite_scope': dict(counts), 'floating_scope': 'None in this verification.',
        'external_scope': 'No new external theorem. Earlier written first-return clock and separation moments are reused.',
        'not_proved': ['An L^p bound with p>1 or a bounded essential supremum for the full image density.',
                       'Control of the full untruncated density on individual integer traces.',
                       'A uniform comparison for actual weighted progression gradients or bounded actual energy.',
                       'Escape exclusion, exclusion of additional cycles, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: return-image moments and finite sampling inputs; weighted energy and Collatz remain open.', flush=True)


if __name__ == '__main__':
    main()
