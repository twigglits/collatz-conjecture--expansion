"""Exact all-future-time costs on finite Collatz source annuli.

Every sampled pair is directly checked to enter {1,2}; its remaining
infinite cost is then a geometric series with ratio 9/16. No such entry
is assumed for an untested source. Conditional energy criteria are written.
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
OUT = ROOT/'results/annulus-time-budgets'
SOURCE = 'lean/AnnulusTimeBudgets.lean'
SPINE_SOURCE = 'lean/BinaryConePredecessors.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', SOURCE,
           'lean/InverseFibreGrowth.lean', 'lean/UniformInverseBranching.lean', SPINE_SOURCE]
THEOREMS = ['cycle_step', 'cycle_two_steps', 'cycle_continuation',
            'cycle_count_comparison', 'cycle_weight_data', 'quadratic_geometric_identity']
SPINE_THEOREMS = ['child_error', 'spine_facts', 'spine_recurrence',
                  'spine_upper', 'spine_lower', 'binary_cone_closed']
AUDITS = {SOURCE: ('AnnulusTimeBudgets', THEOREMS),
          SPINE_SOURCE: ('BinaryConePredecessors', SPINE_THEOREMS)}
PRIOR = ['results/reversal-persistence/verification.json',
         'results/coalescence-energy-caps/verification.json',
         'results/escape-weight-refinements/verification.json',
         'results/binary-image-energy/verification.json',
         'results/uniform-inverse-branching/verification.json']
PRECISION = 1 << 96
DISPLAY_PRECISION = 1 << 64


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pair(x):
    x = Fraction(x)
    return [x.numerator, x.denominator]


def enclosure(lo, hi, denominator):
    lower = lo*DISPLAY_PRECISION//denominator
    upper = (hi*DISPLAY_PRECISION+denominator-1)//denominator
    return {'lower': pair(Fraction(lower, DISPLAY_PRECISION)),
            'upper': pair(Fraction(upper, DISPLAY_PRECISION))}


def add_ratio(acc, numerator, denominator):
    q, r = divmod(PRECISION*numerator, denominator)
    acc[0] += q
    acc[1] += q+bool(r)


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(n, t):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def complete_pair(x, y, scale, first, child_count, counts, exact=False):
    a, b, p, q, t, reversed_history = 0, child_count, 1, 3**child_count, 0, False
    energy, negative, charge = [0, 0], [0, 0], [0, 0]
    exact_energy, exact_negative = Fraction(0), Fraction(0)
    cycle_seen = None
    first_data = None

    def costs():
        delta = p*y-q*x
        denominator = (1 << (2*t))*x*x*y*y
        return scale*scale*delta*delta, (
            scale*scale*p*delta*y if reversed_history and delta > 0 else 0), denominator

    while True:
        if x <= 2 and y <= 2 and cycle_seen is None:
            assert x >= 1 and y >= 1
            cycle_seen = t
        if t == first:
            first_data = (x, y, a, b)
            A, Z = Fraction(scale*p, (1 << t)*x), Fraction(scale*p, (1 << t)*(x+1))
            budget = 3*A+2*Z
            add_ratio(charge, budget.numerator, budget.denominator)
        if cycle_seen is not None and t >= max(first, cycle_seen+2):
            break
        if t >= first:
            en, neg, den = costs()
            add_ratio(energy, en, den)
            add_ratio(negative, neg, den)
            if exact:
                exact_energy += Fraction(en, den)
                exact_negative += Fraction(neg, den)
            counts['exact_precycle_cost_terms'] += 1
        px, py = x & 1, y & 1
        a, b, p, q = a+px, b+py, p*3**px, q*3**py
        x, y, t = step(x), step(y), t+1
        reversed_history |= a > b
        assert t < 10000, 'No cycle entry certified within the finite verifier limit.'

    tail_clock = t
    tail = []
    old_flag = reversed_history
    for _ in range(4):
        assert x in (1, 2) and y in (1, 2)
        en, neg, den = costs()
        tail.append((Fraction(en, den), Fraction(neg, den)))
        px, py = x & 1, y & 1
        a, b, p, q = a+px, b+py, p*3**px, q*3**py
        x, y, t = step(x), step(y), t+1
        reversed_history |= a > b
        assert reversed_history == old_flag
    for j in (0, 1):
        for kind in (0, 1):
            assert 16*tail[j+2][kind] == 9*tail[j][kind]
            counts['exact_cycle_tail_ratio_checks'] += 1
    tail_energy = Fraction(16, 7)*(tail[0][0]+tail[1][0])
    tail_negative = Fraction(16, 7)*(tail[0][1]+tail[1][1])
    add_ratio(energy, tail_energy.numerator, tail_energy.denominator)
    add_ratio(negative, tail_negative.numerator, tail_negative.denominator)
    exact_values = None
    if exact:
        exact_energy += tail_energy
        exact_negative += tail_negative
        assert Fraction(energy[0], PRECISION) <= exact_energy <= Fraction(energy[1], PRECISION)
        assert Fraction(negative[0], PRECISION) <= exact_negative <= Fraction(negative[1], PRECISION)
        exact_values = {'energy': pair(exact_energy), 'reversed_negative': pair(exact_negative)}
        counts['independent_full_rational_sums'] += 1
    counts['pairs_with_certified_known_cycle_entry'] += 1
    return {'energy': energy, 'negative': negative, 'charge': charge,
            'tail_clock': tail_clock, 'first_data': first_data, 'exact': exact_values}


def moments(bounds):
    result = {}
    for p in (1, 2, 4, 8, 12):
        lo = sum(x[0]**p for x in bounds)
        hi = sum(x[1]**p for x in bounds)
        den = len(bounds)*PRECISION**p
        result[str(p)] = enclosure(lo, hi, den)
    return result


def annuli(counts):
    rows, witnesses = [], []
    for k in range(15):
        size = 1 << k
        energy, negative, charge = [0, 0], [0, 0], [0, 0]
        cell_energy, tail_clock = [], 0
        for n in range(size, 2*size):
            exact = n in (1, 37, 21845)
            cell = complete_pair(n, 3*n+2, size, k, 1, counts, exact)
            dx, da = direct(n, k)
            dy, db = direct(3*n+2, k)
            assert cell['first_data'] == (dx, dy, da, db+1)
            for target, key in ((energy, 'energy'), (negative, 'negative'), (charge, 'charge')):
                target[0] += cell[key][0]
                target[1] += cell[key][1]
            cell_energy.append(cell['energy'])
            tail_clock = max(tail_clock, cell['tail_clock'])
            if exact:
                witnesses.append({'level': k, 'source': n, 'tail_clock': cell['tail_clock'], **cell['exact']})
        divisor = 2*size*PRECISION
        assert energy[1] < 4*divisor
        assert negative[1]*4 < 5*divisor
        assert negative[1] <= charge[0]
        if k == 13:
            assert negative[0] > divisor
        counts['finite_all_time_annulus_bounds'] += 3
        row = {'level': k, 'source_interval': [size, 2*size],
               'latest_certified_tail_clock': tail_clock,
               'all_time_energy': enclosure(*energy, divisor),
               'all_time_reversed_negative': enclosure(*negative, divisor),
               'all_time_parent_loss': enclosure(*charge, divisor),
               'unhalved_cell_energy_moments': moments(cell_energy)}
        rows.append(row)
        print('Exact all-time annulus passed:', k,
              'energy/display', float(Fraction(sum(energy), 2*divisor)),
              'negative/display', float(Fraction(sum(negative), 2*divisor)), flush=True)
    return {'rows': rows, 'full_rational_witnesses': witnesses,
            'scope': 'All future offsets, but only the fifteen listed finite source annuli.'}


def returned_intervals(counts):
    rows = []
    for L in (0, 2, 4, 6, 8, 10):
        Q, M = 1 << L, 9*(1 << L)
        all_values, selected = [], []
        max_tail = 0
        # The actual interval associated with r=48 mod64, not a binary period.
        for x in range(M+8, 2*M+8):
            cell = complete_pair(x, x-1, M, L, 0, counts)
            all_values.append(cell['energy'])
            max_tail = max(max_tail, cell['tail_clock'])
            if x % 9 == 8:
                q = (x-8)//9
                assert Q <= q < 2*Q
                selected.append(cell['energy'])
                X, a = direct(32*q+24, L+5)
                Y, b = direct(3*(32*q+24)+2, L+5)
                rx, ra = direct(x, L)
                ry, rb = direct(x-1, L)
                assert X == rx and Y == ry and a == ra+2 and b+1 == rb+2
                counts['actual_returned_source_transport_checks'] += 1
        assert len(all_values) == M and len(selected) == Q
        # Multiplication by the column 9*1_(x=8 mod9) exactly gives the progression mean.
        for p in (1, 2, 4, 8, 12):
            for side in (0, 1):
                weighted = sum(9*v[side]**p for x, v in zip(range(M+8, 2*M+8), all_values) if x % 9 == 8)
                assert Q*weighted == M*sum(v[side]**p for v in selected)
                counts['exact_progression_interval_pairings'] += 1
        rows.append({'L': L, 'source_annulus': [64*Q, 128*Q],
                     'returned_interval': [M+8, 2*M+8], 'progression_size': Q,
                     'first_future_clock': L, 'latest_certified_tail_clock': max_tail,
                     'interval_moments': moments(all_values), 'progression_moments': moments(selected)})
        print('Exact all-time returned interval passed:', L, flush=True)
    return {'rows': rows, 'scope': 'Actual r=48 return progressions and containing intervals; full future sums after clock L. No uniform-in-L power bound is inferred.'}


def inverse_spine(counts):
    offsets = {1: 16, 2: 32, 4: 80, 5: 104, 7: 148, 8: 160}
    value, three, sixtyfour = 1, 1, 1
    witnesses, rows = {}, []
    covered_at = None
    for j in range(8193):
        assert value > 0 and value % 3 != 0
        assert 29*sixtyfour+32*three <= 61*three*value <= 61*sixtyfour
        counts['exact_inverse_spine_mass_bounds'] += 1
        bits = value.bit_length()
        for length in range(1, min(10, bits)+1):
            shift = bits-length
            prefix = value >> shift
            assert prefix*(1 << shift) <= value < (prefix+1)*(1 << shift)
            if prefix not in witnesses:
                witnesses[prefix] = {'prefix': prefix, 'spine_index': j, 'binary_shift': shift}
                counts['certified_binary_cone_witnesses'] += 1
        if len(witnesses) == 1023 and covered_at is None:
            covered_at = j
        if j <= 64 or j in (128, 256, 512):
            assert direct(value, 6*j) == (1, j)
            counts['independent_full_spine_trajectories'] += 1
        if j in (0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512):
            rows.append({'index': j, 'source_bits': bits, 'known_cycle_clock': 6*j,
                         'normalized_source': enclosure(three*value, three*value, sixtyfour)})
        if covered_at is not None and j >= 512:
            assert set(witnesses) == set(range(1, 1024))
            break
        nxt = 192*(value//9)+offsets[value % 9]
        error = 64*value-3*nxt
        assert 4 <= error <= 32
        assert direct(nxt, 6) == (value, 1)
        counts['independent_six_step_spine_links'] += 1
        value, three, sixtyfour = nxt, 3*three, 64*sixtyfour
    assert covered_at is not None
    print('Known-cycle inverse spine covers all binary prefixes 1..1023 by index:', covered_at, flush=True)
    return {'first_complete_prefix_coverage': covered_at, 'largest_checked_index': j,
            'rows': rows, 'binary_cone_witnesses': [witnesses[n] for n in range(1, 1024)],
            'scope': 'Exact finite cone witnesses and orbit links. Density in every binary cone is the separate written irrational-rotation argument, not extrapolation.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-annulus-time-') as directory:
        for source in SOURCES:
            obj, log = Path(directory)/(Path(source).stem+'.olean'), OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            started = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT,
                                  env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(proc.stdout)
            assert proc.returncode == 0, proc.stdout
            assert not any(x in proc.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source in AUDITS:
                namespace, theorems = AUDITS[source]
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", proc.stdout, re.M)
                assert len(roots) == len(theorems)
                assert {name for name, _ in roots} == {namespace+'.'+t for t in theorems}
                for name, axioms in roots:
                    assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': proc.returncode,
                           'elapsed_seconds': round(time.monotonic()-started, 3),
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
        if 'status' in record:
            assert record['status'] == 'passed'
        else:
            assert record['replay_summary']['all_checks_passed']
            assert all(c['returncode'] == 0 for c in record['commands'])
        for path, expected in record['sha256'].items():
            assert digest(ROOT/path) == expected, (prior, path)
        authenticated[prior] = len(record['sha256'])
    version, builds = build_lean()
    counts = Counter()
    replay = {'annuli': annuli(counts), 'returned_intervals': returned_intervals(counts),
              'inverse_spine': inverse_spine(counts),
              'precision_denominator': PRECISION, 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/ANNULUS-TIME-BUDGETS.md',
             'docs/ESCAPE-WEIGHT-REFINEMENTS.md', 'docs/ORDERED-WEIGHT-DRIFT.md',
             *PRIOR, 'results/annulus-time-budgets/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS)+len(SPINE_THEOREMS),
        'builds': builds, 'prior_hashes_validated': authenticated,
        'kernel_scope': ['Known-cycle closure and arbitrary even-step continuation.',
                         'Periodic count comparison, two-step weight data, and the finite geometric identity.',
                         'A convergent inverse spine with bounded affine errors, two-sided normalized growth bounds, and propagation of binary-child closure through every finite binary cone.'],
        'written_scope': ['Quadratic costs of a pair that has reached the known cycle have exact two-phase tails with ratio 9/16.',
                          'The inverse spine has dense binary significands and meets every binary cone, by its normalized positive limit and irrational rotation.',
                          'Sublinear reversed-drift time sums separately at every fixed source level would force nondecreasing limiting refinements, limiting energy at most 1/2, and zero limiting weights through the known-cycle binary-cone intersection.',
                          'A bounded lower Cesaro mean of the all-time annulus energy budgets would give a bounded Cesaro subsequence of actual offset energy.',
                          'The analogous averaged reversed-drift budget would also suffice, using the summable ordered contribution.'],
        'finite_scope': dict(counts),
        'floating_scope': 'Approximate console displays only; all verification decisions are integer or rational.',
        'external_scope': 'No external density or mixing theorem is needed for the qualitative temporal criterion. It uses the explicit inverse spine and the prior written weight/packing characterization. Irrational rotation and infinite limits remain written analysis.',
        'not_proved': ['Sublinear temporal reversed drift at every source level, any uniform all-annulus time budget, or a uniform complementary power norm.',
                       'Unbounded power norms or failure of a direct density-gradient pairing.',
                       'A bounded-energy subsequence, escape exclusion, other-cycle exclusion, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: exact all-time costs on finite annuli; the uniform budget and Collatz remain unresolved.', flush=True)


if __name__ == '__main__':
    main()
