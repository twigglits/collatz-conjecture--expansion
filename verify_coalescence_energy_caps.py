"""Check coalescence caps, the sharper linear bound, and gap/fusion mismatch.

Finite counts, kernel arithmetic, and written energy estimates have
different scopes. This does not certify bounded limiting energy.
"""
from array import array
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
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
OUT = ROOT / 'results/coalescence-energy-caps'
SOURCE = 'lean/CoalescenceEnergyCaps.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', SOURCE]
THEOREMS = [
    'balanced_add', 'balanced_later', 'refinement_data_equal',
    'refinement_cross_equal', 'even_period', 'even_block_count',
    'shell_count', 'cutoff_close', 'cutoff_decomposition', 'cutoff_block',
    'cutoff_remainders', 'tail_cutoff', 'six_first_return',
    'lifted_first_return', 'stopped_but_unmerged', 'cycle_pair',
    'six_never_balanced',
]
PRIOR = ['results/coalescence-tail/verification.json',
         'results/escape-weight-refinements/verification.json']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    return [x.numerator, x.denominator]


def direct(t, n):
    a = 0
    for _ in range(t):
        odd = n & 1
        a += odd
        n = (3*n+1)//2 if odd else n//2
    return n, a


def census(counts, depth=20):
    # Directly evolve every source 0..2^depth, without lifting residue data.
    limit = 1 << depth
    endpoints = array('Q', range(limit+1))
    odds = array('B', [0]) * (limit+1)
    old = json.loads((ROOT/'results/coalescence-tail/replay.json').read_text())['rows']
    rows = []
    for t in range(1, depth+1):
        for n in range(limit+1):
            x = endpoints[n]
            bit = x & 1
            y = (3*x+1)//2 if bit else x//2
            assert 0 <= y < 1 << 64  # No overflowing machine arithmetic.
            endpoints[n] = y
            odds[n] += bit
        counts['direct_shortcut_updates'] += limit+1
        balanced = [0, 0]
        for n in range(1 << t):
            if endpoints[n] == endpoints[n+1] and odds[n] == odds[n+1]:
                balanced[n & 1] += 1
        counts['direct_adjacent_residue_comparisons'] += 1 << t
        assert balanced == old[t-1]['balanced_coalescence_by_initial_parity']
        cap = Fraction((1 << (t-1))-balanced[0], 1 << t)
        assert Fraction(1, 2*t) <= cap <= Fraction(1, 2)
        assert Fraction(comb(t-1, (t-1)//2), 1 << t) <= cap
        rows.append({'depth': t, 'balanced_by_parity': balanced,
                     'even_pair_energy_cap': ratio(cap)})
        print('Independent direct coalescence census passed:', t, flush=True)
    return rows


def family_checks(counts):
    cases = [*range(4096), *[2**b+17 for b in (32, 64, 128, 256, 512, 1024, 2048)]]
    for q in cases:
        n = 2048*q+6
        x, y, a, b = n, n+1, 0, 0
        for t in range(1, 12):
            a += x & 1
            b += y & 1
            x = (3*x+1)//2 if x & 1 else x//2
            y = (3*y+1)//2 if y & 1 else y//2
            if t < 11:
                assert a != b
        assert (x, y, a, b) == (243*q+2, 243*q+1, 5, 5)
        counts['independent_lifted_first_returns'] += 1
    x, y, a, b = 6, 7, 0, 0
    for t in range(4096):
        assert not (x == y and a == b)
        a += x & 1
        b += y & 1
        x = (3*x+1)//2 if x & 1 else x//2
        y = (3*y+1)//2 if y & 1 else y//2
        counts['base_pair_nonfusion_times'] += 1


def energy_checks(counts, caps):
    offsets = (0, 7, 16, 32, 64, 128)
    rows = []
    for k in range(12):
        level = 1 << k
        defect = []
        for n in range(level, 2*level):
            defect.append(direct(k+1, 2*n) != direct(k+1, 2*n+1))
        assert Fraction(sum(defect), 2*level) == caps[k]
        for s in offsets:
            balanced_cells = 0
            for i, n in enumerate(range(level, 2*level)):
                x, a = direct(s+k, n)
                y, b = direct(s+k+1, 2*n+1)
                p, o = Fraction(3**a, (1 << s)*x), Fraction(3**b, (1 << s)*y)
                assert 0 < p <= 1 and 0 < o <= 1
                assert (o-p)**2 <= int(defect[i])
                if not defect[i]:
                    assert (x, a) == (y, b)
                    balanced_cells += 1
                counts['independent_rational_refinement_cells'] += 1
            rows.append({'level': k, 'offset': s, 'cells': level,
                         'zero_cells_certified_by_early_balance': balanced_cells,
                         'energy_cap': ratio(caps[k])})
        print('Rational refinement cap checks passed at level:', k, flush=True)
    return {'offsets': list(offsets), 'max_level': 11, 'rows': rows}


def bound_checks(counts, caps):
    B, q = sum(caps[:19], Fraction()), caps[19]
    T = Fraction(1, 2)*Fraction(1, 4)**19 + Fraction(21, 4)*Fraction(2, 3)**19
    assert B == Fraction(699653, 131072) and q == Fraction(234723, 1048576)
    slope = Fraction(121, 50)*q
    assert slope == Fraction(28401483, 52428800)
    assert B+q+T < 6
    for s in range(1024):
        J = (121*s+49)//50
        assert 121*s <= 50*J < 121*s+50
        assert 2**(3*s+J) <= 3**(s+J)
        assert J == 121*(s//50)+(121*(s%50)+49)//50
        counts['finite_cutoff_inequalities'] += 1
    lower_rows = []
    for s in range(257):
        lower = sum((Fraction(comb(k, k//2), 1 << (k+1)) for k in range(2*s+1)), Fraction())
        closed = Fraction((2*s+1)*comb(2*s, s), 4**s)-Fraction(1, 2)
        assert lower == closed
        counts['finite_walk_tail_sum_identities'] += 1
        if s in (0, 1, 4, 16, 64, 128, 256):
            lower_rows.append({'offset': s, 'certificate_lower_bound': ratio(lower)})
    return {'head_sum': ratio(B), 'cap_at_depth_20': ratio(q),
            'tail_constant': ratio(T), 'linear_coefficient': ratio(slope),
            'unrounded_additive_constant': ratio(B+q+T), 'rounded_additive_constant': 6,
            'certificate_lower_bound_examples': lower_rows,
            'scope': 'Lower bounds concern the cap-plus-tail certificate, never the actual energy.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-energy-caps-') as directory:
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
                assert {n for n, _ in found} == {'CoalescenceEnergyCaps.'+t for t in THEOREMS}
                for name, axioms in found:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': p.returncode,
                           'elapsed_seconds': round(time.monotonic()-start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Lean passed:', source, flush=True)
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
    rows = census(counts)
    caps = [Fraction(*r['even_pair_energy_cap']) for r in rows]
    family_checks(counts)
    replay = {'coalescence_rows': rows, 'energy_caps': energy_checks(counts, caps),
              'bounds': bound_checks(counts, caps), 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/COALESCENCE-ENERGY-CAPS.md',
             'docs/ESCAPE-WEIGHT-REFINEMENTS.md', 'docs/COALESCENCE-TAIL.md', *PRIOR,
             'results/coalescence-tail/replay.json', 'results/coalescence-energy-caps/replay.json',
             *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': validated,
        'kernel_scope': [
            'Balanced coalescence persists and annihilates the later refinement cross product.',
            'Exact periodic even-pair counts on dyadic source annuli at every eligible depth.',
            'All-offset integer cutoff inequality for ceil(121*s/50).',
            'An even-input residue class reaches equal odd counts without merging at time eleven.',
            'The base pair 6,7 is never balanced, although both starts reach the known cycle.',
        ],
        'written_scope': [
            'Each level energy is at most half its full-period even-pair noncoalescence fraction.',
            'Direct finite counts and the prior written tail give E_s <= (28401483/52428800)*s+6.',
            'The cap-plus-tail upper-bound certificate must diverge, at least harmonically by the kernel tail and at square-root order by the written walk comparison.',
            'These certificate lower bounds are not lower bounds on the actual energies.',
            'The exact signed drift identity exists as an ordinary partial-sum limit, without a claim of absolute convergence.',
        ],
        'finite_scope': dict(counts),
        'external_scope': 'No new external result adopted; no coalescence-density-one premise or passage premise used.',
        'not_proved': ['A bounded subsequence of E_s, or a bounded sequence of its Cesaro means.',
                       'No divergent orbit, exclusion of other positive cycles, or full Collatz.'],
        'sha256': {str(p): digest(ROOT/p) for p in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: coalescence energy caps; Collatz remains unresolved.', flush=True)


if __name__ == '__main__':
    main()
