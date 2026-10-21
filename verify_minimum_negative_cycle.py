"""Verify positive detours lifted from the negative magnitude-17 cycle.

Kernel theorems, explicit positive paths, modular tests at enormous exponents,
and first-arrival checks have separate recorded scopes. No range-convergence
claim or optimal inverse-budget claim is made.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-negative-cycle'
PRIOR = 'results/minimum-inverse-escape/verification.json'
NEW_SOURCE = 'lean/MinimumNegativeCycle.lean'
NOTE = 'docs/MINIMUM-NEGATIVE-CYCLE.md'
THEOREMS = [
    'cycle_block', 'cycle_repeated', 'cycle_clock', 'meeting_inverse',
    'meeting_clock', 'seventeen_gain', 'power_gain', 'meeting_smaller',
    'least_no_lift', 'least_residue_exclusion', 'finite_gain_threshold',
    'earlier_cycles_larger', 'repeated_gain', 'meeting_improvement', 'meeting_factor_smaller',
    'cube_divisibility', 'ternary_lift', 'odd_power_divisibility',
    'ladder_exponent', 'ladder_divisibility', 'ladder_source_lift',
    'residue_detour', 'ladder_escape', 'ladder_not_least', 'ladder_growth',
    'finite_positive_witness',
]
AXIOM_FREE = ['seventeen_gain', 'finite_gain_threshold', 'finite_positive_witness']
INVERSE_CYCLE = 'EEEOOOEOOOO'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def ordinary(n, t):
    values = [n]
    for _ in range(t):
        x = values[-1]
        values.append(3*x+1 if x % 2 else x//2)
    return values


def paired(n, t):
    values = [n]
    while len(values) <= t:
        x = values[-1]
        if x % 2:
            values.append(3*x+1)
            if len(values) <= t:
                values.append((3*x+1)//2)
        else:
            values.append(x//2)
    return values


def inverse(b, word, counts):
    x = b
    for letter in word:
        if letter == 'E':
            x *= 2
        else:
            assert letter == 'O' and x % 3 == 2
            x = (2*x-1)//3
        assert x > 0
        counts['positive_inverse_edges'] += 1
    return x


def cycle_replay(counts):
    x = -17
    signed = [x]
    word = ''
    for _ in range(11):
        word += 'O' if x % 2 else 'E'
        x = (3*x+1)//2 if x % 2 else x//2
        signed.append(x)
    assert x == -17 and word[::-1] == INVERSE_CYCLE
    assert word.count('E') == 4 and word.count('O') == 7
    assert ordinary(-17, 18)[-1] == -17
    counts['negative_shortcut_steps'] = 11
    counts['negative_ordinary_steps'] = 18
    for q in range(1, 1025):
        p, b = 2048*q-17, 2187*q-17
        path = ordinary(p, 18)
        assert path == paired(p, 18) and path[-1] == b
        assert inverse(b, INVERSE_CYCLE, counts) == p
        counts['single_block_positive_lifts'] += 1
        counts['single_block_ordinary_steps'] += 18
    return {'negative_shortcut_path': signed, 'forward_word': word,
            'inverse_word': INVERSE_CYCLE, 'q_interval': [1, 1024],
            'scope': 'The negative cycle motivates a word; each listed positive lift is separately replayed with positive values and legal inverse guards.'}


def check_detour(k, q, counts, label):
    n = 3**(7*k-1)*q-6
    p = 2**(11*k)*q-17
    assert k >= 1 and q > 0 and q % 2 == 1 and n % 2 == 1
    b = ordinary(n, 2)[-1]
    word = 'E' + INVERSE_CYCLE*k
    assert word.count('E') == 4*k+1 and word.count('O') == 7*k
    assert inverse(b, word, counts) == p
    path = ordinary(p, 18*k+1)
    assert path == paired(p, 18*k+1) and path[-1] == b
    assert (p < n) == (k >= 17) and p != n
    assert n % 729 == 723
    counts[label+'_paths'] += 1
    counts[label+'_ordinary_steps'] += 18*k+3
    if p < n:
        counts[label+'_smaller_paths'] += 1
    return n, p


def detour_replay(counts):
    for k in range(1, 65):
        for q in range(1, 64, 2):
            check_detour(k, q, counts, 'rectangle')
    rows = []
    for k in [17, 34, 68, 136, 272]:
        for q in [1, 3, 17]:
            n, p = check_detour(k, q, counts, 'large')
            rows.append({'k': k, 'q': q, 'source_bits': n.bit_length(),
                         'predecessor_bits': p.bit_length(),
                         'ordinary_clock': 18*k+1})
    for k in range(1, 17):
        assert 2187**k+33 < 3*2048**k
        counts['threshold_lower_checks'] += 1
    assert 3*2048**17 < 2187**17
    counts['threshold_upper_checks'] = 1
    for h in range(129):
        assert 3**h * 2048**(17*h) <= 2187**(17*h)
        k = 17*(h+1)
        for q in [1, 3, 17]:
            n = 3**(7*k-1)*q-6
            p = 2048**k*q-17
            assert 3**h*(p+17) <= n+6
            assert 3**h*p < n
            counts['improvement_arithmetic_checks'] += 1
        counts['repeated_gain_arithmetic_checks'] += 1
    return {'complete_k_interval': [1, 64], 'complete_odd_q_interval': [1, 63],
            'larger_path_rows': rows, 'gain_h_interval': [0, 128],
            'threshold_scope': 'Seventeen repetitions are sharp for this specific E-plus-cycle word, not for all legal inverse words.',
            'gain_scope': 'Large-h improvement checks are arithmetic; only the rectangle and listed larger rows replay full positive paths.'}


def divisibility_replay(counts):
    # Small exponents are materialized. The enormous family is modular only.
    for s in range(10):
        exponent = 3**s
        value = 8**exponent+1
        assert value % 3**(s+2) == 0
        for h in range(9):
            assert pow(8, exponent*(2*h+1), 3**(s+2)) == 3**(s+2)-1
            counts['small_odd_multiple_checks'] += 1
        counts['materialized_ternary_lifts'] += 1
    for s in range(257):
        modulus = 3**(s+2)
        assert pow(8, 3**s, modulus) == modulus-1
        counts['modular_ternary_lifts'] += 1
    for h in range(1025):
        R = 3**116*(2*h+1)
        assert R % 2 == 1 and R >= 3 and h < R
        assert pow(8, R, 3**118) == 3**118-1
        assert R % 162 != 85
        # A residue comparison, not materialization of 8**R.
        assert (pow(8, R, 729)-5) % 729 == 723
        counts['modular_ladder_progression_checks'] += 1
    return {'materialized_s_interval': [0, 9], 'modular_s_interval': [0, 256],
            'modular_progression_h_interval': [0, 1024],
            'minimum_R': 3**116, 'minimum_ladder_source_bit_length': 3**117,
            'scope': 'No positive source 8**R-5 from the new progression is materialized or numerically iterated. Its paths for every visit are parameterized kernel theorems. Modular arithmetic checks only the stated divisibility and disjointness from the old progression.'}


def arrival_replay(counts):
    rows = []
    for n, t in [(3**118-6, 1247), (2**187-17, 1552)]:
        path = ordinary(n, t)
        assert path == paired(n, t) and path[-1] == 1 and 1 not in path[:-1]
        counts['kernel_arrival_witnesses'] += 1
        counts['arrival_ordinary_steps'] += t
        rows.append({'source': n, 'bits': n.bit_length(), 'first_arrival': t,
                     'peak_bits': max(path).bit_length()})
    return {'rows': rows,
            'scope': 'Arrival existence is separately kernel checked. First-arrival minimality and peak sizes are Python checks. These are general residue-class examples, not members of the enormous return-ladder progression.'}


def build(sources, lean):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version, version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-negative-cycle-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory) / (stem+'.olean')
            log = OUT / (stem+'.log')
            command = [lean, '-o', str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == NEW_SOURCE:
                assert {n for n, _ in roots} == {stem+'.'+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                source_text = (ROOT/source).read_text()
                assert set(re.findall(r'^theorem (\w+)', source_text, re.M)) == set(THEOREMS)
                assert not re.search(r'\b(sorry|native_decide|axiom)\b', source_text)
                for theorem in AXIOM_FREE:
                    assert f"'{stem}.{theorem}' does not depend on any axioms" in result.stdout
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': 0, 'fresh_build': True,
                           'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic()-started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean', help='Lean executable; must match the repository pin')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, h in prior['sha256'].items():
        assert digest(ROOT/name) == h, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [NEW_SOURCE]
    assert len(sources) == 30 and len(set(sources)) == 30
    version, builds = build(sources, args.lean)
    counts = Counter()
    sections = {}
    for name, check in [('cycle_lifts', cycle_replay), ('positive_detours', detour_replay),
                        ('ternary_lifts', divisibility_replay), ('kernel_arrivals', arrival_replay)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources + [Path(__file__).name, NOTE, PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
        'kernel_theorems_audited': len(THEOREMS), 'axiom_free_roots': AXIOM_FREE,
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'For all k,q>0, the inverse word (EEEOOOEOOOO)^k joins 2187^k*q-17 to 2048^k*q-17, with 4k even and 7k odd operations.',
            'For odd n and 2187^k*q=3n+18, prefixing E gives coalescence at ordinary clocks 18k+1 and 2. For k>=17 the positive predecessor is smaller. Earlier k<17 are larger for this specified word.',
            'A least counterexample cannot have 3^118 dividing n+6. For k=17(h+1), the shifted predecessor obeys 3^h*(p+17)<=n+6.',
            'For R=3^116*(2h+1), N=8^R-5 has a smaller predecessor at all return-ladder targets b_i, using i+69 even and 2i+119 odd operations, at ordinary clock 5i+307. Such N is not a least counterexample and the sources are unbounded.',
            'Ternary lifting and odd-multiple divisibility are parameterized kernel proofs. Two explicit positive arrival witnesses use kernel reduction only.',
        ],
        'written_scope': [
            'Combining the new progression with the preceding written classification shows that i+3 even operations still have minimum N, whereas i+69 suffice to improve it. The true minimum required budget is not identified.',
            'The general residue-class examples are distinct from the return-ladder family. The minimum bit length 3^117 of the latter is an arithmetic interpretation, not a stored integer trajectory.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 was downloaded from its official release to /tmp, preserving the repository pin and historical manifests.',
        'finite_scope_limit': 'All replays have explicit finite ranges. Enormous ladder sources are checked symbolically in Lean and only modularly in Python. First-arrival minimality is Python, separate from kernel arrival existence.',
        'not_proved': ['Optimal inverse even budget for the new progression.',
                       'A fixed extra budget sufficient for every return-ladder source or every least-source orbit.',
                       'Universal convergence of the residue class or return-ladder progression.',
                       'The cap/residual bounds, exclusion of all nontrivial cycles or divergence, or the full Collatz conjecture.'],
        'sha256': {p: digest(ROOT/p) for p in files}})
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS), 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
