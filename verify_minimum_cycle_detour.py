"""Verify positive inverse lifts of the negative seventeen cycle.

Strict general detours are materialized. The strict return-ladder subfamily
is symbolic: even its first exponent is too large to materialize its source.
No inverse optimum or universal convergence is inferred from these checks.
"""
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
OUT = ROOT / 'results/minimum-cycle-detour'
PRIOR = 'results/minimum-inverse-escape/verification.json'
NEW_SOURCE = 'lean/MinimumCycleDetour.lean'
THEOREMS = [
    'cycle_block', 'cycle_inverse', 'cycle_clock', 'detour_lift',
    'cycle_detour', 'detour_meeting', 'seventeen_gain', 'detour_smaller',
    'least_cycle_exclusion', 'odd_power_factor', 'cube_lift', 'ternary_lift',
    'ladder_divisibility', 'ladder_parameters', 'ladder_lift', 'ladder_smaller',
    'ladder_meeting', 'ladder_later_inverse', 'ladder_later_clock',
    'ladder_not_least', 'amplified_gain', 'amplified_detour',
    'ladder_arbitrary_gain', 'ladder_growth', 'least_orbit_cycle_bound',
    'ladder_old_detour_residue', 'arbitrarily_strong_ladder_detours',
    'finite_cycle_witness',
]
WORD = 'OOOOEOOOEEE'


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def ordinary(n, steps):
    values = [n]
    for _ in range(steps):
        x = values[-1]
        values.append(3*x+1 if x % 2 else x//2)
    return values


def shortcut_word(n, word, counts):
    """An independent traversal checks every prescribed input parity."""
    values = [n]
    for letter in word:
        x = values[-1]
        assert x > 0 and (x % 2 == 1) == (letter == 'O')
        if letter == 'O':
            values.extend([3*x+1, (3*x+1)//2])
        else:
            assert letter == 'E'
            values.append(x//2)
        counts['prescribed_shortcut_edges'] += 1
    return values


def inverse_word(b, word, counts):
    x = b
    for letter in word:
        if letter == 'E':
            x *= 2
        else:
            assert letter == 'O' and x % 3 == 2
            x = (2*x-1)//3
        assert x > 0
        counts['inverse_edges'] += 1
    return x


def valuation3(x):
    assert x > 0
    value = 0
    while x % 3 == 0:
        value += 1
        x //= 3
    return value


def general_replay(counts):
    for k in range(1, 65):
        for q in range(1, 129):
            p = 2**(11*k)*q-17
            y = 3**(7*k)*q-17
            values = ordinary(p, 18*k)
            assert values == shortcut_word(p, WORD*k, counts)
            assert values[-1] == y
            assert inverse_word(y, WORD[::-1]*k, counts) == p
            counts['cycle_lifts'] += 1
            counts['cycle_ordinary_edges'] += 18*k
            if q % 2:
                n = 3**(7*k-1)*q-6
                assert n > 0 and n % 2 and y == 3*n+1
                b = ordinary(n, 2)[-1]
                assert inverse_word(b, 'E'+WORD[::-1]*k, counts) == p
                assert ordinary(p, 18*k+1)[-1] == b
                counts['general_odd_detours'] += 1
                counts['meeting_ordinary_edges'] += 18*k+3
                if k >= 17:
                    assert 0 < p < n
                    counts['general_strict_detours'] += 1
    gains = [k for k in range(1, 65) if 2**(11*k) < 3**(7*k-1)]
    assert gains == list(range(17, 65))
    return {'complete_k_interval': [1, 64], 'complete_q_interval': [1, 128],
            'odd_source_detours': 'all odd q in that rectangle',
            'uniform_multiplier_gain_first_k_in_checked_range': 17,
            'scope': 'Actual positive paths with every parity and inverse guard checked. No minimal even-budget assertion.'}


def amplification_replay(counts):
    for g in range(65):
        k = 17*(g+1)
        for q in range(1, 34, 2):
            n = 3**(7*k-1)*q-6
            p = 2**(11*k)*q-17
            assert 0 < p and 3**g*p < n
            counts['amplification_arithmetic_checks'] += 1
            if g <= 12 and q <= 9:
                values = ordinary(p, 18*k)
                assert values == shortcut_word(p, WORD*k, counts)
                assert values[-1] == ordinary(n, 1)[-1]
                counts['amplified_actual_detours'] += 1
                counts['amplified_ordinary_edges'] += 18*k+1
    return {'arithmetic_g_interval': [0, 64], 'arithmetic_odd_q_interval': [1, 33],
            'actual_path_g_interval': [0, 12], 'actual_path_odd_q_interval': [1, 9],
            'scope': 'Large-index arithmetic and actual path replays have separate explicit ranges.'}


def ladder_replay(counts):
    rows = []
    # k=1 is deliberately below the strict-gain threshold. These actual
    # ladder prefixes check the construction, not strict ladder reduction.
    for h in range(5):
        R = 81*(2*h+1)
        X = 8**R
        n = X-5
        q = (X+1)//729
        p = 2048*q-17
        assert 729*q == n+6 and p > n
        values = ordinary(n, 5*R)
        assert values == shortcut_word(n, 'OOE'*R, counts)
        assert min(values) == n and values[-1] == 9**R-5
        assert [t for t, x in enumerate(values[:-1]) if x % 27 == 20] == [5*i+2 for i in range(1, R)]
        counts['actual_ladder_prefixes'] += 1
        counts['ladder_prefix_ordinary_edges'] += 5*R
        counts['ladder_target_visits'] += R-1
        for i in sorted({0, 1, 2, R//2, R-1}):
            b = (3*(9**i*8**(R-i)-5)+1)//2
            inverse = 'OEO'*i+'E'+WORD[::-1]
            assert inverse.count('E') == i+5 and inverse.count('O') == 2*i+7
            assert inverse_word(b, inverse, counts) == p
            actual = ordinary(p, 5*i+19)
            assert actual == shortcut_word(p, inverse[::-1], counts)
            assert actual[-1] == b == values[5*i+2]
            counts['actual_ladder_detours'] += 1
            counts['ladder_detour_ordinary_edges'] += 5*i+19
        rows.append({'k': 1, 'h': h, 'R': R, 'source_bits': n.bit_length(),
                     'predecessor_is_smaller': False})

    # These modular tests never construct 8^R for astronomical R.
    for k in range(1, 129):
        modulus = 3**(7*k-1)
        for h in range(9):
            R = 3**(7*k-3)*(2*h+1)
            assert R % 2 == 1 and pow(8, R, modulus) == modulus-1
            assert (pow(8, R+1, 27)-37) % 27 == 9
            counts['symbolic_ladder_modular_checks'] += 1
    for a in range(7):
        for h in range(9):
            R = 3**a*(2*h+1)
            X = 8**R
            assert valuation3(X+1) == a+2+valuation3(2*h+1)
            counts['materialized_ternary_valuation_checks'] += 1
    return {'materialized_ladder_prefixes': rows,
            'materialized_detour_indices': '0,1,2,floor(R/2),R-1 for each listed R',
            'modular_k_interval': [1, 128], 'modular_h_interval': [0, 8],
            'materialized_valuation_a_interval': [0, 6], 'materialized_valuation_h_interval': [0, 8],
            'first_strict_ladder_exponent': str(3**116),
            'scope': 'Strict ladder reductions (k>=17) are symbolic kernel theorems. Modular checks cover their congruences without constructing their sources. All materialized full ladder prefixes here have k=1 and their constructed predecessors are larger.'}


def convergence_replay(counts):
    rows = []
    for x, t in [(3**120-6, 1413), (9*2**187-17, 1718)]:
        values = ordinary(x, t)
        assert values[-1] == 1 and 1 not in values[:-1]
        # Independent accelerated-odd evaluation of the complete prefix.
        replay = [x]
        while len(replay) <= t:
            y = replay[-1]
            if y % 2:
                replay.append(3*y+1)
            else:
                replay.append(y//2)
                while len(replay) <= t and replay[-1] % 2 == 0:
                    replay.append(replay[-1]//2)
        assert replay == values
        counts['kernel_arrival_witnesses'] += 1
        counts['kernel_arrival_ordinary_edges'] += t
        rows.append({'source': str(x), 'source_bits': x.bit_length(), 'first_arrival': t})
    return {'rows': rows,
            'scope': 'Two explicit general-detour sources, not members of the strict ladder subfamily. Arrival existence is kernel checked; first-arrival minimality is Python.'}


def build(sources):
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-cycle-detour-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory)/(stem+'.olean')
            log = OUT/(stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS='1'))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool'))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == NEW_SOURCE:
                assert {n for n, _ in roots} == {stem+'.'+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                assert set(re.findall(r'^theorem (\w+)', (ROOT/source).read_text(), re.M)) == set(THEOREMS)
                assert f"'{stem}.finite_cycle_witness' does not depend on any axioms" in result.stdout
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': 0, 'fresh_build': True,
                           'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic()-start, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for path, expected in prior['sha256'].items():
        assert digest(ROOT/path) == expected, path
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [NEW_SOURCE]
    assert len(sources) == 30
    version, builds = build(sources)
    counts = Counter()
    sections = {}
    for name, check in [('general_cycle_lifts', general_replay),
                        ('amplification', amplification_replay),
                        ('return_ladder', ladder_replay), ('kernel_arrivals', convergence_replay)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources+[Path(__file__).name, 'docs/MINIMUM-CYCLE-DETOUR.md', PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
        'kernel_theorems_audited': len(THEOREMS), 'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': 'Positive lifts of the eleven-shortcut negative-seventeen cycle with four even and seven odd inputs per block. For odd n with 3^(7k-1)*q=n+6, the positive p=2^(11k)*q-17 coalesces with n at ordinary clocks 18k and 1; k>=17 makes p<n. For k=17(g+1), 3^g*p<n. A least orbit meeting such an odd n must have 3^g*A<n. For R=3^(7k-3)*(2h+1), n=8^R-5 has this detour, reaching every b_i at inverse counts i+4k+1 and 2i+7k. The arbitrary-source-size and arbitrary-gain existence theorem retains the actual growing ladder prefix. Old three-even detour coordinate is 9 mod27. Two finite arrival witnesses are axiom-free.',
        'written_scope': ['Interpretation as repeated positive lifts of the classical negative-seventeen cycle.',
                          'The k=17 least-source restriction is 3^118 not dividing n+6.',
                          'The first strict ladder exponent is R=3^116; its source is not materialized.',
                          'The prior written sharp-budget classification implies these ladder sources do not improve at budgets through i+3; no optimality claim for the new budget.'],
        'external_dependency': 'None for the new proofs. Bell-Lagarias (2015), page 101, was reviewed for the classical negative-cycle context only.',
        'finite_scope_limit': 'Strict general detours and k=1 ladder prefixes are distinct datasets. Strict ladder subfamilies are symbolic theorems plus modular replays, not a numerical trajectory census. No minimum is assigned to an unfinished orbit.',
        'not_proved': ['Convergence for every source in either parameterized family.',
                       'An optimal inverse budget or smaller predecessors for every least-source orbit.',
                       'A universal cap/residual estimate, exclusion of all nontrivial cycles, or full Collatz.'],
        'sha256': {p: digest(ROOT/p) for p in files}})
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS), 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
