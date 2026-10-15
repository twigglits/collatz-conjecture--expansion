"""Audit a smaller-source detour beyond the return ladder's inverse budget.

Kernel paths and companion bounds, the written sharp-budget classification,
finite inverse searches, and explicit convergence witnesses retain separate scopes.
"""
from collections import Counter, defaultdict
from datetime import datetime, timezone
from functools import lru_cache
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/minimum-inverse-escape'
PRIOR = 'results/minimum-return-ladder/verification.json'
NEW_SOURCE = 'lean/MinimumInverseEscape.lean'
THEOREMS = [
    'odd_meeting', 'three_even_detour', 'pure_inverse', 'detour_predecessor',
    'detour_clock', 'six_power_gain', 'detour_smaller', 'least_detour_exclusion',
    'least_not_273_mod_729', 'hit_to_initial', 'family_exponent',
    'family_congruence', 'family_lift', 'family_source', 'family_smaller',
    'family_coalescence', 'family_later_inverse', 'family_later_clock',
    'family_not_least', 'family_growth', 'shadow_actual', 'truncated_companion',
    'before_escape_lower', 'smaller_requires_escape', 'escape_frontier',
    'finite_negative_cycles', 'finite_escape_witness',
]


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


def inverse_path(b, word, counts, prefix):
    x = b
    for step in word:
        if step == 'E':
            x *= 2
        else:
            assert step == 'O' and x % 3 == 2
            x = (2*x-1)//3
        assert x > 0
        counts[prefix+'_inverse_edges'] += 1
    return x


def valuation3(x):
    assert x > 0
    j = 0
    while x % 3 == 0:
        x //= 3
        j += 1
    return j, x


def block(R, i):
    return 9**i * 8**(R-i) - 5


def hit(R, i):
    return (3*block(R, i)+1)//2


def inverse_minimum(counts):
    @lru_cache(None)
    def minimum(b, r):
        counts['minimum_inverse_states'] += 1
        if b % 3 == 0:
            return b
        pure = [b]
        while pure[-1] % 3 == 2:
            pure.append((2*pure[-1]-1)//3)
            counts['minimum_odd_edges'] += 1
        best = pure[-1]
        if r:
            for x in pure:
                counts['minimum_even_edges'] += 1
                best = min(best, minimum(2*x, r-1))
        return best
    return minimum


def generic_replay(counts):
    for j in range(21):
        for q in range(1, 513):
            z = 3**j * q
            if z % 16 != 11:
                continue
            n = (z-3)//8
            p = 2**j*q-1
            b = (3*n+1)//2
            assert n > 0 and n % 2 == 1
            assert inverse_path(b, 'EEOE'+'O'*j, counts, 'generic') == p
            values = ordinary(p, 2*j+5)
            assert values == paired(p, 2*j+5) and values[-1] == ordinary(n, 2)[-1]
            if j >= 6:
                assert 0 < p < n
                counts['generic_strict_detours'] += 1
            counts['generic_detours'] += 1
            counts['generic_ordinary_steps'] += 2*j+7
    for t in range(0, 4097, 2):
        n = 729*t+273
        q = 8*t+3
        p = 64*q-1
        assert 729*q == 8*n+3 and 0 < p < n
        assert ordinary(p, 17)[-1] == ordinary(n, 2)[-1]
        counts['residue_class_detours'] += 1
        counts['residue_class_ordinary_steps'] += 19
    return {'j_interval': [0, 20], 'q_interval': [1, 512],
            'filter': '3^j*q = 11 mod16, giving a positive odd n=(3^j*q-3)/8',
            'residue_class': 'n=729*t+273 for every even t from 0 through 4096',
            'scope': 'Actual integer paths; no hypothetical least counterexample is numerically instantiated.'}


def family_replay(counts):
    residues = [r for r in range(162) if pow(8, r+1, 729) == 37]
    assert residues == [85] and pow(8, 162, 729) == 1
    counts['modular_period_residues'] = 162
    for h in range(1025):
        assert pow(8, 162*h+86, 729) == 37
        counts['modular_family_indices'] += 1
    rows = []
    for h in range(17):
        R = 162*h+85
        n = 8**R-5
        q = (8**(R+1)-37)//729
        p = 64*q-1
        j, qmax = valuation3(8*n+3)
        assert 729*q == 8*n+3 and 0 < p < n and n % 729 == 273
        indices = sorted({0, 1, 2, R//2, R-1})
        forward = ordinary(n, 5*R)
        assert forward == paired(n, 5*R) and min(forward) == n
        assert [t for t, x in enumerate(forward[:-1]) if x % 27 == 20] == [5*i+2 for i in range(1, R)]
        counts['family_sources'] += 1
        counts['family_ordinary_prefix_steps'] += 5*R
        counts['family_target_visits'] += R-1
        for i in indices:
            b = hit(R, i)
            word = 'OEO'*i + 'EEOE' + 'O'*6
            assert word.count('E') == i+3 and word.count('O') == 2*i+7
            assert inverse_path(b, word, counts, 'family') == p
            values = ordinary(p, 5*i+17)
            assert values == paired(p, 5*i+17) and values[-1] == b == forward[5*i+2]
            counts['family_attaining_paths'] += 1
            counts['family_attaining_ordinary_steps'] += 5*i+17
        pmax = 2**j*qmax-1
        assert pmax <= p and ordinary(pmax, 2*j+5)[-1] == forward[2]
        counts['maximal_valuation_detours'] += 1
        counts['maximal_valuation_ordinary_steps'] += 2*j+5
        rows.append({'h': h, 'R': R, 'source_bits': n.bit_length(),
                     'fixed_j6_predecessor_bits': p.bit_length(), 'v3_8n_plus_3': j,
                     'maximal_valuation_predecessor_bits': pmax.bit_length(),
                     'sampled_target_indices': indices})
    return {'complete_h_interval': [0, 16], 'modular_h_interval': [0, 1024],
            'residues_R_mod162': residues, 'rows': rows,
            'scope': 'Every ordinary prefix and visit is checked for listed sources; five inverse words per source are replayed. The kernel fixed-j=6 family is distinguished from the maximal-valuation predecessor.'}


def negative_table(counts):
    rows = []
    groups = defaultdict(list)
    for m in range(5, 47):
        x = m
        e = o = 0
        seen = set()
        path = [m]
        while x != 7 and x not in seen:
            seen.add(x)
            if x % 2:
                x = (3*x-1)//2
                o += 1
            else:
                x //= 2
                e += 1
            path.append(x)
        outcome = str(2*e+1-o) if x == 7 else ('cycle1' if 1 in seen else 'cycle17')
        if outcome == 'cycle17':
            assert 17 in seen and 7 not in seen
        groups[outcome].append(m)
        rows.append({'m': m, 'first_path': path, 'outcome': outcome,
                     'even_steps': e, 'odd_steps': o})
        counts['negative_table_states'] += 1
        counts['negative_table_steps'] += e+o
    expected = [[5], [9, 10], [18, 19, 20], [35, 36, 38, 40]]
    bounds = []
    for f in range(4):
        bound = 1+(4*9**f)//4**f
        candidates = [m for m in groups[str(2*f)] if m <= bound]
        assert candidates == expected[f]
        bounds.append({'f': f, 'm_upper_bound': bound, 'candidate_m': candidates})
    return {'complete_m_interval': [5, 46], 'rows': rows, 'groups': dict(groups),
            'frontier_candidates': bounds,
            'scope': 'Finite forward enumeration checks the table. Its extension to arbitrary inverse lengths uses the written cycle/count argument; the exact minimum classification is not a new kernel root.'}


def extended_minima_replay(counts):
    minimum = inverse_minimum(counts)
    indices = list(range(3, 514, 2)) + [1025]
    improved = []
    for R in indices:
        n = 8**R-5
        j, q = valuation3(8*n+3)
        p = 2**j*q-1
        assert j >= 2 and (p < n) == (j >= 6) == (R % 162 == 85)
        targets = range(R) if R <= 17 else range(7)
        for i in targets:
            b = hit(R, i)
            for extra in range(4):
                expected = n if extra < 3 else min(n, p)
                assert minimum(b, i+extra) == expected, (R, i, extra)
                counts['extended_inverse_minima'] += 1
                if expected < n:
                    counts['extended_strict_minima'] += 1
        if p < n:
            improved.append({'R': R, 'valuation': j, 'source_bits': n.bit_length(),
                             'minimum_bits': p.bit_length()})
        counts['extended_sources'] += 1
        minimum.cache_clear()
    return {'complete_odd_R_interval': [3, 513], 'additional_R': [1025],
            'indices_for_R_through17': 'all i=0..R-1',
            'indices_for_larger_R': 'all i=0..6', 'extra_budget_interval': [0, 3],
            'strict_improvement_sources': improved,
            'scope': 'Complete inverse optimization for each explicitly listed query; finite evidence for the written general classification, not a substitute for its proof.'}


def companion_replay(counts):
    cases = Counter()
    queries = []
    for R in list(range(3, 16, 2)) + [85]:
        targets = range(R) if R != 85 else range(7)
        for i in targets:
            n = 8**R-5
            b = hit(R, i)
            L = 2*i+1
            j, q = valuation3(8*n+3)
            expected = min(n, 2**j*q-1)
            stack = [(b, 7, 0, 0)]
            best = b
            while stack:
                x, m, e, o = stack.pop()
                assert e <= i+3 and x >= expected
                best = min(best, x)
                counts['complete_inverse_nodes'] += 1
                if o <= L:
                    assert m is not None and 5 <= m <= 7*2**e and o <= 2*e+1
                    d = 2*e+1-o
                    assert 2**d*(m-1) <= 4*3**d
                    assert 3**o*(x+m) == 2**(e+o)*(b+7)
                    assert x >= n
                    counts['truncated_companion_nodes'] += 1
                    if o == L:
                        f = e-i
                        assert 0 <= f <= 3 and x+m == 2**(3*R+f)
                        assert m in [[5], [9, 10], [18, 19, 20], [35, 36, 38, 40]][f]
                        counts['frontier_nodes'] += 1
                        if x % 3 == 2:
                            assert (f, m) in {(2, 18), (3, 35), (3, 38)}
                            cases[f'{f},{m}'] += 1
                if e < i+3:
                    stack.append((2*x, None if m is None else 2*m, e+1, o))
                if x % 3 == 2:
                    mm = None
                    if o < L:
                        assert (2*m+1) % 3 == 0
                        mm = (2*m+1)//3
                    stack.append(((2*x-1)//3, mm, e, o+1))
            assert best == expected
            counts['complete_companion_queries'] += 1
            queries.append({'R': R, 'i': i, 'budget': i+3})
    return {'queries': queries, 'first_escape_cases_f_m': dict(cases),
            'scope': 'Every inverse branch through the stated budget, including after the companion ceases to be integral. No unrestricted ancestor minimum is inferred.'}


def convergence_replay(counts):
    n = 8**85-5
    p = 64*((8**86-37)//729)-1
    rows = []
    for x, t in [(7563, 83), (5311, 98), (n, 2119), (p, 2134)]:
        values = ordinary(x, t)
        assert values == paired(x, t) and values[-1] == 1 and 1 not in values[:-1]
        rows.append({'source': x, 'source_bits': x.bit_length(), 'first_arrival': t})
        counts['kernel_arrival_witnesses'] += 1
        counts['kernel_arrival_ordinary_steps'] += t
    return {'rows': rows,
            'scope': 'Arrival existence is axiom-free kernel computation. First-arrival minimality is independently checked here. No universal family convergence is claimed.'}


def build(sources):
    version = subprocess.check_output(['lean', '--version'], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-inverse-escape-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory) / (stem+'.olean')
            log = OUT / (stem+'.log')
            command = ['lean', '-o', str(obj), source]
            started = time.monotonic()
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
                for theorem in ['finite_negative_cycles', 'finite_escape_witness']:
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
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, h in prior['sha256'].items():
        assert digest(ROOT/name) == h, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [NEW_SOURCE]
    assert len(sources) == 29
    version, builds = build(sources)
    counts = Counter()
    sections = {}
    for name, check in [('generic_detour', generic_replay), ('escape_family', family_replay),
                        ('negative_frontier_table', negative_table), ('extended_minima', extended_minima_replay),
                        ('companion_branches', companion_replay), ('kernel_arrivals', convergence_replay)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources + [Path(__file__).name, 'docs/MINIMUM-INVERSE-ESCAPE.md', PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'builds': builds,
        'kernel_theorems_audited': len(THEOREMS), 'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': 'For positive q and odd n with 3^j*q=8n+3, an actual predecessor 2^j*q-1 coalesces at ordinary clocks 2j+5 and 2. It is strictly smaller for j>=6. A least counterexample cannot be 273 mod729. For R=162h+85, the source 8^R-5 has an explicit smaller predecessor at every return-ladder target b_i, using i+3 even and 2i+7 odd inverse steps. A companion exists until o=2i+1; every smaller predecessor must pass that odd-count boundary. Frontier arithmetic, actual negative companion semantics, finite negative cycles and four positive arrival witnesses are included.',
        'written_scope': ['Finite negative frontier table assembled with the cycle/count invariant for arbitrary path lengths.',
                          'For odd R>=3 and 0<=i<R, exact minima at even budgets i,i+1,i+2 are 8^R-5; at i+3 the minimum is min(8^R-5,2^j*(8^(R+1)-37)/3^j-1), with j=v3(8^(R+1)-37).',
                          'Strict improvement at budget i+3 occurs exactly for R=85 mod162. The complete sharpness classification is written, not a new kernel theorem.'],
        'external_dependency': 'None. No new external theorem, finite computation, or package installation is used.',
        'finite_scope_limit': 'Every inverse query and complete branch traversal has explicit finite ranges. Family sources vary with the parameter. First-arrival minimality is Python, separate from kernel arrival existence.',
        'not_proved': ['Universal convergence of the return-ladder or escape subfamily.',
                       'Exact minima at larger budgets, or a uniformly bounded useful inverse complexity for every least-source orbit.',
                       'A universal cap/residual bound or the positive-integer Collatz conjecture.'],
        'sha256': {p: digest(ROOT/p) for p in files}})
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS), 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
