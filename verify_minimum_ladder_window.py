"""Verify simultaneous failure of a fixed extra inverse budget on a ladder prefix.

Full kernel statements, complete finite trees, streamed positive prefixes,
and modular-only family checks are recorded separately.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

from verify_minimum_inverse_locality import digest, save, step, ordinary, paired, inverse_tree

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/minimum-ladder-window'
PRIOR = 'results/minimum-inverse-locality/verification.json'
SOURCE = 'lean/MinimumLadderWindow.lean'
NOTE = 'docs/MINIMUM-LADDER-WINDOW.md'
HELPER = 'verify_minimum_inverse_locality.py'
THEOREMS = [
    'shadow_bounds', 'shadow_not_eight', 'frontier_shadow_bound',
    'sharp_shadow_attained', 'backtrack_split_odd', 'cycle_closed',
    'finite_small_paths', 'reference_bounds', 'reference_predecessor',
    'frontier_suffix_lower', 'all_target_lower', 'window_exponent',
    'window_lift', 'window_exact_minimum', 'window_prefix',
    'unbounded_whole_window',
]


def negative_step(m):
    return (3*m-1)//2 if m % 2 else m//2


def shadow_replay(counts):
    stack = [(7, 0, 0)]
    seen = set()
    max_odd = 0
    while stack:
        m, e, o = stack.pop()
        state = (m, e, o)
        if state in seen:
            continue
        seen.add(state)
        assert m >= 5 and m != 8 and o <= 2*e+1
        assert m <= (5 if o % 2 else 7)*2**(e-o//2)
        max_odd = max(max_odd, o)
        if e < 22:
            stack.append((2*m, e+1, o))
        if m % 3 == 1:
            parent = (2*m+1)//3
            assert 5 <= parent < m
            stack.append((parent, e, o+1))
    counts['complete_shadow_states'] = len(seen)
    for i in range(33):
        for f in range(33):
            word = 'O'+'EOO'*i+'E'*f
            m = 7
            for letter in word:
                if letter == 'E':
                    m *= 2
                else:
                    assert m % 3 == 1
                    m = (2*m+1)//3
                counts['attaining_shadow_inverse_steps'] += 1
            assert m == 5*2**f
            assert word.count('E') == i+f and word.count('O') == 2*i+1
            odd = 0
            for _ in word:
                odd += m % 2
                m = negative_step(m)
                counts['attaining_shadow_forward_steps'] += 1
            assert m == 7 and odd == 2*i+1
            counts['attaining_shadow_paths'] += 1
    return {'complete_even_budget': 22, 'maximum_odd_count': max_odd,
            'attainment_i_interval': [0, 32], 'attainment_f_interval': [0, 32],
            'scope': 'The complete finite negative companion tree checks the sharper bound at every state. Attaining paths are independently reversed under the deterministic magnitude map. No negative orbit conjecture is assumed.'}


def small_paths_replay(counts):
    table = []
    for p in range(7):
        path = ordinary(p, 8)
        assert path == paired(p, 8)
        if p:
            assert path[8] in {1, 2, 4}
        assert max(path[:8]) <= 16
        for t, x in enumerate(path[:8]):
            for f in range(3):
                for o in range(4):
                    counts['small_certificate_tuples'] += 1
                    if (2*o <= t and 3*2**f <= x and x+5 <= 2**(f+3)
                            and x+8 != 2**(f+3)):
                        assert 3**o <= 2**(f+t-o)
                        counts['nonvacuous_small_certificate_tuples'] += 1
                        table.append({'p': p, 't': t, 'x': x, 'f': f, 'o': o})
        counts['small_ordinary_steps'] += 8
    # This failure explains the explicit exclusion of companion magnitude 8.
    assert (3, 0, 2) in inverse_tree(8, 0)
    assert 2**(1+0+2) < 3**2
    return {'positive_source_interval': [1, 6], 'zero_source_also_checked': True,
            'nonvacuous_rows': table,
            'excluded_case': {'f': 1, 'm': 8, 'reference_target': 8,
                              'predecessor': 3, 'even': 0, 'odd': 2},
            'scope': 'All tuples of the axiom-free kernel certificate are replayed. Magnitude 8 is impossible in the negative companion tree; allowing it would invalidate the reference multiplier inequality.'}


def reference_replay(counts):
    for s in range(11):
        K = 2*(s+3)
        for f in range(s+1):
            for m in range(5, 5*2**f+1):
                if m == 8:
                    continue
                x = 2**(f+3)-m
                base = inverse_tree(x, s-f)
                for p, e, o in base:
                    assert p >= 3 and 3**o <= 2**(f+e+o)
                    assert o < K
                counts['reference_complete_trees'] += 1
                counts['reference_tree_states'] += len(base)
            # Lift endpoints, a midpoint, and the smallest legal magnitude.
            for m in sorted({5, 5*2**f, max(5, 5*2**f//2)}-{8}):
                x = 2**(f+3)-m
                base = inverse_tree(x, s-f)
                for q in [1, 5, 17]:
                    X = 8+3**K*q
                    b = 2**f*X-m
                    actual = inverse_tree(b, s-f)
                    lifted = {(p+2**(e+o)*3**(K-o)*(2**f*q), e, o)
                              for p, e, o in base}
                    assert actual == lifted
                    for P, e, o in actual:
                        assert P >= X-5
                        assert ordinary(P, e+2*o)[-1] == b
                        counts['frontier_forward_steps'] += e+2*o
                    counts['frontier_lifted_trees'] += 1
                    counts['frontier_lifted_states'] += len(actual)
    return {'extra_budget_interval': [0, 10],
            'reference_box': 'Every f=0..s and m=5..5*2^f except m=8; even budget s-f.',
            'lifted_q_values': [1, 5, 17],
            'scope': 'The reference inequality is checked over its entire stated finite box, including magnitudes not known to be negative companions. Lifted trees at selected magnitudes are complete, with forward replay of every state. Generic X=8+3^K*q here need not be a pure power of eight.'}


def split_replay(counts):
    # Distinct words are retained here to test every chosen odd-count split.
    for b in range(1, 65):
        stack = [(b, '')]
        while stack:
            p, word = stack.pop()
            e, o = word.count('E'), word.count('O')
            for L in range(o+1):
                cut = 0
                if L:
                    cut = next(j+1 for j in range(len(word)) if word[:j+1].count('O') == L)
                x = b
                for letter in word[:cut]:
                    x = 2*x if letter == 'E' else (2*x-1)//3
                suffix = word[cut:]
                a, c = word[:cut].count('E'), suffix.count('E')
                assert a+c == e and suffix.count('O') == o-L
                assert ordinary(p, c+2*(o-L))[-1] == x
                assert ordinary(x, a+2*L)[-1] == b
                counts['word_split_checks'] += 1
            counts['split_inverse_words'] += 1
            if e < 5:
                stack.append((2*p, word+'E'))
            if p % 3 == 2:
                stack.append(((2*p-1)//3, word+'O'))
    return {'target_interval': [1, 64], 'even_budget': 5,
            'scope': 'Every finite inverse word in this range is split at every possible odd count. Both ordinary path segments are replayed independently.'}


def actual_ladder_replay(counts):
    rows = []
    cases = [(0, 0, 12, None), (0, 1, 12, None), (1, 0, 10, None),
             (2, 0, 6, None), (3, 0, 4, 8), (4, 0, 1, 3)]
    for s, h, max_i, partial_blocks in cases:
        K = 2*(s+3)
        R = 1+2*3**K*(h+1)
        X = 1 << (3*R)
        N = X-5
        assert (X-8) % 3**K == 0
        x = N
        visited = 0
        blocks = R if partial_blocks is None else partial_blocks
        for i in range(blocks):
            # Stream the complete ordinary prefix without retaining large paths.
            path = ordinary(x, 5)
            assert path == paired(x, 5)
            assert min(path) >= N
            for j, value in enumerate(path[:5]):
                assert (value % 27 == 20) == (i > 0 and j == 2)
                counts['actual_prefix_residue_checks'] += 1
            u = x
            word = ''
            for _ in range(3):
                word += 'O' if u % 2 else 'E'
                u = (3*u+1)//2 if u % 2 else u//2
            assert word == 'OOE' and u == path[-1]
            assert (x+5) % 8 == 0
            assert u == 9*((x+5)//8)-5
            if i:
                visited += 1
            if i <= max_i:
                b = path[2]
                assert b == (3**(2*i+1) << (3*(R-i)-1))-7
                tree = inverse_tree(b, i+s)
                assert min(p for p, _, _ in tree) == N
                assert (N, i, 2*i+1) in tree
                for p, e, o in tree:
                    assert ordinary(p, e+2*o)[-1] == b
                    counts['actual_tree_forward_steps'] += e+2*o
                counts['actual_complete_inverse_queries'] += 1
                counts['actual_inverse_states'] += len(tree)
            counts['actual_ordinary_prefix_steps'] += 5
            counts['actual_shortcut_prefix_steps'] += 3
            x = u
        assert x == (9**blocks << (3*(R-blocks)))-5 and visited == blocks-1
        counts['actual_target_visits'] += visited
        counts['actual_full_prefixes' if partial_blocks is None else 'actual_partial_prefixes'] += 1
        rows.append({'s': s, 'h': h, 'K': K, 'R': R, 'source_bits': N.bit_length(),
                     'prefix_clock': 5*blocks, 'target_visits': visited,
                     'complete_growing_prefix': partial_blocks is None,
                     'complete_inverse_i_interval': [0, max_i]})
        print('Streamed positive prefix: s=%d, R=%d, blocks=%d' % (s, R, blocks), flush=True)
    return {'rows': rows,
            'scope': 'Every state of each listed ordinary prefix is replayed. The first four examples cover the entire growing ladder; the last two cover only the stated initial blocks. Complete inverse optimization is restricted to the explicitly listed early indices; the theorem for all visits is a separate kernel proof. No eventual convergence of these sources is inferred.'}


def modular_replay(counts):
    for s in range(129):
        K = 2*(s+3)
        M = 3**K
        for h in range(32):
            R = 1+2*M*(h+1)
            assert R >= 3 and R % 2 == 1 and h < R
            assert pow(8, R, M) == 8
            counts['modular_window_checks'] += 1
    return {'s_interval': [0, 128], 'h_interval': [0, 31],
            'scope': 'Only exponents and congruences are computed here. Except for the six separately listed streamed examples, no source 8**R-5 is materialized in this section.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-ladder-window-') as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory)/(stem+'.olean')
            log = OUT/(stem+'.log')
            command = [lean, '-j', str(threads), '-o', str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory,
                                             LEAN_NUM_THREADS=str(threads)))
            log.write_text(result.stdout)
            assert result.returncode == 0, (source, result.stdout)
            assert not any(s in result.stdout for s in ('warning:', 'error:', 'sorryAx', 'ofReduceBool', 'Operation not permitted'))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == SOURCE:
                assert {n for n, _ in roots} == {stem+'.'+t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                text = (ROOT/source).read_text()
                assert set(re.findall(r'^theorem (\w+)', text, re.M)) == set(THEOREMS)
                assert not re.search(r'\b(sorry|native_decide|axiom)\b', text)
                assert "'MinimumLadderWindow.finite_small_paths' does not depend on any axioms" in result.stdout
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(',') if a.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'threads': threads, 'returncode': 0,
                           'fresh_build': True, 'native_computation_used': False,
                           'elapsed_seconds': round(time.monotonic()-started, 3),
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--threads', type=int, default=min(16, os.cpu_count() or 1))
    args = parser.parse_args()
    assert args.threads > 0
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT/name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [SOURCE]
    assert len(sources) == len(set(sources)) == 32
    version, builds = build(sources, args.lean, args.threads)
    counts = Counter()
    sections = {}
    for name, check in [('shadows', shadow_replay), ('small_certificate', small_paths_replay),
                        ('reference_and_lift', reference_replay), ('word_splits', split_replay),
                        ('actual_ladders', actual_ladder_replay), ('modular_families', modular_replay)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources+[Path(__file__).name, HELPER, NOTE, PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'kernel_theorems_audited': len(THEOREMS),
        'axiom_free_roots': ['finite_small_paths'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'Shadow(e,o,m) has m>=5, o<=2e+1, and m<=7*2^(e-floor(o/2)) for even o, or 5*2^(e-floor(o/2)) for odd o. At e=i+f,o=2i+1 the latter bound is sharp. Magnitude 8 is excluded.',
            'Every inverse word splits at any prescribed odd count not exceeding its total.',
            'For 5<=m<=5*2^f, m!=8, and x+m=2^(f+3), every positive inverse predecessor p of x has p>=3 and multiplier 2^(e+o)/3^o>=2^(-f).',
            'For odd R>=3, 8^R=8+3^K*q and K>=2*(s+3), every target b_i, i<R, has exact inverse minimum 8^R-5 at even budget i+s.',
            'The explicit family K=2*(s+3), R=1+2*3^K*(h+1) satisfies those hypotheses. The ordinary prefix minimum through clock 5R is the source, with exactly R-1 residue-20 visits before that clock.',
            'For every fixed extra budget, visit-count bound and source bound, one source exceeds the bound and has a longer complete growing prefix where all of its targets resist that extra budget simultaneously.',
        ],
        'external_dependency': 'No external mathematical premise. Lean 4.33.1 and its standard libraries; no installation or credential access in this continuation.',
        'finite_scope_limit': 'Full ordinary prefixes and bounded inverse-tree queries have separate explicit ranges. Large family exponents are also checked modularly. Numerical queries do not establish the parameterized all-visit statement; that statement is kernel proved.',
        'not_proved': [
            'A fixed extra budget fails at every later target after the growing prefix ends.',
            'A single source has infinitely many obstructed visits or diverges.',
            'Universal convergence of the constructed family, a least-counterexample occurrence theorem, or the cap/residual bounds.',
            'Exclusion of all nontrivial cycles or divergent orbits, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
