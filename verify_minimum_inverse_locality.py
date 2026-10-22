"""Audit bounded inverse locality and the unbounded first-target obstruction.

Kernel proofs, finite integer trees, and modular checks of enormous ladder
sources have distinct scopes. No universal convergence claim is made.
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
OUT = ROOT / 'results/minimum-inverse-locality'
PRIOR = 'results/minimum-negative-cycle/verification.json'
SOURCE = 'lean/MinimumInverseLocality.lean'
NOTE = 'docs/MINIMUM-INVERSE-LOCALITY.md'
THEOREMS = [
    'backtrack_positive', 'backtrack_size', 'odd_count_bound',
    'inverse_locality', 'inverse_lift', 'cycle_avoids', 'avoids_sound',
    'finite_anchor', 'anchor_only_hit', 'anchor_minimum', 'anchor_slope',
    'precision_factor', 'canonical_inverse', 'family_attainment',
    'family_lower', 'family_exact_minimum', 'seven_step_profile',
    'family_first_target', 'unbounded_first_target_obstruction',
    'one_residue_powers', 'eight_period', 'ladder_exponent',
    'ladder_in_family', 'ladder_first_target_minimum', 'ladder_growth',
    'unbounded_ladder_obstruction',
]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def step(n):
    return 3*n+1 if n % 2 else n//2


def ordinary(n, t):
    path = [n]
    for _ in range(t):
        path.append(step(path[-1]))
    return path


def paired(n, t):
    path = [n]
    while len(path) <= t:
        n = path[-1]
        if n % 2:
            path.append(3*n+1)
            if len(path) <= t:
                path.append((3*n+1)//2)
        else:
            path.append(n//2)
    return path


def inverse_tree(b, r):
    """All distinct (value, even count, odd count) states, with no depth cap.

    Odd inverses strictly decrease positive values. Each level of even
    budget is therefore finite; no convergence hypothesis is needed.
    Identical states merge because their legal continuations coincide.
    """
    seen = set()
    stack = [(b, 0, 0)]
    while stack:
        p, e, o = stack.pop()
        state = (p, e, o)
        if state in seen:
            continue
        seen.add(state)
        assert p > 0
        if e < r:
            stack.append((2*p, e+1, o))
        if p % 3 == 2:
            parent = (2*p-1)//3
            assert 0 < parent < p
            stack.append((parent, e, o+1))
    return seen


def anchor_replay(counts):
    rows = []
    largest = (0, 0)
    for p in range(1, 507):
        n = p
        path = [p]
        while n != 1:
            n = step(n)
            path.append(n)
            assert len(path) <= 201
        assert 857 not in path
        assert path == paired(p, len(path)-1)
        counts['anchor_small_sources'] += 1
        counts['anchor_small_ordinary_steps'] += len(path)-1
        largest = max(largest, (len(path)-1, p))
    path = ordinary(507, 35)
    assert path[-1] == 1 and 1 not in path[:-1]
    assert [t for t, n in enumerate(path) if n == 857] == [7]
    assert path == paired(507, 35)
    counts['anchor_source_steps'] = 35
    assert all(step(n) in {1, 2, 4} for n in [1, 2, 4])
    for r in range(21):
        tree = inverse_tree(857, r)
        assert min(p for p, _, _ in tree) == (571 if r == 0 else 507)
        for p, e, o in tree:
            assert p >= 507 and 27*2**(e+o) >= 16*3**o
            assert 3**o*(p+1) <= 2**(e+o)*858
            assert o < 2*(e+10)
        counts['anchor_complete_trees'] += 1
        counts['anchor_tree_states'] += len(tree)
        rows.append({'even_budget': r, 'states': len(tree),
                     'maximum_odd_count': max(o for _, _, o in tree)})
    return {'positive_source_interval': [1, 506],
            'largest_first_arrival': {'source': largest[1], 'clock': largest[0]},
            'anchor_first_arrival': 35, 'unique_857_clock': 7,
            'inverse_tree_rows': rows,
            'scope': 'All smaller positive sources reach the closed 1,4,2 cycle without visiting 857. This finite all-time avoidance also has an axiom-free kernel certificate and a kernel soundness theorem. Tree samples do not replace the universal anchor theorem.'}


def locality_replay(counts):
    for b in range(1, 129):
        d = (b+1).bit_length()
        for r in range(7):
            K = 2*(r+d)
            base = inverse_tree(b, r)
            for p, e, o in base:
                assert o < K and o < 2*(e+d)
                assert 3**o*(p+1) <= 2**(e+o)*(b+1)
            counts['general_reference_trees'] += 1
            for q in [1, 7]:
                B = b+3**K*q
                actual = inverse_tree(B, r)
                lifted = {(p+2**(e+o)*3**(K-o)*q, e, o) for p, e, o in base}
                assert actual == lifted
                for P, e, o in actual:
                    assert ordinary(P, e+2*o)[-1] == B
                    counts['general_forward_replay_steps'] += e+2*o
                counts['general_lifted_trees'] += 1
                counts['general_lifted_states'] += len(actual)
    return {'reference_target_interval': [1, 128], 'even_budgets': [0, 6],
            'q_values': [1, 7], 'precision': 'K=2*(r+d), d=(b+1).bit_length()',
            'scope': 'Complete finite inverse trees are independently enumerated at both endpoints and compared as state sets. All lifted states are forward replayed at their ordinary clocks; no odd-count truncation is imposed.'}


def family_replay(counts):
    for r in range(1, 17):
        K = 2*(r+10)
        base = inverse_tree(857, r)
        for q in [0, 1, 2, 17]:
            n = 507+16*3**(K-3)*q
            b = 857+3**K*q
            tree = inverse_tree(b, r)
            assert tree == {(p+2**(e+o)*3**(K-o)*q, e, o) for p, e, o in base}
            assert min(p for p, _, _ in tree) == n
            assert (n, 1, 3) in tree
            for p, e, o in tree:
                assert ordinary(p, e+2*o)[-1] == b
                counts['family_tree_forward_steps'] += e+2*o
            counts['family_complete_trees'] += 1
            counts['family_tree_states'] += len(tree)
    rows = []
    for r in range(1, 65):
        K = 2*(r+10)
        for q in range(32):
            v = 3**(K-3)*q
            n, b = 507+16*v, 857+27*v
            path = ordinary(n, 7)
            assert path == paired(n, 7)
            assert path == [507+16*v, 1522+48*v, 761+24*v, 2284+72*v,
                            1142+36*v, 571+18*v, 1714+54*v, 857+27*v]
            assert min(path) == n and path[-1] == b
            assert [t for t, x in enumerate(path) if x % 27 == 20] == [7]
            counts['family_first_target_prefixes'] += 1
            counts['family_first_target_steps'] += 7
        rows.append({'r': r, 'precision': K,
                     'q_1_source_bits': (507+16*3**(K-3)).bit_length()})
    return {'complete_tree_r_interval': [1, 16], 'tree_q_values': [0, 1, 2, 17],
            'prefix_r_interval': [1, 64], 'prefix_q_interval': [0, 31],
            'source_size_rows': rows,
            'scope': 'Exact inverse minima and actual seven-step prefixes are checked separately. These are not computations of global forward minima, nor convergence checks for the infinite families.'}


def ladder_replay(counts):
    for K in range(6):
        for h in range(5):
            t = 2*3**K*h
            value = 8**t
            assert (value-1) % 3**K == 0
            z = (value-1)//3**K
            R = 3+t
            n = 8**R-5
            b = 27*2**(3*(R-1)-1)-7
            assert n == 507+512*3**K*z
            assert b == 857+864*3**K*z
            assert ordinary(n, 7)[-1] == b
            counts['materialized_period_identity_checks'] += 1
            counts['materialized_ladder_prefix_steps'] += 7
    for r in range(1, 65):
        K = 2*(r+10)
        modulus = 3**K
        for h in range(65):
            R = 3+2*modulus*h
            assert R >= 3 and R % 2 == 1 and h < R
            assert pow(8, 2*modulus*h, modulus) == 1
            assert (27*pow(2, 3*(R-1)-1, modulus)-7) % modulus == 857 % modulus
            source_modulus = 16*3**(K-3)
            assert (pow(8, R, source_modulus)-5) % source_modulus == 507
            counts['modular_ladder_family_checks'] += 1
    return {'materialized_K_interval': [0, 5], 'materialized_h_interval': [0, 4],
            'modular_r_interval': [1, 64], 'modular_h_interval': [0, 64],
            'first_nonanchor_R_at_r_1': 3+2*3**22,
            'first_nonanchor_source_bits_at_r_1': 3*(3+2*3**22),
            'scope': 'The materialized cases check the general period identity and first-target coordinates. Apart from h=0, the actual precision-dependent ladder family is tested only modulo explicit integers, not materialized or numerically traversed. Its all-parameter path and minimum statements are kernel theorems.'}


def build(sources, lean, threads):
    version = subprocess.check_output([lean, '--version'], text=True).strip()
    assert 'version 4.33.1,' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-inverse-locality-') as directory:
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
                source_text = (ROOT/source).read_text()
                assert set(re.findall(r'^theorem (\w+)', source_text, re.M)) == set(THEOREMS)
                assert not re.search(r'\b(sorry|native_decide|axiom)\b', source_text)
                assert "'MinimumInverseLocality.finite_anchor' does not depend on any axioms" in result.stdout
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
    parser.add_argument('--lean', default='lean', help='Compiler matching the repository pin')
    parser.add_argument('--threads', type=int, default=min(16, os.cpu_count() or 1),
                        help='Threads per Lean process; dependent module builds stay sequential')
    args = parser.parse_args()
    assert args.threads > 0
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for name, expected in prior['sha256'].items():
        assert digest(ROOT/name) == expected, name
    print('Authenticated prior hashes:', len(prior['sha256']), flush=True)
    sources = [b['source'] for b in prior['builds']] + [SOURCE]
    assert len(sources) == len(set(sources)) == 31
    version, builds = build(sources, args.lean, args.threads)
    counts = Counter()
    sections = {}
    for name, check in [('anchor', anchor_replay), ('general_locality', locality_replay),
                        ('first_target_family', family_replay), ('return_ladder', ladder_replay)]:
        sections[name] = check(counts)
        print('Independent replay passed:', name, flush=True)
    save(OUT/'replay.json', {'status': 'passed', 'counts': dict(counts), **sections})
    files = sources+[Path(__file__).name, NOTE, PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name != 'verification.json']
    save(OUT/'verification.json', {
        'status': 'passed', 'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'collatz_status': 'unresolved', 'lean_version': version, 'lean_threads': args.threads,
        'builds': builds, 'kernel_theorems_audited': len(THEOREMS),
        'axiom_free_roots': ['finite_anchor'],
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'finite_replay_counts': dict(counts),
        'kernel_scope': [
            'Positive inverse paths satisfy 3^o*(p+1)<=2^(e+o)*(b+1), and o<2*(e+d) when b+1<=2^d.',
            'If K>=2*(r+d), all paths with at most r even inputs at b+3^K*q transfer to b with the exact affine lift. Conversely every reference path with o<=K lifts.',
            'Every positive ordinary predecessor of 857 at most 507 is 507 at clock 7. Every inverse word to 857 has value at least 507 and multiplier at least 16/27.',
            'For r>=1, K=2*(r+10), n=507+16*3^(K-3)*q, and b=857+3^K*q, the exact inverse minimum with even budget r is n. The first residue-20 visit is at ordinary clock 7, with prefix minimum n.',
            'For R=3+2*3^K*h the return-ladder source 8^R-5 belongs to this family. Its first target b_1 has the same exact bounded inverse minimum. Sources are unbounded, and no uniform fixed extra budget suffices at this first visit.',
        ],
        'external_dependency': 'No external mathematical premise. Pinned Lean 4.33.1 was restored from its official release. The user authorized increased Lean threading; this run records the explicit thread count.',
        'finite_scope_limit': 'General trees and explicit positive prefixes have stated finite ranges. Enormous ladder sources are modular-only Python checks; their paths and minima are parameterized kernel proofs.',
        'not_proved': [
            'Failure of every inverse budget for a single unbounded or exceptional source.',
            'Failure of a fixed extra budget simultaneously at all later visits of these sources.',
            'A source-dependent useful inverse budget at an appropriate visit for every least-counterexample orbit.',
            'Universal convergence, exclusion of all nontrivial cycles or divergence, or the Collatz conjecture.',
        ],
        'sha256': {name: digest(ROOT/name) for name in files},
    })
    print(json.dumps({'status': 'passed', 'kernel_roots': len(THEOREMS),
                      'threads': args.threads, 'counts': dict(counts)}, indent=2))


if __name__ == '__main__':
    main()
