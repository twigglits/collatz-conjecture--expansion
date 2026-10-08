"""Replay synchronized inverse trees, then build their universal Lean proofs.

Run from any directory with Python 3 and the repository's pinned Lean on PATH.
No third-party Python packages or external mathematical theorems are required.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/uniform-inverse-branching'
OFFSETS = {1: (16, 20), 2: (32, 40), 4: (80, 85),
           5: (104, 106), 7: (148, 149), 8: (160, 170)}


def endpoint(n, k):
    weight = 0
    for _ in range(k):
        if n % 2:
            weight += 1
            n = (3*n + 1)//2
        else:
            n //= 2
    return weight, n


def children(a):
    # Derive independently from the inverse equation, rather than the table.
    result = sorted(2**(6-e)*(2**e*a-1)//3 for e in range(1, 7)
                    if 2**e*a % 3 == 1 and 2**e*a % 9 != 1)
    assert result == [192*(a//9)+d for d in OFFSETS[a % 9]]
    assert len(result) == len(set(result)) == 2
    for n in result:
        assert n > a > 0 and n % 3 and 3*n < 64*a
        assert endpoint(n, 6) == (1, a)
    return result


def replay():
    roots = [a for a in range(1, 10001) if a % 3]
    large_roots = [9*(2**bits+17)+r for bits in (128, 1024)
                   for r in OFFSETS]
    for a in roots + large_roots:
        children(a)
    leaf_checks = 0
    records = []
    for a in list(OFFSETS) + large_roots:
        level = [a]
        for h in range(11):
            assert len(level) == len(set(level)) == 2**h
            for n in level:
                assert n > 0 and n % 3 and endpoint(n, 6*h) == (h, a)
                assert 3**h*n <= 64**h*a
                if a < 3**h:
                    assert n < 2**(6*h)
                leaf_checks += 1
            records.append(dict(root=str(a), depth=h, leaves=len(level),
                                maximum_bits=max(level).bit_length()))
            if h < 10:
                level = [n for parent in level for n in children(parent)]
    return dict(all_checks_passed=True, single_root_checks=len(roots+large_roots),
                tree_roots=len(OFFSETS)+len(large_roots), max_tree_depth=10,
                leaf_checks=leaf_checks, records=records)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    result = replay()
    (OUT/'replay.json').write_text(json.dumps(result, indent=2)+'\n')
    sources = ['CollatzAffine.lean', 'lean/InverseFibreGrowth.lean',
               'lean/UniformInverseBranching.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-uniform-branch-') as build:
        env = dict(os.environ, LEAN_PATH=build)
        for source in sources:
            stem = Path(source).stem
            cmd = ['lean', '-o', str(Path(build)/(stem+'.olean')), source]
            check = subprocess.run(cmd, cwd=ROOT, env=env, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT/(stem+'.log')
            log.write_text(check.stdout)
            commands.append(dict(command=cmd, returncode=check.returncode,
                                 log=str(log.relative_to(ROOT))))
            if check.returncode or 'sorryAx' in check.stdout:
                raise RuntimeError(f'Lean verification failed; see {log}')
    files = sources + [Path(__file__).name, str((OUT/'replay.json').relative_to(ROOT))]
    files += [item['log'] for item in commands]
    manifest = dict(
        verified_at_utc=datetime.now(timezone.utc).isoformat(),
        conjecture_status='unresolved',
        lean_version=subprocess.check_output(['lean', '--version'], text=True).strip(),
        kernel_scope=[
            'Two distinct positive unit children at every root a not divisible by three',
            'Each child reaches a in six shortcut steps with exactly one odd step',
            'At depth h the leaf list has exactly 2^h distinct positive unit members',
            'Every leaf has endpoint a at time 6h, weight h, and 3^h*n <= 64^h*a'],
        written_corollaries=[
            'If a < 3^h, every depth-h leaf lies below 2^(6h)',
            'For a hypothetical nonconvergent unit root, all leaves are nonconvergent',
            'No subexponential time-dependent bound for all fixed-root fibre sizes',
            'Uniform binary leaf distribution has h bits of conditional entropy given its endpoint'],
        not_proved=['Collatz convergence or divergence',
                    'A lower bound on a single forward orbit from inverse-tree counts',
                    'Any imported OpenAI math manuscript theorem or its applicability to Collatz'],
        replay_summary={k:v for k,v in result.items() if k != 'records'},
        commands=commands,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(manifest['replay_summary'], indent=2))
    print('All three fresh Lean builds passed; no sorryAx in printed dependencies.')


if __name__ == '__main__':
    main()
