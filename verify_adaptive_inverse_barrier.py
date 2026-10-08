"""Enumerate every inverse branch at the listed depths and replay transport.

Also tests the written unit-root obstruction to bounded two-sided meetings.
The universal inverse-level transport is proved separately in Lean.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/adaptive-inverse-barrier'


def U(n):
    return (3*n+1)//2 if n % 2 else n//2


def previous(level):
    result = {}
    for n, j in level.items():
        result[2*n] = j
        if n % 3 == 2:
            child = (2*n-1)//3
            assert child > 0 and child % 2 and U(child) == n
            if child in result:
                assert result[child] == j+1
            result[child] = j+1
    return result


def replay():
    inverse_checks = 0
    records = []
    for K in range(1, 21):
        for q in (1, 2, 17, 2**128+2):
            a = 3**K*q+1
            level, base = {a: 0}, {1: 0}
            for k in range(K+1):
                expected = {r+2**k*3**(K-j)*q: j for r, j in base.items()}
                assert len(expected) == len(base)
                assert expected == level
                assert all(m >= a for m in level)
                if k:
                    assert all(m > a for m in level)
                inverse_checks += len(level)
                records.append(dict(K=K, quotient=str(q), depth=k, ancestors=len(level)))
                if k < K:
                    base, level = previous(base), previous(level)
    meetings = 0
    witnesses = []
    for K in range(1, 19):
        p, q = 2**K, 3**K
        n0 = 1+q*((-2*pow(q, -1, p)) % p)
        if n0 <= 1:
            n0 += p*q
        for t in (0, 1, 3, 2**64):
            n = n0+p*q*t
            assert n > 1 and n % q == 1 and (n+1) % p == 0
            x = n
            count = 0
            for a in range(K+1):
                assert 2**a*(x+1) == 3**a*(n+1)
                level = {x: 0}
                for b in range(K+1):
                    assert all(m >= n for m in level), (K,n,a,b,min(level))
                    count += len(level)
                    if b < K:
                        level = previous(level)
                x = U(x)
            meetings += count
            witnesses.append(dict(K=K, start=str(n), complete_inverse_nodes=count))
    return dict(all_checks_passed=True, inverse_depth_range=[1,20],
                inverse_root_checks=80, transported_ancestor_checks=inverse_checks,
                meeting_depth_range=[1,18], two_sided_roots=len(witnesses),
                complete_meeting_nodes=meetings, inverse_records=records,
                two_sided_witnesses=witnesses)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    data = replay()
    (OUT/'replay.json').write_text(json.dumps(data, indent=2)+'\n')
    sources = ['CollatzAffine.lean', 'CollatzPacking.lean',
               'lean/InverseFibreGrowth.lean', 'lean/BasinResidueShadow.lean',
               'lean/AdaptiveInverseBarrier.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-adaptive-inverse-') as build:
        for source in sources:
            stem = Path(source).stem
            cmd = ['lean', '-o', str(Path(build)/(stem+'.olean')), source]
            p = subprocess.run(cmd, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT/(stem+'.log')
            log.write_text(p.stdout)
            commands.append(dict(command=cmd, returncode=p.returncode,
                                 log=str(log.relative_to(ROOT))))
            if p.returncode or 'sorryAx' in p.stdout:
                raise RuntimeError(f'Lean verification failed: {log}')
    files = sources+[Path(__file__).name,str((OUT/'replay.json').relative_to(ROOT))]
    files += [c['log'] for c in commands]
    manifest = dict(
        verified_at_utc=datetime.now(timezone.utc).isoformat(), conjecture_status='unresolved',
        lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
        kernel_scope=[
            'All depth-k ancestors of 3^K*q+1, k<=K, are affine lifts of depth-k ancestors of one',
            'The converse lift is valid at every such depth',
            'No positive ancestor within K steps is smaller than 3^K*q+1'],
        written_scope=[
            'For q>0 every positive-depth ancestor in this range is strictly larger',
            'If n=1 modulo 3^K and n=-1 modulo 2^K, no smaller-start meeting has both times at most K',
            'These unit-root witnesses are unbounded and admit logarithmic lower bounds on meeting time'],
        not_proved=['Full Collatz conjecture', 'An obstruction to all unbounded adaptive path rules',
                    'Kernel proof of the unit-root two-sided meeting obstruction',
                    'Any uniform upper bound on a successful meeting horizon'],
        replay_summary={k:v for k,v in data.items() if k not in ('inverse_records','two_sided_witnesses')},
        commands=commands,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(manifest['replay_summary'],indent=2))
    print('Five fresh Lean builds passed; two-sided unit-root extension is written.')


if __name__ == '__main__':
    main()
