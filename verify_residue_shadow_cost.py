"""Check size bounds, odd-root injections and fixed-prefix worst-case costs."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

from verify_basin_residue_shadow import power_lift, trace

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/residue-shadow-cost'


def replay():
    roots = [a for a in range(1, 1024, 2) if a % 3]
    roots += [2**128+1, 2**256+1]
    profiles = []
    checks = 0
    for A in range(5):
        for B in range(2):
            M = 2**A*3**B
            for r in range(M):
                n = r or M
                k = max(A, n.bit_length())
                bits, y = trace(n, k)
                j = sum(bits)
                assert j > 0 and y % 3
                J = j+B
                T = 2*3**(J-1)
                L = y.bit_length()
                E = L+T-1
                D = 2**k*y-3**j*n
                assert D > 0
                seen = {}
                maximum_e = 0
                for a in roots:
                    e, period = power_lift(a, y, J)
                    assert period == T
                    while a*2**e <= y:
                        e += T
                    assert e <= E
                    q, rem = divmod(a*2**e-y, 3**J)
                    assert rem == 0 and q > 0
                    N = 2**k*3**B*q+n
                    assert N % M == r and trace(N, k) == (bits, 2**e*a)
                    assert 3**j*N+D == 2**(k+e)*a
                    assert 3**j*N <= 2**(k+E)*a
                    assert N not in seen
                    seen[N] = a
                    maximum_e = max(maximum_e, e)
                    checks += 1
                # Force the largest minimal exponent, then take increasing
                # odd roots in that class. This checks sharpness of the
                # asymptotic slope within the prescribed-prefix scheme.
                modulus = 3**J
                residue = y*pow(pow(2, T-1, modulus), -1, modulus) % modulus
                witness = residue if residue % 2 else residue+modulus
                sharp = []
                for z in (y+1, 2**64+y):
                    a = witness+2*modulus*z
                    e, _ = power_lift(a, y, J)
                    assert a > y and e == T-1 and a % 2 and a % 3
                    q, rem = divmod(a*2**e-y, modulus)
                    assert rem == 0 and q > 0
                    N = 2**k*3**B*q+n
                    assert 2**(k+T-1)*a-3**j*N == D
                    current = N
                    for _ in range(k+e):
                        assert current >= a
                        current = (3*current+1)//2 if current % 2 else current//2
                    assert current == a
                    sharp.append(dict(root=str(a), ancestor_bits=N.bit_length()))
                profiles.append(dict(A=A, B=B, residue=r, representative=n,
                                     prefix_steps=k, prefix_weight=j, endpoint=y,
                                     period=T, uniform_exponent_bound=E,
                                     sharp_slope_numerator_power_of_two=k+T-1,
                                     sharp_slope_denominator=3**j,
                                     maximum_sample_exponent=maximum_e,
                                     sharp_witnesses=sharp))
    return dict(all_checks_passed=True, cylinders=len(profiles), odd_roots=len(roots),
                ancestor_checks=checks, sharp_witness_checks=2*len(profiles),
                maximum_period=max(p['period'] for p in profiles), profiles=profiles)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    result = replay()
    (OUT/'replay.json').write_text(json.dumps(result, indent=2)+'\n')
    sources = ['CollatzAffine.lean', 'lean/InverseFibreGrowth.lean',
               'lean/BasinResidueShadow.lean', 'lean/ResidueShadowCost.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-shadow-cost-') as build:
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
    files = sources + [Path(__file__).name, 'verify_basin_residue_shadow.py',
                       str((OUT/'replay.json').relative_to(ROOT))]
    files += [c['log'] for c in commands]
    manifest = dict(
        verified_at_utc=datetime.now(timezone.utc).isoformat(), conjecture_status='unresolved',
        lean_version=subprocess.check_output(['lean', '--version'], text=True).strip(),
        kernel_scope=[
            'Conditional size bound 3^j*N <= 2^(k+e)*a and its uniform bounded-exponent form',
            'Uniqueness of a power-of-two times an odd root',
            'Fixed-prefix shadows of distinct odd roots are distinct',
            'At the end of the prescribed prefix the image is at least the root'],
        written_scope=[
            'Every fixed mixed residue class admits a uniform linear-cost bounded-time inverse embedding',
            'The embedding is injective on positive odd roots coprime to three',
            'Its sharp worst asymptotic slope for the fixed-prefix/halving-tail scheme is 2^(k+T-1)/3^j',
            'Infinitely many odd roots have no value below the root anywhere on this constructed path',
            'The count of odd nonconvergent roots transfers to any cylinder with a fixed rescaling'],
        not_proved=['Full Collatz conjecture', 'A uniformly smaller ancestor',
                    'Optimality among arbitrary inverse paths or root-dependent prefixes',
                    'A scale-dependent trapping certificate',
                    'Kernel modular lifting existence or asymptotic/counting arguments'],
        replay_summary={k:v for k,v in result.items() if k != 'profiles'}, commands=commands,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(manifest['replay_summary'], indent=2))
    print('Four fresh Lean builds passed; modular existence and sharp asymptotics remain written.')


if __name__ == '__main__':
    main()
