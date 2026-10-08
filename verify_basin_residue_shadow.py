"""Construct ancestors in mixed 2-adic/3-adic residue classes.

Finite replay of the written lifting argument, followed by fresh Lean builds
of the conditional transport lemmas. No convergence of the chosen target
roots is assumed or tested.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/basin-residue-shadow'


def trace(n, k):
    bits = []
    for _ in range(k):
        bits.append(n % 2)
        n = (3*n+1)//2 if n % 2 else n//2
    return bits, n


def power_lift(a, y, j):
    """Return e<2*3^(j-1) with a*2^e=y modulo 3^j."""
    assert j >= 1 and a % 3 and y % 3
    e = next(e for e in (0, 1) if a*2**e % 3 == y % 3)
    period, modulus = 2, 3
    for _ in range(1, j):
        modulus *= 3
        candidates = [e+d*period for d in range(3)
                      if a*pow(2, e+d*period, modulus) % modulus == y % modulus]
        assert len(candidates) == 1
        e = candidates[0]
        period *= 3
    assert e < period and pow(2, period, modulus) == 1
    assert a*pow(2, e, modulus) % modulus == y % modulus
    return e, period


def shadow(a, A, B, r):
    modulus = 2**A*3**B
    assert 0 <= r < modulus
    n = r or modulus
    k = max(A, n.bit_length())
    bits, y = trace(n, k)
    j = sum(bits)
    assert j > 0 and y % 3
    e, period = power_lift(a, y, j+B)
    # Adding a period preserves the congruence. Select a strictly larger
    # ancestor even when the first solution already happens to be n.
    while a*2**e <= y:
        e += period
    q, remainder = divmod(a*2**e-y, 3**(j+B))
    assert remainder == 0 and q > 0
    N = 2**k*3**B*q+n
    check_bits, check_y = trace(N, k)
    assert check_bits == bits and check_y == a*2**e
    assert N > n and N % modulus == r
    # The remaining e steps are exact halvings, checked separately in Lean.
    assert check_y >> e == a
    return dict(root=str(a), A=A, B=B, residue=r, prefix_steps=k,
                prefix_weight=j, halving_tail=e, ancestor_bits=N.bit_length())


def replay():
    records = []
    for a in (1, 5, 17, 2**128+1):
        for A in range(6):
            for B in range(3):
                for r in range(2**A*3**B):
                    records.append(shadow(a, A, B, r))
    # Independent exhaustive modular check of the lifting routine itself.
    lifts = 0
    for J in range(1, 7):
        modulus = 3**J
        for a in (1, 5, 17):
            seen = {a*pow(2, e, modulus) % modulus for e in range(2*3**(J-1))}
            assert seen == {r for r in range(modulus) if r % 3}
            for y in seen:
                power_lift(a, y, J)
                lifts += 1
    return dict(all_checks_passed=True, ancestor_checks=len(records),
                modular_lift_checks=lifts, roots=4, A_range=[0, 5], B_range=[0, 2],
                max_ancestor_bits=max(r['ancestor_bits'] for r in records),
                max_halving_tail=max(r['halving_tail'] for r in records),
                records=records)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    data = replay()
    (OUT/'replay.json').write_text(json.dumps(data, indent=2)+'\n')
    sources = ['CollatzAffine.lean', 'lean/InverseFibreGrowth.lean',
               'lean/BasinResidueShadow.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-residue-shadow-') as build:
        for source in sources:
            stem = Path(source).stem
            command = ['lean', '-o', str(Path(build)/(stem+'.olean')), source]
            p = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log = OUT/(stem+'.log')
            log.write_text(p.stdout)
            commands.append(dict(command=command, returncode=p.returncode,
                                 log=str(log.relative_to(ROOT))))
            if p.returncode or 'sorryAx' in p.stdout:
                raise RuntimeError(f'Lean verification failed: {log}')
    files = sources+[Path(__file__).name, str((OUT/'replay.json').relative_to(ROOT))]
    files += [c['log'] for c in commands]
    manifest = dict(
        verified_at_utc=datetime.now(timezone.utc).isoformat(),
        conjecture_status='unresolved',
        lean_version=subprocess.check_output(['lean', '--version'], text=True).strip(),
        kernel_scope=[
            'A prefix containing an odd step ends at a root coprime to three',
            'Exact power equality transports a residue-cylinder member to its prescribed root',
            'The construction preserves residue modulo 2^k*3^b and prefix weight',
            'A forward-closed set containing the cylinder captures each root with such a power equality'],
        written_scope=[
            'Elementary induction proves powers of two run through all units modulo every power of three',
            'Every unit-root inverse basin meets every residue class modulo 2^A*3^B infinitely often',
            'An entire positive residue class converges if and only if all positive integers converge',
            'If a counterexample exists, both convergent and nonconvergent starts meet every such class'],
        not_proved=['Full Collatz conjecture',
                    'Kernel formalization of the universal modular lifting/existence theorem',
                    'A quantitative small-ancestor bound adequate for descent',
                    'A scale-dependent trapping certificate'],
        replay_summary={k:v for k,v in data.items() if k != 'records'}, commands=commands,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest, indent=2)+'\n')
    print(json.dumps(manifest['replay_summary'], indent=2))
    print('Three fresh Lean builds passed; universal existence remains a written proof.')


if __name__ == '__main__':
    main()
