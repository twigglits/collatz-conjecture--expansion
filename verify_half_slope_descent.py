"""Replay the half-multiplier certificate and build its universal Lean proof.

Finite searches report fuel exhaustion as unresolved. They do not establish
that all positive starts have a crossing within the required size budget.
"""
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT/'results/half-slope-descent'


def measure(n, fuel):
    x = n
    A = D = 1
    w = 0
    first_descent = None
    peak = n
    for k in range(1, fuel+1):
        # All previous states are above the half-multiplier line, by
        # stopping at its first crossing. Track exact integers throughout.
        assert D <= 2*A
        if x % 2:
            x = (3*x+1)//2
            A *= 3
            w += 1
        else:
            x //= 2
        D *= 2
        peak = max(peak, x)
        assert 3*D*x <= A*(3*n+2*w)
        if first_descent is None and x < n:
            first_descent = k
        if 2*A <= D:
            odd_budget = 2*w < 3*n
            if odd_budget:
                assert x < n
            if k <= n:
                assert odd_budget and x < n
            return dict(start=str(n), crossed=True, time=k, odd_steps=w,
                        endpoint=str(x), odd_budget_passed=odd_budget,
                        linear_time_passed=k<=n, first_descent=first_descent,
                        start_bits=n.bit_length(), peak_bits=peak.bit_length())
    return dict(start=str(n), crossed=False, fuel=fuel, unresolved=True)


def replay():
    interval = [measure(n, 10000) for n in range(1,32769)]
    interval_unresolved = [r for r in interval if not r['crossed']]
    passed = [r for r in interval if r['crossed']]
    budget_failures = [r for r in passed if not r['odd_budget_passed']]
    linear_failures = [r for r in passed if not r['linear_time_passed']]
    worst = sorted((r for r in passed if int(r['start'])>1),
                   key=lambda r: Fraction(2*r['odd_steps'],3*int(r['start'])),
                   reverse=True)[:12]
    family = []
    for K in range(1,513):
        p,q = 2**K,3**K
        for residue in (0,1):
            r = residue+q*(((-1-residue)*pow(q,-1,p)) % p)
            if r <= 1:
                r += p*q
            for t in (0,1,3):
                n = r+p*q*t
                assert n % q == residue and (n+1) % p == 0
                result = measure(n, 100*K+1000)
                result.update(K=K, three_adic_residue=residue, lift=t)
                family.append(result)
    unresolved = interval_unresolved+[r for r in family if not r['crossed']]
    return dict(all_arithmetic_checks_passed=True, universal_crossing_proved=False,
                interval=[1,32768], interval_crossings=len(passed),
                interval_budget_failures=budget_failures,
                interval_linear_time_failures=linear_failures,
                closest_positive_budget_examples=worst,
                family_depth_range=[1,512], family_cases=len(family),
                family_crossings=sum(r['crossed'] for r in family),
                family_budget_failures=[r for r in family if r['crossed'] and not r['odd_budget_passed']],
                family_linear_time_failures=[r for r in family if r['crossed'] and not r['linear_time_passed']],
                unresolved=unresolved, family_records=family)


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    data = replay()
    (OUT/'replay.json').write_text(json.dumps(data,indent=2)+'\n')
    sources = ['CollatzAffine.lean','CollatzContradiction.lean','CollatzGrowth.lean',
               'lean/CoalescenceDescent.lean','lean/CoalescenceEnvelope.lean',
               'lean/HalfSlopeDescent.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-half-slope-') as build:
        for source in sources:
            stem = Path(source).stem
            cmd = ['lean','-o',str(Path(build)/(stem+'.olean')),source]
            p = subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_PATH=build),
                               text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            log = OUT/(stem+'.log')
            log.write_text(p.stdout)
            commands.append(dict(command=cmd,returncode=p.returncode,
                                 log=str(log.relative_to(ROOT))))
            if p.returncode or 'sorryAx' in p.stdout:
                raise RuntimeError(f'Lean verification failed: {log}')
    summary = {k:v for k,v in data.items() if k not in (
        'family_records','closest_positive_budget_examples',
        'interval_budget_failures','interval_linear_time_failures',
        'family_budget_failures','family_linear_time_failures')}
    summary['interval_budget_failure_starts'] = [r['start'] for r in data['interval_budget_failures']]
    summary['interval_linear_time_failure_starts'] = [r['start'] for r in data['interval_linear_time_failures']]
    summary['family_budget_failure_count'] = len(data['family_budget_failures'])
    summary['family_linear_time_failure_count'] = len(data['family_linear_time_failures'])
    files = sources+[Path(__file__).name,str((OUT/'replay.json').relative_to(ROOT))]
    files += [c['log'] for c in commands]
    manifest = dict(
        verified_at_utc=datetime.now(timezone.utc).isoformat(),conjecture_status='unresolved',
        lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
        kernel_scope=[
            'Prefix bound 3*2^k*U^k(n) <= 3^w*(3*n+2*w) before the first half crossing',
            'A first half crossing with 2*w<3*n gives actual descent',
            'Any half crossing by time n gives descent no later than the supplied crossing time',
            'A global crossing certificate beyond a convergent finite base would imply Collatz',
            'Exact 27 certificate at time 65 and necessity of a budget illustrated by the cycle of one'],
        not_proved=['Existence of a suitably early crossing for every positive start',
                    'A universal logarithmic return-time bound',
                    'Terras first-coefficient-stopping-time conjecture',
                    'Full Collatz conjecture'],
        replay_summary=summary,commands=commands,
        sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print('Six fresh Lean builds passed; no universal crossing bound is claimed.')


if __name__ == '__main__':
    main()
