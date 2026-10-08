"""Exact first-drop replay and fresh kernel builds.

The real logarithm bound is a written/external application, not a Lean
dependency. A search that exhausts its fuel is recorded as unresolved.
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
OUT = ROOT/'results/first-slope-budget'


def measure(n, fuel):
    x = n
    A = D = 1
    w = 0
    for k in range(1, fuel+1):
        assert D <= A
        if x % 2:
            x = (3*x+1)//2
            A *= 3
            w += 1
        else:
            x //= 2
        D *= 2
        assert 3*D*x <= A*(3*n+w)
        if A < D:
            gap = D-A
            gap_budget = A*w < 3*n*gap
            power_gap = A**5 < k**21*gap**5
            size_budget = k**26 <= (3*n)**5
            if power_gap and size_budget:
                assert gap_budget
            if gap_budget:
                assert x < n
            if k >= 5:
                assert 11*w <= 7*k and k < 2*w
            return dict(start=str(n),crossed=True,time=k,odd_steps=w,
                        endpoint=str(x),descended=x<n,
                        gap_budget_passed=gap_budget,
                        power_gap_passed=power_gap,size_budget_passed=size_budget,
                        multiplier_above_half=2*A>D,
                        multiplier_numerator=str(A),multiplier_denominator=str(D))
    return dict(start=str(n),crossed=False,fuel=fuel,unresolved=True)


def near_critical_roots(limit):
    # Exact ceil(t*log_3(2)), computed without logarithms.
    upper = [0]
    power = 1
    for t in range(1,limit+1):
        j = upper[-1]
        while power < 2**t:
            power *= 3
            j += 1
        upper.append(j)
    for k in range(2,limit+1):
        if upper[k-1] != upper[k]-1:
            continue
        counts = upper[:k]+[upper[k]-1]
        r = y = 0
        A = M = 1
        for t in range(1,k+1):
            bit = counts[t]-counts[t-1]
            assert bit in (0,1)
            lift = bit ^ (y%2)
            r += lift*M
            y += lift*A
            assert y%2 == bit
            y = (3*y+1)//2 if bit else y//2
            A *= 3**bit
            M *= 2
        assert 0 < r < M and A < M
        for q in (0,1,3):
            n = r+M*q
            record = measure(n,k)
            assert record['crossed'] and record['time']==k
            assert record['odd_steps']==counts[k]
            assert int(record['endpoint'])==y+A*q
            record.update(prescribed_time=k,lift=q)
            yield record


def replay():
    interval = [measure(n,10000) for n in range(1,32769)]
    family = list(near_critical_roots(512))
    crossed = [r for r in interval if r['crossed']]
    def summary(rows):
        finite = [r for r in rows if r['crossed']]
        return dict(cases=len(rows),crossings=len(finite),
                    gap_budget_passes=sum(r['gap_budget_passed'] for r in finite),
                    power_certificates=sum(r['power_gap_passed'] and r['size_budget_passed'] for r in finite),
                    power_gap_failures=sum(not r['power_gap_passed'] for r in finite),
                    first_drop_non_descent_starts=[r['start'] for r in finite if not r['descended']],
                    unresolved=[r for r in rows if not r['crossed']])
    return dict(all_arithmetic_checks_passed=True,
                universal_crossing_existence_proved=False,
                interval=[1,32768],interval_summary=summary(interval),
                interval_gap_budget_failures=[r for r in crossed if not r['gap_budget_passed']],
                family_max_time=512,family_summary=summary(family),
                closest_multiplier_examples=sorted(family,
                    key=lambda r:Fraction(int(r['multiplier_denominator'])-int(r['multiplier_numerator']),
                                          int(r['multiplier_numerator'])))[:9],
                family_records=family)


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    data = replay()
    (OUT/'replay.json').write_text(json.dumps(data,indent=2)+'\n')
    sources = ['CollatzAffine.lean','CollatzContradiction.lean','CollatzGrowth.lean',
               'lean/CoalescenceDescent.lean','lean/CoalescenceEnvelope.lean',
               'lean/FirstSlopeBudget.lean']
    commands = []
    with tempfile.TemporaryDirectory(prefix='collatz-first-slope-budget-') as build:
        for source in sources:
            stem = Path(source).stem
            cmd = ['lean','-o',str(Path(build)/(stem+'.olean')),source]
            result = subprocess.run(cmd,cwd=ROOT,env=dict(os.environ,LEAN_PATH=build),
                                    text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            log = OUT/(stem+'.log')
            log.write_text(result.stdout)
            commands.append(dict(command=cmd,returncode=result.returncode,log=str(log.relative_to(ROOT))))
            if result.returncode or 'sorryAx' in result.stdout or 'ofReduceBool' in result.stdout:
                raise RuntimeError(f'Fresh Lean build failed: {log}')
    summary = {k:v for k,v in data.items() if k not in
               ('family_records','closest_multiplier_examples','interval_gap_budget_failures')}
    files = sources+[Path(__file__).name,str((OUT/'replay.json').relative_to(ROOT))]
    files += [c['log'] for c in commands]
    manifest = dict(verified_at_utc=datetime.now(timezone.utc).isoformat(),
                    conjecture_status='unresolved',
                    lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
                    kernel_scope=[
                        'Prefix bound 3*2^k*U^k(n)<=3^w*(3*n+w) before a first drop below one',
                        'Actual descent when 3^w*w<3*n*(2^k-3^w)',
                        'A rational power-gap hypothesis and polynomial size budget imply actual descent',
                        'The (p,q)=(21,5) specialization uses k^26<=(3*n)^5',
                        'Kernel examples at 7, 27, and an explicit 65-step multiplier above one half'],
                    written_scope=[
                        'Wu-Wang Theorem 1 supplies an effective asymptotic logarithm gap',
                        'The prior explicit logarithm argument supplies the 21/5 gap for k>=10^4000 at a first drop',
                        'The real logarithm-to-integer-power conversion is a written proof'],
                    not_proved=[
                        'A first coefficient drop for every positive starting value',
                        'A universal upper bound on the first-drop time',
                        'The unrestricted coefficient stopping-time claim',
                        'Full Collatz conjecture'],
                    replay_summary=summary,commands=commands,
                    sha256={f:hashlib.sha256((ROOT/f).read_bytes()).hexdigest() for f in files})
    (OUT/'verification.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    print('Six fresh Lean builds passed. The universal existence premise remains unproved.')


if __name__ == '__main__':
    main()
