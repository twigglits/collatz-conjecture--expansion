"""Audit exact inverse minima at repeated actual Collatz target visits.

Finite bounded-word minima, prefix minima, and explicit convergence
witnesses are distinct. No global minimum is assigned to an unfinished orbit.
"""
from collections import Counter
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

ROOT=Path(__file__).resolve().parent
OUT=ROOT/'results/minimum-return-ladder'
PRIOR='results/minimum-first-target/verification.json'
NEW_SOURCE='lean/MinimumReturnLadder.lean'
THEOREMS=['backtrack_actual','companion_even','companion_odd','odd_power_residue',
          'odd_budget_gap','offset_buffer','companion','product_lower','hit_lift',
          'scaled_companion','inverse_ladder_lower','product_monotone','block_monotone',
          'bounded_inverse_lower','backtrack_append','five_block','five_block_inverse',
          'block_coordinates','block_prefix','ladder_attained','hit_clock','hit_residue',
          'block_residues','block_hit_positions','all_hit_positions','exact_inverse_minimum',
          'source_strict','required_even_budget','source_growth',
          'arbitrarily_many_unhelpful_visits','finite_ladder_witness']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path,value):
    Path(path).write_text(json.dumps(value,indent=2)+'\n')


def ordinary(n,t):
    out=[n]
    for _ in range(t):
        x=out[-1]
        out.append(3*x+1 if x%2 else x//2)
    return out


def paired(n,t):
    out=[n]
    while len(out)<=t:
        x=out[-1]
        if x%2:
            out.append(3*x+1)
            if len(out)<=t:
                out.append((3*x+1)//2)
        else:
            out.append(x//2)
    return out


def inverse_minimum(counts,prefix):
    @lru_cache(None)
    def minimum(b,r):
        counts[prefix+'_inverse_states']+=1
        if b%3==0:
            # Every predecessor of a positive multiple of 3 is a doubling.
            return b
        pure=[b]
        while pure[-1]%3==2:
            pure.append((2*pure[-1]-1)//3)
            counts[prefix+'_inverse_odd_edges']+=1
        best=pure[-1]
        if r:
            for x in pure:
                counts[prefix+'_inverse_even_edges']+=1
                best=min(best,minimum(2*x,r-1))
        return best
    return minimum


def forward_inverse_census(counts,cutoff=65536,budget=4):
    tables=[list(range(cutoff+1)) for _ in range(budget+1)]
    for n in range(1,cutoff+1):
        x=n;e=0
        while True:
            if x<=cutoff:
                for r in range(e,budget+1):
                    tables[r][x]=min(tables[r][x],n)
                    counts['forward_minimum_visits']+=1
            if x%2:
                y=3*x+1
                assert y%2==0
                x=y//2
                counts['forward_ordinary_steps']+=2
            else:
                if e==budget:
                    break
                e+=1
                x//=2
                counts['forward_ordinary_steps']+=1
            counts['forward_shortcut_steps']+=1
        counts['forward_sources']+=1
    minimum=inverse_minimum(counts,'census')
    strict=Counter({str(r):0 for r in range(1,budget+1)})
    for b in range(1,cutoff+1):
        for r in range(budget+1):
            assert minimum(b,r)==tables[r][b]
            counts['independent_forward_inverse_comparisons']+=1
            if r and tables[r][b]<tables[r-1][b]:
                strict[str(r)]+=1
    states=minimum.cache_info().currsize
    minimum.cache_clear()
    return {'complete_source_and_target_interval':[1,cutoff],
            'complete_even_budget_interval':[0,budget],
            'strict_improvements_over_previous_budget':dict(strict),
            'distinct_inverse_states':states,
            'scope':'Complete bounded-word minima. Each forward source stops before its fifth even input; no convergence interval or global orbit minimum is inferred.'}


def block(R,i):
    return 9**i*8**(R-i)-5


def hit(R,i):
    return (3*block(R,i)+1)//2


def family_replay(counts):
    minimum=inverse_minimum(counts,'family')
    indices=list(range(3,66,2))+[129,257,1025]
    rows=[]
    for R in indices:
        n=8**R-5
        values=ordinary(n,5*R)
        assert values==paired(n,5*R)
        assert min(values)==n and values[-1]==9**R-5
        assert [t for t,x in enumerate(values[:-1]) if x%27==20]==[5*i+2 for i in range(1,R)]
        assert values[-1]%27!=20
        x=n;word=[]
        for _ in range(3*R):
            word.append(x%2)
            x=(3*x+1)//2 if x%2 else x//2
        assert word==[1,1,0]*R and x==values[-1]
        counts['family_sources']+=1
        counts['family_ordinary_steps']+=5*R
        counts['family_shortcut_steps']+=3*R
        counts['family_prefix_residue_checks']+=5*R+1
        for i in range(R+1):
            assert values[5*i]==block(R,i)
            counts['block_endpoints']+=1
        for i in range(1,R):
            b=hit(R,i)
            assert values[5*i+2]==b
            assert b+7==3**(2*i+1)*2**(3*(R-i)-1)
            assert (4*b+1)%81==(27 if i==1 else 54)
            counts['target_visits']+=1
            counts['ternary_coordinate_checks']+=2
            if R>65 and i not in {1,2,8,R//2,R-1}:
                continue
            budgets=range(i+1) if R<=17 else range(min(i,8)+1)
            for r in budgets:
                p=block(R,i-r)
                assert minimum(b,r)==p
                witness=ordinary(p,5*r+2)
                assert witness==paired(p,5*r+2) and witness[-1]==b and min(witness)==p
                x=p;parities=[]
                for _ in range(3*r+1):
                    parities.append(x%2)
                    x=(3*x+1)//2 if x%2 else x//2
                assert x==b and parities==[1,1,0]*r+[1]
                assert p>=n and (p==n)==(r==i)
                counts['family_inverse_minima']+=1
                counts['attaining_ordinary_steps']+=5*r+2
                counts['attaining_shortcut_steps']+=3*r+1
        if R in [3,5,7,17,65,129,257,1025]:
            rows.append({'R':R,'source_bits':n.bit_length(),'ordinary_prefix':5*R,
                         'exact_number_of_target_visits':R-1,
                         'inverse_budgets':'all 0..i' if R<=17 else '0..min(i,8)',
                         'inverse_target_indices':'all 1..R-1' if R<=65 else sorted({1,2,8,R//2,R-1})})
        minimum.cache_clear()
    return {'complete_small_odd_R_interval':[3,65],'additional_R':[129,257,1025],
            'rows':rows,'scope':'Actual finite prefixes for every listed source. Full target visitation is checked; larger inverse queries are sampled as explicitly listed. No convergence theorem for the family is assumed.'}


def companion_replay(counts):
    queries=0
    for R in range(3,18,2):
        for i in range(1,R):
            for r in range(i+1):
                b=hit(R,i)
                stack=[(b,7,0,0)]
                best=b
                while stack:
                    x,m,e,o=stack.pop()
                    assert e<=r<=i and o<=2*e+1
                    d=2*e+1-o
                    assert 5<=m<=7*2**e
                    assert 2**d*(m-1)<=4*3**d
                    assert 3**o*(x+m)==2**(e+o)*(b+7)
                    assert 2**d*(x+m)==3**d*(block(R,i-e)+5)
                    assert x>=block(R,i-e)>=block(R,i-r)
                    best=min(best,x)
                    counts['companion_inverse_nodes']+=1
                    if e<r:
                        stack.append((2*x,2*m,e+1,o))
                    if x%3==2:
                        assert (2*m+1)%3==0
                        stack.append(((2*x-1)//3,(2*m+1)//3,e,o+1))
                assert best==block(R,i-r)
                queries+=1
    counts['complete_companion_queries']=queries
    return {'complete_R_values':list(range(3,18,2)),
            'for_each_R':'all i=1..R-1 and all r=0..i',
            'scope':'Every inverse word within each finite budget is traversed, including nonminimal branches. The negative magnitude is arithmetic bookkeeping and is never used as a positive Collatz trajectory.'}


def convergence_replay(counts):
    rows=[]
    for n,t in [(507,35),(857,28),(965,23),(32763,160)]:
        xs=ordinary(n,t)
        assert xs==paired(n,t) and xs[-1]==1 and 1 not in xs[:-1]
        counts['kernel_arrival_witnesses']+=1
        counts['kernel_arrival_ordinary_steps']+=t
        rows.append({'source':n,'first_arrival':t})
    return {'rows':rows,'scope':'Arrival existence is kernel checked; first-arrival minimality is independently checked here.'}


def build(sources):
    version=subprocess.check_output(['lean','--version'],text=True).strip()
    builds=[]
    with tempfile.TemporaryDirectory(prefix='collatz-return-ladder-') as directory:
        for source in sources:
            stem=Path(source).stem
            obj=Path(directory)/(stem+'.olean')
            log=OUT/(stem+'.log')
            command=['lean','-o',str(obj),source]
            started=time.monotonic()
            result=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,
                                  stderr=subprocess.STDOUT,
                                  env=dict(os.environ,LEAN_PATH=directory,LEAN_NUM_THREADS='1'))
            log.write_text(result.stdout)
            assert result.returncode==0,result.stdout
            assert not any(s in result.stdout for s in ('warning:','error:','sorryAx','ofReduceBool'))
            roots=re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",result.stdout,re.M)
            if source==NEW_SOURCE:
                assert {n for n,_ in roots}=={stem+'.'+t for t in THEOREMS}
                assert len(roots)==len(THEOREMS)
                assert set(re.findall(r'^theorem (\w+)',(ROOT/source).read_text(),re.M))==set(THEOREMS)
                assert "'MinimumReturnLadder.finite_ladder_witness' does not depend on any axioms" in result.stdout
            for _,axioms in roots:
                assert {a.strip() for a in axioms.split(',') if a.strip()}<={'propext','Classical.choice','Quot.sound'}
            builds.append({'source':source,'source_sha256':digest(ROOT/source),
                           'command':command,'returncode':0,'fresh_build':True,
                           'native_computation_used':False,
                           'elapsed_seconds':round(time.monotonic()-started,3),
                           'log':str(log.relative_to(ROOT)),'log_sha256':digest(log),
                           'olean_sha256':digest(obj)})
            print('Fresh Lean build passed:',source,flush=True)
    return version,builds


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    prior=json.loads((ROOT/PRIOR).read_text())
    assert prior['status']=='passed'
    for name,h in prior['sha256'].items():
        assert digest(ROOT/name)==h,name
    print('Authenticated prior hashes:',len(prior['sha256']),flush=True)
    sources=[b['source'] for b in prior['builds']]+[NEW_SOURCE]
    assert len(sources)==28
    version,builds=build(sources)
    counts=Counter()
    census=forward_inverse_census(counts)
    print('Complete bounded-word forward/inverse census passed.',flush=True)
    family=family_replay(counts)
    print('Actual return prefixes and exact inverse minima passed.',flush=True)
    companions=companion_replay(counts)
    print('All finite companion branches passed.',flush=True)
    arrivals=convergence_replay(counts)
    save(OUT/'replay.json',{'status':'passed','counts':dict(counts),'bounded_word_census':census,
                          'return_family':family,'companion_branches':companions,'kernel_arrivals':arrivals})
    files=sources+[Path(__file__).name,'docs/MINIMUM-RETURN-LADDER.md',PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name!='verification.json']
    save(OUT/'verification.json',{
        'status':'passed','verified_at_utc':datetime.now(timezone.utc).isoformat(),
        'collatz_status':'unresolved','lean_version':version,'builds':builds,
        'kernel_theorems_audited':len(THEOREMS),'prior_hashes_validated':{PRIOR:len(prior['sha256'])},
        'finite_replay_counts':dict(counts),
        'kernel_scope':'For odd R and i<R, exact bounded-even inverse minima at the actual hit (3*(9^i*8^(R-i)-5)+1)/2 equal 9^(i-r)*8^(R-i+r)-5 for 0<=r<=i. All inverse words are covered by the inductive Backtrack relation and an arithmetic companion invariant. Exact prefix minimum, ordinary visit classification, arbitrary consecutive unhelpful windows at fixed inverse budget, and four axiom-free convergence witnesses are included.',
        'written_scope':['Identification of ordinary visits 7,12,...,5R-3 as the numbered target visits for odd R>=3.',
                         'Exact ternary valuations v3(hit+7)=2i+1 and v3(4*hit+1)=3 from the displayed formulas.',
                         'Comparison with the negative five cycle and external residue-class ancestor work; no external theorem is imported.'],
        'external_dependency':'None for the new proofs. Two public research notes were reviewed for scope only; no external computation or theorem was adopted.',
        'finite_scope_limit':'The complete target/source census covers budgets 0..4. Family prefixes and sampled larger inverse queries have explicit ranges. No unknown global minimum or hypothetical least counterexample is numerically instantiated.',
        'not_proved':['The inverse minimum for budgets r>i, or absence of every smaller ancestor with unbounded inverse complexity.',
                      'Universal convergence of this parameterized family, or a single orbit with infinitely many unhelpful visits.',
                      'A useful later target for every least counterexample, a universal cap/residual bound, or full Collatz.'],
        'sha256':{p:digest(ROOT/p) for p in files}})
    print(json.dumps({'status':'passed','kernel_roots':len(THEOREMS),'counts':dict(counts)},indent=2))


if __name__=='__main__':
    main()
