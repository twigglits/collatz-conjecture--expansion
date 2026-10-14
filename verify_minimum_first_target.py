"""Audit actual half-source meetings and sharp first-target ancestry.

All finite paths and bounded-word minima are distinguished from global
minimum or least-counterexample hypotheses, which are never instantiated.
"""
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

ROOT=Path(__file__).resolve().parent
OUT=ROOT/"results/minimum-first-target"
PRIOR="results/minimum-mixed-ancestry/verification.json"
NEW_SOURCE="lean/MinimumFirstTarget.lean"
THEOREMS=["even_step","half_source_meeting","least_half_source_bound",
          "near_source_exit_constraint","least_initial_exit_constraint",
          "family_congruence","family_path","family_one_even","family_target_residue",
          "family_source_residue","family_pair_endpoint","family_first_pair_residue",
          "family_pair_avoids_target","family_odd_clock_avoids_target","family_bridge",
          "family_first_target","family_odd_depth","inverse_five_source_lower",
          "family_one_even_source_lower","family_all_odd_source_lower",
          "family_height_factor","family_source_growth","finite_first_target_witness"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path,value):
    Path(path).write_text(json.dumps(value,indent=2)+"\n")


def direct_path(n,clock):
    values=[n]
    for _ in range(clock):
        x=values[-1]
        values.append(3*x+1 if x%2 else x//2)
    return values


def paired_path(n,clock):
    values=[n]
    while len(values)<=clock:
        x=values[-1]
        if x%2:
            values.append(3*x+1)
            if len(values)<=clock:
                values.append((3*x+1)//2)
        else:
            values.append(x//2)
    return values


def inverse_candidates(b):
    # In reverse, every zero-even word is an odd-inverse prefix;
    # every one-even word doubles at exactly one of those points.
    pure=[b]
    while pure[-1]%3==2:
        pure.append((2*pure[-1]-1)//3)
    candidates=list(pure)
    for anchor in pure:
        x=2*anchor
        candidates.append(x)
        while x%3==2:
            x=(2*x-1)//3
            candidates.append(x)
    return pure,candidates


def meeting_checks(counts):
    rows=[]
    for k in range(65):
        for q in range(1,257):
            power=3**k*q
            if power%4!=3:
                continue
            v=(power-3)//4
            p=2**k*q-1
            n=2**(k+1)*q-1
            small=direct_path(p,2*k+3)
            large=direct_path(n,2*k+4)
            assert small==paired_path(p,2*k+3)
            assert large==paired_path(n,2*k+4)
            assert small[-1]==large[-1]==3*v+2
            assert 0<p<n and n==2*p+1
            counts["half_source_pairs"]+=1
            counts["meeting_ordinary_steps"]+=4*k+7
            counts["independent_meeting_path_comparisons"]+=2
            if k>0:
                # Integer compatibility only: the least-component hypothesis
                # would require floor<=p; a near return requires n<=2*floor.
                for floor in {1,p,p+1,n}:
                    assert not (floor<=p and n<=2*floor)
                    counts["near_floor_arithmetic_checks"]+=1
            if (k,q) in [(0,3),(1,1),(1,9),(2,3),(8,3),(64,255)]:
                rows.append({"k":k,"q":q,"small_source_bits":p.bit_length(),
                             "large_source_bits":n.bit_length(),
                             "small_clock":2*k+3,"large_clock":2*k+4,
                             "large_prefix_minimum_equals_source":min(large)==n})
    return {"complete_parameter_rectangle":{"k":[0,64],"q":[1,256]},
            "filter":"3^k*q=3 mod4","rows":rows,
            "scope":"Exact finite coalescence. Some paths descend; neither prefix nor global self-minimality is presumed. Floor tests are integer compatibility checks, not least-counterexample instantiations."}


def first_family_checks(counts):
    rows=[]
    for h in range(257):
        k=6*h+3
        n=5*2**k-1
        v=(5*3**k+1)//4
        b=3*v-1
        clock=2*k+3
        values=direct_path(n,clock)
        assert values==paired_path(n,clock)
        assert values[-1]==b and b%27==20
        assert all(x%27!=20 for x in values[:-1])
        assert min(values)==n
        quick=n
        parities=[]
        for _ in range(k+2):
            parities.append(quick%2)
            quick=(3*quick+1)//2 if quick%2 else quick//2
        assert parities==[1]*k+[0,1] and quick==b
        pure,candidates=inverse_candidates(b)
        assert len(pure)==2 and len(candidates)==k+4
        assert min(candidates)==n and candidates.count(n)==1
        assert min(pure)>n
        assert (h+1)*(n+1)<=b+1 and h<n and n%3==0
        counts["first_target_family_prefixes"]+=1
        counts["family_ordinary_steps"]+=clock
        counts["family_shortcut_steps"]+=k+2
        counts["family_inverse_candidates"]+=len(candidates)
        counts["family_prefix_residue_checks"]+=clock+1
        if h in [0,1,2,3,8,16,64,128,256]:
            rows.append({"h":h,"first_odd_block":k,"source_bits":n.bit_length(),
                         "target_bits":b.bit_length(),"first_ordinary_hit":clock,
                         "one_even_minimum_equals_original_source":True,
                         "height_ratio_at_least":h+1})
    return {"complete_family_index_interval":[0,256],"rows":rows,
            "scope":"First-hit times and complete inverse-word optimization with at most one even input. No convergence claim for the whole parameter family."}


def first_hit_census(counts,cutoff=65536,limit=4096):
    cache={}
    outcomes=Counter({name:0 for name in ["below_source","equal_source",
                     "above_source","reached_one_before_target","unfinished_at_cutoff"]})
    rows=[]
    for n in range(1,cutoff+1):
        q=n+1
        k=0
        while q%2==0:
            k+=1
            q//=2
        profile=(k>=2 and (3**k*q)%4==3 and n%3!=2 and n%9!=4)
        counts["explicit_profile_source_checks"]+=1
        values=[n]
        while values[-1]%27!=20 and values[-1]!=1 and len(values)-1<limit:
            x=values[-1]
            values.append(3*x+1 if x%2 else x//2)
        clock=len(values)-1
        assert values==paired_path(n,clock)
        counts["first_hit_census_sources"]+=1
        counts["first_hit_census_ordinary_steps"]+=clock
        b=values[-1]
        relation=None
        if b%27==20:
            assert all(x%27!=20 for x in values[:-1])
            if b not in cache:
                pure,candidates=inverse_candidates(b)
                cache[b]=min(pure),min(candidates)
                counts["census_distinct_targets"]+=1
                counts["census_inverse_candidates"]+=len(candidates)
            pure,minimum=cache[b]
            assert minimum<pure
            relation="below_source" if minimum<n else "equal_source" if minimum==n else "above_source"
            outcomes[relation]+=1
            if profile:
                assert clock==2*k+3 and 4*b+1==3**(k+1)*q
                assert minimum==n and pure>n and min(values)==n
                counts["explicit_profile_first_paths"]+=1
            if n in [27,39,2559] or (relation=="above_source" and len(rows)<8):
                rows.append({"source":n,"first_target":b,"first_clock":clock,
                             "all_odd_minimum":pure,"one_even_minimum":minimum,
                             "comparison":relation})
        elif b==1:
            outcomes["reached_one_before_target"]+=1
        else:
            outcomes["unfinished_at_cutoff"]+=1
        # The forward implication is proved in the written argument.
        # Its converse is recorded here ONLY over this finite interval.
        assert (relation=="equal_source")==profile
        counts["finite_profile_equality_comparisons"]+=1
    assert sum(outcomes.values())==cutoff
    return {"complete_source_interval":[1,cutoff],"ordinary_clock_limit":limit,
            "outcomes":dict(outcomes),"rows":rows,
            "explicit_profile":"n+1=2^K*q with q odd; K>=2, 3^K*q=3 mod4, n!=2 mod3, n!=4 mod9",
            "finite_only_equivalence":"On this interval, the first-target inverse minimum equals n exactly for the explicit profile. No universal converse is claimed.",
            "scope":"Stop at the first target, first one, or cutoff. First-target paths are not assumed to converge, and unfinished paths are retained. These are finite source statistics, not orbit-frequency or density statements."}


def convergence_checks(counts):
    rows=[]
    for n,t in [(39,34),(101,25),(2559,115),(73811,94)]:
        values=direct_path(n,t)
        assert values==paired_path(n,t) and values[-1]==1 and 1 not in values[:-1]
        counts["kernel_convergence_witnesses_replayed"]+=1
        counts["kernel_witness_ordinary_steps"]+=t
        rows.append({"source":n,"first_arrival_at_one":t})
    return {"rows":rows,"scope":"Kernel arrival witnesses; first-arrival minimality separately checked in Python."}


def build(sources):
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-first-target-") as directory:
        for source in sources:
            stem = Path(source).stem
            obj = Path(directory) / (stem + ".olean")
            log = OUT / (stem + ".log")
            command = ["lean", "-o", str(obj), source]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_PATH=directory, LEAN_NUM_THREADS="1"))
            log.write_text(result.stdout)
            assert result.returncode == 0, result.stdout
            assert not any(s in result.stdout for s in ("warning:", "error:", "sorryAx", "ofReduceBool"))
            roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout, re.M)
            if source == NEW_SOURCE:
                assert {name for name, _ in roots} == {stem + "." + t for t in THEOREMS}
                assert len(roots) == len(THEOREMS)
                assert set(re.findall(r"^theorem (\w+)", (ROOT / source).read_text(), re.M)) == set(THEOREMS)
                assert "'MinimumFirstTarget.finite_first_target_witness' does not depend on any axioms" in result.stdout
            for _, axioms in roots:
                assert {a.strip() for a in axioms.split(",") if a.strip()} <= {"propext", "Classical.choice", "Quot.sound"}
            builds.append({"source": source, "source_sha256": digest(ROOT / source),
                           "command": command, "returncode": 0, "fresh_build": True,
                           "native_computation_used": False,
                           "elapsed_seconds": round(time.monotonic() - started, 3),
                           "log": str(log.relative_to(ROOT)), "log_sha256": digest(log),
                           "olean_sha256": digest(obj)})
            print("Fresh Lean build passed:", source, flush=True)
    return version, builds


def main():
    OUT.mkdir(parents=True,exist_ok=True)
    record=json.loads((ROOT/PRIOR).read_text())
    assert record["status"]=="passed"
    for name,h in record["sha256"].items():
        assert digest(ROOT/name)==h,name
    sources=[b["source"] for b in record["builds"]]+[NEW_SOURCE]
    assert len(sources)==27
    print("Authenticated prior hashes:",len(record["sha256"]),flush=True)
    version,builds=build(sources)
    counts=Counter()
    meetings=meeting_checks(counts)
    print("Half-source meeting checks passed.",flush=True)
    family=first_family_checks(counts)
    print("First-target family and inverse minima passed.",flush=True)
    census=first_hit_census(counts)
    print("Complete finite first-hit census passed.",flush=True)
    convergence=convergence_checks(counts)
    save(OUT/"replay.json",{"status":"passed","counts":dict(counts),
                           "half_source_meetings":meetings,"first_target_family":family,
                           "finite_first_hit_census":census,"kernel_witnesses":convergence})
    files=sources+[Path(__file__).name,"docs/MINIMUM-FIRST-TARGET.md",PRIOR]
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name!="verification.json"]
    save(OUT/"verification.json",{
        "status":"passed","verified_at_utc":datetime.now(timezone.utc).isoformat(),
        "collatz_status":"unresolved","lean_version":version,"builds":builds,
        "kernel_theorems_audited":len(THEOREMS),
        "prior_hashes_validated":{PRIOR:len(record["sha256"])},
        "finite_replay_counts":dict(counts),"first_hit_outcomes":census["outcomes"],
        "kernel_scope":"Exact half-source coalescence and exclusion of a two-halving exit at qualifying least-component values at most twice the least source. An infinite family has exact first ordinary visits to 20 modulo 27 with unbounded relative height, while every all-odd and one-even affine predecessor is at least the original source and one is equal. Finite examples and four convergence arrivals are axiom-free kernel computations.",
        "written_scope":["Assembly of the complete zero/one-even word minima from the parameterized kernel inequalities.",
                         "For n+1=2^K*q with q odd, K>=2, 3^K*q=3 mod4, n!=2 mod3 and n!=4 mod9, the first target is (3^(K+1)*q-1)/4 at ordinary clock 2K+3 and its minimum zero/one-even predecessor is n. Existing least-counterexample restrictions imply this profile; the general assembly is written, not a new kernel root.",
                         "Comparison with sufficient-set occurrence and near-return research; no universal occurrence-height claim."],
        "external_dependency":"None for the new proofs. Monks et al. and a public near-return note are compared for scope; no external analytic theorem or finite convergence bound is assumed.",
        "finite_scope_limit":"First-hit and meeting censuses contain finite paths and bounded-word minima only. No unknown global minimum or least counterexample is numerically instantiated. The four displayed kernel arrivals are separate convergence witnesses.",
        "not_proved":["An encountered predecessor below every hypothetical least counterexample; repeated occurrence with a useful relative height or unbounded inverse complexity.",
                      "A universal cap/residual bound, exclusion of nontrivial cycles or divergence, or full Collatz."],
        "sha256":{p:digest(ROOT/p) for p in files}})
    print(json.dumps({"status":"passed","kernel_roots":len(THEOREMS),"counts":dict(counts),
                      "first_hit_outcomes":census["outcomes"]},indent=2))


if __name__=="__main__":
    main()
