"""Kernel audit and independent forward/inverse checks of mixed ancestry.

The finite censuses never instantiate a least counterexample. Unknown
infinite minima are never assigned from finite paths.
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

ROOT = Path(__file__).resolve().parent
OUT = ROOT / "results/minimum-mixed-ancestry"
PRIORS = ["results/minimum-root-predecessors/verification.json",
          "results/minimum-critical-clock-lift/verification.json",
          "results/marked-preimage-audit/verification.json"]
NEW_SOURCE = "lean/MinimumMixedAncestry.lean"
THEOREMS = ["word_minimum_transport", "least_word_predecessor", "least_word_affine_lower",
            "two_binary_below_ternary", "one_even_block", "one_even_global_transport",
            "one_even_root_predecessor", "least_one_even_predecessor",
            "doubled_nonterminal_has_no_odd_parent", "doubling_inverse_improves_iff",
            "maximal_doubling_inverse_residue", "least_not_four_mod_nine", "shortcut_append",
            "shortcut_odd_block", "one_even_shortcut_count", "mixed_lift_spec",
            "first_length_bounds", "mixed_family_congruence", "mixed_family_path",
            "mixed_family_one_even", "mixed_source_scale", "mixed_source_growth",
            "mixed_target_scale", "mixed_target_height", "linear_three_two",
            "mixed_family_height_factor", "one_even_beats_all_odd",
            "unbounded_mixed_improvement", "finite_mixed_witness", "finite_height_witness"]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def direct_path(n, clock):
    values = [n]
    for _ in range(clock):
        x = values[-1]
        values.append(3*x+1 if x%2 else x//2)
    return values


def shortcut_path(n, clock):
    values = [n]
    ordinary = [n]
    parities = []
    for _ in range(clock):
        x = values[-1]
        parities.append(x%2)
        if x%2:
            ordinary += [3*x+1, (3*x+1)//2]
            values.append((3*x+1)//2)
        else:
            ordinary.append(x//2)
            values.append(x//2)
    return values, ordinary, parities


def valuation3(n):
    assert n > 0
    k = 0
    while n%3 == 0:
        n //= 3
        k += 1
    return k, n


def inverse_census(counts, cutoff=65536):
    pure = [0]*(cutoff+1)
    mixed = [0]*(cutoff+1)
    rows = []
    for b in range(1, cutoff+1):
        s, v = valuation3(b+1)
        pure[b] = 2**s*v-1
        best = pure[b]
        best_word = None
        for j in range(s+1):
            vj = (b+1)//3**j
            k, q = valuation3(2**(j+1)*vj-1)
            p = 2**k*q-1
            counts["one_even_inverse_branches"] += 1
            if p < best:
                best, best_word = p, (k,j,q,vj)
        mixed[b] = best
        counts["inverse_targets"] += 1
        assert (best < pure[b]) == (pure[b]%9 == 4)
        counts["reduced_residue_criterion_comparisons"] += 1
        if best < pure[b]:
            counts["strict_one_even_improvements"] += 1
            k,j,q,vj = best_word
            assert k >= 2 and q%2 == 1 and best >= 1
            clock = 2*k+1+2*j
            values = direct_path(best, clock)
            quick, paired, parities = shortcut_path(best, k+1+j)
            assert values == paired and values[-1] == quick[-1] == b
            assert parities == [1]*k+[0]+[1]*j
            assert min(values) == best
            counts["strict_branch_ordinary_steps"] += clock
            if len(rows)<12 or b == 152:
                rows.append({"target":b,"all_odd_minimum":pure[b],"one_even_minimum":best,
                             "first_odd_block":k,"last_odd_block":j,"ordinary_clock":clock})
    # Independent FORWARD census: every source that could be a minimum
    # predecessor of b<=cutoff is itself <=cutoff. Stop before a second
    # even-input shortcut step, and include every preceding endpoint.
    pure_forward = list(range(cutoff+1))
    mixed_forward = list(range(cutoff+1))
    for n in range(1, cutoff+1):
        x, evens, steps = n, 0, 0
        while True:
            if x <= cutoff:
                mixed_forward[x] = min(mixed_forward[x],n)
                if evens == 0:
                    pure_forward[x] = min(pure_forward[x],n)
                counts["forward_in_range_endpoints"] += 1
            if x%2 == 0:
                if evens == 1:
                    break
                evens += 1
                x //= 2
            else:
                x = (3*x+1)//2
            steps += 1
            # Explicit diagnostic guard. A failure is not convergence.
            assert steps < 4*cutoff.bit_length()+8
        counts["forward_sources"] += 1
        counts["forward_shortcut_steps"] += steps
    assert pure == pure_forward and mixed == mixed_forward
    counts["independent_minimum_comparisons"] += 2*cutoff
    residue_counts = []
    for exponent in range(cutoff.bit_length()):
        bound = 2**exponent
        total = 0
        scale = 1
        s = 0
        while scale <= bound+1:
            q0 = (5*pow(2,-s,9))%9
            residue = scale*q0-1
            modulus = 9*scale
            if residue <= bound:
                total += (bound-residue)//modulus+1
            scale *= 3
            s += 1
        direct = sum(mixed[b]<pure[b] for b in range(1,bound+1))
        assert total == direct
        counts["progression_union_counts"] += 1
        residue_counts.append({"cutoff":bound,"strict_improvements":total})
    return {"complete_target_interval":[1,cutoff],"complete_forward_source_interval":[1,cutoff],
            "maximum_even_input_shortcut_steps":1,"rows":rows,"progression_counts":residue_counts,
            "scope":"Exact minimum among finite predecessor words with zero or at most one even-input shortcut step. These are not global orbit minima or a convergence census."}


def lifting_checks(counts):
    a = 0
    rows = []
    low_exponents = []
    for j in range(129):
        modulus = 2**(j+3)
        assert a < 2**j and (15*pow(9,a,modulus)+1)%modulus == 0
        counts["modular_lift_levels"] += 1
        if j <= 12:
            # Enumerate the whole exponent period independently of the lift.
            residues = []
            nine = 1
            for e in range(2**j):
                if (15*nine+1)%modulus == 0:
                    residues.append(e)
                nine = nine*9%modulus
                counts["complete_exponent_residues"] += 1
            assert residues == [a]
            counts["unique_lift_periods"] += 1
        k = 2*(a+2**j)+1
        assert 2**(j+1)+1 <= k < 2**(j+2)+1
        assert (5*pow(3,k,modulus)+1)%modulus == 0
        if j <= 10:
            low_exponents.append((j,k))
            n = 5*2**k-1
            v = (5*3**k+1)//modulus
            b = 3**(j+2)*v-1
            clock = 2*k+1+2*(j+2)
            values = direct_path(n,clock)
            quick,paired,parities = shortcut_path(n,k+1+j+2)
            assert values == paired and values[-1] == quick[-1] == b
            assert parities == [1]*k+[0]+[1]*(j+2)
            assert min(values) == n and n+2 < 2**(k+3)
            assert modulus*(b+1) == 3**(j+2)*(5*3**k+1)
            assert 24*(b+1)*2**j >= 5*3**j*3**(k+3)
            for h in range(j//10+1):
                assert h*3**(k+3) <= b+1
                counts["family_height_factor_comparisons"] += 1
            depth,v3part = valuation3(b+1)
            minimum_all_odd = 2**depth*v3part-1
            if b+1 >= 3**(k+3):
                assert minimum_all_odd >= n+2
                counts["family_past_all_odd_barrier"] += 1
            counts["exact_family_prefixes"] += 1
            counts["family_ordinary_steps"] += clock
            counts["family_shortcut_steps"] += len(parities)
            rows.append({"lift_index":j,"first_odd_block":k,"last_odd_block":j+2,
                         "source_bits":n.bit_length(),"target_bits":b.bit_length(),
                         "ordinary_clock":clock,"source_is_prefix_minimum":True,
                         "integer_height_factor":(b+1)//3**(k+3),
                         "all_odd_ancestors_exceed_source_plus_one":minimum_all_odd>=n+2})
        next_modulus = 2*modulus
        top_bit = ((15*pow(9,a,next_modulus)+1)%next_modulus)//modulus
        if top_bit:
            a += 2**j
    for j in list(range(513))+[1024,2048,4096]:
        assert (j+2)*2**j <= 2*3**j
        for h in [0,1,j//10]:
            if 10*h<=j:
                assert 24*h*2**j<=5*3**j
                counts["large_index_height_arithmetic"] += 1
    return {"modular_indices":[0,128],"complete_exponent_period_indices":[0,12],
            "exact_source_prefix_indices":[0,10],"rows":rows,
            "scope":"The modular checks at large indices do not construct or traverse sources of exponentially large bit length. All displayed source paths are finite prefixes; no global-minimum claim is inferred."}


def witness_checks(counts):
    rows = []
    for n,t in [(39,34),(152,23),(45035996273704959,751),(551968206708544316592375437,632)]:
        values = direct_path(n,t)
        assert values[-1]==1 and 1 not in values[:-1]
        # Independent backwards edge check, then shortcut traversal to first 1.
        for x,y in zip(reversed(values[:-1]),reversed(values[1:])):
            assert (x==2*y and x%2==0) or (3*x+1==y and x%2==1)
        x, reconstructed = n,[n]
        while x!=1:
            if x%2:
                reconstructed += [3*x+1,(3*x+1)//2]
                x=(3*x+1)//2
            else:
                x//=2
                reconstructed.append(x)
        assert values==reconstructed
        counts["kernel_convergence_witnesses_replayed"] += 1
        counts["kernel_witness_ordinary_steps"] += t
        rows.append({"source":n,"first_arrival_at_one":t})
    return {"rows":rows,"scope":"These four arrivals are kernel proved; first-arrival minimality is separately checked in Python."}


def build(sources):
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    builds = []
    with tempfile.TemporaryDirectory(prefix="collatz-mixed-ancestry-") as directory:
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
                assert "'MinimumMixedAncestry.finite_mixed_witness' does not depend on any axioms" in result.stdout
                assert "'MinimumMixedAncestry.finite_height_witness' does not depend on any axioms" in result.stdout
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
    sources = []
    authenticated = {}
    for name in PRIORS:
        record=json.loads((ROOT/name).read_text())
        assert record["status"]=="passed"
        for filename,expected in record["sha256"].items():
            assert digest(ROOT/filename)==expected,filename
        authenticated[name]=len(record["sha256"])
        for build_entry in record["builds"]:
            if build_entry["source"] not in sources:
                sources.append(build_entry["source"])
    sources.append(NEW_SOURCE)
    assert len(sources)==26
    print("Prior hashes authenticated:",authenticated,flush=True)
    version,builds=build(sources)
    counts=Counter()
    census=inverse_census(counts)
    print("Independent complete forward/inverse census passed.",flush=True)
    lifts=lifting_checks(counts)
    print("Modular lift and exact family prefixes passed.",flush=True)
    witnesses=witness_checks(counts)
    save(OUT/"replay.json",{"status":"passed","counts":dict(counts),
                            "bounded_even_ancestry":census,"lift_family":lifts,
                            "convergence_witnesses":witnesses})
    files=sources+[Path(__file__).name,"docs/MINIMUM-MIXED-ANCESTRY.md"]+PRIORS
    files += [str(p.relative_to(ROOT)) for p in sorted(OUT.iterdir())
              if p.is_file() and p.name!="verification.json"]
    save(OUT/"verification.json",{
        "status":"passed","verified_at_utc":datetime.now(timezone.utc).isoformat(),
        "collatz_status":"unresolved","lean_version":version,"builds":builds,
        "kernel_theorems_audited":len(THEOREMS),"prior_hashes_validated":authenticated,
        "finite_replay_counts":dict(counts),
        "kernel_scope":"Admissible mixed valuation words inherit the least-component lower bound. Two odd blocks separated by one even-input shortcut step have exact ordinary endpoint, prefix minimum, and parity count. The reduced-target arithmetic characterizes strict improvement and excludes least sources congruent to four modulo nine. Binary lifting constructs an unbounded family whose smaller mixed predecessor beats all all-odd ancestors beyond arbitrarily large multiples of their height barrier. Two axiom-free examples and four convergence arrivals are included.",
        "written_scope":["The exact finite optimization over one-even predecessor words, its reduced-residue criterion, and natural density one sixth of the improved target set.",
                         "A bounded-extra-even height envelope, and its distinction from the nonuniform family."],
        "external_dependency":"None. The Monks et al. sufficient-set paper is reviewed only to distinguish congruence reachability from a useful predecessor height bound.",
        "finite_scope_limit":"Forward/inverse census minima are over words with at most one even-input shortcut step, not global Collatz minima. Large-index modular tests are not source censuses. The least-counterexample hypotheses remain uninstantiated.",
        "not_proved":["That any hypothetical least-counterexample orbit encounters an admissible mixed target with predecessor below that least source.",
                      "A universal cap budget, exclusion of nontrivial cycles or divergence, or full Collatz."],
        "sha256":{p:digest(ROOT/p) for p in files}})
    print(json.dumps({"status":"passed","kernel_roots":len(THEOREMS),"counts":dict(counts)},indent=2))


if __name__=="__main__":
    main()
