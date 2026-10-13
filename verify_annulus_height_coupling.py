"""Exact actual-annulus height arithmetic and count-return transport.

Floating logarithms are display-only. Infinite probability and logarithm
arguments have the written scope recorded separately from kernel checks.
"""
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/annulus-height-coupling'
SOURCE = 'lean/AnnulusHeightCoupling.lean'
SOURCES = ['CollatzAffine.lean', 'lean/CoalescenceTail.lean',
           'lean/EscapeWeightRefinements.lean', 'lean/CountReturnControl.lean', SOURCE]
PRIOR = 'results/count-return-control/verification.json'
THEOREMS = ['height_affine_identity', 'height_lift', 'height_annulus_lower',
            'height_gap_lift', 'height_gap_bound', 'total_constant', 'total_interleave',
            'annulus_height_gap_mass', 'weight_children', 'parity_mass_recurrence',
            'signed_even_count_mass', 'annulus_signed_count_mass']


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def ratio(x):
    return [x.numerator, x.denominator]


def step(n):
    return (3*n+1)//2 if n & 1 else n//2


def direct(t, n):
    a = 0
    for _ in range(t):
        a += n & 1
        n = step(n)
    return n, a


def f(t, n):
    x, a = direct(t, n)
    assert x > 0
    return Fraction(3**a, (1 << t)*x)


def annulus_checks(counts):
    rows = []
    for t in range(1, 20):
        N, three = 1 << t, 3**t
        gap_sum = correction_sum = signed_count = absolute_count = balanced = 0
        log_sum = abs_log_sum = log_error_sum = 0.0
        for r in range(N//2):
            m = N+2*r
            X, a = direct(t, m)
            Y, b = direct(t, m+1)
            hx, hy = 3**(t-a)*X, 3**(t-b)*Y
            qx = 3**(t-a)*(N*X-3**a*m)
            qy = 3**(t-b)*(N*Y-3**b*(m+1))
            assert qx >= 0 and qy >= 0 and hx >= three and hy >= three
            assert N*hx == three*m+qx and N*hy == three*(m+1)+qy
            assert N*abs(hy-hx) <= three+qx+qy
            gap_sum += abs(hy-hx)
            correction_sum += qx+qy
            signed_count += b-a
            absolute_count += abs(b-a)
            balanced += X == Y and a == b
            counts['actual_even_annulus_pairs'] += 1
            # Diagnostic output only; these floats make no verification decisions.
            logarithm = math.log(Y)-math.log(X)
            log_sum += logarithm
            abs_log_sum += abs(logarithm)
            log_error_sum += abs(logarithm-(b-a)*math.log(3))
            if r < 4:
                residue = 2*r
                x0, a0 = direct(t, residue)
                y0, b0 = direct(t, residue+1)
                for q in (0, 1, 7, (1 << 32)+1):
                    x, aa = direct(t, N*q+residue)
                    y, bb = direct(t, N*q+residue+1)
                    assert (x, aa) == (3**a0*q+x0, a0)
                    assert (y, bb) == (3**b0*q+y0, b0)
                    assert abs(3**(t-bb)*y-3**(t-aa)*x) == abs(3**(t-b0)*y0-3**(t-a0)*x0)
                    counts['height_gap_quotient_lifts'] += 1
        assert 2*correction_sum+6**t == 8**t
        assert 2*N*gap_sum <= 8**t
        assert signed_count == N//2
        mean_gap = Fraction(2*gap_sum, N*three)
        assert mean_gap <= Fraction(2, 3)**t
        rows.append({'clock': t, 'source_annulus': [N, 2*N], 'even_pair_count': N//2,
                     'normalized_height_gap_mean': ratio(mean_gap),
                     'normalized_height_gap_bound': ratio(Fraction(2, 3)**t),
                     'signed_count_gap_mean': ratio(Fraction(2*signed_count, N)),
                     'absolute_count_gap_mean': ratio(Fraction(2*absolute_count, N)),
                     'balanced_pairs': balanced,
                     'floating_log_diagnostics_not_certificate': {
                         'mean_log_ratio': 2*log_sum/N,
                         'mean_absolute_log_ratio': 2*abs_log_sum/N,
                         'mean_absolute_log_residual': 2*log_error_sum/N}})
        counts['exact_annulus_mass_and_count_identities'] += 1
        print('Exact actual-annulus height comparison passed:', t, flush=True)
    return rows


def first_returns(counts):
    # Condition on an initial even input; expose higher source bits fairly.
    live = [(0, 0, 2, 0, 1)]  # residue, endpoints after one step, counts
    returns = []
    for t in range(1, 14):
        nxt = []
        for r, x, y, a, b in live:
            assert a < b
            for bit in (0, 1):
                rr = r+bit*(1 << t)
                xx, yy = x+bit*3**a, y+bit*3**b
                aa, bb = a+(xx & 1), b+(yy & 1)
                xx, yy = step(xx), step(yy)
                if aa == bb:
                    assert yy <= xx
                    assert direct(t+1, rr) == (xx, aa)
                    assert direct(t+1, rr+1) == (yy, bb)
                    returns.append((t+1, rr, aa, xx, yy))
                    counts['enumerated_first_count_return_prefixes'] += 1
                else:
                    assert aa < bb
                    nxt.append((rr, xx, yy, aa, bb))
                counts['first_return_tree_edges'] += 1
        live = nxt
    nonfused = [row for row in returns if row[3] != row[4]]
    assert nonfused
    return returns, nonfused[:64]


def transport_checks(counts):
    all_returns, selected = first_returns(counts)
    rows = []
    for tau, r, a, x0, y0 in selected:
        assert r % 2 == 0 and 0 < r < 1 << tau and x0 > y0 > 0
        lam = Fraction(3**a, 1 << tau)
        for extra in (0, 2):
            K, Q = tau+extra, 1 << extra
            A, M = 1 << K, 3**a*Q
            assert M == lam*A
            for offset in (0, 3, 8):
                h, T = K+offset-tau, K+offset
                source_energy, progression_energy = Fraction(0), Fraction(0)
                for q in range(Q, 2*Q):
                    n = (1 << tau)*q+r
                    X, Y = 3**a*q+x0, 3**a*q+y0
                    assert A <= n < n+1 < 2*A
                    assert M+x0 <= X < 2*M+x0 and (X-x0) % (3**a) == 0
                    assert direct(tau, n) == (X, a) and direct(tau, n+1) == (Y, a)
                    original, induced = f(T, n)-f(T, n+1), f(h, X)-f(h, Y)
                    assert original == lam*induced
                    source_energy += A*original**2
                    progression_energy += M*induced**2
                    counts['exact_lifted_weight_factorizations'] += 1
                assert source_energy == lam*progression_energy
                assert lam/Fraction(3**a) == Fraction(1, 1 << tau)
                counts['exact_progression_energy_transports'] += 1
                if len(rows) < 12 and source_energy:
                    rows.append({'prefix_clock': tau, 'residue': r, 'common_count': a,
                                 'base_endpoints': [x0, y0], 'source_level': K,
                                 'later_offset': offset, 'progression_step': 3**a,
                                 'source_energy': ratio(source_energy),
                                 'progression_energy': ratio(progression_energy),
                                 'exact_transport_multiplier': ratio(lam),
                                 'binary_branch_mass': ratio(Fraction(1, 1 << tau))})
    return {'first_returns_through_depth': 14, 'all_return_prefix_count': len(all_returns),
            'nonfused_prefixes_used': len(selected), 'selected_nonzero_transports': rows,
            'scope': 'Progression averages retained exactly. No interval averaging estimate is asserted.'}


def build_lean():
    version = subprocess.check_output(['lean', '--version'], cwd=ROOT, text=True).strip()
    assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
    builds = []
    with tempfile.TemporaryDirectory(prefix='collatz-annulus-height-') as directory:
        build = Path(directory)
        for source in SOURCES:
            obj, log = build/(Path(source).stem+'.olean'), OUT/(Path(source).stem+'.log')
            command = ['lean', '-o', str(obj), source]
            start = time.monotonic()
            p = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT,
                               env=dict(os.environ, LEAN_PATH=str(build), LEAN_NUM_THREADS='1'))
            log.write_text(p.stdout)
            assert p.returncode == 0, p.stdout
            assert not any(x in p.stdout for x in ('error:', 'warning:', 'sorryAx', 'ofReduceBool'))
            if source == SOURCE:
                roots = re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", p.stdout, re.M)
                assert len(roots) == len(THEOREMS)
                assert {name for name, _ in roots} == {'AnnulusHeightCoupling.'+t for t in THEOREMS}
                for name, axioms in roots:
                    assert {x.strip() for x in axioms.split(',') if x.strip()} <= {
                        'propext', 'Classical.choice', 'Quot.sound'}, name
            builds.append({'source': source, 'source_sha256': digest(ROOT/source),
                           'command': command, 'returncode': p.returncode,
                           'elapsed_seconds': round(time.monotonic()-start, 3),
                           'fresh_build': True, 'native_computation_used': False,
                           'log': str(log.relative_to(ROOT)), 'log_sha256': digest(log),
                           'olean_sha256': digest(obj)})
            print('Fresh Lean build passed:', source, flush=True)
    return version, builds


def progression_bias_witness(counts):
    tau, residue, common_count, h = 10, 200, 4, 128
    for t in range(1, tau):
        assert direct(t, residue)[1] != direct(t, residue+1)[1]
    assert direct(tau, residue) == (17, common_count)
    assert direct(tau, residue+1) == (16, common_count)
    assert direct(tau, (1 << tau)+residue) == (98, common_count)
    assert direct(tau, (1 << tau)+residue+1) == (97, common_count)
    numerators = {}
    for n in range(97, 179):
        endpoint, a = direct(h, n)
        assert endpoint in (1, 2)
        numerators[n] = (2//endpoint)*3**a
        assert Fraction(numerators[n], 1 << (h+1)) == f(h, n)
        counts['progression_bias_cycle_endpoints'] += 1
    top = 81*(numerators[98]-numerators[97])**2
    bottom = sum((numerators[x]-numerators[x-1])**2 for x in range(98, 179))
    required = Fraction(top, bottom)
    assert required == Fraction(10453976883, 926254009) and required > 11
    return {'prefix_clock': tau, 'residue': residue, 'common_count': common_count,
            'continuation_clock': h, 'progression_pair': [98, 97],
            'containing_interval': [98, 179], 'progression_spacing': 81,
            'required_multiplier': ratio(required),
            'scope': 'Exact finite counterexample to C<=11 for this progression comparison, not to all finite C.'}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    prior = json.loads((ROOT/PRIOR).read_text())
    assert prior['status'] == 'passed'
    for path, expected in prior['sha256'].items():
        assert digest(ROOT/path) == expected, (PRIOR, path)
    version, builds = build_lean()
    counts = Counter()
    replay = {'annulus_checks': annulus_checks(counts),
              'return_transport': transport_checks(counts),
              'progression_bias_witness': progression_bias_witness(counts), 'counts': dict(counts)}
    (OUT/'replay.json').write_text(json.dumps(replay, indent=2)+'\n')
    files = [*SOURCES, Path(__file__).name, 'docs/ANNULUS-HEIGHT-COUPLING.md',
             'docs/COUNT-RETURN-CONTROL.md', PRIOR,
             'results/annulus-height-coupling/replay.json', *[b['log'] for b in builds]]
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(), 'status': 'passed',
        'collatz_status': 'unresolved', 'lean_version': version,
        'kernel_theorems_audited': len(THEOREMS), 'builds': builds,
        'prior_hashes_validated': {PRIOR: len(prior['sha256'])},
        'kernel_scope': [
            'Scaled endpoint affine identity, lower bound, gap periodicity, and cross-multiplied gap bound.',
            'All-depth actual-annulus normalized-height difference mass bound.',
            'Two-child odd-count identity, parity mass recurrence, and exact signed count mean one on the even annulus.',
        ],
        'written_scope': [
            'Actual-annulus mean |log(Y/X)-(b-a)*log(3)| <=(2/3)^t.',
            'Actual logarithmic height separation has bounded first moment and a uniform integrated threshold-disagreement budget.',
            'Signed logarithmic height mean tends to log(3); combined with earlier coalescence, first-mean convergence and uniform integrability fail.',
            'Every fractional logarithmic height moment of order below one tends to zero at the stated rate.',
            'Expected sum of D_j^(1/16) over all Haar count-return cycles <=(512/3)*(1+6404*C_star).',
            'Exact continuation factorization transports a source residue to a progression of spacing 3^a, retaining multiplier 3^a/2^tau.',
        ],
        'finite_scope': dict(counts),
        'floating_scope': 'Logarithm table columns are diagnostic only; they make no verification decisions.',
        'external_scope': 'No new external theorem or package. Probability consequences reuse the previous written count-return proof.',
        'not_proved': ['A uniform bound comparing the actual progression energies to interval energies.',
                       'Control at arbitrary later clocks from the source-boundary logarithmic estimate alone.',
                       'A bounded energy subsequence, absence of escape, other-cycle exclusion, or full Collatz.'],
        'sha256': {str(path): digest(ROOT/path) for path in files},
    }
    (OUT/'verification.json').write_text(json.dumps(record, indent=2)+'\n')
    print('PASS: actual-annulus height coupling; weighted progression control and Collatz remain open.', flush=True)


if __name__ == '__main__':
    main()
