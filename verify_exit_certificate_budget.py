"""Check the exact budget for exit-mass certificates.

The abstract integer product bound is kernel checked. Cutoff and precision
growth for real infinite masses remain written analysis. No new successful
Collatz horizon or infinite contraction is claimed by this verifier.
"""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/exit-certificate-budget'
SOURCE = 'lean/ExitCertificateBudget.lean'


def reuse_exit_verification():
    path = ROOT / 'results/survivor-exit-mass/verification.json'
    record = json.loads(path.read_text())
    for relative, expected in record['sha256'].items():
        assert hashlib.sha256((ROOT / relative).read_bytes()).hexdigest() == expected, relative
    return {'manifest': str(path.relative_to(ROOT)),
            'matched_hashes': len(record['sha256']),
            'first_entry_table_recomputed': False,
            'scope': 'unchanged independent Python verification reused'}


def build_lean():
    with tempfile.TemporaryDirectory(prefix='collatz-exit-budget-') as build:
        command = ['lean', '-o', str(Path(build) / 'ExitCertificateBudget.olean'), SOURCE]
        result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True)
    log = OUT / 'ExitCertificateBudget.log'
    log.write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    assert not any(s in result.stdout for s in ('sorryAx', 'ofReduceBool', 'warning:'))
    assert result.stdout.count('depends on axioms:') == 7
    print('Fresh Lean build passed: seven abstract integer theorems.', flush=True)
    return {'source': SOURCE, 'command': command, 'returncode': result.returncode,
            'log': str(log.relative_to(ROOT)), 'native_computation_used': False}


def stored_sequence():
    report = json.loads((ROOT / 'results/survivor-exit-mass/replay.json').read_text())
    masses = report['mass_certificates']
    rows = masses['rows']
    tail = masses['whole_tail_upper_numerator']
    initial = rows[0]['mass_scaled_interval'][1]
    good, p_power, q_power = [], 1, 1
    for k, row in enumerate(rows):
        assert row['k'] == k
        u = row['mass_scaled_interval'][1]
        loss = row['relative_loss_lower_fraction'][0]
        assert row['relative_loss_lower_fraction'][1] == u
        assert loss == row['exit_mass_scaled_interval'][0]
        after = rows[k + 1]['mass_scaled_interval'][1] if k + 1 < len(rows) else tail
        # This is the exact hypothesis linking the saved arrays to the kernel lemma.
        assert after + loss + row['known_exit_count'] == u
        assert tail <= after <= u
        passed = 1000 * loss >= 7 * u
        assert passed == row['certifies_ratio_at_most_993_over_1000']
        if passed:
            good.append(k)
            assert loss > 0
            assert 1000 * after <= 993 * u
            p_power *= 1000
            q_power *= 993
        assert p_power * after <= q_power * initial
        assert p_power * tail <= q_power * initial
        assert len(good) + after <= initial
    assert good == masses['certified_horizons'] == [*range(127), 128]
    assert rows[-1]['k'] == report['first_entry_table']['maximum_first_entry_time'] == 335
    assert rows[-1]['mass_scaled_interval'][1] == tail
    assert rows[-1]['known_exit_count'] == 0
    return {'source_cutoff': masses['source_cutoff'], 'scale': masses['scale'],
            'initial_upper_numerator': initial, 'tail_upper_numerator': tail,
            'checked_recurrences': len(rows), 'constant_tail_extension_checked': True,
            'successful_horizons': good, 'success_count': len(good),
            'actual_mass_contractions_beyond_previous_record': 0}


def maximum_power_index(predicate):
    """Find a decreasing predicate's last true integer; check both endpoints."""
    assert predicate(0)
    lo, hi = 0, 1
    while predicate(hi):
        lo, hi = hi, 2 * hi
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if predicate(mid):
            lo = mid
        else:
            hi = mid
    assert predicate(lo) and not predicate(hi)
    return lo, hi


def exact_thresholds(sequence):
    tail, initial = sequence['tail_upper_numerator'], sequence['initial_upper_numerator']
    limit, scale = sequence['source_cutoff'], sequence['scale']
    fixed = maximum_power_index(lambda g: tail * 1000 ** g <= initial * 993 ** g)
    cutoff = maximum_power_index(lambda g: 64 * 1000 ** (2 * g) <= limit * 993 ** (2 * g))
    precision = maximum_power_index(lambda j: 4 * 1000 ** j < scale * 993 ** j)
    assert fixed == cutoff == (736, 737)
    assert precision == (9275, 9276)
    print('Exact bounds: cutoff allows at most 736; fixed scale allows at most 9276.', flush=True)
    return {'fixed_cutoff_integer_budget': {'last_allowed_G': fixed[0],
                                           'first_excluded_G': fixed[1]},
            'arbitrary_schedule_with_cutoffs_at_most_2000000': {
                'last_allowed_G': cutoff[0], 'first_excluded_G': cutoff[1]},
            'arbitrary_cutoffs_with_scales_at_most_2_pow_96': {
                'last_allowed_G': precision[0] + 1, 'first_excluded_G': precision[1] + 1},
            'thresholds_are_necessary_only': True,
            'floating_point_used_for_decisions': False}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    reused = reuse_exit_verification()
    lean = build_lean()
    sequence = stored_sequence()
    thresholds = exact_thresholds(sequence)
    replay = {'all_checks_passed': True, 'stored_sequence': sequence,
              'exact_thresholds': thresholds, 'collatz_status': 'unresolved'}
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    files = [SOURCE, 'docs/EXIT-CERTIFICATE-BUDGET.md', 'verify_exit_certificate_budget.py',
             'results/exit-certificate-budget/ExitCertificateBudget.log',
             'results/exit-certificate-budget/replay.json',
             'results/survivor-exit-mass/verification.json',
             'results/survivor-exit-mass/replay.json']
    manifest = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved', 'lean_build': lean,
        'reused_verification': reused,
        'kernel_scope': ['integer exit test implies envelope contraction',
                         'product bound counts arbitrarily spaced successful horizons',
                         'positive fixed tail bounds the integer success count'],
        'written_scope': ['monotonicity of the exact real test in its source cutoff',
                          'exponential lower cutoff bound for arbitrary schedules',
                          'variable-loss product and logarithmic budget',
                          'fixed arithmetic scale permits only finitely many successes',
                          'polynomial cutoffs limit the density of successful horizons',
                          'conditional failure of polynomial cutoffs under actual exponential decay'],
        'python_scope': ['all saved envelope decrement identities and successful tests',
                         'all stored prefixes satisfy the kernel product inequality',
                         'exact cutoff and precision threshold comparisons'],
        'not_proved': ['another successful contraction horizon',
                       'infinitely many successful contraction horizons',
                       'that larger cutoffs or scales suffice for infinitely many successes',
                       'vanishing survivor mass', 'the full Collatz conjecture'],
        'external_proof_inputs': [],
        'sha256': {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in files}}
    (OUT / 'verification.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('All budget checks passed. No infinite extension has been established.', flush=True)


if __name__ == '__main__':
    main()
