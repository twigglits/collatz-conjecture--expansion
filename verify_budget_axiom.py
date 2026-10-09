"""Exact replay of a false fixed-budget axiom; the witness reaches one.

Also builds the standalone Lean counterexample in a fresh directory. No
foreign source or foreign axiom is imported. This does not disprove Collatz.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/budget-axiom-audit'


def step(n):
    return 3 * n + 1 if n % 2 else n // 2


def prefix_check(n):
    assert n >= 2 ** 71 and n % 4 == 3
    x, odd = n, 0
    rows = []
    for k in range(201):
        assert odd == (k + 1) // 2
        assert not (0 < k <= 200 and odd <= 44 and k - odd >= 71)
        rows.append([k, odd, k - odd])
        odd += x % 2
        x = step(x)
    return rows


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    witness = 2 ** 111 - 1
    prefixes = prefix_check(witness)
    family = []
    for exponent in (*range(101, 133), 201, 512, 1024):
        for q in (1, 3, 5):
            n = 2 ** exponent * q - 1
            prefix_check(n)
            family.append({'exponent': exponent, 'q': q, 'start': str(n)})

    x, steps, peak = witness, 0, witness
    fuel = 100000
    while x != 1 and steps < fuel:
        x = step(x)
        steps += 1
        peak = max(peak, x)
    assert x == 1, 'Fuel exhausted: witness convergence remains unresolved'
    assert steps == 1476 and peak.bit_length() == 177
    replay = {
        'witness': str(witness), 'witness_above_2_pow_109': witness >= 2 ** 109,
        'prefixes_k_odd_even': prefixes, 'family': family,
        'family_cases': len(family), 'witness_first_arrival_at_one': steps,
        'witness_peak_bits': peak.bit_length(), 'convergence_fuel': fuel,
        'fuel_exhausted': False,
    }
    (OUT / 'replay.json').write_text(json.dumps(replay, indent=2) + '\n')

    source = 'lean/BudgetAxiomAudit.lean'
    with tempfile.TemporaryDirectory(prefix='collatz-budget-axiom-') as build:
        command = ['lean', '-o', str(Path(build) / 'BudgetAxiomAudit.olean'), source]
        result = subprocess.run(command, cwd=ROOT, env=dict(os.environ, LEAN_PATH=build),
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = OUT / 'BudgetAxiomAudit.log'
    log.write_text(result.stdout)
    assert result.returncode == 0, result.stdout
    assert 'sorryAx' not in result.stdout and 'ofReduceBool' not in result.stdout

    sources = [source, 'verify_budget_axiom.py', 'docs/BUDGET-AXIOM-AUDIT.md',
               'results/budget-axiom-audit/replay.json',
               'results/budget-axiom-audit/BudgetAxiomAudit.log']
    record = {
        'verified_at_utc': datetime.now(timezone.utc).isoformat(),
        'conjecture_status': 'unresolved',
        'kernel_scope': ['witness hypotheses', 'all 201 ordinary prefix counts',
                         'negation of the stated universal budget', 'arrival at one after 1476 steps'],
        'python_scope': ['105 finite family instances', 'first arrival at one and peak for the witness'],
        'not_proved': ['Collatz for every positive integer', 'foreign repository compilation',
                       'full convergence for all 105 family instances'],
        'source_audited': 'https://github.com/AIDoctrine/CollatzLayerA/blob/main/CollatzLayerA_v8_1_FINAL.lean',
        'foreign_axiom_imported': False,
        'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
        'command': command, 'returncode': result.returncode,
        'sha256': {f: hashlib.sha256((ROOT / f).read_bytes()).hexdigest() for f in sources},
    }
    (OUT / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
    print(result.stdout, end='')
    print(f'Exact replay passed: {len(family)} family instances; witness reaches 1 in {steps} steps.')
    print('The fixed-budget axiom is false. Collatz remains unresolved.')


if __name__ == '__main__':
    main()
