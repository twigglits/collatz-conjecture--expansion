"""Independently rebuild the pinned external predecessor-density proof.

Usage: python3 verify_predecessor_density_source.py /tmp/.../assembled
The assembled directory must come from the authenticated public supplement
and baseline, and its pinned Mathlib cache must already be available.

All project modules are compiled sequentially from source. Official third-party
compiled dependencies are reused. This does not prove density-one convergence
or the Collatz conjecture.
"""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
OUT = ROOT / 'results/predecessor-density-review'
EXPECTED_BASELINE = '23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f'
EXPECTED_TOOLCHAIN = 'leanprover/lean4:v4.30.0-rc2'
PUBLIC = [
    'CollatzPredecessorDensity.predecessors_positive_lower_density',
    'CollatzPredecessorDensity.nonconvergence_positive_lower_density_of_counterexample',
    'CollatzPredecessorDensity.universal_reaches_one_of_arbitrarily_dense_convergence',
]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def capture(command, cwd):
    return subprocess.check_output(command, cwd=cwd, text=True).strip()


def validate_sources(assembled, assembly):
    assert assembly['baseline']['sha256'] == EXPECTED_BASELINE
    assert (assembled / 'lean-toolchain').read_text().strip() == EXPECTED_TOOLCHAIN
    for row in assembly['files']:
        path = assembled / row['path']
        assert path.is_file() and not path.is_symlink(), row['path']
        assert path.stat().st_size == row['bytes'] and sha(path) == row['sha256'], row['path']
    return {row['module']: row for row in assembly['files'] if 'module' in row}


def order_modules(modules):
    ordered, active, seen = [], set(), set()

    def visit(module):
        if module in seen:
            return
        assert module not in active, ('import cycle', module)
        active.add(module)
        for dep in modules[module]['imports']:
            if dep in modules:
                visit(dep)
        active.remove(module)
        seen.add(module)
        ordered.append(module)

    visit('CollatzPredecessorDensity')
    assert len(ordered) == 388
    visit('Verification.ReleaseAudit')
    assert len(ordered) == len(modules) == 389
    return ordered


def main():
    assert len(sys.argv) == 2, __doc__
    assembled = Path(sys.argv[1]).resolve()
    assembly_path = assembled / 'assembly.json'
    assembly = json.loads(assembly_path.read_text())
    modules = validate_sources(assembled, assembly)
    ordered = order_modules(modules)
    OUT.mkdir(parents=True, exist_ok=True)
    logs = OUT / 'build'
    logs.mkdir(exist_ok=True)
    version = capture(['lean', '--version'], assembled)
    assert '4.30.0-rc2' in version and '3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc' in version
    lock_path = assembled / 'lake-manifest.json'
    lock_hash = sha(lock_path)
    lock = json.loads(lock_path.read_text())
    dependencies = []
    for package in lock['packages']:
        checkout = assembled / '.lake/packages' / package['name']
        revision = capture(['git', 'rev-parse', 'HEAD'], checkout)
        assert revision == package['rev'], package['name']
        dependencies.append({'name': package['name'], 'revision': revision,
                             'compiled_dependencies_reused': True})
    lean_path = capture(['lake', 'env', 'printenv', 'LEAN_PATH'], assembled)
    prefix = Path(capture(['lean', '--print-prefix'], assembled))
    compiler = prefix / 'bin/lean'
    build = assembled / '.lake/build/lib/lean'
    # No imported author-supplied project objects may stand in for this replay.
    assert not list(build.rglob('*.olean')), 'Choose a fresh assembled project for a fresh replay.'
    env = dict(os.environ, LEAN_PATH=lean_path, LEAN_NUM_THREADS='1',
               LEAN_STACK_SIZE_KB='65536')
    rows = []
    started = datetime.now(timezone.utc).isoformat()
    progress = {'status': 'running', 'started_at_utc': started, 'assembled': str(assembled),
                'assembly_sha256': sha(assembly_path), 'lean_version': version,
                'modules_total': len(ordered), 'builds': rows,
                'external_dependencies': dependencies, 'collatz_status': 'unresolved'}
    (OUT / 'progress.json').write_text(json.dumps(progress, indent=2) + '\n')
    print(f'Fresh serial replay: {len(ordered)} project modules, {version}', flush=True)
    for index, module in enumerate(ordered, 1):
        row = modules[module]
        source = assembled / row['path']
        assert sha(source) == row['sha256']
        output = build / (module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + '.log')
        command = [str(compiler), '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
                   '-Dpp.unicode.fun=true', '-o', str(output), row['path']]
        before = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=assembled, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - before
        log_text = log.read_text()
        bad = any(marker in log_text for marker in ('sorryAx', 'ofReduceBool', 'declaration uses \'sorry\''))
        entry = {'module': module, 'source_sha256': row['sha256'], 'command': command,
                 'returncode': result.returncode, 'elapsed_seconds': round(elapsed, 3),
                 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                 'olean_sha256': sha(output) if output.exists() else None}
        rows.append(entry)
        if result.returncode != 0 or bad:
            progress['status'] = 'failed'
        (OUT / 'progress.json').write_text(json.dumps(progress, indent=2) + '\n')
        print(f'[{index}/{len(ordered)}] {module}: exit {result.returncode}, {elapsed:.1f}s', flush=True)
        assert result.returncode == 0 and not bad, log_text
    validate_sources(assembled, assembly)
    assert sha(lock_path) == lock_hash
    audit = (logs / 'Verification.ReleaseAudit.log').read_text()
    axiom_lines = [line for line in audit.splitlines() if 'depends on axioms:' in line]
    assert len(axiom_lines) == 3, axiom_lines
    for name in PUBLIC:
        lines = [line for line in axiom_lines if name in line]
        assert len(lines) == 1
        actual = set(lines[0].split('[', 1)[1].split(']', 1)[0].replace(' ', '').split(','))
        assert actual == {'propext', 'Classical.choice', 'Quot.sound'}, lines
    progress['status'] = 'passed'
    progress['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
    progress['axiom_lines'] = axiom_lines
    progress['fresh_project_modules'] = 388
    progress['fresh_audit_modules'] = 1
    progress['full_third_party_source_rebuild'] = False
    progress['independent_leanchecker_used'] = False
    progress['density_one_convergence_proved'] = False
    (OUT / 'progress.json').write_text(json.dumps(progress, indent=2) + '\n')
    (OUT / 'verification.json').write_text(json.dumps(progress, indent=2) + '\n')
    print('All project sources and public roots passed; the density-one premise remains unproved.', flush=True)


if __name__ == '__main__':
    main()
