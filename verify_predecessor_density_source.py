"""Independently rebuild the pinned external predecessor-density proof.

Usage: python3 verify_predecessor_density_source.py /tmp/.../assembled
       python3 verify_predecessor_density_source.py /tmp/.../assembled --resume
The assembled directory must come from the authenticated public supplement
and baseline, and its pinned Mathlib cache must already be available.

All project modules are compiled sequentially from source. Official third-party
compiled dependencies are reused. This does not prove density-one convergence
or the Collatz conjecture.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
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


def write_json(path, value):
    temporary = path.with_suffix(path.suffix + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def bad_log(text):
    return any(marker in text for marker in
               ('sorryAx', 'ofReduceBool', "declaration uses 'sorry'"))


def public_axiom_lines(audit):
    # Lean's pretty printer can wrap the list after any axiom name.
    blocks = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit)
    assert len(blocks) == len(PUBLIC), blocks
    lines = []
    for name in PUBLIC:
        matches = [body for declaration, body in blocks if declaration == name]
        assert len(matches) == 1, (name, matches)
        actual = {axiom.strip() for axiom in matches[0].split(',')}
        assert actual == {'propext', 'Classical.choice', 'Quot.sound'}, (name, actual)
        lines.append(f"'{name}' depends on axioms: [" + ', '.join(sorted(actual)) + ']')
    return lines


def build_command(compiler, output, source_path):
    return [str(compiler), '-DautoImplicit=false', '-DrelaxedAutoImplicit=false',
            '-Dpp.unicode.fun=true', '-o', str(output), source_path]


def validate_resume(progress, assembled, assembly_path, version, dependencies,
                    ordered, modules, build, compiler, logs):
    assert progress['status'] == 'running', 'Resume requires an interrupted running replay.'
    assert progress['assembled'] == str(assembled)
    assert progress['assembly_sha256'] == sha(assembly_path)
    assert progress['lean_version'] == version
    assert progress['external_dependencies'] == dependencies
    assert progress['modules_total'] == len(ordered)
    rows = progress['builds']
    assert [row['module'] for row in rows] == ordered[:len(rows)]
    expected_objects = set()
    for row in rows:
        module = row['module']
        source = modules[module]
        output = build / (module.replace('.', '/') + '.olean')
        log = logs / (module + '.log')
        assert row['returncode'] == 0 and not bad_log(log.read_text()), module
        assert row['source_sha256'] == source['sha256'], module
        assert row['command'] == build_command(compiler, output, source['path']), module
        assert row['log'] == str(log.relative_to(ROOT)), module
        assert not log.is_symlink() and sha(log) == row['log_sha256'], module
        assert not output.is_symlink() and sha(output) == row['olean_sha256'], module
        expected_objects.add(output)
    assert set(build.rglob('*.olean')) == expected_objects, 'Unrecorded project objects present.'
    return rows


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
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('assembled', type=Path)
    parser.add_argument('--resume', action='store_true',
                        help='validate and reuse the recorded successful source-build prefix')
    args = parser.parse_args()
    assembled = args.assembled.resolve()
    assembly_path = assembled / 'assembly.json'
    assembly = json.loads(assembly_path.read_text())
    modules = validate_sources(assembled, assembly)
    ordered = order_modules(modules)
    OUT.mkdir(parents=True, exist_ok=True)
    # The operating system releases this lock even if the verifier is interrupted.
    replay_lock = (assembled / '.source-replay.lock').open('a')
    fcntl.flock(replay_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
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
    env = dict(os.environ, LEAN_PATH=lean_path, LEAN_NUM_THREADS='1',
               LEAN_STACK_SIZE_KB='65536')
    started = datetime.now(timezone.utc).isoformat()
    progress_path = OUT / 'progress.json'
    if args.resume:
        previous_progress_hash = sha(progress_path)
        progress = json.loads(progress_path.read_text())
        rows = validate_resume(progress, assembled, assembly_path, version, dependencies,
                               ordered, modules, build, compiler, logs)
        if 'lake_manifest_sha256' in progress:
            assert progress['lake_manifest_sha256'] == lock_hash
        progress.setdefault('resume_sessions', []).append({
            'started_at_utc': started, 'validated_prior_modules': len(rows),
            'previous_progress_sha256': previous_progress_hash,
            'verifier_sha256': sha(Path(__file__))})
    else:
        # No imported author-supplied project objects may stand in for this replay.
        assert not list(build.rglob('*.olean')), 'Choose a fresh assembled project or use --resume.'
        rows = []
        progress = {'status': 'running', 'started_at_utc': started, 'assembled': str(assembled),
                    'assembly_sha256': sha(assembly_path), 'lean_version': version,
                    'modules_total': len(ordered), 'builds': rows,
                    'external_dependencies': dependencies, 'collatz_status': 'unresolved'}
    previous_count = len(rows)
    progress['lake_manifest_sha256'] = lock_hash
    progress['runner_pid'] = os.getpid()
    progress['verifier_sha256'] = sha(Path(__file__))
    write_json(progress_path, progress)
    print(f'Serial replay: {previous_count} validated prior modules, '
          f'{len(ordered) - previous_count} remaining, {version}', flush=True)
    for index, module in enumerate(ordered[previous_count:], previous_count + 1):
        row = modules[module]
        source = assembled / row['path']
        assert sha(source) == row['sha256']
        output = build / (module.replace('.', '/') + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        log = logs / (module + '.log')
        command = build_command(compiler, output, row['path'])
        progress['current_module'] = module
        write_json(progress_path, progress)
        before = time.monotonic()
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=assembled, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        elapsed = time.monotonic() - before
        log_text = log.read_text()
        bad = bad_log(log_text)
        entry = {'module': module, 'source_sha256': row['sha256'], 'command': command,
                 'returncode': result.returncode, 'elapsed_seconds': round(elapsed, 3),
                 'log': str(log.relative_to(ROOT)), 'log_sha256': sha(log),
                 'olean_sha256': sha(output) if output.exists() else None}
        rows.append(entry)
        if result.returncode != 0 or bad:
            progress['status'] = 'failed'
        write_json(progress_path, progress)
        print(f'[{index}/{len(ordered)}] {module}: exit {result.returncode}, {elapsed:.1f}s', flush=True)
        assert result.returncode == 0 and not bad, log_text
    validate_sources(assembled, assembly)
    assert sha(lock_path) == lock_hash
    audit = (logs / 'Verification.ReleaseAudit.log').read_text()
    axiom_lines = public_axiom_lines(audit)
    progress['status'] = 'passed'
    progress['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
    progress['axiom_lines'] = axiom_lines
    progress['fresh_project_modules'] = 388
    progress['fresh_audit_modules'] = 1
    progress['final_session_compiled_modules'] = len(rows) - previous_count
    progress['source_replay_includes_verified_prior_sessions'] = bool(previous_count)
    progress['full_third_party_source_rebuild'] = False
    progress['independent_leanchecker_used'] = False
    progress['density_one_convergence_proved'] = False
    progress.pop('current_module', None)
    progress.pop('runner_pid', None)
    write_json(progress_path, progress)
    write_json(OUT / 'verification.json', progress)
    print('All project sources and public roots passed; the density-one premise remains unproved.', flush=True)


if __name__ == '__main__':
    main()
