"""Authenticate the assembled external proof against both published ZIP files.

This reads archive members without extracting or executing them. It does not
compile Lean or assert the correctness of any theorem.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
ARCHIVES = {
    'baseline': ('positive-density-log-time-collatz/', 914975,
                 '23f5cac4d66e696401144658752cf180a13ce70373a122f00693e1e1fe969c1f'),
    'companion': ('collatz-predecessor-density/', 55103,
                  '55ceb4df0cca17ae728dc65b30bf5077000e1b47f2dc322454eea9f637ac75b3'),
}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('assembled', type=Path)
    parser.add_argument('baseline_zip', type=Path)
    parser.add_argument('companion_zip', type=Path)
    args = parser.parse_args()
    archive_data, identities = {}, {}
    for kind, path in [('baseline', args.baseline_zip), ('companion', args.companion_zip)]:
        prefix, size, expected = ARCHIVES[kind]
        raw = path.read_bytes()
        assert len(raw) == size and digest(raw) == expected, kind
        with zipfile.ZipFile(path) as archive:
            names = archive.namelist()
            assert len(names) == len(set(names)), 'Duplicate archive members'
            archive_data[kind] = {name[len(prefix):]: archive.read(name)
                                  for name in names if name.startswith(prefix)
                                  and not name.endswith('/')}
        identities[kind] = {'path': str(path.resolve()), 'bytes': size, 'sha256': expected}
    assembled = args.assembled.resolve()
    assembly_bytes = (assembled / 'assembly.json').read_bytes()
    assembly = json.loads(assembly_bytes)
    baseline, companion = archive_data['baseline'], archive_data['companion']
    assert assembly['baseline'] == json.loads(companion['baseline.json'])
    assert assembly['baseline_source_manifest_sha256'] == digest(baseline['source-manifest.json'])
    assert assembly['baseline_project_build_receipt_sha256'] == digest(baseline['evidence/project-build.json'])
    assert assembly['thin_manifest_sha256'] == digest(companion['source-manifest.json'])
    thin = json.loads(companion['source-manifest.json'])
    assert assembly['public_roots'] == thin['public_roots']
    assert len(assembly['files']) == len({row['path'] for row in assembly['files']}) == 404
    assert len({row['module'] for row in assembly['files'] if 'module' in row}) == 389
    rows, counts = [], Counter()
    for row in assembly['files']:
        path = row['path']
        if path.startswith('BASELINE_'):
            kind, member = 'baseline', path.removeprefix('BASELINE_')
        elif path in companion:
            kind, member = 'companion', path
        else:
            kind, member = 'baseline', path
        expected = archive_data[kind][member]
        local = assembled / path
        assert not local.is_symlink() and local.read_bytes() == expected, path
        assert row['sha256'] == digest(expected) and row['bytes'] == len(expected), path
        if 'module' in row:
            assert path == row['module'].replace('.', '/') + '.lean', path
            counts[kind + '_lean_modules'] += 1
        rows.append({'path': path, 'archive': kind, 'member': member,
                     'sha256': row['sha256'], 'bytes': row['bytes']})
    assert sum(counts.values()) == assembly['local_lean_source_files'] == 389
    assert counts == {'baseline_lean_modules': 377, 'companion_lean_modules': 12}
    record = {
        'status': 'passed_archive_and_assembled_source_identity',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(),
        'assembled': str(assembled), 'assembly_sha256': digest(assembly_bytes),
        'archives': identities, 'counts': dict(counts), 'files': rows,
        'verifier_sha256': digest(Path(__file__).read_bytes()),
        'lean_replay_performed_by_this_script': False,
        'collatz_status': 'unresolved',
    }
    output = ROOT / 'results/predecessor-density-review/archive-authentication.json'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(record, indent=2) + '\n')
    print(f'Authenticated {len(rows)} assembled files, including 389 Lean modules; no theorem replayed.')


if __name__ == '__main__':
    main()
