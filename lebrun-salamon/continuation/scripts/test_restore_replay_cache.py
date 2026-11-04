#!/usr/bin/env python3
"""Small cache-integrity fixture; deliberately invokes no Lean compiler."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--workspace', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    continuation = Path(__file__).resolve().parent.parent
    driver = continuation / 'scripts/replay_checkpoint.py'
    restore = continuation / 'scripts/restore_replay_cache.py'
    workspace = args.workspace.resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    fake = workspace / 'simulated_compiler.py'
    fake.write_text("import pathlib,sys\na=sys.argv[1:]\npathlib.Path(a[a.index('-o')+1]).write_bytes(b'SIMULATED_NOT_LEAN\\n'+pathlib.Path(a[-1]).read_bytes())\n")
    results = []
    for name, expected in (
        ('unchanged', ['A', 'B']), ('legacy_unchanged', ['A', 'B']), ('ancestor_source', []), ('leaf_source', ['A']),
        ('output_corruption', []), ('runtime_change', []), ('lock_change', []),
        ('external_change', []), ('log_corruption', []), ('non_native_receipt', ['A']),
        ('unselected_default', ['A']), ('unselected_valid', ['A', 'B']),
        ('unselected_missing_cache', ['A']), ('unselected_stale_source', ['A']),
        ('unselected_altered_output', ['A']), ('unselected_stale_ancestry', ['A']),
        ('unselected_missing_final_check', ['A']), ('unselected_local_receipt', ['A']),
        ('unselected_explicit_failure', ['A']), ('unselected_bad_provenance', ['A']),
    ):
        root = workspace / name
        (root / 'source').mkdir(parents=True)
        (root / 'target').mkdir()
        (root / 'external').mkdir()
        shutil.copy2(continuation / 'target/MainStatement.lean', root / 'target/MainStatement.lean')
        shutil.copy2(continuation / 'TOOLCHAIN.lock.json', root / 'TOOLCHAIN.lock.json')
        (root / 'source/A.lean').write_text('import External\ndef a := 1\n')
        (root / 'source/B.lean').write_text('import A\ndef b := a\n')
        (root / 'external/External.olean').write_text('fixture external bytes')
        (root / 'runtime.txt').write_text('fixture runtime bytes')
        config = root / 'runtime.json'
        config.write_text(json.dumps({
            'command': [sys.executable, str(fake)], 'flags': [],
            'external_olean_roots': [str(root / 'external')],
            'fingerprint_files': [str(fake), str(root / 'runtime.txt')],
            # This label exercises the gate; the command is explicitly a fixture.
            'compiler_kind': 'stock_pinned_frontend',
        }))
        old = root / 'artifact/kernel-evidence'
        run = subprocess.run([sys.executable, str(driver), '--root', str(root),
                              '--runtime-config', str(config), '--build-dir', str(old)],
                             capture_output=True, text=True)
        assert run.returncode == 0, (name, run.stdout, run.stderr)
        if name.startswith('unselected_'):
            status_path = old / 'RUN_STATUS.json'
            prior = json.loads(status_path.read_text())
            prior['modules'].pop('B')
            prior['selected_modules'] = ['A']
            receipt_path = old / 'receipts/B.json'
            rec = json.loads(receipt_path.read_text())
            rec['cache_union_provenance'] = {
                'source_run_id': 1, 'source_artifact_name': 'SIMULATED_FIXTURE_NOT_CI'}
            binding = {
                'source_sha256': rec['key']['source_sha256'],
                'output_sha256': rec['output_sha256'],
                'source_ancestry_fingerprint': rec['source_ancestry_fingerprint'],
                'source_run_id': 1, 'source_artifact_name': 'SIMULATED_FIXTURE_NOT_CI',
            }
            cached = {
                'schema': 'lebrun-ci-cache-union-v1',
                'current_runtime_fingerprint': prior['runtime_fingerprint'],
                'all_final_hash_and_runtime_checks_passed': True,
                'native_kernel_invoked': False, 'acceptance_ledger_modified': False,
                'copied_modules': {'B': binding}, 'copied_module_count': 1,
            }
            if name == 'unselected_stale_source':
                binding['source_sha256'] = '0' * 64
            elif name == 'unselected_altered_output':
                binding['output_sha256'] = '0' * 64
            elif name == 'unselected_stale_ancestry':
                binding['source_ancestry_fingerprint'] = '0' * 64
            elif name == 'unselected_missing_final_check':
                cached['all_final_hash_and_runtime_checks_passed'] = False
            elif name == 'unselected_local_receipt':
                rec['evidence_kind'] = 'local_path_adapter_diagnostic'
            elif name == 'unselected_explicit_failure':
                prior['modules']['B'] = {'status': 'failed', 'return_code': 1}
            elif name == 'unselected_bad_provenance':
                rec['cache_union_provenance']['source_run_id'] = 999
            if name != 'unselected_missing_cache':
                (old / 'CACHE_RESTORE.json').write_text(json.dumps(cached))
            status_path.write_text(json.dumps(prior))
            receipt_path.write_text(json.dumps(rec))
        if name == 'legacy_unchanged':
            for path in (old / 'receipts').glob('*.json'):
                rec = json.loads(path.read_text())
                rec.pop('source_ancestry_fingerprint', None)
                path.write_text(json.dumps(rec))
        elif name == 'ancestor_source':
            (root / 'source/A.lean').write_text('import External\ndef a := 2\n')
        elif name == 'leaf_source':
            (root / 'source/B.lean').write_text('import A\ndef b := a + 1\n')
        elif name == 'output_corruption':
            (old / 'olean/A.olean').write_text('corrupted output')
        elif name == 'runtime_change':
            (root / 'runtime.txt').write_text('changed runtime')
        elif name == 'lock_change':
            (root / 'TOOLCHAIN.lock.json').write_text('{}\n')
        elif name == 'external_change':
            (root / 'external/External.olean').write_text('changed external artifact')
        elif name == 'log_corruption':
            receipt = json.loads((old / 'receipts/A.json').read_text())
            Path(receipt['stdout']).write_text('corrupted log')
        elif name == 'non_native_receipt':
            path = old / 'receipts/B.json'
            receipt = json.loads(path.read_text())
            receipt['evidence_kind'] = 'explicit_validated_historical_seed'
            path.write_text(json.dumps(receipt))
        new = root / 'restored'
        restore_command = [
            sys.executable, str(restore), '--root', str(root), '--runtime-config', str(config),
            '--artifact-dir', str(root / 'artifact'), '--build-dir', str(new),
            '--source-run-id', '1', '--source-artifact-name', 'SIMULATED_FIXTURE_NOT_CI',
        ]
        if name.startswith('unselected_') and name != 'unselected_default':
            restore_command.append('--include-validated-unselected-cache')
        replay = subprocess.run(restore_command, capture_output=True, text=True)
        assert replay.returncode == 0, (name, replay.stdout, replay.stderr)
        result = json.loads((new / 'CACHE_RESTORE.json').read_text())
        copied = list(result['copied_modules'])
        accepted = copied == expected
        reused = None
        if name in {'unchanged', 'legacy_unchanged', 'unselected_valid'}:
            rerun = subprocess.run([sys.executable, str(driver), '--root', str(root),
                                    '--runtime-config', str(config), '--build-dir', str(new)],
                                   capture_output=True, text=True)
            status = json.loads((new / 'RUN_STATUS.json').read_text())
            reused = {m: rec['status'] for m, rec in status['modules'].items()}
            accepted = accepted and rerun.returncode == 0 and reused == {'A': 'reused', 'B': 'reused'}
        results.append({'case': name, 'passed': accepted, 'expected_copied': expected,
                        'copied': copied, 'replayed_statuses': reused,
                        'global_rejection': result['global_rejection'],
                        'unselected_cache_rejection': result.get('unselected_cache_rejection'),
                        'unselected_cache_copied_count': result.get('unselected_cache_copied_count', 0),
                        'rejected_modules': result['rejected_modules']})
    report = {'schema': 'lebrun-cache-integrity-fixture-v1',
              'compiler_kind': 'simulated Python fixture; no Lean invoked',
              'driver_sha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
              'cache_restore_sha256': hashlib.sha256(restore.read_bytes()).hexdigest(),
              'passed': sum(r['passed'] for r in results), 'total': len(results), 'cases': results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'passed': report['passed'], 'total': report['total'],
                      'failed': [r['case'] for r in results if not r['passed']]}))
    return 0 if report['passed'] == report['total'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
