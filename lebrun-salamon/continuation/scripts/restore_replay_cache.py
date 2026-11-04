#!/usr/bin/env python3
"""Restore only native CI receipts that match the current complete ancestry.

The workflow downloads one explicitly pinned GitHub Actions artifact separately
from the fresh runtime configuration. This preflight copies eligible modules to
an empty replay build directory. The replay driver then validates all keys again
and retains its end-of-batch source/dependency/runtime invalidation checks.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import re

from replay_checkpoint import (
    digest, read_json, runtime_context, source_graph, utc, write_json,
    dependency_order, FROZEN_TARGET_SHA256,
    source_ancestry_fingerprint,
)


def validated_unselected_cache(summary, fingerprint):
    """Read an earlier completed union record; never infer success from files alone."""
    if not isinstance(summary, dict) or summary.get('schema') != 'lebrun-ci-cache-union-v1':
        return {}, 'Missing or unsupported completed union record.'
    if (summary.get('current_runtime_fingerprint') != fingerprint
            or summary.get('all_final_hash_and_runtime_checks_passed') is not True
            or summary.get('native_kernel_invoked') is not False
            or summary.get('acceptance_ledger_modified') is not False):
        return {}, 'Completed union runtime or final validation binding differs.'
    copied = summary.get('copied_modules')
    if not isinstance(copied, dict) or summary.get('copied_module_count') != len(copied):
        return {}, 'Completed union module inventory is incomplete.'
    for module, record in copied.items():
        if (not isinstance(module, str) or not isinstance(record, dict)
                or any(not isinstance(record.get(k), str)
                       or re.fullmatch(r'[0-9a-f]{64}', record[k]) is None
                       for k in ('source_sha256', 'output_sha256', 'source_ancestry_fingerprint'))
                or not isinstance(record.get('source_run_id'), int)
                or record['source_run_id'] <= 0
                or not isinstance(record.get('source_artifact_name'), str)
                or not record['source_artifact_name']):
            return {}, 'Completed union contains an invalid module binding.'
    return copied, None


def unselected_binding_errors(record, receipt):
    """Require a native receipt already bound by the completed strict union."""
    reasons = []
    if record.get('source_sha256') != receipt.get('key', {}).get('source_sha256'):
        reasons.append('Unselected cache source binding differs.')
    if record.get('output_sha256') != receipt.get('output_sha256'):
        reasons.append('Unselected cache output binding differs.')
    if record.get('source_ancestry_fingerprint') != receipt.get('source_ancestry_fingerprint'):
        reasons.append('Unselected cache recursive ancestry binding differs.')
    provenance = receipt.get('cache_union_provenance', {})
    if any(provenance.get(k) != record.get(k)
           for k in ('source_run_id', 'source_artifact_name')):
        reasons.append('Unselected cache receipt provenance differs.')
    return reasons


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--runtime-config', type=Path, required=True)
    ap.add_argument('--artifact-dir', type=Path, required=True)
    ap.add_argument('--build-dir', type=Path, required=True)
    ap.add_argument('--source-run-id', type=int, required=True)
    ap.add_argument('--source-artifact-name', required=True)
    ap.add_argument('--include-validated-unselected-cache', action='store_true',
                    help='Also revalidate native receipts bound by a completed strict cache union.')
    args = ap.parse_args()
    root = args.root.resolve()
    previous = args.artifact_dir.resolve() / 'kernel-evidence'
    build = args.build_dir.resolve()
    if build.exists() and any(build.iterdir()):
        raise SystemExit('Cache restoration requires an empty build directory.')
    config = json.loads(args.runtime_config.read_text())
    identity, fingerprint = runtime_context(root, config)
    if digest(root / 'target/MainStatement.lean') != FROZEN_TARGET_SHA256:
        raise SystemExit('Frozen target hash differs; refusing cache restoration.')
    summary = {
        'schema': 'lebrun-ci-cache-restore-v1', 'checked_utc': utc(),
        'source_run_id': args.source_run_id,
        'source_artifact_name': args.source_artifact_name,
        'current_runtime_fingerprint': fingerprint,
        'copied_modules': {}, 'rejected_modules': {}, 'global_rejection': None,
        'native_kernel_invoked': False,
    }
    prior_status = read_json(previous / 'RUN_STATUS.json')
    if not prior_status or prior_status.get('schema') != 'lebrun-native-replay-v1':
        summary['global_rejection'] = 'Missing or unsupported prior replay status.'
    elif config.get('compiler_kind') != 'stock_pinned_frontend':
        summary['global_rejection'] = 'Strict CI cache requires the stock pinned frontend.'
    else:
        previous_identity = prior_status.get('runtime')
        previous_hash = hashlib.sha256(json.dumps(previous_identity, sort_keys=True).encode()).hexdigest()
        if (previous_identity != identity or previous_hash != fingerprint
                or prior_status.get('runtime_fingerprint') != fingerprint):
            summary['global_rejection'] = 'Runtime paths, pinned bytes, flags, environment or toolchain lock differ.'
    if summary['global_rejection']:
        write_json(build / 'CACHE_RESTORE.json', summary)
        print(json.dumps(summary, indent=2))
        return 0  # The workflow can safely continue with a fresh replay.

    cached = {}
    if args.include_validated_unselected_cache:
        cached, rejection = validated_unselected_cache(
            read_json(previous / 'CACHE_RESTORE.json'), fingerprint)
        summary['unselected_cache_rejection'] = rejection
    summary['include_validated_unselected_cache'] = args.include_validated_unselected_cache
    summary['unselected_cache_copied_count'] = 0

    sources, imports, graph = source_graph(root / 'source')
    order, cycles = dependency_order(graph)
    if cycles:
        raise SystemExit('Cyclic imports: ' + ', '.join(cycles))
    external_roots = [Path(p).resolve() for p in config['external_olean_roots']]
    flags = config.get('flags', ['--json', '-j1', '-DElab.async=false',
                                 '-M7200', '-DmaxErrors=1000', '-DmaxHeartbeats=2000000'])
    good = {}
    ancestry = {}
    for module in order:
        old_summary = prior_status.get('modules', {}).get(module)
        cached_only = old_summary is None
        if cached_only:
            if module not in cached:
                continue
        elif old_summary.get('status') not in {'passed', 'reused'}:
            continue  # Never replace an explicit failed/blocked result with an older cache entry.
        receipt_path = previous / 'receipts' / (module + '.json')
        receipt = read_json(receipt_path)
        reasons = []
        if (not receipt or receipt.get('schema') != 'lebrun-module-receipt-v1'
                or receipt.get('module') != module or receipt.get('status') != 'passed'
                or receipt.get('return_code') != 0
                or receipt.get('evidence_kind') != 'native_kernel_compilation'):
            summary['rejected_modules'][module] = ['No successful native compiler receipt.']
            continue
        if cached_only:
            reasons.extend(unselected_binding_errors(cached[module], receipt))
        deps = {}
        for dep in imports[module]:
            if dep in sources:
                if dep not in good:
                    reasons.append('Unvalidated project ancestor: ' + dep)
                else:
                    deps[dep] = {'sha256': good[dep], 'kind': 'project'}
            else:
                rel = Path(*dep.split('.')).with_suffix('.olean')
                path = next((p / rel for p in external_roots if (p / rel).is_file()), None)
                if path is None:
                    reasons.append('Missing external import: ' + dep)
                else:
                    deps[dep] = {'sha256': digest(path), 'kind': 'external'}
        key = {'source_sha256': digest(sources[module]), 'imports': imports[module],
               'dependency_artifacts': deps, 'runtime_fingerprint': fingerprint, 'flags': flags}
        stamp = source_ancestry_fingerprint(module, key,
            {dep: ancestry[dep] for dep in graph[module] if dep in ancestry})
        if receipt.get('key') != key:
            reasons.append('Current source/import/dependency/runtime key differs.')
        if receipt.get('source_ancestry_fingerprint') not in {None, stamp}:
            reasons.append('Transitive source/dependency ancestry differs.')
        if not cached_only and old_summary.get('output_sha256') != receipt.get('output_sha256'):
            reasons.append('Run summary and module receipt disagree.')
        artifact = previous / 'olean' / Path(*module.split('.')).with_suffix('.olean')
        if not artifact.is_file() or digest(artifact) != receipt.get('output_sha256'):
            reasons.append('Output artifact missing or hash differs.')
        log_paths = {}
        for stream in ('stdout', 'stderr'):
            path = previous / 'logs' / Path(receipt.get(stream, '')).name
            if not path.is_file() or digest(path) != receipt.get(stream + '_sha256'):
                reasons.append('Compiler diagnostic log missing or hash differs: ' + stream)
            else:
                log_paths[stream] = path
        if reasons:
            summary['rejected_modules'][module] = reasons
            continue
        target = build / 'olean' / Path(*module.split('.')).with_suffix('.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(artifact, target)
        restored = dict(receipt)
        # The complete original native ancestry was checked recursively above.
        # This also safely upgrades old fixed-source CI receipts to the stamp.
        restored['source_ancestry_fingerprint'] = stamp
        for stream, path in log_paths.items():
            log_target = build / 'logs' / path.name
            log_target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(path, log_target)
            restored[stream] = str(log_target)
        restored['cache_restore_provenance'] = {
            'source_run_id': args.source_run_id,
            'source_artifact_name': args.source_artifact_name,
            'prior_receipt_sha256': digest(receipt_path), 'restored_utc': utc(),
        }
        write_json(build / 'receipts' / (module + '.json'), restored)
        good[module] = receipt['output_sha256']
        ancestry[module] = stamp
        summary['copied_modules'][module] = {
            'source_sha256': key['source_sha256'], 'output_sha256': good[module],
            'prior_receipt_sha256': digest(receipt_path),
        }
        if cached_only:
            summary['unselected_cache_copied_count'] += 1
    summary.update({'copied_module_count': len(good), 'finished_utc': utc()})
    write_json(build / 'CACHE_RESTORE.json', summary)
    print(json.dumps({key: value for key, value in summary.items()
                      if key not in {'copied_modules', 'rejected_modules'}}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
