#!/usr/bin/env python3
"""Validate downloaded stock CI receipts against an exact Git head snapshot.

This collector does not invoke Lean. It separates the committed CI result from
which outputs still match the live source tree and can safely seed local work.
"""
from pathlib import Path
import argparse
from collections import Counter
import hashlib
import json
import shutil
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--base', type=Path, required=True)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--local-runtime', type=Path, required=True)
    ap.add_argument('--previous-base', type=Path)
    args = ap.parse_args()
    base, root = args.base.resolve(), args.root.resolve()
    sys.path.insert(0, str(root / 'scripts'))
    from replay_checkpoint import digest, read_json, write_json, utc, source_graph, dependency_order
    original = base / 'head_snapshot'
    extracted = base / 'extracted'
    build = extracted / 'kernel-evidence'
    run = read_json(base / 'RUN_METADATA.json')
    artifacts = read_json(base / 'ARTIFACTS.json')
    artifact = next(x for x in artifacts['artifacts'] if x['name'].startswith('lebrun-takeover-kernel-'))
    assert run['status'] == 'completed', 'CI is still pending.'
    zip_path = base / 'artifact.zip'
    zip_sha = digest(zip_path)
    if artifact.get('digest'):
        assert artifact['digest'] == 'sha256:' + zip_sha, 'Artifact ZIP hash mismatch.'
    status = read_json(build / 'RUN_STATUS.json')
    assert status['schema'] == 'lebrun-native-replay-v1'
    runtime = status['runtime']
    config = runtime['config']
    assert config['compiler_kind'] == 'stock_pinned_frontend'
    assert config['mathlib_revision'] == '116662aa4c1e9106ab5c609b3214b02f6e11a65a'
    assert runtime['toolchain_lock_sha256'] == digest(original / 'TOOLCHAIN.lock.json')
    assert hashlib.sha256(json.dumps(runtime, sort_keys=True).encode()).hexdigest() == status['runtime_fingerprint']
    assert not status['final_validation']['invalidated_modules']
    assert not status['final_validation']['changed_runtime_files']
    local_runtime = args.local_runtime.resolve()
    for name, expected in runtime['fingerprint_files'].items():
        relative = name.split('/lebrun-runtime/', 1)[1]
        assert digest(local_runtime / relative) == expected, 'Pinned compiler/library mismatch: ' + relative
    sources, imports, graph = source_graph(original / 'source')
    order, cycles = dependency_order(graph)
    assert not cycles
    assert set(status['selected_modules']) <= sources.keys()
    external_roots = [local_runtime / p.split('/lebrun-runtime/', 1)[1]
                      for p in config['external_olean_roots']]
    good, errors, checked = {}, [], []
    external_hashes = {}
    counts = Counter(x['status'] for x in status['modules'].values())
    for module in order:
        item = status['modules'].get(module)
        if not item or item['status'] not in {'passed', 'reused', 'failed'}:
            continue
        receipt_path = build / 'receipts' / (module + '.json')
        rec = read_json(receipt_path)
        assert rec and rec['schema'] == 'lebrun-module-receipt-v1' and rec['module'] == module
        key = rec['key']
        assert key['source_sha256'] == digest(sources[module]), 'Source differs from exact head: ' + module
        assert key['imports'] == imports[module]
        assert key['runtime_fingerprint'] == status['runtime_fingerprint']
        assert key['flags'] == config['flags']
        deps = {}
        for dep in imports[module]:
            if dep in sources:
                assert dep in good, 'Missing accepted ancestor: ' + dep
                deps[dep] = {'sha256': good[dep]['output_sha256'], 'kind': 'project'}
            else:
                if dep not in external_hashes:
                    rel = Path(*dep.split('.')).with_suffix('.olean')
                    found = next((p / rel for p in external_roots if (p / rel).is_file()), None)
                    assert found, 'Missing external dependency: ' + dep
                    external_hashes[dep] = digest(found)
                deps[dep] = {'sha256': external_hashes[dep], 'kind': 'external'}
        assert key['dependency_artifacts'] == deps, 'Dependency key mismatch: ' + module
        module_errors = []
        for stream in ('stdout', 'stderr'):
            log = build / 'logs' / Path(rec[stream]).name
            assert digest(log) == rec[stream + '_sha256'], 'Diagnostic log mismatch: ' + module
            if stream == 'stdout':
                for line in log.read_text().splitlines():
                    try:
                        diagnostic = json.loads(line)
                    except ValueError:
                        continue
                    if diagnostic.get('severity') == 'error':
                        module_errors.append({'module': module, **diagnostic})
        errors.extend(module_errors)
        accepted = item['status'] in {'passed', 'reused'}
        if accepted:
            assert rec['status'] == 'passed' and rec['return_code'] == 0
            assert rec['evidence_kind'] == 'native_kernel_compilation'
            assert not module_errors
            artifact_path = build / 'olean' / Path(*module.split('.')).with_suffix('.olean')
            assert digest(artifact_path) == rec['output_sha256'] == item['output_sha256']
            if item['status'] == 'reused':
                provenance = rec['cache_restore_provenance']
                if args.previous_base:
                    prior = args.previous_base.resolve() / 'extracted/kernel-evidence/receipts' / (module + '.json')
                    assert digest(prior) == provenance['prior_receipt_sha256']
                    prior_rec = read_json(prior)
                    assert prior_rec['key'] == rec['key'] and prior_rec['output_sha256'] == rec['output_sha256']
            good[module] = rec
        checked.append({'module': module, 'status': item['status'], 'return_code': rec.get('return_code'),
                        'seconds': rec.get('seconds'), 'source_sha256': key['source_sha256'],
                        'output_sha256': rec.get('output_sha256'), 'evidence_kind': rec.get('evidence_kind'),
                        'cache_restore_provenance': rec.get('cache_restore_provenance')})
    assert status['final_validation']['checked_module_count'] == len(good)
    live_sources, live_imports, live_graph = source_graph(root / 'source')
    live_order, cycles = dependency_order(live_graph)
    assert not cycles
    seeds, excluded = {}, {}
    lock_sha = digest(root / 'TOOLCHAIN.lock.json')
    for module in live_order:
        if module not in good:
            continue
        rec = good[module]
        reasons = []
        if lock_sha != runtime['toolchain_lock_sha256']:
            reasons.append('Toolchain lock changed.')
        if digest(live_sources[module]) != rec['key']['source_sha256']:
            reasons.append('Source changed since CI commit.')
        if live_imports[module] != rec['key']['imports']:
            reasons.append('Imports changed since CI commit.')
        for dep in live_graph[module]:
            if dep not in seeds:
                reasons.append('Project ancestor no longer matches current source: ' + dep)
        if reasons:
            excluded[module] = reasons
            continue
        seeds[module] = {
            'source_sha256': rec['key']['source_sha256'], 'imports': rec['key']['imports'],
            'dependency_artifacts': rec['key']['dependency_artifacts'], 'toolchain_lock_sha256': lock_sha,
            'artifact_path': str(build / 'olean' / Path(*module.split('.')).with_suffix('.olean')),
            'output_sha256': rec['output_sha256'],
            'provenance': {'kind': 'stock_github_ci' if status['modules'][module]['status'] == 'passed'
                          else 'revalidated_prior_stock_github_ci', 'run_id': run['id'],
                          'head_sha': run['head_sha'], 'run_url': run['html_url'],
                          'artifact_id': artifact['id'], 'artifact_zip_sha256': zip_sha,
                          'original_receipt_sha256': digest(build / 'receipts' / (module + '.json')),
                          'cache_restore_provenance': rec.get('cache_restore_provenance'),
                          'source_and_all_project_ancestors_match_current': True,
                          'direct_external_artifacts_match_local_runtime': True},
        }
    dest = root / 'audit/ci' / str(run['id'])
    dest.mkdir(parents=True, exist_ok=True)
    for name in ('RUN_METADATA.json', 'ARTIFACTS.json', 'FINAL_JOBS.json', 'HEAD_SOURCE_TREE.json'):
        if (base / name).exists():
            shutil.copy2(base / name, dest / name)
    for name in ('RUN_STATUS.json', 'CACHE_RESTORE.json'):
        if (build / name).exists():
            shutil.copy2(build / name, dest / name)
    for folder in ('receipts', 'logs'):
        shutil.copytree(build / folder, dest / folder, dirs_exist_ok=True)
    shutil.copy2(extracted / 'runtime-config.json', dest / 'runtime-config.json')
    selected_run = {k:run[k] for k in ('id','name','head_branch','head_sha','path','event','status','conclusion',
                                      'html_url','created_at','updated_at','run_started_at','run_attempt')}
    evidence = {'schema':'lebrun-github-ci-evidence-v2', 'verified_utc':utc(), 'run':selected_run,
                'artifact_id':artifact['id'], 'artifact_zip_sha256':zip_sha, 'artifact_zip_verified':True,
                'compiler_kind':config['compiler_kind'], 'compiler_flags':config['flags'],
                'counts':dict(counts), 'accepted_count':len(good), 'selected_module_count':len(status['selected_modules']),
                'full_selected_graph_passed':status['full_selected_graph_passed'], 'milestone_met':False,
                'final_validation':status['final_validation'], 'failures':[x['module'] for x in checked if x['status']=='failed'],
                'error_count':len(errors), 'modules':checked}
    write_json(dest / 'CI_RECEIPT.json', evidence)
    write_json(dest / 'ERRORS.json', errors)
    write_json(dest / 'VALIDATED_SEEDS.json', {'schema':'lebrun-explicit-validated-seeds-v1',
               'validated_utc':utc(), 'source_commit':run['head_sha'], 'module_count':len(seeds),
               'validation':'Exact committed source and dependency ancestry verified, then filtered for unchanged live source and entire live ancestry; pinned stock compiler and direct external artifacts match local runtime.',
               'modules':seeds, 'excluded':excluded})
    write_json(dest / 'STATUS.json', {**{k:v for k,v in evidence.items() if k!='modules'},
               'schema':'lebrun-final-ci-snapshot-v2', 'phase':'completed',
               'validated_seed_count':len(seeds), 'seed_file':'VALIDATED_SEEDS.json'})
    (dest / 'SOURCE_HEAD.sha256').write_text(''.join(digest(sources[m]) + '  source/' + sources[m].relative_to(original/'source').as_posix() + '\n' for m in sorted(sources)))
    (dest / 'FILES.sha256').write_text(''.join(digest(p)+'  '+p.relative_to(dest).as_posix()+'\n'
                                           for p in sorted(dest.rglob('*')) if p.is_file() and p.name!='FILES.sha256'))
    print(json.dumps({'run':run['id'], 'counts':dict(counts), 'accepted_count':len(good),
          'current_safe_seed_count':len(seeds), 'excluded':excluded,
          'errors':[{'module':x['module'],'pos':x.get('pos'),'data':x.get('data')} for x in errors],
          'evidence_directory':str(dest)},indent=2,ensure_ascii=False))


if __name__ == '__main__':
    main()
