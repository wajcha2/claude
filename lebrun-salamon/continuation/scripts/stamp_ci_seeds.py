"""Derive new ancestry-stamped seeds from an already downloaded exact CI graph.

No native receipt, output, log, historical seed, or source file is overwritten.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

p = argparse.ArgumentParser()
p.add_argument('--base', type=Path, required=True)
p.add_argument('--driver-dir', type=Path, required=True)
p.add_argument('--live-root', type=Path, required=True)
args = p.parse_args()
sys.path.insert(0, str(args.driver_dir.resolve()))
from replay_checkpoint import (source_graph, dependency_order, digest,
                               source_ancestry_fingerprint, utc)

base = args.base.resolve()
original = base / 'head_snapshot'
build = base / 'extracted/kernel-evidence'
run = json.loads((base / 'RUN_METADATA.json').read_text())
status = json.loads((build / 'RUN_STATUS.json').read_text())
head = json.loads((base / 'HEAD_SOURCE_TREE.json').read_text())
tree_id = head['sha'] if isinstance(head['tree'], list) else head['tree']
entries = head['tree'] if isinstance(head['tree'], list) else head['entries']
assert tree_id == run['head_commit']['tree_id']
assert run['head_commit']['id'] == run['head_sha']
assert not status['final_validation']['invalidated_modules']
assert not status['final_validation']['changed_runtime_files']
git = {x['path']:x['sha'] for x in entries if x['type'] == 'blob'}
sources, imports, graph = source_graph(original / 'source')
order, cycles = dependency_order(graph)
assert not cycles
for path in [*sources.values(), original / 'target/MainStatement.lean', original / 'TOOLCHAIN.lock.json']:
    data = path.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    assert git['lebrun-salamon/continuation/' + path.relative_to(original).as_posix()] == blob

seeds = {}
for module in order:
    state = status['modules'].get(module, {})
    if state.get('status') not in {'passed', 'reused'}:
        continue
    receipt_path = build / 'receipts' / (module + '.json')
    rec = json.loads(receipt_path.read_text())
    key = rec['key']
    assert rec['status'] == 'passed' and rec['return_code'] == 0
    assert rec['evidence_kind'] == 'native_kernel_compilation'
    assert key['source_sha256'] == digest(sources[module]) and key['imports'] == imports[module]
    assert key['runtime_fingerprint'] == status['runtime_fingerprint']
    for dep in graph[module]:
        assert dep in seeds
        assert key['dependency_artifacts'][dep] == {'kind':'project', 'sha256':seeds[dep]['output_sha256']}
    for stream in ('stdout', 'stderr'):
        assert digest(build / 'logs' / Path(rec[stream]).name) == rec[stream + '_sha256']
    artifact = build / 'olean' / Path(*module.split('.')).with_suffix('.olean')
    assert digest(artifact) == rec['output_sha256'] == state['output_sha256']
    stamp = source_ancestry_fingerprint(module, key,
        {dep:seeds[dep]['source_ancestry_fingerprint'] for dep in graph[module]})
    assert rec.get('source_ancestry_fingerprint') in {None, stamp}
    seeds[module] = {'source_sha256':key['source_sha256'], 'imports':key['imports'],
        'dependency_artifacts':key['dependency_artifacts'],
        'toolchain_lock_sha256':status['runtime']['toolchain_lock_sha256'],
        'artifact_path':str(artifact), 'output_sha256':rec['output_sha256'],
        'source_ancestry_fingerprint':stamp,
        'provenance': {'kind':'ancestry_stamped_exact_github_ci', 'run_id':run['id'],
            'head_sha':run['head_sha'], 'original_receipt_sha256':digest(receipt_path),
            'historical_native_receipt_unchanged':True,
            'source_tree_and_full_ancestry_revalidated':True}}
assert len(seeds) == status['final_validation']['checked_module_count']
header = {'schema':'lebrun-explicit-validated-seeds-v2', 'validated_utc':utc(),
    'source_commit':run['head_sha'], 'module_count':len(seeds),
    'validation':'Exact Git source blobs, native receipt/log/output hashes, original complete project ancestry, and final input validation rechecked. Ancestry stamps are derived metadata; no new kernel pass or source eligibility is claimed.',
    'modules':seeds}
(base / 'FROZEN_HEAD_DIAGNOSTIC_SEEDS_V2.json').write_text(json.dumps(header, indent=2) + '\n')

live_sources, live_imports, live_graph = source_graph(args.live_root.resolve() / 'source')
live_order, cycles = dependency_order(live_graph)
assert not cycles
current = {}
for module in live_order:
    entry = seeds.get(module)
    if (entry and digest(live_sources[module]) == entry['source_sha256']
            and live_imports[module] == entry['imports']
            and all(dep in current for dep in live_graph[module])):
        current[module] = entry
(base / 'CURRENT_LIVE_SEEDS_V2.json').write_text(json.dumps({**header,
    'module_count':len(current), 'modules':current,
    'validation':header['validation'] + ' Additionally filtered for the entire current live source ancestry.'}, indent=2) + '\n')
print(json.dumps({'run':run['id'], 'frozen_modules':len(seeds), 'current_modules':len(current),
                  'historical_receipts_modified':False}))
