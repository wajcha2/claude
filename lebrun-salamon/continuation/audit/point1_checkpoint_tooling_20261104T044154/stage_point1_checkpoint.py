"""Copy a stable, announced checkpoint into a new immutable staging directory."""
from pathlib import Path
import argparse
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess

p = argparse.ArgumentParser()
p.add_argument('--live', required=True, type=Path)
p.add_argument('--staged', required=True, type=Path)
p.add_argument('--announced-utc', required=True)
p.add_argument('--parent', required=True)
p.add_argument('--base-tree', required=True)
p.add_argument('--cache-run', type=int, default=41714131927)
a = p.parse_args()
live = a.live.resolve()
staged = a.staged.resolve()
assert not staged.exists(), 'Use a new staging directory; never replace another snapshot.'
assert live != staged

def included(f):
    return (f.is_file() and '__pycache__' not in f.parts
            and f.suffix not in {'.pyc','.olean','.ilean','.o','.so','.zip','.png','.pdf'}
            and not f.name.startswith('EGAI_chapter0_printed_')
            and (f.suffix != '.c' or f.relative_to(live).as_posix() == 'audit/runtime/explicit_exec_path.c'))

def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

def manifest():
    return {f.relative_to(live).as_posix():sha(f) for f in sorted(live.rglob('*')) if included(f)}

ledger = json.loads((live/'audit/MILESTONE_PROGRESS.json').read_text())
metric = ledger['metric']
accepted_units = int(metric['accepted_units'])
denominator = int(metric['denominator'])
assert 0 <= accepted_units <= denominator
before = manifest()
for rel in before:
    target = staged/rel
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(live/rel,target)
after = manifest()
assert before == after, 'Live inputs changed while copying. Keep this failed snapshot for inspection; retry in a new directory.'
assert all(sha(staged/rel) == h for rel,h in before.items()), 'Copy hash mismatch.'
source = {rel:h for rel,h in before.items() if rel.startswith('source/') and rel.endswith('.lean')}
stamp = datetime.now(timezone.utc).isoformat()
assert before['target/MainStatement.lean'] == '9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296'
assert before['TOOLCHAIN.lock.json'] == '7f60e90fabda82f0e4e3c3bf4537d24f1298514f116bc18215f162e203f11c19'
audit = staged/'audit/point1_checkpoint'
audit.mkdir(parents=True, exist_ok=True)
(audit/'FREEZE.json').write_text(json.dumps({
    'schema':'lebrun-immutable-source-freeze-v1',
    'announced_utc':a.announced_utc, 'frozen_utc':stamp,
    'parent_commit':a.parent, 'base_tree':a.base_tree,
    'repository':'wajcha2/claude','branch':'codex/lebrun-takeover-audit-20261103',
    'source_modules':len(source),'source_sha256':source,
    'target_sha256':before['target/MainStatement.lean'],
    'lock_sha256':before['TOOLCHAIN.lock.json'],
    'input_tree_stable_during_copy':True,
    'all_copied_bytes_verified':True,
    'status':'Unverified integrated candidate; native diagnostics are not whole-graph acceptance.',
    'accepted_units':accepted_units,'acceptance_denominator':denominator,
    'acceptance_metric_source':'audit/MILESTONE_PROGRESS.json',
    'acceptance_metric_preserved_without_promotion':True,
    'strict_ci_cache_source_run':a.cache_run,
    'scope':'Source and canonical audit evidence frozen. Generated manifests/status are refreshed after copying. Full publication scan/page copies are reference inputs, not repository contents.'
},ensure_ascii=False,indent=2)+'\n')
(staged/'SOURCE.sha256').write_text(''.join(f'{h}  {rel}\n' for rel,h in sorted(source.items())))
subprocess.run(['python3',str(staged/'scripts/check_checkpoint.py'),'--root',str(staged),
    '--output-dir',str(staged/'audit/current'),'--verify-manifest'],check=True,stdout=subprocess.DEVNULL)
print(json.dumps({'staged':str(staged),'frozen_utc':stamp,'source_modules':len(source),
                  'source_manifest_sha256':sha(staged/'SOURCE.sha256'),'copied_files':len(before)}))
