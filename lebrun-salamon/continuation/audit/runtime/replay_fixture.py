#!/usr/bin/env python3
"""Exercise replay bookkeeping without invoking Lean or making proof evidence."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

CONTINUATION = Path(__file__).resolve().parents[2]
DRIVER = CONTINUATION / 'scripts/replay_checkpoint.py'

FAKE_COMPILER = r'''import hashlib, json, os, pathlib, sys
args=sys.argv[1:]
output=pathlib.Path(args[args.index('-o')+1])
source=pathlib.Path(args[-1])
state=json.loads(pathlib.Path(os.environ['FIXTURE_STATE']).read_text())
mode=state.get('mode')
if source.stem=='A' and mode=='exit_zero_without_output': sys.exit(0)
if source.stem=='B' and mode=='mutate_ancestor':
    ancestor=source.parent/'A.lean'
    ancestor.write_text(ancestor.read_text()+'\n-- edited while descendant compiled\n')
if source.stem=='B' and mode=='mutate_external':
    external=pathlib.Path(os.environ['FIXTURE_EXTERNAL'])/'External.olean'
    external.write_text('external-edited-during-compile')
if source.stem=='B' and mode=='mutate_own_source':
    source.write_text(source.read_text()+'\n-- edited while self compiled\n')
parts=[source.read_bytes()]
for line in source.read_text().splitlines():
    if line.startswith('import '):
        for name in line[len('import '):].split():
            for root in os.environ['LEAN_PATH'].split(os.pathsep):
                artifact=pathlib.Path(root).joinpath(*name.split('.')).with_suffix('.olean')
                if artifact.exists():
                    parts.append(artifact.read_bytes());break
output.write_bytes(b'SIMULATED_COMPILER_NOT_LEAN\n'+hashlib.sha256(b'\0'.join(parts)).hexdigest().encode())
if source.stem=='A' and mode=='fail_with_output':sys.exit(1)
'''


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workspace', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    workspace = args.workspace.resolve()
    workspace.mkdir(parents=True, exist_ok=True)
    fake = workspace / 'simulated_compiler.py'
    fake.write_text(FAKE_COMPILER)
    cases = []

    def prepare(name, mode='normal', external=False):
        root = workspace / name
        src = root / 'source'
        src.mkdir(parents=True)
        (root / 'target').mkdir()
        shutil.copy2(CONTINUATION / 'TOOLCHAIN.lock.json', root / 'TOOLCHAIN.lock.json')
        shutil.copy2(CONTINUATION / 'target/MainStatement.lean', root / 'target/MainStatement.lean')
        (src / 'A.lean').write_text(('import External\n' if external else '') + 'def a := 1\n')
        (src / 'B.lean').write_text('import A\ndef b := a\n')
        ext = root / 'external'
        ext.mkdir()
        (ext / 'External.olean').write_text('fixture-external-v1')
        state = root / 'state.json'
        state.write_text(json.dumps({'mode':mode}))
        fingerprint = root / 'runtime-fingerprint.txt'
        fingerprint.write_text('runtime-v1')
        config = root / 'config.json'
        config.write_text(json.dumps({
            'command':[sys.executable, str(fake)], 'flags':[],
            'external_olean_roots':[str(ext)],
            'fingerprint_files':[str(fake),str(fingerprint)],
            'environment':{'FIXTURE_STATE':str(state),'FIXTURE_EXTERNAL':str(ext)},
        }))
        return root

    def run(root, label, expected, full_pass):
        process = subprocess.run([
            sys.executable,str(DRIVER),'--root',str(root),
            '--runtime-config',str(root / 'config.json'),
            '--build-dir',str(root / 'build'),'--module','B','--keep-going',
        ],capture_output=True,text=True)
        status_path = root / 'build/RUN_STATUS.json'
        status = json.loads(status_path.read_text()) if status_path.exists() else {}
        observed = {m:r.get('status') for m,r in status.get('modules',{}).items()}
        passed = observed == expected and status.get('full_selected_graph_passed') == full_pass
        cases.append({'case':label,'passed':passed,'expected':expected,'observed':observed,
                      'expected_full_graph':full_pass,'observed_full_graph':status.get('full_selected_graph_passed'),
                      'return_code':process.returncode,'stdout':process.stdout,'stderr':process.stderr})

    ordinary = prepare('ordinary',external=True)
    run(ordinary,'initial builds',{'A':'passed','B':'passed'},True)
    run(ordinary,'unchanged receipts reuse',{'A':'reused','B':'reused'},True)
    (ordinary / 'source/A.lean').write_text('import External\ndef a := 2\n')
    run(ordinary,'ancestor source changes invalidate descendants',{'A':'passed','B':'passed'},True)
    (ordinary / 'build/olean/A.olean').write_text('corrupted')
    run(ordinary,'corrupt artifact rebuilt; identical recovered descendant reusable',{'A':'passed','B':'reused'},True)
    (ordinary / 'source/B.lean').write_text('import A\ndef b := a + 1\n')
    run(ordinary,'leaf edit keeps ancestor cache',{'A':'reused','B':'passed'},True)
    (ordinary / 'runtime-fingerprint.txt').write_text('runtime-v2')
    run(ordinary,'runtime fingerprint change invalidates all',{'A':'passed','B':'passed'},True)
    (ordinary / 'external/External.olean').write_text('fixture-external-v2')
    run(ordinary,'external import change invalidates dependent closure',{'A':'passed','B':'passed'},True)
    run(prepare('missing_output','exit_zero_without_output'),'exit zero without output rejected',{'A':'failed','B':'blocked'},False)
    run(prepare('failed_output','fail_with_output'),'nonzero with output rejected',{'A':'failed','B':'blocked'},False)
    run(prepare('self_mutation','mutate_own_source'),'source edited during own compilation rejected',{'A':'passed','B':'failed'},False)
    run(prepare('ancestor_mutation','mutate_ancestor'),'ancestor edit during descendant compile invalidates ancestry',{'A':'invalidated','B':'invalidated'},False)
    run(prepare('external_mutation','mutate_external',external=True),'external edit during later compile invalidates ancestry',{'A':'invalidated','B':'invalidated'},False)
    result={'schema':'replay-bookkeeping-fixture-v1','compiler_kind':'simulated; no Lean invoked',
            'driver_sha256':hashlib.sha256(DRIVER.read_bytes()).hexdigest(),
            'cases':cases,'passed':sum(c['passed'] for c in cases),'total':len(cases)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'passed':result['passed'],'total':result['total'],
                      'failed':[c['case'] for c in cases if not c['passed']],
                      'result':str(args.output)},indent=2))
    return 0 if result['passed']==result['total'] else 1


if __name__ == '__main__':
    sys.exit(main())
