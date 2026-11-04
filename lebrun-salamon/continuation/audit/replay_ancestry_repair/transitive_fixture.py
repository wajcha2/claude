"""Expose stale transitive reuse with a simulated compiler, never Lean."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--driver-dir', type=Path, required=True)
p.add_argument('--workspace', type=Path, required=True)
args = p.parse_args()
workspace = args.workspace.resolve()
assert not workspace.exists(), 'Use a fresh fixture directory.'
(workspace / 'source').mkdir(parents=True)
(workspace / 'target').mkdir()
canonical = Path('/workspace/scratch/4deac2cdddbb/lebrun_takeover/continuation')
for name in ['TOOLCHAIN.lock.json', 'target/MainStatement.lean']:
    shutil.copyfile(canonical / name, workspace / name)
(workspace / 'source/A.lean').write_text('def flag : Bool := true\n')
(workspace / 'source/B.lean').write_text('import A\ndef independent : Nat := 1\n')
(workspace / 'source/C.lean').write_text('import B\nexample : flag = true := rfl\n')
fake = workspace / 'simulated_compiler.py'
fake.write_text('''from pathlib import Path
import json,sys
a=sys.argv[1:];s=Path(a[-1]);out=Path(a[a.index('-o')+1])
with (s.parent.parent/'compiler_calls.txt').open('a') as log:log.write(s.stem+'\\n')
if s.stem=='C' and 'false' in (s.parent/'A.lean').read_text():
 print(json.dumps({'severity':'error','data':'SIMULATED transitive flag changed; C must be rechecked'}))
 raise SystemExit(1)
out.write_bytes(b'SIMULATED_NOT_LEAN '+(s.read_bytes() if s.stem=='A' else s.stem.encode()))
''')
config = workspace / 'runtime.json'
config.write_text(json.dumps({'command': [sys.executable, str(fake)], 'flags': [],
    'external_olean_roots': [], 'fingerprint_files': [str(fake)],
    'compiler_kind': 'simulated_fixture_not_Lean'}))
command = [sys.executable, str(args.driver_dir.resolve() / 'replay_checkpoint.py'),
    '--root', str(workspace), '--runtime-config', str(config),
    '--build-dir', str(workspace / 'build'), '--keep-going']
first = subprocess.run(command, capture_output=True, text=True)
assert first.returncode == 0, first.stderr
first_status = json.loads((workspace / 'build/RUN_STATUS.json').read_text())
b_hash_before = hashlib.sha256((workspace / 'build/olean/B.olean').read_bytes()).hexdigest()
(workspace / 'source/A.lean').write_text('def flag : Bool := false\n')
second = subprocess.run(command, capture_output=True, text=True)
second_status = json.loads((workspace / 'build/RUN_STATUS.json').read_text())
b_hash_after = hashlib.sha256((workspace / 'build/olean/B.olean').read_bytes()).hexdigest()
assert b_hash_before == b_hash_after, 'Fixture must keep the intermediate artifact identical.'
calls = (workspace / 'compiler_calls.txt').read_text().splitlines()
report = {'compiler': 'simulated Python fixture; no Lean invoked',
    'driver_sha256': hashlib.sha256((args.driver_dir / 'replay_checkpoint.py').read_bytes()).hexdigest(),
    'intermediate_artifact_unchanged': True,
    'first_return_code': first.returncode, 'second_return_code': second.returncode,
    'second_statuses': {m:r['status'] for m,r in second_status['modules'].items()},
    'compiler_calls': calls,
    'stale_transitive_reuse_detected': second.returncode == 0 and calls.count('C') == 1,
    'correctly_rechecks_transitive_dependent': second.returncode != 0 and calls.count('C') == 2,
    'final_validation': second_status['final_validation']}
(workspace / 'REPORT.json').write_text(json.dumps(report, indent=2) + '\n')
(workspace / 'first.stdout.txt').write_text(first.stdout)
(workspace / 'second.stdout.txt').write_text(second.stdout)
print(json.dumps(report, indent=2))
