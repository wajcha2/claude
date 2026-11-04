"""Exercise ancestry-stamped explicit seeds without invoking Lean."""
from pathlib import Path
import argparse
import json
import subprocess
import sys

p = argparse.ArgumentParser()
p.add_argument('--fixture', type=Path, required=True)
p.add_argument('--driver-dir', type=Path, required=True)
args = p.parse_args()
root = args.fixture.resolve()
driver = args.driver_dir.resolve() / 'replay_checkpoint.py'
# Reset and make a completely fresh, correct original seed graph.
(root / 'source/A.lean').write_text('def flag : Bool := true\n')
base_command = [sys.executable, str(driver), '--root', str(root),
                '--runtime-config', str(root / 'runtime.json'), '--keep-going']
original = root / 'seed-origin'
run = subprocess.run(base_command + ['--build-dir', str(original)], capture_output=True, text=True)
assert run.returncode == 0, run.stderr
status = json.loads((original / 'RUN_STATUS.json').read_text())
seeds = {}
for m in ('A', 'B', 'C'):
    rec = json.loads((original / 'receipts' / (m + '.json')).read_text())
    seeds[m] = {k:rec['key'][k] for k in ('source_sha256', 'imports', 'dependency_artifacts')}
    seeds[m].update({'toolchain_lock_sha256': status['runtime']['toolchain_lock_sha256'],
        'artifact_path': str(original / 'olean' / (m + '.olean')),
        'output_sha256': rec['output_sha256'],
        'source_ancestry_fingerprint': rec['source_ancestry_fingerprint'],
        'provenance': {'kind': 'SIMULATED_FIXTURE_NOT_LEAN'}})
seed_path = root / 'SEEDS.json'
seed_path.write_text(json.dumps({'modules':seeds}))
results = []
for name, changed, stamped in [('unchanged_seed', False, True),
                               ('changed_transitive_seed', True, True),
                               ('legacy_unstamped_seed', True, False)]:
    (root / 'source/A.lean').write_text('def flag : Bool := ' + ('false' if changed else 'true') + '\n')
    data = json.loads(seed_path.read_text())
    if not stamped:
        for entry in data['modules'].values():
            entry.pop('source_ancestry_fingerprint')
    selected_seeds = root / (name + '.json')
    selected_seeds.write_text(json.dumps(data))
    build = root / name
    run = subprocess.run(base_command + ['--build-dir', str(build), '--seed-receipts', str(selected_seeds)],
                         capture_output=True, text=True)
    state = json.loads((build / 'RUN_STATUS.json').read_text())
    states = {m:r['status'] for m,r in state['modules'].items()}
    if changed:
        assert run.returncode != 0 and states['C'] == 'failed', (name, states)
    else:
        assert run.returncode == 0 and set(states.values()) == {'historical_reuse'}, states
    results.append({'case':name, 'return_code':run.returncode, 'statuses':states, 'passed':True})
(root / 'SEED_REPORT.json').write_text(json.dumps({'compiler':'simulated; no Lean invoked',
    'cases':results, 'passed':3, 'total':3}, indent=2) + '\n')
print(json.dumps(results, indent=2))
