from pathlib import Path
import hashlib
import io
import json
import os
import subprocess
import tarfile

BASE = Path(__file__).resolve().parent
RECOVERY = Path('/workspace/scratch/4deac2cdddbb/lebrun_recovery')
COMMIT = '4324e894c41a831c428fd2c667824d2bb67cb302'
PREFIX = 'lebrun-salamon/continuation/'

def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()

def run(args):
    p = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode:
        raise RuntimeError(f'{args[0]} operation failed with code {p.returncode}')
    return p.stdout

repo = BASE / 'repository'
if not (repo / '.git').is_dir():
    repo.mkdir(exist_ok=True)
    run(['git', 'init', '--quiet', str(repo)])
origin = run(['git', '-C', str(RECOVERY / 'repository'), 'remote', 'get-url', 'origin']).decode().strip()
remotes = run(['git', '-C', str(repo), 'remote']).decode().splitlines()
run(['git', '-C', str(repo), 'remote', 'set-url' if 'origin' in remotes else 'add', 'origin', origin])
run(['git', '-C', str(repo), 'config', 'remote.origin.promisor', 'true'])
run(['git', '-C', str(repo), 'config', 'remote.origin.partialclonefilter', 'blob:none'])
run(['git', '-C', str(repo), 'fetch', '--quiet', '--depth=1', '--filter=blob:none', 'origin', COMMIT])
selected = ['source', 'scripts', 'target', 'TOOLCHAIN.lock.json', 'SOURCE.sha256',
            'audit/point1_checkpoint/FREEZE.json',
            'audit/ci/41763014879/point1/VALIDATED_SEEDS.json']
archive = run(['git', '-C', str(repo), 'archive', '--format=tar', COMMIT,
               *[PREFIX + p for p in selected]])
stage = BASE / 'stage'
stage.mkdir(exist_ok=True)
with tarfile.open(fileobj=io.BytesIO(archive)) as tar:
    for member in tar.getmembers():
        if not (stage / member.name).resolve().is_relative_to(stage.resolve()):
            raise ValueError('Unsafe repository archive path')
    tar.extractall(stage, filter='data')
root = stage / PREFIX
manifest = {}
for line in (root / 'SOURCE.sha256').read_text().splitlines():
    expected, path = line.split('  ', 1)
    assert sha(root / path) == expected, path
    manifest[path] = expected

artifact = BASE / 'artifact'
status = json.loads((artifact / 'kernel-evidence/RUN_STATUS.json').read_text())
config = json.loads((artifact / 'runtime-config.json').read_text())
assert status['runtime']['config'] == config
ci_prefix = '/home/runner/work/_temp/lebrun-runtime/'
mirrored = {}

def mirror(ci_path, expected=None):
    assert ci_path.startswith(ci_prefix), ci_path
    local = RECOVERY / 'runtime' / ci_path[len(ci_prefix):]
    assert local.is_file(), str(local)
    actual = sha(local)
    if expected is not None:
        assert actual == expected, ci_path
    target = Path(ci_path)
    target.parent.mkdir(parents=True, exist_ok=True)
    assert str(target.resolve()) == ci_path, 'Existing path alias would change native identity'
    if target.exists():
        assert sha(target) == actual, 'Existing runtime file mismatch'
    else:
        os.link(local.resolve(), target)
    mirrored[ci_path] = actual

for p, expected in status['runtime']['fingerprint_files'].items():
    mirror(p, expected)
external = {}
for receipt_file in (artifact / 'kernel-evidence/receipts').glob('*.json'):
    r = json.loads(receipt_file.read_text())
    for name, dep in r['key']['dependency_artifacts'].items():
        if dep['kind'] == 'external':
            assert external.get(name, dep['sha256']) == dep['sha256']
            external[name] = dep['sha256']
for name, expected in external.items():
    rel = name.replace('.', '/') + '.olean'
    candidates = [p + '/' + rel for p in config['external_olean_roots']]
    found = next((p for p in candidates if (RECOVERY / 'runtime' / p[len(ci_prefix):]).is_file()), None)
    assert found is not None, name
    mirror(found, expected)

record = {'schema': 'lebrun-cache-validation-workspace-v1', 'commit': COMMIT,
          'source_modules': len(manifest), 'source_manifest_sha256': sha(root / 'SOURCE.sha256'),
          'runtime_config_sha256': sha(artifact / 'runtime-config.json'),
          'mirrored_stock_files': mirrored, 'external_imports_verified': external,
          'native_compiler_invoked': False, 'historical_receipt_or_runtime_key_modified': False,
          'root': str(root)}
(BASE / 'WORKSPACE.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k:v for k,v in record.items() if k not in ('mirrored_stock_files','external_imports_verified')}, indent=2))
