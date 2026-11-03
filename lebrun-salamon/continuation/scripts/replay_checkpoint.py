#!/usr/bin/env python3
"""Compile project modules in dependency order with hash-checked reuse.

The runtime configuration names an already restored, pinned compiler. This
driver never downloads a toolchain, changes source, or restores an old overlay.
Successful compilation and acceptance of admitted theorems are separate gates.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time

from check_checkpoint import dependency_order, strip_noncode, FROZEN_TARGET_SHA256


def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')
    temp.replace(path)


def read_json(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError):
        return None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    ap.add_argument('--runtime-config', type=Path, required=True)
    ap.add_argument('--build-dir', type=Path, required=True)
    ap.add_argument('--module', action='append', help='target module; include all project ancestors')
    ap.add_argument('--seed-receipts', type=Path,
                    help='explicit previously validated historical receipts; no implicit artifact reuse')
    ap.add_argument('--keep-going', action='store_true')
    ap.add_argument('--timeout', type=int, default=2400)
    ap.add_argument('--plan-only', action='store_true')
    args = ap.parse_args()
    root = args.root.resolve()
    src = root / 'source'
    build = args.build_dir.resolve()
    out = build / 'olean'
    receipts = build / 'receipts'
    logs = build / 'logs'
    config = json.loads(args.runtime_config.read_text())
    command = config['command']
    flags = config.get('flags', ['--json', '-j1', '-DElab.async=false',
                                 '-M7200', '-DmaxErrors=1000', '-DmaxHeartbeats=2000000'])
    external_roots = [Path(p).resolve() for p in config['external_olean_roots']]
    fingerprint_files = {str(Path(p).resolve()): digest(p)
                         for p in config.get('fingerprint_files', [])}
    runtime_identity = {
        'config': config,
        'fingerprint_files': fingerprint_files,
        'toolchain_lock_sha256': digest(root / 'TOOLCHAIN.lock.json'),
    }
    runtime_hash = hashlib.sha256(json.dumps(runtime_identity, sort_keys=True).encode()).hexdigest()
    if digest(root / 'target/MainStatement.lean') != FROZEN_TARGET_SHA256:
        raise SystemExit('Frozen target hash differs; refusing replay.')
    sources = {p.relative_to(src).with_suffix('').as_posix().replace('/', '.'): p
               for p in src.rglob('*.lean')}
    imports = {}
    for name, p in sources.items():
        imports[name] = [word for line in re.findall(
            r'(?m)^(?:public\s+)?import\s+([^\n]+)', strip_noncode(p.read_text()))
                        for word in line.split()]
    graph = {m: [d for d in imports[m] if d in sources] for m in sources}
    order, cycles = dependency_order(graph)
    if cycles:
        raise SystemExit('Cyclic imports: ' + ', '.join(cycles))
    selected = set(sources) if not args.module else set(args.module)
    if selected - set(sources):
        raise SystemExit('Unknown modules: ' + ', '.join(sorted(selected - set(sources))))
    while True:
        more = selected | {d for m in selected for d in graph[m]}
        if more == selected:
            break
        selected = more
    order = [m for m in order if m in selected]
    if args.plan_only:
        print(json.dumps({'topological_order': order, 'runtime_fingerprint': runtime_hash,
                          'kernel_invoked': False}, indent=2))
        return 0
    for d in (out, receipts, logs):
        d.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env.update(config.get('environment', {}))
    # No uncontrolled inherited LEAN_PATH and no historical artifact overlays.
    env['LEAN_PATH'] = os.pathsep.join(map(str, [out, *external_roots]))
    seeds = read_json(args.seed_receipts) if args.seed_receipts else {}
    seeds = (seeds or {}).get('modules', {})
    summary = {'schema': 'lebrun-native-replay-v1', 'started_utc': utc(),
               'runtime_fingerprint': runtime_hash, 'runtime': runtime_identity,
               'requested_targets': args.module, 'selected_modules': order,
               'milestone_met': False, 'modules': {}, 'full_selected_graph_passed': False}
    write_json(build / 'RUN_STATUS.json', summary)
    good = {}
    failures = []
    for m in order:
        deps = {}
        blocked = [d for d in graph[m] if d not in good]
        if blocked:
            summary['modules'][m] = {'status': 'blocked', 'dependencies': blocked}
            continue
        for d in imports[m]:
            if d in sources:
                deps[d] = {'sha256': good[d]['output_sha256'], 'kind': 'project'}
            else:
                rel = Path(*d.split('.')).with_suffix('.olean')
                found = [p / rel for p in external_roots if (p / rel).is_file()]
                if not found:
                    raise SystemExit('Missing external import ' + d)
                deps[d] = {'sha256': digest(found[0]), 'kind': 'external'}
        key = {'source_sha256': digest(sources[m]), 'imports': imports[m],
               'dependency_artifacts': deps, 'runtime_fingerprint': runtime_hash,
               'flags': flags}
        artifact = out / Path(*m.split('.')).with_suffix('.olean')
        artifact.parent.mkdir(parents=True, exist_ok=True)
        receipt_path = receipts / (m + '.json')
        old = read_json(receipt_path)
        if (old and old.get('status') == 'passed' and old.get('key') == key
                and artifact.is_file() and digest(artifact) == old.get('output_sha256')):
            good[m] = old
            summary['modules'][m] = {'status': 'reused', 'output_sha256': old['output_sha256']}
            print('REUSE ' + m, flush=True)
            continue
        seed = seeds.get(m)
        # A seed must supply the exact expected direct dependency hashes as well
        # as source/output hashes. The caller retains its provenance separately.
        if (seed and seed.get('source_sha256') == key['source_sha256']
                and seed.get('imports') == key['imports']
                and seed.get('dependency_artifacts') == deps
                and seed.get('toolchain_lock_sha256') == runtime_identity['toolchain_lock_sha256']
                and Path(seed['artifact_path']).is_file()
                and digest(seed['artifact_path']) == seed.get('output_sha256')):
            shutil.copy2(seed['artifact_path'], artifact)
            rec = {'schema': 'lebrun-module-receipt-v1', 'status': 'passed', 'module': m,
                   'key': key, 'output_sha256': digest(artifact),
                   'evidence_kind': 'explicit_validated_historical_seed',
                   'seed_provenance': seed.get('provenance'), 'accepted_utc': utc()}
            write_json(receipt_path, rec)
            good[m] = rec
            summary['modules'][m] = {'status': 'historical_reuse',
                                     'output_sha256': rec['output_sha256']}
            print('SEED ' + m, flush=True)
            continue
        # Preserve any old artifact, but keep it out of the active search path.
        if artifact.exists():
            stale = build / 'invalidated' / (m + '.' + digest(artifact) + '.olean')
            stale.parent.mkdir(parents=True, exist_ok=True)
            artifact.replace(stale)
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
        log_prefix = logs / (m + '.' + stamp)
        cmd = [*command, *flags, '--root=' + str(src), '-o', str(artifact), str(sources[m])]
        rec = {'schema': 'lebrun-module-receipt-v1', 'status': 'running', 'module': m,
               'key': key, 'command': cmd, 'started_utc': utc(),
               'stdout': str(log_prefix) + '.stdout.jsonl',
               'stderr': str(log_prefix) + '.stderr.txt'}
        summary['modules'][m] = rec
        write_json(build / 'RUN_STATUS.json', summary)
        print('BUILD ' + m, flush=True)
        started = time.monotonic()
        try:
            with open(rec['stdout'], 'w') as stdout, open(rec['stderr'], 'w') as stderr:
                process = subprocess.run(cmd, cwd=src, env=env, stdout=stdout, stderr=stderr,
                                         timeout=args.timeout, check=False)
            rc = process.returncode
        except subprocess.TimeoutExpired:
            rc = 124
        unchanged = digest(sources[m]) == key['source_sha256']
        unchanged = unchanged and all(
            digest(out / Path(*d.split('.')).with_suffix('.olean')) == deps[d]['sha256']
            for d in graph[m])
        passed = rc == 0 and artifact.is_file() and unchanged
        rec.update({'status': 'passed' if passed else 'failed', 'return_code': rc,
                    'finished_utc': utc(), 'seconds': round(time.monotonic() - started, 3),
                    'source_and_dependencies_unchanged': unchanged,
                    'stdout_sha256': digest(rec['stdout']), 'stderr_sha256': digest(rec['stderr'])})
        if passed:
            rec['output_sha256'] = digest(artifact)
            rec['evidence_kind'] = 'native_kernel_compilation'
            good[m] = rec
        else:
            failures.append(m)
            if artifact.exists():
                failed = build / 'invalidated' / (m + '.failed.' + stamp + '.olean')
                failed.parent.mkdir(parents=True, exist_ok=True)
                artifact.replace(failed)
        write_json(receipt_path, rec)
        summary['modules'][m] = rec
        write_json(build / 'RUN_STATUS.json', summary)
        print(('PASS ' if passed else 'FAIL ') + m + ' (' + str(rec['seconds']) + 's)', flush=True)
        if not passed and not args.keep_going:
            break
    summary.update({'finished_utc': utc(), 'failures': failures,
                    'full_selected_graph_passed': len(good) == len(order),
                    'verified_module_count': len(good)})
    write_json(build / 'RUN_STATUS.json', summary)
    print(json.dumps({k: v for k, v in summary.items() if k not in {'modules', 'runtime', 'selected_modules'}}, indent=2))
    return 0 if summary['full_selected_graph_passed'] else 1


if __name__ == '__main__':
    sys.exit(main())
