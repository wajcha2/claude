#!/usr/bin/env python3
"""Verify completed current passes in a failed official stage, without acceptance."""
import importlib.util
import json
import sys
import zipfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
BASE = HERE / 'continuation_3h_archive/41902480321'
OUT = BASE / 'failure13360788893'
P = json.loads((BASE / 'VALIDATION_INPUT_PENDING.json').read_text())
ROOT, OLD = Path(P['current_root']), Path(P['baseline_root'])
ARCHIVE = OUT / 'archive'
spec = importlib.util.spec_from_file_location('independent_archive', HERE / 'verify_continuation_archive.py')
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
v.need(v.H((HERE / 'verify_continuation_archive.py').read_bytes()) ==
       '0ba2c8b17741e45e43cb5ae8639831e75e60a72d3be181d23ddf82efc9b1da17', 'Unreviewed verifier')
git = v.read(P['git_binding']); v.check_auxiliary_git_bytes(ROOT, git, P['commit'], P['tree'])
sys.path.insert(0, str(ROOT / 'scripts'))
import continuation_support as cs
from restore_replay_cache import validated_unselected_cache, unselected_binding_errors
for name in ['digest','source_inventory','context_hash','closure','source_ancestry_fingerprint','sha_text']:
    setattr(v, name, getattr(cs, name))
baseline_path = ROOT / 'audit/continuation_3h/BASELINE.json'
plan_path = ROOT / 'audit/continuation_3h/CANDIDATE_PLAN.json'
baseline, plan = v.read(baseline_path), v.read(plan_path)
v.need(cs.digest(plan_path) == P['expected_plan_sha256'] and cs.digest(baseline_path) ==
       P['expected_baseline_sha256'], 'Source plan or baseline changed')
old_inv, inv, change = cs.candidate_plan(ROOT, OLD, baseline, plan)
v.need(inv['sha256'] == P['expected_source_manifest_sha256'], 'Current manifest changed')
v.check_git_bytes(ROOT, git, P['commit'], P['tree'])
meta = v.official_zip(OUT / 'official_artifact.zip', OUT / 'OFFICIAL_ARTIFACT_METADATA.json')
run = v.read(OUT / 'OFFICIAL_RUN_METADATA.json')
v.need(run['id'] == meta['workflow_run']['id'] == 41902480321 and
       run['head_sha'] == meta['workflow_run']['head_sha'] == P['commit'] and
       run['status'] == 'completed' and run['conclusion'] == 'failure' and
       run['event'] == 'push' and run['run_attempt'] == 1 and
       run['path'] == '.github/workflows/lebrun-3h-continuation-native.yml' and
       run['head_branch'] == 'codex/lebrun-3h-native-20261104' and
       meta['id'] == 13360788893 and meta['name'] == 'lebrun-3h-current-native-41902480321-1',
       'Wrong failed official workflow provenance')
with zipfile.ZipFile(OUT / 'official_artifact.zip') as z:
    members = [x for x in z.infolist() if not x.is_dir()]
    v.need(len(members) == len({x.filename for x in members}), 'Duplicate ZIP member')
    v.need({str(x.relative_to(ARCHIVE)) for x in ARCHIVE.rglob('*') if x.is_file()} ==
           {x.filename for x in members}, 'Extracted ZIP inventory differs')
    for item in members:
        v.need(cs.digest(ARCHIVE / item.filename) == v.H(z.read(item)), 'Extracted member differs')
old_build = HERE / 'continuation_3h_archive/baseline-control/kernel-evidence'
old_status = v.read(old_build / 'RUN_STATUS.json')
external = {}
for f in (old_build / 'receipts').glob('*.json'):
    for name, binding in v.read(f)['key']['dependency_artifacts'].items():
        if binding['kind'] == 'external':
            v.need(name not in external or external[name] == binding['sha256'], 'Conflicting external binding')
            external[name] = binding['sha256']
verifier = v.ArchivedNative(baseline, old_status['runtime'], external, P['relocated_runtime'])
build = ARCHIVE / 'kernel-evidence'
native = verifier.verify(ROOT, build)
status = v.read(build / 'RUN_STATUS.json')
report_path = ARCHIVE / 'continuation-evidence/stages/accepted_boundaries.json'
report = v.read(report_path)
preflight_path = ARCHIVE / 'continuation-evidence/PREFLIGHT.json'
preflight = v.read(preflight_path)
binding = {'commit':P['commit'],'tree':P['tree'],'source_manifest_sha256':inv['sha256'],
           'all_source_target_lock_manifest_git_blobs_verified': True}
v.need(preflight['candidate'] == binding and preflight['impact'] == change and
       preflight['plan_sha256'] == cs.digest(plan_path) and
       preflight['baseline_record_sha256'] == cs.digest(baseline_path), 'Preflight differs')
v.need(report['git_binding'] == binding and report['records'] == native['records'] and
       report['status_counts'] == native['status_counts'] and report['impact'] == change and
       report['candidate_plan_sha256'] == cs.digest(plan_path) and
       report['baseline_record_sha256'] == cs.digest(baseline_path) and
       report['preflight_sha256'] == cs.digest(preflight_path) and
       report['run_status_sha256'] == cs.digest(build/'RUN_STATUS.json') and
       report['complete_source_manifest'] == inv['text'] and
       set(report['selected']) == set(preflight['stages']['accepted_boundaries']['selected']) and
       report['return_code'] != 0 and report['full_selected_graph_passed'] is False and
       report['whole_current_graph_passed'] is False, 'Failed stage is inconsistent')
cache_path = build / 'CACHE_RESTORE.json'
cached, rejected = validated_unselected_cache(v.read(cache_path), baseline['runtime_fingerprint'])
v.need(rejected is None, 'Cached-unselected provenance invalid')
combined = dict(native['records'])
unselected = {}
for module in inv['order']:
    if module in status['modules'] or module not in cached:
        continue  # Explicit failed/blocked modules can never be replaced by cache.
    receipt_path = build/'receipts'/(module+'.json'); receipt = v.read(receipt_path)
    v.need(not unselected_binding_errors(cached[module], receipt), 'Cached receipt provenance differs')
    v.need(receipt['schema'] == 'lebrun-module-receipt-v1' and receipt['module'] == module and
           receipt['status'] == 'passed' and receipt['return_code'] == 0 and
           receipt['evidence_kind'] == 'native_kernel_compilation', 'Not a passed native cache receipt')
    deps = {}
    for dep in inv['imports'][module]:
        if dep in inv['sources']:
            v.need(dep in combined, 'Unverified cache project ancestor')
            deps[dep] = {'kind':'project','sha256':combined[dep]['output_sha256']}
        else:
            deps[dep] = verifier.external(dep)
    key = {'source_sha256':cs.digest(inv['sources'][module]),'imports':inv['imports'][module],
           'dependency_artifacts':deps,'runtime_fingerprint':baseline['runtime_fingerprint'],
           'flags':baseline['runtime_flags']}
    v.need(receipt['key'] == key, 'Cached-unselected current key differs')
    for stream in ['stdout','stderr']:
        log = build/'logs'/Path(receipt[stream]).name
        v.need(log.is_file() and cs.digest(log) == receipt[stream+'_sha256'], 'Cached native log differs')
        if stream == 'stdout':
            for line in log.read_text().splitlines():
                try: item = json.loads(line)
                except ValueError: continue
                v.need(item.get('severity') != 'error', 'Cached native output contains an error')
    output = build/'olean'/Path(*module.split('.')).with_suffix('.olean')
    v.need(output.is_file() and cs.digest(output) == receipt['output_sha256'], 'Cached output differs')
    stamp = cs.source_ancestry_fingerprint(module,key,{d:combined[d]['source_ancestry_fingerprint'] for d in inv['graph'][module]})
    v.need(stamp == receipt['source_ancestry_fingerprint'], 'Cached recursive context differs')
    record = {'module':module,'receipt_sha256':cs.digest(receipt_path),'key':key,
              'output_sha256':receipt['output_sha256'],'source_ancestry_fingerprint':stamp,
              'stdout_sha256':receipt['stdout_sha256'],'stderr_sha256':receipt['stderr_sha256'],
              'seconds':receipt.get('seconds'),'state':'unselected_validated_cache'}
    v.need(cs.context_hash(record) == baseline['native_contexts'][module], 'Unselected context not preserved')
    combined[module] = unselected[module] = record
failures = []
for module, state in status['modules'].items():
    if state['status'] != 'failed': continue
    rp = build/'receipts'/(module+'.json'); receipt = v.read(rp)
    v.need(not (build/'olean'/Path(*module.split('.')).with_suffix('.olean')).exists(), 'Failed output is still present')
    logs = {s:(build/'logs'/Path(receipt[s]).name).read_text() for s in ['stdout','stderr']}
    actual_errors = []
    for line in logs['stdout'].splitlines():
        try: item = json.loads(line)
        except ValueError: continue
        if item.get('severity') == 'error': actual_errors.append(item)
    old_receipt = v.read(old_build/'receipts'/(module+'.json'))
    v.need(receipt['key']['source_sha256'] == old_receipt['key']['source_sha256'], 'Failure source unexpectedly changed')
    failures.append({'module':module,'seconds':receipt['seconds'],'return_code':receipt['return_code'],
        'receipt_sha256':cs.digest(rp),'source_sha256':receipt['key']['source_sha256'],
        'source_and_dependencies_unchanged':receipt['source_and_dependencies_unchanged'],
        'stdout_sha256':receipt['stdout_sha256'],'stderr_sha256':receipt['stderr_sha256'],
        'stdout_bytes':len(logs['stdout'].encode()),'stderr_bytes':len(logs['stderr'].encode()),
        'emitted_errors':actual_errors,'previous_accepted_seconds':old_receipt['seconds'],
        'previous_accepted_receipt_sha256':cs.digest(old_build/'receipts'/(module+'.json')),
        'output_absent_and_ineligible_for_resume':True})
durations = []
for module in inv['order']:
    if module in combined or module not in old_inv['sources']: continue
    path=old_build/'receipts'/(module+'.json')
    old_receipt=v.read(path)
    if old_receipt.get('seconds',0)>210:
        durations.append({'module':module,'seconds':old_receipt['seconds'],
            'same_source':old_receipt['key']['source_sha256']==cs.digest(inv['sources'][module]),
            'receipt_sha256':cs.digest(path),'selected_in_failed_stage':module in status['modules']})
result = {'schema':'lebrun-independent-failed-continuation-stage-v1','official_artifact':meta,
    'commit':P['commit'],'tree':P['tree'],'source_manifest_sha256':inv['sha256'],
    'candidate_plan_sha256':cs.digest(plan_path),'source_modules':len(inv['sources']),
    'selected_modules':len(status['selected_modules']),'status_counts':native['status_counts'],
    'independently_verified_selected_passes':len(native['records']),
    'independently_verified_unselected_cache':len(unselected),'strict_current_reusable_count':len(combined),
    'selected_pass_records':native['records'],'unselected_cache_records':unselected,
    'cache_restore_sha256':cs.digest(cache_path),'failed_stage_report_sha256':cs.digest(report_path),
    'failures':failures,'remaining_accepted_historical_durations_over210':durations,
    'all_included_current_source_output_receipt_log_runtime_dependency_recursive_hashes_verified':True,
    'explicit_failed_or_blocked_status_overridden':False,'runtime_keys_rewritten':False,
    'compiler_invoked':False,'full_current_graph_passed':False,'current_boundary_audit_completed':False,
    'accepted_units_unchanged':74,'new_units_credited':0,'milestone_met':False,
    'verification_adapter_sha256':cs.digest(Path(__file__))}
out=OUT/'INDEPENDENT_FAILURE_AND_REUSABLE_CONTEXTS.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'verified_selected_passes':len(native['records']),'verified_unselected':len(unselected),
    'strict_reusable_total':len(combined),'failures':failures,'remaining_historical_over210':durations,
    'report':str(out),'sha256':cs.digest(out)}))
