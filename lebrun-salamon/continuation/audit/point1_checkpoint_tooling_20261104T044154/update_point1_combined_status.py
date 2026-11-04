"""Refresh status only inside an announced immutable candidate snapshot."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import sys
from datetime import datetime

parser = argparse.ArgumentParser()
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--validated-seeds', type=Path, required=True)
parser.add_argument('--cache-run', type=int, required=True)
parser.add_argument('--cache-stage', choices=['full_graph', 'early_ext01'], default='full_graph')
parser.add_argument('--latest-full-run', type=int)
args = parser.parse_args()
root = args.root.resolve()
assert root.name == 'continuation' and 'point1_snapshot_' in str(root)
# This writer intentionally describes a pending Point1 gate. It must never
# overwrite the parent's later acceptance promotion during a metadata refresh.
metric_guard = json.loads((root/'audit/MILESTONE_PROGRESS.json').read_text())['metric']
status_guard = json.loads((root/'TAKEOVER_STATUS.json').read_text())
if (metric_guard['accepted_units'] != 30 or metric_guard['denominator'] != 133
        or status_guard.get('proof_batch', {}).get('point1_complete', False)):
    raise SystemExit('Pending-only status refresh refused: preserve the existing promoted acceptance ledger and use a metadata-only publication.')
sys.path.insert(0, str(root / 'scripts'))
from replay_checkpoint import source_graph, dependency_order

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(rel):
    return json.loads((root / rel).read_text())

def write(rel, value):
    (root / rel).write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')

freeze = read('audit/point1_checkpoint/FREEZE.json')
static = read('audit/current/CHECKPOINT_STATIC_AUDIT.json')
plan = read('audit/current/REBUILD_PLAN.json')
cache_run = args.cache_run
latest_full_run = args.latest_full_run or cache_run
ci_path = f'audit/ci/{latest_full_run}/CI_RECEIPT.json'
ci = read(ci_path)
cache_path = f'audit/ci/{cache_run}/' + ('early_ext01/' if args.cache_stage == 'early_ext01' else '') + 'CI_RECEIPT.json'
cache_ci = read(cache_path)
assert cache_ci['run']['id'] == cache_run
if args.cache_stage == 'early_ext01':
    assert cache_ci['stage'] == 'early_ext01' and cache_ci['full_selected_graph_passed']
cache_description = ('the verified early Ext01 artifact from run' if args.cache_stage == 'early_ext01' else 'run')
accepted_count = ci['accepted_count']
selected_count = ci['selected_module_count']
ci_counts = ci['counts']
ci_commit = ci['run']['head_sha']
failed_names = ', '.join('`' + x + '`' for x in ci['failures'])
assert static['static_integrity_passed']
assert accepted_count > 0 and ci['run']['id'] == latest_full_run
assert ci['run']['status'] == 'completed'
assert not ci['final_validation']['invalidated_modules']
assert not ci['final_validation']['changed_runtime_files']
assert freeze['strict_ci_cache_source_run'] == cache_run
stamp = freeze['frozen_utc']
sources, imports, graph = source_graph(root / 'source')
order, cycles = dependency_order(graph)
assert not cycles
seeds = json.loads(args.validated_seeds.read_text())['modules']
eligible, excluded = {}, {}
for module in order:
    entry = seeds.get(module)
    if entry is None:
        excluded[module] = ['No accepted output from the frozen cache source run.']
        continue
    reasons = []
    if sha(sources[module]) != entry['source_sha256']:
        reasons.append('Source differs from the accepted CI input.')
    if imports[module] != entry['imports']:
        reasons.append('Imports differ from the accepted CI input.')
    if entry['toolchain_lock_sha256'] != sha(root / 'TOOLCHAIN.lock.json'):
        reasons.append('Toolchain lock differs.')
    for ancestor in graph[module]:
        if ancestor not in eligible:
            reasons.append('Project dependency is ineligible: ' + ancestor)
        elif entry['dependency_artifacts'].get(ancestor, {}).get('sha256') != eligible[ancestor]['output_sha256']:
            reasons.append('Project dependency output differs: ' + ancestor)
    artifact = Path(entry['artifact_path'])
    if not artifact.is_file() or sha(artifact) != entry['output_sha256']:
        reasons.append('Validated output artifact is missing or differs.')
    if reasons:
        excluded[module] = reasons
    else:
        eligible[module] = entry
cache_count = len(eligible)
write('audit/point1_checkpoint/CACHE_ELIGIBILITY_AT_FREEZE.json', {
    'schema': 'lebrun-checkpoint-cache-eligibility-v1', 'source_run_id': cache_run,
    'source_commit': cache_ci['run']['head_sha'], 'source_stage': args.cache_stage, 'frozen_utc': stamp,
    'accepted_outputs_at_source_commit': cache_ci['accepted_count'], 'eligible_current_ancestry_count': cache_count,
    'eligible_modules': sorted(eligible), 'excluded': excluded,
    'validation': 'Previously validated pinned-stock-CI outputs; current source, imports, lock, output bytes, and entire project dependency ancestry rechecked at freeze. CI repeats runtime and dependency validation before reuse and at completion.'})

files = {row['file']: row['sha256'] for row in static['source_files']}
aggregate = hashlib.sha256(''.join(f'{k} {v}\n' for k, v in sorted(files.items())).encode()).hexdigest()
count = static['source_modules']
admissions = static['token_counts']['sorry']
assert count == len(sources) == freeze['source_modules']
point1_rows = [x for x in read('audit/MILESTONE_PROGRESS.json')['pending_original_obligations']
               if x['substep'] in ['3c', '3d', '3e', '3f', '3g']]
assert len(point1_rows) == 43
assert {x['id'] for x in point1_rows} == {f'OBL-{n:03d}' for n in range(1, 44)}
point1_modules = sorted({Path(x['file']).stem for x in point1_rows})
write('audit/point1_checkpoint/POINT1_MODULE_TARGETS.json', {
    'schema': 'lebrun-fixed-point1-module-targets-v1',
    'frozen_utc': stamp,
    'scope': 'The modules containing the fixed 43 original Step 3c–3g obligations and their complete project ancestry. Module replay does not by itself establish source eligibility or proof acceptance.',
    'obligations': [{k:x[k] for k in ['id','substep','declaration','file']} for x in point1_rows],
    'modules': point1_modules})
step3d = read('audit/STEP3D_INTEGRATION_READY.json')
assert step3d['public_type_adapters_passed'] and step3d['totalLine_and_totalBundle_both_repaired']
bivector = read('audit/p1_source_bivector_work/SCOPE.json')
assert bivector['old_source_bivector_admission_removed']
product = read('audit/ci_compatibility_repairs/PRODUCT_LATEST_STATUS.json')
assert product['source_sha256'] == sha(root / 'source/LSProductGeometry.lean')
assert product['native_status'] == 'passed'

boundary_path = 'audit/point1_acceptance_current_20261104T031351/POINT1_ACCEPTANCE.json'
boundary = read(boundary_path)
assert boundary['status'] == 'native_and_publication_boundaries_passed_current_reverse_cone_pending'
assert boundary['point1_original_obligations'] == 43 and boundary['native_original_roots_checked'] == 44
assert boundary['distinct_actual_direct_admitted_inputs'] == 50
assert boundary['missing_constants'] == boundary['custom_project_axioms'] == boundary['unexpected_axioms_from_any_module'] == 0
assert not boundary['original_project_admissions_in_actual_closure']
review = boundary['independent_publication_review']
assert review['independent_review_passed_for_original43_and_OBL069']
assert review['all50_actual_admitted_inputs_eligible'] and review['final_snapshot_source_output_ancestry_binding_passed']
for key in ['summary','actual_leaf_source_type_inventory','native_raw_log_reconciliation','reviewed_catalog_snapshot']:
    assert sha(root / review[key]) == review[key + '_sha256']
point1_seed_path = boundary['source_snapshot']['validated_seed_inventory']
assert sha(root / point1_seed_path) == boundary['source_snapshot']['validated_seed_inventory_sha256']
point1_seeds = read(point1_seed_path)['modules']
assert len(point1_seeds) == 190
for module, original in point1_seeds.items():
    assert module in eligible, 'A Point1 source or ancestor changed since its native boundary audit: ' + module
    current = eligible[module]
    assert current['source_sha256'] == original['source_sha256']
    assert current['output_sha256'] == original['output_sha256']
    assert current['source_ancestry_fingerprint'] == original['source_ancestry_fingerprint']
accepted_modules = [entry for entry in ci['modules'] if entry['status'] in ['passed','reused']]
fresh_in_run = sum(not bool(entry.get('cache_restore_provenance')) for entry in accepted_modules)
prior_cache = accepted_count - fresh_in_run
write('audit/point1_checkpoint/POINT1_BOUNDARY_AT_FREEZE.json', {
    'schema':'lebrun-point1-boundary-freeze-binding-v1', 'frozen_utc':stamp,
    'boundary_record':boundary_path, 'boundary_record_sha256':sha(root / boundary_path),
    'point1_original_roots':43, 'additional_inherited_roots':1, 'actual_eligible_leaves':50,
    'point1_sources_outputs_and_complete_ancestry_revalidated':190,
    'required_reverse_cone_gate_passed':False, 'accepted_units_added':0})

frontier_path = 'audit/ci_compatibility_repairs/current_frontier_20261104T044154/SUMMARY.json'
frontier = read(frontier_path)
assert frontier['current_source_modules'] == count
assert not frontier['whole_current_graph_passed']
assert sha(root / frontier['seed_inventory']) == frontier['seed_inventory_sha256']
frontier_seeds = read(frontier['seed_inventory'])['modules']
assert len(frontier_seeds) == frontier['accepted_compatible_modules']
for m, entry in frontier_seeds.items():
    assert sha(sources[m]) == entry['source_sha256'] and imports[m] == entry['imports']
    assert sha(Path(entry['artifact_path'])) == entry['output_sha256']
    for dep in graph[m]:
        assert dep in frontier_seeds
        assert entry['dependency_artifacts'][dep]['sha256'] == frontier_seeds[dep]['output_sha256']

update = f'''## Point 1 checkpoint — {stamp}

**The proof and publication boundary is checked for all 43 original Steps 3c–3g obligations; the required current reverse-dependency compilation gate is still open.** The separately inherited affine-projection obligation OBL-069 is also checked. This checkpoint adds no accepted checklist units before the original plan's complete gate passes.

This immutable candidate contains **{count} Lean modules and {admissions} direct `sorry` tokens**. The frozen target and pinned toolchain lock are unchanged. `SOURCE.sha256` and [the source freeze](audit/point1_checkpoint/FREEZE.json) identify the exact candidate. Neither helper counts nor admission-token counts measure completion or establish publication eligibility.

### Current native and source evidence

The dedicated Point1 stage of [CI {latest_full_run}](https://github.com/wajcha2/claude/actions/runs/{latest_full_run}) passed **190/190 modules**: the 19 distinct containing modules for the fixed 43 obligations and their complete project ancestry. All source files, dependency outputs, logs, compiler/runtime identities and final ancestry checks were independently validated. [The Point1 evidence](audit/ci/{latest_full_run}/point1/README.md) records its exact scope.

The exhaustive declaration audit then checked **43 original roots plus OBL-069**, with **50 distinct actual admitted inputs**. Every actual leaf passed the independent primary-source/hypothesis/map review and is bound to its native type, source, output and ancestry hashes. No original project conclusion remains directly admitted in this audited boundary; no missing constant or unexpected project/global axiom was found. The old project-specific `TotalLine.projection_affine` admission is absent. Its actual theorem now reaches the precise generic affine section-representability input. See [the complete acceptance preparation](audit/point1_acceptance_current_20261104T031351/README.md) and [the source-eligibility ledger](audit/POINT1_PUBLISHED_LEAF_ELIGIBILITY.md).

The 29-root native tranche was carried forward only after all of its recorded ancestor source/output/import/dependency stamps and artifact bytes matched the same 190-module snapshot; the remaining 14 roots and OBL-069 were checked natively against that snapshot. All 44 original public headers match the certified baseline after comments and whitespace are removed, and the 15 changed-tranche native signatures are retained with their stated scope. These checks do not claim a new historical-baseline rebuild or completion of the separate definition-validation obligations. At this freeze, the entire 190-module source/output/ancestry binding was rechecked again in [POINT1_BOUNDARY_AT_FREEZE.json](audit/point1_checkpoint/POINT1_BOUNDARY_AT_FREEZE.json).

| Batch | Original obligations | Native proof and publication boundary | Acceptance |
| --- | ---: | --- | --- |
| 3c | 6 | Passed | Required reverse cone pending |
| 3d | 11 | Passed | Required reverse cone pending |
| 3e | 7 | Passed | Required reverse cone pending |
| 3f | 11 | Passed | Required reverse cone pending |
| 3g | 8 | Passed | Required reverse cone pending |
| Separate OBL-069 | 1 | Passed | Required reverse cone pending |

### Remaining compilation gate

The latest full replay checked commit `{ci_commit}` with all **{selected_count} modules** selected. It accepted **{accepted_count}**, with **{ci_counts.get('failed', 0)} failed and {ci_counts.get('blocked', 0)} blocked**. Across all stages of that run, {fresh_in_run} modules compiled natively and {prior_cache} came from the strictly validated prior cache. The final stage reports {ci_counts.get('passed', 0)} fresh builds and {ci_counts.get('reused', 0)} reuses because it also reused the earlier stages of the same run. Final source/runtime/ancestry validation found no invalidations. The failed modules were {failed_names}; [the full CI evidence](audit/ci/{latest_full_run}/README.md) preserves their exact diagnostics and all successful receipts.

The later current native checks have now repaired both recorded frontiers. **The whole Conic module passed in 186.003 seconds against 78 current ancestors**, preserving the actual differential implementation, all original public headers and its existing admission. Its small extracted reparametrization helper contains no admission. **The entire smoothing closure passed 120/120 modules**, including the checked VelocityAdditionFamily, ScaledVelocityDifferential, SuitablePair and SmoothingAssembly repairs. Their source and dependency receipts are preserved separately from the historical cloud failures.

The independently validated union now contains **{frontier['accepted_compatible_modules']}/{count} mutually compatible current native outputs**, leaving **{frontier['remaining_modules']} modules** for the remaining reverse-dependency replay. Source/import/lock/output hashes, direct dependency artifacts and recursive ancestry stamps were rechecked across the union; the recorded alternative ScaledVelocities output is used consistently by its descendants. See [the current native frontier]({frontier_path}) and its complete seed inventory. These passes have not yet closed the original plan's required reverse-cone gate. Off-graph unverified drafts are excluded from the source graph.

The next stock-compiler replay selects all **{count} modules**, with a 12000 MB memory cap, a 900-second per-module limit, and {cache_description} **{cache_run}** as its sole cache source. Full source/import/lock/output/ancestry checks permit **{cache_count}** previous outputs at this freeze. It first checks the LSSmoothingAssembly closure, including the repaired scaled-velocity branch, and uploads that separate diagnostic artifact. It then preserves separate Ext01, Geometry and fixed-Point1 artifacts before the full graph, and revalidates the entire selected graph at completion. No result from that future run is assumed.

### Current execution order and accounting

Replay the remaining current reverse cone, repair any newly exposed compatibility failures, and bind its successful artifacts to the already completed 43+1 native/publication audit. Only then can the parent-controlled fixed ledger promote the original obligations. Continue the remaining batches and the frozen endpoint/definition-validation work under the existing plan after that gate; the stronger Wolf-homothety endpoint and the whole published-theorems-only milestone remain open.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. This is a count of fully accepted checklist units, not mathematical effort, elapsed time or the proportion of compiled modules. The completed 43-root proof/publication work is recorded substantively without bypassing the original reverse-cone gate.

'''

for name, endmark in [('README.md', '## Findings at the takeover audit'),
                       ('TAKEOVER_PLAN.md', '## Completion announcements and the evidence recovered')]:
    path = root / name
    text = path.read_text()
    if '## Current targeted smoothing replay' in text:
        a, b = text.index('## Current targeted smoothing replay'), text.index('## Point 1 checkpoint')
        text = text[:a] + text[b:]
    start, end = text.index('## Point 1 checkpoint'), text.index(endmark)
    text = text[:start] + update + text[end:]
    if name == 'README.md':
        day = datetime.fromisoformat(stamp).strftime('%-d %B %Y')
        text = re.sub(r'Status on \d+ \w+ \d{4}:', 'Status on ' + day + ':', text)
        text = re.sub(r'^Steps \*\*3c, 3d, 3e and 3f were reported complete\*\*.*$',
            'The earlier completion announcements for Steps **3c, 3d, 3e and 3f** are preserved in the plan. The current native and publication boundary has now passed for all **43 Steps 3c–3g obligations**, plus the inherited affine-projection theorem. The original required reverse-dependency compilation gate remains open; it is distinct from the historical recovery certificate questions.', text, flags=re.M)
        text = text.replace('## Findings at the takeover audit', '## Findings at the takeover audit', 1)
        text = text.replace('The last recorded passing incremental stage is Step 3b:', 'At the initial takeover, the last recorded passing incremental stage was Step 3b:')
    else:
        text = text.replace('**3 November 2026**', '**Initial takeover audit: 3 November 2026. Current checkpoint and execution priorities are recorded below.**', 1)
        old_decision = 'Continue from the actual cumulative Step 3g V2 source, preserving Step 3b as the last recorded passing incremental stage. Reopen the unverified parts of Steps 3c–3g. The first milestone is **not met**, and a successful compilation of the recovered source alone would not have met it: the audit found a false admitted determinant statement, several composite or project-specific admissions, and an exported conclusion weaker than the frozen specification.'
        new_decision = 'Continue from the preserved cumulative source and its verified repairs. All 43 Point1 roots plus the inherited affine-projection theorem now pass their current native/publication boundary; complete the original required reverse-dependency compilation gate before accepting the batch. The published-theorems-only milestone remains **not met**, and the frozen target is unchanged. The historical determinant defect, composite admissions and weaker exported endpoint explain the repair programme documented below.'
        text = text.replace(old_decision, new_decision, 1)
        text = text.replace('This is a recovery and admission-boundary audit, with focused mathematical checks of consequential statements.', 'The initial recovery/admission-boundary audit used focused mathematical checks of consequential statements.')
        text = text.replace('## Completion announcements and the evidence recovered', '## Completion announcements and the evidence recovered', 1)
        historical_note = '\n\nThe following narrative preserves earlier recovery findings and execution records. The dated current-checkpoint section above and the linked current ledgers supersede historical progress wording below.\n'
        if historical_note.strip() not in text:
            text = text.replace('## Completion announcements and the evidence recovered\n', '## Completion announcements and the evidence recovered' + historical_note, 1)
        while historical_note + historical_note in text:
            text = text.replace(historical_note + historical_note, historical_note)
        text = text.replace('The working status for **3c–3f is therefore:', 'The initial recovered handover status for **3c–3f was therefore:')
        text = text.replace('## 2. Where we are in the mathematical proof', '## 2. Proof architecture and the original obligation inventory')
        text = text.replace('## 3. Mathematical findings and their current repairs', '## 3. Earlier mathematical findings and repair records')
        text = text.replace('## 5. Revised execution order', '## 5. Earlier revised execution order and continuing milestone rules')
        text = text.replace('This frozen continuation has 149 modules and regenerates the rebuild plan from its actual imports;', 'The current checkpoint regenerates the rebuild plan from its actual imports;')
        text = text.replace('Twelve simulated bookkeeping cases cover invalidation and source/artifact changes during a run;', 'Infrastructure fixtures cover invalidation and source/artifact changes during a run;')
    path.write_text(text)

path = root / 'audit/MILESTONE_PROGRESS.md'
text = path.read_text()
start, end = text.index('## New work with partial credit only'), text.index('## Earlier completion announcements')
text = text[:start] + update.replace('## Point 1 checkpoint', '## New work with partial credit only — checkpoint').replace('](audit/', '](') + text[end:]
text = re.sub(r'Recorded UTC: `[^`]+`\. (?:Current|Frozen) source snapshot: `[^`]+` across \d+ Lean modules\.',
              f'Recorded UTC: `{stamp}`. Frozen source snapshot: `{aggregate}` across {count} Lean modules.', text)
path.write_text(text)

row = {'run_id': latest_full_run, 'commit': ci['run']['head_sha'],
       'source_modules_selected': selected_count, 'compiler_memory_cap_mb': 12000,
       'status': 'completed', 'conclusion': 'failure', 'counts': ci['counts'],
       'accepted_count_at_that_commit': accepted_count, 'failed_modules': ci['failures'],
       'full_selected_graph_passed': False, 'evidence': ci_path,
       'scope': 'Exact committed source and ancestry only; later source edits are separately revalidated.'}
status = read('TAKEOVER_STATUS.json')
status['recorded_utc'] = stamp
status['date_local'] = stamp[:10]
status['current_source'].update({'modules': count, 'lines': static['source_lines'],
    'bytes': sum(x['bytes'] for x in static['source_files']), 'admissions': static['token_counts'],
    'published_namespace_count_not_certification': static['published_namespace_admissions'],
    'other_direct_admissions': static['other_admissions'], 'kernel_verified': False,
    'static_integrity_passed': True, 'snapshot_utc': stamp, 'aggregate_sha256': aggregate})
previous = status['proof_batch']
status.setdefault('proof_batch_history', []).append(previous)
status['proof_batch'] = {'status': 'All 43 original Point1 roots plus inherited OBL-069 have current native and independent publication boundaries passed, with 50 actual eligible leaves; the required current reverse cone remains the sole acceptance gate.',
    'kernel_accepted': False, 'accepted_units_added': 0, 'point1_obligation_count': 43,
    'point1_complete': False, 'point1_native_and_publication_roots_passed': 43, 'additional_inherited_roots_passed': 1, 'actual_eligible_leaf_count': 50, 'point1_dependency_closure_native_modules': 190, 'required_reverse_cone_passed': False, 'step3cd_native_or_exact_source_evidence': 17,
    'evidence_directories': list(dict.fromkeys(previous.get('evidence_directories', []) + [
        'audit/STEP3D_INTEGRATION_READY.json', 'audit/step3d_transport_build',
        'audit/step3d_exactness_build/cdf_replay_20261103T233324',
        'audit/step3cd_diagonal_build', 'audit/p1_source_bivector_work', boundary_path, review['summary'], f'audit/ci/{cache_run}']))}
status['cumulative_ci_attempts'] = [x for x in status['cumulative_ci_attempts'] if x['run_id'] != latest_full_run] + [row]
status['latest_completed_cumulative_ci_attempt'] = row
status['current_compatible_native_frontier'] = frontier
status['cumulative_ci_attempt'] = {'status': 'awaiting_commit_and_automatic_push_trigger',
    'result_not_yet_accepted': True, 'source_modules_selected': count,
    'source_freeze_utc': stamp, 'compiler_memory_cap_mb': 12000,
    'compiler_timeout_seconds_per_module': 900, 'cache_source_stage': args.cache_stage,
    'strict_cache_source_run_id': cache_run, 'expected_full_ancestry_cache_count': cache_count,
    'first_early_target': 'LSSmoothingAssembly',
    'early_smoothing_timeout_seconds_per_module': 900,
    'early_interface_target': 'RecompileExtensionsPart01',
    'second_early_interface_target': 'RecompileExtensionsPart04Geometry',
    'point1_closure_target_manifest': 'audit/point1_checkpoint/POINT1_MODULE_TARGETS.json',
    'point1_target_module_count': len(point1_modules),
    'early_interface_artifact_is_full_graph_acceptance': False,
    'full_selected_graph_passed': False}
status['rebuild_plan'].update({'changed_modules': plan['changed_count'],
    'affected_modules': plan['affected_count'],
    'omitted_affected_descendants': len(plan['omitted_from_archived_21_module_plan'])})
status['compatibility_repairs']['scope'] = 'Each module retains its separately recorded diagnostic ancestry; current full dependency graph acceptance is pending.'
status['compatibility_repairs']['modules']['LSProductGeometry'] = product
status['compatibility_repairs'].pop('compiler_slot', None)
status['compatibility_repairs']['relative_differential_evidence'] = 'audit/STEP3F_RELATIVE_DIFFERENTIAL.json'
write('TAKEOVER_STATUS.json', status)

ledger = read('audit/MILESTONE_PROGRESS.json')
ledger['updated_utc'] = stamp
ledger['source_snapshot'].update({'source_module_count': count, 'aggregate_sha256': aggregate, 'snapshot_utc': stamp})
ledger['checkpoint_update'] = {'source_freeze': 'audit/point1_checkpoint/FREEZE.json',
    'latest_full_ci': row, 'new_full_ci': 'pending', 'point1_native_publication_boundary_passed': True, 'point1_original_roots_checked': 43, 'additional_inherited_roots_checked': 1, 'actual_eligible_leaf_count': 50, 'point1_boundary_evidence': boundary_path,
    'whole_current_proof_graph_kernel_verified': False, 'accepted_units_added': 0,
    'retained_accepted_units': metric_guard['accepted_units'], 'total_units': metric_guard['denominator'],
    'current_compatible_native_frontier': frontier}
admitted = {x['name'] for x in static['admissions']}
for entry in ledger['pending_original_obligations']:
    entry['current_lexical_status'] = 'direct_admission' if entry['declaration'] in admitted else 'no_direct_admission'
    entry['current_source_file_sha256'] = files.get(entry['file'])
for entry in ledger['historically_accepted_step3b_obligations']:
    entry['current_static_check'] = {'no_direct_admission': entry['declaration'] not in admitted,
        'source_file_sha256': files.get(entry['file']),
        'scope': 'Lexical admission/source check; historical declaration-span comparison retained separately.'}
evidence_id = f'P-CI-{latest_full_run}'
ledger['evidence'][evidence_id] = {'path': ci_path,
    'sha256': sha(root / ci_path),
    'kind': 'historical_exact_commit_native_ci', 'accepted_modules': accepted_count,
    'failed': ci_counts.get('failed', 0), 'blocked': ci_counts.get('blocked', 0), 'source_commit': ci['run']['head_sha'],
    'current_source_full_graph_verified': False}
ledger['partial_progress_no_additional_credit'].append({
    'id': 'PARTIAL-POINT1-COMBINED-' + stamp,
    'description': 'All 43 original Point1 roots plus OBL-069 have passed their current native/publication boundary across 50 actual eligible leaves; the original required reverse-cone compilation gate remains open.',
    'evidence_ids': [evidence_id], 'supports': ['GATE-02'], 'accepted_units_added': 0})
write('audit/MILESTONE_PROGRESS.json', ledger)
(root / 'audit/point1_checkpoint/README.md').write_text('# Immutable Point 1 combined checkpoint\n\n' + update.replace('](audit/', '](../'))
(root / 'audit/point1_checkpoint/WORKING_TREE_AFTER_PUBLICATION.json').unlink(missing_ok=True)
print(json.dumps({'modules': count, 'sorry': admissions, 'aggregate_sha256': aggregate,
                  'safe_cache': cache_count, 'accepted_units_added': 0}))
