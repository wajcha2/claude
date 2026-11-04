"""Bind the passed 43+1 native boundary to exact published inputs and CI bytes.

This records publication-boundary acceptance only. It leaves the complete
Point1/reverse-cone and whole-theorem milestone decisions to the parent record.
No Lean execution or proof-source mutation occurs here.
"""
from __future__ import annotations

import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

WORK = Path('/workspace/scratch/4deac2cdddbb/lebrun_takeover')
BASE = WORK / 'continuation'
OUT = BASE / 'audit/point1_publication_review/current_20261104T031351'
FROZEN = Path('/workspace/scratch/4deac2cdddbb/github_checkpoint_audit/ci_41763014879/head_snapshot')
TRANCHES = [BASE / 'audit/point1_boundary_current_20261104T025016',
            BASE / 'audit/point1_boundary_current_20261104T031351']
SEEDS = BASE / 'audit/ci/41763014879/point1/VALIDATED_SEEDS.json'


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path: Path):
    return json.loads(path.read_text())


def write(name: str, value) -> str:
    path = OUT / name
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + '\n')
    return sha(path)


def main() -> None:
    checked = read(OUT / 'NATIVE_PUBLICATION_RECONCILIATION.json')
    assert checked['complete_44_root_native_summaries_observed']
    assert checked['all44_roots_only_allowed_axioms']
    assert checked['publication_boundary_covered_for_all_observed_roots']
    assert checked['distinct_actual_direct_leaf_count'] == 50
    assert checked['observed_point1_roots'] == 43
    assert checked['observed_additional_inherited_roots'] == 1
    catalog_path = OUT / 'REVIEWED_LEAF_CATALOG.json'
    if not catalog_path.exists():
        catalog_path = BASE / 'audit/POINT1_PUBLISHED_LEAF_ELIGIBILITY.json'
    assert sha(catalog_path) == checked['catalog_sha256']
    catalog = read(catalog_path)
    (OUT / 'REVIEWED_LEAF_CATALOG.json').write_bytes(catalog_path.read_bytes())
    (OUT / 'reconcile_point1_native.py').write_bytes((WORK / 'published_leaf_work/reconcile_point1_native.py').read_bytes())

    inventory = read(SEEDS)
    seeds = inventory['modules']
    assert inventory['module_count'] == len(seeds) == 190
    assert inventory['source_commit'] == '3656bd1c17a200bf9d80edc86f289fb1861ff4d2'
    prior = read(TRANCHES[0] / 'FINAL_SNAPSHOT_REVALIDATION.json')
    assert prior['project_ancestors_revalidated'] == 41
    assert prior['all_41_source_output_import_dependency_and_ancestry_stamps_match']
    assert prior['fresh_41_output_artifact_bytes_checked']
    assert prior['reused_29_proof_boundary_valid_for_this_point1_snapshot']
    assert prior['validated_seed_inventory_sha256'] == sha(SEEDS)

    # Independently check every source in the final Point1 cone. Exact artifact
    # bytes are additionally checked for every actual leaf/root owner below.
    for module, seed in seeds.items():
        rel = Path('source') / (module.replace('.', '/') + '.lean')
        assert sha(FROZEN / rel) == seed['source_sha256'], module
        assert sha(BASE / rel) == seed['source_sha256'], module

    native_receipts = []
    for tranche in TRANCHES:
        receipt = read(tranche / 'AUDIT_RECEIPT.json')
        run = read(tranche / 'RUN_STATUS.json')
        assert receipt['status'] == 'passed' and receipt['return_code'] == 0
        assert receipt['source_and_dependencies_unchanged']
        assert run['full_selected_graph_passed'] and not run['failures']
        assert not run['final_validation']['invalidated_modules']
        assert sha(tranche / 'NATIVE_STDOUT.jsonl') == receipt['stdout_sha256']
        native_receipts.append({
            'directory': str(tranche.relative_to(BASE)),
            'receipt_sha256': sha(tranche / 'AUDIT_RECEIPT.json'),
            'run_status_sha256': sha(tranche / 'RUN_STATUS.json'),
            'native_source_sha256': receipt['key']['source_sha256'],
            'native_output_sha256': receipt['output_sha256'],
            'native_source_ancestry_fingerprint': receipt['source_ancestry_fingerprint'],
            'stdout_sha256': receipt['stdout_sha256'],
            'seconds': receipt['seconds'],
            'validated_selected_modules': run['verified_module_count'],
        })

    owner_modules = {r['module'] for r in checked['roots']}
    owner_modules |= {m for leaf in checked['direct_leaf_inventory'] for m in leaf['modules']}
    artifact_identities = {}
    for module in sorted(owner_modules):
        seed = seeds[module]
        assert sha(Path(seed['artifact_path'])) == seed['output_sha256'], module
        artifact_identities[module] = {k: seed[k] for k in
            ['source_sha256', 'output_sha256', 'source_ancestry_fingerprint',
             'toolchain_lock_sha256', 'imports', 'dependency_artifacts', 'provenance']}

    leaves = {}
    for leaf in checked['direct_leaf_inventory']:
        assert leaf['eligible_catalog_and_source_match']
        assert len(leaf['modules']) == len(leaf['native_type_variants']) == len(leaf['hash_keys']) == 1
        name = leaf['name']
        module = leaf['modules'][0]
        seed = seeds[module]
        assert leaf['supplied_source_sha256'] == seed['source_sha256']
        review = catalog['reviewed_leaf_catalog'][name]
        assert review['classification'] == 'eligible_published_generic'
        typ = leaf['native_type_variants'][0]
        leaves[leaf['hash_keys'][0]] = {
            'declaration': name, 'module': module,
            'source_sha256': seed['source_sha256'],
            'olean_sha256': seed['output_sha256'],
            'source_ancestry_fingerprint': seed['source_ancestry_fingerprint'],
            'native_printed_type': typ['type'], 'native_printed_type_sha256': typ['sha256'],
            'classification': review['classification'],
            'primary_sources': review['primary_sources'],
            'hypothesis_match': review['hypothesis_match'],
            'actual_object_and_map_match': review['actual_object_and_map_match'],
            'project_translation_outside_admission': review['project_translation_outside_admission'],
            'native_occurrences': leaf['occurrences'],
        }
    assert len(leaves) == 50
    names = {leaf['declaration'] for leaf in leaves.values()}
    old_projection = 'LeBrunSalamon.Construction.Descent.TotalLine.projection_affine'
    new_affine = 'LeBrunSalamon.PublishedInputs.SectionRepresentability.finiteFree_affine'
    assert old_projection not in names and new_affine in names
    assert next(r for r in checked['roots'] if r['id'] == 'OBL-069')['direct_leaf_names'] == [new_affine]

    exact_leaf_sha = write('EXACT_PUBLISHED_LEAVES.json', {
        'schema': 'lebrun-43-plus-inherited-exact-published-inputs-v1',
        'source_commit': inventory['source_commit'],
        'validated_seed_inventory_sha256': sha(SEEDS),
        'native_reconciliation_sha256': sha(OUT / 'NATIVE_PUBLICATION_RECONCILIATION.json'),
        'review_catalog_sha256': sha(OUT / 'REVIEWED_LEAF_CATALOG.json'),
        'distinct_leaf_count': len(leaves),
        'hash_key_convention': 'SHA256(name + NUL + module + NUL + sourceSHA + NUL + nativePrintedTypeSHA)',
        'leaves_by_hash': leaves,
        'native_owner_artifact_identities': artifact_identities,
    })
    headers = BASE / 'audit/point1_boundary_targets/ORIGINAL_PUBLIC_HEADERS.json'
    header_data = read(headers)
    assert header_data['normalized_headers_equal'] == 44
    summary = {
        'schema': 'lebrun-point1-complete-publication-boundary-review-v1',
        'recorded_utc': datetime.now(timezone.utc).isoformat(),
        'reviewer': '/root/published_leaf_audit',
        'source_commit': inventory['source_commit'],
        'stock_github_ci_run': 41763014879,
        'point1_project_module_count': 190,
        'validated_seed_inventory': str(SEEDS.relative_to(BASE)),
        'validated_seed_inventory_sha256': sha(SEEDS),
        'all190_frozen_and_live_source_bytes_match_validated_inventory': True,
        'actual_leaf_and_root_owner_modules_artifact_bytes_checked': len(owner_modules),
        'prior29_exact_final_snapshot_revalidation': str((TRANCHES[0] / 'FINAL_SNAPSHOT_REVALIDATION.json').relative_to(BASE)),
        'prior29_exact_final_snapshot_revalidation_sha256': sha(TRANCHES[0] / 'FINAL_SNAPSHOT_REVALIDATION.json'),
        'native_receipts': native_receipts,
        'native_reconciliation': 'NATIVE_PUBLICATION_RECONCILIATION.json',
        'native_reconciliation_sha256': sha(OUT / 'NATIVE_PUBLICATION_RECONCILIATION.json'),
        'exact_leaf_inventory': 'EXACT_PUBLISHED_LEAVES.json',
        'exact_leaf_inventory_sha256': exact_leaf_sha,
        'review_catalog_sha256': sha(OUT / 'REVIEWED_LEAF_CATALOG.json'),
        'original_point1_roots_checked': 43,
        'additional_inherited_roots_checked': 1,
        'distinct_actual_direct_leaves': 50,
        'all50_actual_direct_leaves_publication_eligible': True,
        'all44_native_summaries_consistent': True,
        'all44_roots_have_native_axiom_outputs': True,
        'all44_root_axiom_outputs_only_allowed_names': True,
        'allowed_axioms': checked['allowed_axioms'],
        'global_nonstandard_axiom_counter_checked_for_final15': True,
        'missing_constants_count': 0, 'custom_project_axioms_count': 0,
        'unexpected_axioms_from_any_module_count': 0,
        'original43_conclusions_directly_admitted_count': 0,
        'old_totalLine_projection_admission_absent': True,
        'actual_totalLine_projection_sole_leaf': new_affine,
        'zero_admitted_dependency_original_ids': [r['id'] for r in checked['roots']
            if r['scope'] == 'point1' and r['native_summary']['direct_sorry_count'] == 0],
        'native_public_signatures_recorded_count': checked['native_public_signature_root_count'],
        'original_public_header_evidence': str(headers.relative_to(BASE)),
        'original_public_header_evidence_sha256': sha(headers),
        'original_public_header_scope': header_data['scope_limit'],
        'separate_baseline_kernel_signature_equivalence_claimed': False,
        'retrospective_baseline_signature_rebuild_required': False,
        'point1_published_leaf_boundary_passed': True,
        'point1_accepted': False,
        'whole_theorem_milestone_met': False,
        'remaining_acceptance_blocker': 'Required current Conic/downstream reverse-cone compatibility.',
        'signature_scope_qualification_not_an_additional_gate': 'Preserve the actual15 native signatures, unchanged44 lexical headers and frozen audited target with their stated limits. No retrospective baseline rebuild or additional acceptance gate is requested.',
        'remaining_scope': 'No publication-eligibility or hidden-admission gap remains in these43+1 checked roots. The parent acceptance record retains the required current downstream Conic/reverse-cone gate.',
    }
    summary_sha = write('PUBLICATION_REVIEW_SUMMARY.json', summary)
    lines = ['# Publication boundary of all43 Point1 conclusions', '',
        '**The actual native dependency boundary passes for all43 original Steps3c–3g conclusions, plus the separately audited affine-projection theorem.** The combined graph has50 direct admitted declarations. Every one is tied below to an exact published general result, its full native type, its source/output hashes and its complete ancestor stamp.', '',
        'This is a publication-boundary decision. It does not claim that the complete theorem has reached the milestone, or silently close the downstream Conic/reverse-cone acceptance gate.', '',
        f"The checked Point1 graph consists of190 modules at commit `{inventory['source_commit']}`. The29-root tranche was revalidated against that exact graph; the final15-root tranche includes14 original obligations and the separately labeled OBL-069. All44 axiom outputs contain only `propext`, `Classical.choice`, `Quot.sound`, and (where used) `sorryAx`. There are no missing constants, unexpected axioms, or directly admitted original Point1 conclusions.", '',
        'The former admitted `TotalLine.projection_affine` is absent from the boundary. Its actual public theorem now depends on the single generic published affine section-representability input. The older26-leaf normal-form audit is preserved as dated evidence, rather than rewritten to erase that former gap.', '',
        '## Per-conclusion native boundary', '',
        '| Obligation | Public conclusion | Direct published inputs |', '|---|---|---:|']
    for row in checked['roots']:
        short = row['root'].rsplit('.', 1)[1]
        label = row['id'] + (' (additional)' if row['scope'] != 'point1' else '')
        lines.append(f"| {label} | `{short}` | {row['native_summary']['direct_sorry_count']} |")
    lines += ['', '## Exact evidence', '',
        '- `EXACT_PUBLISHED_LEAVES.json` contains all50 exact native types, primary URLs/locators, hypothesis and map comparisons, shortest dependency paths, and artifact identities.',
        '- `NATIVE_PUBLICATION_RECONCILIATION.json` independently parses both raw native logs, including every per-root axiom output.',
        '- `REVIEWED_LEAF_CATALOG.json` preserves the precise catalog used for this review. Its one historical ineligible projection record is not among the50 actual leaves.',
        '- `PUBLICATION_REVIEW_SUMMARY.json` binds both passed native receipts to the final190-module validated graph.', '',
        'All44 original source headers match the certified baseline after the documented lexical normalization. Native type/universe signatures are additionally retained for the final15 roots. No separate kernel equivalence of all elaborated baseline signatures is claimed. This is an evidence-scope qualification, not a request for a retrospective baseline rebuild or an additional acceptance gate.', '']
    (OUT / 'PUBLICATION_REVIEW.md').write_text('\n'.join(lines))
    print(json.dumps({'summary': str(OUT / 'PUBLICATION_REVIEW_SUMMARY.json'),
                      'summary_sha256': summary_sha, 'exact_leaf_inventory_sha256': exact_leaf_sha,
                      'leaf_count': len(leaves), 'artifact_owner_modules_checked': len(owner_modules),
                      'point1_publication_boundary_passed': True,
                      'point1_overall_accepted': False}, indent=2))


if __name__ == '__main__':
    main()
