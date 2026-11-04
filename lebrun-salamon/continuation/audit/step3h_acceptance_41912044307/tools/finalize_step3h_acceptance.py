#!/usr/bin/env python3
"""Prepare acceptance files only after independent native/artifact/type review.

This is an offline finalizer. It does not launch CI, edit source, write Git,
or accept local diagnostic receipts as native evidence.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path

BASELINE_COMMIT = "bd3524b4bb12ac73cbf7572698208b017071b699"
CANDIDATE_COMMIT = "4d1aa547453f50736035a91f6fea81d340359143"
CANDIDATE_TREE = "f0b2e438b972ca9f08c96bfeffcdfb6a55ea2a67"
MANIFEST = "e48fa8114d0a9eb29d6a8d67442af17a135f64e1160b5936792414b406551998"
PLAN = "aad635599e8be2e0b315c851c84713ce1948cf594ceb06f57610c2d559d165f8"
BASELINE_LEDGER = "2863cfaa283fd3f8ab894ac74eb4469c35a8b7491342da9369ab93a092157844"
NEW_IDS = {f"OBL-{n:03}" for n in range(44, 49)}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")


def finalize(old_bytes, report_bytes, review):
    old, report = json.loads(old_bytes), json.loads(report_bytes)
    need(sha(old_bytes) == BASELINE_LEDGER, "Baseline accepted ledger differs")
    need(old["metric"]["accepted_units"] == 74 and old["metric"]["denominator"] == 133,
         "Unexpected accepted baseline")
    need(review["reviewer"] == "root" and review["independent_review_passed"] is True,
         "Independent final review has not passed")
    need(review["verification_sha256"] == sha(report_bytes), "Report review hash differs")
    need(review["workflow_status"] == "completed" and review["workflow_conclusion"] == "success",
         "Official workflow is not successfully complete")
    need(review["official_artifact_metadata_verified"] is True and
         review["official_artifact_archive_verified"] is True and
         review["all_native_receipts_outputs_logs_and_ancestries_verified"] is True,
         "Official evidence has not been independently verified")
    need(report["schema"] == "lebrun-continuation-full-verification-v1", "Wrong report schema")
    need(report["baseline_accepted_commit"] == BASELINE_COMMIT and
         report["git_binding"]["commit"] == CANDIDATE_COMMIT and
         report["git_binding"]["tree"] == CANDIDATE_TREE and
         report["source_manifest_sha256"] == MANIFEST and
         report["candidate_plan_sha256"] == PLAN, "Wrong candidate source or plan")
    need(str(review["artifact"]["run_id"]) == str(report["github_run_id"]) and
         str(review["run_attempt"]) == str(report["github_run_attempt"]), "Wrong official run")
    for key in ("all_current_sources_kernel_checked", "all_relevant_boundaries_checked",
                "current_native_evidence_ready_for_acceptance_review"):
        need(report[key] is True, "Incomplete native acceptance evidence: " + key)
    need(report["accepted_units_unchanged"] == 74 and report["new_units_credited"] == 0 and
         report["helper_units_credited"] == 0 and report["acceptance_ledger_modified"] is False,
         "Native evidence improperly credited units")
    native, boundaries = report["native"], report["boundaries"]
    need(report["source_modules"] == 308 and len(native["records"]) == 308 and
         native["whole_current_graph_passed"] is True and native["full_selected_graph_passed"] is True
         and not native["errors"], "Current source graph is incomplete")
    need(boundaries["all_current_root_boundaries_verified"] is True and
         boundaries["original_root_accounting_count"] == 49 and
         boundaries["fresh_current_native_root_audits"] == 39 and
         boundaries["preserved_historical_root_boundaries"] == 10 and
         boundaries["retired_admissions_absent_from_current_boundaries"] is True,
         "Incomplete boundary coverage")
    roots = {r["id"]: r for r in boundaries["roots"]}
    old_ids = {r["id"] for r in old["accepted_original_obligations"]}
    need(len(roots) == 49 and set(roots) == old_ids | NEW_IDS and len(old_ids) == 44,
         "Original root accounting changed")
    inputs = report["new_native_publication_type_review_still_required"]
    type_reviews = review["native_published_input_reviews"]
    need(len(inputs) == 5 and set(type_reviews) == set(inputs), "Missing native published-input review")
    for name, item in type_reviews.items():
        binding = boundaries["eligible_leaf_bindings"][name]
        need(item["reviewer"] == "root" and item["eligible"] is True and
             item["native_type_sha256"] == binding["native_type_sha256"] and
             item["native_context_sha256"] == binding["native_context_sha256"],
             "Published-input review is incomplete or stale: " + name)
    need(set(boundaries["actual_direct_leaf_names"]) <= set(boundaries["eligible_leaf_bindings"]),
         "Unreviewed admitted input")
    signatures = {x["name"]: x for x in boundaries["fresh_baseline_signature_comparisons"]}
    need(all(r["declaration"] in signatures for r in roots.values()), "Missing original type comparison")
    manifest = {line.split("  ", 1)[1]: line.split("  ", 1)[0]
                for line in report["complete_source_manifest"].splitlines()}
    need(sha(report["complete_source_manifest"].encode()) == MANIFEST, "Manifest text differs")
    now = review["accepted_utc"]
    record_path = review["acceptance_record_path"]
    verification_path = review["verification_path"]
    evidence_id = "P-STEP3H-ACCEPTED-" + str(report["github_run_id"])
    ledger = copy.deepcopy(old)
    ledger["historical_observations_before_step3h"] = {
        "ledger_path": review["previous_ledger_path"], "ledger_sha256": BASELINE_LEDGER,
        "accepted_commit": BASELINE_COMMIT, "point1_native_and_publication_boundary_preserved": True,
        "point1_acceptance_event_rewritten": False}
    pending = {x["id"]: x for x in ledger["pending_original_obligations"]}
    need(NEW_IDS <= set(pending), "A proposed new unit is not pending")
    accepted = ledger["accepted_original_obligations"] + [pending[i] for i in sorted(NEW_IDS)]
    for item in accepted:
        root = roots[item["id"]]
        need(item["declaration"] == root["declaration"], "Original declaration changed")
        module = root["module"]
        native_record = native["records"][module]
        if item["id"] in old_ids:
            item["historical_point1_acceptance_record"] = item["complete_acceptance_record"]
            item["historical_point1_native_and_publication_boundary"] = item["native_and_publication_boundary"]
        item.update({"status": "accepted_current_native_and_exact_published_boundary",
                     "accepted": True, "current_lexical_status": "no_direct_admission",
                     "acceptance_evidence_complete": True,
                     "current_source_file_sha256": manifest["source/" + module + ".lean"],
                     "complete_acceptance_record": record_path})
        item["evidence_ids"] = sorted(set(item["evidence_ids"]) | {evidence_id})
        item["native_and_publication_boundary"] = {
            **root, "source_sha256": item["current_source_file_sha256"],
            "module_output_sha256": native_record["output_sha256"],
            "module_source_ancestry_fingerprint": native_record["source_ancestry_fingerprint"],
            "native_module_receipt_sha256": native_record["receipt_sha256"],
            "original_public_header_preserved_lexically": True,
            "original_native_public_type_and_universes_preserved": True,
            "current_native_signature_comparison": signatures[item["declaration"]],
            "original_project_conclusion_directly_admitted": False,
            "native_and_publication_boundary_passed": True,
            "current_reverse_dependency_gate_passed": True,
            "current_reverse_dependency_verification": verification_path,
            "current_reverse_dependency_verification_sha256": sha(report_bytes),
            "independent_final_review": review["independent_review_path"],
            "accepted": True, "accepted_utc": now}
    ledger["accepted_original_obligations"] = sorted(accepted, key=lambda x: x["id"])
    ledger["pending_original_obligations"] = [x for x in ledger["pending_original_obligations"]
                                                if x["id"] not in NEW_IDS]
    for item in ledger["pending_original_obligations"]:
        item["current_source_file_sha256"] = manifest["source/" + item["file"]]
    need(len(ledger["pending_original_obligations"]) == 42, "Pending count differs")
    ledger["metric"].update({"accepted_units": 79, "pending_units": 54,
        "percentage": 7900 / 133, "percentage_display": 59.40, "rounded_percentage": 59,
        "formula": "(22 retired originals +8 historically accepted Step3b wrappers +44 accepted Point1/additional roots +5 accepted Step3h obligations) /133",
        "numerator_boundary": "Original accepted checklist units only; no helper, input review or build unit."})
    for group in ledger["groups"]:
        if group["group"] == "Steps3c–3n original obligations":
            group["accepted"] = 49
    ledger["denominator_basis"].update({"current_pending_original_obligations": 42,
        "remaining_original_obligations_scope": "Historical post-Step3b baseline (91); current pending original obligations42. Fixed denominator unchanged."})
    ledger["source_snapshot"].update({"commit": CANDIDATE_COMMIT, "tree": CANDIDATE_TREE,
        "source_module_count": 308, "source_manifest_sha256": MANIFEST, "snapshot_utc": now})
    ledger["latest_verified_full_graph"] = {
        "run_id": report["github_run_id"], "run_attempt": report["github_run_attempt"],
        "commit": CANDIDATE_COMMIT, "source_modules_selected": 308,
        "status": "completed", "conclusion": "success", "counts": native["status_counts"],
        "accepted_count_at_that_commit": 308, "full_selected_graph_passed": True,
        "evidence": verification_path, "source_manifest_sha256": MANIFEST,
        "scope": "All current source modules; the exported endpoint remains conditional."}
    ledger["checkpoint_update"] = {
        "source_freeze": "SOURCE.sha256", "verification": verification_path,
        "step3h_accepted": True, "new_original_roots": sorted(NEW_IDS),
        "current_original_roots_checked": 49, "fresh_native_root_walks": 39,
        "historical_boundaries_reused_in_exact_context": 10,
        "actual_eligible_leaf_count": len(boundaries["actual_direct_leaf_names"]),
        "whole_current_proof_graph_kernel_verified": True,
        "accepted_units_added": 5, "accepted_units_total": 79, "total_units": 133,
        "milestone_met": False}
    ledger["updated_utc"] = now
    ledger["milestone_met"] = False
    ledger["whole_current_proof_graph_kernel_verified"] = True
    ledger["frozen_unconditional_endpoint_kernel_verified"] = False
    for gate in ledger["final_gates"]:
        need(gate["accepted"] is False and gate["status"] == "pending_acceptance", "Final gate promoted")
        gate["evidence_ids"] = sorted(set(gate["evidence_ids"]) | {evidence_id})
        if gate["id"] == "GATE-03":
            gate["partial_progress"] = (f"All49 accepted original roots have current native boundaries with "
                f"{len(boundaries['actual_direct_leaf_names'])} eligible published inputs; the final theorem and42 remaining originals are unaudited for acceptance.")
    for item in ledger["definition_validations"]:
        need(item["accepted"] is False, "Definition validation unexpectedly promoted")
    ledger["evidence"][evidence_id] = {"kind": "complete_step3h_acceptance",
        "path": record_path, "verification_path": verification_path,
        "verification_sha256": sha(report_bytes), "source_commit": CANDIDATE_COMMIT}
    ledger["ledger_production"] = {
        "source_mutation": False, "lean_invoked_by_ledger_writer": False,
        "native_evidence_run": report["github_run_id"],
        "historical_ledger_snapshot": review["previous_ledger_path"],
        "only_written_files": ["audit/MILESTONE_PROGRESS.json", record_path]}
    acceptance = {"schema": "lebrun-step3h-acceptance-v1", "accepted_utc": now,
        "baseline_accepted_commit": BASELINE_COMMIT, "compiled_commit": CANDIDATE_COMMIT,
        "compiled_tree": CANDIDATE_TREE, "source_manifest_sha256": MANIFEST,
        "candidate_plan_sha256": PLAN, "original_ids_accepted": sorted(NEW_IDS),
        "accepted_units_before": 74, "accepted_units_added": 5, "accepted_units_after": 79,
        "denominator": 133, "percentage": 7900 / 133, "helper_units_credited": 0,
        "published_inputs_are_extra_units": False, "milestone_met": False,
        "verification_path": verification_path, "verification_sha256": sha(report_bytes),
        "independent_review_path": review["independent_review_path"],
        "official_artifact": review["artifact"], "root_boundaries": boundaries,
        "source_changed_after_compilation": False,
        "documentation_commit_is_a_new_native_compilation": False,
        "remaining": {"original_obligations": 42, "definition_validations": 8, "final_gates": 4}}
    return ledger, acceptance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("baseline-ledger", "verification", "review", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    ledger, acceptance = finalize(args.baseline_ledger.read_bytes(),
                                  args.verification.read_bytes(), read(args.review))
    # No writes are performed until every required acceptance condition passes.
    write(args.output / "audit/MILESTONE_PROGRESS.json", ledger)
    write(args.output / read(args.review)["acceptance_record_path"], acceptance)
    print(json.dumps({"accepted": 79, "denominator": 133, "pending": 54,
                      "percentage": 59.40, "milestone_met": False}))


if __name__ == "__main__":
    main()
