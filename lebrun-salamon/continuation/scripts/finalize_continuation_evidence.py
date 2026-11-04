#!/usr/bin/env python3
"""Finalize compile/boundary evidence for review; never grant milestone credit."""
from __future__ import annotations
import argparse
import os
import json
from pathlib import Path
from continuation_support import (candidate_plan, compare_contexts, context_hash, digest,
    git_binding, need, publication_inputs, read_json, sha_text, verify_native_build, write_json)
from run_continuation_audit import audit_spec
from continuation_stage_policy import STAGE_ORDER, validate_stages, load_resume
from verify_continuation_boundaries import load_verified_audit, reconcile


def check_completed_stages(preflight, stages, current_native, plan_sha, baseline_sha):
    need(preflight.get("stage_order") == STAGE_ORDER and
         list(preflight["stages"]) == STAGE_ORDER and set(stages) == set(STAGE_ORDER),
         "Missing or reordered required native stage reports")
    hashes = {n: sha_text(json.dumps(r, indent=2, ensure_ascii=False) + "\n") for n, r in stages.items()}
    for name, report in stages.items():
        required = preflight["stages"][name]
        previous = STAGE_ORDER[:STAGE_ORDER.index(name)]
        need(report.get("completed_predecessor_report_sha256") == {n: hashes[n] for n in previous},
             "Completed stage predecessor sequence or hashes differ")
        need(report["stage"] == name and report["return_code"] == 0 and
             report["full_selected_graph_passed"] is True and not report["errors"],
             "A required native stage failed or was incomplete")
        need(report["source_manifest_sha256"] == current_native["source_manifest_sha256"] and
             report["candidate_plan_sha256"] == plan_sha and report["baseline_record_sha256"] == baseline_sha,
             "A stage belongs to a different source or plan")
        need(set(report["selected"]) == set(required["selected"]) == set(report["records"]),
             "Native stage coverage differs from its recomputed closure")
        need(report["module_timeout_seconds"] == required["module_timeout_seconds"],
             "Stage changed the approved timeout")
        need(report["fresh_native_passes_this_invocation"] + report["native_receipts_reused_this_invocation"] ==
             len(report["records"]), "Stage fresh/reuse accounting differs")
        for module, record in report["records"].items():
            need(module in current_native["records"] and
                 context_hash(record) == context_hash(current_native["records"][module]),
                 "A stage context is stale in the final native graph")
    need(stages["full"]["whole_current_graph_passed"] is True and
         current_native["whole_current_graph_passed"] is True and not current_native["errors"],
         "Current full source graph did not pass")


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ("root", "baseline-root", "baseline-build", "build-dir", "baseline", "plan",
                "preflight", "baseline-audit", "current-audit", "runtime-config", "reports", "output"):
        ap.add_argument("--" + key, type=Path, required=True)
    ap.add_argument("--commit", default=os.environ.get("GITHUB_SHA"), required=False)
    args = ap.parse_args()
    need(args.commit, "Exact Git commit required")
    baseline, plan, config = read_json(args.baseline), read_json(args.plan), read_json(args.runtime_config)
    _, inv, change = candidate_plan(args.root, args.baseline_root, baseline, plan)
    binding = git_binding(args.root, args.commit, baseline["continuation_prefix"])
    preflight = read_json(args.preflight)
    need(preflight["candidate"] == binding and preflight["impact"] == change and
         preflight["baseline_record_sha256"] == digest(args.baseline) and
         preflight["plan_sha256"] == digest(args.plan), "Final evidence differs from approved preflight")
    old_native = verify_native_build(args.baseline_root, args.baseline_build, config, baseline)
    need(old_native["whole_current_graph_passed"] and
         set(old_native["records"]) == set(baseline["native_contexts"]), "Accepted baseline graph is incomplete")
    for module, record in old_native["records"].items():
        need(context_hash(record) == baseline["native_contexts"][module], "Accepted native baseline changed")
    native = verify_native_build(args.root, args.build_dir, config, baseline)
    need(native["whole_current_graph_passed"] and native["full_selected_graph_passed"] and not native["errors"],
         "Final current graph is failed or incomplete")
    comparison = compare_contexts(native, baseline, change)
    need(not comparison["pending_current_modules"], "Affected contexts remain unvalidated")
    validate_stages(preflight, inv, baseline)
    resume = load_resume(args.root, plan, inv)
    resume_path = args.reports.parent / "RESUME_CACHE_VALIDATION.json"
    baseline_resume_path = args.reports.parent / "RESUME_BASELINE_AUDIT_VALIDATION.json"
    resume_check, baseline_resume = read_json(resume_path), read_json(baseline_resume_path)
    need(resume_check["every_expected_context_verified"] is True and
         resume_check["strict_current_contexts_verified"] == resume["expected_current_contexts"] and
         baseline_resume["baseline_audit_reused_and_revalidated"] is True and
         baseline_resume["baseline_signature_count"] == resume["baseline_signature_count"] and
         all(x["candidate_plan_sha256"] == digest(args.plan) and
             x["resume_record_sha256"] == plan["resume_record"]["sha256"] and
             x["source_manifest_sha256"] == inv["sha256"] for x in [resume_check, baseline_resume]),
         "Incomplete exact-current resume or baseline-audit validation")
    need(all(context_hash(native["records"][m]) == h for m, h in resume["expected_current_contexts"].items()),
         "A restored current context changed in the final native graph")
    stages = {name: read_json(args.reports / (name + ".json")) for name in preflight["stages"]}
    need(all(r["resume_validation_sha256"] == digest(resume_path) for r in stages.values()),
         "A native stage used a different resume validation")
    check_completed_stages(preflight, stages, native, digest(args.plan), digest(args.baseline))
    new_inputs = publication_inputs(args.root, plan, inv)
    old = load_verified_audit(args.baseline_audit, args.baseline_root, old_native, config, baseline,
                              audit_spec(baseline, "baseline"))
    current = load_verified_audit(args.current_audit, args.root, native, config, baseline,
                                  audit_spec(baseline, "current", change, new_inputs))
    boundaries = reconcile(baseline, change, old, current, native, new_inputs, inv)
    need(boundaries["original_root_accounting_count"] ==
         len(baseline["point1_roots"]) + len(baseline["new_roots"]) and
         boundaries["all_current_root_boundaries_verified"] is True, "Incomplete original-root boundary gate")
    out = {"schema": "lebrun-continuation-full-verification-v1", "git_binding": binding,
           "source_modules": len(inv["sources"]), "complete_source_manifest": inv["text"],
           "source_manifest_sha256": inv["sha256"], "native": native, "impact": change,
           "baseline_context_comparison": comparison, "boundaries": boundaries,
           "baseline_accepted_commit": baseline["accepted_commit"],
           "historical_point1_report_sha256": baseline["verification_sha256"],
           "historical_point1_artifact": baseline["artifact"],
           "historical_point1_all190_unchanged_claim_modified": False,
           "baseline_record_sha256": digest(args.baseline), "candidate_plan_sha256": digest(args.plan),
           "preflight_sha256": digest(args.preflight),
           "resume_validation_sha256": digest(resume_path),
           "baseline_audit_resume_validation_sha256": digest(baseline_resume_path),
           "resume_record_sha256": plan["resume_record"]["sha256"],
           "resumed_current_context_count": len(resume["expected_current_contexts"]),
           "resume_official_artifact": resume["official_artifact"],
           "stage_report_sha256": {name: digest(args.reports / (name + ".json")) for name in stages},
           "all_current_sources_kernel_checked": True, "all_relevant_boundaries_checked": True,
           "current_native_evidence_ready_for_acceptance_review": True,
           "official_current_artifact_metadata_verification_still_required": True,
           "new_native_publication_type_review_still_required": sorted(new_inputs),
           "accepted_units_unchanged": baseline["accepted_units"], "denominator": baseline["denominator"],
           "new_units_credited": 0, "helper_units_credited": 0, "acceptance_ledger_modified": False,
           "milestone_met": False, "github_run_id": os.environ.get("GITHUB_RUN_ID"),
           "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT")}
    write_json(args.output, out)
    print("CONTINUATION_CURRENT_NATIVE_AND_BOUNDARY_GATE_PASSED", out["source_modules"],
          boundaries["original_root_accounting_count"], args.commit)


if __name__ == "__main__":
    main()

