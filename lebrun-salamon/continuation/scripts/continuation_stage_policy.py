#!/usr/bin/env python3
"""Reviewed wall-time exceptions and exact current stage order; no Lean flags change."""
from continuation_support import closure, digest, need, read_json, safe_relative

STAGE_ORDER = ["part07_parents", "part07", "core", "geometry_parents", "geometry",
               "accepted_boundaries", "smooth_descent_parents", "smooth_descent", "full"]
ISOLATED = {"part07": "RecompileBasePart07",
            "geometry": "RecompileExtensionsPart04Geometry",
            "smooth_descent": "LSFamilySmoothDescent"}


def build_stages(inv, baseline):
    targets = {
        "part07_parents": sorted(inv["graph"]["RecompileBasePart07"]),
        "part07": ["RecompileBasePart07"],
        "core": ["RecompileExtensionsPart02"],
        "geometry_parents": sorted(inv["graph"]["RecompileExtensionsPart04Geometry"]),
        "geometry": ["RecompileExtensionsPart04Geometry"],
        "accepted_boundaries": sorted({r["module"] for r in baseline["point1_roots"] + baseline["new_roots"]}),
        "smooth_descent_parents": sorted(inv["graph"]["LSFamilySmoothDescent"]),
        "smooth_descent": ["LSFamilySmoothDescent"],
        "full": sorted(inv["sources"]),
    }
    return {name: {"targets": targets[name], "selected": sorted(closure(inv["graph"], targets[name])),
                   "module_timeout_seconds": 600 if name in ISOLATED else 300}
            for name in STAGE_ORDER}


def validate_stages(preflight, inv, baseline):
    need(preflight.get("stage_order") == STAGE_ORDER and
         preflight.get("stages") == build_stages(inv, baseline),
         "Stage sequence, targets, closure or approved timeout differs")


def load_resume(root, plan, inv):
    binding = plan.get("resume_record")
    need(isinstance(binding, dict) and set(binding) == {"path", "sha256"}, "Missing exact resume binding")
    path = root / safe_relative(binding["path"])
    need(digest(path) == binding["sha256"], "Resume record changed")
    resume = read_json(path)
    need(resume["schema"] == "lebrun-continuation-resume-plan-v1" and
         resume["source_manifest_sha256"] == inv["sha256"] and
         resume["source_modules"] == len(inv["sources"]), "Resume sources differ")
    need(set(resume["walltime_only_exceptions"]) == set(ISOLATED.values()) and
         all(x["seconds"] == 600 for x in resume["walltime_only_exceptions"].values()) and
         resume["all_other_module_timeouts_seconds"] == 300 and
         resume["all_runtime_flags_and_identity_unchanged"] is True,
         "Unapproved wall-time exception or changed runtime policy")
    need(resume["expected_context_count"] == len(resume["expected_current_contexts"]) and
         not (set(resume["failed_modules_excluded"]) & set(resume["expected_current_contexts"])) and
         resume["failed_modules_excluded"] == ["RecompileExtensionsPart04Geometry"] and
         resume["new_units_credited"] == 0 and resume["accepted_units_unchanged"] == 74,
         "Invalid resume context or accounting scope")
    evidence = resume["independent_verification"]
    record_path = root / safe_relative(evidence["path"])
    need(digest(record_path) == evidence["sha256"], "Independent resume evidence changed")
    record = read_json(record_path)
    from continuation_support import context_hash
    records = {**record["selected_pass_records"], **record["unselected_cache_records"]}
    need(resume["official_artifact"] == record["official_artifact"] and
         resume["source_commit"] == record["commit"] and resume["source_tree"] == record["tree"] and
         resume["source_manifest_sha256"] == record["source_manifest_sha256"] and
         resume["expected_current_contexts"] == {m: context_hash(r) for m, r in records.items()} and
         record["all_included_current_source_output_receipt_log_runtime_dependency_recursive_hashes_verified"] is True and
         record["explicit_failed_or_blocked_status_overridden"] is False,
         "Resume does not match independently verified native contexts")
    return resume


def check_predecessors(stage, reports, plan_sha, baseline_sha, source_sha):
    expected = STAGE_ORDER[:STAGE_ORDER.index(stage)]
    hashes = {}
    for name in expected:
        path = reports / (name + ".json")
        need(path.is_file(), "Required predecessor stage is missing: " + name)
        report = read_json(path)
        need(report["stage"] == name and report["return_code"] == 0 and
             report["full_selected_graph_passed"] is True and not report["errors"] and
             report["candidate_plan_sha256"] == plan_sha and
             report["baseline_record_sha256"] == baseline_sha and
             report["source_manifest_sha256"] == source_sha,
             "Predecessor stage failed or belongs to another current candidate")
        need(report.get("completed_predecessor_report_sha256") == hashes,
             "Predecessor sequence or report hashes differ")
        hashes[name] = digest(path)
    return hashes
