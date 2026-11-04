#!/usr/bin/env python3
"""Revalidate exact official resume data using unchanged native/cache validators."""
import argparse
import shutil
from pathlib import Path
from continuation_support import (candidate_plan, context_hash, digest, module_path, need,
    read_json, runtime_context, source_ancestry_fingerprint, source_inventory, verify_native_build, write_json)
from continuation_stage_policy import load_resume
from restore_replay_cache import validated_unselected_cache, unselected_binding_errors
from run_continuation_audit import audit_spec
from verify_continuation_boundaries import load_verified_audit


def check_artifact_and_source(resume, metadata, inv):
    expected = resume["official_artifact"]
    need(all(metadata.get(k) == expected[k] for k in
             ("id", "name", "size_in_bytes", "digest", "workflow_run")) and
         metadata.get("expired") is False, "Resume official artifact metadata differs")
    need(metadata["workflow_run"]["head_sha"] == resume["source_commit"] and
         metadata["workflow_run"]["head_branch"] == "codex/lebrun-3h-native-20261104" and
         inv["sha256"] == resume["source_manifest_sha256"] and
         len(inv["sources"]) == resume["source_modules"], "Resume commit, branch or source differs")


def check_runtime(identity, fingerprint, baseline):
    need(fingerprint == baseline["runtime_fingerprint"] and
         identity["config"]["flags"] == baseline["runtime_flags"] and
         identity["config"]["compiler_kind"] == "stock_pinned_frontend" and
         identity["config"]["mathlib_revision"] == baseline["mathlib_revision"] and
         identity["toolchain_lock_sha256"] == baseline["lock_sha256"], "Resume runtime identity or flags differ")


def check_contexts(records, resume):
    actual = {m: context_hash(r) for m, r in records.items()}
    need(actual == resume["expected_current_contexts"] and
         not (set(records) & set(resume["failed_modules_excluded"])), "Restored resume contexts are missing, stale or ineligible")
    return actual


def restored_records(root, build, config, baseline, resume):
    inv = source_inventory(root)
    identity, fingerprint = runtime_context(root, config)
    check_runtime(identity, fingerprint, baseline)
    summary_path = build / "CACHE_RESTORE.json"
    summary = read_json(summary_path)
    cached, rejection = validated_unselected_cache(summary, fingerprint)
    need(rejection is None and set(cached) == set(resume["expected_current_contexts"]),
         "Strict restored union does not contain every exact resume context")
    external_roots = [Path(p) for p in config["external_olean_roots"]]
    records = {}
    for module in inv["order"]:
        if module not in cached:
            continue
        path = build / "receipts" / (module + ".json")
        receipt = read_json(path)
        need(not unselected_binding_errors(cached[module], receipt), "Restored union binding differs")
        need(receipt["schema"] == "lebrun-module-receipt-v1" and receipt["module"] == module and
             receipt["status"] == "passed" and receipt["return_code"] == 0 and
             receipt["evidence_kind"] == "native_kernel_compilation", "Resume receipt is not a native pass")
        deps = {}
        for dep in inv["imports"][module]:
            if dep in inv["sources"]:
                need(dep in records, "Resume project ancestor is not verified")
                deps[dep] = {"kind": "project", "sha256": records[dep]["output_sha256"]}
            else:
                rel = module_path(dep).with_suffix(".olean")
                p = next((r / rel for r in external_roots if (r / rel).is_file()), None)
                need(p is not None, "Resume external import is missing")
                deps[dep] = {"kind": "external", "sha256": digest(p)}
        key = {"source_sha256": digest(inv["sources"][module]), "imports": inv["imports"][module],
               "dependency_artifacts": deps, "runtime_fingerprint": fingerprint, "flags": config["flags"]}
        need(receipt["key"] == key, "Resume source, dependency or native runtime key differs")
        stamp = source_ancestry_fingerprint(module, key,
            {d: records[d]["source_ancestry_fingerprint"] for d in inv["graph"][module]})
        need(receipt["source_ancestry_fingerprint"] == stamp, "Resume recursive context differs")
        for stream in ("stdout", "stderr"):
            p = build / "logs" / Path(receipt[stream]).name
            need(p.is_file() and digest(p) == receipt[stream + "_sha256"], "Resume raw log differs")
        output = build / "olean" / module_path(module).with_suffix(".olean")
        need(output.is_file() and digest(output) == receipt["output_sha256"], "Resume output differs")
        records[module] = {"key": key, "output_sha256": receipt["output_sha256"],
            "stdout_sha256": receipt["stdout_sha256"], "stderr_sha256": receipt["stderr_sha256"],
            "source_ancestry_fingerprint": stamp}
    contexts = check_contexts(records, resume)
    need(source_inventory(root)["sha256"] == inv["sha256"] and
         runtime_context(root, config) == (identity, fingerprint), "Resume inputs changed during validation")
    return contexts, digest(summary_path)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ("root", "baseline-root", "baseline-build", "baseline", "plan", "runtime-config",
                 "artifact-dir", "artifact-metadata", "output"):
        ap.add_argument("--" + name, type=Path, required=True)
    ap.add_argument("--phase", choices=["baseline-audit", "cache"], required=True)
    ap.add_argument("--baseline-audit-output", type=Path)
    ap.add_argument("--build-dir", type=Path)
    args = ap.parse_args()
    baseline, plan, config = read_json(args.baseline), read_json(args.plan), read_json(args.runtime_config)
    _, inv, _ = candidate_plan(args.root, args.baseline_root, baseline, plan)
    resume = load_resume(args.root, plan, inv)
    metadata = read_json(args.artifact_metadata)
    check_artifact_and_source(resume, metadata, inv)
    identity, fingerprint = runtime_context(args.root, config)
    check_runtime(identity, fingerprint, baseline)
    result = {"schema": "lebrun-continuation-resume-validation-v1", "phase": args.phase,
        "source_manifest_sha256": inv["sha256"], "candidate_plan_sha256": digest(args.plan),
        "resume_record_sha256": plan["resume_record"]["sha256"],
        "official_artifact_metadata_sha256": digest(args.artifact_metadata),
        "official_artifact": metadata, "native_runtime_fingerprint": fingerprint,
        "native_runtime_keys_rewritten": False, "compiler_invoked": False,
        "accepted_units_unchanged": 74, "new_units_credited": 0}
    if args.phase == "baseline-audit":
        need(args.baseline_audit_output is not None and not args.baseline_audit_output.exists(),
             "Baseline audit destination must be fresh")
        audit = args.artifact_dir / "continuation-evidence/baseline-audit"
        need(digest(audit / "AUDIT_RECEIPT.json") == resume["baseline_audit_receipt_sha256"],
             "Wrong original baseline native type capture")
        old_native = verify_native_build(args.baseline_root, args.baseline_build, config, baseline)
        need(old_native["whole_current_graph_passed"] and
             {m: context_hash(r) for m, r in old_native["records"].items()} == baseline["native_contexts"],
             "Original baseline context differs")
        parsed = load_verified_audit(audit, args.baseline_root, old_native, config, baseline,
                                     audit_spec(baseline, "baseline"))
        need(len(parsed["signatures"]) == resume["baseline_signature_count"], "Baseline type count differs")
        shutil.copytree(audit, args.baseline_audit_output)
        need({str(p.relative_to(audit)): digest(p) for p in audit.rglob('*') if p.is_file()} ==
             {str(p.relative_to(args.baseline_audit_output)): digest(p)
              for p in args.baseline_audit_output.rglob('*') if p.is_file()}, "Copied baseline audit differs")
        result.update({"baseline_audit_reused_and_revalidated": True,
                       "baseline_signature_count": len(parsed["signatures"]),
                       "baseline_signature_evidence": parsed["evidence"]})
    else:
        need(args.build_dir is not None, "Restored build is required")
        contexts, union_hash = restored_records(args.root, args.build_dir, config, baseline, resume)
        result.update({"strict_current_contexts_verified": contexts,
                       "strict_current_context_count": len(contexts),
                       "cache_restore_sha256": union_hash, "failed_modules_excluded": resume["failed_modules_excluded"],
                       "every_expected_context_verified": True})
    write_json(args.output, result)
    print("CONTINUATION_RESUME_VALIDATED", args.phase, inv["sha256"], len(resume["expected_current_contexts"]))


if __name__ == "__main__":
    main()
