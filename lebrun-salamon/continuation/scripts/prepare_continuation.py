#!/usr/bin/env python3
"""Materialize the immutable accepted source and validate an approved continuation."""
from __future__ import annotations
import argparse
import subprocess
from pathlib import Path
from continuation_support import (candidate_plan, closure, context_hash, digest,
    git_binding, need, read_json, safe_relative, source_inventory,
    verify_native_build, write_json)


def materialize(baseline, destination):
    destination = Path(destination)
    need(not destination.exists() or not any(destination.iterdir()), "Baseline directory is not empty")
    prefix = baseline["continuation_prefix"]
    names = list(source_inventory_names(baseline)) + [
        "SOURCE.sha256", "TOOLCHAIN.lock.json", "target/MainStatement.lean"]
    for name in names:
        path = destination / safe_relative(name)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(subprocess.check_output(
            ["git", "show", baseline["compiled_commit"] + ":" + prefix + "/" + name]))
    return git_binding(destination, baseline["compiled_commit"], prefix)


def source_inventory_names(baseline):
    return [line[66:] for line in baseline["source_manifest"].splitlines()]


def verify_baseline(root, artifact, config, baseline):
    artifact = Path(artifact)
    build = artifact / "kernel-evidence"
    report = build / "FULL_REPLAY_VERIFICATION.json"
    need(digest(report) == baseline["verification_sha256"], "Historical full report bytes differ")
    historic = read_json(report)
    need(historic["commit"] == baseline["compiled_commit"] and
         historic["source_manifest_sha256"] == baseline["source_manifest_sha256"] and
         historic["all_current_sources_kernel_checked"] is True,
         "Historical report is not the accepted snapshot")
    stage = verify_native_build(root, build, config, baseline)
    need(stage["whole_current_graph_passed"] and
         set(stage["records"]) == set(baseline["native_contexts"]), "Incomplete accepted native archive")
    for module, record in stage["records"].items():
        need(context_hash(record) == baseline["native_contexts"][module],
             "Accepted native context differs: " + module)
    return {"schema": "lebrun-continuation-baseline-validation-v1",
            "compiled_commit": baseline["compiled_commit"], "accepted_commit": baseline["accepted_commit"],
            "official_artifact": baseline["artifact"], "historical_report_sha256": digest(report),
            "all_accepted_native_contexts_verified": True, "native": stage}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--baseline-root", type=Path, required=True)
    ap.add_argument("--baseline", type=Path, required=True)
    ap.add_argument("--plan", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--materialize", action="store_true")
    ap.add_argument("--artifact-dir", type=Path)
    ap.add_argument("--artifact-metadata", type=Path)
    ap.add_argument("--runtime-config", type=Path)
    args = ap.parse_args()
    baseline, plan = read_json(args.baseline), read_json(args.plan)
    if args.materialize:
        materialize(baseline, args.baseline_root)
    current_commit = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    base_binding = git_binding(args.baseline_root, baseline["compiled_commit"], baseline["continuation_prefix"])
    current_binding = git_binding(args.root, current_commit, baseline["continuation_prefix"])
    _, cur, change = candidate_plan(args.root, args.baseline_root, baseline, plan)
    root_modules = sorted({r["module"] for r in baseline["point1_roots"] + baseline["new_roots"]})
    stages = {
        "part07_parents": sorted(set(cur["graph"]["RecompileBasePart07"])),
        "part07": ["RecompileBasePart07"],
        "core": ["RecompileExtensionsPart02"],
        "accepted_boundaries": root_modules,
        "full": sorted(cur["sources"]),
    }
    out = {"schema": "lebrun-continuation-preflight-v1", "baseline": base_binding,
           "candidate": current_binding, "plan_sha256": digest(args.plan),
           "baseline_record_sha256": digest(args.baseline), "impact": change,
           "stages": {k: {"targets": targets,
                         "selected": sorted(closure(cur["graph"], targets)),
                         "module_timeout_seconds": 600 if k == "part07" else 300}
                      for k, targets in stages.items()},
           "counts_recomputed_from_current_graph": True,
           "accepted_units_unchanged": baseline["accepted_units"],
           "denominator": baseline["denominator"], "acceptance_ledger_modified": False}
    if args.artifact_dir:
        need(args.runtime_config is not None, "Runtime config required for native baseline validation")
        need(args.artifact_metadata is not None, "Official accepted artifact metadata required")
        meta = read_json(args.artifact_metadata)
        expected = baseline["artifact"]
        need(meta["id"] == expected["id"] and meta["name"] == expected["name"] and
             meta["workflow_run"]["id"] == expected["run_id"] and not meta["expired"] and
             meta["digest"] == "sha256:" + expected["sha256"] and
             meta["size_in_bytes"] == expected["size_in_bytes"], "Official baseline artifact metadata differs")
        out["baseline_native"] = verify_baseline(args.baseline_root, args.artifact_dir,
                                                read_json(args.runtime_config), baseline)
        out["baseline_native"]["official_metadata_sha256"] = digest(args.artifact_metadata)
        out["baseline_native"]["transport_note"] = "Extracted by official download action; all accepted native contents independently checked. ZIP digest was independently verified at historical acceptance; this step checks its exact official metadata."
    write_json(args.output, out)
    print("CONTINUATION_PREFLIGHT", out["candidate"]["commit"],
          len(cur["sources"]), len(change["baseline_contexts_to_preserve"]),
          len(change["baseline_contexts_to_replace"]))


if __name__ == "__main__":
    main()

