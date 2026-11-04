#!/usr/bin/env python3
"""Record a current continuation stage without rewriting historical Point1 evidence."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
from continuation_support import (candidate_plan, compare_contexts, context_hash, digest,
    git_binding, need, read_json, verify_native_build, write_json)


def make_report(root, baseline_root, build, config, baseline, plan, commit, stage_name):
    _, _, change = candidate_plan(root, baseline_root, baseline, plan)
    report = verify_native_build(root, build, config, baseline)
    report["git_binding"] = git_binding(root, commit, baseline["continuation_prefix"])
    report["stage"] = stage_name
    report["baseline_accepted_commit"] = baseline["accepted_commit"]
    report["baseline_compiled_commit"] = baseline["compiled_commit"]
    report["baseline_manifest_sha256"] = baseline["source_manifest_sha256"]
    report["impact"] = change
    report["baseline_context_comparison"] = compare_contexts(report, baseline, change)
    report["fresh_native_passes_this_invocation"] = report["status_counts"].get("passed", 0)
    report["native_receipts_reused_this_invocation"] = report["status_counts"].get("reused", 0)
    report["accepted_units_unchanged"] = baseline["accepted_units"]
    report["denominator"] = baseline["denominator"]
    report["milestone_met"] = False
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--baseline-root", type=Path, required=True)
    ap.add_argument("--baseline", type=Path, required=True)
    ap.add_argument("--plan", type=Path, required=True)
    ap.add_argument("--runtime-config", type=Path, required=True)
    ap.add_argument("--build-dir", type=Path, required=True)
    ap.add_argument("--stage", required=True)
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--commit", default=os.environ.get("GITHUB_SHA"))
    ap.add_argument("--require-pass", action="store_true")
    ap.add_argument("--require-whole-graph", action="store_true")
    args = ap.parse_args()
    need(args.commit, "Exact candidate commit required")
    report = make_report(args.root, args.baseline_root, args.build_dir, read_json(args.runtime_config),
                         read_json(args.baseline), read_json(args.plan), args.commit, args.stage)
    report.update({"baseline_record_sha256": digest(args.baseline),
                   "candidate_plan_sha256": digest(args.plan),
                   "run_status_sha256": digest(args.build_dir / "RUN_STATUS.json"),
                   "github_run_id": os.environ.get("GITHUB_RUN_ID"),
                   "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT")})
    write_json(args.output, report)
    for error in report["errors"]:
        print("NATIVE_DIAGNOSTIC " + json.dumps(error, ensure_ascii=False), flush=True)
    for name, rec in report["records"].items():
        if rec["state"] == "passed":
            print("NATIVE_RECEIPT " + json.dumps({"module": name, **rec}, ensure_ascii=False), flush=True)
    print("CONTINUATION_NATIVE_STAGE " + json.dumps({k: report[k] for k in (
        "stage", "source_modules", "selected_modules", "accepted_modules", "status_counts",
        "source_manifest_sha256", "full_selected_graph_passed", "whole_current_graph_passed",
        "fresh_native_passes_this_invocation", "native_receipts_reused_this_invocation")}))
    if args.require_pass:
        need(report["full_selected_graph_passed"], "Native selected stage failed or is incomplete")
    if args.require_whole_graph:
        need(report["whole_current_graph_passed"], "Whole current source graph is not accepted")


if __name__ == "__main__":
    main()

