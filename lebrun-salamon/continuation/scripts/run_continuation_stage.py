#!/usr/bin/env python3
"""Execute one bounded continuation stage using the unchanged native replay driver."""
from __future__ import annotations
import argparse
import json
import os
import subprocess
import sys
from pathlib import Path
from continuation_support import (candidate_plan, closure, digest, need, read_json,
    verify_native_build, write_json)
from report_continuation_stage import make_report
from continuation_stage_policy import (STAGE_ORDER, ISOLATED, validate_stages,
                                       load_resume, check_predecessors)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ("root", "baseline-root", "baseline", "plan", "preflight", "runtime-config", "build-dir", "reports"):
        ap.add_argument("--" + key, type=Path, required=True)
    ap.add_argument("--stage", required=True,
                    choices=STAGE_ORDER)
    args = ap.parse_args()
    root = args.root.resolve()
    baseline, plan, config = read_json(args.baseline), read_json(args.plan), read_json(args.runtime_config)
    _, inv, change = candidate_plan(root, args.baseline_root, baseline, plan)
    preflight = read_json(args.preflight)
    need(preflight["plan_sha256"] == digest(args.plan) and
         preflight["baseline_record_sha256"] == digest(args.baseline) and
         preflight["candidate"]["source_manifest_sha256"] == inv["sha256"],
         "Stage does not match approved preflight")
    validate_stages(preflight, inv, baseline)
    resume = load_resume(root, plan, inv)
    predecessors = check_predecessors(args.stage, args.reports, digest(args.plan),
                                     digest(args.baseline), inv["sha256"])
    resume_validation_path = args.reports.parent / "RESUME_CACHE_VALIDATION.json"
    resume_validation = read_json(resume_validation_path)
    need(resume_validation["candidate_plan_sha256"] == digest(args.plan) and
         resume_validation["resume_record_sha256"] == plan["resume_record"]["sha256"] and
         resume_validation["source_manifest_sha256"] == inv["sha256"] and
         resume_validation["every_expected_context_verified"] is True and
         resume_validation["strict_current_contexts_verified"] == resume["expected_current_contexts"],
         "Every strict current resume context must be validated before stages")
    spec = preflight["stages"][args.stage]
    need(set(spec["selected"]) == closure(inv["graph"], spec["targets"]), "Stale stage closure")
    allowed_timeout = 600 if args.stage in ISOLATED else 300
    need(spec["module_timeout_seconds"] == allowed_timeout, "Unauthorized module timeout")
    if args.stage in ISOLATED:
        isolated_module = ISOLATED[args.stage]
        # No other module can receive the longer compile allowance: all strict
        # ancestor receipts must already pass, and the replay must reuse them.
        prior = verify_native_build(root, args.build_dir, config, baseline)
        parents = closure(inv["graph"], inv["graph"][isolated_module])
        need(prior["full_selected_graph_passed"] and parents <= set(prior["records"]),
             "Isolated target current parents have not all been validated")
        need(spec["targets"] == [isolated_module], "The 600-second exception must select only its target")
    command = [sys.executable, str(root / "scripts/replay_checkpoint.py"),
               "--root", str(root), "--runtime-config", str(args.runtime_config.resolve()),
               "--build-dir", str(args.build_dir.resolve()), "--keep-going", "--timeout", str(allowed_timeout)]
    if args.stage != "full":
        for module in spec["targets"]:
            command += ["--module", module]
    rc = subprocess.run(command, check=False).returncode
    commit = os.environ.get("GITHUB_SHA") or subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
    report = make_report(root, args.baseline_root, args.build_dir, config, baseline, plan, commit, args.stage)
    report.update({"candidate_plan_sha256": digest(args.plan), "baseline_record_sha256": digest(args.baseline),
                   "preflight_sha256": digest(args.preflight), "command": command, "return_code": rc,
                   "module_timeout_seconds": allowed_timeout, "run_status_sha256":
                   digest(args.build_dir / "RUN_STATUS.json"), "github_run_id": os.environ.get("GITHUB_RUN_ID"),
                   "github_run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
                   "completed_predecessor_report_sha256": predecessors,
                   "resume_validation_sha256": digest(resume_validation_path)})
    if args.stage in ISOLATED:
        need(all(report["records"].get(m, {}).get("state") == "reused" for m in parents),
             "An ancestor unexpectedly rebuilt under the isolated longer timeout")
    need(all(report["records"][m]["state"] == "reused"
             for m in set(report["records"]) & set(resume["expected_current_contexts"])),
         "An exact preserved current context unexpectedly recompiled")
    args.reports.mkdir(parents=True, exist_ok=True)
    destination = args.reports / (args.stage + ".json")
    write_json(destination, report)
    for error in report["errors"]:
        print("NATIVE_DIAGNOSTIC " + json.dumps(error, ensure_ascii=False), flush=True)
    for module, record in report["records"].items():
        if record["state"] == "passed":
            print("NATIVE_RECEIPT " + json.dumps({"module": module, **record}, ensure_ascii=False), flush=True)
    print("CONTINUATION_NATIVE_STAGE " + json.dumps({k: report[k] for k in (
        "stage", "source_modules", "selected_modules", "accepted_modules", "status_counts",
        "full_selected_graph_passed", "whole_current_graph_passed", "fresh_native_passes_this_invocation",
        "native_receipts_reused_this_invocation")}), flush=True)
    need(rc == 0 and report["full_selected_graph_passed"], "Native stage failed or is incomplete")
    if args.stage == "full":
        need(report["whole_current_graph_passed"], "Not all current production sources passed")


if __name__ == "__main__":
    main()

