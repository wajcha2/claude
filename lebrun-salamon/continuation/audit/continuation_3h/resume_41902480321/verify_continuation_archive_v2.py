#!/usr/bin/env python3
"""Independent, read-only verification of an official continuation artifact.

No compiler is invoked, no receipt or native runtime key is rewritten, and no
acceptance ledger is changed. The old Point1 all190 equality gate is untouched.
The native runtime identity is checked against the exact accepted official
artifact, and its pinned bytes are additionally checked in a relocated runtime.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import sys
import zipfile
from pathlib import Path

NATIVE_PREFIX = "/home/runner/work/_temp/lebrun-runtime/"
HELPER_MODULE = "Lean.Util.CollectAxioms"


def H(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def need(ok, message):
    if not ok:
        raise ValueError(message)


def native_hash(value):
    return H(json.dumps(value, sort_keys=True).encode())


def safe_extract(archive, destination):
    destination = Path(destination)
    need(not destination.exists() or
         (destination.is_dir() and not any(destination.iterdir())),
         "Official archive extraction requires a fresh empty directory")
    destination.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive) as z:
        names = z.namelist()
        need(len(names) == len(set(names)), "Duplicate ZIP member")
        for name in names:
            p = Path(name)
            need(not p.is_absolute() and ".." not in p.parts, "Unsafe ZIP member")
            need(not ((z.getinfo(name).external_attr >> 16) & 0o170000) == 0o120000,
                 "ZIP symlinks are forbidden")
        z.extractall(destination)


def official_zip(path, metadata, expected=None):
    meta = read(metadata) if not isinstance(metadata, dict) else metadata
    data = Path(path).read_bytes()
    need(meta["digest"] == "sha256:" + H(data) and meta["size_in_bytes"] == len(data),
         "Official ZIP size or digest mismatch")
    need(not meta["expired"], "Official artifact expired at metadata capture")
    if expected:
        need(meta["id"] == expected["id"] and meta["name"] == expected["name"] and
             meta["workflow_run"]["id"] == expected["run_id"] and
             H(data) == expected["sha256"], "Wrong accepted baseline artifact")
    return meta


def check_run_provenance(run, meta, commit):
    need(run["id"] == meta["workflow_run"]["id"] and
         run["head_sha"] == commit == meta["workflow_run"]["head_sha"] and
         run["status"] == "completed" and run["conclusion"] == "success" and
         run["event"] == "push" and
         run["path"] == ".github/workflows/lebrun-3h-continuation-native.yml" and
         run["head_branch"] == "codex/lebrun-3h-native-20261104" and
         meta["name"] == f"lebrun-3h-current-native-{run['id']}-{run['run_attempt']}",
         "Wrong or unsuccessful official workflow/run/artifact provenance")


class ArchivedNative:
    def __init__(self, baseline, identity, external_hashes, relocated_runtime):
        self.baseline = baseline
        self.identity = identity
        self.external_hashes = external_hashes
        self.relocated_runtime = Path(relocated_runtime)
        config = identity["config"]
        need(config["compiler_kind"] == "stock_pinned_frontend" and
             config["flags"] == baseline["runtime_flags"] and
             config["mathlib_revision"] == baseline["mathlib_revision"],
             "Native compiler, flags or mathlib identity differs")
        need(identity["toolchain_lock_sha256"] == baseline["lock_sha256"] and
             native_hash(identity) == baseline["runtime_fingerprint"],
             "Accepted runtime fingerprint differs")
        self.runtime_files = {}
        for name, expected in identity["fingerprint_files"].items():
            path = self.relocate(name)
            need(path.is_file() and digest(path) == expected,
                 "Pinned relocated runtime bytes differ: " + name)
            self.runtime_files[name] = expected
        self.external_roots = [self.relocate(p) for p in config["external_olean_roots"]]

    def relocate(self, name):
        need(name.startswith(NATIVE_PREFIX), "Unexpected native runtime path")
        relative = Path(name[len(NATIVE_PREFIX):])
        need(not relative.is_absolute() and ".." not in relative.parts,
             "Unsafe runtime relocation")
        return self.relocated_runtime / relative

    def external(self, module):
        need(module in self.external_hashes, "Unbound external module: " + module)
        relative = Path(*module.split(".")).with_suffix(".olean")
        path = next((p / relative for p in self.external_roots
                     if (p / relative).is_file()), None)
        expected = self.external_hashes[module]
        need(path is not None and digest(path) == expected,
             "Pinned external artifact differs: " + module)
        return {"kind": "external", "sha256": expected}

    def verify(self, root, build):
        root, build = Path(root), Path(build)
        inv = source_inventory(root)
        status = read(build / "RUN_STATUS.json")
        need(status["runtime"] == self.identity and
             status["runtime_fingerprint"] == self.baseline["runtime_fingerprint"],
             "Archived run uses another native runtime")
        need(digest(root / "target/MainStatement.lean") == self.baseline["target_sha256"] and
             digest(root / "TOOLCHAIN.lock.json") == self.baseline["lock_sha256"],
             "Frozen target or lock differs")
        need(not status["final_validation"]["invalidated_modules"] and
             not status["final_validation"]["changed_runtime_files"],
             "Native final validation invalidated inputs")
        selected = set(status["selected_modules"])
        need(len(selected) == len(status["selected_modules"]) and
             selected <= set(inv["sources"]) and set(status["modules"]) == selected,
             "Incomplete native status or selection")
        need(all(set(inv["graph"][m]) <= selected for m in selected),
             "Native selection lacks an ancestor")
        records, errors = {}, []
        for module in inv["order"]:
            if module not in selected:
                continue
            state = status["modules"][module]
            if state["status"] == "blocked":
                errors.append({"module": module, "status": "blocked"})
                continue
            receipt_path = build / "receipts" / (module + ".json")
            receipt = read(receipt_path)
            deps = {}
            for dep in inv["imports"][module]:
                if dep in inv["sources"]:
                    need(dep in records, "Unverified project parent: " + module)
                    deps[dep] = {"kind": "project", "sha256": records[dep]["output_sha256"]}
                else:
                    deps[dep] = self.external(dep)
            key = {"source_sha256": digest(inv["sources"][module]),
                   "imports": inv["imports"][module],
                   "dependency_artifacts": deps,
                   "runtime_fingerprint": self.baseline["runtime_fingerprint"],
                   "flags": self.baseline["runtime_flags"]}
            need(receipt["key"] == key, "Complete native key differs: " + module)
            logs = {}
            for stream in ("stdout", "stderr"):
                log = build / "logs" / Path(receipt[stream]).name
                need(log.is_file() and digest(log) == receipt[stream + "_sha256"],
                     "Raw native log differs: " + module)
                logs[stream] = log
            if state["status"] not in ("passed", "reused"):
                errors.append({"module": module, "status": state["status"],
                               "return_code": receipt.get("return_code")})
                continue
            need(receipt["schema"] == "lebrun-module-receipt-v1" and
                 receipt["module"] == module and receipt["status"] == "passed" and
                 receipt["return_code"] == 0 and
                 receipt["evidence_kind"] == "native_kernel_compilation",
                 "Not a completed native receipt: " + module)
            for line in logs["stdout"].read_text().splitlines():
                try:
                    item = json.loads(line)
                except ValueError:
                    continue
                need(item.get("severity") != "error", "Successful receipt contains an error")
            output = build / "olean" / Path(*module.split(".")).with_suffix(".olean")
            need(output.is_file() and digest(output) == receipt["output_sha256"] ==
                 state["output_sha256"], "Native output differs: " + module)
            stamp = source_ancestry_fingerprint(module, key,
                {d: records[d]["source_ancestry_fingerprint"] for d in inv["graph"][module]})
            need(stamp == receipt["source_ancestry_fingerprint"],
                 "Recursive source/dependency ancestry differs: " + module)
            records[module] = {"module": module, "receipt_sha256": digest(receipt_path),
                "key": key, "output_sha256": receipt["output_sha256"],
                "source_ancestry_fingerprint": stamp, "stdout_sha256": receipt["stdout_sha256"],
                "stderr_sha256": receipt["stderr_sha256"], "seconds": receipt.get("seconds"),
                "state": state["status"]}
        need(len(records) == status["final_validation"]["checked_module_count"],
             "Native accepted count differs")
        counts = {}
        for state in status["modules"].values():
            counts[state["status"]] = counts.get(state["status"], 0) + 1
        return {"records": records, "errors": errors, "status_counts": counts,
                "selected": sorted(selected), "source_manifest_sha256": inv["sha256"],
                "full_selected_graph_passed": not errors and set(records) == selected,
                "whole_current_graph_passed": not errors and set(records) == set(inv["sources"])}


def check_git_bytes(root, binding, commit, tree):
    need(binding["commit"] == commit and binding["tree"] == tree, "Wrong immutable Git binding")
    inv = source_inventory(root)
    expected = set(inv["files"]) | {"SOURCE.sha256", "TOOLCHAIN.lock.json", "target/MainStatement.lean"}
    entries = binding["entries"]
    need(len(entries) == len(expected) and {x["path"] for x in entries} == expected,
         "Git source/target/lock/manifest membership differs")
    for item in entries:
        need(item["mode"] == "100644" and item["type"] == "blob", "Unexpected Git source kind")
        raw = (Path(root) / item["path"]).read_bytes()
        need(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == item["sha"],
             "Git source bytes differ: " + item["path"])


def check_auxiliary_git_bytes(root, binding, commit, tree):
    need(binding["commit"] == commit and binding["tree"] == tree,
         "Wrong auxiliary Git binding")
    entries = binding["auxiliary_entries"]
    paths = [x["path"] for x in entries]
    required = {"scripts/continuation_support.py", "scripts/check_checkpoint.py",
                "scripts/replay_checkpoint.py", "scripts/run_continuation_audit.py",
                "scripts/verify_continuation_boundaries.py",
                "scripts/finalize_continuation_evidence.py",
                "scripts/continuation_stage_policy.py", "scripts/verify_continuation_resume.py",
                "audit/continuation_3h/BASELINE.json", "audit/continuation_3h/CANDIDATE_PLAN.json"}
    need(len(paths) == len(set(paths)) and required <= set(paths),
         "Missing/duplicate auxiliary source binding")
    for item in entries:
        p = Path(item["path"])
        need(not p.is_absolute() and ".." not in p.parts and
             item["mode"] == "100644" and item["type"] == "blob", "Unsafe auxiliary Git entry")
        raw = (Path(root) / p).read_bytes()
        need(hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest() == item["sha"],
             "Reviewed auxiliary code/record changed: " + item["path"])


def check_audit(directory, production_root, production_native, verifier, spec):
    directory = Path(directory)
    receipt = read(directory / "AUDIT_RECEIPT.json")
    inv = source_inventory(production_root)
    module = "LSContinuationBaselineSignatures" if spec["mode"] == "baseline" else "LSContinuationCurrentBoundaries"
    need(receipt["mode"] == spec["mode"] and receipt["spec"] == spec and
         receipt["audit_module"] == module and receipt["production_manifest_sha256"] == inv["sha256"],
         "Audit mode, spec or production source differs")
    text = generate_audit(spec, inv["sources"])
    snapshot = directory / "snapshot"
    need((snapshot / "source" / (module + ".lean")).read_text() == text and
         receipt["audit_source_sha256"] == sha_text(text), "Generated audit code differs")
    snapshot_inv = source_inventory(snapshot)
    need(snapshot_inv["files"] == {**inv["files"], "source/" + module + ".lean": sha_text(text)} and
         snapshot_inv["sha256"] == receipt["audit_snapshot_manifest_sha256"],
         "Audit copied sources differ")
    native = verifier.verify(snapshot, directory / "kernel-evidence")
    need(native["full_selected_graph_passed"] and receipt["return_code"] == 0 and
         native["records"] == receipt["native"]["records"] and
         receipt["only_audit_module_compiled"] is True and
         receipt["production_build_unchanged"] is True and
         receipt["production_module_count_excludes_audit"] == len(inv["sources"]),
         "Audit is not a complete independent native pass")
    contexts = {m: context_hash(r) for m, r in native["records"].items() if m != module}
    need(contexts == receipt["production_native_contexts"] and
         native["status_counts"].get("passed") == 1 and
         native["records"][module]["state"] == "passed", "Audit fresh/reuse scope differs")
    need(set(contexts) == closure(inv["graph"], spec["imports"]), "Audit parent closure differs")
    for m, h in contexts.items():
        need(m in production_native["records"] and
             context_hash(production_native["records"][m]) == h and
             native["records"][m]["state"] == "reused", "Audit parent has another current context")
    raw_receipt = directory / "kernel-evidence" / "receipts" / (module + ".json")
    need(digest(raw_receipt) == receipt["audit_receipt_sha256"], "Audit native receipt changed")
    for stream in ("stdout", "stderr"):
        path = directory / receipt[stream + "_relative"]
        need(path.resolve().is_relative_to(directory.resolve()) and
             digest(path) == receipt[stream + "_sha256"] ==
             native["records"][module][stream + "_sha256"], "Audit log binding differs")
    parsed = parse_audit((directory / receipt["stdout_relative"]).read_text(), spec)
    parsed["evidence"] = {"receipt_sha256": digest(directory / "AUDIT_RECEIPT.json"),
        "native_receipt_sha256": digest(raw_receipt), "source_sha256": sha_text(text),
        "stdout_sha256": receipt["stdout_sha256"],
        "native_output_sha256": native["records"][module]["output_sha256"],
        "production_native_contexts": contexts}
    return parsed


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("input", type=Path)
    args = ap.parse_args()
    p = read(args.input)
    root, old_root = Path(p["current_root"]), Path(p["baseline_root"])
    git = read(p["git_binding"])
    check_auxiliary_git_bytes(root, git, p["commit"], p["tree"])
    sys.path.insert(0, str(root / "scripts"))
    global digest, source_inventory, candidate_plan, publication_inputs, context_hash, closure
    global source_ancestry_fingerprint, compare_contexts, audit_spec, generate_audit, parse_audit, reconcile, sha_text
    from continuation_support import (digest, source_inventory, candidate_plan, publication_inputs,
        context_hash, closure, source_ancestry_fingerprint, compare_contexts, sha_text)
    from run_continuation_audit import audit_spec, generate_audit
    from verify_continuation_boundaries import parse_audit, reconcile
    from finalize_continuation_evidence import check_completed_stages
    from continuation_stage_policy import validate_stages, load_resume
    baseline_path = root / "audit/continuation_3h/BASELINE.json"
    plan_path = root / "audit/continuation_3h/CANDIDATE_PLAN.json"
    baseline, plan = read(baseline_path), read(plan_path)
    need(digest(plan_path) == p["expected_plan_sha256"] and
         digest(baseline_path) == p["expected_baseline_sha256"], "Candidate plan/baseline changed")
    old_inv, inv, change = candidate_plan(root, old_root, baseline, plan)
    need(inv["sha256"] == p["expected_source_manifest_sha256"], "Wrong current source manifest")
    check_git_bytes(root, git, p["commit"], p["tree"])
    base_meta = official_zip(p["baseline_zip"], p["baseline_metadata"], baseline["artifact"])
    current_meta = official_zip(p["current_zip"], p["current_metadata"])
    run = read(p["run_metadata"])
    check_run_provenance(run, current_meta, p["commit"])
    base_dir, cur_dir = Path(p["output"]) / "accepted-artifact", Path(p["output"]) / "current-artifact"
    safe_extract(p["baseline_zip"], base_dir)
    safe_extract(p["current_zip"], cur_dir)
    historical = base_dir / "kernel-evidence/FULL_REPLAY_VERIFICATION.json"
    need(digest(historical) == baseline["verification_sha256"], "Accepted historical report differs")
    base_status = read(base_dir / "kernel-evidence/RUN_STATUS.json")
    external = {}
    for receipt_path in (base_dir / "kernel-evidence/receipts").glob("*.json"):
        for name, binding in read(receipt_path)["key"]["dependency_artifacts"].items():
            if binding["kind"] == "external":
                need(name not in external or external[name] == binding["sha256"], "Conflicting accepted external import")
                external[name] = binding["sha256"]
    supplement = read(p["pinned_audit_external"])
    lock = read(root / "TOOLCHAIN.lock.json")
    need(supplement["module"] == HELPER_MODULE and
         supplement["archive_sha256"] == lock["lean_linux_release_sha256"] and
         supplement["sha256"] == "60556ab5263a908aa74a5e65620b5e957cac3846aa6e4f05414434b8c12ea7de",
         "Unbound native audit library")
    external[HELPER_MODULE] = supplement["sha256"]
    verifier = ArchivedNative(baseline, base_status["runtime"], external, p["relocated_runtime"])
    old_native = verifier.verify(old_root, base_dir / "kernel-evidence")
    need(old_native["whole_current_graph_passed"] and
         set(old_native["records"]) == set(baseline["native_contexts"]), "Incomplete accepted graph")
    for m, record in old_native["records"].items():
        need(context_hash(record) == baseline["native_contexts"][m], "Accepted native context differs: " + m)
    native = verifier.verify(root, cur_dir / "kernel-evidence")
    need(native["whole_current_graph_passed"], "Current graph did not completely pass")
    comparison = compare_contexts(native, baseline, change)
    need(not comparison["pending_current_modules"], "Unvalidated affected context")
    report_path = cur_dir / "continuation-evidence/FULL_CONTINUATION_VERIFICATION.json"
    report = read(report_path)
    binding = {"commit": p["commit"], "tree": p["tree"], "source_manifest_sha256": inv["sha256"],
               "all_source_target_lock_manifest_git_blobs_verified": True}
    need(report["git_binding"] == binding and report["source_modules"] == len(inv["sources"]) and
         report["complete_source_manifest"] == inv["text"] and
         report["source_manifest_sha256"] == inv["sha256"] and
         report["all_current_sources_kernel_checked"] is True and
         report["all_relevant_boundaries_checked"] is True and
         report["current_native_evidence_ready_for_acceptance_review"] is True,
         "Full report is incomplete or unbound")
    need(report["native"]["records"] == native["records"] and
         report["native"]["whole_current_graph_passed"] is True and not report["native"]["errors"],
         "Full report native receipt inventory differs")
    preflight_path = cur_dir / "continuation-evidence/PREFLIGHT.json"
    preflight = read(preflight_path)
    need(preflight["candidate"] == binding and preflight["impact"] == change and
         preflight["plan_sha256"] == digest(plan_path) and
         preflight["baseline_record_sha256"] == digest(baseline_path), "Preflight binding differs")
    stages = {name: read(cur_dir / "continuation-evidence/stages" / (name + ".json"))
              for name in preflight["stages"]}
    validate_stages(preflight, inv, baseline)
    check_completed_stages(preflight, stages, native, digest(plan_path), digest(baseline_path))
    resume = load_resume(root, plan, inv)
    resume_check_path = cur_dir / "continuation-evidence/RESUME_CACHE_VALIDATION.json"
    baseline_resume_path = cur_dir / "continuation-evidence/RESUME_BASELINE_AUDIT_VALIDATION.json"
    resume_check, baseline_resume = read(resume_check_path), read(baseline_resume_path)
    need(resume_check["every_expected_context_verified"] is True and
         resume_check["strict_current_contexts_verified"] == resume["expected_current_contexts"] and
         resume_check["strict_current_context_count"] == len(resume["expected_current_contexts"]) and
         resume_check["failed_modules_excluded"] == resume["failed_modules_excluded"] and
         baseline_resume["baseline_audit_reused_and_revalidated"] is True and
         baseline_resume["baseline_signature_count"] == resume["baseline_signature_count"] and
         all(x["candidate_plan_sha256"] == digest(plan_path) and
             x["resume_record_sha256"] == plan["resume_record"]["sha256"] and
             x["source_manifest_sha256"] == inv["sha256"] and
             x["official_artifact"] == resume["official_artifact"] and
             x["native_runtime_fingerprint"] == baseline["runtime_fingerprint"] and
             x["native_runtime_keys_rewritten"] is False and x["compiler_invoked"] is False
             for x in (resume_check, baseline_resume)), "Resume validation scope or bindings differ")
    need(all(context_hash(native["records"][m]) == h for m, h in resume["expected_current_contexts"].items()),
         "A reused current context differs in the full native graph")
    need(report["resume_validation_sha256"] == digest(resume_check_path) and
         report["baseline_audit_resume_validation_sha256"] == digest(baseline_resume_path) and
         report["resume_record_sha256"] == plan["resume_record"]["sha256"] and
         report["resumed_current_context_count"] == len(resume["expected_current_contexts"]) and
         report["resume_official_artifact"] == resume["official_artifact"] and
         all(s["resume_validation_sha256"] == digest(resume_check_path) for s in stages.values()),
         "Final report or stages do not bind exact resume evidence")
    inputs = publication_inputs(root, plan, inv)
    old = check_audit(cur_dir / "continuation-evidence/baseline-audit", old_root, old_native,
                      verifier, audit_spec(baseline, "baseline"))
    need(old["evidence"] == baseline_resume["baseline_signature_evidence"] and
         digest(cur_dir / "continuation-evidence/baseline-audit/AUDIT_RECEIPT.json") ==
         resume["baseline_audit_receipt_sha256"], "Original native type capture was not preserved exactly")
    current = check_audit(cur_dir / "continuation-evidence/current-audit", root, native,
                          verifier, audit_spec(baseline, "current", change, inputs))
    boundaries = reconcile(baseline, change, old, current, native, inputs, inv)
    need(report["boundaries"] == boundaries and report["impact"] == change and
         report["baseline_context_comparison"] == comparison and
         boundaries["original_root_accounting_count"] == len(baseline["point1_roots"]) + len(baseline["new_roots"]),
         "Independent current boundaries differ from report")
    need(report["baseline_record_sha256"] == digest(baseline_path) and
         report["candidate_plan_sha256"] == digest(plan_path) and
         report["preflight_sha256"] == digest(preflight_path) and
         report["stage_report_sha256"] == {n: digest(cur_dir / "continuation-evidence/stages" / (n + ".json")) for n in stages},
         "Full report auxiliary evidence hashes differ")
    need(report["github_run_id"] == str(run["id"]) and
         report["github_run_attempt"] == str(run["run_attempt"]) and
         report["accepted_units_unchanged"] == 74 and report["new_units_credited"] == 0 and
         report["helper_units_credited"] == 0 and report["acceptance_ledger_modified"] is False and
         report["milestone_met"] is False, "Official run or accounting binding differs")
    result = {"schema": "lebrun-independent-continuation-archive-v1",
        "commit": p["commit"], "tree": p["tree"], "run_id": run["id"], "run_attempt": run["run_attempt"],
        "official_artifact": current_meta, "current_source_manifest_sha256": inv["sha256"],
        "candidate_plan_sha256": digest(plan_path), "baseline_record_sha256": digest(baseline_path),
        "strict_resumed_current_context_count": len(resume["expected_current_contexts"]),
        "resume_validation_sha256": digest(resume_check_path),
        "baseline_audit_resume_validation_sha256": digest(baseline_resume_path),
        "all_resumed_contexts_and_original_type_capture_preserved": True,
        "source_modules": len(inv["sources"]), "accepted_current_modules": len(native["records"]),
        "baseline_context_comparison": comparison, "original_root_accounting_count": len(boundaries["roots"]),
        "fresh_current_native_root_audits": boundaries["fresh_current_native_root_audits"],
        "preserved_historical_root_boundaries": boundaries["preserved_historical_root_boundaries"],
        "all_current_sources_and_relevant_boundaries_verified": True,
        "all_native_source_output_log_receipt_dependency_recursive_hashes_verified": True,
        "native_runtime_identity_preserved": True, "pinned_runtime_bytes_relocation_verified": True,
        "native_runtime_keys_rewritten": False, "compiler_invoked": False,
        "full_verification_archive_path": str(report_path.relative_to(cur_dir)),
        "full_verification_sha256": digest(report_path),
        "baseline_signature_evidence": old["evidence"], "current_audit_evidence": current["evidence"],
        "new_native_publication_types": {n: current["signatures"][n] for n in sorted(inputs)},
        "new_native_type_review_required_before_credit": sorted(inputs),
        "accepted_units_unchanged": 74, "new_units_credited": 0, "milestone_met": False}
    out = Path(p["output"]) / "INDEPENDENT_CONTINUATION_VERIFICATION.json"
    out.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"independent_archive_passed": True, "source_modules": len(inv["sources"]),
                      "root_count": len(boundaries["roots"]), "report": str(out), "sha256": digest(out)}))


if __name__ == "__main__":
    main()
