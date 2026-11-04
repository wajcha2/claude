#!/usr/bin/env python3
"""Strict continuation checks. No compiler invocation or acceptance mutation.

The accepted Point1 reporter is deliberately not imported or modified. Historical
equality and current native revalidation are different evidence claims.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from check_checkpoint import strip_noncode
from replay_checkpoint import (dependency_order, digest, runtime_context,
                               source_ancestry_fingerprint, source_graph)


class GateError(ValueError):
    pass


def need(condition, message):
    if not condition:
        raise GateError(message)


def read_json(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def sha_text(text):
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def json_hash(value):
    return sha_text(json.dumps(value, sort_keys=True, ensure_ascii=False))


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def safe_relative(value):
    path = Path(value)
    need(not path.is_absolute() and value and ".." not in path.parts, "Unsafe relative path")
    return path


def module_path(module):
    need(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module),
         "Unsupported module name: " + str(module))
    return Path(*module.split("."))


def parse_manifest(text):
    rows = {}
    for line in text.splitlines():
        match = re.fullmatch(r"([0-9a-f]{64})  (source/.+\.lean)", line)
        need(match is not None, "Malformed source manifest")
        h, name = match.groups()
        safe_relative(name)
        need(name not in rows, "Duplicate source manifest path")
        rows[name] = h
    need(rows and text == "".join(rows[p] + "  " + p + "\n" for p in sorted(rows)),
         "Source manifest is not the exact sorted complete serialization")
    return rows


def source_inventory(root):
    root = Path(root)
    text = (root / "SOURCE.sha256").read_text(encoding="utf-8")
    rows = parse_manifest(text)
    actual = {p.relative_to(root).as_posix(): digest(p) for p in (root / "source").rglob("*.lean")}
    need(rows == actual, "Source manifest/file membership or bytes differ")
    sources, imports, graph = source_graph(root / "source")
    for p in sources.values():
        # The unchanged production driver understands ordinary import commands.
        need(not re.search(r"^\s*(?:public|private|meta)\s+import\b|^\s*prelude\b",
                           strip_noncode(p.read_text()), re.M),
             "Import form unsupported by the unchanged production driver: " + str(p))
    order, cycles = dependency_order(graph)
    need(not cycles, "Cyclic project imports")
    return {"text": text, "sha256": sha_text(text), "files": rows,
            "sources": sources, "imports": imports, "graph": graph, "order": order}


def git_binding(root, commit, prefix):
    """Check exact source membership and Git blobs, without reading a worktree index."""
    root = Path(root)
    inv = source_inventory(root)
    prefix = safe_relative(prefix).as_posix()
    tracked = [prefix + "/source", prefix + "/target/MainStatement.lean",
               prefix + "/TOOLCHAIN.lock.json", prefix + "/SOURCE.sha256"]
    raw = subprocess.check_output(["git", "ls-tree", "-r", "-z", commit, "--", *tracked])
    entries = {}
    for item in raw.split(b"\0"):
        if not item:
            continue
        metadata, filename = item.split(b"\t", 1)
        mode, kind, blob = metadata.split()
        need(kind == b"blob" and mode == b"100644", "Unexpected source Git entry")
        entries[filename.decode()] = blob.decode()
    expected = set(inv["files"]) | {"target/MainStatement.lean", "TOOLCHAIN.lock.json", "SOURCE.sha256"}
    need(set(entries) == {prefix + "/" + p for p in expected}, "Git source membership differs")
    for p in expected:
        data = (root / p).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        need(entries[prefix + "/" + p] == blob, "Git/file bytes differ: " + p)
    return {"commit": commit, "tree": subprocess.check_output(
        ["git", "rev-parse", commit + "^{tree}"], text=True).strip(),
        "source_manifest_sha256": inv["sha256"], "all_source_target_lock_manifest_git_blobs_verified": True}


def context_hash(record):
    return json_hash({k: record[k] for k in
                     ("key", "output_sha256", "stdout_sha256", "stderr_sha256", "source_ancestry_fingerprint")})


def apply_exact_patches(text, patches):
    for patch in patches:
        before, after = patch["before"], patch["after"]
        need(before and before != after and text.count(before) == 1, "Nonunique or empty guarded patch")
        text = text.replace(before, after, 1)
    return text


def verify_protected_files(root, baseline):
    for name, expected in baseline["protected_files"].items():
        need(digest(Path(root) / safe_relative(name)) == expected,
             "Historical driver, reporter, runtime recipe or accepted ledger changed: " + name)


def closure(graph, modules):
    selected = set(modules)
    need(selected <= set(graph), "Unknown closure target")
    todo = list(selected)
    for module in todo:
        for dep in graph[module]:
            if dep not in selected:
                selected.add(dep)
                todo.append(dep)
    return selected


def publication_inputs(root, plan, inv):
    """Bind independent eligibility reviews to exact current declarations.

    Eligibility is not native instantiation or acceptance. The native walker
    later binds these reviewed declarations to their actual types and contexts.
    """
    result = {}
    for entry in plan.get("publication_reviews", []):
        path = Path(root) / safe_relative(entry["path"])
        need(digest(path) == entry["sha256"], "Publication review bytes changed")
        review = read_json(path)
        need(review.get("schema") == "lebrun-independent-publication-review-v1" and
             review.get("reviewer") == "root", "Unapproved publication review")
        source = review["source"]
        source_hash = source.get("candidate_sha256", source.get("sha256"))
        need(inv["files"].get(source["path"]) == source_hash, "Publication review source is stale")
        module = source["path"][7:-5].replace("/", ".")
        text = inv["sources"][module].read_text()
        fragments = {x["name"]: x["declaration_source"] for x in entry["declarations"]}
        need(len(fragments) == len(entry["declarations"]), "Duplicate reviewed declaration")
        need(set(fragments) == {x["declaration"] for x in review["interfaces"]},
             "Review interfaces and supplied declarations differ")
        for interface in review["interfaces"]:
            name = interface["declaration"]
            fragment = fragments[name]
            need(name not in result and interface.get("eligible") is True and
                 interface.get("primary_sources"), "Duplicate or ineligible published input")
            need(fragment and text.count(fragment) == 1 and
                 sha_text(fragment) == interface["declaration_sha256"],
                 "Reviewed declaration/source binding changed: " + name)
            result[name] = {"name": name, "module": module, "source_sha256": source_hash,
                            "declaration_sha256": interface["declaration_sha256"],
                            "review_path": entry["path"], "review_sha256": entry["sha256"],
                            "primary_sources": interface["primary_sources"]}
    need(result, "No exact independent publication reviews supplied")
    return result


def candidate_plan(root, baseline_root, baseline, plan):
    need(plan.get("schema") == "lebrun-continuation-candidate-plan-v1", "Wrong candidate-plan schema")
    need(plan.get("status") == "approved_for_native_validation" and plan.get("dispatch_authorized") is True,
         "Complete candidate handoff and guard approval are required; no compilation authorized by this plan")
    need(plan.get("baseline_accepted_commit") == baseline["accepted_commit"], "Wrong accepted baseline")
    need(plan.get("baseline_source_manifest_sha256") == baseline["source_manifest_sha256"], "Wrong baseline manifest")
    need(plan.get("baseline_accepted_units") == 74 and plan.get("denominator") == 133, "Accounting boundary changed")
    old, cur = source_inventory(baseline_root), source_inventory(root)
    need(old["text"] == baseline["source_manifest"], "Baseline source bytes differ")
    need(cur["sha256"] == plan.get("candidate_manifest_sha256"), "Unbound candidate manifest")
    need(set(old["files"]) <= set(cur["files"]), "Original production source removed")
    edits = plan.get("source_edits", [])
    added = plan.get("added_sources", [])
    need(len({x["path"] for x in edits}) == len(edits), "Duplicate source edit")
    need(len({x["path"] for x in added}) == len(added), "Duplicate added source")
    changed = {p for p in old["files"] if old["files"][p] != cur["files"][p]}
    need(changed == {x["path"] for x in edits}, "Changed sources differ from the approved handoff")
    need(set(cur["files"]) - set(old["files"]) == {x["path"] for x in added}, "Added sources differ from approved handoff")
    for edit in edits:
        p = safe_relative(edit["path"])
        need(old["files"][str(p)] == edit["baseline_sha256"] and
             cur["files"][str(p)] == edit["candidate_sha256"], "Guard source hash mismatch")
        before = (Path(baseline_root) / p).read_text()
        after = (Path(root) / p).read_text()
        need(apply_exact_patches(before, edit["patches"]) == after, "Forward patch does not reproduce candidate")
        inverse = [{"before": x["after"], "after": x["before"]} for x in reversed(edit["patches"])]
        need(apply_exact_patches(after, inverse) == before, "Inverse patch does not restore accepted source")
    for item in added:
        need(item["path"] not in old["files"] and cur["files"][item["path"]] == item["sha256"],
             "New-module absence or hash guard failed")
    for r in baseline["new_roots"]:
        text = cur["sources"][r["module"]].read_text()
        need(text.count(r["original_header"]) == 1, "Original public header changed: " + r["id"])
    for leaf in baseline["leaf_policies"]:
        if leaf["policy"] == "unchanged_declaration_and_native_type_rebinding":
            text = cur["sources"][leaf["module"]].read_text()
            need(sha_text(leaf["declaration_source"]) == leaf["declaration_sha256"] and
                 text.count(leaf["declaration_source"]) == 1,
                 "Published declaration was changed: " + leaf["name"])
    verify_protected_files(root, baseline)
    publication_inputs(root, plan, cur)
    return old, cur, impact(old, cur, baseline)


def impact(old, cur, baseline):
    changed = {m for m in old["sources"] if m not in cur["sources"] or
               old["files"]["source/" + module_path(m).as_posix() + ".lean"] !=
               cur["files"].get("source/" + module_path(m).as_posix() + ".lean") or
               old["imports"][m] != cur["imports"].get(m)}
    added = set(cur["sources"]) - set(old["sources"])
    reverse = {m: set() for m in set(old["sources"]) | set(cur["sources"])}
    for graph in (old["graph"], cur["graph"]):
        for m, dependencies in graph.items():
            for dep in dependencies:
                reverse[dep].add(m)
    affected = changed | added
    todo = list(affected)
    for m in todo:
        for child in reverse[m]:
            if child not in affected:
                affected.add(child)
                todo.append(child)
    preserved = set(old["sources"]) - affected
    boundary = set(baseline["point1_boundary_modules"])
    roots = baseline["point1_roots"]
    return {
        "changed_modules": sorted(changed), "added_modules": sorted(added),
        "affected_current_modules": sorted(affected & set(cur["sources"])),
        "baseline_contexts_to_preserve": sorted(preserved),
        "baseline_contexts_to_replace": sorted(affected & set(old["sources"])),
        "historical_point1_contexts_to_preserve": sorted(boundary & preserved),
        "historical_point1_contexts_to_revalidate": sorted(boundary & affected),
        "preserved_point1_root_ids": sorted(r["id"] for r in roots if r["module"] in preserved),
        "reaudit_point1_root_ids": sorted(r["id"] for r in roots if r["module"] in affected),
        "new_root_ids": sorted(r["id"] for r in baseline["new_roots"]),
    }


def verify_native_build(root, build, config, baseline):
    """Same strict native bindings as Point1, without assuming unchanged ancestors."""
    root, build = Path(root), Path(build)
    inv = source_inventory(root)
    status = read_json(build / "RUN_STATUS.json")
    identity, fingerprint = runtime_context(root, config)
    need(config.get("compiler_kind") == "stock_pinned_frontend", "Non-stock compiler")
    need(fingerprint == baseline["runtime_fingerprint"], "Pinned native runtime identity changed")
    need(config["flags"] == baseline["runtime_flags"] and config["mathlib_revision"] == baseline["mathlib_revision"],
         "Compiler flags or mathlib changed")
    need(digest(root / "target/MainStatement.lean") == baseline["target_sha256"] and
         digest(root / "TOOLCHAIN.lock.json") == baseline["lock_sha256"], "Frozen target or lock changed")
    need(status["runtime"] == identity and status["runtime_fingerprint"] == fingerprint, "Run/runtime binding differs")
    need(not status["final_validation"]["invalidated_modules"] and
         not status["final_validation"]["changed_runtime_files"], "Native final validation invalidated inputs")
    selected = set(status["selected_modules"])
    need(len(selected) == len(status["selected_modules"]) and selected <= set(inv["sources"]), "Invalid selection")
    need(set(status["modules"]) == selected, "Incomplete selected-module status coverage")
    need(all(set(inv["graph"][m]) <= selected for m in selected), "Selection omits an ancestor")
    external_roots = [Path(p) for p in config["external_olean_roots"]]
    good, errors, records = {}, [], {}
    for module in inv["order"]:
        if module not in selected:
            continue
        state = status["modules"][module]
        if state["status"] == "blocked":
            errors.append({"module": module, "status": "blocked"})
            continue
        recpath = build / "receipts" / (module + ".json")
        rec = read_json(recpath)
        need(rec["key"]["source_sha256"] == digest(inv["sources"][module]) and
             rec["key"]["imports"] == inv["imports"][module], "Receipt source/import mismatch: " + module)
        deps = {}
        for dep in inv["imports"][module]:
            if dep in inv["sources"]:
                need(dep in good, "Successful/attempted module has no verified parent: " + module)
                deps[dep] = {"kind": "project", "sha256": good[dep]["output_sha256"]}
            else:
                rel = module_path(dep).with_suffix(".olean")
                p = next((r / rel for r in external_roots if (r / rel).is_file()), None)
                need(p is not None, "Missing external import: " + dep)
                deps[dep] = {"kind": "external", "sha256": digest(p)}
        need(rec["key"] == {"source_sha256": digest(inv["sources"][module]),
             "imports": inv["imports"][module], "dependency_artifacts": deps,
             "runtime_fingerprint": fingerprint, "flags": config["flags"]}, "Complete native key mismatch: " + module)
        logs = {}
        for stream in ("stdout", "stderr"):
            p = build / "logs" / Path(rec[stream]).name
            need(p.is_file() and digest(p) == rec[stream + "_sha256"], "Native log mismatch: " + module)
            logs[stream] = p
        if state["status"] not in {"passed", "reused"}:
            diagnostics = []
            for line in logs["stdout"].read_text().splitlines():
                try:
                    item = json.loads(line)
                except ValueError:
                    continue
                if item.get("severity") == "error":
                    diagnostics.append(item)
            errors.append({"module": module, "status": state["status"], "return_code": rec.get("return_code"),
                           "seconds": rec.get("seconds"), "errors": diagnostics,
                           "stderr": logs["stderr"].read_text()})
            continue
        need(rec.get("schema") == "lebrun-module-receipt-v1" and rec.get("module") == module and
             rec.get("status") == "passed" and rec.get("return_code") == 0 and
             rec.get("evidence_kind") == "native_kernel_compilation", "Not a successful native receipt: " + module)
        output = build / "olean" / module_path(module).with_suffix(".olean")
        need(output.is_file() and digest(output) == rec["output_sha256"] == state["output_sha256"],
             "Native output mismatch: " + module)
        stamp = source_ancestry_fingerprint(module, rec["key"],
            {d: good[d]["source_ancestry_fingerprint"] for d in inv["graph"][module]})
        need(stamp == rec.get("source_ancestry_fingerprint"), "Recursive ancestry mismatch: " + module)
        record = {"module": module, "receipt_sha256": digest(recpath), "key": rec["key"],
                  "output_sha256": rec["output_sha256"], "source_ancestry_fingerprint": stamp,
                  "stdout_sha256": rec["stdout_sha256"], "stderr_sha256": rec["stderr_sha256"],
                  "seconds": rec.get("seconds"), "state": state["status"]}
        good[module] = record
        records[module] = (recpath, output, logs)
    need(len(good) == status["final_validation"]["checked_module_count"], "Accepted count differs from final check")
    need(source_inventory(root)["text"] == inv["text"], "Sources changed during report validation")
    need(runtime_context(root, config) == (identity, fingerprint), "Runtime changed during report validation")
    for module, (recpath, output, logs) in records.items():
        record = good[module]
        need(digest(recpath) == record["receipt_sha256"] and digest(output) == record["output_sha256"],
             "Receipt/output changed during report validation")
        for stream, path in logs.items():
            need(digest(path) == record[stream + "_sha256"], "Log changed during report validation")
        for dep, binding in record["key"]["dependency_artifacts"].items():
            rel = module_path(dep).with_suffix(".olean")
            path = build / "olean" / rel if binding["kind"] == "project" else next(
                (r / rel for r in external_roots if (r / rel).is_file()), None)
            need(path is not None and digest(path) == binding["sha256"], "Dependency changed during report validation")
    counts = {}
    for state in status["modules"].values():
        counts[state["status"]] = counts.get(state["status"], 0) + 1
    return {"schema": "lebrun-continuation-native-stage-v1", "source_modules": len(inv["sources"]),
            "selected_modules": len(selected), "accepted_modules": len(good), "status_counts": counts,
            "selected": sorted(selected), "records": good, "errors": errors,
            "source_manifest_sha256": inv["sha256"], "complete_source_manifest": inv["text"],
            "runtime": identity, "runtime_fingerprint": fingerprint,
            "full_selected_graph_passed": not errors and len(good) == len(selected),
            "whole_current_graph_passed": not errors and set(good) == set(inv["sources"]),
            "all_native_source_output_log_receipt_runtime_dependency_and_recursive_hashes_verified": True,
            "acceptance_ledger_modified": False}


def compare_contexts(stage, baseline, change):
    preserved, replaced, added = [], [], []
    affected = set(change["baseline_contexts_to_replace"])
    for module, record in stage["records"].items():
        if module not in baseline["native_contexts"]:
            need(module in change["added_modules"], "Unapproved new native module")
            added.append(module)
        elif module in affected:
            # A new recursive context is required even if an intermediate .olean is identical.
            need(context_hash(record) != baseline["native_contexts"][module],
                 "Affected module retained its historical context: " + module)
            replaced.append(module)
        else:
            need(context_hash(record) == baseline["native_contexts"][module],
                 "Unchanged context differs from accepted baseline: " + module)
            preserved.append(module)
    return {"preserved_baseline_contexts": sorted(preserved),
            "verified_replacement_contexts": sorted(replaced), "verified_new_contexts": sorted(added),
            "pending_current_modules": sorted(set(change["affected_current_modules"]) - set(stage["records"])),
            "historical_point1_equality_claim_reused": False}
