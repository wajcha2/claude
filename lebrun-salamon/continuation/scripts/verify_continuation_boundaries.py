#!/usr/bin/env python3
"""Check current native boundaries and types; never mutate an acceptance ledger."""
from __future__ import annotations
import argparse
import json
import re
from pathlib import Path
from continuation_support import (candidate_plan, compare_contexts, context_hash, digest,
    need, publication_inputs, read_json, sha_text, source_inventory, verify_native_build, write_json)
from run_continuation_audit import audit_spec, generate_audit

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound", "sorryAx"}


def no_elision(text):
    need(text and not any(x in text for x in ("⋯", "…", "<unknown>", "[anonymous]")),
         "Native type was elided or is incomplete")


def parse_audit(log_text, spec):
    signatures, roots, axiom_prints = {}, {}, {}
    signature_end, boundary_end = 0, 0
    expected_roots = {r["declaration"]: r["id"] for r in spec["walks"]}
    for line in log_text.splitlines():
        if not line.strip():
            continue
        try:
            item = json.loads(line)
        except ValueError as exc:
            raise ValueError("Non-JSON native audit output") from exc
        need(item.get("severity") != "error", "Native audit emitted an error")
        data = item.get("data", "")
        need(isinstance(data, str), "Malformed native message")
        if data.startswith("CI_SIGNATURE "):
            m = re.fullmatch(r"CI_SIGNATURE (\S+)\nLEVEL_PARAMS ([^\n]*)\nMODULE (\S+)\nTYPE ([\s\S]+)", data)
            need(m is not None, "Malformed native signature")
            name, levels, module, typ = m.groups()
            need(name not in signatures and spec["signatures"].get(name) == module,
                 "Unexpected/duplicate signature or declaring module")
            no_elision(typ)
            signatures[name] = {"name": name, "module": module, "level_params": levels,
                                "native_type": typ, "native_type_sha256": sha_text(typ)}
        elif data == "CI_SIGNATURES_COMPLETE":
            signature_end += 1
        elif data.startswith("CI_ROOT "):
            m = re.fullmatch(r"CI_ROOT (OBL-\d+) (\S+)", data)
            need(m is not None, "Malformed root event")
            audit_id, root = m.groups()
            need(expected_roots.get(root) == audit_id and root not in roots, "Unexpected/duplicate root")
            roots[root] = {"id": audit_id, "declaration": root, "leaves": {}, "summary": None}
        elif data.startswith("CI_DIRECT_SORRY "):
            m = re.fullmatch(r"CI_DIRECT_SORRY (\S+)\nNAME (\S+)\nMODULE (\S+)\nSHORTEST_PATH (.*?)\nTYPE ([\s\S]+)", data)
            need(m is not None, "Malformed native direct-admission event")
            root, name, module, route, typ = m.groups()
            route = route.split(" -> ")
            need(root in roots and route[0] == root and route[-1] == name,
                 "Invalid root-to-admission route")
            need(name not in roots[root]["leaves"], "Duplicate native direct admission")
            no_elision(typ)
            roots[root]["leaves"][name] = {"name": name, "module": module, "shortest_path": route,
                                          "native_type": typ, "native_type_sha256": sha_text(typ)}
        elif data.startswith("CI_SUMMARY "):
            fields = dict(re.findall(r"(\w+)=(\S+)", data))
            root = fields.pop("root", None)
            expected_keys = {"all_constants", "project_constants", "direct_sorry_count",
                             "missing_count", "custom_project_axiom_count", "nonstandard_axiom_count"}
            need(root in roots and roots[root]["summary"] is None and set(fields) == expected_keys,
                 "Missing, duplicate or incomplete root summary")
            summary = {k: int(v) for k, v in fields.items()}
            need(summary["direct_sorry_count"] == len(roots[root]["leaves"]) and
                 all(summary[k] == 0 for k in ("missing_count", "custom_project_axiom_count",
                                               "nonstandard_axiom_count")),
                 "Incomplete traversal or unapproved axiom")
            need(summary["all_constants"] >= summary["project_constants"] > 0,
                 "Invalid traversal counts")
            roots[root]["summary"] = summary
        elif data == "CI_BOUNDARIES_COMPLETE":
            boundary_end += 1
        elif data.startswith(("CI_MISSING ", "CI_NONSTANDARD_AXIOM ", "CI_PROJECT_AXIOM ")):
            raise ValueError("Missing constant or unapproved axiom: " + data)
        elif data.startswith("CI_"):
            raise ValueError("Unrecognized audit event: " + data)
        else:
            m = re.fullmatch(r"'([^']+)' depends on axioms:\s*\[([\s\S]*)\]", data)
            empty = re.fullmatch(r"'([^']+)' does not depend on any axioms\.?", data)
            if m or empty:
                name = re.sub(r"\.\{[^}]*\}", "", (m or empty).group(1)).strip()
                # pp.all prints explicit universe parameters even on standard
                # axiom names. Normalize that notation before splitting; a
                # universe list can itself contain commas. Preserve raw logs.
                axiom_text = "" if empty else re.sub(r"\.\{[^}]*\}", "", m.group(2))
                values = {x.strip() for x in axiom_text.split(",") if x.strip()}
                need(name in expected_roots and name not in axiom_prints and values <= ALLOWED_AXIOMS,
                     "Unexpected/duplicate all-module axiom print")
                axiom_prints[name] = sorted(values)
            elif "depends on axioms" in data or "does not depend on any axioms" in data:
                raise ValueError("Malformed all-module axiom print")
    need(signature_end == 1 and set(signatures) == set(spec["signatures"]), "Incomplete signature capture")
    need(set(roots) == set(expected_roots) and all(r["summary"] for r in roots.values()),
         "Incomplete current root traversal")
    need(set(axiom_prints) == set(expected_roots), "Missing all-module axiom print")
    need(boundary_end == (1 if expected_roots else 0), "Incomplete boundary audit")
    for name, values in axiom_prints.items():
        roots[name]["all_module_axioms"] = values
    return {"signatures": signatures, "roots": roots}


def load_verified_audit(directory, production_root, production_native, config, baseline, expected_spec):
    directory = Path(directory)
    receipt = read_json(directory / "AUDIT_RECEIPT.json")
    need(receipt["mode"] == expected_spec["mode"] and receipt["spec"] == expected_spec,
         "Audit selection/specification changed")
    inv = source_inventory(production_root)
    need(receipt["production_manifest_sha256"] == inv["sha256"], "Audit used a different source snapshot")
    audit_root = directory / "snapshot"
    audit_source = receipt["audit_module"]
    expected_module = ("LSContinuationBaselineSignatures" if expected_spec["mode"] == "baseline"
                       else "LSContinuationCurrentBoundaries")
    need(audit_source == expected_module, "Unrecognized generated audit module")
    text = generate_audit(expected_spec, inv["sources"])
    need(digest(audit_root / "source" / (audit_source + ".lean")) == sha_text(text) ==
         receipt["audit_source_sha256"], "Generated native audit code changed")
    audit_inv = source_inventory(audit_root)
    expected_files = {**inv["files"], "source/" + audit_source + ".lean": sha_text(text)}
    need(audit_inv["files"] == expected_files, "Audit snapshot includes changed production sources")
    native = verify_native_build(audit_root, directory / "kernel-evidence", config, baseline)
    need(native["full_selected_graph_passed"] and native["records"] == receipt["native"]["records"] and
         receipt["return_code"] == 0 and receipt["only_audit_module_compiled"] is True,
         "Audit is not a complete stock native pass")
    contexts = {m: context_hash(rec) for m, rec in native["records"].items() if m != audit_source}
    need(contexts == receipt["production_native_contexts"], "Audit parent context inventory changed")
    need(native["status_counts"].get("passed") == 1 and
         native["records"][audit_source]["state"] == "passed", "Audit fresh/reuse scope differs")
    for module, h in contexts.items():
        need(module in production_native["records"] and
             h == context_hash(production_native["records"][module]) and
             native["records"][module]["state"] == "reused", "Audit has stale or non-native parents")
    raw_receipt = directory / "kernel-evidence" / "receipts" / (audit_source + ".json")
    need(digest(raw_receipt) == receipt["audit_receipt_sha256"], "Audit receipt changed")
    for stream in ("stdout", "stderr"):
        path = directory / receipt[stream + "_relative"]
        need(path.resolve().is_relative_to(directory.resolve()) and
             digest(path) == receipt[stream + "_sha256"] ==
             native["records"][audit_source][stream + "_sha256"], "Audit log bytes differ")
    parsed = parse_audit((directory / receipt["stdout_relative"]).read_text(), expected_spec)
    parsed["evidence"] = {"receipt_sha256": digest(directory / "AUDIT_RECEIPT.json"),
                          "native_receipt_sha256": digest(raw_receipt),
                          "source_sha256": sha_text(text), "stdout_sha256": receipt["stdout_sha256"],
                          "native_output_sha256": native["records"][audit_source]["output_sha256"],
                          "production_native_contexts": contexts}
    return parsed


def reconcile(baseline, change, old, current, native, new_inputs, inv):
    roots = baseline["point1_roots"] + baseline["new_roots"]
    old_names = {r["name"]: r for r in baseline["old_admitted_leaves"]}
    retired = {x["name"] for x in baseline["leaf_policies"] if
               x["policy"] == "retire_direct_admission_preserve_header_and_native_type"}
    protected_leaf_names = {x["name"] for x in baseline["leaf_policies"] if
                            x["policy"] == "unchanged_declaration_and_native_type_rebinding"}
    original_names = {r["declaration"] for r in roots}
    signature_comparisons = []
    for name, before in old["signatures"].items():
        after = current["signatures"].get(name)
        need(after is not None and before == after, "Original/published native type changed: " + name)
        signature_comparisons.append({"name": name, "module": after["module"],
                                      "level_params": after["level_params"],
                                      "native_type_sha256": after["native_type_sha256"]})
    eligible = {}
    for name, item in old_names.items():
        if name in retired:
            continue
        module = item["module"]
        source_hash = inv["files"]["source/" + module.replace(".", "/") + ".lean"]
        need(source_hash == item["source_sha256"] or name in protected_leaf_names,
             "Previously eligible declaration changed without an exact rebind policy")
        eligible[name] = {"kind": "historically_reviewed_current_native_rebinding",
                          "module": module, "source_sha256": source_hash,
                          "native_type_sha256": current["signatures"][name]["native_type_sha256"],
                          "native_context_sha256": context_hash(native["records"][module]),
                          "unchanged_source_or_exact_declaration_guard": True}
    for name, item in new_inputs.items():
        need(name not in eligible and name not in original_names and name not in retired,
             "Original root or retired admission cannot be relabeled a new generic input")
        signature = current["signatures"].get(name)
        need(signature and signature["module"] == item["module"], "Missing native instantiation of reviewed input")
        eligible[name] = {**item, "kind": "new_independently_reviewed_published_input",
                          "native_type_sha256": signature["native_type_sha256"],
                          "native_context_sha256": context_hash(native["records"][item["module"]])}
    root_results, actual_leaves = [], set()
    preserved_ids = set(change["preserved_point1_root_ids"])
    required_ids = set(change["reaudit_point1_root_ids"]) | set(change["new_root_ids"])
    need(preserved_ids.isdisjoint(required_ids) and
         preserved_ids | required_ids == {r["id"] for r in roots}, "Incomplete original-root accounting")
    need({r["id"] for r in current["roots"].values()} == required_ids, "Missing current native root audit")
    for root in roots:
        name, module = root["declaration"], root["module"]
        if root["id"] in preserved_ids:
            need(context_hash(native["records"][module]) == baseline["native_contexts"][module],
                 "Historical boundary reuse has a changed native context")
            leaves = set(root["direct_leaves"])
            need(not leaves & retired and leaves <= set(eligible), "Preserved root has a retired or unreviewed admission")
            mode = "accepted_historical_boundary_in_exact_native_context"
        else:
            result = current["roots"].get(name)
            need(result and result["id"] == root["id"], "Missing required current boundary")
            leaves = set(result["leaves"])
            need(not leaves & original_names and not leaves & retired,
                 "Original obligation is still a direct admission")
            need(leaves <= set(eligible), "Unreviewed current transitive admissions: " +
                 ", ".join(sorted(leaves - set(eligible))))
            for leaf_name, observed in result["leaves"].items():
                signature = current["signatures"].get(leaf_name)
                need(signature and observed["module"] == signature["module"] and
                     observed["native_type"] == signature["native_type"], "Leaf type/context disagrees with signature")
            mode = "fresh_current_native_traversal_and_all_module_axiom_print"
        actual_leaves |= leaves
        root_results.append({"id": root["id"], "declaration": name, "module": module, "mode": mode,
                             "native_type_sha256": current["signatures"][name]["native_type_sha256"],
                             "native_context_sha256": context_hash(native["records"][module]),
                             "direct_leaf_names": sorted(leaves)})
    return {"schema": "lebrun-continuation-boundary-verification-v1",
            "original_root_accounting_count": len(root_results),
            "fresh_current_native_root_audits": len(required_ids),
            "preserved_historical_root_boundaries": len(preserved_ids),
            "fresh_baseline_signature_comparisons": signature_comparisons,
            "historical_point1_signature_scope_unchanged": baseline["historical_signature_scope"],
            "retired_admissions": sorted(retired), "retired_admissions_absent_from_current_boundaries": True,
            "roots": root_results, "actual_direct_leaf_names": sorted(actual_leaves),
            "eligible_leaf_bindings": eligible, "all_current_root_boundaries_verified": True,
            "baseline_signature_evidence": old["evidence"], "current_audit_evidence": current["evidence"],
            "new_native_type_review_required_before_credit": sorted(new_inputs),
            "accepted_units_unchanged": baseline["accepted_units"], "acceptance_ledger_modified": False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ("root", "baseline-root", "build-dir", "baseline-build", "runtime-config",
                "baseline", "plan", "baseline-audit", "current-audit", "output"):
        ap.add_argument("--" + key, type=Path, required=True)
    args = ap.parse_args()
    baseline, plan, config = read_json(args.baseline), read_json(args.plan), read_json(args.runtime_config)
    _, inv, change = candidate_plan(args.root, args.baseline_root, baseline, plan)
    old_native = verify_native_build(args.baseline_root, args.baseline_build, config, baseline)
    need(old_native["whole_current_graph_passed"], "Baseline native graph incomplete")
    need(set(old_native["records"]) == set(baseline["native_contexts"]), "Wrong baseline native modules")
    for m, rec in old_native["records"].items():
        need(context_hash(rec) == baseline["native_contexts"][m], "Baseline context mismatch")
    native = verify_native_build(args.root, args.build_dir, config, baseline)
    need(native["full_selected_graph_passed"], "Current audit parent stage failed")
    compare_contexts(native, baseline, change)
    inputs = publication_inputs(args.root, plan, inv)
    old = load_verified_audit(args.baseline_audit, args.baseline_root, old_native, config, baseline,
                              audit_spec(baseline, "baseline"))
    current = load_verified_audit(args.current_audit, args.root, native, config, baseline,
                                  audit_spec(baseline, "current", change, inputs))
    result = reconcile(baseline, change, old, current, native, inputs, inv)
    result.update({"candidate_plan_sha256": digest(args.plan),
                   "source_manifest_sha256": inv["sha256"],
                   "baseline_record_sha256": digest(args.baseline)})
    write_json(args.output, result)
    print("CONTINUATION_BOUNDARIES_PASSED", result["original_root_accounting_count"],
          result["fresh_current_native_root_audits"], result["preserved_historical_root_boundaries"])


if __name__ == "__main__":
    main()

