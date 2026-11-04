#!/usr/bin/env python3
"""Generate and run one isolated stock-native continuation type/boundary audit.

The production build and its RUN_STATUS are never modified. Verified parent
artifacts and raw receipts are copied byte-for-byte into an audit-only build.
Only the generated audit module may compile; all production parents must reuse.
"""
from __future__ import annotations
import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path
from continuation_support import (closure, context_hash, digest, module_path, need,
    publication_inputs, read_json, sha_text, source_inventory, verify_native_build, write_json)


def audit_spec(baseline, mode, change=None, new_inputs=None):
    roots = baseline["point1_roots"] + baseline["new_roots"]
    names = {r["declaration"]: r["module"] for r in roots}
    names.update({r["name"]: r["module"] for r in baseline["old_admitted_leaves"]})
    if mode == "current":
        need(change is not None and new_inputs is not None, "Current audit needs an approved impact/review plan")
        names.update({n: r["module"] for n, r in new_inputs.items()})
        walk_ids = set(change["reaudit_point1_root_ids"]) | set(change["new_root_ids"])
        walks = [r for r in roots if r["id"] in walk_ids]
        need({r["id"] for r in walks} == walk_ids, "Unrecognized root audit ID")
    else:
        walks = []
    return {"mode": mode, "signatures": dict(sorted(names.items())),
            "walks": sorted(walks, key=lambda r: r["id"]),
            "imports": sorted(set(names.values()))}


def generate_audit(spec, project_modules):
    # Public names come only from the immutable baseline and approved input plan.
    for name in [*spec["signatures"], *project_modules]:
        need(name and all(c not in name for c in "\n\r\"\x60"), "Unsafe Lean name")
    imports = "".join("import " + m + "\n" for m in spec["imports"])
    names = ",\n    ".join("\x60\x60" + name for name in spec["signatures"])
    modules = ", ".join(json.dumps(name) for name in sorted(project_modules))
    text = imports + """import Lean.Util.CollectAxioms

/-! Generated audit only. Not a production module or an additional obligation.
Native output is authoritative only with its exact receipt and parent contexts. -/
open Lean Elab Command
set_option pp.all true
set_option pp.maxSteps 10000000

run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  for root in #[
    """ + names + """
  ] do
    let some ci := env.checked.get.find? root | throwError m!"Missing audit constant {root}"
    logInfo m!"CI_SIGNATURE {root}\nLEVEL_PARAMS {String.intercalate "," (ci.levelParams.map Name.toString)}\nMODULE {moduleFor root}\nTYPE {ci.type}"
  logInfo "CI_SIGNATURES_COMPLETE"
"""
    if not spec["walks"]:
        return text
    pairs = ",\n    ".join('("' + r["id"] + '", \x60\x60' + r["declaration"] + ')' for r in spec["walks"])
    text += """
run_cmd do
  let env := (← getEnv).setExporting false
  let moduleFor (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => .anonymous
  let projectModules : Array String := #[""" + modules + """]
  let isProject (n : Name) : Bool := projectModules.contains (moduleFor n).toString
  for (auditId, root) in #[
    """ + pairs + """
  ] do
    logInfo m!"CI_ROOT {auditId} {root}"
    let mut todo : Array (Name × List Name) := #[(root, [root])]
    let mut cursor := 0
    let mut seen : NameSet := ({} : NameSet).insert root
    let mut projectSeen : NameSet := {}
    let mut directSorry : Array Name := #[]
    let mut missing : Array Name := #[]
    let mut customAxioms : Array Name := #[]
    let mut nonstandardAxioms : Array Name := #[]
    while cursor < todo.size do
      let (n, path) := todo[cursor]!
      cursor := cursor + 1
      if isProject n then projectSeen := projectSeen.insert n
      let some ci := env.checked.get.find? n | do
        missing := missing.push n
        logInfo m!"CI_MISSING {root} {n}"
        continue
      let mut deps := ci.type.getUsedConstants
      if let some value := ci.value? (allowOpaque := true) then
        deps := deps ++ value.getUsedConstants
      if let .inductInfo v := ci then
        deps := deps ++ v.ctors.toArray
      if let .axiomInfo _ := ci then
        if !(#[\x60\x60propext, \x60\x60Classical.choice, \x60\x60Quot.sound, \x60\x60sorryAx]).contains n then
          nonstandardAxioms := nonstandardAxioms.push n
          logInfo m!"CI_NONSTANDARD_AXIOM {root} {n}"
        if isProject n then
          customAxioms := customAxioms.push n
          logInfo m!"CI_PROJECT_AXIOM {root} {n}"
      if deps.contains \x60\x60sorryAx then
        directSorry := directSorry.push n
        let route := String.intercalate " -> " (path.reverse.map Name.toString)
        logInfo m!"CI_DIRECT_SORRY {root}\nNAME {n}\nMODULE {moduleFor n}\nSHORTEST_PATH {route}\nTYPE {ci.type}"
      for dep in deps do
        if !seen.contains dep then
          seen := seen.insert dep
          todo := todo.push (dep, dep :: path)
    logInfo m!"CI_SUMMARY root={root} all_constants={seen.toArray.size} project_constants={projectSeen.toArray.size} direct_sorry_count={directSorry.size} missing_count={missing.size} custom_project_axiom_count={customAxioms.size} nonstandard_axiom_count={nonstandardAxioms.size}"
  logInfo "CI_BOUNDARIES_COMPLETE"
"""
    text += "\n" + "".join("#print axioms " + r["declaration"] + "\n" for r in spec["walks"])
    return text


def run_audit(production_root, production_build, output, config_path, baseline, spec):
    root, build, output = Path(production_root), Path(production_build), Path(output)
    need(not output.exists() or not any(output.iterdir()), "Audit output directory must be empty")
    config = read_json(config_path)
    inv = source_inventory(root)
    native = verify_native_build(root, build, config, baseline)
    needed = closure(inv["graph"], spec["imports"])
    need(needed <= set(native["records"]), "Audit would use an unverified or missing parent")
    for name, expected_module in spec["signatures"].items():
        need(expected_module in inv["sources"], "Unknown declaring module: " + name)
    audit_root, audit_build = output / "snapshot", output / "kernel-evidence"
    audit_source = "LSContinuationBaselineSignatures" if spec["mode"] == "baseline" else "LSContinuationCurrentBoundaries"
    need(audit_source not in inv["sources"], "Audit module collides with production")
    shutil.copytree(root / "source", audit_root / "source")
    for path in ("target/MainStatement.lean", "TOOLCHAIN.lock.json"):
        target = audit_root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / path, target)
    lean_text = generate_audit(spec, inv["sources"])
    (audit_root / "source" / (audit_source + ".lean")).write_text(lean_text)
    rows = dict(inv["files"])
    rows["source/" + audit_source + ".lean"] = sha_text(lean_text)
    (audit_root / "SOURCE.sha256").write_text("".join(rows[p] + "  " + p + "\n" for p in sorted(rows)))
    for module in needed:
        rec = read_json(build / "receipts" / (module + ".json"))
        files = [("receipts/" + module + ".json", build / "receipts" / (module + ".json")),
                 ("olean/" + module_path(module).with_suffix(".olean").as_posix(),
                  build / "olean" / module_path(module).with_suffix(".olean"))]
        for stream in ("stdout", "stderr"):
            name = Path(rec[stream]).name
            files.append(("logs/" + name, build / "logs" / name))
        for relative, original in files:
            target = audit_build / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(original, target)
            need(digest(target) == digest(original), "Audit artifact copy changed bytes")
    command = [sys.executable, str(Path(__file__).with_name("replay_checkpoint.py")),
               "--root", str(audit_root.resolve()), "--runtime-config", str(Path(config_path).resolve()),
               "--build-dir", str(audit_build.resolve()), "--module", audit_source,
               "--keep-going", "--timeout", "300"]
    result = subprocess.run(command, check=False)
    audited = verify_native_build(audit_root, audit_build, config, baseline)
    need(source_inventory(root)["text"] == inv["text"], "Production source changed during audit")
    parents_after = verify_native_build(root, build, config, baseline)
    need(parents_after["records"] == native["records"], "Production native contexts changed during audit")
    for module in needed:
        need(audited["records"].get(module, {}).get("state") == "reused" and
             context_hash(audited["records"][module]) == context_hash(native["records"][module]),
             "Audit recompiled or altered a production parent")
    receipt = read_json(audit_build / "receipts" / (audit_source + ".json"))
    evidence = {"schema": "lebrun-continuation-native-audit-v1", "mode": spec["mode"],
                "spec": spec, "audit_module": audit_source, "audit_source_sha256": sha_text(lean_text),
                "audit_snapshot_manifest_sha256": digest(audit_root / "SOURCE.sha256"),
                "production_manifest_sha256": inv["sha256"], "production_native_contexts":
                    {m: context_hash(native["records"][m]) for m in sorted(needed)},
                "audit_receipt_sha256": digest(audit_build / "receipts" / (audit_source + ".json")),
                "stdout_relative": "kernel-evidence/logs/" + Path(receipt["stdout"]).name,
                "stderr_relative": "kernel-evidence/logs/" + Path(receipt["stderr"]).name,
                "stdout_sha256": receipt["stdout_sha256"], "stderr_sha256": receipt["stderr_sha256"],
                "native": audited, "return_code": result.returncode,
                "only_audit_module_compiled": audited["status_counts"].get("passed") == 1 and
                    all(audited["records"][m]["state"] == "reused" for m in needed),
                "production_build_unchanged": True, "production_module_count_excludes_audit": len(inv["sources"]),
                "accepted_obligation_credit": 0, "acceptance_ledger_modified": False}
    write_json(output / "AUDIT_RECEIPT.json", evidence)
    need(result.returncode == 0 and audited["full_selected_graph_passed"] and
         evidence["only_audit_module_compiled"], "Native audit did not complete")
    # Require complete unelided baseline signatures before any candidate build.
    from verify_continuation_boundaries import parse_audit
    parsed = parse_audit((output / evidence["stdout_relative"]).read_text(), spec)
    evidence["native_message_validation"] = {"complete_unelided_signatures": len(parsed["signatures"]),
                                              "complete_root_walks": len(parsed["roots"])}
    write_json(output / "AUDIT_RECEIPT.json", evidence)
    print("CONTINUATION_AUDIT_PASSED", spec["mode"], len(spec["signatures"]), len(spec["walks"]))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--build-dir", type=Path, required=True)
    ap.add_argument("--runtime-config", type=Path, required=True)
    ap.add_argument("--baseline", type=Path, required=True)
    ap.add_argument("--mode", choices=["baseline", "current"], required=True)
    ap.add_argument("--plan", type=Path)
    ap.add_argument("--preflight", type=Path)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    baseline = read_json(args.baseline)
    change, inputs = None, None
    if args.mode == "current":
        need(args.plan and args.preflight, "Current audit requires the approved plan/preflight")
        preflight = read_json(args.preflight)
        need(preflight["plan_sha256"] == digest(args.plan) and
             preflight["candidate"]["source_manifest_sha256"] == source_inventory(args.root)["sha256"],
             "Stale preflight for current audit")
        change = preflight["impact"]
        inputs = publication_inputs(args.root, read_json(args.plan), source_inventory(args.root))
    spec = audit_spec(baseline, args.mode, change, inputs)
    run_audit(args.root, args.build_dir, args.output, args.runtime_config, baseline, spec)


if __name__ == "__main__":
    main()

