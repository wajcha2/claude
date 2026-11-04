#!/usr/bin/env python3
"""Restore a coherent union of independently validated native CI artifacts.

Each input is first checked by the unchanged single-artifact restore utility.
The union then selects receipts in the current source dependency order, requiring
the exact chosen parent outputs and recursive source-ancestry fingerprints.
Conflicting native outputs for the same key are rejected and must be recompiled.
This script does not change source files, the target, or an acceptance ledger.
"""
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
import tempfile

from replay_checkpoint import (
    digest, read_json, runtime_context, source_graph, dependency_order,
    source_ancestry_fingerprint, utc, write_json, FROZEN_TARGET_SHA256,
)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--runtime-config", type=Path, required=True)
    ap.add_argument("--inputs", type=Path, required=True,
                    help="JSON list of artifact_dir, source_run_id, source_artifact_name.")
    ap.add_argument("--build-dir", type=Path, required=True)
    args = ap.parse_args()
    root, build = args.root.resolve(), args.build_dir.resolve()
    if build.exists() and any(build.iterdir()):
        raise SystemExit("Union cache restoration requires an empty build directory.")
    config_path = args.runtime_config.resolve()
    config_hash = digest(config_path)
    config = read_json(config_path)
    identity, fingerprint = runtime_context(root, config)
    if config.get("compiler_kind") != "stock_pinned_frontend":
        raise SystemExit("Union restoration requires the stock pinned frontend.")
    if digest(root / "target/MainStatement.lean") != FROZEN_TARGET_SHA256:
        raise SystemExit("Frozen target changed.")
    inputs_path = args.inputs.resolve()
    inputs_hash = digest(inputs_path)
    inputs = read_json(inputs_path)
    if not isinstance(inputs, list) or not inputs:
        raise SystemExit("Expected a nonempty JSON list of artifact inputs.")
    sources, imports, graph = source_graph(root / "source")
    order, cycles = dependency_order(graph)
    if cycles:
        raise SystemExit("Cyclic source imports: " + ", ".join(cycles))
    source_hashes = {m: digest(p) for m, p in sources.items()}
    external_roots = [Path(p).resolve() for p in config["external_olean_roots"]]
    flags = config.get("flags", ["--json", "-j1", "-DElab.async=false",
        "-M7200", "-DmaxErrors=1000", "-DmaxHeartbeats=2000000"])
    summary = {
        "schema": "lebrun-ci-cache-union-v1", "started_utc": utc(),
        "current_runtime_fingerprint": fingerprint,
        "source_modules": len(sources), "inputs_sha256": inputs_hash,
        "inputs": [], "copied_modules": {}, "rejected_modules": {},
        "native_kernel_invoked": False, "acceptance_ledger_modified": False,
    }
    build.parent.mkdir(parents=True, exist_ok=True)
    good, ancestry, chosen = {}, {}, {}
    with tempfile.TemporaryDirectory(prefix="lebrun-cache-union-", dir=build.parent) as td:
        candidates = {}
        for index, item in enumerate(inputs):
            for key in ("artifact_dir", "source_run_id", "source_artifact_name"):
                if key not in item:
                    raise SystemExit("Missing input field: " + key)
            artifact_dir = Path(item["artifact_dir"]).resolve()
            stage = Path(td) / str(index)
            command = [
                sys.executable, str(root / "scripts/restore_replay_cache.py"),
                "--root", str(root), "--runtime-config", str(config_path),
                "--artifact-dir", str(artifact_dir), "--build-dir", str(stage),
                "--source-run-id", str(int(item["source_run_id"])),
                "--source-artifact-name", item["source_artifact_name"],
            ]
            include_unselected = item.get("include_validated_unselected_cache", False)
            if not isinstance(include_unselected, bool):
                raise SystemExit("Unselected-cache option must be a boolean.")
            if include_unselected:
                command.append("--include-validated-unselected-cache")
            result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT)
            if result.returncode:
                print(result.stdout, flush=True)
                raise SystemExit("Independent artifact validation failed.")
            restored = read_json(stage / "CACHE_RESTORE.json")
            record = {
                "source_run_id": int(item["source_run_id"]),
                "source_artifact_name": item["source_artifact_name"],
                "artifact_dir": str(artifact_dir),
                "validation_sha256": digest(stage / "CACHE_RESTORE.json"),
                "independently_copied_modules": restored.get("copied_module_count", 0),
                "global_rejection": restored.get("global_rejection"),
                "include_validated_unselected_cache": include_unselected,
                "unselected_cache_copied_count": restored.get("unselected_cache_copied_count", 0),
                "unselected_cache_rejection": restored.get("unselected_cache_rejection"),
            }
            summary["inputs"].append(record)
            print("CACHE_UNION_INPUT " + json.dumps(record), flush=True)
            for module in restored.get("copied_modules", {}):
                path = stage / "receipts" / (module + ".json")
                receipt = read_json(path)
                artifact = stage / "olean" / Path(*module.split(".")).with_suffix(".olean")
                candidates.setdefault(module, []).append(
                    (receipt, artifact, path, record))
        for module in order:
            if module not in candidates:
                continue
            deps = {}
            missing = []
            for dep in imports[module]:
                if dep in sources:
                    if dep not in good:
                        missing.append(dep)
                    else:
                        deps[dep] = {"sha256": good[dep], "kind": "project"}
                else:
                    rel = Path(*dep.split(".")).with_suffix(".olean")
                    p = next((p / rel for p in external_roots if (p / rel).is_file()), None)
                    if p is None:
                        missing.append(dep)
                    else:
                        deps[dep] = {"sha256": digest(p), "kind": "external"}
            if missing:
                summary["rejected_modules"][module] = {
                    "reason": "No validated chosen dependency", "dependencies": missing}
                continue
            key = {"source_sha256": source_hashes[module], "imports": imports[module],
                   "dependency_artifacts": deps, "runtime_fingerprint": fingerprint,
                   "flags": flags}
            stamp = source_ancestry_fingerprint(
                module, key, {dep: ancestry[dep] for dep in graph[module]})
            eligible = [x for x in candidates[module]
                        if x[0].get("key") == key
                        and x[0].get("source_ancestry_fingerprint") == stamp
                        and x[0].get("status") == "passed"
                        and x[0].get("return_code") == 0
                        and x[0].get("evidence_kind") == "native_kernel_compilation"]
            if not eligible:
                summary["rejected_modules"][module] = {
                    "reason": "No receipt matches the chosen complete ancestry"}
                continue
            outputs = {x[0]["output_sha256"] for x in eligible}
            if len(outputs) != 1:
                summary["rejected_modules"][module] = {
                    "reason": "Conflicting native outputs for the exact same key",
                    "outputs": sorted(outputs)}
                continue
            receipt, artifact, receipt_path, origin = eligible[0]
            if digest(artifact) != receipt["output_sha256"]:
                raise SystemExit("Validated input output changed: " + module)
            target = build / "olean" / Path(*module.split(".")).with_suffix(".olean")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(artifact, target)
            restored = dict(receipt)
            for stream in ("stdout", "stderr"):
                log = Path(receipt[stream])
                if not log.is_file() or digest(log) != receipt[stream + "_sha256"]:
                    raise SystemExit("Validated input log changed: " + module)
                log_target = build / "logs" / (module + "." + stream + ".log")
                log_target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(log, log_target)
                restored[stream] = str(log_target)
            restored["cache_union_provenance"] = {
                "source_run_id": origin["source_run_id"],
                "source_artifact_name": origin["source_artifact_name"],
                "independently_restored_receipt_sha256": digest(receipt_path),
                "restored_utc": utc(),
            }
            write_json(build / "receipts" / (module + ".json"), restored)
            good[module] = receipt["output_sha256"]
            ancestry[module] = stamp
            chosen[module] = restored
            summary["copied_modules"][module] = {
                "source_sha256": key["source_sha256"], "output_sha256": good[module],
                "source_ancestry_fingerprint": stamp,
                "source_run_id": origin["source_run_id"],
                "source_artifact_name": origin["source_artifact_name"],
            }
        # Final checks occur after every copy, while the validated input trees exist.
        for module, receipt in chosen.items():
            target = build / "olean" / Path(*module.split(".")).with_suffix(".olean")
            if digest(target) != receipt["output_sha256"]:
                raise SystemExit("Restored output changed: " + module)
            for stream in ("stdout", "stderr"):
                if digest(Path(receipt[stream])) != receipt[stream + "_sha256"]:
                    raise SystemExit("Restored log changed: " + module)
            if read_json(build / "receipts" / (module + ".json")) != receipt:
                raise SystemExit("Restored receipt changed: " + module)
            for dep, expected in receipt["key"]["dependency_artifacts"].items():
                rel = Path(*dep.split(".")).with_suffix(".olean")
                if expected["kind"] == "project":
                    path = build / "olean" / rel
                else:
                    path = next((p / rel for p in external_roots if (p / rel).is_file()), None)
                if path is None or digest(path) != expected["sha256"]:
                    raise SystemExit("Chosen dependency changed: " + module + " -> " + dep)
    final_sources, final_imports, final_graph = source_graph(root / "source")
    if final_imports != imports or final_graph != graph or {
            m: digest(p) for m, p in final_sources.items()} != source_hashes:
        raise SystemExit("Source graph changed during cache validation.")
    if digest(config_path) != config_hash or digest(inputs_path) != inputs_hash:
        raise SystemExit("Runtime configuration or input manifest changed.")
    if runtime_context(root, config) != (identity, fingerprint):
        raise SystemExit("Pinned runtime or toolchain changed during cache validation.")
    if digest(root / "target/MainStatement.lean") != FROZEN_TARGET_SHA256:
        raise SystemExit("Frozen target changed during cache validation.")
    summary.update({"finished_utc": utc(), "copied_module_count": len(good),
                    "all_final_hash_and_runtime_checks_passed": True})
    write_json(build / "CACHE_RESTORE.json", summary)
    print("CACHE_UNION_SUMMARY " + json.dumps(
        {k: v for k, v in summary.items()
         if k not in {"copied_modules", "rejected_modules"}}), flush=True)


if __name__ == "__main__":
    main()
