from pathlib import Path
import hashlib,json,os,subprocess,sys
root=Path("lebrun-salamon/continuation")
build=Path("kernel-evidence")
sys.path.insert(0,str(root/"scripts"))
from replay_checkpoint import source_graph,dependency_order,source_ancestry_fingerprint,digest,runtime_context
status=json.loads((build/"RUN_STATUS.json").read_text())
sources,imports,graph=source_graph(root/"source")
order,cycles=dependency_order(graph)
assert not cycles
before={m:digest(p) for m,p in sources.items()}
runtime,fingerprint=runtime_context(root,status["runtime"]["config"])
assert runtime==status["runtime"] and fingerprint==status["runtime_fingerprint"]
assert runtime["config"]["compiler_kind"]=="stock_pinned_frontend"
assert runtime["config"]["mathlib_revision"]=="116662aa4c1e9106ab5c609b3214b02f6e11a65a"
assert runtime["toolchain_lock_sha256"]=="7f60e90fabda82f0e4e3c3bf4537d24f1298514f116bc18215f162e203f11c19"
assert digest(root/"target/MainStatement.lean")=="9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296"
assert not status["final_validation"]["invalidated_modules"] and not status["final_validation"]["changed_runtime_files"]
external_roots=[Path(p) for p in runtime["config"]["external_olean_roots"]]
good={};records={};errors=[]
for module in order:
    state=status["modules"].get(module)
    if not state or state["status"]=="blocked":continue
    recpath=build/"receipts"/(module+".json")
    rec=json.loads(recpath.read_text());key=rec["key"]
    assert key["source_sha256"]==before[module] and key["imports"]==imports[module]
    assert key["runtime_fingerprint"]==fingerprint
    deps={}
    for dep in imports[module]:
        if dep in sources:
            assert dep in good
            deps[dep]={"kind":"project","sha256":good[dep]["output_sha256"]}
        else:
            rel=Path(*dep.split(".")).with_suffix(".olean")
            path=next((p/rel for p in external_roots if (p/rel).is_file()),None)
            assert path is not None
            deps[dep]={"kind":"external","sha256":digest(path)}
    assert key["dependency_artifacts"]==deps
    for stream in ["stdout","stderr"]:
        if stream in rec:assert digest(Path(rec[stream]))==rec[stream+"_sha256"]
    if state["status"] not in {"passed","reused","historical_reuse"}:
        parsed=[]
        for line in Path(rec["stdout"]).read_text().splitlines():
            try:item=json.loads(line)
            except ValueError:continue
            if item.get("severity")=="error":parsed.append(item)
        item={"module":module,"status":state["status"],"source_sha256":before[module],
              "return_code":rec.get("return_code"),"seconds":rec.get("seconds"),"errors":parsed,
              "stderr":Path(rec["stderr"]).read_text()}
        errors.append(item);print("NATIVE_DIAGNOSTIC "+json.dumps(item,ensure_ascii=False));continue
    assert rec["status"]=="passed" and rec["return_code"]==0 and rec["evidence_kind"]=="native_kernel_compilation"
    out=build/"olean"/Path(*module.split(".")).with_suffix(".olean")
    assert digest(out)==rec["output_sha256"]==state["output_sha256"]
    stamp=source_ancestry_fingerprint(module,key,{d:good[d]["source_ancestry_fingerprint"] for d in graph[module]})
    assert stamp==rec["source_ancestry_fingerprint"]
    record={"module":module,"receipt_sha256":digest(recpath),"key":key,"output_sha256":rec["output_sha256"],
            "source_ancestry_fingerprint":stamp,"seconds":rec.get("seconds"),
            "stdout_sha256":rec.get("stdout_sha256"),"stderr_sha256":rec.get("stderr_sha256"),
            "cache_restore_provenance":rec.get("cache_restore_provenance")}
    records[module]=record;good[module]=record
    print("NATIVE_RECEIPT "+json.dumps(record,ensure_ascii=False))
assert len(good)==status["final_validation"]["checked_module_count"]
boundary=json.loads((root/"audit/ci/41763014879/point1/VALIDATED_SEEDS.json").read_text())["modules"]
assert len(boundary)==190
bound_good=0
for module,old in boundary.items():
    assert before[module]==old["source_sha256"] and imports[module]==old["imports"]
    if module in good:
        now=good[module]
        assert now["output_sha256"]==old["output_sha256"]
        assert now["source_ancestry_fingerprint"]==old["source_ancestry_fingerprint"]
        assert now["key"]["dependency_artifacts"]==old["dependency_artifacts"]
        bound_good+=1
assert before=={m:digest(p) for m,p in sources.items()}
assert runtime_context(root,status["runtime"]["config"])==(runtime,fingerprint)
for module,rec in good.items():assert digest(build/"olean"/Path(*module.split(".")).with_suffix(".olean"))==rec["output_sha256"]
summary={"schema":"lebrun-remote-stage-validation-v1","commit":subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip(),
         "source_modules":len(sources),"selected_modules":len(status["selected_modules"]),"accepted_modules":len(good),
         "failed_modules":status["failures"],"full_selected_graph_passed":status["full_selected_graph_passed"],
         "whole_source_graph_passed":status["full_selected_graph_passed"] and set(status["selected_modules"])==set(sources),
         "Point1_source_boundary_unchanged":190,"Point1_native_boundary_rechecked_in_this_stage":bound_good,
         "all_final_hash_and_runtime_checks_passed":True,"acceptance_ledger_modified":False}
(build/"NATIVE_STAGE_REPORT.json").write_text(json.dumps({"summary":summary,"runtime":runtime,"errors":errors,"receipts":records},indent=2,ensure_ascii=False)+"\n")
print("NATIVE_REPLAY_SUMMARY "+json.dumps(summary,ensure_ascii=False))
print("NATIVE_RUNTIME "+json.dumps(runtime,ensure_ascii=False))
