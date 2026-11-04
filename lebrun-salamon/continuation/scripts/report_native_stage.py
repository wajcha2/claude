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
    assert key["flags"]==runtime["config"]["flags"]
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
            "cache_restore_provenance":rec.get("cache_restore_provenance"),
            "cache_union_provenance":rec.get("cache_union_provenance")}
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

# Bind the complete source snapshot and the final gate to exact Git objects.
commit=subprocess.check_output(["git","rev-parse","HEAD"],text=True).strip()
tree=subprocess.check_output(["git","rev-parse","HEAD^{tree}"],text=True).strip()
if os.environ.get("GITHUB_SHA"):assert commit==os.environ["GITHUB_SHA"]
tracked=[str(root/"source"),str(root/"target/MainStatement.lean"),
         str(root/"TOOLCHAIN.lock.json"),str(root/"SOURCE.sha256")]
git_entries=subprocess.check_output(["git","ls-tree","-r","-z","HEAD","--",*tracked]).split(b"\0")
git_hashes={}
for entry in git_entries:
    if not entry:continue
    metadata,path=entry.split(b"\t",1)
    mode,kind,blob=metadata.split()
    assert kind==b"blob"
    git_hashes[path.decode()]=blob.decode()
source_bytes={}
for module,path in sources.items():
    rel=path.resolve().relative_to(root.resolve())
    git_path=str(root/rel)
    data=path.read_bytes()
    blob=hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
    assert git_hashes[git_path]==blob
    source_bytes[str(rel)]=hashlib.sha256(data).hexdigest()
assert {p for p in git_hashes if p.startswith(str(root/"source")+"/") and p.endswith(".lean")}=={str(root/p) for p in source_bytes}
for path in [root/"target/MainStatement.lean",root/"TOOLCHAIN.lock.json",root/"SOURCE.sha256"]:
    data=path.read_bytes()
    assert git_hashes[str(path)]==hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest()
manifest=(root/"SOURCE.sha256").read_text()
expected_manifest="".join(source_bytes[p]+"  "+p+"\n" for p in sorted(source_bytes))
assert manifest==expected_manifest
final_sources,final_imports,final_graph=source_graph(root/"source")
assert final_imports==imports and final_graph==graph
assert {m:digest(p) for m,p in final_sources.items()}==before
for module,record in records.items():
    recpath=build/"receipts"/(module+".json")
    assert digest(recpath)==record["receipt_sha256"]
    rec=json.loads(recpath.read_text())
    for stream in ["stdout","stderr"]:
        assert digest(Path(rec[stream]))==record[stream+"_sha256"]
    for dep,key in record["key"]["dependency_artifacts"].items():
        rel=Path(*dep.split(".")).with_suffix(".olean")
        if key["kind"]=="project":path=build/"olean"/rel
        else:path=next((p/rel for p in external_roots if (p/rel).is_file()),None)
        assert path is not None and digest(path)==key["sha256"]
assert runtime_context(root,status["runtime"]["config"])==(runtime,fingerprint)
counts={}
for module,state in status["modules"].items():
    counts[state["status"]]=counts.get(state["status"],0)+1
basis=root/"audit/ci/41763014879/point1/VALIDATED_SEEDS.json"
verification={
    "schema":"lebrun-full-replay-verification-v1",
    "commit":commit,"tree":tree,"run_id":int(os.environ.get("GITHUB_RUN_ID","0")),
    "run_attempt":int(os.environ.get("GITHUB_RUN_ATTEMPT","0")),
    "source_modules":len(sources),"selected_modules":len(status["selected_modules"]),
    "accepted_modules":len(good),"status_counts":counts,
    "fresh_native_passes":counts.get("passed",0),
    "native_receipts_reused":counts.get("reused",0),
    "failures":status["failures"],
    "all_current_sources_kernel_checked":summary["whole_source_graph_passed"],
    "source_manifest_sha256":digest(root/"SOURCE.sha256"),
    "complete_source_manifest":manifest,
    "frozen_target_sha256":digest(root/"target/MainStatement.lean"),
    "toolchain_lock_sha256":digest(root/"TOOLCHAIN.lock.json"),
    "source_target_lock_manifest_git_blob_binding_verified":True,
    "runtime_fingerprint":fingerprint,
    "runtime_flags":runtime["config"]["flags"],
    "compiler_kind":runtime["config"]["compiler_kind"],
    "mathlib_revision":runtime["config"]["mathlib_revision"],
    "native_stage_report_sha256":digest(build/"NATIVE_STAGE_REPORT.json"),
    "complete_native_receipts_sha256":hashlib.sha256(
        json.dumps(records,sort_keys=True,ensure_ascii=False).encode()).hexdigest(),
    "all_accepted_output_log_receipt_dependency_and_recursive_ancestry_hashes_verified":True,
    "all_final_source_graph_and_runtime_hashes_verified":True,
    "point1_boundary":{
        "basis_path":str(basis),"basis_sha256":digest(basis),
        "source_and_import_comparisons":190,
        "native_output_dependency_and_recursive_stamp_comparisons":bound_good,
        "all190_compared_and_unchanged":bound_good==190,
        "modules":sorted(boundary)},
    "acceptance_ledger_modified":False
}
(build/"FULL_REPLAY_VERIFICATION.json").write_text(
    json.dumps(verification,indent=2,ensure_ascii=False)+"\n")
print("FULL_REPLAY_VERIFICATION "+json.dumps(verification,ensure_ascii=False))
