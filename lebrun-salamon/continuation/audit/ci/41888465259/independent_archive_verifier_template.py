import json,hashlib,zipfile,pathlib,urllib.request,os,re
p=json.loads(__PAYLOAD__)
H=lambda b:hashlib.sha256(b).hexdigest()
enc=lambda x:json.dumps(x,sort_keys=True,ensure_ascii=False).encode()
fields=lambda r:{k:r[k] for k in ["key","output_sha256","stdout_sha256","stderr_sha256","source_ancestry_fingerprint"]}
zp=pathlib.Path(p["archive_path"]);zp.parent.mkdir(parents=True,exist_ok=True)
if not zp.exists():
    temp=zp.with_suffix(".download")
    with urllib.request.urlopen(p["download_url"],timeout=120) as response,temp.open("wb") as f:
        while True:
            block=response.read(1048576)
            if not block:break
            f.write(block)
    os.replace(temp,zp)
assert H(zp.read_bytes())==p["archive_sha256"]
def member(path):return "kernel-evidence/"+path.split("kernel-evidence/")[-1]
out=pathlib.Path(p["export_directory"])
def put(rel,data):
    path=out/rel;path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():assert path.read_bytes()==data,str(path)
    else:path.write_bytes(data)
with zipfile.ZipFile(zp) as z:
    names=z.namelist()
    assert len(names)==len(set(names)),"Duplicate ZIP names"
    vr=z.read("kernel-evidence/FULL_REPLAY_VERIFICATION.json");v=json.loads(vr)
    sr=z.read("kernel-evidence/NATIVE_STAGE_REPORT.json");stage=json.loads(sr)
    state=json.loads(z.read("kernel-evidence/RUN_STATUS.json"))
    manifest=v["complete_source_manifest"]
    assert isinstance(manifest,str) and manifest==p["source_manifest"]
    assert H(manifest.encode())==p["source_manifest_sha256"]==v["source_manifest_sha256"]
    rows=manifest.strip().splitlines()
    assert len(rows)==p["source_modules"] and all(re.fullmatch(r"[a-f0-9]{64}  source/.+\.lean",x) for x in rows)
    sources={row[66+7:-5].replace("/","."):row[:64] for row in rows}
    assert len(sources)==p["source_modules"]
    assert v["commit"]==p["commit"] and v["tree"]==p["tree"] and v["run_id"]==p["run_id"]
    assert v["run_attempt"]==int(p["artifact_name"].rsplit("-",1)[1])
    assert v["source_modules"]==v["selected_modules"]==len(sources)
    assert set(state["selected_modules"])==set(sources) and set(state["modules"])==set(sources)
    assert v["compiler_kind"]=="stock_pinned_frontend"
    assert v["mathlib_revision"]=="116662aa4c1e9106ab5c609b3214b02f6e11a65a"
    assert v["runtime_fingerprint"]==p["native_runtime"] and v["runtime_flags"]==p["flags"]
    assert stage["runtime"]==state["runtime"]==p["expected_runtime"]
    assert H(enc(stage["runtime"]))==p["native_runtime"]
    assert json.loads(z.read("runtime-config.json"))==stage["runtime"]["config"]
    assert H(sr)==v["native_stage_report_sha256"]
    assert H(enc(stage["receipts"]))==v["complete_native_receipts_sha256"]
    assert v["frozen_target_sha256"]=="9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296"
    assert v["toolchain_lock_sha256"]=="7f60e90fabda82f0e4e3c3bf4537d24f1298514f116bc18215f162e203f11c19"
    for k in ["source_target_lock_manifest_git_blob_binding_verified","all_accepted_output_log_receipt_dependency_and_recursive_ancestry_hashes_verified","all_final_source_graph_and_runtime_hashes_verified"]:assert v[k] is True,k
    assert v["acceptance_ledger_modified"] is False
    assert not state["final_validation"]["invalidated_modules"] and not state["final_validation"]["changed_runtime_files"]
    raws={n[len("kernel-evidence/receipts/"):-5]:z.read(n) for n in names if n.startswith("kernel-evidence/receipts/") and n.endswith(".json")}
    rs={m:json.loads(b) for m,b in raws.items()}
    good=set(stage["receipts"]);expected=set(p["expected"])
    failed={m for m,s in state["modules"].items() if s["status"] not in ["passed","reused","historical_reuse","blocked"]}
    blocked={m for m,s in state["modules"].items() if s["status"]=="blocked"}
    assert good=={m for m,s in state["modules"].items() if s["status"] in ["passed","reused","historical_reuse"]}
    assert expected<=good and set(rs)==good|failed
    assert len(good)==v["accepted_modules"]==state["final_validation"]["checked_module_count"]
    counts={}
    for s in state["modules"].values():counts[s["status"]]=counts.get(s["status"],0)+1
    assert counts==v["status_counts"]
    assert v["fresh_native_passes"]==counts.get("passed",0) and v["native_receipts_reused"]==counts.get("reused",0)
    assert v["fresh_native_passes"]+v["native_receipts_reused"]==len(good)
    for m,r in rs.items():
        assert r["module"]==m and r["key"]["source_sha256"]==sources[m]
        assert r["key"]["runtime_fingerprint"]==p["native_runtime"] and r["key"]["flags"]==p["flags"]
        assert set(r["key"]["dependency_artifacts"])==set(r["key"]["imports"])
        for k in ["stdout","stderr"]:assert H(z.read(member(r[k])))==r[k+"_sha256"],(m,k)
        parents={}
        for d in r["key"]["imports"]:
            dep=r["key"]["dependency_artifacts"][d]
            if d in sources:
                assert d in good and dep=={"kind":"project","sha256":rs[d]["output_sha256"]},(m,d)
                parents[d]=rs[d]["source_ancestry_fingerprint"]
            else:assert dep=={"kind":"external","sha256":p["expected_external"][d]},(m,d)
        stamp={"module":m,"source_sha256":r["key"]["source_sha256"],"imports":r["key"]["imports"],"dependency_artifacts":r["key"]["dependency_artifacts"],"project_ancestors":parents}
        assert H(enc(stamp))==r["source_ancestry_fingerprint"],m
        output="kernel-evidence/olean/"+m.replace(".","/")+".olean"
        if m in good:
            assert r["status"]=="passed" and r["return_code"]==0 and r["evidence_kind"]=="native_kernel_compilation",m
            assert H(z.read(output))==r["output_sha256"]==state["modules"][m]["output_sha256"],m
            record=stage["receipts"][m]
            assert record["receipt_sha256"]==H(raws[m]) and all(record[k]==value for k,value in fields(r).items()),m
            if m in expected:assert H(enc(fields(r)))==p["expected"][m],m
        else:
            assert r["return_code"]!=0 and output not in names,m
    for m in blocked:assert "kernel-evidence/olean/"+m.replace(".","/")+".olean" not in names,m
    boundary=v["point1_boundary"]
    assert boundary["basis_sha256"]=="b4681aeb45d66ae34215850d7957f4d9a64c04c50470b8c517c796a1347db533"
    assert set(boundary["modules"])==set(p["boundary_expected"]) and len(p["boundary_expected"])==190
    assert boundary["source_and_import_comparisons"]==boundary["native_output_dependency_and_recursive_stamp_comparisons"]==190
    assert boundary["all190_compared_and_unchanged"] is True
    for m,sig in p["boundary_expected"].items():assert m in good and H(enc(fields(rs[m])))==sig,m
    complete=not failed and not blocked and good==set(sources)
    assert v["all_current_sources_kernel_checked"] is complete
    assert stage["summary"]["whole_source_graph_passed"] is complete
    if p["require_full_pass"]:
        assert complete and v["failures"]==[] and state["full_selected_graph_passed"] is True
    for m,source in p["fresh_sources"].items():
        assert H(source.encode())==sources[m],m
        if m not in rs:continue
        put("sources/"+m+".lean",source.encode())
        put("native-receipts/"+m+".json",raws[m])
        for k in ["stdout","stderr"]:put("native-logs/"+m+"."+k,z.read(member(rs[m][k])))
        if m in good:put("native-olean/"+m+".olean",z.read("kernel-evidence/olean/"+m+".olean"))
    put("FULL_REPLAY_VERIFICATION.json",vr)
    put("NATIVE_STAGE_REPORT.json",sr)
    summary={"schema":"lebrun-independent-full-current-native-archive-v1","artifact_id":p["artifact_id"],"artifact_name":p["artifact_name"],"run_id":p["run_id"],"official_archive_sha256":p["archive_sha256"],"source_commit":v["commit"],"source_tree":v["tree"],"source_manifest_sha256":v["source_manifest_sha256"],"source_modules":len(sources),"selected_modules":v["selected_modules"],"accepted_modules":len(good),"fresh_native_passes":v["fresh_native_passes"],"native_receipts_reused":v["native_receipts_reused"],"prior_native_contexts_exactly_matched":len(expected),"point1_native_contexts_exactly_matched":190,"all_current_sources_kernel_checked":complete,"failed_modules":sorted(failed),"blocked_modules":sorted(blocked),"all_native_source_output_log_receipt_runtime_dependency_and_recursive_hashes_verified":True,"full_replay_verification_archive_path":"kernel-evidence/FULL_REPLAY_VERIFICATION.json","full_replay_verification_sha256":H(vr),"complete_native_receipts_sha256":v["complete_native_receipts_sha256"],"native_evidence_not_rewritten":True,"compiler_not_invoked_by_export":True,"acceptance_ledger_modified":False,"fresh_native_receipts":[stage["receipts"][m] for m in sorted(good-expected)],"export_directory":str(out)}
    put("INDEPENDENT_FULL_REPLAY_VERIFICATION.json",(json.dumps(summary,indent=2)+"\n").encode())
    print(json.dumps(summary))
