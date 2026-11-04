#!/usr/bin/env python3
"""Verify original stock evidence for relocated local diagnostic imports."""
from pathlib import Path
import hashlib,json,shutil,sys,datetime
BASE=Path('/workspace/scratch/4deac2cdddbb/lebrun_recovery')
ROOT=BASE/'source-checkpoint'
ART=BASE/'runtime/downloads/13316275024'
OUT=BASE/'verified-native'
RUNTIME=BASE/'runtime'
sys.path.insert(0,str(ROOT/'scripts'))
from replay_checkpoint import digest,source_graph,dependency_order,source_ancestry_fingerprint
from restore_replay_cache import validated_unselected_cache,unselected_binding_errors
def read(p):return json.loads(p.read_text())
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def main():
    if OUT.exists() and any(OUT.iterdir()):raise SystemExit('Use an empty diagnostic import pool.')
    assert digest(ART.with_suffix('.zip'))=='699441074ffac022244fa4d28b4a7bf6a53e5a2e85fd13279ddeb66ad2fd3f4f'
    native=ART/'kernel-evidence'
    status=read(native/'RUN_STATUS.json')
    identity=status['runtime']
    fp=hashlib.sha256(json.dumps(identity,sort_keys=True).encode()).hexdigest()
    assert fp==status['runtime_fingerprint']=='9387025ac24e8fbfc8c41c101ebb879f2345074bbb8683f5b65951d1f5cb8004'
    cfg=identity['config']
    assert cfg['compiler_kind']=='stock_pinned_frontend'
    assert cfg['flags']==['--json','-j1','-DElab.async=false','-M12000','-DmaxErrors=1000','-DmaxHeartbeats=2000000']
    assert read(ART/'runtime-config.json')==cfg
    assert digest(ROOT/'TOOLCHAIN.lock.json')==identity['toolchain_lock_sha256']=='7f60e90fabda82f0e4e3c3bf4537d24f1298514f116bc18215f162e203f11c19'
    assert digest(ROOT/'target/MainStatement.lean')=='9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296'
    prefix=Path('/home/runner/work/_temp/lebrun-runtime')
    mapped={}
    for old,h in identity['fingerprint_files'].items():
        path=RUNTIME/Path(old).relative_to(prefix)
        assert digest(path)==h,(old,h)
        mapped[old]={'local_path':str(path),'sha256':h}
    external=[RUNTIME/Path(p).relative_to(prefix) for p in cfg['external_olean_roots']]
    full=read(native/'FULL_REPLAY_VERIFICATION.json')
    manifest=full['complete_source_manifest']
    assert hashlib.sha256(manifest.encode()).hexdigest()==full['source_manifest_sha256']=='7867c5ad65b40a07545dbde03451ebd312d98b399935c4e083c5da5c5adf2ae7'
    expected={}
    for line in manifest.splitlines():
        h,p=line.split()
        assert digest(ROOT/p)==h,p
        expected[p]=h
    sources,imports,graph=source_graph(ROOT/'source')
    actual={str(p.relative_to(ROOT)):digest(p) for p in sources.values()}
    assert actual==expected and len(sources)==291
    assert full['commit']=='e79a5a00d5019e277f158be5bbe0cf690d11d618'
    order,cycles=dependency_order(graph);assert not cycles
    cache,rejection=validated_unselected_cache(read(native/'CACHE_RESTORE.json'),fp)
    assert rejection is None,rejection
    good={};ancestry={};receipts={};blocked={}
    for m in order:
        sm=status['modules'].get(m)
        cached_only=sm is None
        if cached_only:
            if m not in cache:continue
        elif sm.get('status') not in {'passed','reused'}:
            continue
        rp=native/'receipts'/(m+'.json');r=read(rp)
        assert r['schema']=='lebrun-module-receipt-v1' and r['module']==m
        assert r['status']=='passed' and r['return_code']==0 and r['evidence_kind']=='native_kernel_compilation'
        if cached_only:assert not unselected_binding_errors(cache[m],r),m
        deps={}
        for dep in imports[m]:
            rel=Path(*dep.split('.')).with_suffix('.olean')
            if dep in sources:
                assert dep in good,(m,dep,'unvalidated project ancestor')
                deps[dep]={'sha256':good[dep],'kind':'project'}
            else:
                p=next((base/rel for base in external if (base/rel).is_file()),None)
                assert p is not None,(m,dep,'missing external import')
                deps[dep]={'sha256':digest(p),'kind':'external'}
        key={'source_sha256':digest(sources[m]),'imports':imports[m],'dependency_artifacts':deps,'runtime_fingerprint':fp,'flags':cfg['flags']}
        assert r['key']==key,(m,'key')
        stamp=source_ancestry_fingerprint(m,key,{dep:ancestry[dep] for dep in graph[m]})
        assert r['source_ancestry_fingerprint']==stamp,(m,'ancestry')
        if not cached_only:assert sm['output_sha256']==r['output_sha256'],m
        p=native/'olean'/Path(*m.split('.')).with_suffix('.olean')
        assert digest(p)==r['output_sha256'],m
        for stream in ['stdout','stderr']:
            log=native/'logs'/Path(r[stream]).name
            assert digest(log)==r[stream+'_sha256'],(m,stream)
        good[m]=r['output_sha256'];ancestry[m]=stamp;receipts[m]=r
    assert len(good)==280,len(good)
    basis=ROOT/'audit/ci/41763014879/point1/VALIDATED_SEEDS.json'
    assert digest(basis)=='b4681aeb45d66ae34215850d7957f4d9a64c04c50470b8c517c796a1347db533'
    boundary=full['point1_boundary']
    assert boundary['basis_sha256']==digest(basis)
    # Boundary identity is also bound by each original native key and recursive stamp.
    seeds=read(basis)['modules'];assert len(seeds)==190
    for m,seed in seeds.items():
        assert m in good,m
        if 'source_sha256' in seed:assert seed['source_sha256']==receipts[m]['key']['source_sha256'],m
        if 'output_sha256' in seed:assert seed['output_sha256']==good[m],m
        assert seed['imports']==receipts[m]['key']['imports'],m
        assert seed['dependency_artifacts']==receipts[m]['key']['dependency_artifacts'],m
        assert seed['source_ancestry_fingerprint']==ancestry[m],m
        assert seed['toolchain_lock_sha256']==identity['toolchain_lock_sha256'],m
    records={}
    for m in good:
        rel=Path(*m.split('.')).with_suffix('.olean')
        target=OUT/'olean'/rel;target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(native/'olean'/rel,target)
        assert digest(target)==good[m],m
        records[m]={'source_sha256':receipts[m]['key']['source_sha256'],'output_sha256':good[m],'native_receipt_sha256':digest(native/'receipts'/(m+'.json')),'source_ancestry_fingerprint':ancestry[m]}
    assert {str(p.relative_to(ROOT)):digest(p) for p in sources.values()}==actual
    for old,item in mapped.items():assert digest(Path(item['local_path']))==item['sha256'],old
    result={'schema':'lebrun-relocated-stock-import-pool-v1','checked_utc':now(),'validation_passed':True,'purpose':'Verified stock outputs used only as imports for separate local diagnostics; no stock runtime claim for local execution.','source_commit':full['commit'],'source_manifest_sha256':full['source_manifest_sha256'],'source_count':291,'module_count':len(good),'original_boundary_contexts':len(seeds),'stock_runtime_fingerprint':fp,'original_runtime_bytes_mapped':mapped,'native_artifact_id':13316275024,'native_artifact_sha256':'699441074ffac022244fa4d28b4a7bf6a53e5a2e85fd13279ddeb66ad2fd3f4f','modules':records,'kernel_invoked':False,'acceptance_ledger_modified':False}
    (OUT/'IMPORT_POOL_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['validation_passed','source_count','module_count','original_boundary_contexts','stock_runtime_fingerprint','kernel_invoked']}))
if __name__=='__main__':main()
