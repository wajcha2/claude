#!/usr/bin/env python3
"""Bounded local diagnostics; never creates stock native acceptance receipts."""
from pathlib import Path
import argparse,datetime,fcntl,hashlib,json,os,re,signal,subprocess,sys,time
BASE=Path('/workspace/scratch/4deac2cdddbb')
REC=BASE/'lebrun_recovery'
CFG=REC/'runtime/runtime-config-local-diagnostic.json'
POOL=REC/'verified-native/olean'
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for b in iter(lambda:f.read(1048576),b''):h.update(b)
    return h.hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('source',type=Path)
    ap.add_argument('--timeout',type=float,default=90)
    ap.add_argument('--extra',type=Path,action='append',default=[])
    args=ap.parse_args()
    src=args.source.resolve()
    module=src.stem
    cfg=json.loads(CFG.read_text())
    assert cfg['compiler_kind']=='stock_pinned_frontend_with_explicit_own_executable_path'
    assert '-M7200' in cfg['flags'] and '-DElab.async=false' in cfg['flags']
    native=json.loads((REC/'verified-native/IMPORT_POOL_VALIDATION.json').read_text())
    assert native['validation_passed'] is True and native['stock_runtime_fingerprint']=='9387025ac24e8fbfc8c41c101ebb879f2345074bbb8683f5b65951d1f5cb8004'
    lock=(REC/'local-lean.lock').open('a')
    fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    sys.path.insert(0,str(REC/'source-checkpoint/scripts'))
    from check_checkpoint import strip_noncode
    code=strip_noncode(src.read_text())
    if re.search(r'\b(sorry|admit|axiom)\b',code):
        raise SystemExit('This zero-new-admission diagnostic runner refuses admissions in its test source.')
    imports=[w for line in re.findall(r'(?m)^(?:public\s+)?import\s+([^\n]+)',code) for w in line.split()]
    extras=[p.resolve() for p in args.extra]
    roots=[*extras,POOL,*map(Path,cfg['external_olean_roots'])]
    depfiles={}
    for m in imports:
        rel=Path(*m.split('.')).with_suffix('.olean')
        found=next((p/rel for p in roots if (p/rel).is_file()),None)
        if found is None:raise SystemExit('Missing direct diagnostic import '+m)
        depfiles[str(found)]=sha(found)
    expected={str(POOL/Path(*m.split('.')).with_suffix('.olean')):v['output_sha256'] for m,v in native['modules'].items()}
    for p,h in expected.items():
        if sha(p)!=h:raise SystemExit('Verified native diagnostic import changed: '+p)
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%f')
    out=BASE/'root_diagnostics/runs'/(stamp+'-'+module);out.mkdir(parents=True)
    artifact=out/(module+'.olean')
    stdout=out/'stdout.jsonl';stderr=out/'stderr.log'
    frozen=[src,CFG,Path(__file__).resolve(),REC/'verified-native/IMPORT_POOL_VALIDATION.json',*map(Path,cfg['fingerprint_files'])]
    def inventory():
        d={str(p):sha(p) for p in frozen}
        for r in [POOL,*extras]:
            for p in sorted(r.rglob('*.olean')):d[str(p)]=sha(p)
        d.update({p:sha(p) for p in depfiles})
        return d
    before=inventory()
    env=os.environ.copy();env.update(cfg.get('environment',{}))
    env['LEAN_PATH']=os.pathsep.join(map(str,roots))
    cmd=['/usr/bin/stdbuf','-o0','-e0',*cfg['command'],*cfg['flags'],'--root='+str(src.parent),'-o',str(artifact),str(src)]
    started=datetime.datetime.now(datetime.timezone.utc).isoformat()
    tick=time.monotonic()
    timed_out=False
    with stdout.open('wb') as so,stderr.open('wb') as se:
        proc=subprocess.Popen(cmd,stdout=so,stderr=se,env=env,cwd=src.parent,start_new_session=True)
        try:rc=proc.wait(timeout=args.timeout)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(proc.pid,signal.SIGKILL);proc.wait();rc=124
    elapsed=time.monotonic()-tick
    after=inventory()
    errors=[];messages=[]
    for line in stdout.read_text(errors='replace').splitlines():
        try:
            item=json.loads(line)
            if isinstance(item,dict):
                messages.append(item)
                if item.get('severity')=='error':errors.append(item)
        except ValueError:pass
    stable=before==after
    passed=rc==0 and not errors and stable and artifact.is_file()
    receipt={
      'schema':'lebrun-local-bounded-diagnostic-v2','scope':'Local diagnostic only; never stock native acceptance',
      'module':module,'source':str(src),'source_sha256':before[str(src)],
      'runtime_config':str(CFG),'runtime_config_sha256':before[str(CFG)],
      'compiler_kind':cfg['compiler_kind'],'flags':cfg['flags'],
      'started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'seconds':round(elapsed,3),'timeout_seconds':args.timeout,'timed_out':timed_out,
      'return_code':rc,'emitted_error_count':len(errors),'complete_success':passed,
      'all_source_runtime_and_import_hashes_unchanged':stable,
      'command':cmd,'direct_import_artifacts':depfiles,
      'input_fingerprint_before':before,'input_fingerprint_after':after,
      'stdout':str(stdout),'stdout_sha256':sha(stdout),
      'stderr':str(stderr),'stderr_sha256':sha(stderr),
      'output':str(artifact),'output_sha256':sha(artifact) if artifact.is_file() else None,
      'native_acceptance_ledger_modified':False
    }
    receipt_path=out/'receipt.json'
    receipt_path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({k:receipt[k] for k in ['module','source_sha256','seconds','return_code','emitted_error_count','complete_success','all_source_runtime_and_import_hashes_unchanged','output','output_sha256']}),flush=True)
    print('RECEIPT '+str(receipt_path),flush=True)
    for e in errors[:5]:print(json.dumps(e),flush=True)
    for line in stderr.read_text(errors='replace').splitlines():
        if '_STAGE ' in line or '_COMPLETE' in line or 'total time:' in line:print(line,flush=True)
    return 0 if passed else (rc or 1)
if __name__=='__main__':raise SystemExit(main())
