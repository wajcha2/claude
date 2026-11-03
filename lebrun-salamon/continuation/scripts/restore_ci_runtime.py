#!/usr/bin/env python3
"""Restore pinned Lean/mathlib binaries from existing repository artifacts."""
from pathlib import Path
import argparse, hashlib, json, os, shutil, subprocess, urllib.request

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()

def run(command,**kw):
    subprocess.run(command,check=True,**kw)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--runtime',type=Path,required=True)
    ap.add_argument('--config',type=Path,required=True)
    args=ap.parse_args()
    root=args.runtime.resolve();root.mkdir(parents=True,exist_ok=True)
    download=root/'downloads';download.mkdir(exist_ok=True)
    archive=download/'lean.tar.zst'
    run(['curl','--fail','--location','--retry','5','--retry-all-errors',
         'https://github.com/leanprover/lean4/releases/download/v4.36.0-rc1/lean-4.36.0-rc1-linux.tar.zst',
         '--output',str(archive)])
    assert sha(archive)=='26b3cea1a006ad419215520b8668dcd3f6a9eeba1a123756563a739f9c6274b2'
    lean=root/'toolchain';lean.mkdir(exist_ok=True)
    run(['tar','--no-same-owner','--use-compress-program=unzstd','-xf',str(archive),'-C',str(lean),'--strip-components=1'])
    run([str(lean/'bin/lean'),'--version'])
    archive.unlink()
    artifacts=[(41234129669,'mathlib-cache-*'),(41309680327,'mathlib-full-ir-*'),(41440059394,'mathlib-package-runtime')]
    for run_id,pattern in artifacts:
        dest=download/str(run_id)
        run(['gh','run','download',str(run_id),'--repo','wajcha2/claude','--pattern',pattern,'--dir',str(dest)])

    def unpack_group(group,expected,dest,strip):
        manifests=list(download.rglob(group+'.parts.sha256'))
        assert len(manifests)==1,(group,manifests)
        parts=[]
        for line in manifests[0].read_text().splitlines():
            part_hash,name=line.split()
            found=list(download.rglob(name));assert len(found)==1,(name,found)
            assert sha(found[0])==part_hash,name
            parts.append(found[0])
        combined=download/(group+'.tar.zst')
        with combined.open('wb') as out:
            for part in parts:
                with part.open('rb') as src:shutil.copyfileobj(src,out)
        assert sha(combined)==expected,group
        dest.mkdir(parents=True,exist_ok=True)
        run(['tar','--no-same-owner','--use-compress-program=unzstd','-xf',str(combined),'-C',str(dest),'--strip-components='+str(strip)])
        combined.unlink()
        for part in parts:part.unlink()

    mathlib=root/'mathlib'
    unpack_group('mathlib-cache','69d48979417b59f9e5e01f9659f661f70a6bc17c17678c45395c2459f4ad801e',mathlib,1)
    full_ir=root/'full-ir'
    unpack_group('mathlib-full-ir','fcf02ea9b7380048f6b3c8e82df4ab1d7d4d7d7f3545c3b928199a44dae87982',full_ir,1)
    for name in (full_ir/'packages').iterdir():
        shutil.copytree(name,mathlib/'packages'/name.name,dirs_exist_ok=True)
    package_archive=list(download.rglob('mathlib-package-runtime.tar.zst'))
    assert len(package_archive)==1
    assert sha(package_archive[0])=='4020bbef12b19f9ef87f2a5c15ea21ab2372134ec5e95c5c2b87d1008eba42ff'
    package=root/'package-runtime';package.mkdir(exist_ok=True)
    run(['tar','--no-same-owner','--use-compress-program=unzstd','-xf',str(package_archive[0]),'-C',str(package),'--strip-components=1'])
    libs=package/'.lake/build/lib'
    for path in libs.glob('*.so'):
        target=mathlib/'packages/mathlib/.lake/build/lib'/path.name
        target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(path,target)
    for p in (package/'.lake/packages').iterdir():
        shutil.copytree(p,mathlib/'packages'/p.name,dirs_exist_ok=True)
    pkgs=mathlib/'packages'
    names=['LeanSearchClient','Qq','aesop','batteries','importGraph','mathlib','plausible','proofwidgets']
    order=[('batteries','libbatteries_Batteries.so'),('Qq','libQq_Qq.so'),('aesop','libaesop_Aesop.so'),('proofwidgets','libproofwidgets_ProofWidgets.so'),('LeanSearchClient','libLeanSearchClient_LeanSearchClient.so'),('importGraph','libimportGraph_ImportGraph.so'),('plausible','libplausible_Plausible.so'),('mathlib','libmathlib_Mathlib.so')]
    dylibs=[pkgs/name/'.lake/build/lib'/file for name,file in order]
    assert all(p.is_file() for p in dylibs)
    root_olean=pkgs/'mathlib/.lake/build/lib/lean/Mathlib.olean'
    assert sha(root_olean)=='cf4e1b9c97a496d1a653ac6ebe1abfac5b62e8f6a3e442041b5d8845789e09bf'
    config={
      'command':[str(lean/'bin/lean')]+['--load-dynlib='+str(p) for p in dylibs],
      # The public ubuntu-24.04 runner has 16 GB RAM.  The complete graph
      # exceeds the local 8 GB environment's conservative 7200 MB cap.
      'flags':['--json','-j1','-DElab.async=false','-M12000','-DmaxErrors=1000','-DmaxHeartbeats=2000000'],
      'external_olean_roots':[str(pkgs/n/'.lake/build/lib/lean') for n in names]+[str(lean/'lib/lean')],
      'environment':{'LD_LIBRARY_PATH':':'.join([str(lean/'lib/lean'),str(lean/'lib')]+[str(pkgs/n/'.lake/build/lib') for n in names])},
      'fingerprint_files':[str(lean/'bin/lean'),str(lean/'lib/lean/libleanshared.so'),str(root_olean)]+[str(p) for p in dylibs],
      'compiler_kind':'stock_pinned_frontend',
      'mathlib_revision':'116662aa4c1e9106ab5c609b3214b02f6e11a65a'
    }
    args.config.write_text(json.dumps(config,indent=2)+'\n')
    print(json.dumps({'runtime_config':str(args.config),'restored':True}),flush=True)

if __name__=='__main__':main()
