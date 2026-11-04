from pathlib import Path
import sys,json,hashlib
base=Path('/workspace/scratch/4deac2cdddbb')
root=base/'lebrun_takeover/continuation'
sys.path.insert(0,str(root/'scripts'))
from replay_checkpoint import source_graph,dependency_order,source_ancestry_fingerprint,digest,utc
inputs=[base/'github_checkpoint_audit/ci_41769360325/CURRENT_LIVE_SEEDS_V2.json',base/'github_checkpoint_audit/conic_current_20261104T042633/SEEDS_V2.json',root/'audit/scaled_branch_compatibility/current_20261104T043610/CURRENT_BRANCH_SEEDS_V2.json']
fields=['source_sha256','imports','dependency_artifacts','toolchain_lock_sha256','output_sha256','source_ancestry_fingerprint']
seeds={};alternative_outputs=[]
for p in inputs:
 d=json.loads(p.read_text()); assert d['schema']=='lebrun-explicit-validated-seeds-v2'
 for m,e in d['modules'].items():
  if m in seeds:
   differences=[k for k in fields if seeds[m][k]!=e[k]]
   assert differences in ([],['output_sha256']), (m,differences)
   if differences: alternative_outputs.append({'module':m,'old_output':seeds[m]['output_sha256'],'selected_output':e['output_sha256'],'selected_inventory':str(p)})
  seeds[m]=e
rp=base/'github_checkpoint_audit/conic_current_20261104T042633/build/receipts/LSConicJets.json'
r=json.loads(rp.read_text()); assert r['status']=='passed' and r['return_code']==0 and r['source_and_dependencies_unchanged']
for stream in ['stdout','stderr']: assert digest(Path(r[stream]))==r[stream+'_sha256']
out=Path(r['command'][r['command'].index('-o')+1]); assert digest(out)==r['output_sha256']
k=r['key']; seeds['LSConicJets']={'source_sha256':k['source_sha256'],'imports':k['imports'],'dependency_artifacts':k['dependency_artifacts'],'toolchain_lock_sha256':digest(root/'TOOLCHAIN.lock.json'),'artifact_path':str(out),'output_sha256':r['output_sha256'],'source_ancestry_fingerprint':r['source_ancestry_fingerprint'],'provenance':{'kind':'exact_native_current_conic_whole_module','receipt':str(rp),'receipt_sha256':digest(rp),'source_snapshot':str(base/'github_checkpoint_audit/conic_current_20261104T042633')}}
sources,imports,graph=source_graph(root/'source'); order,cycles=dependency_order(graph); assert not cycles
cfg=json.loads((base/'github_checkpoint_audit/conic_current_20261104T042633/runtime-config.json').read_text()); external_roots=[Path(x) for x in cfg['external_olean_roots']]
accepted={};checked_external={}
for m in order:
 if m not in seeds: continue
 e=seeds[m]
 assert digest(sources[m])==e['source_sha256'],('source',m)
 assert imports[m]==e['imports'],('imports',m)
 assert digest(Path(e['artifact_path']))==e['output_sha256'],('output',m)
 assert e['toolchain_lock_sha256']==digest(root/'TOOLCHAIN.lock.json'),('lock',m)
 assert set(e['dependency_artifacts'])==set(imports[m]),('imports/artifacts',m)
 for d in imports[m]:
  de=e['dependency_artifacts'][d]
  if d in sources:
   assert d in accepted,('missing ancestry',m,d)
   assert de=={'kind':'project','sha256':accepted[d]['output_sha256']},('dependency',m,d)
  else:
   if d not in checked_external:
    rel=Path(*d.split('.')).with_suffix('.olean'); p=next((x/rel for x in external_roots if (x/rel).is_file()),None)
    assert p is not None,('external missing',d)
    checked_external[d]=digest(p)
   assert de=={'kind':'external','sha256':checked_external[d]},('external',m,d)
 assert source_ancestry_fingerprint(m,e,{d:accepted[d]['source_ancestry_fingerprint'] for d in graph[m]})==e['source_ancestry_fingerprint'],('ancestry stamp',m)
 accepted[m]=e
assert len(accepted)==247,(len(accepted),set(seeds)-set(accepted)); assert len(sources)==269
result={'schema':'lebrun-explicit-validated-seeds-v2','validated_utc':utc(),'module_count':len(accepted),'current_source_module_count':len(sources),'validation':'Union of independently validated exact GitHub full-graph outputs and current native Conic/helper/smoothing outputs. Every live source, import list, artifact byte hash, pinned lock, project/external dependency output and recursive project-ancestry stamp was rechecked. This does not claim remaining reverse-cone acceptance.','inputs':[{'path':str(p),'sha256':digest(p)} for p in inputs]+[{'path':str(rp),'sha256':digest(rp)}],'external_modules_checked':len(checked_external),'alternative_output_selection':alternative_outputs,'modules':accepted}
p=base/'github_checkpoint_audit/CURRENT_COMPATIBLE_SEEDS_20261104T0439_V2.json'; p.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'path':str(p),'sha256':digest(p),'validated_modules':len(accepted),'live_modules':len(sources),'external_modules_checked':len(checked_external),'remaining_modules':sorted(set(sources)-set(accepted))}))
