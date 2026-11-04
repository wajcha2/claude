#!/usr/bin/env python3
"""Focused corruption controls for exact-current resume and measured stage policy."""
import argparse
import copy
import json
import re
import tempfile
from pathlib import Path
from continuation_support import candidate_plan, digest, read_json, write_json
from continuation_stage_policy import (STAGE_ORDER, build_stages, validate_stages,
                                       load_resume, check_predecessors)
from verify_continuation_resume import check_artifact_and_source, check_runtime, check_contexts


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', type=Path, required=True)
    ap.add_argument('--baseline-root', type=Path, required=True)
    ap.add_argument('--approved-source-plan', type=Path, required=True)
    ap.add_argument('--baseline-native-status', type=Path, required=True)
    ap.add_argument('--workflow', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    root = args.root
    bp = root/'audit/continuation_3h/BASELINE.json'; pp = root/'audit/continuation_3h/CANDIDATE_PLAN.json'
    baseline, plan = read_json(bp), read_json(pp)
    source_plan = read_json(args.approved_source_plan)
    assert all(plan[k] == source_plan[k] for k in source_plan if k not in
               ("status", "dispatch_authorized", "dispatch_scope")), "Approved source handoff changed"
    _, inv, _ = candidate_plan(root, args.baseline_root, baseline, source_plan)
    resume = load_resume(root, plan, inv)
    native = read_json(args.baseline_native_status)
    evidence = read_json(root/resume['independent_verification']['path'])
    records = {**evidence['selected_pass_records'], **evidence['unselected_cache_records']}
    metadata = copy.deepcopy(resume['official_artifact'])
    preflight = {'stage_order': list(STAGE_ORDER), 'stages': build_stages(inv, baseline)}
    results = []
    def passes(name, fn):
        fn(); results.append({'name':name,'passed':True,'expected':'valid'})
    def rejects(name, fn):
        try: fn()
        except (ValueError, AssertionError) as exc:
            results.append({'name':name,'passed':True,'expected':'rejection','reason':str(exc)})
        else: raise AssertionError('Corruption was accepted: '+name)
    passes('exact official metadata and source',lambda:check_artifact_and_source(resume,metadata,inv))
    passes('exact native runtime identity',lambda:check_runtime(native['runtime'],native['runtime_fingerprint'],baseline))
    passes('all105 exact current contexts',lambda:check_contexts(records,resume))
    passes('exact nine-stage graph and caps',lambda:validate_stages(preflight,inv,baseline))
    for key,value in [('id',-1),('digest','sha256:'+'0'*64)]:
        bad=copy.deepcopy(metadata);bad[key]=value
        rejects('altered artifact '+key,lambda bad=bad:check_artifact_and_source(resume,bad,inv))
    bad=copy.deepcopy(metadata);bad['workflow_run']['head_sha']='0'*40
    rejects('wrong artifact commit',lambda:check_artifact_and_source(resume,bad,inv))
    wrong=copy.copy(inv);wrong['sha256']='0'*64
    rejects('altered source snapshot',lambda:check_artifact_and_source(resume,metadata,wrong))
    identity=copy.deepcopy(native['runtime']);identity['config']['flags'].append('-DmaxHeartbeats=4000000')
    rejects('altered native flags',lambda:check_runtime(identity,native['runtime_fingerprint'],baseline))
    rejects('altered runtime fingerprint',lambda:check_runtime(native['runtime'],'0'*64,baseline))
    name=next(iter(records));bad=copy.deepcopy(records);bad.pop(name)
    rejects('missing preserved context',lambda:check_contexts(bad,resume))
    bad=copy.deepcopy(records);bad[name]['output_sha256']='0'*64
    rejects('stale current output context',lambda:check_contexts(bad,resume))
    bad=copy.deepcopy(records);bad['RecompileExtensionsPart04Geometry']=copy.deepcopy(records[name])
    rejects('failed Geometry inserted as eligible',lambda:check_contexts(bad,resume))
    bad=copy.deepcopy(preflight);bad['stages']['accepted_boundaries']['module_timeout_seconds']=600
    rejects('ordinary stage receives longer cap',lambda:validate_stages(bad,inv,baseline))
    bad=copy.deepcopy(preflight);bad['stages']['geometry']['module_timeout_seconds']=900
    rejects('isolated cap exceeds authorization',lambda:validate_stages(bad,inv,baseline))
    bad=copy.deepcopy(preflight);bad['stage_order'][3],bad['stage_order'][4]=bad['stage_order'][4],bad['stage_order'][3]
    rejects('isolated target precedes parents',lambda:validate_stages(bad,inv,baseline))
    bad=copy.deepcopy(preflight);bad['stages']['geometry']['targets'].append('LSFamilySmoothDescent')
    rejects('second target inherits longer cap',lambda:validate_stages(bad,inv,baseline))
    bad=copy.deepcopy(preflight);bad['stages']['geometry_parents']['selected'].pop()
    rejects('missing ancestor in isolation stage',lambda:validate_stages(bad,inv,baseline))
    with tempfile.TemporaryDirectory() as folder:
        reports=Path(folder)
        rejects('missing predecessor report',lambda:check_predecessors('geometry',reports,digest(pp),digest(bp),inv['sha256']))
        previous={}
        for stage in STAGE_ORDER[:STAGE_ORDER.index('geometry')]:
            report={'stage':stage,'return_code':0,'full_selected_graph_passed':True,'errors':[],
                    'candidate_plan_sha256':digest(pp),'baseline_record_sha256':digest(bp),
                    'source_manifest_sha256':inv['sha256'],'completed_predecessor_report_sha256':dict(previous)}
            path=reports/(stage+'.json');write_json(path,report);previous[stage]=digest(path)
        passes('exact predecessor report chain',lambda:check_predecessors('geometry',reports,digest(pp),digest(bp),inv['sha256']))
        path=reports/'geometry_parents.json';bad=read_json(path);bad['return_code']=124;write_json(path,bad)
        rejects('failed predecessor blocks isolation',lambda:check_predecessors('geometry',reports,digest(pp),digest(bp),inv['sha256']))
    stages=re.findall(r'--stage ([A-Za-z0-9_]+)',args.workflow.read_text())
    assert stages==STAGE_ORDER,('workflow stage order differs',stages)
    results.append({'name':'actual workflow follows reviewed stage order','passed':True,'expected':'valid'})
    out={'schema':'lebrun-continuation-resume-controls-v1','source_manifest_sha256':inv['sha256'],
         'source_modules':len(inv['sources']),'candidate_plan_sha256':digest(pp),'approved_source_plan_sha256':digest(args.approved_source_plan),
         'resume_record_sha256':plan['resume_record']['sha256'],'workflow_sha256':digest(args.workflow),
         'controls':results,'all_passed':True,'native_compiler_invoked':False,'new_units_credited':0}
    write_json(args.output,out)
    print(json.dumps({'controls':len(results),'all_passed':True,'output':str(args.output),'sha256':digest(args.output)}))


if __name__=='__main__':
    main()
