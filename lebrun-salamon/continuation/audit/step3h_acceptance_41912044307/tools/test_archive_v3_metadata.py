#!/usr/bin/env python3
"""Focused controls for the one observed optional metadata field."""
import base64
import copy
import hashlib
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OUT = HERE / 'continuation_3h_archive/41912044307/boundary13364047897'
spec = importlib.util.spec_from_file_location('archive_v3', HERE / 'verify_continuation_archive_v3.py')
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
record = json.loads((OUT / 'ARTIFACT_METADATA_REPRESENTATION_DIFFERENCE.json').read_text())
actual, expected = record['actual'], record['expected']
results = []
def check(name, a, e, should_pass):
    try:
        passed = v.same_artifact_metadata(a, e)
    except (ValueError, TypeError, KeyError):
        passed = False
    assert passed is should_pass, name
    results.append({'case':name, 'expected':should_pass, 'observed':passed})

check('exact real runner and connector metadata', actual, expected, True)
check('both representations omit optional identifier', expected, expected, True)
check('both representations carry correct identifier', actual, actual, True)
check('only expected representation carries correct identifier', expected, actual, True)
for name, node in [
    ('wrong encoded artifact ID', base64.b64encode(b'08:Artifact13360788894').decode()),
    ('wrong decoded object type', base64.b64encode(b'08:Repository13360788893').decode()),
    ('invalid base64', 'not!base64'),
    ('noncanonical padding', actual['node_id'] + '='),
    ('wrong JSON type', 13360788893),
    ('null identifier', None),
    ('empty identifier', '')]:
    bad = copy.deepcopy(actual); bad['node_id'] = node
    check(name, bad, expected, False)
    check(name + ' on expected side', expected, bad, False)
bad = copy.deepcopy(actual); bad['unexpected_field'] = 'not authorized'
check('other extra key', bad, expected, False)
bad = copy.deepcopy(actual); del bad['name']
check('missing mandatory field', bad, expected, False)
bad = copy.deepcopy(actual); bad['digest'] = 'sha256:' + '0' * 64
check('changed archive digest', bad, expected, False)
bad = copy.deepcopy(actual); bad['workflow_run']['head_sha'] = '0' * 40
check('changed source commit', bad, expected, False)
bad = copy.deepcopy(actual); bad['expired'] = 0
check('non-node JSON type change', bad, expected, False)
out = {'schema':'lebrun-archive-v3-focused-metadata-controls-v1',
       'verifier_sha256':hashlib.sha256((HERE/'verify_continuation_archive_v3.py').read_bytes()).hexdigest(),
       'previous_verifier_sha256':hashlib.sha256((HERE/'verify_continuation_archive_v2.py').read_bytes()).hexdigest(),
       'difference_sha256':hashlib.sha256((OUT/'ARTIFACT_METADATA_REPRESENTATION_DIFFERENCE.json').read_bytes()).hexdigest(),
       'controls':results, 'all_controls_passed':True, 'compiler_invoked':False,
       'source_runtime_workflow_modified':False}
(OUT/'ARCHIVE_V3_METADATA_CONTROLS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'controls_passed':len(results), 'verifier_sha256':out['verifier_sha256'],
                  'previous_verifier_sha256':out['previous_verifier_sha256']}))
