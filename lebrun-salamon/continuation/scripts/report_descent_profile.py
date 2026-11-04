from pathlib import Path
import hashlib,json
names=["LSModelDifferentialFlushSmoke","LSFamilyDescentProfilePrefix"]
for name in names:
    p=Path("kernel-evidence/receipts")/(name+".json")
    if not p.exists():
        print("PROFILE_RESULT "+json.dumps({"module":name,"status":"no_receipt","scope":"diagnostic_prefix_only"}),flush=True)
        continue
    r=json.loads(p.read_text())
    print("PROFILE_RESULT "+json.dumps({"module":name,"status":r.get("status"),"return_code":r.get("return_code"),"seconds":r.get("seconds"),"source_sha256":r["key"]["source_sha256"],"receipt_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"scope":"diagnostic_prefix_only_not_original_Descent"}),flush=True)
    for stream in ["stdout","stderr"]:
        q=Path(r[stream])
        print("PROFILE_STREAM_BEGIN "+json.dumps({"module":name,"stream":stream,"sha256":hashlib.sha256(q.read_bytes()).hexdigest()}),flush=True)
        print(q.read_text(),flush=True)
        print("PROFILE_STREAM_END "+json.dumps({"module":name,"stream":stream}),flush=True)
