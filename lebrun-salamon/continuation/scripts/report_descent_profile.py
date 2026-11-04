from pathlib import Path
import hashlib,json
p=Path("kernel-evidence/receipts/LSFamilyDescentProfilePrefix.json")
if not p.exists():
    print("PROFILE_RESULT "+json.dumps({"status":"no_receipt"}))
else:
    r=json.loads(p.read_text())
    print("PROFILE_RESULT "+json.dumps({"status":r.get("status"),"return_code":r.get("return_code"),"seconds":r.get("seconds"),"source_sha256":r["key"]["source_sha256"],"receipt_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"scope":"diagnostic_prefix_only_not_original_Descent"}))
    for stream in ["stdout","stderr"]:
        q=Path(r[stream])
        print("PROFILE_"+stream.upper()+"_BEGIN",flush=True)
        print(q.read_text(),flush=True)
        print("PROFILE_"+stream.upper()+"_END",flush=True)
