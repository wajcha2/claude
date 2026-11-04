from pathlib import Path
import json
p=Path("kernel-evidence/receipts/LSModelDifferentialFlushSmoke.json")
r=json.loads(p.read_text())
s=Path(r["stderr"]).read_text()
marker="MODEL_DIFFERENTIAL_FLUSH_SMOKE_RAW_STDERR"
assert r.get("return_code")==0, r
assert marker in s, "Native smoke succeeded but no actual raw-stderr marker was preserved"
print("PROFILE_SMOKE_GATE "+json.dumps({"passed":True,"source_sha256":r["key"]["source_sha256"],"raw_stderr_marker":marker}),flush=True)
