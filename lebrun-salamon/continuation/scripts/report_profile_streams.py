#!/usr/bin/env python3
"""Print exact preserved profiler streams using timestamped receipt bindings."""
from pathlib import Path
import argparse, hashlib, json

ap = argparse.ArgumentParser()
ap.add_argument("--build-dir", type=Path, required=True)
ap.add_argument("--module", action="append", required=True)
ap.add_argument("--allow-unattempted", action="store_true")
args = ap.parse_args()
build = args.build_dir
for module in args.module:
    if not all(c.isalnum() or c in "._" for c in module):
        raise SystemExit("Invalid module name")
    rp = build / "receipts" / (module + ".json")
    if not rp.is_file():
        if args.allow_unattempted:
            print("PROFILE_RECEIPT_NOT_CREATED " + module, flush=True)
            continue
        raise SystemExit("Missing profile receipt: " + str(rp))
    rec_bytes = rp.read_bytes()
    rec = json.loads(rec_bytes)
    assert rec["module"] == module
    print("PROFILE_RECEIPT " + json.dumps({
        "module": module, "receipt_sha256": hashlib.sha256(rec_bytes).hexdigest(),
        "status": rec["status"], "return_code": rec.get("return_code"),
        "seconds": rec.get("seconds"), "source_sha256": rec["key"]["source_sha256"],
        "output_sha256": rec.get("output_sha256")
    }), flush=True)
    for stream in ("stdout", "stderr"):
        if stream not in rec:
            raise SystemExit("Missing stream binding: " + module + " " + stream)
        p = build / "logs" / Path(rec[stream]).name
        data = p.read_bytes()
        expected = rec[stream + "_sha256"]
        assert hashlib.sha256(data).hexdigest() == expected, str(p)
        print("PROFILE_STREAM_BEGIN " + json.dumps({"module": module, "stream": stream,
              "file": p.name, "sha256": expected}), flush=True)
        print(data.decode("utf-8"), end="", flush=True)
        print("PROFILE_STREAM_END " + module + " " + stream, flush=True)
