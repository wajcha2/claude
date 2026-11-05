#!/usr/bin/env python3
"""Verify the preserved LeBrun--Salamon snapshot and added handoff files.

Run from any directory after cloning/extracting the handoff snapshot:
    python3 PATH/TO/verify_handoff.py --root REPOSITORY_ROOT
This checks file content only; it does not run Lean or confer proof acceptance.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def checked_path(root: Path, relative: str) -> Path:
    rel = Path(relative)
    if rel.is_absolute() or ".." in rel.parts:
        raise ValueError(f"Unsafe manifest path: {relative}")
    path = (root / rel).resolve()
    if not path.is_relative_to(root):
        raise ValueError(f"Manifest path escapes repository: {relative}")
    return path


def digest_file(path: Path, algorithm: str, git_blob: bool = False) -> str:
    h = hashlib.new(algorithm)
    if git_blob:
        h.update(f"blob {path.stat().st_size}\0".encode("ascii"))
    with path.open("rb") as stream:
        while chunk := stream.read(1024 * 1024):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True, help="Repository root, not continuation/")
    args = parser.parse_args()
    root = args.root.resolve()
    here = Path(__file__).resolve().parent
    inventory = json.loads((here / "BASE_INVENTORY.json").read_text(encoding="utf-8"))
    failures = []
    checked = 0
    total_bytes = 0
    for item in inventory["files"]:
        rel = item["path"]
        try:
            path = checked_path(root, rel)
            if not path.is_file():
                raise ValueError("missing regular file")
            size = path.stat().st_size
            if size != item["bytes"]:
                raise ValueError(f"size {size} != {item['bytes']}")
            actual = digest_file(path, "sha1", git_blob=True)
            if actual != item["git_blob"]:
                raise ValueError(f"Git blob {actual} != {item['git_blob']}")
            checked += 1
            total_bytes += size
        except (OSError, ValueError) as exc:
            failures.append({"path": rel, "error": str(exc)})
    handoff_checked = 0
    for line in (here / "HANDOFF_FILES.sha256").read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        expected, rel = line.split("  ", 1)
        try:
            path = checked_path(root, rel)
            actual = digest_file(path, "sha256")
            if actual != expected:
                raise ValueError(f"SHA-256 {actual} != {expected}")
            handoff_checked += 1
        except (OSError, ValueError) as exc:
            failures.append({"path": rel, "error": str(exc)})
    print(json.dumps({
        "accepted_commit": inventory["accepted_commit"],
        "base_files_verified": checked,
        "base_files_expected": len(inventory["files"]),
        "base_bytes_verified": total_bytes,
        "handoff_files_verified": handoff_checked,
        "failures": failures,
        "pass": not failures,
        "scope": "Content-integrity verification only; not a Lean run or new acceptance."
    }, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
