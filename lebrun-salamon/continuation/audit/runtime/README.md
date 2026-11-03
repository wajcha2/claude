# Pinned runtime restoration

The recovered Lean 4.36.0-rc1 runtime and mathlib commit `116662aa4c1e9106ab5c609b3214b02f6e11a65a` successfully compiled the preserved `SmokeMathlib.lean` source with the stock Lean frontend. The return code was 0 and an output `.olean` was produced. The simple `False` smoke test was rejected. These are runtime checks, not acceptance of the LeBrun–Salamon proof.

`RESTORE_RECEIPT.json` records archive provenance, SHA-256 fingerprints, the successful smoke output and the local execution qualification. Large binaries are recovered using `../../scripts/restore_ci_runtime.py`; they are deliberately absent from this evidence directory. The eight package libraries and full IR are required by this mathlib cache.

## Local executable discovery adapter

The workspace prevents Lean's normal own-executable-path discovery through `/proc/<numeric-pid>/exe`. `explicit_exec_path.c` supplies an explicitly configured absolute executable path for that exact query by the current process. It does not read the restricted path. Every other `readlink` call retains libc behavior. The compiler executable, shared libraries, kernel and sources remain the pinned bytes. The adapter does not alter proof checking.

Build the adapter with the command recorded in the receipt. Replace `${RUNTIME}` in `runtime-config.template.json` with the restored runtime root, then provide that configuration to `../../scripts/replay_checkpoint.py`. The environment sets `LEAN_EXPLICIT_EXECUTABLE` to the pinned Lean path and `LD_PRELOAD` to the compiled adapter. Normal GitHub CI uses the stock executable without this adapter.

The attempted embedded frontend `lean-explicit-root` is abandoned and must not be used as proof evidence. Only the stock frontend configuration described here is validated. Use one heavy compiler process at a time in this 8 GiB workspace. `-M5400` exhausted Lean's memory allowance for a plain Mathlib import; the successful configuration uses `-M7200`.

## Replay bookkeeping regression check

A simulated compiler fixture invokes no Lean process and provides no proof evidence. It exercises the replay driver's cache and failure bookkeeping. Before the repair, 10 of 12 cases passed: edits to an ancestor source or an external artifact during descendant compilation were incorrectly accepted as a complete current snapshot. After adding final source, import, output, dependency and runtime checks with transitive invalidation, all 12 cases passed. Invalidated outputs are removed from the active import path.

`replay_fixture_before.json` and `replay_fixture_after.json` preserve the exact observations and tested driver hashes. Reproduce the fixture using a fresh workspace directory:

```sh
python audit/runtime/replay_fixture.py --workspace /tmp/lebrun-replay-fixture --output /tmp/lebrun-replay-fixture.json
```
