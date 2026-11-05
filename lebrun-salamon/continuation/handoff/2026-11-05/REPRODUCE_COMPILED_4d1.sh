#!/usr/bin/env bash
# Recovered from .github/workflows/lebrun-3h-continuation-native.yml at 4d1aa547.
# READ/LOCAL-EXECUTION REFERENCE ONLY: not executed by the 2026-11-05 handoff audit.
# Run from a fresh detached worktree at the exact compiled commit.
# This performs a new local reproduction; it does not create a GitHub native run,
# rewrite any historical receipt, or grant acceptance.
set -euo pipefail

test "$(git rev-parse HEAD)" = "4d1aa547453f50736035a91f6fea81d340359143"
test -z "$(git rev-parse --show-prefix)"
export CONTINUATION=lebrun-salamon/continuation
export BASELINE_RECORD="$CONTINUATION/audit/continuation_3h/BASELINE.json"
export CANDIDATE_PLAN="$CONTINUATION/audit/continuation_3h/CANDIDATE_PLAN.json"
# These runtime paths are part of the native cache identity. A relocated runtime
# can compile fresh sources, but cannot silently reuse these native cache keys.
export LEBRUN_NATIVE_TEMP=/home/runner/work/_temp
export LEBRUN_NATIVE_WORKSPACE="$PWD"
# Authenticate gh using your existing authorized Actions-read credentials.
# Do not set GITHUB_RUN_ID/GITHUB_RUN_ATTEMPT to the historical run.
for path in accepted-baseline kernel-evidence lebrun-cache-inputs continuation-evidence runtime-config.json; do
  if test -e "$path"; then
    echo "Use a fresh reproduction worktree; already present: $path" >&2
    exit 1
  fi
done
if test -e "$LEBRUN_NATIVE_TEMP/lebrun-runtime"; then
  echo "This clean-machine recipe expects an absent runtime directory; preserve any existing runtime separately." >&2
  exit 1
fi
mkdir -p "$LEBRUN_NATIVE_TEMP"

# Validate frozen drivers, approved candidate and exact accepted source
git fetch --no-tags --depth=1 origin 80bbb1ce6343260cdba2de6a1d067a3a4e65fd91
python3 "$CONTINUATION/scripts/prepare_continuation.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --materialize --output continuation-evidence/PREFLIGHT.json
python3 "$CONTINUATION/scripts/check_checkpoint.py" --root "$CONTINUATION" --verify-manifest --output-dir diagnostic-static

# Restore exact pinned stock runtime
python3 "$CONTINUATION/scripts/restore_ci_runtime.py" --runtime "$LEBRUN_NATIVE_TEMP/lebrun-runtime" --config "$LEBRUN_NATIVE_WORKSPACE/runtime-config.json"

# Read exact official accepted artifact metadata
gh api repos/wajcha2/claude/actions/artifacts/13353190843 > continuation-evidence/BASELINE_ARTIFACT_METADATA.json

# Download accepted full native artifact (local equivalent of actions/download-artifact@v4)
gh run download 41888465259 --repo wajcha2/claude --name lebrun-final-current-native-41888465259-2 --dir lebrun-cache-inputs/0

# Independently verify every accepted native context
python3 "$CONTINUATION/scripts/prepare_continuation.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --artifact-dir lebrun-cache-inputs/0 --artifact-metadata continuation-evidence/BASELINE_ARTIFACT_METADATA.json --runtime-config runtime-config.json --output continuation-evidence/PREFLIGHT.json

# Read exact official completed continuation metadata
gh api repos/wajcha2/claude/actions/artifacts/13360788893 > continuation-evidence/RESUME_ARTIFACT_METADATA.json

# Download verified current continuation contexts (local equivalent of actions/download-artifact@v4)
gh run download 41902480321 --repo wajcha2/claude --name lebrun-3h-current-native-41902480321-1 --dir lebrun-cache-inputs/1

# Revalidate and preserve exact original native type capture
python3 "$CONTINUATION/scripts/verify_continuation_resume.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline-build lebrun-cache-inputs/0/kernel-evidence --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --runtime-config runtime-config.json --artifact-dir lebrun-cache-inputs/1 --artifact-metadata continuation-evidence/RESUME_ARTIFACT_METADATA.json --phase baseline-audit --baseline-audit-output continuation-evidence/baseline-audit --output continuation-evidence/RESUME_BASELINE_AUDIT_VALIDATION.json

# Restore only exact current reusable contexts
python3 "$CONTINUATION/scripts/restore_replay_cache_union.py" --root "$CONTINUATION" --runtime-config runtime-config.json --inputs "$CONTINUATION/audit/continuation_3h/CURRENT_CACHE_INPUTS.json" --build-dir kernel-evidence

# Require every exact current context before resuming
python3 "$CONTINUATION/scripts/verify_continuation_resume.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline-build lebrun-cache-inputs/0/kernel-evidence --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --runtime-config runtime-config.json --artifact-dir lebrun-cache-inputs/1 --artifact-metadata continuation-evidence/RESUME_ARTIFACT_METADATA.json --phase cache --build-dir kernel-evidence --output continuation-evidence/RESUME_CACHE_VALIDATION.json

# Compile current Part07 ancestors with ordinary limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage part07_parents

# Compile Part07 alone with measured 600-second limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage part07

# Compile current core closure with ordinary limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage core

# Preserve completed core evidence before later work: the local folders are retained; no upload is performed.

# Validate Geometry ancestors with ordinary limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage geometry_parents

# Compile Geometry alone with measured 600-second limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage geometry

# Compile current accepted-root and 3h closure
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage accepted_boundaries

# Preserve completed accepted-root closure before reverse-dependency replay: the local folders are retained; no upload is performed.

# Audit current roots and exact published input types
python3 "$CONTINUATION/scripts/run_continuation_audit.py" --root "$CONTINUATION" --build-dir kernel-evidence --runtime-config runtime-config.json --baseline "$BASELINE_RECORD" --mode current --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --output continuation-evidence/current-audit
python3 "$CONTINUATION/scripts/verify_continuation_boundaries.py" --root "$CONTINUATION" --baseline-root accepted-baseline --build-dir kernel-evidence --baseline-build lebrun-cache-inputs/0/kernel-evidence --runtime-config runtime-config.json --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --baseline-audit continuation-evidence/baseline-audit --current-audit continuation-evidence/current-audit --output continuation-evidence/CURRENT_BOUNDARIES.json

# Compile SmoothDescent ancestors with ordinary limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage smooth_descent_parents

# Compile SmoothDescent alone with measured 600-second limit
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage smooth_descent

# Revalidate the whole current source graph
python3 "$CONTINUATION/scripts/run_continuation_stage.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --runtime-config runtime-config.json --build-dir kernel-evidence --reports continuation-evidence/stages --stage full

# Independently require all current native and boundary evidence
python3 "$CONTINUATION/scripts/finalize_continuation_evidence.py" --root "$CONTINUATION" --baseline-root accepted-baseline --baseline-build lebrun-cache-inputs/0/kernel-evidence --build-dir kernel-evidence --baseline "$BASELINE_RECORD" --plan "$CANDIDATE_PLAN" --preflight continuation-evidence/PREFLIGHT.json --baseline-audit continuation-evidence/baseline-audit --current-audit continuation-evidence/current-audit --runtime-config runtime-config.json --reports continuation-evidence/stages --output continuation-evidence/FULL_CONTINUATION_VERIFICATION.json

# Preserve exact completed or failed continuation evidence: the local folders are retained; no upload is performed.

# Local output: continuation-evidence/FULL_CONTINUATION_VERIFICATION.json
# This new local result is distinct from the historical official acceptance event.
