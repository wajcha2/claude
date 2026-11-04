# Continuation gate for Step 3h

## Scope

This infrastructure continues from accepted commit
bd3524b4bb12ac73cbf7572698208b017071b699 and the exact native source snapshot
80bbb1ce6343260cdba2de6a1d067a3a4e65fd91. It preserves the historical Point 1
report, source boundary and acceptance event. It does not edit the original
replay driver, cache restorers, runtime recipe, historical reporter or ledger.

The accepted ledger remains **74 of 133**. The proposed next original
obligations are OBL-044 through OBL-048. New helper declarations and modules
receive no progress credit. A successful workflow emits reviewable evidence;
independent review of the five new native published-input types and official
artifact metadata must still precede a separate acceptance event.

The initial combined handoff changes RecompileBasePart06 and
RecompileExtensionsPart02 and adds LSChartSmoothnessCriteria. Every module
count, ancestor closure, affected reverse-dependency set and root selection is
recomputed from that exact source inventory. Counts are not encoded in the
workflow as 307, 308, 36 or 190.

## Trigger and authorization

The infrastructure branch is codex/lebrun-3h-infrastructure-20261104. It is
excluded from the workflow trigger. The only trigger is a push to
codex/lebrun-3h-native-20261104.

CANDIDATE_PLAN.json initially has awaiting_complete_candidate_handoff status and
dispatch_authorized=false. Preflight rejects it before runtime restoration or
compiler execution. After the full handoff, exact source guards and independent
reviews are approved, a single combined source/infrastructure/plan commit can
advance the native branch. Creating that branch at the accepted baseline first
does not contain this workflow. The infrastructure commit alone must never be
pushed to the native branch.

## Native workflow

The job has a 120-minute wall-clock bound. It restores the unchanged pinned
stock runtime and exact accepted native artifact13353190843 from
run41888465259 attempt2. The official metadata must match its id, name, run,
size and SHA256 digest. Extracted receipt, source, output, log, runtime and
recursive dependency bindings are independently revalidated for every accepted
module. The prior independently verified ZIP digest remains historical evidence;
an action's extracted directory is not falsely reported as a newly hash-checked
ZIP.

Before rebuilding candidate sources, an isolated native audit captures the
complete printed types and universe parameters of the five original3h roots,
all44 accepted roots, and the50 old published leaves. OBL044 overlaps those
sets, so the expected signature-name count is derived as a set. Explicit
printing includes proofs, universes, full names and implicit arguments.
Incomplete, missing, duplicated or elided types fail the gate.

The stock replay driver then restores only context-compatible baseline outputs:

1. Compile the current ancestors of RecompileBasePart07 with a300-second limit.
2. Compile Part07 with a600-second limit. Its ancestors must have completed
   strict validation and must all be reused. Its historical422.832-second pass
   is the reason for this isolated exception.
3. Compile the current RecompileExtensionsPart02 closure with300-second limits.
   Upload an official early artifact immediately.
4. Compile the current closure of all44 accepted and five proposed original
   roots. Upload a second official early artifact.
5. Run the current native type/boundary audit and reconcile its exact results.
6. Select every current production source, reuse validated current contexts and
   compile the remaining affected modules with300-second limits.
7. Independently repeat final source, Git, native-context and boundary checks.
   Upload complete or failed evidence without modifying the ledger.

A failed stage stops subsequent compilation. Final evidence upload still runs.
No unchanged proof retry or compiler flag increase is automated.

## Source and dependency binding

BASELINE.json records the accepted307 module contexts and exact manifest, all
historical190 Point1 ancestors,44 accepted roots, five proposed roots,50 old
eligible leaves, the frozen target/lock/runtime and protected file hashes.

CANDIDATE_PLAN.json binds the complete candidate manifest and exactly which
old files changed or new files were added. Every edited source includes an
ordered exact before/after patch sequence; applying it must reproduce the
candidate and reversing it must restore the accepted bytes. The five original
written headers must remain exact. Added modules must be absent from the
baseline.

The affected cone uses the union of old and new import edges. A changed
ancestor invalidates its descendants even when an intermediate native output is
byte-identical. The recursive source-ancestry stamp must change for every
affected existing module. An unaffected module must retain its exact accepted
context, including source/imports, runtime, output, logs and recursive stamp.

The report distinguishes:

- Baseline contexts preserved exactly.
- Baseline contexts replaced by verified current native contexts.
- New current modules.
- Fresh compilation versus reused receipts in each replay invocation.

These quantities describe different facts. A final invocation may reuse modules
that were rebuilt earlier in the same staged job.

## Current publication and type boundary

All49 original root names receive fresh baseline/current native signature
comparison. Current transitive admission walks are required for every affected
accepted root and all five proposed roots. Unaffected accepted roots may reuse
their historical boundary only with their exact accepted native contexts.
For the planned two-file change this is34+5 fresh walks and10 preserved roots;
the actual counts are recomputed.

The historical Point1 signature claim remains15 explicitly printed native
signatures and29 lexical public-header checks. A new baseline capture does not
retroactively strengthen that historical event.

The native walker traverses types and opaque proof bodies, inductive
constructors and all referenced modules. It checks each root's complete
all-module axiom print as well. Missing constants, project axioms and
nonstandard axioms fail. The permitted foundational names are propext,
Classical.choice, Quot.sound and sorryAx. Every actual direct sorry leaf must
separately match the reviewed publication boundary.

OBL044's old direct admission is retired. Its header and native type remain
fixed, but its body is allowed to become a proved wrapper. None of the49
original roots can be accepted as a direct admission or relabeled as a new
generic input.

The two other published leaves in the edited files retain their exact
declaration source:

- PublishedInputs.ProjectiveLineGeometry.nonconstantCurveDifferential.
- Refinement.Boundary.LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne.

Their baseline/current native types and declaring-module contexts are
rechecked. Old leaves in unchanged source modules retain their original
source eligibility and receive current native bindings. A newly admitted leaf
requires an explicit independent reviewer root, eligible=true, primary-source
citations, exact full declaring-file hash and exact declaration-source hash.
Its native type and dependency context are then captured for independent final
review. A name alone never establishes eligibility.

## Audit isolation

run_continuation_audit.py copies exact production source bytes and only verified
native parent outputs, raw receipts and logs into an audit-only directory. The
generated audit module is excluded from production counts. Every production
parent must reuse; only the generated audit module can compile. The original
production build, receipts and RUN_STATUS remain unchanged.

The final verifier regenerates the expected audit source, revalidates its native
receipt and copied parent contexts, rehashes full stdout/stderr and reparses the
complete message stream. It does not trust success booleans in a report alone.

## Evidence schema

The principal artifacts are:

| File | Evidence |
| --- | --- |
| PREFLIGHT.json | Exact accepted/current Git source bindings, approved plan hash, recomputed cones and stage selections |
| baseline-audit/AUDIT_RECEIPT.json | Native baseline signature capture with immutable accepted parents |
| stages/part07_parents.json and part07.json | Separate ordinary-parent and justified Part07 budgets |
| stages/core.json | Current core closure and early reusable output contexts |
| stages/accepted_boundaries.json | Current accepted-root/3h closure |
| current-audit/AUDIT_RECEIPT.json | Current signatures, complete native walks and all-module axiom prints |
| CURRENT_BOUNDARIES.json | Exact old-to-new signature/admission and publication reconciliation |
| stages/full.json | All-current production replay, with independent baseline and invocation counts |
| FULL_CONTINUATION_VERIFICATION.json | Final whole-graph and boundary checks joined to source, Git, plan, baseline and stage hashes |

The final record sets current_native_evidence_ready_for_acceptance_review=true
only after all gates pass. It retains new_units_credited=0,
acceptance_ledger_modified=false and milestone_met=false. It explicitly lists
new native publication types and official current artifact metadata as requiring
independent review before any credit.

## Validation

test_continuation_gate.py uses clearly synthetic files and receipts; it never
invokes Lean. Focused corruption cases cover ancestor changes with identical
outputs, stale recursive stamps, output/log/receipt/runtime mutations, changed
published bodies or public headers, missing review identity, retired/original
admissions, missing/universe-altered native signatures, incomplete walks and
failed/missing final stages.

Two generated Lean syntax probes were run separately by the root diagnostic
owner against accepted imports. Both completed with zero errors. Their real
explicit-print axiom output exposed universe annotations in axiom names; the
parser now normalizes only that notation before validating the permitted names.
The original raw messages and hashes remain preserved. Those probes provide
syntax/parser evidence only and no native acceptance or obligation credit.

