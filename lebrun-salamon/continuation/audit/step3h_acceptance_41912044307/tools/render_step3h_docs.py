#!/usr/bin/env python3
"""Render current repository documents from a completed Step3h acceptance."""
import argparse
import copy
import json
import posixpath
from pathlib import Path


def read(path):
    return json.loads(Path(path).read_text())


def render(ledger, status_before, review):
    if ledger["metric"]["accepted_units"] != 79 or not ledger["checkpoint_update"]["step3h_accepted"]:
        raise ValueError("A completed 79/133 Step3h acceptance is required")
    update = ledger["checkpoint_update"]
    graph = ledger["latest_verified_full_graph"]
    source = ledger["source_snapshot"]
    leaves = update["actual_eligible_leaf_count"]
    run = str(graph["run_id"])
    evidence = review["verification_path"]
    record = review["acceptance_record_path"]
    history = str(Path(review["previous_ledger_path"]).parent)
    accounting = (
        "The accepted checklist total is **79/133 = 59.40%**: 22 retired original admissions, "
        "eight historically accepted Step 3b wrappers, 43 Point 1 obligations, the separately "
        "accepted OBL-069, and five Step 3h obligations. There remain **42 original obligations, "
        "eight definition validations and four final gates: 54 units**. The denominator remains "
        "121 original admissions plus eight definition validations and four final gates. This "
        "measures accepted checklist units; it does not estimate mathematical effort, time "
        "remaining or the fraction of source lines. Helpers, publication reviews and build "
        "receipts add no units."
    )
    native = (
        f"[Native run {run}](https://github.com/wajcha2/claude/actions/runs/{run}) verifies "
        f"**308/308 current source modules** at `{source['commit']}`. Exactly 50 accepted-baseline "
        "native contexts are preserved; 257 existing contexts have been revalidated, and one "
        "new module is verified. All source, output, log, receipt, recursive dependency and "
        "runtime bindings were checked. The final full-stage reuse count includes work already "
        "compiled in earlier stages of the same workflow. It is not the number of unchanged "
        "modules relative to Point 1.\n\n"
        "The historical Point 1 audit used 190 ancestor modules. In the current source graph, "
        "40 of those contexts are preserved and 150 have been revalidated. The historical "
        "all-190-unchanged event remains intact in its original record. The frozen theorem "
        "statement, toolchain lock and historical native drivers are unchanged.\n\n"
        f"See [the complete verification]({evidence}) and [the acceptance record]({record})."
    )
    boundary = (
        f"The current boundary covers **49 original roots** and **{leaves} actual distinct "
        "eligible published inputs**. There are 39 fresh current native dependency walks and "
        "10 historical boundaries reused only because their complete native contexts match "
        "exactly. Fresh baseline/current native type and universe comparisons preserve all 49 "
        "original statements. No original conclusion in this boundary is directly admitted; "
        "no missing constant, custom project axiom or unexpected axiom was found.\n\n"
        "The five new published inputs state canonical restriction of differentials, the "
        "immersion differential epimorphism, the kernel rank of an epimorphism between locally "
        "free sheaves, square-zero lifting for smooth morphisms, and the rational-point tangent "
        "criterion for smoothness. Their exact native types were independently compared with "
        "the reviewed primary statements. The former direct admission of OBL-044 has been "
        "retired from the boundary. The original Point 1 evidence remains historical evidence; "
        "its distinction between 15 explicit native signature comparisons and 29 written-header "
        "comparisons is not retrospectively changed."
    )
    proofs = """| Original obligation | Completed project proof |
|---|---|
| OBL-044 | Identify the actual cotangent map with the canonical restriction map by universal derivations and adjunction; transfer the restriction isomorphism. |
| OBL-045 | Identify the actual differential with the immersion epimorphism and prove the rank of its literal kernel from smooth cotangent ranks. |
| OBL-046 | Lift the actual dual-number thickening through the supplied smooth open, then prove compatibility with the project tangent differential. |
| OBL-047 | Convert surjectivity of that differential into the canonical tangent-lift criterion, retaining both original structural smoothness assumptions. |
| OBL-048 | Construct a linear equivalence between project derivations and the dual of the actual cotangent fiber; deduce its dimension using existing rank results. No new published input is needed. |"""
    fu = (
        "The first architecture comparison with Baohua Fu's "
        "[*The classification of Fano contact manifolds revisited*, arXiv:2611.01423v1]"
        "(https://arxiv.org/html/2611.01423v1) is complete; see "
        "[the source-bound review](audit/continuation_3h/FU_ROUTE_REVIEW.md). "
        "The relative-conic and quadratic-term arguments may replace much of the remaining "
        "branch-geometry work, particularly OBL-073–077. The actual coarse-family comparison, "
        "arbitrary reduced-base chart construction and contact compatibility must be proved "
        "before any old obligation is retired. The finite-cover input still needs the correct "
        "single-target Picard-one scope. No obligation has been retired on the strength of this "
        "review, and the whole classification theorem has not been admitted."
    )
    next_work = (
        'Continue Step 3i with one coherent relative-Hom construction. The project presentation is now compared with the genuine functor on arbitrary test schemes in both directions, including the actual universal evaluation and target base-change naturality. The isolated OBL-055 composition and exact generic finite-presentation boundary have a reviewed proposed integration. Representing-scheme existence remains separate: the classical Hom/Hilbert reference has a locally-Noetherian-test restriction, and the SGA 3 XI, Remark 3.4 upgrade still requires its Zariski gluing and limit-preservation hypotheses to be proved.\n\n'
        'For OBL-050 and OBL-051, the canonical isomorphism between supplied Hom presentations and its evaluation compatibility are proved. A supplied fixed-degree stratum now transfers to the original HomDegree.Open contract, preserving closedness, local finite type, quasi-compactness and the degree condition for every complex point. Its exhaustive local boundary contains exactly two already accepted published inputs and neither original OBL-050 nor OBL-051. Constructing the initial bounded stratum remains: preserve the given ample line through a very ample power and compute the actual graph Hilbert polynomial.\n\n'
        'An end-to-end conditional OBL-052 prototype proves density of the actual universal two-point evaluation with the original geometric hypotheses. It fixes the two source markings, realizes their prescribed infinitesimal motions through the Hom universal property, and applies the smoothness criterion on the supplied smooth Hom open. The complete local dependency walk found four previously eligible published inputs and no pending original dominance or integrality admission. Four generic criteria remain explicit in that prototype; a separate checked specialization supplies its tangent criterion from the exact native Step 3h input.\n\n'
        'For OBL-056, the parameter-lift equivalence is proved with the actual familyChange and evaluation equations. Finite coproducts preserve the original Yoneda first-cohomology vanishing predicate, including the empty family, and formal smoothness of the actual stalk map gives a smooth open containing the whole field-valued point. The main remaining comparison identifies the actual square-zero kernel and differential-Hom obstruction sheaf with the original fibre tangent-sheaf coefficient. The proposed published boundaries are SGA 1 III, Proposition 5.1/Corollary 5.2 for a specified thickening, and Stacks 02HX for all residue-compatible small Artinian extensions. These are a precise plan, not newly accepted admissions.\n\n'
        'The target-product irreducibility prerequisite has a separate conditional composition for OBL-057 in Step 3j, using three generic field/normality criteria. The reviewed static integration proposal moves seven dominance/detection declarations to a later module and changes three consumer imports. Its complete native validation remains pending. All these isolated preparations add zero accepted units; their proposed source changes remain outside the accepted production snapshot until source, publication and native checks pass.'
    )
    endpoint = (
        "The full milestone remains **open**. The compiled assembly still takes the explicit "
        "`LeBrunSalamon.Milestone.PositiveQKSimpleConnectedness` bridge. The unconditional "
        "frozen theorem, including the actual positive-metric Wolf homothety, is not yet "
        "proved. All eight semantic definition validations and all four final-theorem gates "
        "remain pending. Current conditional compilation does not close those gates."
    )
    accepted_table = """| Step | Accepted original obligations |
|---|---:|
| 3c | 6/6 |
| 3d | 11/11 |
| 3e | 7/7 |
| 3f | 11/11 |
| 3g | 8/8 |
| 3h | 5/5 |
| Separate inherited OBL-069 | 1/1 |"""
    remaining_table = """| Batch | Pending original obligations | Scope |
|---|---:|---|
| 3i | 8 | Hom representability, deformation and evaluation |
| 3j | 8 | Stable maps, nodal families and global functions |
| 3k | 7 | Finite covers, normalization and spreading; OBL-069 accepted |
| 3l | 6 | Branch geometry, purity and extension; review Fu replacement |
| 3m | 5 | Contact lines, directions and cone geometry |
| 3n | 8 | Automorphism groups, adjoint varieties and metric recovery |
| **Total** | **42** | |"""
    readme = f"""# LeBrun–Salamon formalisation: continuation

**Point 1 and Step 3h are accepted. The full published-theorems-only milestone remains open.**

{accounting}

## Accepted scope

{accepted_table}

## Step 3h proofs

{proofs}

## Native verification

{native}

## Published-input boundary

{boundary}

## Remaining proof and the Fu comparison

{fu}

{next_work}

{endpoint}

Continue with [the plan](TAKEOVER_PLAN.md), [the progress ledger](audit/MILESTONE_PROGRESS.md),
and [the machine-readable status](TAKEOVER_STATUS.json).

## Reproduction and history

`SOURCE.sha256` binds the checked production sources, `target/MainStatement.lean` the frozen
specification, and `TOOLCHAIN.lock.json` the runtime. The acceptance documentation commit
has identical production sources to the compiled commit; it is not a new compiler event.
The earlier current documents are preserved under [{history}]({history}).
Run 41900703071 stopped in the static checker before any compiler invocation; its sole
missing-section-end repair and complete failure evidence are retained under
`audit/continuation_3h/attempts/41900703071`.
"""
    plan = f"""# LeBrun–Salamon continuation plan

**Current decision: Point 1 and Step 3h accepted; continue the unchanged published-theorems-only milestone.**

## 1. Recovered 3c–3g work — complete

The 43 original Point 1 obligations and inherited OBL-069 remain accepted. Their historical
acceptance record is preserved. Current affected boundaries have now been revalidated as
part of Step 3h; earlier completion announcements and failed attempts remain in history.

## 2. Cotangent and smoothness work, Step 3h — complete

{proofs}

{native}

## 3. Fu architecture comparison — first review complete

{fu}

## 4. Next original obligations

{remaining_table}

{next_work}

Follow [the original Step 3 dependency plan](audit/ORIGINAL_STEP3_PLAN.md), with any change
of proof architecture recorded explicitly. A retirement requires actual liveness and
compilation evidence. A retained `sorry` must state a precise known published result; its
project applications, comparisons and compositions must be proved.

## 5. Definitions and the exact endpoint

{endpoint}

Keep all eight definition validations open until explicit identifications with the standard
mathematical notions are established. Then prove the simple-connectedness bridge with its
exact published hypotheses and validated operational definitions.

## 6. Final milestone gates

1. Compile the exact unconditional frozen theorem.
2. Compile its complete current dependency and reverse-dependency graph with locked evidence.
3. Audit every final-theorem transitive assumption against the exact published-input list.
4. Publish one reproducible final source revision containing all acceptance evidence.

## Accounting and evidence

{accounting}

{boundary}

The current acceptance is [recorded here]({record}); previous current documents are preserved
under [{history}]({history}).
"""
    pending_rows = "\n".join(f"| {x['id']} | {x['substep']} | `{x['declaration']}` |"
                             for x in ledger["pending_original_obligations"])
    native_for_progress = native.replace(
        f"]({evidence})", f"]({posixpath.relpath(evidence, 'audit')})"
    ).replace(f"]({record})", f"]({posixpath.relpath(record, 'audit')})")
    progress = f"""# Milestone progress

{accounting}

## Accepted original batches

{accepted_table}

{native_for_progress}

{boundary}

## Pending original obligations

| ID | Step | Original declaration |
|---|---|---|
{pending_rows}

## Separate definition and final-gate obligations

All eight definition validations and all four final gates remain pending. The complete
unit-by-unit record is [MILESTONE_PROGRESS.json](MILESTONE_PROGRESS.json).

{endpoint}
"""
    status = copy.deepcopy(status_before)
    status["previous_status_snapshot"] = history + "/TAKEOVER_STATUS.json"
    status["historical_point1_at_acceptance"] = status.pop("point1")
    status["point1"] = {"complete": True, "historical_event": status["historical_point1_at_acceptance"]["evidence"],
        "original_obligations": 43, "additional_inherited_obligations": ["OBL-069"],
        "current_boundaries_revalidated": True, "current_acceptance_record": record}
    status["step3h"] = {"complete": True, "original_obligations": 5,
        "ids": [f"OBL-{i:03}" for i in range(44, 49)], "acceptance_record": record,
        "new_generic_published_inputs": 5, "new_input_review_units_credited": 0}
    status["updated_utc"] = review["accepted_utc"]
    status["current_source"].update({"compiled_commit": source["commit"], "compiled_tree": source["tree"],
        "source_modules": 308, "source_manifest_sha256": source["source_manifest_sha256"],
        "entire_current_source_graph_native_verified": True, "frozen_unconditional_endpoint_verified": False})
    status["percentage_metric"].update({"accepted": 79, "pending": 54, "percentage": 7900 / 133,
        "percentage_display": 59.40, "rounded_percentage": 59})
    status["proof_completion_percentage"] = 59.40
    status["native_current_ci"].update({"run_id": graph["run_id"], "run_attempt": graph["run_attempt"],
        "source_commit": source["commit"], "verified_current_modules": 308, "selected_modules": 308,
        "status_counts": graph["counts"], "status_counts_scope": "Final full-stage invocation",
        "baseline_contexts_preserved": 50, "baseline_contexts_revalidated": 257, "new_modules": 1,
        "verification": evidence, "verification_sha256": review["verification_sha256"],
        "artifact": review["artifact"]})
    status["native_current_ci"].pop("fresh_native_passes", None)
    status["native_current_ci"].pop("reused_native_receipts", None)
    status["remaining_original_batches"].pop("3h")
    status["remaining_original_obligations"] = 42
    status["next_execution_priorities"] = [
        "Finish the Step3i actual relative-Hom construction, all-test upgrade, fixed-degree stratum and evaluation comparisons.",
        "Implement the selected Fu relative-conic/coarse-family comparisons before any scope retirement.",
        "Complete the remaining42 original obligations and8 definition validations.",
        "Prove the simple-connectedness bridge and unchanged unconditional target; pass all4 final gates."]
    status["admission_boundary_scope"] = f"Current49 accepted roots and{leaves} actual eligible published inputs; final-theorem audit remains open."
    status["milestone_met"] = False
    return {"README.md": readme, "TAKEOVER_PLAN.md": plan, "audit/MILESTONE_PROGRESS.md": progress,
            "TAKEOVER_STATUS.json": json.dumps(status, ensure_ascii=False, indent=2) + "\n"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for key in ("ledger", "previous-status", "review", "output"):
        parser.add_argument("--" + key, type=Path, required=True)
    args = parser.parse_args()
    files = render(read(args.ledger), read(args.previous_status), read(args.review))
    for name, text in files.items():
        path = args.output / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    print(json.dumps({"written": sorted(files), "accepted": 79, "milestone_met": False}))


if __name__ == "__main__":
    main()
