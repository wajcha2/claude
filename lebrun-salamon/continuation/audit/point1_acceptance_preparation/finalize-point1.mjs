/* Point 1 acceptance preparation only. This file does not run Lean or write a ledger.
 * Calls fail unless the exact current stock-native verification and publication
 * boundary satisfy all fixed gates. Current accepted credit is unchanged until
 * a reviewed final record is generated and published. */

export const sha256 = function sha256(s) {
 const a=[];for(const x of s){const c=x.codePointAt(0);if(c<128)a.push(c);else if(c<2048)a.push(192|(c>>6),128|(c&63));else if(c<65536)a.push(224|(c>>12),128|((c>>6)&63),128|(c&63));else a.push(240|(c>>18),128|((c>>12)&63),128|((c>>6)&63),128|(c&63));}
 const len=a.length*8;a.push(128);while(a.length%64!==56)a.push(0);const hi=Math.floor(len/4294967296),lo=len>>>0;for(let i=3;i>=0;i--)a.push((hi>>>(i*8))&255);for(let i=3;i>=0;i--)a.push((lo>>>(i*8))&255);
 const K=[0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
 const H=[0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];const rr=(x,n)=>(x>>>n)|(x<<(32-n));
 for(let o=0;o<a.length;o+=64){const w=[];for(let i=0;i<16;i++)w[i]=(a[o+4*i]<<24)|(a[o+4*i+1]<<16)|(a[o+4*i+2]<<8)|a[o+4*i+3];for(let i=16;i<64;i++){const s0=rr(w[i-15],7)^rr(w[i-15],18)^(w[i-15]>>>3),s1=rr(w[i-2],17)^rr(w[i-2],19)^(w[i-2]>>>10);w[i]=(w[i-16]+s0+w[i-7]+s1)|0;}
 let [v0,v1,v2,v3,v4,v5,v6,v7]=H;for(let i=0;i<64;i++){const t1=(v7+(rr(v4,6)^rr(v4,11)^rr(v4,25))+((v4&v5)^(~v4&v6))+K[i]+w[i])|0;const t2=((rr(v0,2)^rr(v0,13)^rr(v0,22))+((v0&v1)^(v0&v2)^(v1&v2)))|0;v7=v6;v6=v5;v5=v4;v4=(v3+t1)|0;v3=v2;v2=v1;v1=v0;v0=(t1+t2)|0;}
 const v=[v0,v1,v2,v3,v4,v5,v6,v7];for(let i=0;i<8;i++)H[i]=(H[i]+v[i])|0;
 }return H.map(x=>(x>>>0).toString(16).padStart(8,"0")).join("");
};

export const finalizePoint1Ledger = function finalizePoint1Ledger(verification, context, baselineLedger, preparation, sha256) {
  const require = (ok, message) => { if (!ok) throw new Error("Point1 promotion blocked: " + message); };
  require(verification.all_current_sources_kernel_checked === true, "full current compilation not passed");
  require(verification.accepted_modules === verification.source_modules &&
          verification.selected_modules === verification.source_modules, "incomplete source coverage");
  require(Array.isArray(verification.failures) && verification.failures.length === 0, "native failures remain");
  require(Object.entries(verification.status_counts).every(([s,n]) =>
    n === 0 || ["passed","reused","historical_reuse"].includes(s)), "unaccepted module statuses remain");
  require(verification.source_target_lock_manifest_git_blob_binding_verified &&
          verification.all_accepted_output_log_receipt_dependency_and_recursive_ancestry_hashes_verified &&
          verification.all_final_source_graph_and_runtime_hashes_verified, "source/runtime/artifact verification incomplete");
  require(verification.frozen_target_sha256 === "9afe9c5b2e63db17e8f217b71c821eaca83fe26c5cfbc2956fc1b92832d09296", "frozen target changed");
  require(verification.toolchain_lock_sha256 === "7f60e90fabda82f0e4e3c3bf4537d24f1298514f116bc18215f162e203f11c19", "toolchain lock changed");
  require(verification.runtime_fingerprint === "9387025ac24e8fbfc8c41c101ebb879f2345074bbb8683f5b65951d1f5cb8004" &&
          verification.compiler_kind === "stock_pinned_frontend" &&
          verification.mathlib_revision === "116662aa4c1e9106ab5c609b3214b02f6e11a65a", "pinned native runtime differs");
  require(JSON.stringify(verification.runtime_flags) === JSON.stringify(
    ["--json","-j1","-DElab.async=false","-M12000","-DmaxErrors=1000","-DmaxHeartbeats=2000000"]), "native flags differ");
  const boundary=verification.point1_boundary;
  require(boundary.all190_compared_and_unchanged === true &&
    boundary.source_and_import_comparisons === 190 &&
    boundary.native_output_dependency_and_recursive_stamp_comparisons === 190 &&
    boundary.basis_sha256 === "b4681aeb45d66ae34215850d7957f4d9a64c04c50470b8c517c796a1347db533", "audited190 boundary changed");
  require(sha256(verification.complete_source_manifest) === verification.source_manifest_sha256, "manifest digest mismatch");
  const manifest={};
  for(const line of verification.complete_source_manifest.trimEnd().split("\n")){
    const m=/^([0-9a-f]{64})  (source\/.+\.lean)$/.exec(line);
    require(!!m,"invalid manifest row");
    require(!(m[2] in manifest),"duplicate manifest path");
    manifest[m[2]]=m[1];
  }
  require(Object.keys(manifest).length === verification.source_modules,"source manifest incomplete");
  require(preparation.point1_original_obligations === 43 &&
    preparation.distinct_actual_direct_admitted_inputs === 50 &&
    preparation.independent_publication_review.all50_actual_admitted_inputs_eligible &&
    preparation.all44_printed_axioms_use_exact_allowlist &&
    preparation.missing_constants === 0 && preparation.custom_project_axioms === 0 &&
    preparation.unexpected_axioms_from_any_module === 0 &&
    preparation.original_project_admissions_in_actual_closure.length === 0, "proof/publication audit is not complete");
  const rows=[...preparation.obligations,...preparation.additional_inherited_obligations_detail];
  const expected=[...Array.from({length:43},(_,i)=>"OBL-"+String(i+1).padStart(3,"0")),"OBL-069"];
  require(JSON.stringify(rows.map(r=>r.id))===JSON.stringify(expected),"acceptance scope differs from44 agreed units");
  for(const r of rows)require(manifest[r.source_file]===r.source_sha256 && r.native_and_publication_boundary_passed &&
    r.original_public_header_preserved_lexically && !r.original_project_conclusion_directly_admitted,
    "obligation source/boundary mismatch for "+r.id);
  for(const l of preparation.actual_leaf_inventory)
    require(manifest["source/"+l.module+".lean"]===l.source_sha256,"published leaf source mismatch for "+l.name);
  require(context.workflow_conclusion === "success", "official full workflow has not succeeded");
  require(typeof context.verification_text === "string" &&
    sha256(context.verification_text) === context.verification_sha256 &&
    JSON.stringify(JSON.parse(context.verification_text)) === JSON.stringify(verification),
    "archived verification bytes do not match the reviewed report");
  require(context.artifact && Number.isInteger(context.artifact.id) && context.artifact.id > 0 &&
    context.artifact.run_id === verification.run_id && typeof context.artifact.name === "string" &&
    /^[0-9a-f]{64}$/.test(context.artifact.sha256),
    "official evidence artifact metadata is incomplete");
  const ledger=JSON.parse(JSON.stringify(baselineLedger));
  require(ledger.metric.denominator===133 && ledger.metric.accepted_units===30,"fixed accounting baseline changed");
  require(ledger.pending_original_obligations.length===91,"original inventory changed");
  for(const id of expected)require(ledger.pending_original_obligations.filter(x=>x.id===id).length===1,"missing/duplicate ledger ID "+id);
  const acceptanceEvidenceId="P-POINT1-ACCEPTED-"+verification.run_id;
  const acceptedRows=rows.map(r=>({
    ...r,acceptance_status:"accepted_current_native_and_exact_published_boundary",
    accepted:true,remaining_acceptance_gate:null,
    current_reverse_dependency_gate_passed:true,
    current_reverse_dependency_verification:context.verification_path,
    current_reverse_dependency_verification_sha256:context.verification_sha256,
    accepted_utc:context.accepted_utc
  }));
  const finalRecord={
    schema:"lebrun-point1-final-acceptance-v1",
    accepted_utc:context.accepted_utc,
    status:"accepted_exact_published_boundary_and_current_reverse_dependencies",
    point1_accepted:true,whole_theorem_milestone_met:false,
    point1_original_obligations:43,additional_inherited_obligations:1,
    point1_source_substep_counts:preparation.point1_source_substep_counts,
    preparation_record:context.preparation_record,
    current_compilation:verification,
    current_verification_evidence:{path:context.verification_path,sha256:context.verification_sha256,artifact:context.artifact},
    original_audited_source_snapshot:preparation.source_snapshot,
    native_audits:preparation.native_audits,
    original_header_comparison:preparation.original_header_comparison,
    original_header_comparison_sha256:preparation.original_header_comparison_sha256,
    signature_scope:preparation.signature_scope,
    publication_catalog:preparation.publication_catalog,
    publication_catalog_sha256:preparation.publication_catalog_sha256,
    independent_publication_review:preparation.independent_publication_review,
    native_original_roots_checked:44,distinct_actual_direct_admitted_inputs:50,
    missing_constants:0,custom_project_axioms:0,unexpected_axioms_from_any_module:0,
    all44_printed_axioms_use_exact_allowlist:true,
    standard_axiom_allowlist:preparation.standard_axiom_allowlist,
    original_project_admissions_in_actual_closure:[],
    required_current_reverse_cone_gate:{passed:true,scope:"All current source modules, including all affected reverse dependencies.",verification:context.verification_path},
    obligations:acceptedRows.slice(0,43),
    additional_inherited_obligations_detail:acceptedRows.slice(43),
    actual_leaf_inventory:preparation.actual_leaf_inventory,
    milestone_accounting:{fixed_denominator:133,previously_accepted_units:30,newly_accepted_original_units:44,
      accepted_units:74,pending_units:59,percentage:7400/133,percentage_display:55.64,rounded_percentage:56,
      helper_modules_count_as_units:false,sorry_token_count_used_for_credit:false,
      final_gates_promoted:0,definition_validations_promoted:0},
    endpoint_scope:"The current conditional assembly compiles. The unchanged frozen unconditional theorem and the whole published-theorems-only milestone remain open."
  };
  ledger.updated_utc=context.accepted_utc;
  ledger.metric={...ledger.metric,accepted_units:74,pending_units:59,percentage:7400/133,percentage_display:55.64,rounded_percentage:56,
    formula:"(22 retired original admissions +8 historically accepted wrappers +43 accepted Point1 obligations +1 separately accepted OBL-069) /133",
    numerator_boundary:"Original accepted checklist units only;43 Point1 obligations and OBL-069 now have complete native, publication and current reverse-dependency evidence."};
  ledger.milestone_met=false;
  ledger.whole_current_proof_graph_kernel_verified=true;
  ledger.frozen_unconditional_endpoint_kernel_verified=false;
  ledger.historical_partial_progress_before_point1=ledger.partial_progress_no_additional_credit;
  ledger.accepted_original_obligations=acceptedRows.map(r=>{
    const old=ledger.pending_original_obligations.find(x=>x.id===r.id);
    return {...old,status:r.acceptance_status,accepted:true,acceptance_evidence_complete:true,
      current_lexical_status:"no_direct_admission",current_source_file_sha256:r.source_sha256,
      evidence_ids:[...(old.evidence_ids||[]),acceptanceEvidenceId],
      complete_acceptance_record:context.acceptance_path,native_and_publication_boundary:r};
  });
  ledger.pending_original_obligations=ledger.pending_original_obligations.filter(x=>!expected.includes(x.id))
    .map(x=>({...x,current_source_file_sha256:manifest["source/"+x.file]||x.current_source_file_sha256}));
  ledger.groups=ledger.groups.map(g=>g.group==="Steps3c–3n original obligations"?{...g,accepted:44}:g);
  ledger.source_snapshot={
    commit:verification.commit,tree:verification.tree,source_module_count:verification.source_modules,
    source_manifest:"SOURCE.sha256",source_manifest_sha256:verification.source_manifest_sha256,
    manifest_convention:"Sorted lines: source SHA256 +two spaces +source-relative path +newline.",
    original_csv_sha256:baselineLedger.source_snapshot.original_csv_sha256,
    frozen_target_sha256:verification.frozen_target_sha256,toolchain_lock_sha256:verification.toolchain_lock_sha256,
    snapshot_utc:context.accepted_utc
  };
  ledger.evidence[acceptanceEvidenceId]={kind:"complete_original_obligation_acceptance",
    path:context.acceptance_path,run_id:verification.run_id,source_commit:verification.commit,
    exact_original_ids:expected,current_verification_path:context.verification_path,
    current_verification_sha256:context.verification_sha256,
    native_roots:44,actual_eligible_admitted_leaves:50,point1_ancestor_modules:190,whole_current_source_modules:verification.source_modules};
  ledger.latest_verified_full_graph={
    run_id:verification.run_id,commit:verification.commit,source_modules_selected:verification.source_modules,
    status:"completed",conclusion:"success",counts:verification.status_counts,
    accepted_count_at_that_commit:verification.accepted_modules,full_selected_graph_passed:true,
    fresh_native_passes:verification.fresh_native_passes,native_receipts_reused:verification.native_receipts_reused,
    evidence:context.verification_path,
    scope:"All current source modules and their complete current ancestry; the exported milestone endpoint is still conditional."
  };
  ledger.checkpoint_update={source_freeze:"SOURCE.sha256",verification:context.verification_path,
    point1_accepted:true,point1_original_roots_checked:43,additional_inherited_roots_checked:1,
    actual_eligible_leaf_count:50,whole_current_proof_graph_kernel_verified:true,
    accepted_units_added:44,accepted_units_total:74,total_units:133,milestone_met:false};
  ledger.final_gates=ledger.final_gates.map(g=>{
    require(g.accepted===false,"unexpected final gate credit");
    const partial={
      "GATE-01":"The exact frozen statement is preserved; the complete current conditional assembly compiles. PositiveQKSimpleConnectedness is still an explicit outstanding bridge.",
      "GATE-02":"All current source modules now compile with exact source/runtime/recursive dependency receipts. The final unconditional frozen endpoint has not yet been implemented, so this final milestone gate remains pending.",
      "GATE-03":"The44 accepted original roots have an exhaustive native dependency audit with50 eligible published leaves. The final unconditional theorem and remaining original obligations have not passed the exhaustive final audit.",
      "GATE-04":"The accepted Point1 checkpoint is reproducible and bound to locked native evidence. The complete theorem milestone remains open."
    };
    return {...g,partial_progress:partial[g.id]||g.partial_progress,evidence_ids:[...(g.evidence_ids||[]),acceptanceEvidenceId]};
  });
  ledger.partial_progress_no_additional_credit=[{
    id:"CURRENT-CONDITIONAL-GRAPH",description:"All current source modules compile; the unconditional frozen endpoint and definition validations remain pending.",
    supports:["GATE-01","GATE-02","GATE-03","GATE-04"],evidence_ids:[acceptanceEvidenceId],accepted_units_added:0
  }];
  ledger.ledger_production={source_mutation:false,lean_invoked_by_ledger_writer:false,
    native_evidence_run:verification.run_id,historical_ledger_snapshot:context.previous_ledger_path,
    only_written_files:["audit/MILESTONE_PROGRESS.json","audit/MILESTONE_PROGRESS.md",context.acceptance_path]};
  ledger.historical_observations_before_point1={
    historical_ledger_snapshot:context.previous_ledger_path,
    targeted_smoothing_replay:baselineLedger.targeted_smoothing_replay,
    checkpoint_update:baselineLedger.checkpoint_update,
    latest_full_graph:baselineLedger.latest_verified_full_graph,
    completion_announcements:baselineLedger.recovered_completion_announcements
  };
  delete ledger.targeted_smoothing_replay;
  ledger.denominator_basis.remaining_original_obligations_scope=
    "Historical post-Step3b baseline (91). The fixed denominator is unchanged; the current pending original-obligation list contains 47.";
  ledger.denominator_basis.current_pending_original_obligations=47;
  ledger.acceptance_rule.historical_boundary=
    "The 22 Step 3a retirements and 8 Step 3b wrappers retain their recovered stage-acceptance credit. Current whole-source compilation is documented separately in latest_verified_full_graph; it does not itself re-audit their literature statements.";
  ledger.recovered_completion_announcements={
    ...baselineLedger.recovered_completion_announcements,
    status:"Reconciled by current native, exact-publication and full reverse-dependency acceptance for Point1.",
    current_reconciliation:{acceptance_record:context.acceptance_path,
      verification:context.verification_path,reported_stages_accepted:["3c","3d","3e","3f"],
      additional_accepted_stage:"3g",credit_from_announcements_alone:0}
  };
  ledger.historically_accepted_step3b_obligations=
    ledger.historically_accepted_step3b_obligations.map(r=>({...r,
      current_native_compilation:context.verification_path,
      current_static_check:{...r.current_static_check,source_file_sha256:manifest["source/"+r.file]}}));
  ledger.latest_verified_full_graph.conclusion=context.workflow_conclusion;
  require(ledger.accepted_original_obligations.length===44 && ledger.pending_original_obligations.length===47,"ledger partition failed");
  require(ledger.groups.reduce((n,g)=>n+g.accepted,0)===74,"group numerator mismatch");
  require(ledger.groups.reduce((n,g)=>n+g.total,0)===133,"group denominator mismatch");
  return {ledger,finalRecord};
};

export const point1Documents = function point1Documents(v, c) {
  const auditRelative=p=>p.startsWith("audit/")?p.slice(6):p;
  const run="https://github.com/wajcha2/claude/actions/runs/"+v.run_id;
  const countTable=[
    "| Step | Original obligations accepted |","|---|---:|",
    "| 3c — external tensors and diagonal sections | 6/6 |",
    "| 3d — base change, fibers and total spaces | 11/11 |",
    "| 3e — determinants, ampleness and first jets | 7/7 |",
    "| 3f — infinitesimal algebra and nodal models | 11/11 |",
    "| 3g — projective-line geometry and normalization | 8/8 |",
    "| **Point 1** | **43/43** |",
    "| Separate inherited affine-projection obligation OBL-069 | 1/1 |"].join("\n");
  const accounting="The accepted checklist total is **74/133 = 55.64%, rounded to 56%**: 22 retired original admissions, eight historically accepted Step 3b wrappers, 43 Point 1 obligations, and the separately accepted OBL-069. The denominator remains 121 original admissions plus eight definition validations and four final gates. This measures fully accepted checklist units; it is not an estimate of mathematical effort, elapsed time, or the proportion of source lines. Helper modules, compatibility repairs, shared publication reviews and compilation receipts do not add units.";
  const native=`[Native run ${v.run_id}](${run}) verifies **${v.accepted_modules}/${v.source_modules} current source modules**. In this run, ${v.fresh_native_passes} passed by fresh compilation and ${v.native_receipts_reused} reused native receipts matched the current source, imported outputs, recursive ancestry, runtime and compiler flags. All **190 modules** underlying the Point 1 declaration audits match their audited source, imports, outputs, direct dependencies and recursive ancestry exactly. The frozen statement and toolchain lock are unchanged.`;
  const boundary="The native declaration audit covers **44 original roots**: 43 Point 1 obligations and OBL-069. Their actual dependency closure contains **50 distinct directly admitted published inputs**, each reviewed against its primary source, hypotheses, conclusion and maps. No original project conclusion is directly admitted in this audited boundary. No missing constant, custom project axiom or unexpected axiom was found. All 44 original public headers match after removal of comments and whitespace. Explicit native type events are recorded for the 15 roots in the changed tranche; no retrospective native signature comparison is claimed for the other 29. The eight semantic definition validations remain separate.";
  const proofs=[
    "- **Tensor and base-change arguments:** prove the actual external-section, diagonal, fiber, dual, Hom and total-space comparisons.",
    "- **Determinants and first jets:** isolate the necessary alternating determinant input, prove its contact specialization, and check the first-jet translation.",
    "- **Infinitesimal and nodal geometry:** prove square-zero arguments, chart identities, fundamental-class gluing, and the actual polarized smooth and nodal trait models.",
    "- **Projective-line normalization:** check the explicit normalized source bivector, uniqueness and compatibility with the chosen projective-line geometry.",
    "- **Affine projection:** prove OBL-069 from generic affine section representability and the actual universal construction."].join("\n");
  const remaining="The full published-theorems-only milestone remains **open**. The current complete source graph includes a compiled **conditional** assembly: `LSMilestoneTarget.lean` still takes the explicit `PositiveQKSimpleConnectedness` bridge, which is absent from the frozen unconditional theorem. There remain **47 original obligations, eight definition validations and four final gates: 59 units**. Current conditional compilation does not discharge GATE-02 for the final unconditional theorem, and the 50-input Point 1 review is not the exhaustive final-theorem audit.";
  const paper="Baohua Fu's [*The classification of Fano contact manifolds revisited*, arXiv:2611.01423v1](https://arxiv.org/html/2611.01423v1) supplies a shorter geometric route. Its relative-conic treatment and direct use of the quadratic term are relevant to the remaining extension and homogeneity work. The completed tensor, infinitesimal, conic and projective-line foundations are retained. Compare the new route with the remaining 3k–3n dependencies before further branch-geometry implementation. The whole classification theorem has not been introduced as an admitted shortcut. Record any change in scope explicitly; the fixed denominator is unchanged.";
  const readme=`# LeBrun–Salamon formalisation: continuation

**Point 1 is complete. The full published-theorems-only milestone remains open.**

${accounting}

## Accepted scope

${countTable}

The binding decision is [the final Point 1 acceptance record](${c.acceptance_path}). The original completion announcements for 3c, 3d, 3e and 3f, recovered sources and earlier audit records remain preserved.

## Native verification

${native}

See [the full verification report](${c.verification_path}) for the exact source manifest, runtime, artifact and dependency hashes.

## Published-input boundary

${boundary}

The [publication review](audit/point1_publication_review/current_20261104T031351/PUBLICATION_REVIEW.md) and [exact input catalog](audit/POINT1_PUBLISHED_LEAF_ELIGIBILITY.md) retain their original evidence-bound bytes. Their dated pending-acceptance labels are superseded by the final acceptance record.

## Proof work completed

${proofs}

## Remaining work

${remaining}

Continue with [TAKEOVER_PLAN.md](TAKEOVER_PLAN.md), [the fixed progress ledger](audit/MILESTONE_PROGRESS.md), and [the machine-readable status](TAKEOVER_STATUS.json).

## The new Fu proof

${paper}

## Reproduction and history

The checked sources are identified by \`SOURCE.sha256\`, the frozen specification by \`target/MainStatement.lean\`, and the runtime by \`TOOLCHAIN.lock.json\`. The native workflow and artifacts are linked in the acceptance record. Source-preserving recovery commit \`d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0\` and the original 129-module checkpoint remain in repository history. Previous current documents are preserved under [${c.history_dir}](${c.history_dir}).
`;
  const plan=`# LeBrun–Salamon continuation plan

**Current decision: Point 1 accepted; continue toward the unchanged published-theorems-only milestone.**

## 1. Complete and accept the recovered 3c–3g work — finished

${countTable}

Every credited original obligation has its preserved statement, exact published-input boundary, actual project translations, native declaration evidence and matching current reverse-dependency compilation. See [the final acceptance record](${c.acceptance_path}).

${native}

${proofs}

## 2. Compare the remaining proof architecture with Fu's simplification

${paper}

Identify which existing obligations are still required, which checked definitions and lemmas carry over, and which actual maps need new comparison proofs. Any retirement of unused admissions must have explicit liveness and compilation evidence.

## 3. Discharge the remaining original obligations

| Batch | Remaining original units | Scope |
|---|---:|---|
| 3h | 5 | Cotangent sequences and smoothness |
| 3i | 8 | Hom representability, deformation and evaluation |
| 3j | 8 | Stable maps, nodal families and global functions |
| 3k | 7 | Finite covers, normalization and spreading; OBL-069 is accepted |
| 3l | 6 | Branch geometry, purity and extension |
| 3m | 5 | Contact lines, directions and cone geometry |
| 3n | 8 | Automorphism groups, adjoint varieties and metric recovery |
| **Total** | **47** | |

Use the dependency order in [the original Step 3 plan](audit/ORIGINAL_STEP3_PLAN.md), subject to an explicitly documented architecture revision. A retained \`sorry\` must state a precise known published theorem. Its hypotheses, conclusion and actual maps must match the source, and the project-specific specializations and compositions must be proved.

## 4. Validate definitions and close the exact frozen endpoint

Keep all eight definition validations open until the operational Lean definitions are identified with their standard mathematical notions. These include quaternionic-Kähler geometry, the curvature conventions, global symmetry and the intrinsic Wolf-space class.

The current conditional assembly is kernel checked. Prove the outstanding \`PositiveQKSimpleConnectedness\` bridge using its exact published hypothesis and validated definition translation, then check an unconditional theorem with the unchanged frozen hypotheses and both conclusions, including the actual positive metric Wolf homothety. No extra input may remain hidden in a proof package.

## 5. Pass the four final milestone gates

1. Compile the exact unconditional frozen theorem.
2. Compile its complete current dependency and reverse-dependency graph with locked native evidence.
3. Audit every transitive assumption of that final theorem and reconcile every retained admission with the exact published-input allowlist.
4. Package one reproducible locked final source revision with all acceptance evidence.

These are final-theorem gates. The successful current conditional graph does not close them prematurely.

## Accounting and evidence rules

${accounting}

For each retained admission, record the fully qualified Lean declaration, expanded mathematical statement, stable primary publication locator, hypothesis/conclusion comparison, separately proved project translation, and matching native compilation evidence. Validate actual transitive constants; namespace names and raw \`sorry\` counts do not establish eligibility.

Keep original public statements and the frozen target unchanged. Preserve historical evidence when newer records supersede it. Each accepted substep requires changed-module and reverse-dependency compilation, as specified by the original plan. The earlier takeover plan and findings are archived under [${c.history_dir}](${c.history_dir}).
`;
  const progress=`# Milestone progress

**Accepted checklist completion: 74/133 = 55.64%, rounded to 56%.**

The published-theorems-only milestone is not yet met. Point 1 is complete, with the separate OBL-069 accepted at the same evidence boundary.

| Group | Accepted | Total |
|---|---:|---:|
| Step 3a retired original admissions | 22 | 22 |
| Step 3b historically accepted wrappers | 8 | 8 |
| Steps 3c–3n original obligations | 44 | 91 |
| Step 2 semantic definition validations | 0 | 8 |
| Final milestone gates | 0 | 4 |
| **Total** | **74** | **133** |

${accounting}

## Acceptance evidence

${native}

${boundary}

The binding [final acceptance record](${auditRelative(c.acceptance_path)}) and [native verification](${auditRelative(c.verification_path)}) retain exact evidence. The [JSON ledger](MILESTONE_PROGRESS.json) lists every original acceptance unit. The previous ledger is preserved at [${c.previous_ledger_path}](${auditRelative(c.previous_ledger_path)}).

## Remaining work

${remaining}

See [the continuation plan](../TAKEOVER_PLAN.md).
`;
 return {readme,plan,progress};
};

export const point1Status = function point1CurrentStatus(v,c,ledger,oldStatus) {
  if (!v.all_current_sources_kernel_checked || ledger.metric.accepted_units!==74 ||
      ledger.pending_original_obligations.length!==47 || ledger.milestone_met)
    throw Error("Cannot produce accepted current status before the full Point1 gate");
  return {
    schema:"lebrun-takeover-status-v2",
    recorded_utc:c.accepted_utc,updated_utc:c.accepted_utc,timezone:"Etc/UTC",
    milestone:oldStatus.milestone,milestone_met:false,
    repository:"wajcha2/claude",branch:"codex/lebrun-takeover-audit-20261103",
    byte_preserving_recovery_commit:oldStatus.byte_preserving_recovery_commit,
    recovered_archive:oldStatus.recovered_archive,
    previous_status_snapshot:c.previous_status_path,
    reported_complete_stages:oldStatus.reported_complete_stages,
    completion_report_reconciliation:{
      historical_reconciliation:oldStatus.completion_report_reconciliation,
      current_decision:"All43 original3c–3g obligations now accepted on current native/publication evidence and completed reverse dependencies.",
      original_announcements_preserved:true,
      acceptance_from_announcement_alone:false,
      final_acceptance_record:c.acceptance_path
    },
    point1:{
      complete:true,original_obligations:43,
      counts_by_step:{"3c":6,"3d":11,"3e":7,"3f":11,"3g":8},
      additional_inherited_obligations:["OBL-069"],
      actual_native_roots_audited:44,actual_eligible_admitted_inputs:50,
      original_audited_ancestor_modules:190,
      audited_boundary_unchanged_in_current_full_replay:true,
      required_reverse_dependencies_passed:true,
      evidence:c.acceptance_path
    },
    current_source:{
      compiled_commit:v.commit,compiled_tree:v.tree,
      source_modules:v.source_modules,source_manifest:"SOURCE.sha256",
      source_manifest_sha256:v.source_manifest_sha256,
      entire_current_source_graph_native_verified:true,
      frozen_unconditional_endpoint_verified:false
    },
    frozen_target:{
      path:"target/MainStatement.lean",sha256:v.frozen_target_sha256,
      changed:false,unconditional_theorem_completed:false,
      outstanding_explicit_bridge:"LeBrunSalamon.Milestone.PositiveQKSimpleConnectedness"
    },
    percentage_metric:{
      kind:"conservative accepted-checklist completion",
      accepted:74,denominator:133,pending:59,
      percentage:7400/133,percentage_display:55.64,rounded_percentage:56,
      mathematical_effort_estimate:false,time_remaining_estimate:false,
      ledger:"audit/MILESTONE_PROGRESS.json"
    },
    proof_completion_percentage:55.64,
    native_current_ci:{
      run_id:v.run_id,source_commit:v.commit,verified_current_modules:v.accepted_modules,
      selected_modules:v.selected_modules,fresh_native_passes:v.fresh_native_passes,
      reused_native_receipts:v.native_receipts_reused,status_counts:v.status_counts,
      complete_current_source_graph_passed:true,
      verification:c.verification_path,verification_sha256:c.verification_sha256,
      artifact:c.artifact,toolchain_lock_sha256:v.toolchain_lock_sha256,
      runtime_fingerprint:v.runtime_fingerprint,mathlib_revision:v.mathlib_revision,
      scope:"Current source graph, including the conditional assembly; not the final unconditional frozen theorem."
    },
    remaining_original_batches:Object.fromEntries(
      ["3h","3i","3j","3k","3l","3m","3n"].map(step=>[step,
        ledger.pending_original_obligations.filter(x=>x.substep===step).map(x=>x.id)])),
    remaining_original_obligations:47,
    definition_validations:{accepted:0,total:8,ids:ledger.definition_validations.map(x=>x.id)},
    final_gates:{accepted:0,total:4,ids:ledger.final_gates.map(x=>x.id)},
    next_execution_priorities:[
      "Compare the remaining extension/homogeneity route with Fu arXiv:2611.01423v1, preserving accepted foundations and documenting any scope change.",
      "Continue the47 original3h–3n obligations with exact published-input checks and proved project translations.",
      "Validate the8 operational definition bridges and discharge the explicit simple-connectedness bridge.",
      "Verify the unchanged unconditional frozen endpoint and all4 final milestone gates."
    ],
    admission_boundary_scope:"The50-leaf review certifies the44 accepted original roots. The remaining original obligations and final-theorem trust audit remain open.",
    notes:[
      "No new milestone units are credited for helper modules, source files, shared publication reviews or compilation receipts.",
      "Native current output reuse requires exact source, imports, direct dependency outputs, recursive source ancestry, runtime and compiler flags.",
      "Historical evidence-bound publication catalogs and audit records retain their original bytes; final acceptance is a separate event."
    ]
  };
};
