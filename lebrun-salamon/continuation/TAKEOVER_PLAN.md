# LeBrun–Salamon formalisation: takeover audit and revised continuation plan

**3 November 2026**

## Decision

Continue from the actual cumulative Step 3g V2 source, preserving Step 3b as the last recorded passing incremental stage. Reopen the unverified parts of Steps 3c–3g. The first milestone is **not met**, and a successful compilation of the recovered source alone would not have met it: the audit found a false admitted determinant statement, several composite or project-specific admissions, and an exported conclusion weaker than the frozen specification.

The continuation branch is `codex/lebrun-takeover-audit-20261103` in `wajcha2/claude`. Commit `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0` preserves the recovered 129-module source without modification. Later commits contain the proof work described below, with separate compiler receipts. Historical branches and reports have been preserved.

This is a recovery and admission-boundary audit, with focused mathematical checks of consequential statements. It is not a line-by-line correctness audit of all 103,000 source lines.

## Point 1 checkpoint — 2026-11-04T00:03:44.890500+00:00

This immutable candidate contains **172 Lean modules and 85 direct `sorry` tokens**. The frozen target and pinned toolchain lock are unchanged. Exact candidate bytes are identified by `SOURCE.sha256` and [audit/point1_checkpoint/FREEZE.json](audit/point1_checkpoint/FREEZE.json). Source admission counts do not establish eligibility as published theorem inputs.

The latest completed full replay, [41732181431](https://github.com/wajcha2/claude/actions/runs/41732181431), checked commit `cdf4d8a5ae81407900431d905634c97bae4c9996` with all 155 modules selected. It accepted **121 modules: 28 strictly reused and 93 freshly compiled**. Four modules failed and 30 were blocked. The failed modules were `LSConicJets`, `LSRelativeDifferential`, `LSStandardConicDifferential`, and `LSProductGeometry`; their exact diagnostics are retained in [audit/ci/41732181431/](audit/ci/41732181431/).

That run freshly checked `RecompileSections`, Extensions Parts 01–04Geometry, `LSHomVelocity`, `LSNodalTangent`, `LSNodalFixedEnds`, and the integrated epsilon/Hom and family-degree helpers at its committed source. Every accepted source, import, dependency output, native artifact, log, and compiler/runtime identity was validated; final validation found no changed inputs or runtime files. Later edits change the dependency ancestry, so these 121 passes retain their exact-commit scope.

All **17 original Step 3c/3d obligations** now have native proof/source evidence: 14 project composites have proved translations and three are exact generic published inputs. Step 3d includes actual pullback and fibre exactness, canonical Hom base change and fibre injectivity, the generating-unit-open cover, and both total-line and total-bundle representations. Native public-type adapters and exhaustive dependency inventories are retained. The changed containing modules and live reverse dependency graph still require replay. See [audit/STEP3CD_ACCEPTANCE_LEDGER.md](audit/STEP3CD_ACCEPTANCE_LEDGER.md) and [audit/STEP3D_INTEGRATION_READY.json](audit/STEP3D_INTEGRATION_READY.json).

The original normalized-source-bivector signature is also now implemented by construction, symmetry, uniqueness, affine-frame normalization, and the second-diagonal argument. Its ten proof modules and exhaustive 82,298-constant diagnostic passed, with the old normalized-source admission absent. That diagnostic used historical project interfaces; its old diagonal and affine-derivation leaves have proved replacements in this candidate, which the fresh full replay must connect. Exact scope is recorded in [audit/p1_source_bivector_work/SCOPE.json](audit/p1_source_bivector_work/SCOPE.json).

The exact `LSRelativeDifferential` compatibility repair passed a focused native check over the frozen cdf ancestors. `LSProductGeometry` remains unverified: its parser and explicit-map candidate reached a 120-second local wall cap without emitting a new diagnostic. Its original generic product-geometry admission is unchanged and belongs to the later Step 3m work. The next full run must resolve this compilation gate; a local timeout does not certify a mathematical or source error.

The next stock-compiler replay selects all **172 modules**, with a 12000 MB cap and run **41732181431** as its sole cache source. Source, import, lock, output, and full project ancestry checks permit **30** cache outputs at this freeze. All other selected modules must compile against the candidate's actual dependencies. The replay revalidates the complete selected graph at completion; no result from that run is assumed.

**Point 1 remains open.** Its 43 obligations across Steps 3c–3g still require the stage acceptance gates: exact published statements, proofs of the nondefinitional project translations, and successful replay of the affected current sources and dependencies. The remaining proof work and compatibility candidates are recorded with their individual evidence. Off-graph unfinished drafts are excluded from the source graph.

The conservative accepted floor remains **30/133 = 22.56%, rounded to 23%**. This checkpoint adds no accepted checklist unit before the current source and proof-boundary gates pass. The published-theorem-only milestone and the frozen endpoint bridge remain open.

## Completion announcements and the evidence recovered

The user was explicitly told that **Steps 3c, 3d, 3e and 3f were finished**. The retrieved original conversation history records a cumulative announcement on 2 November 2026 at 20:35 CET marking 3c, 3d and 3e **"Passed cumulatively"**, followed at 22:46 CET by **"Step 3f completed — PASSED"**. These were completion claims, not merely reports that source editing had started.

The cumulative 3c–3e announcement named `LeBrunSalamon_Cumulative_Steps1_2_3a_3e_20261102.zip`, `LeBrunSalamon_Cumulative_1_2_3a_3e_REPORT.md`, and `LeBrunSalamon_Cumulative_1_2_3a_3e_STATUS.json`. A matching final certificate has not been recovered from the available file and repository searches. This is a statement about recovered evidence; it does not prove that the claimed later work never occurred. In particular, earlier failed or pending records, considered alone, cannot exclude a later successful run.

The surviving Step 3d report is itself inconsistent: it lists all eleven wrappers as proved, while also saying all eleven still contain direct admissions and that the replay and boundary checks did not pass. The Step 3e saved finalizer failed. Separately, the recovered cumulative V2 source contains the concrete mathematical and proof-boundary defects identified in this audit. Those are specific reasons for repair; they should not be conflated with missing historical build evidence.

The working status for **3c–3f is therefore: reported complete; source changes recovered; completion awaiting verification and identified repairs**. Keep the newer cumulative source and all recoverable work. "Step 3b is the last recorded passing incremental stage" describes the verified evidence boundary and does not describe the latest development position or authorize discarding the later work.

## 1. The recovered state before this proof batch

### Source and evidence

| Item | Verified finding |
|---|---|
| Latest recovered source archive | `LeBrunSalamon_Cumulative_Precompile_Step3g_V2_20261103.zip` |
| Archive SHA-256 | `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32` |
| Recovered source | 129 Lean modules; 103,239 lines; 4,995,434 bytes |
| Direct admissions | 98 `sorry` declarations; no lexical `admit`, custom `axiom`, or project `opaque` |
| `PublishedInputs` namespace inventory | 50 admissions: eight inherited from Step 3b and 42 new candidate leaves |
| Other direct admissions | 48 |
| Latest recorded passing incremental stage | Step 3b, 1 November 2026 |
| Step 3b accounting | 99 direct admissions; eight recorded published leaves; 91 further proof/refactoring obligations |
| Cumulative V2 kernel evidence | Pending; the archive contains no module build receipts or compiled outputs |
| Initial takeover correction | One source module amended; 98 direct admissions remained; no new `sorry`; not compiled at that point |

The latest archive checksum matches. All 174 entries in the Step 3b `FILES.sha256` also match. V2's old internal manifest has one stale source hash, for `LSClassicalReduction.lean`, consistent with its documented import change after the earlier manifest was produced. The continuation has a regenerated current source manifest.

The Step 3b evidence consists of successful checks of `RecompileBasePart03` and `RecompileBasePart04`, a compatibility import of 73 earlier artifacts, and its strict boundary checker. It must not be described as a clean compilation of the entire present proof. Three Step 3a groups were carried forward through recorded receipts and source hashes; their logs were not rematerialized in that report. These are historical evidence boundaries, not new kernel runs performed in this takeover.

### Why some previous progress reports cannot be used as acceptance evidence

The preserved Step 3e finalizer reports `passed = false`; its failed overlay left a packaged tree identical to Step 3b. The Step 3f delivery records also report a failed gate. Today's V2 is a real cumulative source recovery, but its `kernel_replay = running` field records a process state at the time of saving. It does not show that a job is still running or that the source passed.

GitHub had no later cumulative-project build result. Its successful runtime-packaging and standalone statement workflows are evidence for those narrower tasks. Before this takeover, the latest cumulative catalogue referred to archive parts that were absent from the Git tree; the new branch now contains the actual source files.

## 2. Where we are in the mathematical proof

The source contains the contact-geometric construction chain: contact lines and their families, nodal deformation and smoothing, moving pairs, descent of the global kernel, first jets, Hamiltonian spanning, homogeneous contact geometry, and Riemannian recovery. The public legacy endpoint assembles its input package internally; it does not simply assume `ProjectInputs` as a public theorem hypothesis. Nevertheless, the construction still depends on the admitted statements described below.

The immediate work is not merely to remove the visible `sorry` tokens in the final file. It is to verify the exact assumptions supporting this entire chain and supply the project-specific arguments between them.

### Original obligations against the existing plan

The following counts refer to the 91 obligations recorded after Step 3b. They measure source obligations, not equal amounts of mathematical effort.

| Step | Subject | Obligations | Current source state |
|---|---|---:|---|
| 3c | External tensors, diagonal jets, descent of sections | 6 | Exact-map and diagonal algebra proof work integrated; remaining coordinate bridges and cumulative acceptance pending |
| 3d | Base change, fibres, pushouts, total spaces | 11 | Actual fiber rank proof integrated; exactness, internal-Hom and scheme constructions still require translation/boundary gates |
| 3e | Ampleness, determinants, first jets | 7 | Seven project proof translations repaired or implemented; current dependency/reverse-cone and exact-leaf gates pending |
| 3f | Infinitesimal algebra and nodal local models | 11 | Actual cotangent deformation and normal-form proofs integrated; Hom vanishing and remaining local-model work pending |
| 3g | Projective-line geometry and source normalization | 8 | Projectivity, splitting, Laurent, Picard and marked tangent translations integrated; normalized bivector calculation and full acceptance remain |
| 3h | Cotangent sequences and smoothness criteria | 5 | Still directly admitted |
| 3i | Hom spaces, deformation smoothness, evaluation | 8 | Still directly admitted |
| 3j | Stable maps, nodal families, global functions | 8 | Still directly admitted |
| 3k | Finite covers and numerical ramification | 8 | Still directly admitted |
| 3l | Purity, branch geometry, extension | 6 | Still directly admitted |
| 3m | Contact directions and cone/product geometry | 5 | Still directly admitted |
| 3n | Automorphisms, classification, metric recovery | 8 | Still directly admitted |
| **Total** | | **91** | **43 rewritten wrappers; 48 original direct admissions** |

At recovery, those 43 rewritten wrappers were supplied by 42 new admitted declarations. The difference of one comes from deriving finite dimensionality from the rank calculation rather than introducing another admission. The rewritten wrappers do not yet count as 43 accepted proofs. In particular, the remaining workload is not just 48: the 42 new candidate leaves require individual review, and the final-statement bridges are additional explicit work.

Step 3a removed 22 dead admissions, retained the live two-point evaluation theorem, and identified `stageDescription` as a false-positive string match. Accordingly Step 3i has eight surviving obligations, rather than the seven anticipated before deletion triage.

## 3. Mathematical findings and their current repairs

### 3.1 The determinant input omitted an essential hypothesis

The recovered `PublishedInputs.Step3e.symplecticDeterminant` assumes only a perfect bilinear form

\[
b:E\otimes E\longrightarrow L,\qquad \operatorname{rk}E=2n,
\]

and concludes \(\det E\simeq L^{\otimes n}\). Alternation was missing. Perfection alone gives the squared determinant relation and is insufficient for this conclusion.

For a concrete counterexample, let \(T\) be a nontrivial two-torsion line bundle on a complex elliptic curve. Put \(E=\mathcal O\oplus T\), \(L=\mathcal O\), and choose \(T^{\otimes2}\simeq\mathcal O\). The diagonal symmetric pairing on \(E\) is perfect, but \(\det E=T\) is nontrivial. The admitted conclusion would trivialize \(T\).

The continuation adds the explicit condition \(b(u,u)=0\) on sections. Its contact application supplies this condition using the existing `intrinsicLevi_alternating` theorem and the tensor universal pairing. The correction introduces no new mathematical assumption on contact manifolds and no additional `sorry`.

The replacement admitted theorem is now `PublishedInputs.Step3e.alternatingDiscriminantTrivial`, restricted to a smooth proper connected complex base. Its source is Asher Auel's [2009 dissertation](https://math.dartmouth.edu/~auel/papers/docs/AUEL_thesisSS.pdf), Proposition 1.10 (trivial discriminant of a regular alternating form) and Definition 1.7 (the underlying discriminant line). The project proves the conversion from triviality of \((L^\vee)^{\otimes n}\otimes\det E\) to \(\det E\simeq L^{\otimes n}\) by tensor associativity, symmetry and evaluation. `RecompileBasePart05A` and its complete current ancestor graph passed fresh stock-compiler CI in run 41682674689. The [current-artifact native audit](audit/current_determinant_build/README.md) confirms the five remaining admitted inputs and excludes the false original theorem. The 12000 MB replay subsequently passed Part07 without a proof-source change. Acceptance of the current edited reverse-dependency cone remains a separate gate.

### 3.2 Several obligations were renamed without completing their required proofs

These are concrete examples, not a rejection of the underlying classical mathematics:

- `normalizedSourceBivector` still directly assumes the project's diagonal vanishing and normalized contact symbol. Step 3g requires the calculation on \(\mathbf P^1\times\mathbf P^1\), its normalization, and the actual interface identifications.
- At recovery, `laurentExpansionAtPole` admitted a composite of compactification, pole, completion and Laurent-order assertions. The current candidate instead proves the project conclusion from four separately stated field-theoretic inputs, with actual residue and completion maps and the order comparison. Its isolated Mathlib-only proof check passed; exact reference and cumulative acceptance gates remain explicit.
- `dualThickening_hom_vanishing` explicitly calls itself a derived classical corollary in its comment, while retaining a direct `sorry` and the project-specific `DualThickening` interface.
- The diagonal second-derivative detection theorem and the formal two-component model likewise require the compositions and coordinate comparisons described in the original plan.

The detailed locations and further examples are in [the published-boundary audit](audit/PUBLISHED_BOUNDARY_AUDIT.md). A `PublishedInputs` namespace is organizational metadata. It does not establish that the admitted statement is a published theorem.

The first-jet and zero-section admissions, the Laurent composite, four Base04 Step 3e admissions and several further point-1 translations now have actual proof candidates. Their exact native diagnostic scope is recorded separately. The still-admitted normalized bivector and Hom-vanishing examples remain open; no full stage acceptance is inferred from these partial advances. An independent primary-source comparison also established publication eligibility for the height-one normal-domain extension leaf and the two affine derivation leaves. That comparison alone is not a kernel or transitive-trust pass.

### 3.3 The frozen target still requires its full endpoint bridge

The frozen Step 2 target requires both

```lean
IsLocallyRiemannianSymmetric n M ∧
  Nonempty (WolfHomothety (closedRiemannianSpace n M))
```

under the ordinary closed connected positive quaternionic–Kähler hypotheses and `2 ≤ n`. Its SHA-256 remains unchanged.

`source/LSCompletedTargets.lean` concludes only `IsLocallyRiemannianSymmetric n M`. At recovery no source module referenced `WolfHomothety` or `LeBrunSalamonStatement`. There is a genuine intermediate symmetric-homothety construction, but its target structure does not supply all fields of the frozen Wolf target, including simple connectedness.

`LSMilestoneStatement` now imports the shared foundational core and retains the entire frozen `AuditedStatement` namespace byte-for-byte. It and `LSMilestoneTopology` passed a fresh CI build. `LSMilestoneTarget` supplies explicit inverse transports between the old and audited structures and assembles the frozen conclusion conditional on `PositiveQKSimpleConnectedness`. The condition must still be derived from the original positive-QK hypotheses using an exact published theorem and the relevant definition identifications. The eight definition-validation obligations recorded in Step 2 remain in scope; a compiled definition is not itself a completed definition-validation proof.

## 4. Compilation must follow the real dependency graph

At recovery nineteen source modules differed from Step 3b. Their reverse import closure contained 120 modules. The old replay script listed only 21 and omitted 99 affected descendants, including the final target module. This frozen continuation has 149 modules and regenerates the rebuild plan from its actual imports; see `audit/current/REBUILD_PLAN.json` for current hashes and the full order.

The old reuse condition recorded only a module's own source and output hashes, not the artifacts of its dependencies. It also restored an old Part04 artifact on every restart. The replacement runner records exact direct dependency hashes, rejects stale artifacts and revalidates the whole selected batch at the end. Twelve simulated bookkeeping cases cover invalidation and source/artifact changes during a run; they are infrastructure tests, not Lean proof evidence.

Use the exact locked Lean `v4.36.0-rc1` and mathlib revision `116662aa4c1e9106ab5c609b3214b02f6e11a65a`. At the end of a coherent completed source batch, rebuild its unchecked or invalidated dependency cone in topological order. Reuse an artifact only if its source, toolchain, flags and exact dependency artifacts match its receipt. Unchanged source text alone is insufficient. If the required receipt is absent, the module remains unchecked.

The portable static checker and generated rebuild plan identify the affected source modules. They deliberately do not claim Lean verification. The final Step 3o gate still requires the whole final proof graph and its transitive admissions to be checked; rebuilding mathlib unnecessarily is not part of this plan.

## 5. Revised execution order

The mathematical subdivision 3a–3o remains useful. The change is to repair its enforcement and expose the endpoint work now.

1. **Recover and preserve the source — completed.** Actual source, frozen target, toolchain lock, hashes, admission inventory and historical evidence are preserved on the continuation branch. The original recovery commit remains available.
2. **Correct demonstrably invalid assumptions — determinant repair implemented and diagnostically compiled.** Its published leaf is now restricted to the applicable scope and its project conversion proved. Audit the remaining newly introduced leaf signatures before accepting a cumulative stage. Do not change the main theorem's hypotheses to make an input available.
3. **Connect the exact target and audit the difficult geometric inputs in parallel.** Make the frozen Wolf-homothety target importable through shared definitions, and map its missing bridges. Independently audit the high-risk branch/transversality/purity inputs in 3l and the global recovery in 3n, so a substantive obstruction is discovered before polishing all routine wrappers.
4. **Complete and accept 3c–3g in dependency order.** Start with exact Künneth/projection-formula/diagonal leaves and explicit translations; verify base-change maps; complete the first-jet argument; isolate square-zero and nodal algebra; prove the normalized source calculation. Literature checking and independent proofs may proceed in parallel, while source integration respects imports.
5. **Continue the remaining 48 original admissions in 3h–3n.** Keep the plan's dependency order for cotangents, Hom deformation, stable maps, finite covers, branch geometry, contact directions and final classification. Record any genuinely new obligation explicitly rather than hiding it in a stronger admitted theorem.
6. **Run the incremental kernel checks only after the batch is ready.** Validate receipts and rebuild the full affected cone. A build result records compilation; a separate publication audit records which assumptions are allowed.
7. **Pass Step 3o on the frozen target.** Verify the actual final theorem type and all transitive trusted inputs. Every remaining admission must match an accepted exact published theorem, with the specializations and compositions proved in Lean. No project-specific axiom, hidden proof-package assumption, weakened conclusion, or unsupported transport may remain.

### Required record for every retained admission

Each ledger row must contain the actual fully qualified Lean declaration, its expanded mathematical statement, one stable publication locator, the hypothesis/conclusion comparison, the separate project-translation theorem, and the kernel receipt for that translation and its affected dependencies. Mark composite corollaries and statements awaiting a reference as open proof obligations. The current lexical scanner is provisional; native Lean declaration/dependency output must confirm the final names and graph.

## 6. What the first milestone will mean

The milestone will be reported as complete only when one reproducible source revision simultaneously has:

- the exact frozen mathematical conclusion, including the Wolf homothety;
- successful kernel evidence for all required project modules and the final theorem;
- an exhaustive, individually checked list of precisely published admitted theorems;
- Lean proofs of every novel argument, composite application and project-specific translation;
- a transitive assumption audit consistent with that list and no concealed extra assumptions.

At present these conditions are not satisfied. The current batch supplies real compiled proof work and independent CI evidence within explicit scopes. [The progress ledger](audit/MILESTONE_PROGRESS.md) uses fixed acceptance obligations and gives separate credit only when their full gates are met. It is a conservative completion floor, not a prediction of the fraction of mathematical effort or elapsed time remaining.
