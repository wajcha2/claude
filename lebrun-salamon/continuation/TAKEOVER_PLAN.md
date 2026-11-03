# LeBrun–Salamon formalisation: takeover audit and revised continuation plan

**3 November 2026**

## Decision

Continue from the actual cumulative Step 3g V2 source, preserving Step 3b as the last recorded passing incremental stage. Reopen the unverified parts of Steps 3c–3g. The first milestone is **not met**, and a successful compilation of the recovered source alone would not have met it: the audit found a false admitted determinant statement, several composite or project-specific admissions, and an exported conclusion weaker than the frozen specification.

The new continuation branch is `codex/lebrun-takeover-audit-20261103` in `wajcha2/claude`. Commit `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0` preserves the recovered 129-module source without modification. The continuation then records a minimal determinant correction, explicitly awaiting kernel verification, together with this audit and plan. Historical branches and reports have been preserved.

This is a recovery and admission-boundary audit, with focused mathematical checks of consequential statements. It is not a line-by-line correctness audit of all 103,000 source lines.

## 1. The precise current state

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
| Current takeover correction | One source module amended; 98 direct admissions remain; no new `sorry`; not compiled |

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
| 3c | External tensors, diagonal jets, descent of sections | 6 | Wrapper bodies rewritten; new assumptions require review and kernel checks |
| 3d | Base change, fibres, pushouts, total spaces | 11 | Wrapper bodies rewritten; new assumptions require review and kernel checks |
| 3e | Ampleness, determinants, first jets | 7 | Wrapper bodies rewritten; definite determinant defect found and amended provisionally |
| 3f | Infinitesimal algebra and nodal local models | 11 | Wrapper bodies rewritten; several admitted composites remain |
| 3g | Projective-line geometry and source normalization | 8 | Wrapper bodies rewritten; normalization and other translations still require proofs |
| 3h | Cotangent sequences and smoothness criteria | 5 | Still directly admitted |
| 3i | Hom spaces, deformation smoothness, evaluation | 8 | Still directly admitted |
| 3j | Stable maps, nodal families, global functions | 8 | Still directly admitted |
| 3k | Finite covers and numerical ramification | 8 | Still directly admitted |
| 3l | Purity, branch geometry, extension | 6 | Still directly admitted |
| 3m | Contact directions and cone/product geometry | 5 | Still directly admitted |
| 3n | Automorphisms, classification, metric recovery | 8 | Still directly admitted |
| **Total** | | **91** | **43 rewritten wrappers; 48 original direct admissions** |

Those 43 rewritten wrappers are supplied by 42 new admitted declarations. The difference of one comes from deriving finite dimensionality from the rank calculation rather than introducing another admission. The rewritten wrappers do not yet count as 43 accepted proofs. In particular, the remaining workload is not just 48: the 42 new candidate leaves require individual review, and the final-statement bridges are additional explicit work.

Step 3a removed 22 dead admissions, retained the live two-point evaluation theorem, and identified `stageDescription` as a false-positive string match. Accordingly Step 3i has eight surviving obligations, rather than the seven anticipated before deletion triage.

## 3. Mathematical findings that change the continuation priorities

### 3.1 The determinant input omitted an essential hypothesis

The recovered `PublishedInputs.Step3e.symplecticDeterminant` assumes only a perfect bilinear form

\[
b:E\otimes E\longrightarrow L,\qquad \operatorname{rk}E=2n,
\]

and concludes \(\det E\simeq L^{\otimes n}\). Alternation was missing. Perfection alone gives the squared determinant relation and is insufficient for this conclusion.

For a concrete counterexample, let \(T\) be a nontrivial two-torsion line bundle on a complex elliptic curve. Put \(E=\mathcal O\oplus T\), \(L=\mathcal O\), and choose \(T^{\otimes2}\simeq\mathcal O\). The diagonal symmetric pairing on \(E\) is perfect, but \(\det E=T\) is nontrivial. The admitted conclusion would trivialize \(T\).

The continuation adds the explicit condition \(b(u,u)=0\) on sections. Its contact application supplies this condition using the existing `intrinsicLevi_alternating` theorem and the tensor universal pairing. The correction introduces no new mathematical assumption on contact manifolds and no additional `sorry`. It is still a **source candidate**, not a kernel-verified repair.

The familiar symplectic determinant statement is illustrated precisely by Biswas–Hoffmann, *Some moduli stacks of symplectic bundles on a curve are rational*, §2, equation (1) and the following paragraph: [arXiv:math/0604183v2](https://arxiv.org/pdf/math/0604183). That source treats the bundle statement on curves. The arbitrary-scheme leaf still needs an exact reference at that scope, or a proof from a precise ring-level Pfaffian theorem and gluing. The narrower reference must not silently certify the broader statement.

### 3.2 Several obligations were renamed without completing their required proofs

These are concrete examples, not a rejection of the underlying classical mathematics:

- `polarizedEmbedding_firstJets` has the same project-facing embedding/first-jet signature under a new admitted name. Step 3e explicitly requires proving the argument through the actual closed immersion and fat-point restriction.
- `normalizedSourceBivector` still directly assumes the project's diagonal vanishing and normalized contact symbol. Step 3g requires the calculation on \(\mathbf P^1\times\mathbf P^1\), its normalization, and the actual interface identifications.
- `laurentExpansionAtPole` combines compactification, a boundary pole, completion of a DVR, a coefficient field, passage to fractions, and negative Laurent order. Its five cited ingredients do not constitute one published theorem with the admitted composite conclusion.
- `dualThickening_hom_vanishing` explicitly calls itself a derived classical corollary in its comment, while retaining a direct `sorry` and the project-specific `DualThickening` interface.
- The diagonal second-derivative detection theorem and the formal two-component model likewise require the compositions and coordinate comparisons described in the original plan.

The detailed locations and further examples are in [the published-boundary audit](audit/PUBLISHED_BOUNDARY_AUDIT.md). A `PublishedInputs` namespace is organizational metadata. It does not establish that the admitted statement is a published theorem.

### 3.3 The frozen target is not connected to the exported theorem

The frozen Step 2 target requires both

```lean
IsLocallyRiemannianSymmetric n M ∧
  Nonempty (WolfHomothety (closedRiemannianSpace n M))
```

under the ordinary closed connected positive quaternionic–Kähler hypotheses and `2 ≤ n`. Its SHA-256 remains unchanged.

`source/LSCompletedTargets.lean` currently concludes only `IsLocallyRiemannianSymmetric n M`. No recovered source module references `WolfHomothety` or `LeBrunSalamonStatement`. There is a genuine intermediate symmetric-homothety construction, but its target structure does not supply all fields of the frozen Wolf target, including simple connectedness.

The standalone target and source also overlap in their foundational names. Integration must reuse one set of definitions and prove the necessary identifications; merely importing both files is not a solution. Preserve the immutable target as a specification and prove equivalence of the importable formulation to it. The eight definition-validation obligations recorded in Step 2 remain in scope.

## 4. Compilation must follow the real dependency graph

Nineteen recovered source modules differ from Step 3b. Their reverse import closure contains 120 modules. The old replay script lists only 21 and omits 99 affected descendants, including the final target module. It can therefore finish its list without checking the current full argument.

The old reuse condition records only a module's own source and output hashes, not the artifacts of its dependencies. It also restores an old Part04 artifact on every restart. Both behaviours can preserve obsolete elaboration after an upstream change. Its absolute paths point into a previous workspace.

Use the exact locked Lean `v4.36.0-rc1` and mathlib revision `116662aa4c1e9106ab5c609b3214b02f6e11a65a`. At the end of a coherent completed source batch, rebuild its unchecked or invalidated dependency cone in topological order. Reuse an artifact only if its source, toolchain, flags and exact dependency artifacts match its receipt. Unchanged source text alone is insufficient. If the required receipt is absent, the module remains unchecked.

The portable static checker and generated rebuild plan identify the affected source modules. They deliberately do not claim Lean verification. The final Step 3o gate still requires the whole final proof graph and its transitive admissions to be checked; rebuilding mathlib unnecessarily is not part of this plan.

## 5. Revised execution order

The mathematical subdivision 3a–3o remains useful. The change is to repair its enforcement and expose the endpoint work now.

1. **Recover and preserve the source — completed.** Actual source, frozen target, toolchain lock, hashes, admission inventory and historical evidence are preserved on the continuation branch. The original recovery commit remains available.
2. **Correct demonstrably invalid assumptions — started.** The determinant hypothesis and its contact application have been amended provisionally. Audit the remaining newly introduced leaf signatures before accepting their compilation as progress. Do not change the main theorem's hypotheses to make an input available.
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

At present these conditions are not satisfied. The useful progress from this takeover is a recoverable canonical working source, a corrected understanding of its proof boundary, one explicit mathematical repair candidate, and a dependency-aware continuation plan. A percentage based on source lines or namespace counts would not describe the remaining work accurately.
