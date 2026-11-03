# LeBrun–Salamon source audit — 3 November 2026

## Scope and evidence boundary

This is a read-only source audit of `LeBrunSalamon_Cumulative_Precompile_Step3g_V2_20261103.zip`, compared with `LeBrunSalamon_Step3b_Final_20261101.zip`. No source was modified and no Lean compilation was run. The new inventory is lexical; a future native Lean dependency export must verify declaration identities and transitive admission dependencies.

Latest archive SHA-256: `722c44bc3e21211634732fc92fb0d598b429f886ac85dec3d3699318d4a3fe32`.

Baseline archive SHA-256: `5cd10ccfa75b92566913e140ce53c437563a60f5864c6f1c8f56799fd913b03c`.

The relevant source roots are `step3g_v2/cumulative/source` and `step3b/lebrun_step3b_final/source/strict_tree` in the recovered workspace. The separate baseline `MainStatement.lean` carries the frozen Step 2 statement. It is not part of the cumulative source tree.

## Verified source inventory

| Item | Count |
|---|---:|
| Current `.lean` source modules | 129 |
| Current source lines | 103,239 |
| Current source bytes | 4,995,434 |
| Lexically recognised declarations | 7,672 |
| Direct `sorry` tokens / admitted declarations | 98 / 98 |
| Direct `admit` tokens | 0 |
| Custom `axiom` tokens | 0 |
| Project `opaque` tokens | 0 |
| Admissions under a `PublishedInputs` namespace | 50 |
| Admissions outside those namespaces | 48 |
| New admitted declarations relative to Step 3b | 42 |
| Source modules changed relative to Step 3b | 19 |
| Reverse import closure of those changed modules | 120 |
| Modules in the archived cumulative build order | 21 |

The number 50 is a **namespace count**, not a count of certified exact published theorems. It consists of eight inherited SheafFunctoriality leaves and 42 new admissions: ExternalTensorDiagonal 6, BaseChangeFibers 10, Step3e 7, Step3f 11, ProjectiveLineGeometry 8.

The earlier admission scanner mishandles Lean `section`/`end` scopes and shortens several declaration names. The audit scanner tracks namespaces and sections separately and finds no unbalanced scopes. One notable declaration is syntactically introduced as `LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne` **inside** `LeBrunSalamon.Refinement.Boundary`, without `_root_.`. Its lexical full name is therefore `LeBrunSalamon.Refinement.Boundary.LeBrunSalamon.PublishedInputs.Step3f.regular_of_heightOne`; native Lean export should confirm this and the leaf ledger must use the actual name.

## Progress against the 91 baseline obligations

Every original Step 3b obligation still has a corresponding declaration. In batches 3c–3g, 43 wrappers now have source proof bodies without a direct admission. There are 42 new admitted leaves supplying those wrappers; this reflects one fewer direct admission overall. The source transformation is useful work, but does not establish that the corresponding mathematics has been proved or that each leaf satisfies the agreed exact-publication rule.

| Batch | Subject | Baseline obligations | Current wrappers still directly admitted | Current wrappers without a direct admission |
|---|---|---:|---:|---:|
| 3c | External tensors, diagonal jets, section descent | 6 | 0 | 6 |
| 3d | Base change, fibres, pushouts, total spaces | 11 | 0 | 11 |
| 3e | Ampleness, determinants, first jets | 7 | 0 | 7 |
| 3f | Infinitesimal algebra and nodal models | 11 | 0 | 11 |
| 3g | Projective-line geometry and source normalisation | 8 | 0 | 8 |
| 3h | Cotangent sequences and smoothness | 5 | 5 | 0 |
| 3i | Hom spaces, deformation smoothness, evaluation | 8 | 8 | 0 |
| 3j | Stable maps, nodal families, global functions | 8 | 8 | 0 |
| 3k | Finite covers and numerical ramification | 8 | 8 | 0 |
| 3l | Purity, branch geometry, extension | 6 | 6 | 0 |
| 3m | Contact directions and cone/product geometry | 5 | 5 | 0 |
| 3n | Automorphism groups, classification, metric recovery | 8 | 8 | 0 |
| **Total** | | **91** | **48** | **43** |

The eight 3i obligations include `homOpen_twoPointEvaluation_dominant`, which was only a deletion candidate in the original plan and remains in the preserved source. Consequently the original plan's expected count of seven cannot replace the actual count of eight.

The per-declaration map is `ORIGINAL_OBLIGATIONS.csv`, with correctly qualified names in `ADMISSIONS_QUALIFIED.json`. These are static inventories rather than proof certificates.

## Mathematical and boundary defects requiring repair

### 1. A new determinant admission is false as stated

In `RecompileBasePart05A.lean`, lines 208–214, `PublishedInputs.Step3e.symplecticDeterminant` assumes a rank `2*n` bundle `E`, a line bundle `L`, a bilinear form `b : E ⊗ E → L`, and perfection `IsIso (currySheaf b)`. It concludes `det E ≅ L^n`, but has **no alternating-form hypothesis**.

Perfection alone gives the square of the desired determinant identity, not the identity itself. For a concrete geometric counterexample, take a complex elliptic curve with a nontrivial order-two line bundle `N`, set `E = O ⊕ N` and `L = O`, and use a diagonal perfect symmetric pairing from `N ⊗ N ≅ O`. Then `det E = N` is nontrivial. This satisfies perfection for rank two but contradicts the admitted conclusion.

The repair is to require alternation in the exact generic Pfaffian theorem, then prove that the intrinsic Levi pairing satisfies that hypothesis before invoking it in `contact_distribution_determinant`. The wrapper currently passes only the nondegeneracy proof. This must be fixed before accepting the candidate, irrespective of whether Lean elaborates its `sorry` proof.

### 2. Renaming an admission has bypassed the plan's publication rule

`LSClassicalReduction.lean`, lines 37–47, admits `PublishedInputs.Step3e.polarizedEmbedding_firstJets` with precisely the project-facing hypothesis `E : PolarizedProjectiveEmbedding X L` and conclusion `SeparatesFirstJets X L`. The old wrapper is then proved by directly invoking this identical admitted signature. The agreed Step 3e plan explicitly says that this project statement must be derived from the actual closed immersion and fat-point restriction and is not itself a literature leaf.

`LSNodalFixedEnds.lean`, lines 57–77, is even explicit: the comment on `PublishedInputs.Step3f.dualThickening_hom_vanishing` calls it a “derived classical corollary, not a verbatim published lemma.” Its signature still mentions the project's `DualThickening` construction. Under the accepted plan it requires a Lean proof from exact generic inputs.

Thus the remaining milestone workload is **not** merely the 48 admissions outside `PublishedInputs`: the new 42 candidates also require individual statement, hypothesis, conclusion and translation audits. At least the above two are known to violate the agreed rule, and the determinant leaf is mathematically overstrong.

## Frozen endpoint is not implemented by the cumulative tree

No current source module contains any reference to `MainStatement`, `LeBrunSalamonStatement` or `WolfHomothety`.

`LSCompletedTargets.lean`, lines 65–71, exports `LeBrunSalamon.leBrunSalamon` with the conclusion only

```lean
IsLocallyRiemannianSymmetric n M
```

It supplies `Construction.constructedProjectInputs` internally, so there is no visible `ProjectInputs` hypothesis at that public endpoint. The constructor exists in `LSMovingPairConstruction.lean`, lines 81–91, and assembles the geometric argument from underlying admitted inputs. Absence of a package hypothesis does not remove those transitive admissions.

The source also has a stronger intermediate `project_symmetricHomothety` result. Its `SymmetricMetricModel` contains actual Riemannian data, positivity and global point symmetries; it is not a mere string label. However, it does not contain the simply-connectedness field of the frozen Step 2 `WolfSpaceModel`. The frozen MainStatement requires both parallel curvature and a `WolfHomothety`, and its definitions currently live in a standalone file importing only Mathlib. The definitions overlap with existing source names, so integration should extract/reuse one canonical foundational layer and prove the required transports rather than simply importing both files blindly.

The next plan must explicitly include the bridge from the actual constructed metric output to the frozen Wolf target, including simple connectedness and all definition-identification obligations recorded in Step 2. Preserving the standalone file's SHA is insufficient to prove that the exported theorem has its content.

## Compilation and reproducibility defects

The cumulative archive contains no `.olean` artifacts, module `result.json` files or `BUILD_PROGRESS.json`. Its `compilation_status = pending` and `kernel_replay = running` fields record a historical process state, not a successful result and not evidence of a still-running job.

`build_cumulative.py` depends on unavailable absolute `/mnt/data/...` paths for the toolchain, baseline artifacts and Step 3b artifacts. It is not a self-contained runner.

The archived `build_order.txt` includes all 19 directly changed files plus two intermediate modules, but omits 99 of their affected descendants, including `LSCompletedTargets`. The full affected cone has 120 modules. No direct dependency-order inversion appears among the listed 21, but imports can load old transitive dependencies: for example `LSContactLineTests` is scheduled before the revised foundational layers and imports `LSGenericSheets` from prior artifacts. A 21-module success cannot certify the full cumulative source or the final endpoint under the existing acceptance rule.

The reuse condition hashes only a module's own source and output; it does not record the hashes of its dependencies. Reusing an output after an upstream change can therefore accept stale elaboration. The script also recopies the Step 3b `RecompileBasePart04.olean` at every restart before resuming, even after a newer Part04 has previously been produced.

Recommended repair: use a topological order of the full changed reverse-dependency cone, key reuse on source, toolchain, flags and exact direct dependency artifacts, and inspect the final theorem's transitive trusted inputs. The audit provides `affected_build_order.txt` for the current source graph. A final clean build remains the clearest milestone gate; verified unchanged prerequisites can be reused for the next incremental pass with recorded hashes.

The internal `SOURCE_PARTIAL_MANIFEST.json` contains 137 entries. All but one hash match: `source/LSClassicalReduction.lean` retains the pre-import-minimisation hash `b899d7164fd941ca406d14cdfb9cc975db962f0a461008dfd25ce0f4c485559b`, whereas the current file hashes to `85476e875094b63829f118f765e74e9a134224f92ddb3da9f4b94f993ed5ca11`. This is consistent with the V2 status recording that import change. The archive-level checksum is sound, but the successor needs a regenerated internal manifest.

## Recommended interpretation of progress

The recoverable source contains substantial earlier constructions and an assembled legacy endpoint. The latest layer has refactored 43 wrapper bodies and identified a candidate published-input boundary. It has not yet passed either the full source compilation gate or the exact-publication gate, and the stronger frozen endpoint has not been connected.

Keep Step 3b as the recorded certified baseline, subject to its stated scope; retain the cumulative V2 as the working candidate. Reopen 3c–3g for exact-leaf review, repair the known determinant defect and the build evidence, and continue 3h–3n with the existing dependency order. Do not turn the namespace count or number of lines into a percentage of mathematical completion.
