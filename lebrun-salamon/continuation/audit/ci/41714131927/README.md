# Full incremental CI run 41714131927

[GitHub Actions run](https://github.com/wajcha2/claude/actions/runs/41714131927), source commit `0e7a654645d92fe82473e358a925b47101305e97`, completed on 2026-11-03 at 21:07:07 UTC with **failure**.

The dependency-aware replay selected all 135 project modules. It safely reused 32 outputs from run 41685948946, freshly passed 65 more modules, failed 5 modules, and blocked 33 downstream modules. Thus 97 modules were accepted for this exact committed source graph. Final exhaustive validation found zero changed sources, dependency artifacts, or runtime files among those accepted outputs.

| Failing module | Diagnostics | First concrete issue |
| --- | ---: | --- |
| LSBranchRamification | 7 | Dependent stalk transport at line 214; later field-name and set-coercion errors |
| LSNodalFixedEnds | 84 | Pullback condition at line 114, followed by API and dependent rewriting errors |
| LSConicJets | 52 | Rewrite failure at line 107, then section-map API and dependent transport errors |
| LSClassicalActions | 4 | Composition association at line 64 and three unopened names |
| LSProductGeometry | 1 | The 2,000,000-heartbeat elaboration cap in componentAddition_denseRange |

All original diagnostic text is retained in `ERRORS.json` and the hashed native logs. These counts include cascading errors; they are not counts of mathematical gaps. Geometry and its gluing modules passed, as did the committed versions of LSHomVelocity, LSNodalTangent, LSIntrinsicVelocity, LSFirstJetEmbeddingGeometry and LSClassicalReduction.

## Verification

Artifact `13271232648` is 44,804,953 bytes. Its ZIP SHA-256, checked against GitHub's artifact digest, is `00a5b495b0a05e3fd90d81f47d37249f484f0bc8033b146cfd8963e041bc4380`.

The exact 135 source files, frozen target and toolchain lock were compared with the committed Git tree before the run finished. The downloaded receipts were then checked against that snapshot, complete accepted dependency ancestry, output and log hashes, and the pinned stock Lean/compiler-library files. Reused receipt provenance was checked against the previous downloaded artifact. Compiler memory cap was 12,000 MB; the pinned Lean and Mathlib revisions are recorded in the runtime configuration.

The source tree has since changed through additional proof work. At evidence collection, only **12** outputs still matched the current sources and their complete ancestor chains; these are listed in `VALIDATED_SEEDS.json`. The other 85 accepted old-head outputs are retained as evidence of this committed run, and may support clearly labeled frozen-head interface diagnostics. They do not accept the edited current graph.

The full graph and the only-published-admissions milestone are not accepted by this run.
