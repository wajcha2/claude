# LeBrun–Salamon formalisation — start here for takeover

Prepared **5 November 2026**. This handoff preserves the accepted development, the latest unfinished proofs, the failed diagnostic variants and their evidence, the proof plan, and the exact acceptance boundary. It is a documentation handoff: it adds no proof-completion credit.

## 1. Get the correct snapshot

Repository: **wajcha2/claude**. Handoff branch: **codex/lebrun-agent-handoff-20261105**.

The repository's default branch is unrelated to this continuation. Select the handoff branch explicitly:

```bash
git clone -c core.autocrlf=false --single-branch --depth 1 --branch codex/lebrun-agent-handoff-20261105 https://github.com/wajcha2/claude.git lebrun-handoff
cd lebrun-handoff
python3 lebrun-salamon/continuation/handoff/2026-11-05/verify_handoff.py --root .
```

The integrity command checks every preserved LeBrun–Salamon file and associated workflow against the pinned base, then checks the added handoff files. It does not compile Lean or grant acceptance. Preserve UTF-8 bytes and LF line endings; the clone option above disables automatic line-ending conversion. The native build instructions assume Linux, as in the accepted CI run.

The accepted base is **11c18cdcb5e92e3975626a6a1276abfe419ad4f8**, tree **a78c46ad6af4a3d96a42b8bd47895de30fcb92f6**. Its 308 production modules are exactly those compiled at **4d1aa547453f50736035a91f6fea81d340359143** in [successful native run 41912044307](https://github.com/wajcha2/claude/actions/runs/41912044307).

For a new proof attempt, create a work branch from this handoff. Keep the pinned accepted sources and evidence available for comparison. No predecessor scratch directory, running agent, or conversation transcript is needed to recover the saved work.

## 2. Read these next

1. **[Unfinished work and integration order](handoff/2026-11-05/UNFINISHED_WORK.md)** — exact latest source filenames, what each prototype proves, what is still assumed, failed variants, and the mathematical gap in OBL-056.
2. **[Build and resume instructions](handoff/2026-11-05/BUILD_AND_RESUME.md)** — toolchain, artifact retrieval, exact historical reproduction, and how to start a new compilation.
3. **[Published inputs, statement fidelity, and final gates](handoff/2026-11-05/ACCEPTANCE_RULES.md)** — what may retain a `sorry`, all remaining definition validations, and the limits of current certification.
4. **[Current proof plan](TAKEOVER_PLAN.md)** and **[milestone ledger](audit/MILESTONE_PROGRESS.md)** — the accepted status and original obligation accounting.
5. **[Machine-readable handoff snapshot](handoff/2026-11-05/SNAPSHOT.json)** and **[complete unfinished-file index](audit/deferred_next_steps_20261104/INDEX.json)** — exact commits, hashes, scope, and file identities.

## 3. Current accepted status

The first milestone is **one reproducible current source revision proving the frozen theorem with `sorry` only for exact known published theorems**.

| Item | Status |
| --- | --- |
| Fixed checklist | **79/133 = 59.40% accepted** |
| Original proof obligations remaining | **42** |
| Definition validations remaining | **8** |
| Final gates remaining | **4** |
| Current production modules compiled | **308/308** |
| Most recently accepted original obligations | **OBL-044 through OBL-048, Step 3h** |
| Current audited original-root boundary | **49 roots, 54 distinct eligible published inputs** |
| Full requested milestone | **Open** |

The 79 accepted units comprise 22 retired original admissions, eight historical Step 3b wrappers, 43 Point 1 obligations, separately accepted OBL-069, and the five Step 3h obligations. The percentage measures this fixed checklist; it is not a measure of mathematical effort, time, or code volume.

The 49-root audit used 39 fresh native dependency walks and 10 reused walks with exactly matching full native contexts. Its 54-input count applies to that boundary. It does not certify the pending original obligations or the final theorem.

The current assembly still has the explicit `LeBrunSalamon.Milestone.PositiveQKSimpleConnectedness` bridge. The unchanged unconditional target, including the actual positive-metric Wolf homothety, is not yet established. The semantic definition checks and all four final milestone gates remain open.

Primary evidence: [Step 3h acceptance](audit/step3h_acceptance_41912044307/STEP3H_ACCEPTANCE.json), [full current-source verification](audit/step3h_acceptance_41912044307/FULL_CONTINUATION_VERIFICATION.json), and [root's final publication readback](handoff/2026-11-05/PREVIOUS_ROOT_READBACK.json).

## 4. Where everything is

All paths below are relative to `lebrun-salamon/continuation/`.

| Path | Contents and scope |
| --- | --- |
| `source/` | The accepted 308-module production Lean source. |
| `target/MainStatement.lean` | The frozen theorem specification. Preserve its hypotheses and both conclusions. |
| `SOURCE.sha256`, `TOOLCHAIN.lock.json` | Source and historical toolchain locks; see the build note for effective native flags. |
| `scripts/` | Published static checkers, native compilation drivers, cache validators, dependency audits, and evidence finalizers. |
| `audit/MILESTONE_PROGRESS.json` | Original obligation identities, accepted and pending units, eight definition validations, four final gates, and evidence links. |
| `audit/deferred_next_steps_20261104/` | **35 groups, 126 indexed files plus the index itself, including 41 Lean files.** Contains all saved unfinished source, prototypes, proposed replacements, planning notes, reviews, and diagnostic evidence. |
| `audit/step3h_acceptance_41912044307/` | Accepted native/source/publication records and the lossless native text-evidence archive. |
| `audit/continuation_3h/` | Step 3h baseline/candidate records, earlier attempts, cache bindings, and the Fu comparison. |
| `audit/history/` and other audit subdirectories | Previous accepted states, original dependency plans, repair history, failed attempts, and detailed evidence. |
| `handoff/2026-11-05/` | This takeover guide's supporting notes, complete base inventory, verifier, and recovered supplemental reviews. |

The associated repository workflows are in `.github/workflows/lebrun-*.yml`. The handoff retains all **11,667** pre-existing project/workflow files (**110,186,611 bytes**) from the accepted snapshot without modifying their contents. This total includes historical evidence; it is not a count of active Lean modules.

When retrieving through the GitHub connector, a large file may be returned with empty `content` by the file endpoint. Fetch its immutable Git blob from the tree instead; an empty endpoint representation is not evidence of an empty file. This applies in particular to the complete inventories and large evidence envelopes.

The existing `CONTINUATION_FILES.sha256` is the accepted-base inventory. Added handoff files are covered separately by `handoff/2026-11-05/HANDOFF_FILES.sha256`; the latter excludes itself. `BASE_INVENTORY.json` binds every pre-existing project/workflow path to its Git blob and size.

## 5. Latest unfinished part — do not overlook these files

The unfinished-file index is authoritative for exact saved filenames and hashes. Its groups are not all at the same completion level.

- **Early Hom constructions:** `early_hom_construction/core_source.lean` and `absolute_source.lean` provide the early-import constructor organization. They avoid the later Geometry/SectionRepresentability/Ext02 import cycle; they do not prove existence of a representing scheme.
- **Presentation and stratum comparison:** `hom_presentation_comparison/`, `relative_hom_reverse_comparison/`, `basechangeHom/`, and `fixed_degree_open_transport/` contain the all-test comparisons and transport of supplied data. The initial representer and initial bounded stratum remain separate existence obligations.
- **Latest free-neighbourhood proof:** `obl053_free_open_transport/source.lean` is the reviewed successful FreeOpen transport, with its boundary, evidence, and root review. It transports all 13 fields of supplied data; it does not construct the first free neighbourhood.
- **Conditional OBL-052 / proposed OBL-055 and OBL-057 integration:** the `conditional052_closure/`, `criterion_specialization/`, `obl052_integration_proposal/`, `obl055_integration_proposal/`, and `integrality_integration_proposal/` groups contain the compositions and proposed source replacements. `combined_future_static_review/` reviews a 311-module proposal. That proposed integration is statically checked but has not passed full native integration.
- **Latest OBL-056 support:** `parameter_family_lifting/`, `smooth_locus_neighborhood/`, `obl056_finite_yoneda_h1/`, `obl056_ordinary_lifting/`, `obl056_residue_field_boundary/`, `small_extension_kernel_algebra/`, and `obl056_central_coefficient/` contain the saved supporting proofs.
- **Last completed supporting construction:** `obl056_residue_point_lifting/source.lean` is the successful residue-point V2 source. Its `progress_markdown.md` and `progress_index.json` update the earlier `obl056_progress_note/`. The later update resolves the test-centre construction only; the full deformation/cohomology bridge remains open. A further [independent residue review](handoff/2026-11-05/RESIDUE_POINT_LIFTING_INDEPENDENT_REVIEW.json), previously stored only as a Git blob, is now attached with this handoff.

All group paths in this section are beneath `audit/deferred_next_steps_20261104/`. The [unfinished-work guide](handoff/2026-11-05/UNFINISHED_WORK.md) maps them to original diagnostic module names and explains their dependencies.

These preparations contribute **zero accepted original obligations so far**. Some proofs compiled in an older verified local dependency pool. Their source, compiler outputs, exact dependency scopes, and failed variants are retained; a new integration must revalidate the affected current contexts. Neither their local success nor a statically acyclic import graph is full current-source acceptance.

## 6. Next mathematical work

Continue Step 3i with one coherent relative-Hom construction. Use the saved all-test comparisons and early-import organization, then address the genuine representability and bounded-stratum existence requirements. Transport lemmas alone do not supply those existence statements.

For OBL-056, use the latest residue-point addendum. Complete the identification of the actual flat family's square-zero ideal and obstruction coefficients with the fibre tangent-sheaf coefficients. This includes the internal-Hom/dual/tensor/residue-scalar, pushforward, and cohomology comparisons. Then construct the required global small-Artin-extension lifting and pass to the pointwise smoothness conclusion. The proposed SGA 1 and Stacks boundaries are still proposals requiring exact source/type review; a dual-number-only criterion is insufficient for this step.

After integration, run the native compiler and actual transitive admission audits before updating the ledger. Preserve original theorem statements and actual geometric maps. Prove project-specific applications and transports explicitly, and count completion only against the original obligation IDs.

The [Fu-route review](audit/continuation_3h/FU_ROUTE_REVIEW.md) records a possible simplification for later branch geometry, especially OBL-073–077. It does not retire those obligations. The coarse-family comparison, reduced-base conic charts, contact/evaluation compatibility and the correct single-target Picard-one slice remain to be formalised before adopting that route.

## 7. Reproduction details that matter

The exact historical staged Step 3h verifier protects the then-current baseline ledger. Reproduce that historical native event in a **separate checkout at compiled commit 4d1aa547...**, following [BUILD_AND_RESUME.md](handoff/2026-11-05/BUILD_AND_RESUME.md). Use this handoff/accepted checkpoint for current status and unfinished work. Keep the 79/133 accepted ledger intact.

Likewise, `TOOLCHAIN.lock.json` retains historical `-M5400`, while the reviewed generated native runtime used `-M12000`. The effective runtime, precise flags, and dependency fingerprints are bound by the native evidence. Follow the build note and existing validators instead of silently conflating the two.

The final native artifact is `lebrun-3h-current-native-41912044307-1`, ID **13366173425**, ZIP SHA-256 **aa96014256646d209d710f8b32e98ab61991c0a9c5d1020b38a66876b3e60f3d**. Its availability and the bootstrap artifacts were rechecked on 5 November 2026. Source and text evidence are committed; compiled caches are downloadable Actions artifacts with the retention dates recorded in the build note.

## 8. Short instruction to the successor

> Take over the LeBrun–Salamon formalisation from this handoff. Read the unfinished-work, build/resume, acceptance-rules, and current-plan documents before editing. The accepted baseline is 79/133 checklist units and 308 compiled production modules. Preserve the frozen theorem and all existing acceptance evidence. Recover and use the saved 35 unfinished-work groups, particularly the latest OBL-056 residue-point addendum and the early Hom construction. Distinguish accepted results, isolated checked proofs, conditional compositions, and uncompiled source proposals. Continue toward the milestone of sorry proofs only for exact known published theorems. Record each integrated proof, run the required native and dependency checks, and report progress against the unchanged 133-unit ledger.
