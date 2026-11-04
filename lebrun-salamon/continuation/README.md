# LeBrun–Salamon formalisation: continuation

**Point 1 is complete. The full published-theorems-only milestone remains open.**

The accepted checklist total is **74/133 = 55.64%, rounded to 56%**: 22 retired original admissions, eight historically accepted Step 3b wrappers, 43 Point 1 obligations, and the separately accepted OBL-069. The denominator remains 121 original admissions plus eight definition validations and four final gates. This measures fully accepted checklist units; it is not an estimate of mathematical effort, elapsed time, or the proportion of source lines. Helper modules, compatibility repairs, shared publication reviews and compilation receipts do not add units.

## Accepted scope

| Step | Original obligations accepted |
|---|---:|
| 3c — external tensors and diagonal sections | 6/6 |
| 3d — base change, fibers and total spaces | 11/11 |
| 3e — determinants, ampleness and first jets | 7/7 |
| 3f — infinitesimal algebra and nodal models | 11/11 |
| 3g — projective-line geometry and normalization | 8/8 |
| **Point 1** | **43/43** |
| Separate inherited affine-projection obligation OBL-069 | 1/1 |

The binding decision is [the final Point 1 acceptance record](audit/point1_acceptance_final_20261104T184658Z/POINT1_ACCEPTANCE.json). The original completion announcements for 3c, 3d, 3e and 3f, recovered sources and earlier audit records remain preserved.

## Native verification

[Native run 41888465259](https://github.com/wajcha2/claude/actions/runs/41888465259) verifies **307/307 current source modules**. In this run, 2 passed by fresh compilation and 305 reused native receipts matched the current source, imported outputs, recursive ancestry, runtime and compiler flags. All **190 modules** underlying the Point 1 declaration audits match their audited source, imports, outputs, direct dependencies and recursive ancestry exactly. The frozen statement and toolchain lock are unchanged.

See [the full verification report](audit/ci/41888465259/FULL_REPLAY_VERIFICATION.json) for the exact source manifest, runtime, artifact and dependency hashes.

## Published-input boundary

The native declaration audit covers **44 original roots**: 43 Point 1 obligations and OBL-069. Their actual dependency closure contains **50 distinct directly admitted published inputs**, each reviewed against its primary source, hypotheses, conclusion and maps. No original project conclusion is directly admitted in this audited boundary. No missing constant, custom project axiom or unexpected axiom was found. All 44 original public headers match after removal of comments and whitespace. Explicit native type events are recorded for the 15 roots in the changed tranche; no retrospective native signature comparison is claimed for the other 29. The eight semantic definition validations remain separate.

The [publication review](audit/point1_publication_review/current_20261104T031351/PUBLICATION_REVIEW.md) and [exact input catalog](audit/POINT1_PUBLISHED_LEAF_ELIGIBILITY.md) retain their original evidence-bound bytes. Their dated pending-acceptance labels are superseded by the final acceptance record.

## Proof work completed

- **Tensor and base-change arguments:** prove the actual external-section, diagonal, fiber, dual, Hom and total-space comparisons.
- **Determinants and first jets:** isolate the necessary alternating determinant input, prove its contact specialization, and check the first-jet translation.
- **Infinitesimal and nodal geometry:** prove square-zero arguments, chart identities, fundamental-class gluing, and the actual polarized smooth and nodal trait models.
- **Projective-line normalization:** check the explicit normalized source bivector, uniqueness and compatibility with the chosen projective-line geometry.
- **Affine projection:** prove OBL-069 from generic affine section representability and the actual universal construction.

## Remaining work

The full published-theorems-only milestone remains **open**. The current complete source graph includes a compiled **conditional** assembly: `LSMilestoneTarget.lean` still takes the explicit `PositiveQKSimpleConnectedness` bridge, which is absent from the frozen unconditional theorem. There remain **47 original obligations, eight definition validations and four final gates: 59 units**. Current conditional compilation does not discharge GATE-02 for the final unconditional theorem, and the 50-input Point 1 review is not the exhaustive final-theorem audit.

Continue with [TAKEOVER_PLAN.md](TAKEOVER_PLAN.md), [the fixed progress ledger](audit/MILESTONE_PROGRESS.md), and [the machine-readable status](TAKEOVER_STATUS.json).

## The new Fu proof

Baohua Fu's [*The classification of Fano contact manifolds revisited*, arXiv:2611.01423v1](https://arxiv.org/html/2611.01423v1) supplies a shorter geometric route. Its relative-conic treatment and direct use of the quadratic term are relevant to the remaining extension and homogeneity work. The completed tensor, infinitesimal, conic and projective-line foundations are retained. Compare the new route with the remaining 3k–3n dependencies before further branch-geometry implementation. The whole classification theorem has not been introduced as an admitted shortcut. Record any change in scope explicitly; the fixed denominator is unchanged.

## Reproduction and history

The checked sources are identified by `SOURCE.sha256`, the frozen specification by `target/MainStatement.lean`, and the runtime by `TOOLCHAIN.lock.json`. The native workflow and artifacts are linked in the acceptance record. Source-preserving recovery commit `d8749550ace47a9186fcc1d8c2a38fa81d8b3ba0` and the original 129-module checkpoint remain in repository history. Previous current documents are preserved under [audit/history/before_point1_acceptance_20261104T184658Z](audit/history/before_point1_acceptance_20261104T184658Z).
