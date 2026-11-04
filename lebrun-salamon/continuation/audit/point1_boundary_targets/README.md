# Prepared Point1 proof-boundary audit

This directory contains the Lean evidence programs. Complete43+1 coverage has now passed using the two disjoint29 and14+1 tranches, followed by independent publication review. The aggregate and substep programs remain unexecuted alternatives. Acceptance is still pending the required current downstream reverse-cone gate; this record adds no milestone units. `TARGETS.json` records the source snapshot, exact original declarations, containing modules and a static comparison with the validated CI 41757281666 source ancestry.

The Point1 denominator remains **43 original obligations**: Step 3c has 6, Step 3d has 11, Step 3e has 7, Step 3f has 11, and Step 3g has 8. **OBL-069 is a separate 44th audit root**, because proving the inherited total-line affine projection was necessary to close the normal-form dependency boundary. It remains a Step 3k obligation.

`LSPoint1BoundaryAudit.lean` covers all 44 roots. The five `LSPoint1Boundary3*.lean` files partition the original 43 roots, and `LSInheritedAffineBoundaryAudit.lean` handles only OBL-069. An execution may use the aggregate program or all six disjoint programs. Do not count the aggregate and partitioned executions as separate progress units.

Each program reuses the exhaustive, already checked constant-closure walker. It traverses constant types, available opaque values and inductive constructors, including nonproject dependencies. For each root it logs every direct `sorryAx` dependency, its owning module, its fully qualified printed Lean type and a shortest dependency path, together with missing constants and custom project axioms. The root ID and scope are logged independently. The final `#print axioms` is supplementary; it does not identify which theorem introduced `sorryAx` by itself.

## Execution boundary

Keep these evidence programs outside the canonical `source/` graph. Copy the selected program into an isolated source snapshot and run the dependency-aware replay driver with the matching source, toolchain lock and ancestry-stamped V2 seed receipts. In particular, the new Geometry proof invalidates old descendants even when their own source bytes are unchanged. A static source-hash comparison is not an artifact-validation receipt.

After successful execution, preserve the exact audit source, imports, full source ancestry, native receipt, stdout/stderr and parsed per-root inventory. Reconcile every remaining admitted leaf with the independent publication-eligibility ledger; any missing constant, original composite admission or unaudited custom project axiom prevents acceptance. These programs do not decide whether an English source proves a Lean statement.

At preparation, all 44 exact original declarations were found once and had no direct lexical `sorry`/`admit` in their own declaration span. Of the original 43 roots, 29 still had unchanged source ancestors compared with CI 41757281666; 14 were affected by the newly installed Geometry/formal-trait proof chain. Those numbers describe the prepared snapshot, not proof completion or future replay results.

## Optional early/current-change partition

`LSPoint1UnchangedBoundaryAudit.lean` covers the 29 original roots whose source ancestry still matched the validated246-module CI at preparation. `LSPoint1ChangedBoundaryAudit.lean` covers the other14 Point1 roots plus the separately labeled OBL-069. These two tranches provide another exact partition of the same44 roots, allowing the unchanged cones to be checked before fresh Geometry descendants arrive. The filenames describe the prepared snapshot; the replay driver must still validate every source and artifact before reuse. They add no new progress units.

## Hidden-axiom check

The final aggregate and future partition walkers also inspect every axiom reached, irrespective of its module name. `NONSTANDARD_AXIOM` and the `nonstandard_axiom_count` summary field flag anything outside exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. Each root’s `#print axioms` output must independently contain only that allowlist. The already-running29-root snapshot is deliberately preserved; its all-module axiom check is performed from those per-root printed sets, not retroactively attributed to a changed walker.

## First native tranche — 2026-11-04 02:50 UTC

The exact unchanged29-root program passed in82.105seconds after strict reuse of all41 project ancestors; final validation accepted42 selected modules with no invalidation or runtime change. The [preserved evidence](../point1_boundary_current_20261104T025016/NATIVE_BOUNDARY.json) contains25 distinct admitted leaves, zero original composite admissions, zero missing constants and valid four-name axiom allowlists for all29 roots. The independent source reviewer has now recorded both inherited exterior-power primitives that were absent from the catalog at that moment; all25 actual leaves pass that separate review. The14+1 tranche and final snapshot/ancestry reconciliation remain pending.

## Complete native/publication boundary — 2026-11-04 03:13 UTC

The changed14 Point1 roots plus OBL-069 passed in73.477seconds on188 validated current ancestors. All41 source/output/ancestry stamps from the earlier29-root audit were revalidated against the same190-module Point1 snapshot, so no sufficient proof was rerun. Across43+1 roots the actual boundary has50 eligible generic admitted inputs, no original composite admission, no missing constant, and no unexpected axiom. The [combined43-row record plus separateOBL-069](../point1_acceptance_current_20261104T031351/POINT1_ACCEPTANCE.json) records exact current module hashes and evidence. The current downstream compatibility/reverse-cone check remains the named blocking acceptance gate.
