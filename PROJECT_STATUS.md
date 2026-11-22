# Project status: combined isotypic flattenings (455 / 555)

Last updated: 2026-10-22 20:20 UTC. This file is a read-only summary for other agents working on
the same problem. It is refreshed on request; the branches named below hold the actual code and logs.

Formats: "455" = C^4 ⊗ C^5 ⊗ C^5, testing border rank 8 vs 9. "555" = C^5 ⊗ C^5 ⊗ C^5, rank 9 vs 10.
Method: combined isotypic flattenings (several isotypic components at once), not projection to a single
isotypic factor. Subspaces (Kronecker-subspace projections) are not being tested.

Code used by all threads: branch `claude/tender-ride-7mz2gl`, directory `isotypic_flattenings/combined/`
(combflat.py, comb_search.py, comb_jobs.py). Known combined separators that guide source choice:
C^3 at d=4 and C^4 at d=6, both family B with sources (d-1,1), (d-2,2), (d-2,1,1).

## Degree 9, 455 and 555

- Families: B (sums over sources) and A (fixed source, sums of targets).
- Sources, first pass: λ1 ≥ 7, i.e. (8,1), (7,2), (7,1,1). For 455 both the C^4 factor and a C^5 factor
  as source; for 555 one direction. Every subset checked; Kronecker spaces on the source side or through
  a shared C^2.
- Next: family B with sources λ1 ≥ 6.
- Job file `combined/jobs_d9.txt`, job names `d9_*`, 4 cores.
- Results so far: runs started, no ranks reported yet.

## Degree 8, 455

- Prior coverage: single-component sweep (one isotypic factor at a time, incl. V-stacks) finished all
  1578 degree 8 components, no separation of rank 8 from 9 (branch `claude/wonderful-fermat-1v76ux`).
  The original combined-flattening agent had 455 d=8 queued but not started (still on d=7); it was asked
  to drop those two jobs.
- Running now (4 cores):
  - family B, sources with first row ≥ 5, source C^4 and source C^5
  - family E (reshaped single components), both directions
  - queued: family D (same targeted sums with a shared 2-dimensional target space Y = C^2)
- Results so far: first lattices show equal ranks (no separation yet).

## Degree 8, 555

- Prior coverage: 90 of 729 degree 8 components checked earlier, no separator.
- Plan: full degree 8 sweep (generic functional and full multiplicity stack, 3 directions), then a
  V-stack pass.
- Coordination: `pat_555_d8` is queued in `combined/jobs_455_555.txt` on `claude/tender-ride-7mz2gl` but
  not started; whether this thread takes it over is still open.
- Results so far: sanity checks in progress, no ranks yet.

## Degrees ≤ 7

Covered by the original combined-flattening agent (d=5..7 for 455 and 555), no separation found.
See `isotypic_flattenings/combined/README.md` on `claude/tender-ride-7mz2gl`.
