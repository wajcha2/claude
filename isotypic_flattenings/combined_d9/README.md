# Combined isotypic flattenings at degree 9 (4x5x5 rank 8 vs 9, 5x5x5 rank 9 vs 10)

Session https://claude.ai/code/session_019u9z1y8ZKPYSUqwLbW8dbV, branch `claude/charming-heisenberg-f66sy8`, started 2026-10-22.
This continues the combined-flattening search of the 455/555 agent (branch `claude/tender-ride-7mz2gl`, `combined/`, degrees
5..7, no separation) one degree beyond the degree-8 runs of the project thread (branch `claude/project-thread-uj02nh`).
Kronecker-subspace projections (branch `claude/zealous-mendel-i9qpdu`, `kronproj/`) are not repeated here.

Code: `../combined/` copied unchanged from `claude/tender-ride-7mz2gl` at 4c2baa0 (combflat.py, comb_search.py, comb_jobs.py,
test_comb.py, brute.py; see `../combined/README.md` for the construction and its validation).  Additions to
`comb_search.py`: `--allsub M` (below), transposed pairs {(μ,ν), (ν,μ)} as named groups of family A, and members whose
level-1 subspace alone already has the lattice's maximal dimension on the lowest rank are dropped from the subsets (every sum
containing one is saturated on every rank; at d=9 every target of the source (7,1,1) has rank n1 = 280 on rank 8).  Check:
C^5 d=5 family A, source (3,2): 25 of 27 members dropped, the known hit [1^5,221 + 221,1^5] 105/150 still found (19 s).  `combflat.LatticeFamily.dims`: once a
sum is saturated (rankcap) on a lower rank, the higher ranks are not computed (dims are nondecreasing in r and <= rankcap);
`test_comb.py quick` 0 failures (`logs/test_quick_dims_earlyexit.log`).  Here: `d9_jobs.py` (the same
resumable runner, logs in `logs/jobs/`, cache in `live/cache/`), `jobs_d9.txt` (job list), `memlog.sh` (memory log).

## Changes to the shared library

`isoflat.MODRANK_BLOCK` = 32 instead of 256 (2026-10-23, suggested by the user): same ranks (200 small / degenerate matrices
against `modrank_ref`, block 32 = block 256 on full and rank-deficient matrices of size 576..3000), 4x faster at n = 576..1100
(the family-A lattices), 2x at n = 2500..3000; `test_comb.py quick` 0 failures (`logs/test_quick_modrank32.log`).  Family-B
workers restarted at 16:15 UTC; the family-A worker after its (8,1) aux-2 lattice.

### `hwv_fast.minors_of_points`

At degree 9 the targets need up to K = 4716 sample points, and computing the minors of the sample points took 2 minutes per
target (`hwv.col_dets` builds all n^l ordered row tuples over all l! permutations; profiled on ((7,1,1),(4,3,1,1),(4,3,1,1))).
For the 304 targets of 4x5x5 dir 0 that was about as much as the flattening evaluations themselves.  `minors_of_points` now
evaluates only the C(n, l) row subsets (Leibniz expansion, int64 exact); the old function is kept as `minors_of_points_ref`.
Output identical on n = 2..5, all l, random and degenerate points (`np.array_equal`), 0.04 s instead of 61 s for 4716 points
of 5x5.  `combined/test_comb.py quick` rerun with it: `logs/test_quick_fastminors.log`.

## Plan and flattenings tested

Directions: 4x5x5 dir 0 = the C^4 factor as source (targets in C^5 (x) C^5), dir 1 = a C^5 factor as source (targets in
C^4 (x) C^5; dir 2 is dir 1 with the two C^5 factors swapped); 5x5x5 one direction (symmetric).

First pass: sources λ with λ1 >= 7, i.e. (8,1), (7,2), (7,1,1) (`--sources pattern:2`).  This is the source pattern of both
known combined separators (C^3 d=4: {31, 22}; C^4 d=6: {51, 42, 411}).  Every subset of every lattice (at most 3 members),
Kronecker spaces whole (level g) and one generic functional (level 1).

| job | flattening family | notes |
|---|---|---|
| d9_455_dir0_B | B: fixed target, sum over sources; Kronecker spaces on the source side (aux 1) or through a shared Y = C^2 on the target side (aux 2, "family D") | 304 targets, compressed size <= 4708 |
| d9_455_dir1_B | B, aux 1 | 164 of 242 targets (compressed size <= 6000) |
| d9_555_B | B, aux 1 | 198 of 304 targets (compressed size <= 6000) |
| d9_455_dir0_AE | A: fixed source, sums over targets (aux 1: Kronecker spaces on the target side; aux 2: shared X = C^2 on the source side, "family C"); E: reshaped single components (Ψ generic in M^*⊗X^*⊗Y, k, l >= 2) | shares the flattening cache with d9_455_dir0_B; every transposed pair {(μ,ν), (ν,μ)} at both levels (the C^5 d=5 family-A hit for 7 vs 8 was such a pair); 4000 random pairs and one greedy run ((7,1,1) aux 1: all pairs; all 14000 pairs of (7,1,1) aux 2 took > 4.5 h, so the job was restarted with these settings) |

Estimated evaluation cost (from the timing of ((8,1),(5,3,1),(5,3,1)): 24.5 s per functional for 448 x 4708 samples): dir 0
about 6 core-hours, dir 1 and 555 with size <= 6000 about 15 and 18 core-hours; all targets of dir 1 / 555 would be
about 90 / 120 core-hours.  Sources with λ1 >= 6 (`pattern:3`): dir 0 about 18 core-hours at size <= 6000.

## Results

See `STATUS.md`.
