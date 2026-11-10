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

**Fast low-memory `combflat.py`** (2026-10-23 18:00 UTC, from branch `claude/project-thread-ttahoa`, commit e3b58d6: filling
pool + DP contraction paths, blocked rref, thin lattices with reused contraction blocks; see `../combined/SWITCH.md`,
`GUIDE.md`, `GUIDE_MEMORY.md`), with this thread's two edits ported onto it (`dims` early exit at `rankcap`,
`enumerate(members=)`).  The disk cache stays valid (bit-identical flattenings).  Checks: `test_comb.py quick` 0 failures
(`logs/test_quick_fastcombflat.log`); C^5 d=5 family A 105/150; C^4 d=6 family B 196/316/320 and 392/512/516; d=9
lattices re-run with the job arguments and compared with the logs: 455 dir 0 54|54 (aux 1, 2), 455 dir 1 3321|33111
(3 members, 17 subsets), 5x5x5 42111|22221: summary lines identical; peak memory 125-160 MB per process (old workers
1-5 GB).  Family-B workers restarted at 18:03 UTC; the family-A worker after its (7,2) lattice.

`isoflat.MODRANK_BLOCK` = 32 instead of 256 (2026-10-23, suggested by the user): same ranks (200 small / degenerate matrices
against `modrank_ref`, block 32 = block 256 on full and rank-deficient matrices of size 576..3000), 4x faster at n = 576..1100
(the family-A lattices), 2x at n = 2500..3000; `test_comb.py quick` 0 failures (`logs/test_quick_modrank32.log`).  Family-B
workers restarted at 16:15 UTC; the family-A worker after its (8,1) aux-2 lattice.

Memory (2026-10-23): family A kept the flattenings of all targets of a source in memory during the whole search (3.9 GB for
(7,2)) besides the compressed matrices (~5 GB at aux 2); `comb_search.py` now frees the flattenings once a lattice is built
(the next lattice reloads them from the disk cache) and the matrices of dropped saturated members.  Fixed with it: the
`--exhaust` walk (`LatticeFamily.enumerate(members=...)`) now runs over the kept members only (before, a lattice that the
saturation drop brought below the --exhaust limit raised ValueError).  Checks: `test_comb.py quick` 0 failures
(`logs/test_quick_memfix.log`); C^5 d=5 family A source 32 with --exhaust 3 finds 105/150 (25 of 27 dropped); C^4 d=6
family B target (321, 222) with --exhaust 14 finds [411 + 42 + 51] 316/320.

### `hwv_fast.minors_of_points`

At degree 9 the targets need up to K = 4716 sample points, and computing the minors of the sample points took 2 minutes per
target (`hwv.col_dets` builds all n^l ordered row tuples over all l! permutations; profiled on ((7,1,1),(4,3,1,1),(4,3,1,1))).
For the 304 targets of 4x5x5 dir 0 that was about as much as the flattening evaluations themselves.  `minors_of_points` now
evaluates only the C(n, l) row subsets (Leibniz expansion, int64 exact); the old function is kept as `minors_of_points_ref`.
Output identical on n = 2..5, all l, random and degenerate points (`np.array_equal`), 0.04 s instead of 61 s for 4716 points
of 5x5.  `combined/test_comb.py quick` rerun with it: `logs/test_quick_fastminors.log`.

**Memory budget in the runner** (2026-11-02 22:28 UTC).  The container's memory cgroup limit is 14.3 GB.  The 74th lattice
of d9_455_dir1_B_big (target ((6,2,1),(6,2,1)) of C^4 (x) C^5, compressed size 19588) needs more than 6.3 GB for its
thin lattice matrices; next to the three other workers (about 8-9 GB) it was OOM-killed five times between 20:54 and
22:23 (parts 8-12), and one of those OOM events killed the 5x5x5 worker (d9_555_B_big) in the middle of a lattice.  `d9_jobs.py` now takes
memory hints (`name @GB | args`, expected peak) and launches a job only when the sum over running jobs of max(hint,
current RSS) plus its hint fits in 13.5 GB (a blocked job lets only jobs with hint <= 2 GB pass it; a job of the runner
killed by SIGKILL gets its hint raised to 1.25 x its peak RSS, `logs/jobs/memhints.json`).  d9_455_dir1_B_big (@8, 5 of
78 lattices left) waits until the other large jobs leave room; nothing of it is lost (flattenings cached, `--resume`).
After the container restart of 2026-11-03 00:40 the queue order is: d9_455_dir1_B_big next to the small λ1 >= 5 jobs and
d9_455_dir1_B_p3 (4 workers, 12.5 of 13.5 GB reserved); d9_555_B_big and d9_455_dir0_B_p3_big after them.
At 02:38 UTC d9_455_dir1_B_p3 (hint 1.5 GB) had grown to 4 GB next to d9_455_dir1_B_big (7.6 GB): 13.4 GB used of 14.3,
and the OOM killer would have chosen the largest process, i.e. the 8 GB job in the middle of its lattice.  The runner now
raises each job's `oom_score_adj` to (largest hint - its hint) / 14.34 GB x 1000 (it cannot be lowered in this container),
so an OOM kill hits the job furthest above its own hint (here d9_455_dir1_B_p3: oom_score 1124 against 979).
It did at 05:52 UTC: d9_455_dir1_B_p3 (3.5 GB, hint 1.5) was killed, d9_455_dir1_B_big (8.6 GB) kept its lattice.  Its hint is
now 4.5 GB, so it waits until the large job is done (lattice 129 is redone from the cached flattenings).
The container stopped at about 08:00 UTC on 2026-11-03 and was started again on 2026-11-08 13:50 (no work in between); the
runner was restarted with d9_455_dir1_B_p3 after the small jobs (4 workers: the 8 GB job and three small ones).
2026-11-08 18:28 UTC: d9_455_dir1_B_big was OOM-killed at 9.9 GB on its lattice 76 (hint 8; the job furthest above its hint);
the runner raised its hint to 12.1 GB (`logs/jobs/memhints.json`), and the job (3 lattices left) now runs last, alone.
2026-11-09 14:53 UTC: d9_555_B_big (hint 5) was OOM-killed at 6.3 GB on its lattice 94 (the job furthest above its hint);
learned hint 7.64 GB, it waits for memory (13 lattices left); d9_555_B_p5_mid fills the core.
2026-11-09 19:36 UTC: d9_455_dir1_A1 finished (family A of the C^5 source, (7,1,1), (8,1), (7,2): no separation, peak about
3 GB).  d9_555_B_big's learned hint set to 7.4 GB (killed at 6.3 GB) so that it fits next to the three small jobs.
2026-11-10 01:22 UTC: container restart (up 1 day 11 h); runner and memlog restarted at 01:24, the same four jobs resumed from
their logs (13.4 of 13.5 GB reserved).

**Family A of a C^5 source** (2026-11-03; for 5x5x5 and 4x5x5 dir 1, which so far had family B only).  A family-A lattice
of a source λ lives in S_λ C^5 (n1 = 1760, 2475, 1540 for (8,1), (7,2), (7,1,1)) and has one member per target (106, 233,
242).  The two-pass build needs the flattenings of all targets of λ on disk (~100 GB) or in memory, and the thin matrices of
all members (~30 GB).  Changes to `../combined/` (all opt-in in the library, `comb_search.py` options):
* `LatticeFamily.skip_saturated` (default in comb_search, `--keepsat` = old): no thin matrices for members saturated at
  level 1 on the lowest rank (search() drops them anyway).
* `--single-pass` (`LatticeFamily._build_single`): one pass over the members, ncols = size, each member's flattenings freed
  after its sketches and thin matrices (same per-member random draws); `--no-cache-write`: nothing written to the cache.
* `--a-exclude FILE.json | GLOB;GLOB`: family-A members (aux 1) whose level-1 rank on the lowest rank is n1 in family-B
  summary lines of the same tensors are left out (their flattenings are never computed; rank does not depend on the side
  the lattice lives on).  From the 5x5x5 B logs (277 of 304 targets): (8,1) 67 of 106, (7,2) 150 of 233, (7,1,1) 186 of 242
  saturated.  `a_exclude.py` writes the JSON.
* `dims()`: a sum with a summand of dimension rankcap is rankcap (exact, no rank); stacks of more than 2^27 elements
  (`TALLRANK`) are ranked as G @ stack with G random (c + 8) x rows, accumulated block by block (`_tall_rank`, exact
  except with probability < p^-8).
Validation (every comparison: all summary lines identical, timings aside): C^5 d=5 family A source (3,2) (the hit
[1^5,221 + 221,1^5] 105/150), 4x5x5 d=9 dir 0 family A (7,1,1) (262 of 269 saturated) and family B (22221|22221,
32211|22221) against `--keepsat` / the two-pass build; single pass with and without the cache; the (7,1,1) run with
`--a-exclude` (JSON and logs) tests the same sums (the left-out members' singles aside); `TALLRANK=1` (every stack ranked
by random combinations) on both family-A cases; `_tall_rank` = `modrank` on 12 random low-rank stacks; `test_comb.py
quick` 0 failures with the defaults and with `TALLRANK=1` (`logs/test_quick_singlepass_tall.log`,
`logs/test_quick_tallrank1.log`).  Peak memory of the (7,1,1) lattice: 92 MB instead of 328 MB.
Queued: d9_555_A1 and d9_455_dir1_A1 (sources (8,1), (7,2), (7,1,1); all named groups, 4000 pairs, 1000 triples, 100
random subsets; no greedy run: its RREF bases would double the memory), after d9_555_B_big (whose logs complete the
exclusion list).
d9_455_dir1_A1 moved first (2026-11-09 02:33): its exclusion list is complete up to 3 targets (dir-1 B logs: 239 targets; kept
(8,1) 43, (7,2) 45, (7,1,1) 52 members), estimated thin matrices <= 2.6 GB plus one member's flattenings <= 0.75 GB, hint 3.8 GB.

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
| d9_455_dir1_B_big, d9_555_B_big | B, aux 1, the targets skipped above (compressed size 6000 < size <= 25000, `--bmin`) | queued 2026-10-23 after the switch to the fast low-memory combflat.py |
| d9_455_dir0_B_p3 | B, aux 1, sources λ1 >= 6 ((8,1), (7,2), (7,1,1), (6,3), (6,2,1), (6,1,1,1)), every subset at levels 1 and g (`--exhaust 14`) | 382 of 426 targets (size <= 8000); queued 2026-10-23 22:50 |
| d9_555_B_p3 | 5x5x5, B, aux 1, sources λ1 >= 6, every subset at levels 1 and g (`--exhaust 14`) | 159 of 426 targets (size <= 8000); queued 2026-10-25 23:50 |
| d9_455_dir1_B_p3 | 4x5x5 source a C^5 factor, B, aux 1, sources λ1 >= 6, every subset at levels 1 and g (`--exhaust 14`) | 142 of 335 targets (size <= 8000); queued 2026-11-02 11:40 |
| d9_455_dir0_B_p3_big | the 44 dir-0 targets above size 8000 of the λ1 >= 6 pass (`--bmin 8000 --bmax 15000`) | queued 2026-11-02 13:10 |
| d9_455_dir0_B_p4 | 4x5x5 dir 0, B, aux 1, sources λ1 >= 5 (adds (5,4), (5,3,1), (5,2,2), (5,2,1,1)), every subset of at most 3 members at levels 1 and g (`--exhaust 14 --maxsub 3`) | targets of size <= 3000; queued 2026-11-02 22:28 (low memory, fills the core left free by the memory budget) |
| d9_555_B_p4, d9_455_dir1_B_p4 | the same λ1 >= 5 pass for 5x5x5 and 4x5x5 dir 1 (11 sources: also (5,1,1,1,1)), targets of size <= 3000 | queued 2026-11-03 00:45 |
| d9_455_dir0_B_p5 | 4x5x5 dir 0, B, aux 1, sources λ1 >= 4 (14 sources: also (4,4,1), (4,3,2), (4,3,1,1), (4,2,2,1)), subsets of at most 3 members at levels 1 and g | targets of size <= 2000; queued 2026-11-03 05:54 (fills the core while d9_455_dir1_B_p3 waits for memory) |
| d9_555_B_p5 | 5x5x5, B, aux 1, sources λ1 >= 4 (16 sources), subsets of at most 3 members at levels 1 and g | targets of size <= 2000; queued 2026-11-08 13:50 |
| d9_455_dir1_B_p5 | 4x5x5 dir 1, B, aux 1, sources λ1 >= 4 (16 sources), subsets of at most 3 members at levels 1 and g | targets of size <= 2000; queued 2026-11-08 14:35 |
| d9_555_B_p4_mid | 5x5x5, B, aux 1, sources λ1 >= 5 (11), subsets of at most 3 members, targets of size 3000..4500 | queued 2026-11-08 17:00 |
| d9_455_dir1_B_p4_mid | 4x5x5 dir 1, B, aux 1, sources λ1 >= 5 (11), subsets of at most 3 members, targets of size 3000..4500 | queued 2026-11-08 22:02 |
| d9_455_dir0_B_p5_mid | 4x5x5 dir 0, B, aux 1, sources λ1 >= 4 (14), subsets of at most 3 members, targets of size 2000..3000 | queued 2026-11-09 06:05 |
| d9_455_dir1_B_p5_mid | 4x5x5 dir 1, B, aux 1, sources λ1 >= 4 (16), subsets of at most 3 members, targets of size 2000..3000 | queued 2026-11-09 11:00 |
| d9_555_B_p5_mid | 5x5x5, B, aux 1, sources λ1 >= 4 (16), subsets of at most 3 members, targets of size 2000..3000 | queued 2026-11-09 14:55 |
| d9_455_dir1_B_p5_mid2 | 4x5x5 dir 1, B, aux 1, sources λ1 >= 4 (16), subsets of at most 3 members, targets of size 3000..4000 | queued 2026-11-09 18:45 |
| d9_455_dir0_AE | A: fixed source, sums over targets (aux 1: Kronecker spaces on the target side; aux 2: shared X = C^2 on the source side, "family C"); E: reshaped single components (Ψ generic in M^*⊗X^*⊗Y, k, l >= 2) | shares the flattening cache with d9_455_dir0_B; every transposed pair {(μ,ν), (ν,μ)} at both levels (the C^5 d=5 family-A hit for 7 vs 8 was such a pair); 4000 random pairs, one greedy run and (from 2026-10-25, after three container restarts lost the (7,2) aux-2 lattice) 100 random subsets ((7,1,1) aux 1: all pairs; all 14000 pairs of (7,1,1) aux 2 took > 4.5 h, so the job was restarted with these settings) |

Estimated evaluation cost (from the timing of ((8,1),(5,3,1),(5,3,1)): 24.5 s per functional for 448 x 4708 samples): dir 0
about 6 core-hours, dir 1 and 555 with size <= 6000 about 15 and 18 core-hours; all targets of dir 1 / 555 would be
about 90 / 120 core-hours.  Sources with λ1 >= 6 (`pattern:3`): dir 0 about 18 core-hours at size <= 6000.

## Results

See `STATUS.md`.
