# Switching the combined-flattening runs to the fast, low-memory combflat.py (2026-10-23)

This branch (`claude/project-thread-ttahoa`) = `claude/tender-ride-7mz2gl` at 7dc9bc2 + one new file,
`isotypic_flattenings/combined/combflat.py`, which contains three changes made in other threads of the project:

1. filling pool scored by path cost + optimal DP contraction paths (details: `GUIDE.md`), 12-30x faster flattenings;
2. blocked Gauss-Jordan `rref` (panels of 64 columns, BLAS trailing update), 10-20x faster `--exhaust` enumeration;
3. low-memory lattices and memory-sized contraction blocks with reuse (details and tables: `GUIDE_MEMORY.md`).

comb_search.py, comb_jobs.py, test_comb.py, job files and logs are unchanged. Requirements unchanged (`pip install sympy opt_einsum`).

## How to switch (one file)

```bash
git fetch origin claude/project-thread-ttahoa
git checkout origin/claude/project-thread-ttahoa -- isotypic_flattenings/combined/combflat.py
cd isotypic_flattenings/combined && OPENBLAS_NUM_THREADS=1 python3 test_comb.py quick   # expect "0 failures"
```

Then restart the runner as usual (`setsid nohup python3 -u comb_jobs.py jobs_455_555.txt 4 ...`). Running workers keep
the old module until they finish their job; every new comb_search process loads the new file. To be sure all jobs use
it, stop the runner and its workers and start it again: `--resume` skips every lattice already in the logs.

## Cache and --resume

* The disk cache (`live/cache`) stays valid: fillings, Psi, sample points and tensors are unchanged and the flattening
  matrices are bit-identical (md5 checked). Do not change `MEMCAP` (it steers the filling choice; changing it only
  invalidates cache reuse, not the ranks).
* `--resume` and comb_jobs.py's log parts stay valid: the log format is unchanged.

## Peak memory and safe parallelism (13-15 GB container, 4 cores)

Measured old -> new, one BLAS thread, rank lines identical:

| job | old | new |
|---|---|---|
| 455 d=8 dir 0, sources 71;62;611, (3221,2222) | 41.6 s, 0.64 GB | 28.6 s, 0.14 GB |
| 555 d=8 pattern:3, 3 targets | 175 s, 0.85 GB | 129 s, 0.14 GB |
| 455 d=9 dir 0, sources 711;6111 | 26 s, 0.21 GB | 23.5 s, 0.13 GB |
| 455 d=6 dir 1 aux 2 exhaustive (1500 s) | 53 lattices, 1.34 GB | 59 lattices, 0.25 GB |
| 555 d=10 (91,82,811 \| 61111,61111), size 12658 | 2677 s, 10.07 GB | 1034 s, 0.76 GB |

Recommended:

| format, degree | workers on 4 cores | notes |
|---|---|---|
| 455 and 555, d <= 8 (incl. pat_455_d7, pat_555_d7, pat_555_d8) | 4 (one per core) | each job < 0.5 GB |
| 455 and 555, d = 9 | 4 | measured 0.13 GB (455 d=9 aux 1) |
| 555 d = 10, 455 d = 10 | 2-4 | measured only on 555 (size 12658): 0.76 GB; start with 2 workers and watch RSS before going to 4; `--bmax 16000` worked |

* Always `OPENBLAS_NUM_THREADS=1` per job (comb_jobs.py already sets it). The work is mostly single-threaded numpy;
  4 BLAS threads per job oversubscribe the cores and do not make a single job much faster.
* `--bmax` values chosen earlier to avoid OOM (4000-5000 at d = 7, 8) can be raised: the lattice no longer stores
  size x size matrices, so memory grows roughly with size x (sum of member dims), not size^2. Time still grows with size.
* Tunable `EVALMEM` (float64 elements per flattening evaluation, default 2^23 = 64 MB); leave it unless a job still
  runs out of memory (lower it) or you have memory to spare (2^25 gives the same speed).

## Checks done for this branch (2026-10-23, in this container)

* `test_comb.py quick`: 0 failures (78 s).
* C^4 d=6 separators, `comb_search.py 4 6 5,6,7 --fam B --aux 1 --exhaust 3 --sources "51;42;411" --only-mn "321|222;411|321"`:
  `196/316/320` and `392/512/516` as before.
* Your own queues, old (tender-ride 7dc9bc2) vs new, same command lines as jobs_455_555.txt with `--only-mn`:
  pat_555_d7 targets 22111|22111, 31111|22111 and pat_455_d7_dir1 targets 2221|22111, 2221|31111: summary lines identical
  (555: 24.2 s + 24.9 s -> 10.8 s + 21.8 s). Note: the snapshot logs in logs/jobs_snapshot for these lattices were written
  before `--allsub 6` (949a043), so their `tested=` and `named:` fields differ from any current run, old code or new;
  the singles are the same.
* The memory thread's checks are in GUIDE_MEMORY.md (all rank lines identical, md5-identical flattenings).
