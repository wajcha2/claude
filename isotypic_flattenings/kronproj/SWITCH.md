# Switching kronproj to the fast, low-memory combflat.py (2026-10-23)

Branch `claude/project-thread-ttahoa-kronproj` = `claude/zealous-mendel-i9qpdu` (at the commit it was branched from) + the
changes below. Nothing was pushed to `claude/zealous-mendel-i9qpdu`. Ranks, lattice dimensions, summary lines and hit
lines are the same as before; only time and memory change.

## What changed

| file | change |
|---|---|
| `combflat.py` | replaced by `combined/combflat.py` of `claude/project-thread-ttahoa`, byte for byte: filling pool scored by contraction cost + optimal DP paths (12-30x faster flattenings on large components), blocked `rref`, thin lattice storage (no `size x size` matrices per (member, level, rank)), memory-sized contraction blocks, `only_sources` option. Details: `combined/GUIDE.md`, `GUIDE_MEMORY.md`, `SWITCH.md` on that branch. |
| `kplib.py` | `empty_basis(fam)` / `basis_width(fam)`: the RREF bases from `fam.basis_rows()` now have `fam.ncols` columns (the first sum-of-member-dims + 8 generic coordinates), not `fam.size`. New class `KPLattice(LatticeFamily)`: same lattice, `dims()` compresses a stack of thin matrices that is much taller than wide (kpA: up to 137 members in F_p^N1, N1 = 14..400, e.g. 1950 x 58) by a fixed random (c+8) x rows matrix before the rank (20x faster on such stacks; same probabilistic argument, and the same compression, as the old `dims()` with `R[:c]`). |
| `kp_search.py` | exhaustive walk and greedy start from `empty_basis(fam)` (was `np.zeros((0, fam.size))`, which no longer has the right width); lattices are `KPLattice`. `FILLCHEAP` defaults to 1e9 (see below). The `size=` field of summary lines is still the nominal compressed size. |
| `kp_single.py` | no API change needed (`eval_F`, `EXTRA`, `ctx.basis` keep their meaning); `FILLCHEAP` defaults to 1e9. |
| `test_kp.py` | validates `KPLattice` (what kp_search uses), walk starts from `empty_basis`; `FILLCHEAP` 1e9. |

`FILLCHEAP`: the new `Context.basis` scores up to 1500 random fillings per component unless it finds one below
`FILLCHEAP` flops (default 1e8). kronproj touches hundreds of small components per job (kpA lattices have 39-137
members), and at 1e8 that scoring cost 1-4 s per component (kpA lam=33 at 4x5x5 d=6: 62 of 177 s, slower than the old
code). With 1e9 the scoring stops after 100 fillings whenever one evaluates in about a second; large components (d = 7, 8)
still get the full pool. Only the chosen basis of each Kronecker space changes, never a rank. The environment variable
still overrides it (`FILLCHEAP=1e8 python3 kp_search.py ...`).

## How to switch

```bash
git fetch origin claude/project-thread-ttahoa-kronproj
git checkout origin/claude/project-thread-ttahoa-kronproj -- isotypic_flattenings/kronproj/{combflat.py,kplib.py,kp_search.py,kp_single.py,test_kp.py,SWITCH.md}
cd isotypic_flattenings/kronproj
OPENBLAS_NUM_THREADS=1 python3 test_comb.py quick     # expect "0 failures" (~80 s)
OPENBLAS_NUM_THREADS=1 python3 test_kp.py quick       # expect "0 failures" (~15 min alone)
```

All five files go together (the old kp_search.py breaks on the new combflat.py: width mismatch in the exhaustive walk).
Then restart the runner as usual (`python3 kp_jobs.py jobs.txt 4`). Running workers keep the old modules in memory and
finish their job normally; the runner adopts them. Every new kp_search / kp_single process uses the new code. To move a
long job over now, kill its worker: the runner relaunches it with `--resume` and only the lattice in progress is redone.

## Cache, resume, job runner

* **Disk cache `live/cache/` stays valid.** The cache directory tag is unchanged. Files written by the old code hold the
  flattenings in the old choice of filling basis, new files in the new choice: the same functional spaces (full levels
  give the same subspaces), and partial levels are generic projections either way (generic Psi), so mixing old and new
  files gives the same dimensions (with the same p^-8-type failure probability as before). No need to clear it.
* **`--resume` and `kp_jobs.py` unchanged.** Summary and hit lines have the same format (identical text apart from
  timings). New stderr lines `#   basis ...: pool N, chosen cost ...` (one per component) start with `#` and are ignored
  by the resume parser.
* `jobs.txt` needs no change. Lattices deferred or skipped for memory (321|321 at 5x5x5 d=6, size 5713, "~8 GB";
  `--bmax 2500/3000` at d = 7) no longer need size^2 storage: memory is now about size x (sum of member dims) float32 per
  rank plus the exhaustive-walk bases (ncols wide). Not measured on those lattices; try one with `--only-mn` and watch
  RSS before raising `--bmax` across the board. Time still grows with the size.

## Safe parallelism (4 cores, ~13 GB shared)

`kp_jobs.py` already sets `OPENBLAS_NUM_THREADS=1`; keep one worker per core. Every job measured below stayed under
0.25 GB with the new code (old: 0.2-1.06 GB). The old runner's mem.log showed workers at 0.8-2.5 GB on the d = 7 kpB jobs;
those were dominated by the size x size lattice matrices that are gone now. 4 workers are safe for the d <= 7 jobs in
`jobs.txt`.

## Verification (2026-10-23, this container, OPENBLAS_NUM_THREADS=1, fresh caches, old and new run side by side)

* `test_comb.py quick`: old 0 failures, 94.8 s, 0.17 GB; new 0 failures, 78.6 s, 0.07 GB.
* `test_kp.py quick` (final code): 0 failures, 200 checks (H_s/V_s per level, mixed-level sums vs assembled block matrices,
  known C^3 values, grids/pencils, exhaustive walk vs dims), 750 s, 0.34 GB (the agent's earlier quick run needed
  over 50 min on a CPU shared with 4 workers).
* Old vs new on jobs from `jobs.txt` restricted to lattices of < 5 min: every summary / result line identical after
  removing timings (old vs new), and identical to the agent's own logs in `logs/jobs_snapshot/` for every lattice /
  component present there (80 lines).

| job (command line, all `--seed 5`) | lines | old wall / peak RSS | new wall / peak RSS |
|---|---|---|---|
| `kp_search.py 4,5,5 6 8,9 --dir 0 --fam B --only-mn "42\|2211;411\|3111;42\|42;411\|411;321\|222"` (exhaustive level vectors) | 5 lattices, identical | 265 s / 0.72 GB | 119 s / 0.15 GB |
| `kp_search.py 4,5,5 6 8,9 --dir 0 --fam A --only-lam "222;33"` (39 members each, sampled search + greedy) | identical | 69 s / 0.67 GB | 52 s / 0.15 GB |
| `kp_search.py 4,5,5 5 8,9 --dir 0 --fam A,B,G --gcount 300` (the whole k455_d5_dir0 job) | 56 lines, identical | 110 s / 0.19 GB | 94 s / 0.08 GB |
| `kp_search.py 4,5,5 6 8,9 --dir 0 --fam E` (13 components, rank-s grids) | identical | 103 s / 1.06 GB | 27 s / 0.16 GB |
| `kp_single.py 4,5,5 7 8,9 --dir 0 --mode HV --only "421\|421\|421;421\|3211\|3211;52\|3211\|3211;421\|4111\|421;2221\|3211\|3211"` | 5 components (g up to 9), identical | 257 s / 0.68 GB | 156 s / 0.19 GB |
| `kp_search.py 5 6 9,10 --fam B --only-mn "42\|2211;321\|21111"` | 2 lattices, identical | 619 s / 0.75 GB | 167 s / 0.22 GB |

Per lattice (old -> new): 455 d=6 kpB 411|411 120 -> 65 s, 42|42 60 -> 21 s, 321|222 33 -> 6 s; 555 d=6 kpB 42|2211
281 -> 56 s, 321|21111 338 -> 111 s; kpA lam=222 34 -> 17 s, lam=33 35 -> 35 s. Without the two kronproj adaptations
(plain `LatticeFamily.dims`, FILLCHEAP 1e8) the kpA run took 192 s and the d=5 job 256 s, i.e. slower than the old code:
both are needed for the many-member kpA lattices.

Caveats: kp_single gains less (its own H_s / V_s loops do not use combflat); the speed-up grows with component size
(d = 7, 8), where the old code spent most time in the contraction. The cache argument above is probabilistic in the same
way as every generic-rank computation here; a hit should still be re-checked with another seed / `PRIME=524269`.
