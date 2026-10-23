# Isotypic flattenings on C^4 ⊗ C^5 ⊗ C^5: rank 8 vs rank 9 — final report

Agent `d10`, 2026-10-23 07:30 UTC. Shared branch `claude/wonderful-fermat-1v76ux`, mirror `claude/tender-hopper-mcnmta`.

## Question and result

Is there an isotypic flattening of a component S_λ1(C^4) ⊗ S_λ2(C^5) ⊗ S_λ3(C^5) of S^d(C^4 ⊗ C^5 ⊗ C^5) whose rank on a
generic tensor of rank 8 is smaller than on a generic tensor of rank 9 (i.e. a degree-d equation separating σ_8 from σ_9)?

**No separator was found in any checked component.** Every flattening tested has the same rank on the rank-8 and the
rank-9 tensor. No `*** SEPARATES` line occurs in any log, so there are no hits to verify.

## Method

* `sweep_fast.py 4,5,5 d 8,9 5 …`: random rank-8 and rank-9 tensors (seed 5), exact arithmetic mod p = 524287.
* For every isotypic component λ = (λ1, λ2, λ3) of multiplicity g and every direction N (source S^{λN}(C^{nN})^*):
  * **gN**: flattening of a generic element of the multiplicity space (g independent fillings, random combination);
  * **HN** (g ≥ 2): the stack of all g flattenings (full multiplicity space), compressed by a random matrix;
  * **VN** (g ≥ 2, V-stack passes only): the vertical stack U ⊗ S^{λN}V^* → S^{λi}V ⊗ S^{λj}V.
* Evaluation at random points with ROWCAP (samples capped by the rank bounds); `span` = number of independent fillings found.
* Workers claim components cheapest first; logs `hwv455_d<d>[_<job>]_w<k>.log` (gN/HN, "noV") and `hwv455V_d<d>*.log` (VN).

## Coverage per degree

| d | components | gN, HN checked | VN checked | core-h (gN/HN) | core-h (VN) |
|---|---|---|---|---|---|
| 2 | 3 | 3 | 3 | 0.0 | 0.0 |
| 3 | 8 | 8 | 8 | 0.0 | 0.0 |
| 4 | 28 | 28 | 28 | 0.0 | 0.0 |
| 5 | 82 | 82 | 82 | 0.0 | 0.0 |
| 6 | 250 | 250 | 250 | 0.2 | 0.3 |
| 7 | 639 | 639 | 639 | 2.5 | 5.8 |
| 8 | 1578 | 1578 | 1578 | 36.3 | 186.7 |
| 9 | 3339 | 3339 | — (skipped, user decision) | 565.9 | — |
| 10 | 7244 | 3082 | — (not planned) | 280.8 | — |

Total compute over finished components: about 883 core-h for gN/HN and 193 core-h for VN, roughly 1076 core-h. Not
counted: work lost to container restarts (at most one direction per in-flight component before 2026-10-22, at most one
contraction after the in-direction checkpoints) and aborted runs.

### Degree 10 in detail

| job | selection | components | core-h |
|---|---|---|---|
| d10_max3000_adj | adjoint-type C^5 factor (3,2,2,2,1), all factor dims ≤ 3000 | 406 | 63.1 |
| d10_max400 | all factor dims ≤ 400 | 666 | 19.6 |
| d10_max1000 | all factor dims ≤ 1000 | 782 | 64.7 |
| d10_adj | remaining adjoint-type components (dims up to 4725) | 68 | 48.0 |
| d10_c1e7 | ROWCAP cost ≤ 1e7 among the rest | 1160 | 85.4 |
| **total** | | **3082 of 7244** | **280.8** |

So at d = 10, gN and HN are checked for every component with all factor dimensions ≤ 1000, every adjoint-type
component, and every component with ROWCAP cost proxy g·Σ_N (min(nN, g·n_other)+8)(min(nN, n_other)+8) ≤ 1e7.

### Not checked

* **d = 10, gN/HN: 4162 components.** None is adjoint-type. All have a factor of dimension 1024–4725 and ROWCAP cost
  above 1e7. Estimated cost from a fit on the 400 most expensive finished d = 10 components (secs ≈ 1.5e-6 · cost^1.22):

  | ROWCAP cost | components | est. core-h | largest single |
  |---|---|---|---|
  | (1e7, 3e7] | 1614 | ~490 | 0.5 h |
  | (3e7, 1.25e8] | 1833 | ~2440 | 3 h |
  | (1.25e8, 3e8] | 534 | ~2670 | 9 h |
  | (3e8, 1e9] | 180 | ~2720 | 37 h |
  | > 1e9 | 1 | ~50 | 51 h |

* **VN at d = 9 and d = 10** (VN is checked through d = 8).
* **Degrees ≥ 11.**

## Remarks

* **span < g** (fewer independent fillings than the multiplicity) occurred in 3 components, all at d = 10:
  ((6,4),(6,1,1,1,1),(6,1,1,1,1)), ((7,3),(7,1,1,1),(7,1,1,1)) and ((6,3,1),(7,1,1,1),(6,1,1,1,1)), each with g = 2.
  All three are harmless. In every direction with span < g, gN already has rank equal to the source dimension on both
  tensors, so the full stack has that rank as well (checked automatically by `t455_spancheck.py`).
* **Hardest component:** ((5,3,2),(6,3,1),(3,2,2,2,1)), g = 7, dims (300, 4725, 24). It took 10 h on one core
  (14 contractions of ~2·10^12 flops in direction 2). All ranks are full: H2 = g2 = 4725/4725.

## Method changes made during this sweep (`[method]` commits, results unchanged)

| change | effect | verification |
|---|---|---|
| per-direction checkpoints (`#partial` lines) | a restart resumes at the next direction | identical results resuming after either direction |
| VONLY / VLOCK_GB | V-stack memory ~4S → ~2S; large V ranks serialised | d = 4, 5 V reruns identical |
| noV streaming of the g flattenings | peak memory ~2g·N1·K → ~7·N1·K doubles | d = 5 (82 comps) and d = 7, 8 (24 comps, g = 3..10) identical |
| optional in-direction checkpoints (CKPT_SECS) | a restart loses at most one contraction | 76 runs killed at random, all lines identical |
| adopted c9c1f7d: `minors_of_points` on C(n, l) row subsets only | ~14% faster on components with 5-row C^5 factors | bit-identical output; two components rerun identical |

## Reproduction

Logs: `hwv455_d*.log` (gN/HN) and `hwv455V_d*.log` (VN). Job queue: `t455_jobs.txt`. ONLY lists: `only455_adj.txt`,
`only455_c1e7.txt`. Status and per-component tables: `agents/d10.md` (regenerated by `t455_report.py`). Restart
instructions are in the "Restart" section of `agents/d10.md`.
