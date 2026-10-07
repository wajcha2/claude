# Isotypic-flattening rank scan (n x n x n): status

Updated 2026-10-07 10:04 UTC.  For each format and rank r: the lowest degree d in which some isotypic flattening has smaller rank on a random rank-r tensor than on a random rank-(r+1) tensor, and all components that do it in that degree.  Configurations: `1H1` = direction 1 (source S^{l1}V^*), one generic functional (dim U = 1); `1H2-4` = stacked flattening S^{l1}V^* -> U^* (x) S^{l2}V (x) S^{l3}V for a generic U of dim 2..4; `1V3` = U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V, dim U = 3.  Partitions are written without commas, e.g. (62,3221,3221).  Method and code: SCAN.md, rankscan.py.

* **3x3x3** (generic rank 5): with d up to 5 [d <= 5 complete] separated r = 1-2 at d = 1; r = 3 at d = 2; r = 4 at d = 5 -- every rank up to r_gen - 1 = 4 is separated (max rank reached at d = 5).  Finished.
* **4x4x4** (generic rank 7): with d up to 8 [d <= 8 complete] separated r = 1-3 at d = 1; r = 4 at d = 2; r = 5 at d = 3; r = 6 at d = 8 -- every rank up to r_gen - 1 = 6 is separated (max rank reached at d = 8).  Finished.
* **5x5x5** (generic rank 10): with d up to 7 [d <= 6 complete; d = 7: 13 of 297 components] separated r = 1-4 at d = 1; r = 5 at d = 2; r = 6 at d = 3; r = 7 at d = 5; r = 8 at d = 6; r = 9 not pursued (rank 9 vs 10 needs higher d; handled by the d13 agent at d = 13, 14 (agents/d13.md)).  Finished.
* **6x6x6** (generic rank 14): with d up to 8 [d <= 7 complete for r = 10; d = 8: 64 of 926 components (running)] separated r = 1-5 at d = 1; r = 6 at d = 2; r = 7 at d = 3; r = 8 at d = 4; r = 9 at d = 5, but NOT r = 10-13 (vs r + 1)
* **7x7x7** (generic rank 19): with d up to 7 [d <= 6 complete for r = 12; d = 7: 256 of 341 components (running)] separated r = 1-6 at d = 1; r = 7 at d = 2; r = 8 at d = 3; r = 9 at d = 4; r = 10-11 at d = 5, but NOT r = 12-18 (vs r + 1)
* **8x8x8** (generic rank 24): with d up to 9 [d <= 6 complete for r = 13; d = 7: 6 of 341 components (running); d = 8: 2 of 995 components; d = 9: 4 of 2665 components] separated r = 1-7 at d = 1; r = 8 at d = 2; r = 9 at d = 3; r = 10 at d = 4; r = 11 at d = 5; r = 12 at d = 6, but NOT r = 13-23 (vs r + 1)
* **9x9x9** (generic rank 30): with d up to 10 [d <= 5 complete for r = 14; d = 6: 83 of 119 components (running); d = 8: 1 of 995 components; d = 9: 2 of 2681 components; d = 10: 4 of 7374 components] separated r = 1-8 at d = 1; r = 9 at d = 2; r = 10 at d = 3; r = 11 at d = 4; r = 12 at d = 5; r = 13 at d = 6, but NOT r = 14-29 (vs r + 1)
* **10x10x10** (generic rank 36): with d up to 10 [d <= 5 complete for r = 15; d = 6: 9 of 119 components (running); d = 9: 1 of 2681 components; d = 10: 2 of 7396 components] separated r = 1-9 at d = 1; r = 10 at d = 2; r = 11 at d = 3; r = 12 at d = 4; r = 13 at d = 5; r = 14 at d = 6, but NOT r = 15-35 (vs r + 1)

## 3x3x3 (generic rank 5)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 3x3x3 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 3x3x3 1H1 |
| 3 vs 4 | 2 | 1 | (2,11,11) g=1 6x3x3 1H1 |
| 4 vs 5 | 5 | 3 | (311,221,221) g=1 6x3x3 1H1; (32,311,221) g=1 15x6x3 1H1; (32,311,311) g=2 15x6x6 1H1-2 1V2 |

## 4x4x4 (generic rank 7)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 4x4x4 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 4x4x4 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 4x4x4 1H1 |
| 4 vs 5 | 2 | 1 | (2,11,11) g=1 10x6x6 1H1 |
| 5 vs 6 | 3 | 1 | (3,111,111) g=1 20x4x4 1H1 |
| 6 vs 7 | 8 | 8 | (5111,3221,3221) g=5 35x15x15 1V5; (53,3311,3311) g=2 280x20x20 1V2; (53,5111,5111) g=2 280x35x35 1V2; (62,3221,3221) g=4 360x15x15 1H2-4; (422,4211,3311) g=6 84x45x20 1V6; (53,5111,4211) g=3 280x35x45 1V2-3; (53,4211,3311) g=4 280x45x20 1V3-4; (53,4211,4211) g=6 280x45x45 1V4-6 |

## 5x5x5 (generic rank 10)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 5x5x5 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 5x5x5 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 5x5x5 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 5x5x5 1H1 |
| 5 vs 6 | 2 | 1 | (2,11,11) g=1 15x10x10 1H1 |
| 6 vs 7 | 3 | 1 | (3,111,111) g=1 35x10x10 1H1 |
| 7 vs 8 | 5 | 1 | (41,2111,2111) g=1 224x24x24 1H1 |
| 8 vs 9 | 6 | 1 | (42,222,21111) g=1 420x50x5 1H1 |
| 9 vs 10 | not pursued: rank 9 vs 10 needs higher d; handled by the d13 agent at d = 13, 14 (agents/d13.md) | 0 | |

## 6x6x6 (generic rank 14)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 6x6x6 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 6x6x6 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 6x6x6 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 6x6x6 1H1 |
| 5 vs 6 | 1 | 1 | (1,1,1) g=1 6x6x6 1H1 |
| 6 vs 7 | 2 | 1 | (2,11,11) g=1 21x15x15 1H1 |
| 7 vs 8 | 3 | 1 | (3,111,111) g=1 56x20x20 1H1 |
| 8 vs 9 | 4 | 1 | (4,1111,1111) g=1 126x15x15 1H1 |
| 9 vs 10 | 5 | 1 | (41,2111,11111) g=1 504x84x6 1H1 |
| 10 vs 11 | not yet (checked up to d = 8) | 0 | |
| 11 vs 12 | not yet (checked up to d = 8) | 0 | |
| 12 vs 13 | not yet (checked up to d = 8) | 0 | |
| 13 vs 14 | not yet (checked up to d = 8) | 0 | |

## 7x7x7 (generic rank 19)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 5 vs 6 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 6 vs 7 | 1 | 1 | (1,1,1) g=1 7x7x7 1H1 |
| 7 vs 8 | 2 | 1 | (2,11,11) g=1 28x21x21 1H1 |
| 8 vs 9 | 3 | 1 | (3,111,111) g=1 84x35x35 1H1 |
| 9 vs 10 | 4 | 1 | (4,1111,1111) g=1 210x35x35 1H1 |
| 10 vs 11 | 5 | 1 | (5,11111,11111) g=1 462x21x21 1H1 |
| 11 vs 12 | 5 | 1 | (5,11111,11111) g=1 462x21x21 1H1 |
| 12 vs 13 | not yet (checked up to d = 7) | 0 | |
| 13 vs 14 | not yet (checked up to d = 7) | 0 | |
| 14 vs 15 | not yet (checked up to d = 7) | 0 | |
| 15 vs 16 | not yet (checked up to d = 7) | 0 | |
| 16 vs 17 | not yet (checked up to d = 7) | 0 | |
| 17 vs 18 | not yet (checked up to d = 7) | 0 | |
| 18 vs 19 | not yet (checked up to d = 7) | 0 | |

## 8x8x8 (generic rank 24)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 5 vs 6 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 6 vs 7 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 7 vs 8 | 1 | 1 | (1,1,1) g=1 8x8x8 1H1 |
| 8 vs 9 | 2 | 1 | (2,11,11) g=1 36x28x28 1H1 |
| 9 vs 10 | 3 | 1 | (3,111,111) g=1 120x56x56 1H1 |
| 10 vs 11 | 4 | 1 | (4,1111,1111) g=1 330x70x70 1H1 |
| 11 vs 12 | 5 | 1 | (5,11111,11111) g=1 792x56x56 1H1 |
| 12 vs 13 | 6 | 1 | (6,111111,111111) g=1 1716x28x28 1H1 |
| 13 vs 14 | not yet (checked up to d = 9) | 0 | |
| 14 vs 15 | not yet (checked up to d = 9) | 0 | |
| 15 vs 16 | not yet (checked up to d = 9) | 0 | |
| 16 vs 17 | not yet (checked up to d = 9) | 0 | |
| 17 vs 18 | not yet (checked up to d = 9) | 0 | |
| 18 vs 19 | not yet (checked up to d = 9) | 0 | |
| 19 vs 20 | not yet (checked up to d = 9) | 0 | |
| 20 vs 21 | not yet (checked up to d = 9) | 0 | |
| 21 vs 22 | not yet (checked up to d = 9) | 0 | |
| 22 vs 23 | not yet (checked up to d = 9) | 0 | |
| 23 vs 24 | not yet (checked up to d = 9) | 0 | |

## 9x9x9 (generic rank 30)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 5 vs 6 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 6 vs 7 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 7 vs 8 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 8 vs 9 | 1 | 1 | (1,1,1) g=1 9x9x9 1H1 |
| 9 vs 10 | 2 | 1 | (2,11,11) g=1 45x36x36 1H1 |
| 10 vs 11 | 3 | 1 | (3,111,111) g=1 165x84x84 1H1 |
| 11 vs 12 | 4 | 1 | (4,1111,1111) g=1 495x126x126 1H1 |
| 12 vs 13 | 5 | 1 | (5,11111,11111) g=1 1287x126x126 1H1 |
| 13 vs 14 | 6 | 1 | (6,111111,111111) g=1 3003x84x84 1H1 |
| 14 vs 15 | not yet (checked up to d = 10) | 0 | |
| 15 vs 16 | not yet (checked up to d = 10) | 0 | |
| 16 vs 17 | not yet (checked up to d = 10) | 0 | |
| 17 vs 18 | not yet (checked up to d = 10) | 0 | |
| 18 vs 19 | not yet (checked up to d = 10) | 0 | |
| 19 vs 20 | not yet (checked up to d = 10) | 0 | |
| 20 vs 21 | not yet (checked up to d = 10) | 0 | |
| 21 vs 22 | not yet (checked up to d = 10) | 0 | |
| 22 vs 23 | not yet (checked up to d = 10) | 0 | |
| 23 vs 24 | not yet (checked up to d = 10) | 0 | |
| 24 vs 25 | not yet (checked up to d = 10) | 0 | |
| 25 vs 26 | not yet (checked up to d = 10) | 0 | |
| 26 vs 27 | not yet (checked up to d = 10) | 0 | |
| 27 vs 28 | not yet (checked up to d = 10) | 0 | |
| 28 vs 29 | not yet (checked up to d = 10) | 0 | |
| 29 vs 30 | not yet (checked up to d = 10) | 0 | |

## 10x10x10 (generic rank 36)

| r vs r+1 | lowest d | # components | separating components at that degree: partitions, g, dims, configurations |
|---|---|---|---|
| 1 vs 2 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 2 vs 3 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 3 vs 4 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 4 vs 5 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 5 vs 6 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 6 vs 7 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 7 vs 8 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 8 vs 9 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 9 vs 10 | 1 | 1 | (1,1,1) g=1 10x10x10 1H1 |
| 10 vs 11 | 2 | 1 | (2,11,11) g=1 55x45x45 1H1 |
| 11 vs 12 | 3 | 1 | (3,111,111) g=1 220x120x120 1H1 |
| 12 vs 13 | 4 | 1 | (4,1111,1111) g=1 715x210x210 1H1 |
| 13 vs 14 | 5 | 1 | (5,11111,11111) g=1 2002x252x252 1H1 |
| 14 vs 15 | 6 | 1 | (6,111111,111111) g=1 5005x210x210 1H1 |
| 15 vs 16 | not yet (checked up to d = 10) | 0 | |
| 16 vs 17 | not yet (checked up to d = 10) | 0 | |
| 17 vs 18 | not yet (checked up to d = 10) | 0 | |
| 18 vs 19 | not yet (checked up to d = 10) | 0 | |
| 19 vs 20 | not yet (checked up to d = 10) | 0 | |
| 20 vs 21 | not yet (checked up to d = 10) | 0 | |
| 21 vs 22 | not yet (checked up to d = 10) | 0 | |
| 22 vs 23 | not yet (checked up to d = 10) | 0 | |
| 23 vs 24 | not yet (checked up to d = 10) | 0 | |
| 24 vs 25 | not yet (checked up to d = 10) | 0 | |
| 25 vs 26 | not yet (checked up to d = 10) | 0 | |
| 26 vs 27 | not yet (checked up to d = 10) | 0 | |
| 27 vs 28 | not yet (checked up to d = 10) | 0 | |
| 28 vs 29 | not yet (checked up to d = 10) | 0 | |
| 29 vs 30 | not yet (checked up to d = 10) | 0 | |
| 30 vs 31 | not yet (checked up to d = 10) | 0 | |
| 31 vs 32 | not yet (checked up to d = 10) | 0 | |
| 32 vs 33 | not yet (checked up to d = 10) | 0 | |
| 33 vs 34 | not yet (checked up to d = 10) | 0 | |
| 34 vs 35 | not yet (checked up to d = 10) | 0 | |
| 35 vs 36 | not yet (checked up to d = 10) | 0 | |

## Coverage, time and memory per (n, d)

checked = components with a result (all three directions, every needed rank); remaining = not yet run (cost proxy above the current band, or job still running); partial = some direction or rank infeasible (memory caps), worker failure or time limit.  CPU h = sum over components; wall s / RSS MB = largest single component.

| n | d | components (g>0) | checked | cost band reached | remaining | partial/failed | CPU h | max wall s | max RSS MB |
|---|---|---|---|---|---|---|---|---|---|
| 3 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 3 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 3 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 3 | 4 | 12 | 12 | 3e+05 | 0 | 0 | 0.00 | 0 | 36 |
| 3 | 5 | 24 | 24 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 4 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 34 |
| 4 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 4 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 4 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 4 | 5 | 36 | 36 | 3e+05 | 0 | 0 | 0.00 | 0 | 42 |
| 4 | 6 | 92 | 92 | 3e+05 | 0 | 0 | 0.01 | 1 | 148 |
| 4 | 7 | 195 | 195 | 3e+06 | 0 | 0 | 0.07 | 14 | 658 |
| 4 | 8 | 426 | 426 | 3e+07 | 0 | 0 | 0.68 | 118 | 912 |
| 5 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 34 |
| 5 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 5 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 5 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.00 | 0 | 71 |
| 5 | 5 | 40 | 40 | 3e+05 | 0 | 0 | 0.01 | 2 | 325 |
| 5 | 6 | 113 | 113 | 3e+06 | 0 | 0 | 0.08 | 18 | 870 |
| 5 | 7 | 297 | 13 | 3e+05 | 284 | 0 | 0.01 | 12 | 436 |
| 6 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 6 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 6 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 41 |
| 6 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.00 | 1 | 250 |
| 6 | 5 | 40 | 40 | 3e+06 | 0 | 0 | 0.03 | 19 | 656 |
| 6 | 6 | 119 | 119 | 3e+07 | 0 | 0 | 0.78 | 232 | 1332 |
| 6 | 7 | 333 | 333 | 3e+09 | 0 | 0 | 31.94 | 8292 | 6761 |
| 6 | 8 | 926 | 64 | 3e+06 | 862 | 0 | 9.47 | 2063 | 1277 |
| 7 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 7 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 7 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 49 |
| 7 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.01 | 5 | 336 |
| 7 | 5 | 40 | 40 | 3e+07 | 0 | 0 | 0.39 | 831 | 1696 |
| 7 | 6 | 119 | 119 | 3e+08 | 0 | 0 | 6.13 | 1124 | 2124 |
| 7 | 7 | 341 | 256 | 3e+08 | 85 | 6 | 130.53 | 24166 | 3145 |
| 7 | 8 | 983 | 0 | 3e+05 | 983 | 0 | 0.00 | 0 | 0 |
| 8 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 8 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 8 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 1 | 67 |
| 8 | 4 | 15 | 15 | 3e+06 | 0 | 0 | 0.02 | 18 | 770 |
| 8 | 5 | 40 | 40 | 3e+07 | 0 | 0 | 0.45 | 161 | 1902 |
| 8 | 6 | 119 | 119 | 3e+09 | 0 | 0 | 34.73 | 8059 | 10023 |
| 8 | 7 | 341 | 6 | 3e+07 | 335 | 2 | 1.29 | 2199 | 2466 |
| 8 | 8 | 995 | 2 | 3e+05 | 993 | 2 | 0.00 | 0 | 34 |
| 8 | 9 | 2665 | 4 | 3e+05 | 2661 | 4 | 0.00 | 0 | 35 |
| 9 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 9 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 36 |
| 9 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 1 | 123 |
| 9 | 4 | 15 | 15 | 3e+06 | 0 | 0 | 0.08 | 179 | 2138 |
| 9 | 5 | 40 | 40 | 3e+08 | 0 | 0 | 1.49 | 546 | 2170 |
| 9 | 6 | 119 | 83 | 3e+08 | 36 | 5 | 47.42 | 13319 | 4051 |
| 9 | 7 | 341 | 0 | - | 341 | 0 | 0.00 | 0 | 0 |
| 9 | 8 | 995 | 1 | 3e+05 | 994 | 1 | 0.00 | 0 | 34 |
| 9 | 9 | 2681 | 2 | 3e+05 | 2679 | 2 | 0.00 | 0 | 35 |
| 9 | 10 | 7374 | 4 | 3e+05 | 7370 | 4 | 0.00 | 0 | 37 |
| 10 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 10 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 10 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 3 | 210 |
| 10 | 4 | 15 | 15 | 3e+07 | 0 | 0 | 0.07 | 52 | 1884 |
| 10 | 5 | 40 | 40 | 3e+08 | 0 | 0 | 5.05 | 1278 | 6392 |
| 10 | 6 | 119 | 9 | 3e+08 | 110 | 1 | 2.44 | 2233 | 2729 |
| 10 | 7 | 341 | 0 | - | 341 | 0 | 0.00 | 0 | 0 |
| 10 | 8 | 995 | 0 | - | 995 | 0 | 0.00 | 0 | 0 |
| 10 | 9 | 2681 | 1 | 3e+05 | 2680 | 1 | 0.00 | 0 | 35 |
| 10 | 10 | 7396 | 2 | 3e+05 | 7394 | 2 | 0.00 | 0 | 37 |

## Last resource samples (scan/monitor.log)

```
2026-10-07T09:54:07Z avail=13400MB cgroup=2225MB cgroup_peak=13216MB load=3.12 workers=3 n7_d7_s4:10991:732MB:7402s n9_d6_s4:12700:854MB:995s n8_d7_s3:12910:568MB:304s
2026-10-07T09:59:10Z avail=13403MB cgroup=2251MB cgroup_peak=13216MB load=3.12 workers=3 n7_d7_s4:10991:708MB:7705s n9_d6_s4:12700:932MB:1298s n8_d7_s3:12910:540MB:607s
2026-10-07T10:04:13Z avail=12343MB cgroup=3306MB cgroup_peak=13216MB load=3.10 workers=3 n7_d7_s4:10991:768MB:8008s n9_d6_s4:12700:1425MB:1601s n10_d6_s4:13053:1038MB:148s
```
