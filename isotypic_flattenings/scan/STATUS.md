# Isotypic-flattening rank scan (n x n x n): status

Updated 2026-10-04 06:41 UTC.  For each format and rank r: the lowest degree d in which some isotypic flattening has smaller rank on a random rank-r tensor than on a random rank-(r+1) tensor, and all components that do it in that degree.  Configurations: `1H1` = direction 1 (source S^{l1}V^*), one generic functional (dim U = 1); `1H2-4` = stacked flattening S^{l1}V^* -> U^* (x) S^{l2}V (x) S^{l3}V for a generic U of dim 2..4; `1V3` = U (x) S^{l1}V^* -> S^{l2}V (x) S^{l3}V, dim U = 3.  Partitions are written without commas, e.g. (62,3221,3221).  Method and code: SCAN.md, rankscan.py.

* **3x3x3** (generic rank 5): with d up to 5 [d <= 5 complete] separated r = 1-2 at d = 1; r = 3 at d = 2; r = 4 at d = 5 -- every rank up to r_gen - 1 = 4 is separated (max rank reached at d = 5).  Finished.
* **4x4x4** (generic rank 7): with d up to 6 [d <= 6 complete] separated r = 1-3 at d = 1; r = 4 at d = 2; r = 5 at d = 3, but NOT r = 6 (vs r + 1)
* **5x5x5** (generic rank 10): with d up to 6 [d <= 5 complete; d = 6: 2 of 113 components (running)] separated r = 1-4 at d = 1; r = 5 at d = 2; r = 6 at d = 3; r = 7 at d = 5, but NOT r = 8-9 (vs r + 1)
* **6x6x6** (generic rank 14): with d up to 5 [d <= 4 complete; d = 5: 24 of 40 components] separated r = 1-5 at d = 1; r = 6 at d = 2; r = 7 at d = 3; r = 8 at d = 4; r = 9 at d = 5, but NOT r = 10-13 (vs r + 1)
* **7x7x7** (generic rank 19): with d up to 5 [d <= 4 complete; d = 5: 3 of 40 components (running)] separated r = 1-6 at d = 1; r = 7 at d = 2; r = 8 at d = 3; r = 9 at d = 4, but NOT r = 10-18 (vs r + 1)
* **8x8x8** (generic rank 24): with d up to 4 [d <= 3 complete; d = 4: 8 of 15 components] separated r = 1-7 at d = 1; r = 8 at d = 2; r = 9 at d = 3; r = 10 at d = 4, but NOT r = 11-23 (vs r + 1)
* **9x9x9** (generic rank 30): with d up to 4 [d <= 3 complete; d = 4: 1 of 15 components (running)] separated r = 1-8 at d = 1; r = 9 at d = 2; r = 10 at d = 3, but NOT r = 11-29 (vs r + 1)
* **10x10x10** (generic rank 36): with d up to 3 [d <= 3 complete] separated r = 1-9 at d = 1; r = 10 at d = 2; r = 11 at d = 3, but NOT r = 12-35 (vs r + 1)

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
| 6 vs 7 | not yet (checked up to d = 6) | 0 | |

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
| 8 vs 9 | not yet (checked up to d = 6) | 0 | |
| 9 vs 10 | not yet (checked up to d = 6) | 0 | |

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
| 10 vs 11 | not yet (checked up to d = 5) | 0 | |
| 11 vs 12 | not yet (checked up to d = 5) | 0 | |
| 12 vs 13 | not yet (checked up to d = 5) | 0 | |
| 13 vs 14 | not yet (checked up to d = 5) | 0 | |

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
| 10 vs 11 | not yet (checked up to d = 5) | 0 | |
| 11 vs 12 | not yet (checked up to d = 5) | 0 | |
| 12 vs 13 | not yet (checked up to d = 5) | 0 | |
| 13 vs 14 | not yet (checked up to d = 5) | 0 | |
| 14 vs 15 | not yet (checked up to d = 5) | 0 | |
| 15 vs 16 | not yet (checked up to d = 5) | 0 | |
| 16 vs 17 | not yet (checked up to d = 5) | 0 | |
| 17 vs 18 | not yet (checked up to d = 5) | 0 | |
| 18 vs 19 | not yet (checked up to d = 5) | 0 | |

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
| 11 vs 12 | not yet (checked up to d = 4) | 0 | |
| 12 vs 13 | not yet (checked up to d = 4) | 0 | |
| 13 vs 14 | not yet (checked up to d = 4) | 0 | |
| 14 vs 15 | not yet (checked up to d = 4) | 0 | |
| 15 vs 16 | not yet (checked up to d = 4) | 0 | |
| 16 vs 17 | not yet (checked up to d = 4) | 0 | |
| 17 vs 18 | not yet (checked up to d = 4) | 0 | |
| 18 vs 19 | not yet (checked up to d = 4) | 0 | |
| 19 vs 20 | not yet (checked up to d = 4) | 0 | |
| 20 vs 21 | not yet (checked up to d = 4) | 0 | |
| 21 vs 22 | not yet (checked up to d = 4) | 0 | |
| 22 vs 23 | not yet (checked up to d = 4) | 0 | |
| 23 vs 24 | not yet (checked up to d = 4) | 0 | |

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
| 11 vs 12 | not yet (checked up to d = 4) | 0 | |
| 12 vs 13 | not yet (checked up to d = 4) | 0 | |
| 13 vs 14 | not yet (checked up to d = 4) | 0 | |
| 14 vs 15 | not yet (checked up to d = 4) | 0 | |
| 15 vs 16 | not yet (checked up to d = 4) | 0 | |
| 16 vs 17 | not yet (checked up to d = 4) | 0 | |
| 17 vs 18 | not yet (checked up to d = 4) | 0 | |
| 18 vs 19 | not yet (checked up to d = 4) | 0 | |
| 19 vs 20 | not yet (checked up to d = 4) | 0 | |
| 20 vs 21 | not yet (checked up to d = 4) | 0 | |
| 21 vs 22 | not yet (checked up to d = 4) | 0 | |
| 22 vs 23 | not yet (checked up to d = 4) | 0 | |
| 23 vs 24 | not yet (checked up to d = 4) | 0 | |
| 24 vs 25 | not yet (checked up to d = 4) | 0 | |
| 25 vs 26 | not yet (checked up to d = 4) | 0 | |
| 26 vs 27 | not yet (checked up to d = 4) | 0 | |
| 27 vs 28 | not yet (checked up to d = 4) | 0 | |
| 28 vs 29 | not yet (checked up to d = 4) | 0 | |
| 29 vs 30 | not yet (checked up to d = 4) | 0 | |

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
| 12 vs 13 | not yet (checked up to d = 3) | 0 | |
| 13 vs 14 | not yet (checked up to d = 3) | 0 | |
| 14 vs 15 | not yet (checked up to d = 3) | 0 | |
| 15 vs 16 | not yet (checked up to d = 3) | 0 | |
| 16 vs 17 | not yet (checked up to d = 3) | 0 | |
| 17 vs 18 | not yet (checked up to d = 3) | 0 | |
| 18 vs 19 | not yet (checked up to d = 3) | 0 | |
| 19 vs 20 | not yet (checked up to d = 3) | 0 | |
| 20 vs 21 | not yet (checked up to d = 3) | 0 | |
| 21 vs 22 | not yet (checked up to d = 3) | 0 | |
| 22 vs 23 | not yet (checked up to d = 3) | 0 | |
| 23 vs 24 | not yet (checked up to d = 3) | 0 | |
| 24 vs 25 | not yet (checked up to d = 3) | 0 | |
| 25 vs 26 | not yet (checked up to d = 3) | 0 | |
| 26 vs 27 | not yet (checked up to d = 3) | 0 | |
| 27 vs 28 | not yet (checked up to d = 3) | 0 | |
| 28 vs 29 | not yet (checked up to d = 3) | 0 | |
| 29 vs 30 | not yet (checked up to d = 3) | 0 | |
| 30 vs 31 | not yet (checked up to d = 3) | 0 | |
| 31 vs 32 | not yet (checked up to d = 3) | 0 | |
| 32 vs 33 | not yet (checked up to d = 3) | 0 | |
| 33 vs 34 | not yet (checked up to d = 3) | 0 | |
| 34 vs 35 | not yet (checked up to d = 3) | 0 | |
| 35 vs 36 | not yet (checked up to d = 3) | 0 | |

## Coverage, time and memory per (n, d)

checked = components with a result (all three directions, every needed rank); remaining = not yet run (cost proxy above the current band, or job still running); partial = some direction or rank infeasible (memory caps) or worker failure.  CPU h = sum over components; wall s / RSS MB = largest single component.

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
| 4 | 7 | 195 | 0 | 3e+05 | 195 | 0 | 0.00 | 0 | 0 |
| 5 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 34 |
| 5 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 5 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 5 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.00 | 0 | 71 |
| 5 | 5 | 40 | 40 | 3e+05 | 0 | 0 | 0.01 | 2 | 325 |
| 5 | 6 | 113 | 2 | 3e+05 | 111 | 0 | 0.00 | 1 | 105 |
| 6 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 6 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 6 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 41 |
| 6 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.00 | 1 | 250 |
| 6 | 5 | 40 | 24 | 3e+05 | 16 | 0 | 0.02 | 19 | 656 |
| 6 | 6 | 119 | 0 | 3e+05 | 119 | 0 | 0.00 | 0 | 0 |
| 7 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 7 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 7 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 0 | 49 |
| 7 | 4 | 15 | 15 | 3e+05 | 0 | 0 | 0.01 | 5 | 336 |
| 7 | 5 | 40 | 3 | 3e+05 | 37 | 0 | 0.00 | 7 | 375 |
| 8 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 8 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 8 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 1 | 67 |
| 8 | 4 | 15 | 8 | 3e+05 | 7 | 0 | 0.01 | 17 | 770 |
| 8 | 5 | 40 | 0 | - | 40 | 0 | 0.00 | 0 | 0 |
| 8 | 6 | 119 | 0 | - | 119 | 0 | 0.00 | 0 | 0 |
| 8 | 7 | 341 | 0 | 3e+05 | 341 | 0 | 0.00 | 0 | 0 |
| 9 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 9 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 36 |
| 9 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 1 | 123 |
| 9 | 4 | 15 | 1 | 3e+05 | 14 | 0 | 0.00 | 1 | 50 |
| 10 | 1 | 1 | 1 | 3e+05 | 0 | 0 | 0.00 | 0 | 35 |
| 10 | 2 | 2 | 2 | 3e+05 | 0 | 0 | 0.00 | 0 | 37 |
| 10 | 3 | 5 | 5 | 3e+05 | 0 | 0 | 0.00 | 3 | 210 |
| 10 | 4 | 15 | 0 | - | 15 | 0 | 0.00 | 0 | 0 |
| 10 | 5 | 40 | 0 | - | 40 | 0 | 0.00 | 0 | 0 |
| 10 | 6 | 119 | 0 | - | 119 | 0 | 0.00 | 0 | 0 |
| 10 | 7 | 341 | 0 | - | 341 | 0 | 0.00 | 0 | 0 |
| 10 | 8 | 995 | 0 | - | 995 | 0 | 0.00 | 0 | 0 |
| 10 | 9 | 2681 | 0 | 3e+05 | 2681 | 0 | 0.00 | 0 | 0 |

## Last resource samples (scan/monitor.log)

```
2026-10-04T06:39:37Z avail=15570MB cgroup=70MB cgroup_peak=562MB load=0.06 workers=4 n3_d1_s1:1155:7MB:0s n4_d1_s1:1156:7MB:0s n5_d1_s1:1157:6MB:0s n6_d1_s1:1158:3MB:0s
```
