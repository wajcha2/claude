# m2loci agent status (M2 at the rank-6 drop loci, C^4 (x) C^4 (x) C^4, components with g >= 2)
Session https://claude.ai/code/session_017H9Kf3uFufsJ1Tk1hepqHS, branch `claude/sweet-euler-01spak`. Summary: `M2_LOCI.md`.

Task: find U in M^* with rank_U(general rank-6 tensor) < rank_U(M2) (would reprove border rank M2 = 7), checking the
loci where rank-6 ranks go down (rank-scan agent: 8 separating components at d = 8), for d up to 9 and beyond.

## Results so far
* GL2^3 symmetry bound for every flattening type of M2 (`m2_bound_stacks.py`): exact on 95% of 2244 computed values,
  never violated.  At the 8 d = 8 separators M2 has rank 19, 34, 34, 19, 39, 45, 45, 79 vs rank 6 146-970.  No win.
* d <= 7: every g >= 2 component and direction, all U types: no separation, no win; non-excluded cases have only
  tensor-independent drop loci (rank 7 drops equally).
* d = 9: running (`m2loci/all_d9_w*.log`, 4 workers, cheapest first).

## Restart
```
pip install numpy sympy opt_einsum; cd isotypic_flattenings
export OPENBLAS_NUM_THREADS=1 ALLK=1 NOR6B=1 MEMLIMIT_GB=3.5 MEMEL=4e7
for w in 0 1 2 3; do RESUME=m2loci/all_d9_w$w.log nohup python3 m2cmp2.py LIST m2loci/jobs_d9_sorted.txt 3000 $w 4 >> m2loci/all_d9_w$w.log 2>&1 & done
```
