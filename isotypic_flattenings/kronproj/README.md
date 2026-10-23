# Random projections of the Kronecker spaces (4x5x5 rank 8 vs 9, 5x5x5 rank 9 vs 10)

Companion of the combined-flattening search (`combined/` on branch `claude/tender-ride-7mz2gl`, session "Isotypic flattening
rank separation agents").  T^{⊗d} = ⊕ S_λA ⊗ S_μB ⊗ S_νC ⊗ M_{λμν}, M = Kronecker space (dim g).  By Schur's lemma the only
freedom a GL(A)×GL(B)×GL(C)-equivariant flattening has is a linear map on the Kronecker spaces, and for EVERY such map the
rank is a lower semicontinuous GL-invariant (a drop on general rank-r tensors gives equations of σ_r).

**What was already covered (checked 2026-10-22 before starting).**  `combined/comb_search.py` builds every lattice with
`levels='ends'`: each block uses either one generic functional of M (level 1) or the whole M (level g); the library's
`levels='all'` option is never called.  Overlaps: `--aux 2` (a shared 2-dim auxiliary space: a random 2-dim projection,
on the side opposite to the members), family E (generic Ψ ∈ M^*⊗C^k*⊗C^l with k, l ≥ 2, full rank min(g, kl)).  The
isotypic sweeps (`sweep_fast.py`, d10 / d13 agents) use gN (1 functional) and HN / VN (all of M); intermediate subspaces were
only looked at by hand for the C^4 d=8 hit, and `specialU.py` tried natural (non-random) subspaces at C^4.

**Here: every block uses a random projection of M of rank s, 1 ≤ s ≤ g** (s = 1: a generic functional, the same for H
and V; s = g: the whole M).

| type | flattening | code |
|---|---|---|
| H_s | S^λA^* → U^* ⊗ S^μB ⊗ S^νC, U ⊂ M^* random of dim s | `kp_single.py` (cut samples), kpA singles |
| V_s | U ⊗ S^λA^* → S^μB ⊗ S^νC | `kp_single.py`, kpB singles |
| kpA | fixed source λ, ⊕ over a set of targets, member j at level s_j (target side) | `kp_search.py --fam A` |
| kpB | fixed target (μ, ν), ⊕ over a set of sources, member i at level s_i (source side) | `kp_search.py --fam B` |
| kpE | one component, k×l grid, Ψ = P·Q of rank s, 2 ≤ s < min(g, kl) (pencils / nets of functionals, e.g. the L_2 pencil [[F1, F2, 0], [0, F1, F2]] for 2×3, s = 2) | `--fam E` |
| kpG | several sources × several targets, X_i = C^{k_i}, Y_j = C^{l_j}, block (i, j) of random rank s_ij | `--fam G` |

kpA over all targets with all s_j = g_j is S_λ(T_A) (never separates); with s_j < g_j it is a different map.
Levels are nested (level s = the first s columns of one generic Ψ), so each level is a generic s-dim projection and sums are
lattice dimensions (combflat.LatticeFamily, since 2026-10-23 the fast low-memory `combined/combflat.py` of `claude/project-thread-ttahoa`, see `SWITCH.md`; before: copied from `combined/` at 82d3d98; with its validation `test_comb.py`
and `brute.py`).  Per lattice: all singles (member, s); **all level vectors** (s_m ∈ 0..g_m) when ∏(g_m + 1) ≤ `--exh`
(incremental RREF walk), otherwise uniform / codim-t levels, full sum with one member lowered, all-but-one, natural groups,
pairs with all level combinations, random level vectors and greedy growth.  Lattices whose members all have g = 1 are
skipped (identical to the combined agent's search).  Hit classes: **[I]** some level strictly between 1 and g (not covered
before), **[M]** levels 1 and g mixed in one sum, **[E]** ends only, **[G]** general blocks.

Tensors: the same random rank-r tensors as `sweep_fast.py` / `comb_search.py` (seed 5), exact mod p = 524287; a hit is to be
re-checked with other seeds and `PRIME=524269`.

## Validation (`python3 test_kp.py quick|full`)
* H_s / V_s for every s from the lattice == assembled block matrix with an independent Ψ of shape (g, 1, s) / (g, s, 1)
  (4x5x5 d=6 both directions, 5x5x5 d=6, components with g up to 5);
* random mixed-level sums (A and B) == assembled block matrices with the lattice's Ψ;
* known values: C^3 d=5 ((3,2),(3,1,1),(3,1,1)) H1 12/15, V2 15/21; (full) C^4 d=8 ((6,2),(3,2,2,1),(3,2,2,1)) H1 225/225,
  H_2 = H_3 = H_4 = 304/309;
* grids: rank-1 Ψ gives min(k,l)·gN, a generic square pencil gives k·gN, the 2×3 pencil equals the hand-built L_2 block;
* the exhaustive walk (incremental RREF) == direct lattice ranks on every node.
* `kp_single.py` at 4x5x5 d=6 dir 0 reproduces the kpA / kpB singles.

## Running
```
pip install numpy sympy opt_einsum
python3 kp_jobs.py jobs.txt 4          # resumable job runner, logs in logs/jobs/<job>_partK.log
python3 kp_search.py 4,5,5 6 8,9 --dir 1 --fam A,B,E      # one search
python3 kp_single.py 5 8 9,10 --mode H --worker 0 --nworkers 2
```
Flattening matrices are cached in `live/cache/` (untracked).  Status and results: `STATUS.md`.
