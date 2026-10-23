"""kplib.py -- helpers shared by kp_search.py and test_kp.py."""
import numpy as np
from combflat import p, rref, reduce_rows, mulmod, fmm, LatticeFamily, EXTRA
from isoflat import modrank

def add_basis(R, piv, V):
    """span(R) + span(V) as an RREF basis (R, piv), exact mod p (as LatticeFamily.enumerate)."""
    red = reduce_rows(V, R, piv)
    if not red.size or not red.any():
        return R, piv
    Rn, pn = rref(red)
    if not pn:
        return R, piv
    if piv:
        R = np.mod(R - mulmod(R[:, pn], Rn).astype(np.float64), p)
    R2 = np.vstack([R, Rn]).astype(np.float32); p2 = piv + pn
    order = np.argsort(p2)
    return R2[order], [p2[i] for i in order]

def basis_width(fam):
    """number of columns of fam.basis_rows(): the low-memory LatticeFamily (combflat.py of 2026-10-23) keeps every
    subspace on its first fam.ncols generic coordinates instead of all fam.size compressed coordinates; the old one
    has no ncols."""
    return getattr(fam, 'ncols', fam.size)

def empty_basis(fam):
    """the RREF basis (R, piv) of the zero subspace, with the width of fam.basis_rows()."""
    return np.zeros((0, basis_width(fam)), dtype=np.float32), []

class KPLattice(LatticeFamily):
    """combflat.LatticeFamily with a faster dims() for sums of MANY subspaces in a SMALL ambient space (kpA: up to 137
    members in F_p^N1 with N1 = 14..400).  The low-memory dims() ranks the stacked thin matrices (sum of the member
    dims rows x c columns, c <= ncols); when the rows far outnumber the columns (e.g. 1950 x 58 for kpA lam=33 at
    4x5x5 d=6) that rank is 20x slower than the old c x c rank.  Here such a stack is first multiplied by a fixed
    random (c + EXTRA) x rows matrix (rank preserved except with probability < p^-EXTRA, the same argument and the
    same compression the old dims() used with R[:c]); short stacks are ranked as before.  Same numbers."""

    def dims(self, S):
        key = tuple(sorted(S, key=repr))
        if key in self._dims:
            return self._dims[key]
        c = min(self.ncols, sum(max(self._dims[(s,)]) for s in key) + EXTRA)
        out = []
        for r in self.ctx.ranks:
            M = np.vstack([self.mats[r][s][:, :c] for s in key])
            if M.shape[0] > c + 2 * EXTRA:
                G = np.random.default_rng([self.ctx.seed, 19, self.ctx.dirn, self.tag, self.aux, r, M.shape[0], c]).integers(
                    0, p, (c + EXTRA, M.shape[0])).astype(np.float64)
                M = fmm(G, M.astype(np.float64))
            out.append(modrank(M))
        self._dims[key] = tuple(out)
        return self._dims[key]
