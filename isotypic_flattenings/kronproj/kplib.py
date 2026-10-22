"""kplib.py -- helpers shared by kp_search.py and test_kp.py."""
import numpy as np
from combflat import p, rref, reduce_rows, mulmod

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
