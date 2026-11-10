"""Koszul flattenings (large projections) and degree-2 isotypic flattenings of the isotypic tensor, all components,
using the fast evaluator.  usage: python3 koszul_fast.py n d r_low,r_high maxprod [KBUDGET]"""
import numpy as np, sys, time, itertools, os
import hwv, hwv_fast
hwv.flattening_matrix = hwv_fast.flattening_matrix_fast
from hwv import *
from isoflat import modrank
import koszul, schur2
n = int(sys.argv[1]); d = int(sys.argv[2]); rl, rh = [int(x) for x in sys.argv[3].split(',')]
maxprod = float(sys.argv[4]) if len(sys.argv) > 4 else 3e6
rng = np.random.default_rng(61)
DONE = set()
for lf in os.environ.get('RESUME', '').split(':'):
    if lf and os.path.exists(lf):
        DONE |= {l.split(' g=')[0] for l in open(lf) if l.startswith('lam=') and 'SKIPPED' not in l}
WK, NW = [int(x) for x in os.environ.get('WORKER', '0/1').split('/')]
MINPROD = float(os.environ.get('MINPROD', '0'))   # skip components whose full grid has <= MINPROD points (done by another pass)
todo, ci = [], -1
for lam in itertools.combinations_with_replacement(partitions(d, n), 3):
    g = kronecker(*lam)
    if g == 0: continue
    ci += 1
    if ci % NW != WK: continue
    if ('lam=%s' % (lam,)) in DONE: continue
    dims = tuple(dim_schur(l, n) for l in lam)
    full = np.prod([x + 2 for x in dims])
    if full <= MINPROD: continue
    cost = koszul.kwedge_cost(dims) if koszul.KWEDGE else np.prod([min(x + 2, koszul.GCAP) if koszul.GCAP else x + 2 for x in dims])
    if cost > maxprod:
        print("lam=%s dims=%s SKIPPED (size)" % (lam, dims)); sys.stdout.flush(); continue
    todo.append((cost, lam, g, dims))
todo.sort()
print("# %d components to do, costs %s .. %s" % (len(todo), todo[0][0] if todo else None, todo[-1][0] if todo else None)); sys.stdout.flush()
CLAIMDIR = os.environ.get('CLAIMDIR', '')   # dynamic claims: any number of workers (all WORKER=0/1) share the queue
if CLAIMDIR: os.makedirs(CLAIMDIR, exist_ok=True)
def _cfile(lam): return os.path.join(CLAIMDIR, '_'.join('-'.join(map(str, l)) for l in lam))
def claim(lam):
    """One file per component holding the pid of the worker computing it ('done' once finished).  A claim whose pid is
    dead (crash, container replacement) is taken over; a finished component is never recomputed."""
    if not CLAIMDIR: return True
    cf, me = _cfile(lam), '%d\n' % os.getpid()
    try:
        fd = os.open(cf, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.write(fd, me.encode()); os.close(fd); return True
    except FileExistsError:
        pass
    txt = open(cf).read().strip()
    if txt == 'done': return False
    try:
        pid = int(txt)
        alive = os.path.exists('/proc/%d' % pid) and b'koszul_fast' in open('/proc/%d/cmdline' % pid, 'rb').read()
    except Exception:
        alive = False
    if alive: return False
    open(cf, 'w').write(me); return True
def release(lam):
    if CLAIMDIR: open(_cfile(lam), 'w').write('done\n')
for cost, lam, g, dims in todo:
    if not claim(lam): continue
    t0 = time.time()
    try: line = koszul.analyse(lam, n, rl, rh, rng, pks=(1, 2))
    except Exception as ex: line = "lam=%s ERROR %r" % (lam, ex)
    print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
    if os.environ.get('DEG2', '0') == '1':
        t0 = time.time()
        try: line = schur2.analyse(lam, n, rl, rh, rng)
        except Exception as ex: line = "lam=%s DEG2 ERROR %r" % (lam, ex)
        print(line + " (%.0fs)" % (time.time() - t0)); sys.stdout.flush()
    release(lam)
