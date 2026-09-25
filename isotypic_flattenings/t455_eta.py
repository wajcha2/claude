"""ETA for the unfinished components of the C^4x5x5 sweep: fit secs ~ a*cost^b on finished components of the same
degree (log-log least squares), predict the rest with the cost proxy of sweep_fast (g * sum (dim_i+4)^2), 3 workers."""
import glob, re, itertools, sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hwv import dim_schur
from t455_common import components as comps, cost, ns
jobs = [tuple(l.split()) for l in open('t455_jobs.txt') if l.strip() and not l.startswith('#')]
done = {}
for lf in glob.glob('hwv455_d*_w*.log'):
    d = int(re.search(r'hwv455_d(\d+)', lf).group(1))
    for line in open(lf):
        m = re.match(r'lam=(\(.*?\)\)) g=(\d+) .* cost=([\d.e+]+) \(([\d.]+)s\)', line)
        if m: done[(d, eval(m.group(1)))] = (float(m.group(3)), float(m.group(4)))
def fit(points):
    n = len(points); mx = sum(x for x, _ in points) / n; my = sum(y for _, y in points) / n
    b = sum((x - mx) * (y - my) for x, y in points) / sum((x - mx) ** 2 for x, _ in points); a = my - b * mx
    return a, b
allpts = [(math.log(c), math.log(max(s, 0.05))) for (c, s) in done.values() if c > 0]
total = 0; seen = set()
for d, M in jobs:
    d = int(d); Mf = float('inf') if M == 'inf' else float(M)
    members = [(lam, g) for lam, g in comps(d) if (d, lam) not in seen and max(dim_schur(l, ns[t]) for t, l in enumerate(lam)) <= Mf]
    seen |= {(d, lam) for lam, g in members}
    rest = [(lam, g) for lam, g in members if (d, lam) not in done]
    if not rest: continue
    # fit on the finished components of this very job if there are enough, else on the 300 most expensive finished ones overall
    own = [(math.log(done[(d, lam)][0]), math.log(max(done[(d, lam)][1], 0.05))) for lam, g in members if (d, lam) in done and done[(d, lam)][0] > 0]
    pts = own if len(own) >= 30 else sorted(allpts)[-300:]
    a, b = fit(pts); pred = lambda c: math.exp(a + b * math.log(c))
    est = sum(pred(cost(lam, g)) for lam, g in rest) / 3 / 3600; total += est
    print("job d=%d MAXDIM=%s: %d of %d components left, predicted %.1f h wall on 3 workers (fit secs=%.3g*cost^%.2f on %d comps); largest single %.2f h" % (
        d, M, len(rest), len(members), est, math.exp(a), b, len(pts), max(pred(cost(lam, g)) for lam, g in rest) / 3600))
print("total predicted wall time for the queue: %.1f h" % total)
