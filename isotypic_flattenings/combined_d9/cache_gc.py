"""cache_gc.py -- free disk: delete cached flattenings (live/cache/<tag>/r<r>_<lam>_<mu>_<nu>.npy) of targets whose family-B
lattices are finished in the logs of the jobs that alone use that cache (d9_455_dir1_B, d9_555_B; every aux listed in
the job must be summarised).  The dir-0 cache is shared with the family-A job (all targets of a source) and is kept.
usage: python3 cache_gc.py [--dry]"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBS = {'d9_455_dir1_B': ('n4-5-5_d9_s5_dir1_r8-9_*_ax1_*', [1]), 'd9_555_B': ('n5-5-5_d9_s5_dir0_r9-10_*_ax1_*', [1])}
dry = '--dry' in sys.argv
freed = 0
for job, (pat, auxes) in JOBS.items():
    done = {}
    for f in glob.glob(os.path.join(HERE, 'logs', 'jobs', '%s_part*.log' % job)):
        for l in open(f):
            m = re.match(r'famB(?:\(aux=(\d+)\))? mn=(\S+)\|(\S+) (?:members=|aux=(\d+) SKIPPED)', l)
            if m:
                done.setdefault((m.group(2), m.group(3)), set()).add(int(m.group(1) or m.group(4) or 1))
    fin = {mn for mn, a in done.items() if set(auxes) <= a}
    for d in glob.glob(os.path.join(HERE, 'live', 'cache', pat)):
        for fn in os.listdir(d):
            m = re.match(r'r\d+_[^_]+_([^_]+)_([^_.]+)\.npy$', fn)
            if m and (m.group(1), m.group(2)) in fin:
                path = os.path.join(d, fn)
                freed += os.path.getsize(path)
                if not dry:
                    os.remove(path)
print('%s %.2f GB of finished targets\' flattenings' % ('would free' if dry else 'freed', freed / 2**30))
