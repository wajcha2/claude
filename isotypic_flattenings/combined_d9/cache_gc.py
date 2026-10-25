"""cache_gc.py -- free disk: delete cached flattenings (live/cache/<tag>/r<r>_<lam>_<mu>_<nu>.npy) of targets whose family-B
lattices are finished (summary line) in the logs of the jobs that alone use that cache (d9_455_dir1_B, d9_555_B and their
--bmin complements *_big; every aux listed in the job must be summarised).  The dir-0 cache is shared with the family-A job (all targets of a source) and is kept.
usage: python3 cache_gc.py [--dry]"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBS = {'d9_455_dir1_B': ('n4-5-5_d9_s5_dir1_r8-9_*_ax1_srca3d7b922', [1]), 'd9_555_B': ('n5-5-5_d9_s5_dir0_r9-10_*_ax1_srca3d7b922', [1]),
        'd9_455_dir1_B_big': ('n4-5-5_d9_s5_dir1_r8-9_*_ax1_srca3d7b922', [1]), 'd9_555_B_big': ('n5-5-5_d9_s5_dir0_r9-10_*_ax1_srca3d7b922', [1]),
        'd9_455_dir0_B_p3': ('n4-5-5_d9_s5_dir0_r8-9_*_ax1_src2307563d', [1]),      # ax1 dir 0 = the lam_1 >= 6 pass only (src a3d7b922 = sources lam_1 >= 7, 2307563d = lam_1 >= 6)
        'd9_555_B_p3': ('n5-5-5_d9_s5_dir0_r9-10_*_ax1_src2307563d', [1])}     # its own cache only (the pattern:2 cache is in use by d9_555_B_big)
dry = '--dry' in sys.argv
freed = 0
for job, (pat, auxes) in JOBS.items():
    done = {}
    for f in glob.glob(os.path.join(HERE, 'logs', 'jobs', '%s_part*.log' % job)):
        for l in open(f):
            # only lattice summaries (members=): a 'SKIPPED' line of the bmax job is a target the --bmin job computes
            m = re.match(r'famB(?:\(aux=(\d+)\))? mn=(\S+)\|(\S+) members=', l)
            if m:
                done.setdefault((m.group(2), m.group(3)), set()).add(int(m.group(1) or 1))
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
