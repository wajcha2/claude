"""d9_report.py -- summary of the degree-9 job logs (logs/jobs/<job>_partK.log): lattices / components done, skipped,
separations, saturation and time.  A lattice is 'saturated' when every value printed for it (singles and named sums) on
the LOWER rank already equals size - 8 = min(target dimension, sum of g n1) (aux 1): then no subset can separate.  For the
others the largest gap between the size bound and the lower-rank value is listed (largest first).  usage: python3 d9_report.py [jobfile]"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(HERE, 'logs', 'jobs')
jobfile = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'jobs_d9.txt')
jobs = []
for l in open(jobfile):
    l = l.split('#')[0].strip()
    if l:
        jobs.append(l.split('|')[0].strip())
print('| job | lattices / components done | saturated at the lower rank | skipped (size > bmax) | separations | finished | time (s) |')
print('|---|---|---|---|---|---|---|')
unsat = []
for name in jobs:
    fs = sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)))
    if not fs:
        print('| %s | not started | | | | | |' % name)
        continue
    lat, skip, sep, secs, fin, sat = set(), set(), 0, 0.0, False, set()
    for f in fs:
        for l in open(f):
            m = re.match(r'(fam[AB](?:\(aux=\d+\))? (?:lam|mn)=\S+) members=.*\(([\d.]+)s\)\s*$', l)
            if m:
                lat.add(m.group(1)); secs += float(m.group(2))
                size = int(re.search(r' size=(\d+)', l).group(1))
                vals = [tuple(map(int, v.split('/'))) for v in re.findall(r':(\d+(?:/\d+)+)(?=\s)', l.split('  singles: ')[1])]
                lo = max(v[0] for v in vals)
                if '(aux=' not in m.group(1) and lo >= size - 8:
                    sat.add(m.group(1))
                elif '(aux=' not in m.group(1):
                    unsat.append((size - 8 - lo, name, m.group(1), size - 8, max(vals)))
                continue
            m = re.match(r'famE (.*) g=\d+ dims=.*\(([\d.]+)s\)\s*$', l)
            if m:
                lat.add('E ' + m.group(1)); secs += float(m.group(2)); continue
            m = re.match(r'(fam[AB] mn=\S+ aux=\d+) SKIPPED', l)
            if m:
                skip.add(m.group(1)); continue
            if l.startswith('*** SEPARATES'):
                sep += 1
            if ' total ' in l and l.startswith('n='):
                fin = True
    print('| %s | %d | %d | %d | %d | %s | %.0f |' % (name, len(lat), len(sat), len(skip), sep, 'yes' if fin else 'no', secs))
unsat.sort(reverse=True)
print('\nfamily B, aux 1, not saturated at the lower rank: %d lattices (gap = size bound - lower-rank value; values lower/higher rank)' % len(unsat))
for gap, name, lat, cap, v in unsat[:25]:
    print('  %s %s bound %d gap %d max %s' % (name, lat, cap, gap, '/'.join(map(str, v))))
