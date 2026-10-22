"""d9_report.py -- summary of the degree-9 job logs (logs/jobs/<job>_partK.log): lattices / components done, skipped,
separations, saturation (lattices whose 'all' value is the same on both ranks and equals the compressed size bound) and
time.  usage: python3 d9_report.py [jobfile]"""
import os, re, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))
JOBDIR = os.path.join(HERE, 'logs', 'jobs')
jobfile = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'jobs_d9.txt')
jobs = []
for l in open(jobfile):
    l = l.split('#')[0].strip()
    if l:
        jobs.append(l.split('|')[0].strip())
print('| job | lattices / components done | skipped (size > bmax) | separations | finished | time (s) |')
print('|---|---|---|---|---|---|')
for name in jobs:
    fs = sorted(glob.glob(os.path.join(JOBDIR, '%s_part*.log' % name)))
    if not fs:
        print('| %s | not started | | | | |' % name)
        continue
    lat, skip, sep, secs, fin = set(), set(), 0, 0.0, False
    for f in fs:
        for l in open(f):
            m = re.match(r'(fam[AB](?:\(aux=\d+\))? (?:lam|mn)=\S+) members=.*\(([\d.]+)s\)\s*$', l)
            if m:
                lat.add(m.group(1)); secs += float(m.group(2)); continue
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
    print('| %s | %d | %d | %d | %s | %.0f |' % (name, len(lat), len(skip), sep, 'yes' if fin else 'no', secs))
