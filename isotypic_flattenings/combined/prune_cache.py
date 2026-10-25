"""prune_cache.py -- delete cached flattenings that no job of a job file will read again.

usage: python3 prune_cache.py JOBFILE [--do]        (without --do: dry run, prints what would be deleted)

A cached flattening live/cache/<tag>/r<r>_<lam>_<mu>_<nu>.npy belongs to one family-B target mu|nu.  Once every job
of JOBFILE that uses the directory <tag> (same n, d, seed, dir, ranks, aux max and sources as Context computes it) has
a summary (or SKIPPED) line for that target in its logs/jobs/<name>_part*.log, a restart with --resume never loads the
file again, so it is deleted.  Directories used by a job with family A or E (they read every target of a source) are
left alone.  comb_jobs.py runs this every 10 minutes (2026-10-23: the cache of three d = 7, 8 pattern jobs reached
30 GB and filled the disk)."""
import os, re, sys, glob, shlex, hashlib, argparse
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from combflat import partitions

def job_args(a):
    ap = argparse.ArgumentParser(add_help=False)
    ap.add_argument('n'); ap.add_argument('d', type=int); ap.add_argument('ranks')
    ap.add_argument('--fam', default='A,B'); ap.add_argument('--aux', default='1'); ap.add_argument('--dir', type=int, default=0)
    ap.add_argument('--seed', type=int, default=5); ap.add_argument('--sources', default='')
    ap.add_argument('--cache', default=os.path.join(HERE, 'live', 'cache'))
    ap.add_argument('--only-mn', dest='only_mn', default='')
    return ap.parse_known_args(shlex.split(a))[0]

def cache_dir(o):
    """the directory Context(...) uses for these comb_search arguments (same rules as combflat.Context.__init__)."""
    ns = tuple(int(x) for x in o.n.split(',')); ns = ns * 3 if len(ns) == 1 else ns
    ranks = [int(x) for x in o.ranks.split(',')]
    auxmax = max(int(x) for x in o.aux.split(','))
    src = None
    if o.sources.startswith('pattern:'):
        kk = int(o.sources.split(':')[1])
        src = [l for l in partitions(o.d, ns[o.dir]) if l[0] >= o.d - kk and l != (o.d,)]
    elif o.sources:
        src = [tuple(int(c) for c in s.split('.')) if '.' in s else tuple(int(c) for c in s) for s in o.sources.split(';') if s]
    tag = 'n%s_d%d_s%d_dir%d_r%s_nc%s_kc%s_ax%d' % ('-'.join(map(str, ns)), o.d, o.seed, o.dir, '-'.join(map(str, ranks)),
                                                   float('inf'), float('inf'), auxmax)
    if src is not None:
        tag += '_src' + hashlib.md5(repr(sorted(src)).encode()).hexdigest()[:8]
    return os.path.join(o.cache, tag)

def done_targets(name):
    """(finished, set of 'mu|nu' with a family-B summary or SKIPPED line) from the job's logs."""
    done, fin = set(), False
    for f in glob.glob(os.path.join(HERE, 'logs', 'jobs', '%s_part*.log' % name)):
        for l in open(f, errors='replace'):
            m = re.match(r'famB(?:\(aux=\d+\))? mn=(\S+) (?:members=|aux=\d+ SKIPPED)', l)
            if m:
                done.add(m.group(1))
            elif l.startswith('n=') and ' total ' in l:
                fin = True
    return fin, done

def main():
    jobfile, do = sys.argv[1], '--do' in sys.argv
    dirs = {}
    for l in open(jobfile):
        l = l.split('#')[0].strip()
        if not l:
            continue
        name, a = [x.strip() for x in l.split('|', 1)]
        o = job_args(a)
        dirs.setdefault(cache_dir(o), []).append((name, o))
    tot = 0
    for d, jobs in sorted(dirs.items()):
        if not os.path.isdir(d):
            continue
        states = [(name, o) + done_targets(name) for name, o in jobs]
        if any(not fin and set(o.fam.split(',')) - {'B'} for name, o, fin, _ in states):
            continue                                        # a running/waiting family A or E job reads whole sources
        # an unfinished job needs a target unless it has a summary line for it or excludes it by --only-mn
        live = [(dn, set(x for x in o.only_mn.split(';') if x)) for name, o, fin, dn in states if not fin]
        n = b = 0
        for f in glob.glob(os.path.join(d, 'r*_*_*_*.npy')):
            parts = os.path.basename(f)[:-4].split('_')
            if len(parts) != 4:
                continue
            mn = parts[2] + '|' + parts[3]
            if all(mn in dn or (only and mn not in only) for dn, only in live):
                n += 1; b += os.path.getsize(f)
                if do:
                    os.remove(f)
        if n:
            print('%s %s: %d files, %.2f GB (%s)' % ('deleted' if do else 'would delete', os.path.basename(d), n, b / 1e9,
                                                   ', '.join(name for name, _ in jobs)))
        tot += b
    print('total %.2f GB%s' % (tot / 1e9, '' if do else ' (dry run)'))

if __name__ == '__main__':
    main()
