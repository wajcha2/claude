"""python3 m2loci/joblists.py followups  -> live/needfull_valid.txt   (screen failures with a VALID verdict, not yet followed up,
                                                                       cheapest first; then those whose only verdict is NEEDFULL?)
   python3 m2loci/joblists.py tally      -> screen / follow-up tallies (latest valid verdict wins over NEEDFULL?)"""
import re, glob, sys, collections
def screen_verdicts():
    best = {}
    for fn in sorted(glob.glob('live/screen_d1011_*.log')) + sorted(glob.glob('live/screen_d11tail_*.log')):
        for l in open(fn):
            m = re.match(r'lam=(.*) dir(\d) g=(\d+) n1=(\d+) n23=(\d+) N1=\d+ K=\d+ SCREEN .* (EXCL|NEEDFULL\??) ', l)
            if not m: continue
            key = (m.group(1), int(m.group(2)) - 1); v = m.group(6); g, n1, n23 = map(int, m.group(3, 4, 5))
            if key not in best or best[key][0] == 'NEEDFULL?':
                best[key] = (v, g, n1, n23)
    return best
def followed():
    done = set()
    for fn in glob.glob('live/deep2_*.log'):
        for l in open(fn):
            if l.startswith('lam=') and 'ERROR' not in l and ' g=' in l:
                m = re.match(r'lam=(.*) dir(\d) g=', l); done.add((m.group(1), int(m.group(2)) - 1))
    return done
if __name__ == '__main__':
    best, done = screen_verdicts(), followed()
    if sys.argv[1] == 'followups':
        cost = lambda x: x[1] * x[2] * min(x[1] * x[2], x[3])
        val = sorted([(cost(x), k) for k, x in best.items() if x[0] == 'NEEDFULL' and k not in done])
        inv = sorted([(cost(x), k) for k, x in best.items() if x[0] == 'NEEDFULL?' and k not in done])
        open('live/needfull_valid.txt', 'w').write(''.join('%s %d\n' % k for _, k in val + inv))
        print('follow-ups to do: %d valid NEEDFULL + %d NEEDFULL? (last)' % (len(val), len(inv)))
    else:
        c = collections.Counter()
        for k, x in best.items():
            d = sum(eval(k[0])[0]); c[(d, x[0])] += 1
        for d in (10, 11):
            print('d=%d: screened %d, EXCL %d, NEEDFULL %d, NEEDFULL? %d' % (d, sum(v for (dd, _), v in c.items() if dd == d), c[(d, 'EXCL')], c[(d, 'NEEDFULL')], c[(d, 'NEEDFULL?')]))
        print('follow-ups done:', len(done))
