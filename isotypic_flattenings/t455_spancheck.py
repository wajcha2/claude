"""span<g lines of the C^4x5x5 logs: a direction N with span_N < g used fewer than g independent fillings, so HN is not the
full-multiplicity stack. Harmless when gN already has rank = dim S^{l_N}(source)^* on both tensors (the stack contains that
flattening as a block and has at most that rank). Prints one line per span<g component: 'harmless' or '*** UNRESOLVED'."""
import glob, re, ast
for f in sorted(glob.glob('hwv455_*.log')):
    for l in open(f):
        if not l.startswith('lam=') or ' span=' not in l: continue
        g = int(re.search(r' g=(\d+)', l).group(1))
        sp = [int(x) for x in re.search(r' span=([\d,]+)', l).group(1).split(',')]
        if min(sp) >= g: continue
        dims = ast.literal_eval(re.search(r' dims=(\([^)]*\))', l).group(1))
        bad = []
        for N in range(3):
            if sp[N] >= g: continue
            m = re.search(r' g%d:(\d+)/(\d+)' % (N + 1), l)
            if not m or int(m.group(1)) != dims[N] or int(m.group(2)) != dims[N]: bad.append(N + 1)
        lam = l.split(' g=')[0][4:]
        print('span<g %s: %s g=%d span=%s -> %s' % (f, lam, g, ','.join(map(str, sp)),
              'harmless (g%s = source dim on both tensors)' % ','.join(str(N + 1) for N in range(3) if sp[N] < g) if not bad
              else '*** UNRESOLVED in direction(s) %s' % bad))
