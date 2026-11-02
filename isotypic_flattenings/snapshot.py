#!/usr/bin/env python3
"""Merge live worker logs into tracked *_done.log snapshots.

usage: python3 snapshot.py DONE LIVE [LIVE ...]
Keeps every line of DONE whose component (text before ' |' / '  H1' on a
'lam=' line) is not present in the LIVE logs, then appends the LIVE logs.
'# blocks' progress lines are dropped from the snapshot."""
import sys, re, os

def key(line):
    m = re.match(r'(lam=\(.*?\)\))', line)
    return m.group(1) if m else None

def main():
    done, lives = sys.argv[1], sys.argv[2:]
    live_lines = []
    for f in lives:
        if os.path.exists(f):
            live_lines += [l for l in open(f) if not l.startswith('# blocks')]
    live_keys = {key(l) for l in live_lines if key(l)}
    live_set = set(live_lines)
    old = []
    if os.path.exists(done):
        for l in open(done):
            if l.startswith('# blocks'):
                continue
            k = key(l)
            if (k and k in live_keys) or l in live_set:
                continue
            old.append(l)
    out, seen = [], set()
    for l in old + live_lines:   # drop exact duplicates (SKIPPED lines are re-printed after every restart)
        if l in seen: continue
        seen.add(l); out.append(l)
    nlam = sum(1 for l in out if l.startswith('lam='))
    nsep = sum(1 for l in out if 'SEPARATES' in l)
    with open(done, 'w') as fh:
        fh.writelines(out)
    print(f"{done}: {nlam} components, {nsep} separators")

if __name__ == '__main__':
    main()
