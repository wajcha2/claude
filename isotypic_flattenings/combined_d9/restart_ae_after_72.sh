#!/bin/bash
# one-shot: when the family-A lattice (7,2) aux 1 is summarised, restart the AE worker before it builds the aux-2 lattice
# with the old code (all flattenings of (7,2) kept in memory, ~3.9 GB, plus ~5 GB of compressed matrices); the new code
# frees the flattenings after building a lattice and the matrices of dropped saturated members
cd "$(dirname "$0")"
until grep -q '^famA lam=72 members=' logs/jobs/d9_455_dir0_AE_part*.log 2>/dev/null; do sleep 15; done
pid=$(pgrep -f '^/usr/bin/python3 -u .*comb_search.py 4,5,5 9 8,9 --dir 0 --fam A,E')
[ -n "$pid" ] && kill $pid && echo "$(date +%H:%M:%S) restarted AE worker $pid after famA lam=72 (memory fixes)" >> logs/jobs/mem.log
