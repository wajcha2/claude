#!/bin/bash
# one-shot: when the family-A lattice (8,1) aux 2 is summarised, restart the AE worker so that it loads MODRANK_BLOCK = 32
# (the runner relaunches it with --resume; finished lattices are skipped)
cd "$(dirname "$0")"
until grep -q '^famA(aux=2) lam=81 members=' logs/jobs/d9_455_dir0_AE_part*.log 2>/dev/null; do sleep 30; done
pid=$(pgrep -f '^/usr/bin/python3 -u .*comb_search.py 4,5,5 9 8,9 --dir 0 --fam A,E')
[ -n "$pid" ] && kill $pid && echo "$(date +%H:%M:%S) restarted AE worker $pid after famA(aux=2) lam=81 (MODRANK_BLOCK 32)" >> logs/jobs/mem.log
