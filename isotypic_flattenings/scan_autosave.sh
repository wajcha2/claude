#!/bin/bash
# Every PERIOD seconds (default 1800): regenerate the report, copy the live files of scan/live/ (untracked, written
# by the runner and the workers) into scan/, commit and push.  `./scan_autosave.sh once` does one snapshot.
PERIOD=${PERIOD:-1800}
cd "$(dirname "$0")"
snapshot() {
  PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 SCAN=scan/live python3 scan_report.py >/dev/null 2>&1
  for f in state.json STATUS.md summary.json monitor.log runner.log; do [ -f scan/live/$f ] && cp scan/live/$f scan/$f; done
  for dn in res jobs logs; do [ -d scan/live/$dn ] && mkdir -p scan/$dn && cp -r scan/live/$dn/. scan/$dn/; done
  cd ..
  if [ ! -e .git/index.lock ]; then
    git add isotypic_flattenings/scan >/dev/null 2>&1
    if ! git diff --cached --quiet; then
      git commit -q -m "rank scan: status + results $(date -u +%Y-%m-%dT%H:%MZ)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01A51D6Z3hiqcCpMJhPW4qv5" && \
      for i in 1 2 3 4; do
        # another agent (special subspaces) pushes to the same branch: rebase onto it first (only its own files)
        git pull -q --rebase --autostash origin claude/trusting-bohr-hdnmbv && git push -q origin claude/trusting-bohr-hdnmbv && break
        git rebase --abort >/dev/null 2>&1; sleep $((2**i))
      done
    fi
  fi
  cd isotypic_flattenings
}
if [ "$1" = "once" ]; then snapshot; exit 0; fi
while true; do sleep "$PERIOD"; snapshot; done
