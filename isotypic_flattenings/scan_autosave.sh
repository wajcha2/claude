#!/bin/bash
# commits and pushes scan/ every PERIOD seconds (default 1800); run with setsid nohup.
PERIOD=${PERIOD:-1800}
cd "$(dirname "$0")"
while true; do
  sleep "$PERIOD"
  PYTHONDONTWRITEBYTECODE=1 OPENBLAS_NUM_THREADS=1 python3 scan_report.py >/dev/null 2>&1
  cd ..
  if [ ! -e .git/index.lock ]; then
    git add isotypic_flattenings/scan >/dev/null 2>&1
    if ! git diff --cached --quiet; then
      git commit -q -m "rank scan: status + results $(date -u +%Y-%m-%dT%H:%MZ)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01A51D6Z3hiqcCpMJhPW4qv5" && \
      for i in 1 2 3 4; do git push -q origin claude/trusting-bohr-hdnmbv && break; sleep $((2**i)); done
    fi
  fi
  cd isotypic_flattenings
done
