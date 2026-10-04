#!/bin/bash
# copy the live results/logs of special_runner.py (untracked special/live) into special/res, special/logs, regenerate
# special/RESULTS.md, commit and push (only the agent's own files)
cd "$(dirname "$0")/.."
cp special/live/res/*.jsonl special/res/ 2>/dev/null
cp special/live/logs/*.log special/logs/ 2>/dev/null
cp special/live/runner.log special/runner.log 2>/dev/null
python3 special_report.py > /dev/null
cd ..
git add isotypic_flattenings/special isotypic_flattenings/agents/special.md
git commit -q -m "${1:-special: status + results $(date -u +%Y-%m-%dT%H:%MZ)}

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011PvHpiz5uTxAuvZ6vYqqez" || true
for i in 1 2 3 4; do
  git pull -q --rebase --autostash origin claude/trusting-bohr-hdnmbv && git push -q -u origin claude/trusting-bohr-hdnmbv && break
  sleep $((2 ** i))
done
git log --oneline -1
