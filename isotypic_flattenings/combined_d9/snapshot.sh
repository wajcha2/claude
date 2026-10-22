#!/bin/bash
# snapshot.sh: copy the live job logs (untracked logs/jobs/) to logs/jobs_snapshot/ and the report to STATUS_TABLE.md
cd "$(dirname "$0")"
mkdir -p logs/jobs_snapshot
cp logs/jobs/*.log logs/jobs/runner.status logs/jobs_snapshot/ 2>/dev/null
python3 d9_report.py > logs/jobs_snapshot/report.md
