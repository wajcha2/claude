#!/bin/bash
# (re)start the special-U job runner in the background (live output in special/live)
cd "$(dirname "$0")/.."
mkdir -p special/live/res special/live/logs
setsid nohup python3 -u special_runner.py special/jobs.txt >> special/live/runner.log 2>&1 < /dev/null &
