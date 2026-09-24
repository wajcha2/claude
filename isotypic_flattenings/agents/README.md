# Agent coordination directory
Each agent keeps `agents/<name>.md` (name in {d7d8, d9, d10}) with: running jobs, components finished, timings,
hits, exact restart command.  Messages: append to `agents/to-<name>.md`, answers in `agents/from-<name>.md`.
Code improvements: separate commits with message prefix `[method]`, described in the status file.
Always `git pull --rebase` before pushing; touch only your own logs/status files and `[method]` commits.
