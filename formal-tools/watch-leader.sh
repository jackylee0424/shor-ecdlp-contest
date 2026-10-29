#!/usr/bin/env bash
# Poll the Yukon leaderboard and exit (printing the new best and commit) as soon as the best score
# differs from the one given. Meant to run in the background so the orchestrator is notified.
# usage: watch-leader.sh <current-best> [interval-seconds]
set -uo pipefail
export PATH="$HOME/.local/bin:$PATH"
current="$1"; interval="${2:-900}"
bench=a721dbcb-4a80-4074-853c-53534959dcb8
while true; do
  best=$(cd ~/shorecdlp-a && yukon benchmark show "$bench" 2>/dev/null | sed 's/\x1b\[[0-9;]*m//g' | awk '/current best/{print $3}')
  src=$(cd ~/shorecdlp-a && yukon benchmark show "$bench" 2>/dev/null | sed 's/\x1b\[[0-9;]*m//g' | awk '/^source /{print $NF}')
  if [[ -n "$best" && "$best" != "$current" ]]; then
    echo "NEW LEADER: best=$best (was $current) source=$src at $(date -Is)"
    exit 0
  fi
  sleep "$interval"
done
