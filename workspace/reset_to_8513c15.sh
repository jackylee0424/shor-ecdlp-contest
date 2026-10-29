#!/usr/bin/env bash
set -euo pipefail
for b in shorecdlp shorecdlp-m; do
  cd /home/gitzard/$b
  git fetch -q origin
  git reset -q --hard 8513c15
  git clean -fdq -- ShorECDLP/Submission/Entrant
  echo "$b: $(git log --oneline -1) dirty=$(git status --short | wc -l)"
done
cd /mnt/c/code/shor-ecdlp-contest && formal-tools/score.sh 2>&1 | grep -E 'Verified score|replay passed|rc=' | tail -4
formal-tools/snapshot.sh frontier-3e53f42 "leader dadon 3e53f42 (single trial 263/263, EEA literal cancellation); local accepted"
