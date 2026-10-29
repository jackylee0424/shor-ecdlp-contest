#!/usr/bin/env bash
set -euo pipefail
bash /mnt/c/code/shor-ecdlp-contest/workspace/make_bench_copy.sh /home/gitzard/shorecdlp-a 20261029-1215-rounds6
cd /home/gitzard/shorecdlp-a
git fetch -q origin
echo "== protected diff vs origin/master (excluding Entrant):"
git diff --stat HEAD origin/master -- . ':!ShorECDLP/Submission/Entrant' | tail -3
echo "== yukon harness-only sync"
git stash -q -- ShorECDLP/Submission/Entrant 2>/dev/null || true
yukon sync --harness-only 2>&1 | sed 's/\x1b\[[0-9;]*m//g' | tail -8
git stash pop -q 2>/dev/null || true
git log --oneline -1
git status --short | head
