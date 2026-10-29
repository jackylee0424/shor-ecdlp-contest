#!/usr/bin/env bash
# Reset builder checkouts to the leader commit (default: origin/master tip).
set -euo pipefail
cd /home/gitzard/shorecdlp && git fetch -q origin
tgt=${1:-$(git rev-parse --short origin/master)}
echo "leader commit: $tgt ($(git log -1 --format=%s $tgt))"
for b in shorecdlp shorecdlp-m shorecdlp-c; do
  cd /home/gitzard/$b
  git fetch -q origin
  git reset -q --hard "$tgt"
  git clean -fdq -- ShorECDLP/Submission/Entrant
  git stash clear || true
  echo "$b: $(git log --oneline -1 | cut -c1-60) dirty=$(git status --short | wc -l)"
done
