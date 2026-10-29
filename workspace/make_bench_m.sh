#!/usr/bin/env bash
# Independent checkout for the multiplier builder: copy the idle A checkout, reset to the frontier commit.
set -euo pipefail
dest=/home/gitzard/shorecdlp-m
[ -e "$dest" ] && { echo "exists: $dest"; exit 1; }
cp -a /home/gitzard/shorecdlp-a "$dest"
cd "$dest"
git fetch -q origin
git reset -q --hard 93051d2
git clean -fdq -- ShorECDLP/Submission/Entrant
git log --oneline -1; git status --short | wc -l
bash /mnt/c/code/shor-ecdlp-contest/workspace/cmp_snapshot.sh 20261029-1355-frontier-ff1bf8d >/dev/null 2>&1 || true
diff -rq ShorECDLP/Submission/Entrant /mnt/c/code/shor-ecdlp-contest/entrants/20261029-1355-frontier-ff1bf8d/Entrant && echo "entrant == frontier snapshot"
cd /mnt/c/code/shor-ecdlp-contest && BENCH=$dest formal-tools/build.sh 2>&1 | tail -2
