#!/usr/bin/env bash
set -euo pipefail
cd /home/gitzard/shorecdlp-a
git checkout -q -- . 2>/dev/null || true
rm -rf ShorECDLP/Submission/Entrant
cp -r /mnt/c/code/shor-ecdlp-contest/entrants/20261029-1215-rounds6/Entrant ShorECDLP/Submission/Entrant
git stash drop -q || true
bash /mnt/c/code/shor-ecdlp-contest/workspace/cmp_snapshot.sh 20261029-1215-rounds6 >/dev/null
cd /home/gitzard/shorecdlp-a/ShorECDLP/Submission/Entrant && for f in *.lean; do cmp -s $f /mnt/c/code/shor-ecdlp-contest/entrants/20261029-1215-rounds6/Entrant/$f && echo "$f same"; done; find . -type f | wc -l
cd /home/gitzard/shorecdlp-a; git log --oneline -1; git status --short | wc -l
